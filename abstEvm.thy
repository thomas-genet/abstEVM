(* Authors: Justine Sauvage and Thomas Genet *)
theory abstEvm
  imports Main 
begin 

section \<open>First EVM abstract semantics : yellow paper\<close>

subsection \<open>Common assumptions for the two abstract semantics\<close>
text \<open>
   This theory defines an asbtract version of the Ethereum Virtual Machine (EVM) 
   The corresponding functions are:
      smallstep ::"call_stack \<Rightarrow> call_stack"  (for one step evaluation)
      execute :: "call_stack \<Rightarrow> frame"        (for complete evaluation)
   The main purpose of this theory is to show termination of the execute function.
  \<close>

text \<open>
  Here are the abstractions that are done w.r.t. EVM semantics:
  - We make no difference between different calls w.r.t. gas consumption
  - We make no difference between all "local" operations, they have an arbitrary cost greater than 0
  - The call stack size is bounded by a natural greater than 0 (called stack_lim) 
  - The create is represented by a call on an undefined contract name. It creates the contract 
    with an arbitrary program, and runs it.
  - We make no difference between return and revert 
  - We make no difference between stop and suicide/selfdestruct
  \<close>

subsection \<open>Specific assumptions : yellow paper\<close> 

text \<open>Assumptions coherent with the yellow paper:
  - A call consumes the gas **after** the return
  - Because of the above assumption, a contract recursively calling itself would 
    never stop (it consumes no gas) if there was no call stack limit. This is why
    the termination proof highly depends on the call stack bound.
  - A successful call can result into a gas refund
  - When a call returns with a gas greater than the gas that was initially sent, 
    we throw an exception.
  \<close>

(* Maximum call stack size *)
consts
 stack_lim::nat

axiomatization
  where min_stack_lim: "stack_lim>0" 

type_synonym 
  gas = nat

type_synonym
  pc= nat

type_synonym
  contractName= string

datatype
  instr = Nil  (* Undefined instruction *)
  | Local "gas" (* For each local operation we associate a gas cost *)
  (* The call operation has two gas values. The first one is the cost of the call instruction
     and the second one is the gas transferred to the called contract *)
  | Call "gas*gas*contractName"  (*g_base_mem(gas 1) = Cbase+Cmem on Yellow paper ; gcall(gas 2)= ccall *)
  | Stop (* Stop represent selfdestruct (suicide), stop, and return *)
  | Jump "gas*pc"

type_synonym program = "instr list"

definition "p1= [Local 10,Call (1,1,''c1''),(Jump (5,0))]"

value "nth p1 0"
value "nth p1 1"
value "nth p1 2"


(* The instruction associated to a pc in a given program *)
fun mynth :: "program \<Rightarrow> pc \<Rightarrow> instr" ("_.(_)")
  where
  "mynth p pc = (if pc < (length p ) then (nth p pc) else Stop)"

value "p1.(0)"
value "p1.(1)"
value "p1.(2)"
value "p1.(5)"

abbreviation "name_test \<equiv> (''hello''::contractName) "

type_synonym env= "contractName \<Rightarrow> program option"

(* Examples of environments  *)
definition "(e1::env)= (\<lambda>x. None)"                 (* The empty environement *)
definition "(e2::env)= e1 (''c1'':= Some [Nil])"   (* association between contract name "c1" and a [Nil] program *)
definition "(e3::env)= e2 (''c2'':= Some [Local 10,Stop])"
definition "(e4::env)= e3 (''c1'':= Some [Jump((5::gas),0)])"      (* we change the program associated to c1*)   
definition "(e5::env) = e4 (name_test := Some [Stop])"

value "e4(''c1'')"  
value "e4(''c2'')"
value "e4(''c3'')"   (* Contract ''c3'' is undefined *)
value "e4(name_test)"
value "e5(name_test)"


(* This predicates represents valid instructions, i.e., instructions with a strictly positive cost! *)
fun valid_instr :: "instr \<Rightarrow> bool" 
  where 
  "valid_instr (Local n) = (n>0)"|
  "valid_instr (Stop) = True"|
  "valid_instr (Nil) = True"|
  "valid_instr (Call (g,gcall,name)) = ((g>0)\<and>(gcall>0))"|
  "valid_instr (Jump(n,pc)) = (n>0)"

(* Remark: Nil is a valid instruction whose execution will result into an exception *)

(* A valid program is composed of valid instructions *)
fun valid_prog :: "program \<Rightarrow> bool"
  where 
  "valid_prog  [] = True"|
  "valid_prog (i#p) = ((valid_instr i) \<and> (valid_prog p))"

(* A function returning an arbitrary valid program *)
consts 
  any_valid_program:: "nat \<Rightarrow> program"

axiomatization
  where any_valid_is_valid: "\<forall> x. valid_prog (any_valid_program x)"

(* A valid environement maps contracts names to valid programs *)
fun valid_env :: "env \<Rightarrow> bool"
  where
"valid_env e= (\<forall> n. 
  (case e(n) of
     None \<Rightarrow> True
   | (Some p) \<Rightarrow> valid_prog p))"


(* Datatype of frames (i.e. program evaluation states) *)
datatype 
  frame =   
    Ok "gas*pc*program*env"  (* Regular program state *)
    | Exception              (* Exceptional program final state *)
    | Halt "gas*env"         (* Regular program final state *)
    | Invalid_frame          (* Invalid_frame should never occur. Present only for totality of the small_step semantic function (on programs that are ill formed) *)

type_synonym
  call_stack = "frame list"

(* A call stack is a list of frames where the most recent frame is at the beginning of the list *)
(* We show in the soundness theorem below (see finalCorrection) that the execution of any valid call_stack (i.e. without Invalid_frames)
   results into another valid call_stack *)

fun depth_stack:: " call_stack \<Rightarrow> nat"
  where "depth_stack stack = (length  stack)"

(* The valid_stack_aux function only checks that a stack is composed of OK states *)
fun valid_stack_aux :: "call_stack \<Rightarrow> bool"
  where 
    "valid_stack_aux [] = True"|
    "valid_stack_aux ((Ok (g,pc,p,e))#[]) = ((valid_env e) \<and> (valid_prog p ))"|
    "valid_stack_aux ((Ok (g,pc,p,e))#(Ok (g2,pc2,p2,env2))#l) = 
       (case p2.(pc2) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall+ccall)>g2 | (gcall\<le>0) | (ccall\<le>0)) then False
                                     else ((valid_prog p) \<and> (valid_env e) \<and> (valid_stack_aux (Ok(g2,pc2,p2,env2)#l))))
        | _ \<Rightarrow> False)" |
    "valid_stack_aux l = False"

(* A stack is valid if it is a list of valid program states and after a Halt/Exception there can only
   be OK frames ... and the current called instruction in the state Ok should be
   a call with correct values.
   Besides, all environement should map names to valid programs (valid_env)!
 *)
fun valid_stack :: "call_stack \<Rightarrow> bool"
  where
  "valid_stack [] = False"|
  "valid_stack [Halt (g,e)] = (valid_env e)"|
  "valid_stack [Exception] = True"|
  "valid_stack [Invalid_frame] = False"|
  "valid_stack ((Ok (g,pc,p,e))#[]) = ((valid_env e) \<and> (valid_prog p ))"|
  "valid_stack ((Ok (g,pc,p,e))#(Ok (g2,pc2,p2,env2))#l) = 
       (case p2.(pc2) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall+ccall)>g2 | (gcall\<le>0) | (ccall\<le>0)) then False
                                     else ((valid_prog p) \<and> (valid_env e) \<and> (valid_stack_aux (Ok(g2,pc2,p2,env2)#l))))
        | _ \<Rightarrow> False)" |
  "valid_stack ((Ok (g,pc,p,e))#_) = False" |
  "valid_stack ((Halt (g,e))#Ok(g2,pc,p,env2)#l) = 
      (case p.(pc) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall+ccall)>g2 | (gcall\<le>0) | (ccall\<le>0)) then False
                                    else ((valid_env e) \<and> (valid_stack_aux (Ok(g2,pc,p,env2)#l))))
        | _ \<Rightarrow> False)" |
  "valid_stack ((Halt (g,e))#_) = False" |
  "valid_stack ((Exception)#Ok(g2,pc,p,env2)#l) = (case p.(pc) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall+ccall)>g2 | (gcall\<le>0) | (ccall\<le>0)) then False
                                    else (valid_stack_aux (Ok(g2,pc,p,env2)#l)))
        | _ \<Rightarrow> False)"|
  "valid_stack ((Exception)#_) = False"|
  "valid_stack (Invalid_frame#l) = False"

(* We associate gas for exception/Invalid frame for the termination measures *)
fun get_gas_frame :: "frame \<Rightarrow> nat"
  where
  "get_gas_frame Invalid_frame = 1"|
  "get_gas_frame Exception = 1"|
  "get_gas_frame (Halt (g,e)) = g+2"|
  "get_gas_frame (Ok (g,pc,p,e)) = g+3"

value "get_gas_frame Exception"
value "get_gas_frame Invalid_frame"

fun get_gas :: "call_stack \<Rightarrow> nat "
  where
  "get_gas [] = 0"|
  "get_gas (a#l) = (get_gas_frame a)+(get_gas l)"

fun order :: "nat \<Rightarrow> call_stack \<Rightarrow> nat"
  where
  "order n [] = 0"|
  "order n (Exception#l) = (if (n>(length l)) then 0 else ((get_gas_frame (nth (rev (Exception#l)) n))))"|
  "order n (Invalid_frame#l) = (if (n>(length l)) then 0 else ((get_gas_frame (nth (rev (Invalid_frame#l)) n))))"|
  "order n ((Halt (g,e))#l) = (if (n>(length l)) then (g+3) else ((get_gas_frame (nth (rev ((Halt (g,e))#l)) n))))"|
  "order n ((Ok (g,pc,p,e))#l) = (if (n>(length l)) then (g+4) else ((get_gas_frame (nth (rev ((Ok (g,pc,p,e))#l)) n))))"

fun list_order_aux :: "nat \<Rightarrow> nat \<Rightarrow> (call_stack \<Rightarrow> nat) list"
  where
"list_order_aux 0 _ = []" |
"list_order_aux (Suc x) y= (order (y - (Suc x)))#(list_order_aux x y)"

(* This is the main termination measure function: given a maximal stack size i, 
   it results into a list (of length i) of measure functions mapping call_stack to nat
  
   E.g., (list_order 3) is [(order 0),(order 1),(order 2)]
 *)
fun list_order :: "nat \<Rightarrow> (call_stack \<Rightarrow> nat) list"
  where
"list_order i = (list_order_aux i i)" 

value "list_order 3"

(* Basic properties on list_order *)
lemma size_list_order_aux: "(length (list_order_aux i j)) = i"
  apply (induct i arbitrary:j)
   apply auto
  done

lemma size_list_order: "(length (list_order i)) = i"
  using size_list_order_aux apply auto
  done

lemma list_order_aux_nth:"(j\<ge>i \<and> k<i) \<longrightarrow> ((list_order_aux i j) ! k) = (order (j - i + k))"
  apply (induct i arbitrary:j k)
   apply auto
  using less_Suc_eq_0_disj by auto
  
lemma list_order_nth:"(i<j) \<longrightarrow> ((list_order j)! i) = (order i)"
  using list_order_aux_nth by auto

(* Recall that a call stack is a list of frames where the most recent frame is at the beginning of the list *)
value "order 0 [Ok (18,pc,p,e)]" 
value "order 1 [Ok (18,pc,p,e)]" 
(* After a call 10 given to contract c1, the stack become *)
value "order 0 [Ok (10,pc2,p2,e_2),Ok (18,pc,p,e)]"
(* After a call 5 given to contract c2, the stack becomes  *)
value "order 0 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "order 1 [Halt(2,e_4),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]" (* We assume that contract c2 ends with 2 gas *)
value "order 0 [Ok (7,pc2,p2,e_2),Ok (18,pc,p,e)]" (* We return from the contract c2*)
value "order 0 [Halt (7,e_2),Ok (18,pc,p,e)]"   (* Contract c1 ends with 7 gas *)
value "order 0 [Ok (12,pc,p,e)]"               (* We return from the contract c1 *)

value "order 3 [Exception, Ok (7,pc2,p2,e_2),Ok (18,pc,p,e)]" 

value "order 0 [Exception]"
value "order 0 [Invalid_frame]"  
value "order 1 [Ok (12,pc,p,e),Invalid_frame]"            
value "order 1 [Invalid_frame]" 
value "order 1 [Invalid_frame,Invalid_frame]"  


(* Functions used to explain the measure *)
fun specialMap:: "('a \<Rightarrow> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b list"
  where
"specialMap [] _ = []" |
"specialMap (f#r) x = (f x)#(specialMap r x)"

fun demoMeasure:: "nat \<Rightarrow> call_stack \<Rightarrow> nat list"
  where
"demoMeasure max_stack_size c = specialMap (list_order max_stack_size) c"

(* How order is used?*)
(* We associate to each frame stack a list of natural numbers *)
(* For instance, by executing a call(...,10,...) we move from [Ok (18,pc,p,e)] to stack:
   [Ok (10,pc2,p2,e_2),Ok (18,pc,p,e)] 

   For a stack, the measure becomes a list of natural numbers that are compared with lexicographic order 

  e.g the above stacks are (in the correct order for lexicographic comparison): 
  ||Ok 18|         and       ||Ok 18|Ok 10|  the measurement lists are of the form
  [18,19,19,19]    and       [18,10,11,11]     (where the numbers may be greater in the real measure functions (there are +2 and +3 in Justine's 
                                                measure functions)

*)

value "demoMeasure 4 [Ok (18,pc,p,e)]" 
value "demoMeasure 4 [Exception,Ok (18,pc,p,e)]" 
value "demoMeasure 4 [Ok (18,pc,p,e)]" 

value "demoMeasure 4 [Ok (10,pc2,p2,e_2),Ok (18,pc,p,e)]" 
value "demoMeasure 4 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "demoMeasure 4 [Halt(2,e_4)]"
value "demoMeasure 4 [Exception]"

(* because the measure is a list of functions, [(order 0), (order 1), (order 2), (order 3)] and we have *)
value "order 0 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "order 1 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "order 2 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "order 3 [Ok (5,pc3,p3,e_2),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"

value "demoMeasure 4 [Halt(2,e_4),Ok (10,pc2,p2,e2),Ok (18,pc,p,e)]"
value "demoMeasure 4 [Ok (7,pc2,p2,e_2),Ok (18,pc,p,e)]"
value "demoMeasure 4 [Ok (12,pc,p,e)]"            


(*____________________________Some lemmas on order______________________________________ *)


lemma order_equal_frame : " n < length l \<longrightarrow> get_gas_frame (((rev l)@a) !  n ) = get_gas_frame ( (rev l)! n) "
  by (simp add: nth_append)

lemma order_equal_base : "  (n < length (i#l)) \<longrightarrow> get_gas_frame (((rev (i#l))@a) ! n) = order n (i#l)"
  apply (induct i)
  apply auto
  apply (simp add: nth_append)
  apply (metis length_rev less_Suc_eq nth_append nth_append_length)
  apply (metis length_rev less_Suc_eq nth_append nth_append_length)
  apply (simp add: nth_append)
  done  
  

lemma order_equal : "n<(length l) \<longrightarrow> (order n (a#l)) = (order n l)"
  apply (cases "l=[]")
  apply simp
  apply (induct a)
  apply auto
  apply (metis get_gas.elims order_equal_base)
  apply (metis get_gas.elims order_equal_base)
  apply (metis get_gas.elims order_equal_base)
  apply (metis get_gas.elims order_equal_base)
  done
  
 
lemma order_rev : "(n<(length l)) \<longrightarrow> (order n l ) = (get_gas_frame (nth (rev l) n))"
  using less_Suc_eq order_equal order_equal_base order_equal_frame by auto
  
lemma order_rev_length : " (order (length l) (a#l)) = (get_gas_frame a)"
  by (metis length_Cons length_rev lessI nth_append_length order_rev rev.simps(2))
   

lemma trivial : "(~ i = [] ) \<longrightarrow> ((order 0 (a#i)) = (order 0 i)) "
  by (simp add: order_equal)    

lemma min_callstack : " ~ ((i = [])\<or>(i=[Invalid_frame]))\<longrightarrow> (a = nth (rev i) 0 )\<longrightarrow> order 0 i > 0"
  apply (induct a)
  apply simp
     apply (simp add: order_rev)
  using frame.distinct(5) get_gas_frame.elims gr_zeroI numeral_3_eq_3 apply auto[1]
  apply simp
  using get_gas_frame.elims order_rev apply force
  apply simp
  using get_gas_frame.elims order_rev apply force
  apply simp
  by (simp add: order_rev)

lemma order_min_diff : "get_gas_frame a > get_gas_frame b \<longrightarrow> (order (length l) (a#l) ) > (order (length l) (b#l) )"
  apply (induct l)
  apply (simp add: order_rev)
  by (metis length_Cons length_rev lessI nth_append_length order_rev rev.simps(2))

lemma order_list_part1 : "(length l)< stack_lim \<longrightarrow> ( ((n<(length l)) \<longrightarrow> (order n (a#l)) = (order n (b#l))))"
  by (simp add: order_equal)

lemma order_list_part2 : "(length l)< stack_lim \<longrightarrow> get_gas_frame a > get_gas_frame b \<longrightarrow> (order (length l) (a#l) ) > (order (length l) (b#l))"
  by (simp add: order_min_diff)

value "order 0 [Halt (18,Map.empty)]" 
value "order 0 [Exception]" 





lemma list_order_rec1: "((f1 a) = (f1 b)) \<longrightarrow> (((a,b) \<in> (measures (f1#lf))) = ((a,b) \<in> (measures lf)))"
  apply simp
  done


    
lemma list_order_rec2: "(i<(length (lf::('a \<Rightarrow> nat)list)) \<and> (\<forall> j. (j<i \<longrightarrow> (((lf!j) a) = ((lf!j) b))) \<and> ((lf!i) a) < ((lf!i) b))) \<longrightarrow> 
                            (\<forall> j. (j<i \<and> f=lf!j) \<longrightarrow> \<not> ((f a)>(f b)))"
  apply (induct lf arbitrary: f a b)
   apply auto
  done  

lemma list_order_length: "(\<exists> i. lf=[] \<and> i<(length (f1#lf)) \<and> (((f1#lf)!i) a)<(((f1#lf)!i) b)) \<longrightarrow> ((a,b) \<in> (measures (f1#lf)))"
  apply auto
  done
  

lemma list_order_length2: "(\<exists> i. i>0 \<and> i<(length (f1#lf)) \<and> (\<forall> j. j<i \<longrightarrow> (((f1#lf)!j) a) = (((f1#lf)!j) b))) \<longrightarrow> (((a,b) \<in> (measures (f1#lf))) = ((a,b) \<in> (measures lf)) )"
  apply auto
  done


lemma list_order_seq: "(\<exists> i. i<(length lf) \<and> (\<forall> j. (j<i) \<longrightarrow> ((lf!j) a) = ((lf!j) b)) \<and> ((lf!i) a) < ((lf!i) b)) \<longrightarrow> ((a,b) \<in> (measures lf))"
  apply (case_tac "(\<exists> i. i<(length lf) \<and> (\<forall> j. (j<i) \<longrightarrow> ((lf!j) a) = ((lf!j) b)) \<and> ((lf!i) a) < ((lf!i) b))")
  apply auto
   apply (induct lf arbitrary: a b)
   apply simp
  apply (rename_tac f1 lf i a b)
  by (metis gr0_conv_Suc in_measures(2) length_Cons not_less_eq nth_Cons_0 nth_Cons_Suc nth_non_equal_first_eq)


lemma list_order_pos: "(a\<noteq>[] \<and> b\<noteq>[]) \<longrightarrow>(\<exists> i. i<stack_lim \<and> (\<forall> j. (j<i) \<longrightarrow> ((order j) a) = ((order j) b)) \<and> ((order i) a) < ((order i) b)) \<longrightarrow> ((a,b) \<in> (measures (list_order stack_lim)))"
  apply auto
  apply (case_tac "(\<exists> i. i<(length (list_order stack_lim)) \<and> (\<forall> j. (j<i) \<longrightarrow> (((list_order stack_lim)!j) a) = (((list_order stack_lim)!j) b)) \<and> (((list_order stack_lim)!i) a) < (((list_order stack_lim)!i) b))")
  apply (simp add: list_order_seq)
  apply (case_tac "length (list_order stack_lim) = stack_lim")
  defer
  using size_list_order apply blast
  apply (case_tac "j<i \<longrightarrow> ((list_order stack_lim ! j) a = (list_order stack_lim ! j) b)")
  defer
  using list_order_nth apply auto[1]
  apply (case_tac "((list_order stack_lim ! i) a < (list_order stack_lim ! i) b)")
  defer
  using list_order_nth apply auto[1]
  using list_order_nth by auto
  

lemma gas_order: "get_gas_frame a > get_gas_frame b \<longrightarrow> (order (length l) (a#l) ) > (order (length l) (b#l))"
  apply (induct l)
  apply auto
  apply (metis list.size(3) order_rev_length)
  by (metis length_Cons order_rev_length)



lemma list_order_aux:"((length l)< stack_lim \<and> (\<forall> j<(length l). (order j (a#l)) = (order j (b#l))) \<and>
                  (order (length l) (a#l) ) > (order (length l) (b#l)) \<and> lf= (list_order stack_lim)) \<longrightarrow> 
          (\<exists> i. i=(length l) \<and> (\<forall> j. (j<i) \<longrightarrow> ((lf!j) (a#l)) = ((lf!j) (b#l))) \<and> ((lf!i) (a#l)) > ((lf!i) (b#l)))"
  apply simp
  apply (case_tac "(list_order_aux stack_lim stack_lim ! length l) = (order (length l))")
  apply (metis less_imp_le_nat less_le_trans list_order.simps list_order_nth)
  by (metis list_order.simps list_order_nth )



lemma list_order_seq2: "((length l)< stack_lim \<and> (\<forall> j<(length l). (order j (a#l)) = (order j (b#l))) \<and>
                  (order (length l) (a#l) ) > (order (length l) (b#l))) \<longrightarrow> ((b#l),(a#l))\<in> measures (list_order stack_lim)"
  apply (case_tac "(\<exists> i. i=(length l) \<and> (\<forall> j. (j<i) \<longrightarrow> (((list_order stack_lim)!j) (a#l)) = (((list_order stack_lim)!j) (b#l))) \<and> (((list_order stack_lim)!i) (a#l)) > (((list_order stack_lim)!i) (b#l)))")
  apply (metis list_order_seq size_list_order)
  using list_order_aux by auto
  



lemma order_list : " (length l)<( stack_lim ) \<longrightarrow> get_gas_frame a > get_gas_frame b \<longrightarrow> ((b#l),(a#l))\<in> measures (list_order stack_lim)"
  using list_order_seq2 order_list_part1 order_rev_length by auto
  



lemma impossible_case_aux : " length l > 1 \<longrightarrow> order 1 l > 0"
  using get_gas_frame.elims order_rev by force


lemma teste : " order 1 l = 0 \<longrightarrow> length l \<le> 1"
  using impossible_case_aux not_less by blast

  
lemma impossible_case :"order 1 l = 0 \<longrightarrow> (l = [Invalid_frame] \<or> l = [Exception] \<or> l = []) "
  apply (case_tac l)
  apply simp
  apply (case_tac list)
  prefer 2
  using impossible_case_aux apply auto[1]
  apply (case_tac a)
  apply auto
  done

lemma min_invalid_frame : "(length i\<le>stack_lim) \<longrightarrow> \<not>(i =[Invalid_frame] \<or> i = []\<or>(i=[Exception])) \<longrightarrow> ([Invalid_frame],i) \<in> measures (list_order stack_lim)"
  apply auto
  apply (case_tac i)
  apply simp
  apply (case_tac "(order 0 (a#list))>(order 0 [Invalid_frame])")
  apply (metis diff_self_eq_0 gr0_conv_Suc list_order_aux.simps(2) measures_less min_stack_lim)
  apply (case_tac "(order 0 (a#list)) =(order 0 [Invalid_frame])")
  apply (case_tac "(order 1 (a#list))>(order 1 [Invalid_frame])")
    apply (case_tac "stack_lim<1")
  using min_stack_lim apply linarith
  apply (metis (no_types, hide_lams) add_2_eq_Suc' add_cancel_right_left get_gas_frame.elims get_gas_frame.simps(1) le_eq_less_or_eq length_Cons length_greater_0_conv less_add_Suc2 less_one list_order.simps list_order_pos not_less numeral_3_eq_3 order_rev_length)
  using impossible_case apply auto[1]
  by (simp add: Suc_lessI min_callstack)
  
  
lemma min_exception : "(length i\<le>stack_lim) \<longrightarrow> \<not>(i =[Invalid_frame] \<or> i = []\<or>(i=[Exception])) \<longrightarrow> ([Exception],i) \<in> measures (list_order stack_lim)" 
  apply auto  
  apply (case_tac i)
  apply simp
  apply (case_tac "(order 0 (a#list))>(order 0 [Exception])")
  apply (metis diff_self_eq_0 gr0_conv_Suc list_order_aux.simps(2) measures_less min_stack_lim)
  apply (case_tac "(order 0 (a#list)) =(order 0 [Exception])")
   apply (case_tac "(order 1 (a#list))>(order 1 [Exception])")
    apply (case_tac "stack_lim<1")
  using min_stack_lim apply linarith
  apply (metis One_nat_def diff_Suc_1 get_gas_frame.simps(1) get_gas_frame.simps(2) in_measures(1) less_one list.distinct(1) list.size(3) list_order.simps list_order_aux.simps(1) list_order_aux.simps(2) list_order_pos list_order_rec1 min_invalid_frame not_less_iff_gr_or_eq order_rev_length)
  using impossible_case apply auto[1]
  by (simp add: Suc_lessI min_callstack)
  
(*_______________________Semantics______________________________________________________________*)

(* The small step function of EVM *)
fun smallstep ::"call_stack \<Rightarrow> call_stack"
  where
  "smallstep ((Ok (g,pc,p,e))#l) = (case p.(pc) of 
                                  Stop \<Rightarrow> ((Halt (g,e))#l) |
                                  Nil  \<Rightarrow>  (Exception#l)|
                                  \<comment> \<open>Basic instruction : pc is increased and we consume the gas of the instuction (n)\<close>
                                  Local(n) \<Rightarrow>( if (n>0) then (
                                                        if (n\<le>g) then 
                                                                     ((Ok ((g-n),pc+1,p,e))#l)
                                                                  else
                                                                    (Exception#l))
                                                       else ([Invalid_frame]) )|
                                 Jump(n,pj) \<Rightarrow> if (n>0) then (
                                                           if (n\<le>g) then (if (pj<(length p)) then  
                                                                                          ((Ok (g-n,pj,p,e))#l)
                                                                                       else
                                                                                          (Exception#l)) 
                                                                     else (Exception#l) )
                                                        else ([Invalid_frame]) |
                                \<comment> \<open>Call instruction call: gas is not consumed (yet) and we stack a frame_stack\<close>
                                Call (gcall,ccall,name) \<Rightarrow> if ((gcall>0)\<and>(ccall>0)\<and>(((length l)+1)<stack_lim)\<and>((gcall+ccall)\<le>g)) then 
                                                                            (case e(name) of
                                                                                None \<Rightarrow> 
                                                                                        \<comment> \<open>If the contract name is undefined then the contract is defined (i.e. create)
                                                                                            we stack a new frame in which we run an arbitrary new program.
                                                                                            In the environment, we associate the new name to this empty program (Some pnew). \<close>
                                                                                    (let pnew=(any_valid_program 0) in ((Ok (ccall,0,pnew,e( name := (Some pnew) )))#(Ok (g,pc,p,e))#l))
                                                                            \<comment>\<open>Otherwise, we create a new frame where the current program becomes pcall \<close>
                                                                               | (Some pcall) \<Rightarrow>((Ok (ccall,0,pcall,e))#(Ok (g,pc,p,e))#l))
                                                            else ( if (((length l)\<ge>(stack_lim - 1))|((gcall+ccall)>g)) then  (Exception#l)
                                                                   else ([Invalid_frame]) )                  
                             )"|
  "smallstep ([Halt (g,e)]) = [Halt (g,e)] "|
  "smallstep ([Exception]) =[Exception] "|
                                                  \<comment> \<open>Call return with an exception\<close>
  "smallstep ( (Exception)#(Ok (g,pc,p,e))#l ) = (case p.(pc) of
                                                                              \<comment>\<open>if running the call was impossible initially then we produce an invalid_frame
                                                                                 Only here for totality reasons (cannot happend)\<close>
                                                   Call(gcall,ccall,name) \<Rightarrow>  (if ((gcall+ccall)>g) | (gcall\<le>0)|(ccall\<le>0) then [Invalid_frame]  
                                                                               \<comment> \<open>Normal call return with an exception: we consume the gas: gcall and ccall\<close>
                                                                               else  ((Ok ((g-gcall-ccall),(pc+1),p,e))#l))
                                                  | _ \<Rightarrow> [Invalid_frame] )"|
                                               \<comment> \<open>Standard call return with a regular Halt event\<close>
 "smallstep ((Halt (gend,ef))#(Ok (g,pc,p,e))#l) = (case p.(pc) of 
                                                  Call(gcall,ccall,name) \<Rightarrow>  if ((gcall+ccall)>g) then [Invalid_frame]
                                                                             else if (gcall\<le>0) then [Invalid_frame]
                                                                             else if (ccall\<le>0) then [Invalid_frame] 
                                                                             \<comment> \<open>This is coherent with the yellow paper: a call return is valid iff the returned gas is 
                                                                                lesser or equal to the gas sent for the call. Otherwise we throw an exception\<close>
                                                                             else if (ccall<gend) then (Exception#(Ok (g,pc,p,e))#l) 
                                                                              \<comment>\<open>The resulting (modified) environment ef is passed to the current OK top stack_frame\<close>
                                                                             else  ((Ok ((g+gend-gcall-ccall),(pc+1),p,ef))#l)|
                                                  _ \<Rightarrow> [Invalid_frame] )"|
  "smallstep l = [Invalid_frame]"

lemma validMember: "(valid_prog p) \<longrightarrow> (List.member p i) \<longrightarrow> (valid_instr i)"
  apply (induct p)
   apply auto
  apply (simp add: member_rec(2))
  by (simp add: member_rec(1))
 
lemma validInstr: "(valid_prog p) \<longrightarrow> (pc < (length p)) \<longrightarrow> (valid_instr (p ! pc))"
  by (meson in_set_member nth_mem validMember)
 
lemma notValidStackExceptionException: "\<not> (valid_stack (e#(Exception#l)))"
  apply (case_tac e)
     apply auto
  done

lemma valid_stack_aux: "valid_stack_aux (e#l) \<longrightarrow> (valid_stack_aux l)"
  apply (induct "(e#l)" rule:valid_stack_aux.induct)
  apply auto
  apply (case_tac "p2!pc2")
      apply auto
  apply (smt instr.simps(24) instr.simps(27))
  apply (smt instr.simps(25) instr.simps(27))
  apply (smt instr.simps(26) instr.simps(27) old.prod.case)
  apply (smt instr.simps(27))
  by (smt instr.simps(27) instr.simps(28))
  
lemma invalid_invalid: "\<not> (valid_stack (Invalid_frame#l))"  
  apply (induct l)
   apply auto
  done

lemma validstack_Ok_prog: "(valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_prog p)"
  apply (case_tac l)
   apply auto
  apply (case_tac a)
  apply (case_tac x1) 
  apply (rename_tac g2 pc2 p2 e2)
  apply auto[1]
  apply (case_tac "p2!pc2")
  apply (smt instr.simps(24) instr.simps(27))
  apply (smt instr.simps(25) instr.simps(27))
  apply (case_tac "x3")
  apply (rename_tac gcall2 ccall2 name2)
  apply auto[1]
  apply (smt case_prod_conv instr.simps(26) instr.simps(27) valid_env.elims(2))
  apply (smt instr.simps(27))
  apply (smt instr.simps(27) instr.simps(28))
  apply simp
  apply simp
  by simp
  

lemma validstack_Ok_env: "(valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_env e)"
  apply (case_tac l)
  apply auto
  apply (case_tac a)
  apply (case_tac x1) 
  apply (rename_tac g2 pc2 p2 e2)
  apply auto[1]
  apply (case_tac "p2!pc2")
  apply (smt instr.simps(24) instr.simps(27))
  apply (smt instr.simps(25) instr.simps(27))
  apply (case_tac "x3")
  apply (rename_tac gcall2 ccall2 name2)
  apply auto[1]
  apply (smt case_prod_conv instr.simps(26) instr.simps(27) valid_env.elims(2))
  apply (smt instr.simps(27))
  apply (smt instr.simps(27) instr.simps(28))
  apply simp
  apply simp
  by auto

lemma validstack_Ok_aux: "(valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_stack_aux (Ok(g,pc,p,e)#l))"
  apply (case_tac l)
  apply auto
  apply (case_tac a)
  apply auto
  done

lemma validstack_Ok_aux2: "(valid_stack_aux (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_stack (Ok(g,pc,p,e)#l))"
  apply (case_tac l)
  apply auto
  apply (case_tac a)
  apply auto
  done

lemma validstack_Ok: "(valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_stack (Ok(g2,pc2,p,e)#l))"
  apply (case_tac l)
  apply auto
  apply (case_tac a)
  apply auto
  done

lemma validstack_Ok2: "(valid_env env2) \<longrightarrow> (valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_stack (Ok(g,pc,p,env2)#l))"
  apply (case_tac l)
  apply auto
  apply (case_tac "\<not>(valid_stack_aux (a#list))")
  using valid_stack_aux validstack_Ok_aux apply blast
  apply (case_tac a)
  apply simp
  apply (case_tac x1)
  apply (rename_tac y g2 pc2 p2 env3)
  apply simp
  apply (case_tac "p2!pc2")
  apply auto[1]
  apply (smt instr.simps(24) instr.simps(27))
  using instr.simps(27) apply fastforce
  apply auto[1]
  apply (meson gr_zeroI)
  apply (meson neq0_conv)
  using instr.simps(27) apply fastforce
  using instr.simps(27) apply fastforce
  using instr.simps(27) apply fastforce
  apply simp
  apply simp
  apply simp
  done

lemma validstack_exception_step: "(valid_stack (e#l)) \<longrightarrow> (valid_stack (Exception#l))"
  apply (case_tac e)
  apply auto
  apply (case_tac l)
  apply auto
  apply (case_tac ac)
  apply (case_tac x1)
  apply auto
  apply (case_tac "c ! baa ")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  using instr.simps(27) apply fastforce
  apply (case_tac l)
  apply auto
  apply (case_tac aa)
  apply auto
  apply (case_tac "ad ! ac ")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  using instr.simps(27) apply fastforce
  by (simp add: invalid_invalid)

lemma validstack_halt_step: "(valid_env env2) \<longrightarrow> (valid_stack (Ok(g,pc,p,e)#l)) \<longrightarrow> (valid_stack (Halt(g2,env2)#l))"
   apply auto
   apply (case_tac l)
   apply auto
   (* by case on the frame below *)
   apply (case_tac a)
   apply (case_tac x1)
   apply auto
   apply (case_tac "c ! ba ")
   apply auto
   apply (meson neq0_conv)
   apply (meson neq0_conv)
  using instr.simps(27) by fastforce

lemma validstack_exception_top: "valid_stack (Exception # l) \<longrightarrow> valid_stack (smallstep (Exception # l))"
  apply (case_tac l)
  apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac x1)
  (* (1) Ok on top *)
     apply (rename_tac y g pc p e)
     apply (case_tac "p.(pc)")
     apply auto[1]
        apply (simp add: validstack_exception_step) 
        (* call case *)
         apply (case_tac x3)
         apply (rename_tac z gcall ccall name)
         apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length list)+1)<stack_lim)\<and>((gcall+ccall)\<le>g)")
         apply auto[1]
         using validstack_Ok validstack_Ok_aux2 apply blast
         apply auto[1]
         using validstack_Ok validstack_Ok_aux2 apply blast
   apply auto
done                  

lemma validstack_halt_top: "valid_stack ((Halt x) # l) \<longrightarrow> valid_stack (smallstep ((Halt x) # l))"
  apply (case_tac l)
   apply auto
  apply (metis frame.distinct(11) frame.distinct(7) get_gas_frame.elims smallstep.simps(2) valid_stack_aux.simps(5) validstack_Ok_aux)
  apply (case_tac a)
  apply simp
  apply (case_tac x1)
  apply simp
  (* (1) Ok on top *)
     apply (rename_tac y g pc p e)
     apply (case_tac "p.(pc)")
     apply auto[1]
     using validstack_exception_step
     apply force
     using validstack_exception_step apply force 
        (* call case *)
         apply (case_tac x3)
         apply (rename_tac z gcall ccall name)
            (* by case on the return value of Halt *)
         apply (case_tac x)
         apply (rename_tac gend ef)
         apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length list)+1)<stack_lim)\<and>((gcall+ccall)\<le>g)\<and>(gend\<le>gcall)")
         apply simp
         apply (case_tac "\<not> (valid_stack (Ok (g, pc, p, e) # list))")
         apply auto [1]
         apply (simp add: validstack_Ok_aux2)
         apply (simp add: validstack_Ok_aux2)
           apply auto[1]
           apply (case_tac list)
            apply auto[1]
         (* We first show that the sublist is necessarily valid *)
         apply (case_tac "\<not> (valid_stack_aux list)")
     using valid_stack_aux apply blast
         (* We then show that the new environement ef is valid *)
           apply (case_tac "\<not> (valid_env ef)")
     apply simp
      apply (case_tac "\<not> (valid_stack (Ok (g + gend - (gcall + ccall), Suc pc, p, e) # list))")
     using validstack_Ok validstack_Ok_aux2 apply blast
     using validstack_Ok2 apply blast
     apply auto[1]
     apply (meson neq0_conv)
     apply (meson neq0_conv)
     apply (meson valid_env.elims(3) validstack_Ok validstack_Ok2 validstack_Ok_aux2)
     apply (meson not_gr0)
     apply (meson neq0_conv)
     apply (meson valid_env.elims(3) validstack_Ok validstack_Ok2 validstack_Ok_aux2)
     apply (case_tac x)
     apply auto[1]
     apply (case_tac x)
     apply auto[1]
     apply auto
     apply (simp add: notValidStackExceptionException)
     using valid_stack.simps(16) validstack_exception_step apply blast
     using valid_stack.simps(17) validstack_exception_step by blast

(* If a stack is valid then we can replace the program of the top frame by any valid program *)
lemma validstack_any_valid_prog: "(valid_stack (Ok(g,pc,p,e)#l) \<and> (valid_prog p2)) \<longrightarrow> (valid_stack (Ok (g, i, p2, e(name := (Some p2))) #l))"
  apply (induct l arbitrary: g pc p e p2 rule: valid_stack.induct )
  apply auto
  apply (case_tac "p!pc")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  apply (case_tac "p!pc")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  apply (meson not_gr0)
     apply (case_tac "a=0")
      apply auto
  apply (case_tac "p!pc")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
    apply (case_tac "a=0")
     apply auto
   apply (case_tac "p!pc")
       apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
  apply (meson valid_stack_aux.simps(11))
  apply (case_tac "p!pc")
  apply auto
  apply (meson neq0_conv)
  apply (meson neq0_conv)
    apply (case_tac "a=0")
     apply auto
  done

lemma validstack_smallstep: "(valid_stack l)\<longrightarrow> (valid_stack (smallstep l))"
  apply (case_tac l)
  apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac x1)
  (* (1) Ok on top *)
     apply (rename_tac y g pc p e)
     apply (case_tac "p.(pc)")
         apply auto[1]
         apply (simp add: validstack_exception_step)  
         (* Local case *)
         apply (rename_tac n)
         apply (case_tac "n>0 \<and> n\<le>g")
         apply auto[1]
         using validstack_Ok apply blast
         apply (case_tac "n\<le>0")
         apply auto[1]
         apply (case_tac "list=[]")
         apply auto[1]
         apply (metis instr.distinct(11) less_numeral_extra(3) validInstr valid_instr.simps(1))
         apply (case_tac "valid_prog p")
         apply (metis instr.distinct(11) less_numeral_extra(3) validInstr valid_instr.simps(1))
         using validstack_Ok_prog apply blast
         apply (simp add: validstack_exception_step)
         (* Call case *)
         apply (case_tac x3)
         apply (rename_tac z gcall ccall name)
         apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length list)+1)<stack_lim)\<and>((gcall+ccall)\<le>g)")
         apply auto[1]
         apply (case_tac "e(name)")
         apply auto[1]
         using validstack_Ok_env apply auto[1]
         apply (case_tac "\<not>(valid_env e)")
         apply auto[1]
         apply auto[1]
         (* This is the case where call mimic a create. 
            We first prove that adding a frame where the program is empty is valid and then we use the lemma validstack_any_valid_prog 
            stating that this program can be replaced by any (arbitrary) valid program *)
         apply (case_tac "valid_stack ((Ok (ccall, 0, [], e(name := Some []))) # Ok (g, pc, p, e) # list)")
         apply (meson any_valid_is_valid validstack_Ok2 validstack_Ok_env validstack_any_valid_prog)
         apply auto[1]
         apply (metis (full_types) option.simps(5) valid_prog.simps(1))
         using validstack_Ok_aux apply auto[1]
         apply auto[1]
         apply (metis option.simps(5) valid_env.elims(2) validstack_Ok_env)
         using validstack_Ok_env apply auto[1]
         using validstack_Ok_aux apply blast
         apply auto[1]
         using validstack_exception_step apply blast
         using validstack_exception_step apply blast
         using validstack_exception_step apply blast
         apply (simp add: validstack_exception_step)
         apply (metis instr.distinct(15) less_numeral_extra(3) validInstr valid_instr.simps(4) validstack_Ok_prog)
         using validstack_exception_step apply blast
         using validstack_exception_step apply blast
         apply (metis instr.distinct(15) less_numeral_extra(3) validInstr valid_instr.simps(4) validstack_Ok_prog)
         using validstack_exception_step apply blast
         apply (simp add: validstack_exception_step)
         apply auto[1]
         using validstack_Ok_env validstack_halt_step apply blast
         (* Jump case *)
         apply (case_tac x5)
         apply simp
         apply (metis instr.distinct(19) less_numeral_extra(3) validInstr valid_instr.simps(5) validstack_Ok validstack_Ok_prog validstack_exception_step)
 (* (2) Exception on top *) 
      apply (simp add: validstack_exception_top)
 (* (3) Halt on top *)
          apply (simp add: validstack_halt_top)
 (* (4) Invalid frame on top *)
         by (simp add: invalid_invalid)

function (sequential,domintros)  execute :: "call_stack \<Rightarrow> frame"
  where 
  "execute ([]) = Invalid_frame"|
  "execute ([Halt (g,e)]) = (Halt (g,e))"|
  "execute ([Exception]) = (Exception)"|
  "execute ([Invalid_frame]) = Invalid_frame"|
  "execute l = (if (length l > stack_lim) then Invalid_frame else execute (smallstep l)) "
  apply pat_completeness
  apply auto
  done


(* --------------------- Examples of runs of the execute function --------------------------------*)

(* See the examples below, after the proofs *)

(*________________________________Termination proof________________________________________________*)

(* _________________________ Some difficult step __________________________________________________*)

lemma ok_nil : "instr.Nil = mynth p pc \<longrightarrow> n = length l \<longrightarrow> (order n ((Ok (g,pc,p,e))#l))> (order n (smallstep ((Ok (g,pc,p,e))#l)))"
  by (metis (no_types, lifting) Suc_1 add_Suc_right get_gas_frame.simps(2) get_gas_frame.simps(4) instr.simps(24) le_imp_less_Suc less_add_Suc2 less_imp_le_nat numeral_3_eq_3 numerals(2) order_rev_length smallstep.simps(1))


lemma ok_local_caseinf : "x \<le> 0 \<longrightarrow> Local x = mynth p pc \<longrightarrow> n = length l \<longrightarrow> smallstep (Ok (g, pc, p, e) # l) = [Invalid_frame]"
  by (smt instr.simps(25) le_zero_eq less_numeral_extra(3) smallstep.simps(1))
  
lemma ok_local_casesup : " \<not> x \<le> 0 \<longrightarrow>
    \<not> g < x \<longrightarrow> Local x = mynth  p pc  \<longrightarrow>  (smallstep (Ok (g, pc, p, e) # l)) = ((Ok (g-x,pc+1,p,e))#l) "
  by (smt instr.simps(25) leI smallstep.simps(1))

lemma ok_local_casesup_2 : "\<not> x \<le> 0 \<longrightarrow>
    \<not> g < x \<longrightarrow>  Local x = mynth  p pc  \<longrightarrow> get_gas_frame (((Ok (g,pc,p,e))#l) ! 0) > get_gas_frame ((smallstep ( (Ok (g,pc,p,e))#l)) ! 0 )"
  using ok_local_casesup by auto
  

lemma ok_local : "Local x = mynth p pc \<longrightarrow> n = length l \<longrightarrow> (order n ((Ok (g,pc,p,e))#l))> (order n (smallstep ((Ok (g,pc,p,e))#l)))"
  apply (case_tac "x\<le>0")
  apply (metis (no_types, lifting) One_nat_def Suc_less_eq get_gas_frame.simps(1) get_gas_frame.simps(4) length_greater_0_conv lessI less_add_Suc2 less_trans list.size(3) numeral_3_eq_3 ok_local_caseinf order.simps(3) order_rev_length)
  apply (case_tac "x>g")
  apply (smt Suc_1 add_Suc_right get_gas_frame.simps(2) get_gas_frame.simps(4) instr.simps(25) le_less_trans lessI less_add_Suc2 less_or_eq_imp_le not_le numeral_3_eq_3 numerals(2) order_rev_length smallstep.simps(1))
  by (metis (no_types) nth_Cons_0 ok_local_casesup ok_local_casesup_2 order_min_diff)


lemma ok_jump_aux : " (n>0) \<longrightarrow> (n\<le>g)\<longrightarrow>(pj<(length p))\<longrightarrow> Jump(n,pj) = mynth p pc \<longrightarrow> (smallstep ((Ok (g,pc,p,e))#l)) = ((Ok (g-n,pj,p,e))#l)"
  apply auto
  by (smt instr.simps(28) old.prod.case)

lemma ok_jump_case1 : " (n>0) \<longrightarrow> (n\<le>g)\<longrightarrow>(pj<(length p))\<longrightarrow> Jump(n,pj) = mynth p pc \<longrightarrow> (len = length l) \<longrightarrow> (order len (smallstep ((Ok (g,pc,p,e))#l))) < (order len ((Ok (g,pc,p,e))#l))"
proof -
  have "\<forall>n na. \<exists>nb. \<not> (na::nat) \<le> n \<or> na + nb = n"
    by (metis (full_types) le_iff_add)
  then obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    f1: "\<And>n na. \<not> n \<le> na \<or> n + nn na n = na"
    by metis
  have "n + nn g n = g \<longrightarrow> 0 < n \<longrightarrow> n \<le> g \<longrightarrow> pj < length p \<longrightarrow> Jump (n, pj) = mynth  p pc \<longrightarrow> len = length l \<longrightarrow> order len (smallstep (Ok (g, pc, p, e) # l)) < order len (Ok (g, pc, p, e) # l)"
    by (metis (no_types) add.left_neutral add_diff_cancel_left' add_mono_thms_linordered_field(1) get_gas_frame.simps(4) ok_jump_aux order_rev_length)
  then show ?thesis
    using f1 by blast
qed

  
lemma ok_jump_subcase : " n> 0 \<longrightarrow> Jump (n,pj) = mynth p pc \<longrightarrow> len = length l \<longrightarrow> (order len (smallstep ((Ok (g,pc,p,e))#l))) < (order len ((Ok (g,pc,p,e))#l))"
  apply (case_tac "n\<le>g")
  apply (case_tac "pj < (length p) ")
  using ok_jump_case1 apply blast
   apply simp
  apply (smt One_nat_def get_gas_frame.simps(2) get_gas_frame.simps(4) instr.simps(28) length_rev less_Suc_eq linorder_neqE_nat not_add_less2 nth_append_length numeral_3_eq_3 old.prod.case order_rev_length)
  apply auto
  by (smt Nat.add_diff_assoc add_diff_cancel_left' diff_is_0_eq get_gas_frame.simps(2) get_gas_frame.simps(4) instr.simps(28) leI le_add1 length_rev less_add_Suc2 nth_append_length numeral_3_eq_3 order_rev_length plus_1_eq_Suc prod.simps(2) zero_order(2) zero_order(3))
  
  

lemma ok_jump_case_1_2 : " n> 0 \<longrightarrow> Jump (n,pj) = mynth p pc \<longrightarrow> len = length l\<longrightarrow> len < stack_lim \<longrightarrow>  ((smallstep ((Ok (g,pc,p,e))#l)),((Ok (g,pc,p,e))#l)) \<in> measures (list_order stack_lim)"
  by (smt One_nat_def get_gas_frame.simps(2) get_gas_frame.simps(4) instr.simps(28) less_Suc_eq linorder_neqE_nat not_add_less2 numeral_3_eq_3 ok_jump_case1 old.prod.case order_list order_rev_length smallstep.simps(1))


lemma ok_jump : "n>0 \<longrightarrow> Jump (n,pj) = mynth p pc \<longrightarrow> length l < stack_lim \<longrightarrow> ((smallstep ((Ok (g,pc,p,e))#l)),((Ok (g,pc,p,e))#l)) \<in> measures (list_order stack_lim)"
  apply (subst smallstep.simps)
  using ok_jump_case_1_2 by auto
  

lemma ok_stop_aux : " Stop = mynth p pc \<longrightarrow> ((smallstep ((Ok (g,pc,p,e))#l)) =(( Halt (g,e)) # l))"
  apply auto
  done

lemma ok_stop : " Stop = mynth p pc \<longrightarrow> len = length l \<longrightarrow> (order len (smallstep ((Ok (g,pc,p,e))#l)))<(order len ( (Ok (g,pc,p,e))#l))"
  using get_gas_frame.simps(3) get_gas_frame.simps(4) ok_stop_aux order_rev_length by presburger

lemma modularityOrder1: "(length l < stack_lim) \<longrightarrow> ((order (length l) (a#l)) < (order (length l) (b#l))) \<longrightarrow> ((a#l,b#l)\<in> measures (list_order stack_lim))"
  apply (induct l)
   apply auto
  apply (metis list.size(3) list_order.simps order_list order_rev_length)
  apply (metis length_Cons order_rev_length)
  by (metis length_Cons list_order.simps order_list order_rev_length)
  
 

lemma exceptionOrder: "(length l < stack_lim) \<longrightarrow> (Exception#l,Ok(g,pc,p,e)#l) \<in> measures (list_order stack_lim)"
  by (metis One_nat_def Suc_lessI add_gr_0 get_gas_frame.simps(2) get_gas_frame.simps(4) less_add_Suc2 less_antisym not_numeral_less_one numeral_eq_one_iff order_list semiring_norm(86) zero_less_numeral)

lemma ok_call_order: "(length (Ok (g,pc,p,e)#l) < stack_lim) \<longrightarrow> g2<g \<longrightarrow> (Ok(g2,pc2,p2,env2)#(Ok (g,pc,p,e)#l),Ok (g,pc,p,e)#l)\<in> measures (list_order stack_lim)"
  apply (case_tac "(order ((length l)+1) (Ok(g2,pc2,p2,env2)#(Ok (g,pc,p,e)#l)))<(order ((length l)+ 1) (Ok (g,pc,p,e)#l))")
  apply (metis (no_types, lifting) One_nat_def list.distinct(1) list.size(4) list_order_pos order_equal)
  by (smt One_nat_def add_Suc add_Suc_right add_less_mono get_gas_frame.simps(4) length_Cons lessI list.size(4) nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 order.simps(5) order_rev_length)
  
lemma ok_call_possibilities: "(Call (gcall,ccall,name) = mynth p pc  \<and> (res = (smallstep (((Ok(g,pc,p,e)))#l)))) \<longrightarrow>
      (res=[Invalid_frame]\<or> res= Exception#l \<or> (\<exists> g2 pc2 p2 e2. (length (Ok(g,pc,p,e)#l)) < stack_lim \<and> res= (Ok(g2,pc2,p2,e2)#(Ok (g,pc,p,e)#l)) \<and> g2<g))"
  apply (case_tac "p!pc")
  apply simp
  apply simp
    apply (case_tac "\<not>(x3=(gcall, ccall, name))")
     apply auto[1]
    apply simp
    apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length (Ok(g,pc,p,e)#l))<stack_lim))\<and>((gcall+ccall)\<le>g)")
  apply (case_tac "e(name)")
      apply auto
  by (metis (no_types, hide_lams) add.commute less_add_same_cancel1 less_le_trans)
  
    
lemma ok_call : "(length l < stack_lim) \<longrightarrow>  Call (gcall,ccall,name) = mynth p pc  \<longrightarrow> ((smallstep (((Ok(g,pc,p,e)))#l)),((Ok (g,pc,p,e))#l)) \<in> measures (list_order stack_lim) "
  (* Eval of call, case 1: [Invalid_frame] *)
  apply (case_tac "(smallstep (((Ok(g,pc,p,e)))#l)) = [Invalid_frame]")
  using min_invalid_frame apply auto[1]
  (* Eval of call, case 2: Exception *)  
  apply (case_tac "(smallstep (((Ok(g,pc,p,e)))#l)) =  Exception#l")
  using exceptionOrder apply auto[1]
  apply (case_tac "(\<exists> g2 pc2 p2 e2. ((length (Ok(g,pc,p,e)#l)) < stack_lim) \<and> (smallstep (((Ok(g,pc,p,e)))#l)) = (Ok(g2,pc2,p2,e2)#(Ok (g,pc,p,e)#l)) \<and> g2<g)")
  using ok_call_order
  apply fastforce
  using ok_call_possibilities apply blast
  done


(*_________________________________Case 1 : Exception _____________________________________________*)

lemma case1_subcaseOK_Nil : "instr.Nil = mynth p pc \<longrightarrow> (smallstep (Exception # Ok (g, pc, p, e) # vb) = [Invalid_frame])"
  by simp

lemma case1_subcaseOk_Local : " Local x = mynth p pc \<longrightarrow> (smallstep (Exception # Ok (g, pc, p, e) # vb)) = [Invalid_frame]"
  by (smt instr.simps(25) smallstep.simps(4))

lemma case1_subcaseOK_call1 : "Call (gcall,ccall,name)  = mynth  p pc \<longrightarrow>((gcall+ccall)>g)|(gcall\<le>0)|(ccall\<le>0)\<longrightarrow> (smallstep (Exception # Ok (g, pc, p, e) # vb)) = [Invalid_frame] "
  apply (case_tac "(gcall+ccall)>g")
  apply (smt instr.simps(26) old.prod.case smallstep.simps(4))
  apply (case_tac "gcall\<le>0")
  apply (smt case_prod_conv instr.simps(26) smallstep.simps(4))
  apply (case_tac "ccall\<le>0")
  apply (smt case_prod_conv instr.simps(26) smallstep.simps(4))
  by blast

  

lemma case1_smallstep_OK: "(res= (smallstep (Exception # (Ok (g,pc,p,e))# vb))) \<longrightarrow> (res=[Invalid_frame] \<or> (\<exists> g2 pc2. res= Ok(g2,pc2,p,e)#vb \<and> g2<g))"
  apply (case_tac "p!pc")
  apply simp
  apply simp
  apply (case_tac x3)
  apply (rename_tac x gcall ccall name)
  apply (case_tac "gcall+ccall>g \<or> gcall\<le>0 \<or> ccall\<le>0")
  apply auto
  done



lemma case1 : " \<not> stack_lim < length (Exception # v # vb) \<longrightarrow> (smallstep (Exception # v # vb), Exception # v # vb) \<in> measures (list_order stack_lim)"
  apply (case_tac v)
  (* For Exception + Ok, first case, we continue on Ok *)
  apply (case_tac x1)
  apply (rename_tac y g pc p e)
  apply (case_tac "(\<exists> g2 pc2. (smallstep (Exception # (Ok (g,pc,p,e))# vb)= Ok(g2,pc2,p,e)#vb) \<and> g>g2)")
  apply (rename_tac y mg mpc mp me)
  apply (smt add_mono_thms_linordered_field(1) get_gas_frame.simps(4) length_Cons less_Suc_eq linorder_neqE_nat list.simps(3) list_order_pos order_equal order_rev_length)
  apply (metis case1_smallstep_OK leI list.inject list.simps(3) min_invalid_frame)
  using min_invalid_frame apply auto[1]
  using min_invalid_frame apply auto[1]
  using min_invalid_frame by auto
 
(*___________________case 2 ______________________________________________________________________*)

lemma case2_okTop: "((smallstep (Ok(g,pc,p,e) # va)) = res) \<longrightarrow>( 
          (res= [Invalid_frame] \<or> res= (Halt (g,e)#va) \<or> (res= (Exception#va)) 
            \<or> (\<exists> g2 pc2. res= (Ok(g2,pc2,p,e)#va) \<and> g2<g)) \<or> \<comment>\<open>Local inst case or jump\<close>
                (\<exists> g2 pc2 p2 e2. res= (Ok(g2,pc2,p2,e2)#Ok(g,pc,p,e)#va) \<and> g2<g) \<comment>\<open>Call case env may be augmented if contract call does not exist\<close>
              )"
  apply (case_tac "p!pc")
  apply simp
  apply simp
  apply auto[1]
  apply (case_tac x3)
  apply (case_tac "e c")
     apply auto[1]
  apply (metis (no_types, lifting) leI less_add_same_cancel2 less_le_trans)
  apply (metis mynth.simps ok_call_possibilities ok_stop_aux)
  apply simp
  apply (case_tac x5)
  apply auto[1]
  done

lemma case2 : "\<not> stack_lim < length ((Ok (g,pc,p,e))  # va)\<longrightarrow> (smallstep ((Ok (g,pc,p,e)) # va), (Ok (g,pc,p,e)) # va) \<in> measures (list_order stack_lim)"
  apply (case_tac "(\<exists> g2 pc2 p2 e2. (smallstep (Ok(g,pc,p,e) # va)) = (Ok(g2,pc2,p2,e2)#Ok(g,pc,p,e)#va) \<and> g2<g)")
   apply (case_tac "p!pc") (* Proof by case on the instruction at position pc in p *)
  apply (metis (no_types, lifting) length_Cons lessI mynth.elims nat_neq_iff ok_nil ok_stop_aux order_equal)
  apply (metis length_Cons lessI less_irrefl_nat mynth.elims ok_local ok_stop_aux order_equal)
  apply (case_tac x3)
  apply (metis antisym_conv3 length_Cons lessI mynth.simps ok_call ok_call_order ok_stop_aux)
  apply (metis antisym_conv3 length_Cons lessI mynth.simps ok_call_order ok_stop_aux)
  apply (case_tac x5)
  apply (smt instr.case(5) list.inject list.simps(3) mynth.simps not_Cons_self2 ok_stop_aux old.prod.case smallstep.simps(1))
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = [Invalid_frame]")
  using min_invalid_frame apply auto[1]
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = (Exception#va)")
  apply (metis Suc_lessI add_gr_0 get_gas_frame.simps(2) get_gas_frame.simps(4) le_imp_less_Suc length_Cons nat_1_add_1 not_add_less2 not_less numeral_2_eq_2 numeral_3_eq_3 order_list zero_less_numeral)
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = (Halt (g,e)#va)")
  apply (metis add_less_cancel_left get_gas_frame.simps(3) get_gas_frame.simps(4) leI le_imp_less_Suc length_Cons lessI numeral_2_eq_2 numeral_3_eq_3 order_list)
  apply (case_tac "(\<exists> g2 pc2. (smallstep (Ok(g,pc,p,e) # va)) = (Ok(g2,pc2,p,e)#va) \<and> g2<g)")
  apply (metis (no_types, lifting) add_lessD1 add_mono_thms_linordered_field(1) antisym_conv3 get_gas_frame.simps(4) length_Cons lessI list.size(4) order_list) 
  using case2_okTop apply blast
  done 


(*__________________case 3_________________________________________________________________________*)


lemma case3 : "\<not> stack_lim < length (Invalid_frame # v # vb) \<longrightarrow> (smallstep (Invalid_frame # v # vb), Invalid_frame # v # vb) \<in> measures (list_order stack_lim)"
  using min_invalid_frame by auto
  
(*___________________case 4________________________________________________________________________*)

 
  
(* When halting correctly, we end up on a stack with an Ok with good property, or we end up with an Invalid_frame *)
lemma case4_haltTop: "((smallstep (Halt x # ((Ok(g,pc,p,e) # vc)))) = res) \<longrightarrow> (res= [Invalid_frame] \<or> (res= Exception # (Ok(g,pc,p,e) # vc)) \<or> (\<exists> g2 e2. res= (Ok(g2,pc+1,p,e2)#vc) \<and> g2<g))"
  apply (case_tac x)
  apply (case_tac "p!pc")  (* Proof by case on the instruction at position pc in p *)
  apply auto [1]
  apply auto [1]
  (* Call case *)
  apply (case_tac x3)
  apply (rename_tac y gcall ccall name)
  apply (case_tac x)
  apply (rename_tac gend ef)
  apply simp
  apply (case_tac "gcall+ccall>g")
  apply auto [1]
  apply (case_tac "gcall\<le>0")
  apply auto [1]
  apply (case_tac "ccall\<le>0")
  apply auto [1]
  apply (case_tac "ccall\<le>gend")
  apply auto [1]
  apply auto[1]
  apply auto
  done

lemma case4_subcaseHalt : "\<not> stack_lim < length (Halt x # vb # vc) \<longrightarrow> (smallstep (Halt x # vb # vc), Halt x # vb # vc) \<in> measures (list_order stack_lim)"
  apply (case_tac vb)
  (* vb=Ok*)
  apply (case_tac x1)
  apply (rename_tac y g pc p e)
  apply (case_tac "smallstep (Halt x # vb # vc) = [Invalid_frame]")
  using min_invalid_frame apply auto[1]
  apply (case_tac "smallstep (Halt x # vb # vc) = Exception # vb # vc")
  apply (metis One_nat_def frame.distinct(11) frame.distinct(3) frame.distinct(7) get_gas_frame.elims get_gas_frame.simps(2) length_Cons not_add_less2 not_less_eq numerals(2) order_list)
  apply (case_tac "\<not>(\<exists> g2 e2. smallstep (Halt x # vb # vc) = (Ok(g2,pc+1,p,e2)#vc) \<and> g2<g)")
  using case4_haltTop apply blast
  apply auto[1]
  apply (smt add_mono_thms_linordered_field(1) get_gas_frame.simps(4) length_Cons less_Suc_eq linorder_neqE_nat list.distinct(1) list_order.simps list_order_pos order_equal order_rev_length)
  using min_invalid_frame apply auto[1]
  using min_invalid_frame apply auto[1]
  using min_invalid_frame by auto
  
lemma case4: "\<not> stack_lim < length (v # vb # vc) \<longrightarrow> (smallstep (v # vb # vc), v # vb # vc) \<in> measures (list_order stack_lim)"
  apply (case_tac v)
  apply (metis (no_types, lifting) case2 case4_subcaseHalt frame.distinct(1) frame.distinct(5) get_gas_frame.elims)  
  using case1 apply blast
  using case4_subcaseHalt apply blast
  using case3 by blast

(* --------------------------- The termination theorem ---------------------------------------------*)

termination execute
  apply (relation "measures (list_order stack_lim)")
  apply simp
  using case2 apply force
  using case1 apply blast
  using case3 apply blast
  using case4 by blast

(* --------------------------- The soundness theorem ---------------------------------------------*)
lemma finalLength : "(length l\<le> stack_lim) \<longrightarrow> (length (smallstep l)\<le> stack_lim)"
  apply (induct l rule:smallstep.induct)
  apply auto
  apply (case_tac "p!pc")
  apply auto
  apply (case_tac "e b")
  apply auto
  apply (case_tac "p!pc")
  apply auto
  apply (case_tac "p!pc")
  apply auto
  apply (metis Suc_leI length_Cons)
  apply (case_tac "p!pc")
  apply auto
  apply (case_tac "p!pc")
  apply auto
  by (simp add: Suc_leI min_stack_lim)


lemma finalSoundnessTheorem: "(valid_stack l \<and> (length l \<le> stack_lim)) \<longrightarrow> (valid_stack [(execute l)])"
  apply (induct l rule:execute.induct)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  using finalLength validstack_smallstep apply auto[1]
  apply (simp add: finalLength validstack_exception_top)
  apply simp
  by (simp add: finalLength validstack_smallstep)


(* For running test cases only... we define a default value for stack_lim *)
(* ----------------------------------- Examples --------------------------------------- *)

(* (testSem i s) performs at most i steps of EVM semantincs on a call_stack s *)
fun testSem:: "nat \<Rightarrow> call_stack \<Rightarrow> call_stack"
  where 
"testSem 0 fs = fs" |
"testSem (Suc x) fs = (testSem x (smallstep fs))"

(* An example environement for a test execution of the semantics *)
definition "(exenv1::env)= (\<lambda>x. None)"       (* l'env vide *)
definition "(exenv2::env)= exenv1 (''c1'':= Some [(Call(1,10,''c2'')),Stop])"  (* useless for the test *)
definition "(exenv3::env)= exenv2 (''c2'':= Some [(Call(1,5,''c3'')),Stop])"
definition "(exenv4::env)= exenv3 (''c3'':= Some [Local(3),Stop])"       

value "exenv4(''c1'')"  
value "exenv4(''c2'')"  
value "exenv4(''c3'')" 


(* An example stack for running the test *)
definition "exstack= [Ok(18,0,[(Call(1,10,''c2'')),Stop],exenv4)]"

(* A maximal call stack size defined for tests *)
lemma stack_lim[code]: "stack_lim=4"
  sorry

(* The function returning an arbitrary program (CREATE) for test only *)
lemma any_valid[code]: "any_valid_program x= [Stop]"
  sorry

value "testSem 0 exstack"
value "testSem 1 exstack"
value "testSem 2 exstack"
value "testSem 3 exstack"
value "testSem 4 exstack"
value "testSem 5 exstack"
value "testSem 6 exstack"
value "testSem 7 exstack"
value "testSem 8 exstack"
value "testSem 9 exstack"

definition "invalidStack= [Exception,Ok(18,0,[],exenv4),Exception]"
value "(testSem 1 invalidStack)"
value "(testSem 2 invalidStack)"



end