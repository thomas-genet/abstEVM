theory abstEvm2
  imports Main 
begin 

(* Isabelle 2018 *)
section \<open>Second EVM abstract semantics : implementations of EVM\<close>

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

subsection \<open>Specific assumptions : EVM implementations\<close> 

text \<open>Assumptions coherent with EVM implementations:
  - A call consumes the gas at the call site, i.e., 
    call to contract c2 in contract c1 updates immediately
    the gas in contract c1 before stacking the frame of contract c2.
  - A successful call can result into a gas refund.
  \<close>

subsection \<open>Main datatypes\<close>

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


type_synonym env= "contractName \<Rightarrow> program option"

subsection \<open>Valid instructions, programs, environments, frames, stacks\<close>

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
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall\<le>0) | (ccall\<le>0)) then False
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
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall\<le>0) | (ccall\<le>0)) then False
                                     else ((valid_prog p) \<and> (valid_env e) \<and> (valid_stack_aux (Ok(g2,pc2,p2,env2)#l))))
        | _ \<Rightarrow> False)" |
  "valid_stack ((Ok (g,pc,p,e))#_) = False" |
  "valid_stack ((Halt (g,e))#Ok(g2,pc,p,env2)#l) = 
      (case p.(pc) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall\<le>0) | (ccall\<le>0)) then False
                                    else ((valid_env e) \<and> (valid_stack_aux (Ok(g2,pc,p,env2)#l))))
        | _ \<Rightarrow> False)" |
  "valid_stack ((Halt (g,e))#_) = False" |
  "valid_stack ((Exception)#Ok(g2,pc,p,env2)#l) = (case p.(pc) of 
          Call(gcall,ccall,name) \<Rightarrow> (if ((gcall\<le>0) | (ccall\<le>0)) then False
                                    else (valid_stack_aux (Ok(g2,pc,p,env2)#l)))
        | _ \<Rightarrow> False)"|
  "valid_stack ((Exception)#_) = False"|
  "valid_stack (Invalid_frame#l) = False"

subsection \<open>Measure definition\<close>

(* We associate gas for exception/Invalid frame for the termination measures *)
fun get_gas_frame :: "frame \<Rightarrow> nat"
  where
  "get_gas_frame Invalid_frame = 0"|
  "get_gas_frame Exception = 0"|
  "get_gas_frame (Halt (g,e)) = g"|
  "get_gas_frame (Ok (g,pc,p,e)) = g"

value "get_gas_frame Exception"
value "get_gas_frame Invalid_frame"

fun sum_gas :: "call_stack \<Rightarrow> nat "
  where
  "sum_gas [] = 0"|
  "sum_gas (a#l) = (get_gas_frame a)+(sum_gas l)"

fun top_frame_measure:: "call_stack \<Rightarrow> nat"
  where
"top_frame_measure [] = 0" |
"top_frame_measure ((Ok _)#_) = 3"|
"top_frame_measure ((Halt _)#_) = 2"|
"top_frame_measure (_#_) = 1"

definition "(list_order :: (call_stack \<Rightarrow> nat) list) = [sum_gas, length, top_frame_measure]"

value "(list_order)!0"
value "(list_order)!1"

fun demoMeasure:: "call_stack \<Rightarrow> nat list"
  where
"demoMeasure l = (List.map (\<lambda> f. (f l)) list_order)"

(* Recall that a call stack is a list of frames where the most recent frame is at the beginning of the list *)
value "demoMeasure [Ok (18,pc,p,e)]" 
value "demoMeasure [Ok (10,pc2,p2,e_2),Ok (7,pc,p,e)]"
value "demoMeasure [Ok (8,pc2,p2,e_2),Ok (7,pc,p,e)]"
value "demoMeasure [Halt (8,e_2),Ok (7,pc,p,e)]"
value "demoMeasure [Ok (15,pc,p,e)]"

value "demoMeasure [Ok (18,pc,p,e)]" 
(* After a call 10 given to contract c1, the stack become *)
value "demoMeasure [Ok (10,pc2,p2,e_2),Ok (7,pc,p,e)]"
(* After a call 5 given to contract c2, the stack becomes  *)
value "demoMeasure [Ok (5,pc3,p3,e_2),Ok (4,pc2,p2,e2),Ok (7,pc,p,e)]"
value "demoMeasure [Halt(2,e_4),Ok (4,pc2,p2,e2),Ok (7,pc,p,e)]" (* We assume that contract c2 ends with 2 gas *)
value "demoMeasure [Ok (6,pc2,p2,e_2),Ok (7,pc,p,e)]" (* We return from the contract c2*)
value "demoMeasure [Halt (6,e_2),Ok (7,pc,p,e)]"   (* Contract c1 ends with 7 gas *)
value "demoMeasure [Ok (13,pc,p,e)]"               (* We return from the contract c1 *)

value "demoMeasure [Exception, Ok (5,pc2,p2,e_2),Ok (7,pc,p,e)]"

(*____________________________Some lemmas on order______________________________________ *)

lemma gas_order: "sum_gas a < sum_gas b \<longrightarrow> ((a,b) \<in> (measures list_order))"
  by (simp add: list_order_def)

lemma gas_order2: "sum_gas a = sum_gas b \<and> (length a < length b) \<longrightarrow> ((a,b) \<in> (measures list_order))"
  by (simp add: list_order_def)

lemma gas_order3: "sum_gas a = sum_gas b \<and> (length a = length b) \<and> (top_frame_measure a < top_frame_measure b)\<longrightarrow> ((a,b) \<in> (measures list_order))"
  by (simp add: list_order_def)

lemma min_invalid_frame : "\<not>(i =[Invalid_frame] \<or> i = []\<or>(i=[Exception])) \<longrightarrow> ([Invalid_frame],i) \<in> (measures list_order)"
  apply auto
  apply (case_tac i)
  apply simp
  apply (case_tac a)
  apply auto
  apply (rename_tac g pc p e)
  apply (case_tac g)
  apply (smt comm_monoid_add_class.add_0 get_gas_frame.simps(1) in_measures(2) length_greater_0_conv less_add_Suc2 less_add_same_cancel2 list.size(4) list_order_def nat_1_add_1 not_gr_zero numeral_2_eq_2 numeral_3_eq_3 sum_gas.simps(1) sum_gas.simps(2) top_frame_measure.simps(2) top_frame_measure.simps(5))
  apply (simp add: gas_order)
  apply (metis get_gas_frame.simps(1) gr0I in_measures(2) length_Cons length_greater_0_conv less_add_same_cancel2 list.size(4) list_order_def sum_gas.simps(1) sum_gas.simps(2))
  apply (metis One_nat_def comm_monoid_add_class.add_0 get_gas_frame.simps(1) in_measures(2) lessI less_add_same_cancel2 list.size(3) list.size(4) list_order_def not_gr_zero numeral_2_eq_2 sum_gas.simps(1) sum_gas.simps(2) top_frame_measure.simps(3) top_frame_measure.simps(5))
  by (metis comm_monoid_add_class.add_0 get_gas_frame.simps(1) gr0I in_measures(2) length_greater_0_conv less_add_same_cancel2 list.size(4) list_order_def sum_gas.simps(1) sum_gas.simps(2))


(*_______________________Semantics______________________________________________________________*)

subsection \<open>Semantics\<close>

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
                                                                                    (let pnew=(any_valid_program 0) in ((Ok (ccall,0,pnew,e( name := (Some pnew) )))#(Ok (g-gcall-ccall,pc,p,e))#l))
                                                                            \<comment>\<open>Otherwise, we create a new frame where the current program becomes pcall \<close>
                                                                               | (Some pcall) \<Rightarrow>((Ok (ccall,0,pcall,e))#(Ok (g-gcall-ccall,pc,p,e))#l))
                                                            else ( if (((length l)\<ge>(stack_lim - 1))|((gcall+ccall)>g)) then  (Exception#l)
                                                                   else ([Invalid_frame]) )                  
                             )"|
  "smallstep ([Halt (g,e)]) = [Halt (g,e)] "|
  "smallstep ([Exception]) =[Exception] "|
                                                  \<comment> \<open>Call return with an exception\<close>
  "smallstep ( (Exception)#(Ok (g,pc,p,e))#l ) = (case p.(pc) of
                                                                              \<comment>\<open>if running the call was impossible initially then we produce an invalid_frame
                                                                                 Only here for totality reasons (cannot happend)\<close>
                                                   Call(gcall,ccall,name) \<Rightarrow>  (if ((gcall\<le>0)|(ccall\<le>0)) then [Invalid_frame]  
                                                                               \<comment> \<open>Normal call return with an exception: we consume the gas: gcall and ccall\<close>
                                                                               else  ((Ok (g,(pc+1),p,e))#l))
                                                  | _ \<Rightarrow> [Invalid_frame] )"|
                                               \<comment> \<open>Standard call return with a regular Halt event\<close>
 "smallstep ((Halt (gend,ef))#(Ok (g,pc,p,e))#l) = (case p.(pc) of 
                                                  Call(gcall,ccall,name) \<Rightarrow>  if (gcall\<le>0) then [Invalid_frame]
                                                                             else if (ccall\<le>0) then [Invalid_frame] 
                                                                              \<comment>\<open>The resulting (modified) environment ef is passed to the current OK top stack_frame\<close>
                                                                             else  ((Ok ((g+gend),(pc+1),p,ef))#l)|
                                                  _ \<Rightarrow> [Invalid_frame] )"|
  "smallstep l = [Invalid_frame]"

subsection \<open>Validity proof\<close>

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
         apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length list)+1)<stack_lim)")
        apply auto[1]
         using validstack_Ok validstack_Ok_aux2 apply blast
              apply auto         
         using validstack_Ok validstack_Ok_aux2 apply blast
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
     using validstack_Ok validstack_Ok2 apply blast
     apply auto[1]
     apply (meson not_gr_zero)
     apply (meson valid_env.elims(3) validstack_Ok validstack_Ok2 validstack_Ok_aux2)
     apply (meson not_gr_zero)
     apply (meson valid_env.elims(3) validstack_Ok validstack_Ok2 validstack_Ok_aux2)
     apply (meson not_gr0)
     apply (meson valid_env.elims(3) validstack_Ok validstack_Ok2 validstack_Ok_aux2)
     apply (case_tac x)
     apply auto[1]
     apply (case_tac x)
     apply auto[1]
       apply (meson neq0_conv)
     apply (simp add: notValidStackExceptionException)
     using valid_stack.simps(16) validstack_exception_step apply blast
     apply (case_tac x)
     apply auto
     done
     
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

subsubsection \<open>Main Validity Theorem for one step of semantics\<close>

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
                apply (case_tac "valid_stack ((Ok (ccall, 0, [], e(name := Some []))) # Ok (g-gcall-ccall, pc, p, e) # list)")
                 apply (metis any_valid_is_valid diff_diff_left valid_env.elims(3) validstack_Ok2 validstack_any_valid_prog)
         apply auto[1]
         apply (metis (full_types) option.simps(5) valid_prog.simps(1))
         using validstack_Ok validstack_Ok_aux apply blast      
         using validstack_Ok_aux apply auto[1]
         apply (metis option.simps(5) valid_env.elims(2) validstack_Ok_env)
         using validstack_Ok_env apply auto[1]
         using validstack_Ok apply blast
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

subsection \<open>Semantics : complete execution\<close>

function (sequential)  execute :: "call_stack \<Rightarrow> frame"
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

subsubsection \<open>Termination proof\<close>

(* _________________________ Some difficult lemmas __________________________________________________*)

subsection \<open>Some technical lemmas\<close>


lemma exceptionOrder: "(Exception#l,Ok(g,pc,p,e)#l) \<in> (measures list_order)"
  by (metis comm_monoid_add_class.add_0 gas_order gas_order3 get_gas_frame.simps(2) length_Cons less_add_Suc2 less_antisym nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3 sum_gas.simps(2) top_frame_measure.simps(2) top_frame_measure.simps(4))
  
lemma ok_call_order: "g2+g3<g \<longrightarrow> (Ok(g2,pc2,p2,env2)#(Ok (g3,pc,p,e)#l),Ok (g,pc,p,e)#l)\<in> (measures list_order)"
  by (simp add: gas_order)
 
lemma ok_call_possibilities: "(Call (gcall,ccall,name) = mynth p pc  \<and> (res = (smallstep (((Ok(g,pc,p,e)))#l)))) \<longrightarrow>
      (res=[Invalid_frame]\<or> res= Exception#l \<or> (\<exists> g2 g3 pc2 p2 e2. (length (Ok(g,pc,p,e)#l)) < stack_lim \<and> res= (Ok(g2,pc2,p2,e2)#(Ok (g3,pc,p,e)#l)) \<and> g2+g3<g))"
  apply (case_tac "p!pc")
  apply simp
  apply simp
  apply (case_tac "(x3=(gcall, ccall, name))")
  apply (case_tac "(gcall>0)\<and>(ccall>0)\<and>(((length (Ok(g,pc,p,e)#l))<stack_lim))\<and>((gcall+ccall)\<le>g)")
  apply (case_tac "e(name)")
  apply simp
  apply (metis (no_types, lifting) add_diff_inverse_nat add_mono_thms_linordered_field(1) less_add_same_cancel2 not_less)
  apply (case_tac "\<not>(\<exists> newp. (res= (Ok (ccall, 0, newp, e(name \<mapsto> newp))) # (Ok (g - (gcall + ccall), pc, p, e)) # l))")
  apply simp
  apply (case_tac "gcall\<le>0")
  apply simp
  apply (case_tac "ccall\<le>0")
  apply simp
  apply (case_tac "((length (Ok(g,pc,p,e)#l))\<ge>stack_lim)")
  apply auto
done

subsubsection \<open>Case 1 : Exception\<close>

(*_________________________________Case 1 : Exception _____________________________________________*)

lemma case1_smallstep_OK: "(res= (smallstep (Exception # (Ok (g,pc,p,e))# vb))) \<longrightarrow> (res=[Invalid_frame] \<or> (\<exists> pc2. res= Ok(g,pc2,p,e)#vb))"
  apply (case_tac "p!pc")
  apply simp
  apply simp
  apply (case_tac x3)
  apply (rename_tac x gcall ccall name)
  apply (case_tac "gcall\<le>0 \<or> ccall\<le>0")
  apply auto
  done

lemma case1 : "(smallstep (Exception # v # vb), Exception # v # vb) \<in> (measures list_order)"
  apply (case_tac v)
  (* For Exception + Ok, first case, we continue on Ok *)
  apply (case_tac x1)
  apply (rename_tac y g pc p e)
  apply (case_tac "(\<exists> g2 pc2. (smallstep (Exception # (Ok (g,pc,p,e))# vb)= Ok(g2,pc2,p,e)#vb))")
  apply (rename_tac y mg mpc mp me)
  apply (metis case1_smallstep_OK comm_monoid_add_class.add_0 frame.distinct(5) gas_order2 get_gas_frame.simps(2) get_gas_frame.simps(4) length_Cons less_Suc_eq nth_Cons_0 sum_gas.simps(2))
  apply (metis case1_smallstep_OK list.distinct(1) list.inject min_invalid_frame)
  apply (simp add: min_invalid_frame)
  apply (simp add: min_invalid_frame)
  by (simp add: min_invalid_frame)
  
subsubsection \<open>Case 2 of termination proof\<close>

(*___________________case 2 ______________________________________________________________________*)

lemma case2_okTop: "((smallstep (Ok(g,pc,p,e) # va)) = res) \<longrightarrow>( 
          (res= [Invalid_frame] \<or> res= (Halt (g,e)#va) \<or> (res= (Exception#va)) 
            \<or> (\<exists> g2 pc2. res= (Ok(g2,pc2,p,e)#va) \<and> g2<g)) \<or> \<comment>\<open>Local inst case or jump\<close>
                (\<exists> g2 g3 pc2 p2 e2. res= (Ok(g2,pc2,p2,e2)#Ok(g3,pc,p,e)#va) \<and> g2+g3<g) \<comment>\<open>Call case env may be augmented if contract call does not exist\<close>
              )"
  apply (case_tac "p!pc")
  apply simp
  apply simp
  apply auto[1]
  apply (case_tac x3)
  apply (case_tac "e c")
  apply auto[1]
  apply (metis (no_types, lifting) add_diff_inverse_nat add_mono_thms_linordered_field(1) less_add_same_cancel2)
  apply auto[1]
  apply auto[1]
  apply (case_tac x5)
  apply auto[1]
  done

lemma case2 : "(smallstep ((Ok (g,pc,p,e)) # va), (Ok (g,pc,p,e)) # va) \<in> (measures list_order)"
  apply (case_tac "(\<exists> g2 g3 pc2 p2 e2. (smallstep (Ok(g,pc,p,e) # va)) = (Ok(g2,pc2,p2,e2)#Ok(g3,pc,p,e)#va) \<and> g2+g3<g)")
  using ok_call_order apply auto[1]
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = [Invalid_frame]")
  apply (simp add: min_invalid_frame)
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = (Exception#va)")
   apply (simp add: exceptionOrder)
  apply (case_tac "(smallstep (Ok(g,pc,p,e) # va)) = (Halt (g,e)#va)")
  apply (simp add: gas_order3)
    apply (case_tac "(\<exists> g2 pc2. (smallstep (Ok(g,pc,p,e) # va)) = (Ok(g2,pc2,p,e)#va) \<and> g2<g)")
  using gas_order apply auto[1]
  using case2_okTop by blast

subsubsection \<open>Case 3 of termination proof\<close>

(*__________________case 3_________________________________________________________________________*)


lemma case3 : "\<not> stack_lim < length (Invalid_frame # v # vb) \<longrightarrow> (smallstep (Invalid_frame # v # vb), Invalid_frame # v # vb) \<in> (measures list_order)"
  using min_invalid_frame by auto

subsubsection \<open>Case 4 of termination proof\<close>

(*___________________case 4________________________________________________________________________*)

 
  
(* When halting correctly, we end up on a stack with an Ok with good property, or we end up with an Invalid_frame *)
lemma case4_haltTop: "((smallstep (Halt(gend,ef) # ((Ok(g,pc,p,e) # vc)))) = res) \<longrightarrow> (res= [Invalid_frame] \<or> (res= Exception # (Ok(g,pc,p,e) # vc)) \<or> (res= (Ok(g+gend,pc+1,p,ef)#vc)))" 
  apply (case_tac "p!pc")  (* Proof by case on the instruction at position pc in p *)
  apply auto [1]
  apply auto [1]
  (* Call case *)
  apply (case_tac x3)
  apply (rename_tac y gcall ccall name)
  apply (case_tac "gcall\<le>0")
  apply auto [1]
  apply (case_tac "ccall\<le>0")
  apply auto [1]
  apply (case_tac "ccall<gend")
  apply auto
done

lemma case4_subcaseHalt : "(smallstep (Halt (gend,ef) # vb # vc), Halt (gend,ef) # vb # vc) \<in> (measures list_order)"
  apply (case_tac vb)
  (* vb=Ok*)
  apply (case_tac x1)
  apply (rename_tac y g pc p e)
  apply (case_tac "smallstep (Halt (gend,ef) # vb # vc) = [Invalid_frame]")
  using min_invalid_frame apply auto[1]
     apply (case_tac "smallstep (Halt (gend,ef) # vb # vc) = Exception # vb # vc")
  apply (metis One_nat_def add_cancel_right_left gas_order gas_order3 get_gas_frame.simps(2) lessI less_add_same_cancel2 list.size(4) numeral_2_eq_2 sum_gas.simps(2) top_frame_measure.simps(3) top_frame_measure.simps(4) zero_less_iff_neq_zero)
  apply (case_tac "smallstep (Halt(gend,ef) # vb # vc) = (Ok(gend+g,pc+1,p,ef)#vc)")
  apply (simp add: gas_order2)
  apply (metis add.commute case4_haltTop)
  apply (simp add: min_invalid_frame)
  apply (simp add: min_invalid_frame)
  apply (simp add: min_invalid_frame)
done
  
lemma case4: "(smallstep (v # vb # vc), v # vb # vc) \<in> (measures list_order)"
  apply (case_tac v)
  apply (metis (no_types, lifting) case2 case4_subcaseHalt frame.distinct(1) frame.distinct(5) get_gas_frame.elims)  
  using case1 apply blast
  using case4_subcaseHalt apply auto[1]
  by (simp add: min_invalid_frame)


subsubsection \<open>The main termination theorem\<close>

(* --------------------------- The termination theorem ---------------------------------------------*)

termination execute
  apply (relation "(measures list_order)")
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

subsection \<open>Test examples for the formal semantics\<close>

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

axiomatization
  (* A maximal call stack size defined for tests *)
  where stack_lim[code]: "stack_lim=4"
  (* The function returning an arbitrary program (CREATE) for test only *)
  and any_valid_program[code]: "any_valid_program x= [Stop]"

value "testSem 0 exstack"
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