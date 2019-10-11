# Ethereum Formal Semantics for Gas Consumption

This is a formal semantics of Ethereum Virtual Machine (EVM) specialized for gas consumption analysis. This formal model is used for proving termination of any contract on EVM. The model is defined and property are proved using the [Isabelle/HOL proof assistant](https://isabelle.in.tum.de/), more precisely [Isabelle/HOL 2018](http://isabelle.in.tum.de/website-Isabelle2018/). The only assumptions made on EVM are:

* all EVM instructions have a cost strictly greater to zero (except the zero-cost operations like return, etc.).
* the call stack size is bounded by a natural number strictly greater to zero.
 
Other technical assumptions and abstractions are explained in the theory files. There are two theory files. The two theories differs on a very particular point: how gas is consumed when a contract is called from another one.

* `abstEvm.thy` where the EVM semantics is based on the reference yellow papers:[yellow paper 2014](http://gavwood.com/Paper.pdf) and [yellow paper 2019](https://ethereum.github.io/yellowpaper/paper.pdf).
* `abstEvm2.thy` where the EVM semantics is closer to the implementations of EVM.

The subtle differences between the two are explained in the comments at the beginning of the files.