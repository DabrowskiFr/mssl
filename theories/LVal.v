Require Import Variables.

Inductive lval : Type :=
| LVar : Var.t -> lval 
| LDeref : lval -> lval.