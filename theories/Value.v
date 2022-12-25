Require Import Ensembles.
Require Import Variables.
Require Import Lattice.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Lifetime.
(* Scheme equality eq_dec, Scheme Boolean Equality beq, search for eq_A*)

Module Value.

    Definition location : Type := sum (Var.t * Lifetime.t) nat.

    Inductive kind : Set :=
    | Owned : kind (* black square *)
    | Borrowed : kind (* white circle *)
    | Trc : bool -> kind. (* losange *)

    Inductive value : Type := 
        | Unit : value
        | Int : nat -> value
        | Location : location -> kind -> value.

    Definition partialValue : Type := option value.

End Value.