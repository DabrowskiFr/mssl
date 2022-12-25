Require Import Lattice.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Module Lifetime.

    Parameter t : Type.
    Parameter glob : t.
    Parameter eq : relation t.
    Parameter lt : relation t.
    Parameter join : t -> t -> t.

    #[export] Declare Instance k : Equivalence eq.
    #[export] Declare Instance j : PreOrder lt.
    #[export] Declare Instance m : PartialOrder eq lt.
    #[export] Declare Instance i : MeetLattice eq lt join.

End Lifetime.