
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import MSSL.Misc.
Require Import MSSL.LVal MSSL.Lattice.

Open Scope program_scope.

    Inductive total : Type := 
        | TUnit : total 
        | TInt : total 
        | TRef : bool -> Ensemble lval -> total
        | TTRC : total -> total
        | TBox : total -> total.

    Inductive moved : Type :=
        | TMoved : total -> moved
        | TMBox : moved -> moved.
    
    Definition partial : Type := sum total moved.

    Definition lift_total : total -> partial := (@inl total moved).
    Definition lift_moved : moved -> partial := (@inr total moved).

    Coercion lift_total : total >-> partial.
    Coercion lift_moved : moved >-> partial.

    Inductive lt : relation partial := 
        | lt_unit : lt TUnit TUnit
        | lt_int : lt TInt TInt
        | lt_ref : forall b l1 l2,
            Included _ l1 l2  -> lt (TRef b l1) (TRef b l2)
        | lt_trc : forall (t1 t2 : total),
            lt t1 t2 -> lt (TTRC t1) (TTRC t2)
        | lt_box1 : forall (t1 t2 : total),
            lt t1 t2 -> lt (TBox t1) (TBox t2) 
        | lt_box2 : forall (t1 : total) (t2 : moved),
            lt t1 t2 -> lt (TBox t1) (TMBox t2) 
        | lt_box3 : forall (t1 t2 : moved),
            lt t1 t2 -> lt (TMBox t1) (TMBox t2) 
        | lt_undef1 : forall (t1 t2 : total),
            lt t1 t2 -> lt (TMoved t1) (TMoved t2)
        | lt_undef2 : forall (t1 t2 : total),
            lt t1 t2 -> lt t1 (TMoved t2)
        | lt_undef3 : forall (t1 : total) (t2 : total),
            lt t1 (TMoved t2) -> lt (TBox t1) (TMoved (TBox t2))
        | lt_undef4 : forall (t1 : moved) (t2 : total),
            lt t1 (TMoved t2) -> lt (TMBox t1) (TMoved (TBox t2)).

Lemma lt_moved_total : forall (t1 : moved) (t2 : total), lt t1 t2 -> False.
Proof.
    intros t1 t2 Ha.
    dependent induction Ha.
Qed.

Lemma lt_moved : forall (t1 t2 : total), lt (inl t1) (TMoved t2) -> lt t1 t2.
Proof.
    intros t1 t2 Ha.
    dependent induction Ha; auto using lt_box1, JMeq_refl.
Qed.

Lemma lt_refl : forall t, lt t t.
Proof.
    assert (forall t : total, lt t t) as Ha by
        (induction t; auto using lt, reflexivity).
    destruct t; [apply Ha | induction m; auto using lt]. 
Qed.

Lemma lt_trans : forall t1 t2, lt t1 t2 -> forall t3, lt t2 t3 -> lt t1 t3.
Proof.
    intros t1 t2 Ha.
    dependent induction Ha; intros t3 Hb.
    -   assumption.
    -   assumption.
    -   destruct t3 as [ [  ] | [ t |  ] ]; try solve [inversion Hb].
        +   inversion Hb; subst.
            eauto using lt_ref, transitivity.
        +   dependent destruction Hb.
            destruct t; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef2.
            eauto using lt_ref, transitivity.
    -   destruct t3 as [ [  ] | [ t |  ] ]; try solve [inversion Hb].
        +   inversion Hb; subst.
            *   apply lt_trc.
                apply IHHa.
                assumption.
        +   dependent destruction Hb.
            destruct t; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef2.
            apply lt_trc; apply IHHa; assumption.
    -   destruct t3 as [ [  ] | [ t |  ] ]; try solve [inversion Hb].
        +   inversion Hb; subst.
            apply lt_box1; apply IHHa; assumption.
        +   dependent destruction Hb.
            destruct t; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef2.
            apply lt_box1; apply IHHa; assumption. 
            * apply lt_undef2.
                apply lt_box1.
                apply IHHa.
                apply lt_moved.
                assumption.
        +   inversion Hb; subst.
            apply lt_box2.
            apply IHHa; assumption.
    -   destruct t3 as [ [  ] | [ t |  ] ]; try solve [inversion Hb].
        +   destruct t; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef3.
            apply IHHa; assumption.
        +   apply lt_box2.
            inversion Hb; subst.
            apply IHHa; assumption.
    -   destruct t3 as [ [  ] | [ t |  ] ]; try solve [inversion Hb].
        +   destruct t; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef4.
            apply IHHa; assumption.
        +   apply lt_box3.
            inversion Hb; subst.
            apply IHHa; assumption.
    -   destruct t3; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        apply lt_undef1.
        apply IHHa; assumption. 
    -   destruct t3; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        apply lt_undef2.
        apply IHHa; assumption.
    -   destruct t3; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        destruct t3; (try inversion H1).
        subst.
        apply lt_undef2.
        apply lt_box1.
        apply lt_moved.
        apply IHHa.
        constructor.
        assumption.
    -   destruct t3 ; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        destruct t3; (try inversion H1;subst).
        apply lt_undef4.
        apply IHHa.
        apply lt_undef1; assumption.
Qed.

Lemma lt_antisymmetric_total : forall (t1 t2 : total), lt t1 t2 -> lt t2 t1 -> t1 = t2.
Proof.
    induction t1; intros.
    -   inversion H; reflexivity.
    -   inversion H; reflexivity.
    -   inversion H; inversion H0; subst; try auto.
        injection H5; intro; subst.
        replace e with l2.
        reflexivity.
        apply Extensionality_Ensembles; unfold Same_set; auto.
    -   inversion H; inversion H0; subst; try auto.
        injection H4; intros; subst.
        f_equal; eauto.
    -   inversion H; inversion H0; subst; try auto.
        injection H4; intros; subst.
        f_equal; eauto.
Qed.

Lemma lt_antisymmetric_moved : forall (t1 t2 : moved), lt t1 t2 -> lt t2 t1 -> t1 = t2.
Proof.
    intros t1 t2. revert t1.
    dependent induction t2; intros.
    -   inversion H; subst.
        +   inversion H0; subst.
            *   f_equal.
                now apply lt_antisymmetric_total.
        +   inversion H0; subst.
    -   inversion H; subst.
        +   inversion H0; subst.
            *   f_equal; auto.   
Qed.             


Lemma lt_antisymmetric : forall (t1 t2 : partial), lt t1 t2 -> lt t2 t1 -> t1 = t2.
Proof.
    intros t1 t2 Ha Hb.
    destruct t1, t2.
    -   f_equal.
        apply lt_antisymmetric_total.
        assumption.
        assumption.
    -   apply lt_moved_total in Hb.
        elim Hb.
    -   apply lt_moved_total in Ha.
        elim Ha.
    -   f_equal.
        apply lt_antisymmetric_moved.
        assumption.
        assumption.
Qed.

Definition lt' (t1 t2 : option partial) : Prop :=
    match (t1, t2) with
        |   (Some t1, Some t2) => lt t1 t2
        |   (None, _ ) => True 
        |   (Some _, None ) => False
    end.

#[export] Instance lt_Reflexive : Reflexive lt'.
Proof.
    intro x.
    destruct x; unfold lt'; auto using lt_refl.
Qed.

#[export] Instance lt_Transitive : Transitive lt'.
Proof.
    intros x y z H1 H2.
    destruct x, y, z; unfold lt' in *; eauto using lt_trans.
    elim H1.
Qed.

#[export] Instance lt_AntiSymmetric : Antisymmetric _ (@eq (option partial)) lt'.
Proof.
    intros x y Ha Hb.
    destruct x, y.
    f_equal.
    now apply lt_antisymmetric.
    inversion Ha.
    inversion Hb.
    reflexivity.
Qed.

#[export] Instance typePreorder : PreOrder lt'.
constructor.
apply lt_Reflexive.
apply lt_Transitive.
Qed.

#[export] Instance PartialOrderlt : PartialOrder eq lt'.
constructor.
-   intro.
    unfold relation_conjunction.
    unfold predicate_intersection.
    unfold pointwise_extension.
    split; subst.
    reflexivity.
    unfold flip.
    reflexivity.
-   unfold relation_conjunction.
    unfold predicate_intersection.
    unfold pointwise_extension.
    unfold lt'.
    intros [Ha Hb].
    unfold flip in Hb.
    destruct x, x0.
    f_equal.
    apply lt_antisymmetric.
    assumption.
    assumption.
    elim Ha.
    elim Hb.
    reflexivity.
Qed.

Fixpoint type_join (t1 t2 : option partial) : option partial := 
    match t1, t2 with 
        | _,_ => None 
    end.

#[export] Instance typeJoinLattice : JoinLattice (@eq (option partial)) lt' type_join.
Admitted.

