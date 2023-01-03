
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
    
    Notation "⟙" := (@None (sum total moved)).

    Definition partial : Type := option (sum total moved).

    Definition lift_total : total -> partial := 
        fun x => (Some (@inl total moved x)).

    Definition lift_moved : moved -> partial := 
        fun x => (Some (@inr total moved x)).

    Coercion lift_total : total >-> partial.
    Coercion lift_moved : moved >-> partial.

    Inductive lt : relation partial := 
        | lt_top : forall t, lt t ⟙
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

Lemma lt_moved : forall (t1 t2 : total), lt t1 (TMoved t2) -> lt t1 t2.
Proof.
    intros t1 t2 Ha.
    dependent induction Ha; auto using lt_box1, JMeq_refl.
Qed.

Lemma lt_refl : forall t, lt t t.
Proof.
    assert (forall t : total, lt t t) as Ha by
        (induction t; auto using lt, reflexivity).
    destruct t; [ | apply lt_top].
    destruct s; [apply Ha | induction m; eauto using lt].
Qed.

Lemma lt_trans : forall t1 t2, lt t1 t2 -> forall t3, lt t2 t3 -> lt t1 t3.
Proof.
    intros t1 t2 Ha .
    dependent induction Ha; intros t3 Hb.
    -   inversion Hb; subst; apply lt_top.
    -   assumption.
    -   assumption.
    -   destruct t3 as [ [ ] | ].
        +   inversion Hb; subst.
            eauto using lt_ref, transitivity.
        +   dependent destruction Hb.
            destruct t2; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef2.
            eauto using lt_ref, transitivity.
        +   apply lt_top.
    -   destruct t3 as [ [  ] | ].
        +   inversion Hb; subst.
            apply lt_trc.
            now apply IHHa.
        +   dependent destruction Hb.
            destruct t3; try solve [inversion Hb].
            inversion Hb; subst.
            apply lt_undef2.
            apply lt_trc.
            now apply IHHa.
        +   apply lt_top.
    -   destruct t3 as [[ |  ] | ].
        +   inversion Hb; subst.
            apply lt_box1.
            now apply IHHa; assumption.
        +   dependent destruction Hb.
            *   apply lt_box2.
                now apply IHHa.
            *   destruct t3; try solve [inversion Hb].
                inversion Hb; subst.
                apply lt_undef2.
                apply lt_box1.
                now apply IHHa.
            *   apply lt_undef2.
                apply lt_box1.
                apply lt_moved.
                now apply IHHa.
        +   apply lt_top.
    -   destruct t3 as [ [] |  ]; try solve [inversion Hb].
        +   inversion Hb; subst.
            *   apply lt_box2.
                now apply IHHa.
            *   apply lt_undef3.
                now apply IHHa.
        +   apply lt_top.   
    -   destruct t3 as [ [  ] | ]; try solve [inversion Hb].
        +   inversion Hb; subst.
            *   apply lt_box3.
                now apply IHHa.
            *   apply lt_undef4.
                now apply IHHa. 
        +   apply lt_top.   
    -   destruct t3.
        destruct s; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        +   apply lt_undef1.
            now apply IHHa.
        +   apply lt_top. 
    -   destruct t3; [ | apply lt_top ].
        destruct s; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        apply lt_undef2.
        now apply IHHa.
    -   destruct t3; [ | apply lt_top].
        destruct s; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        destruct t3; (try inversion H1).
        subst.
        apply lt_undef2.
        apply lt_box1.
        apply lt_moved.
        apply IHHa.
        now apply lt_undef1.
    -   destruct t3; [ | apply lt_top].
        destruct s ; [elim (lt_moved_total _ _ Hb) | ].
        inversion Hb; subst.
        destruct t3; (try inversion H1; subst).
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
    destruct t1 as [ [] | ], t2 as [ [] | ]; 
        try solve [inversion Ha | inversion Hb].
    -   repeat f_equal.
        now apply lt_antisymmetric_total.
    -   repeat f_equal.
        now apply lt_antisymmetric_moved.
    -   reflexivity.
Qed.

#[export] Instance lt_Reflexive : Reflexive lt.
Proof.
    exact lt_refl.
Qed.

#[export] Instance lt_Transitive : Transitive lt.
Proof.
    intros x y z Ha Hb.
    eapply lt_trans; eauto.
Qed.

#[export] Instance lt_AntiSymmetric : Antisymmetric _ (@eq (partial)) lt.
Proof.
    intros x y Ha Hb.
    destruct x, y.
    now apply lt_antisymmetric.
    inversion Ha.
    inversion Hb.
    inversion Ha.
    reflexivity.
Qed.

#[export] Instance typePreorder : PreOrder lt.
constructor.
apply lt_Reflexive.
apply lt_Transitive.
Qed.

#[export] Instance PartialOrderlt : PartialOrder eq lt.
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
    intros [Ha Hb].
    unfold flip in Hb.
    destruct x, x0.
    + apply lt_antisymmetric.
        assumption.
        assumption.
    + inversion Hb.
    + inversion Ha.   
    + reflexivity.
Qed.

Fixpoint type_join (t1 t2 : partial) : partial := 
    match t1, t2 with 
        | _,_ => ⟙
    end.


#[export] Instance typeJoinLattice : JoinLattice (@eq partial) lt type_join.
Admitted.

