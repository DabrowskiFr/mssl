
Definition eqb (b1 b2 : bool) : Prop := b1 = b2.
Definition ltb (b1 b2 : bool) : Prop := 
    match (b1, b2) with 
        | (false, _) => True
        | (true, true) => True
        | (true, talse) => False 
        end.

#[export] Instance ref_eqb : Reflexive eqb.
constructor.
Qed.

#[export] Instance sym_eqb : Symmetric eqb.
intros x y  H.
symmetry.
assumption.
Qed.

#[export] Instance trans_eqb : Transitive eqb.
intros x y z H1 H2.
transitivity y.
assumption.
assumption.
Qed.

#[export] Instance eq_eqb : Equivalence eqb.
constructor.
apply ref_eqb.
apply sym_eqb.
apply trans_eqb.
Qed.

#[export] Instance refl_ltb : Reflexive ltb.
intros x.
unfold ltb.
case_eq x; intros; subst.
trivial.
trivial.
Qed.

#[export] Instance trans_ltb : Transitive ltb.
intros x y z H1 H2.
destruct x,y,z;  trivial.
Qed.

#[export] Instance preo_eqb : PreOrder ltb.
constructor.
apply refl_ltb.
apply trans_ltb.
Qed.

#[export] Instance po : PartialOrder eqb ltb.
constructor.
-   unfold eqb, ltb, Basics.flip.
    split; destruct x, x0; solve [trivial | discriminate].
-   unfold eqb, ltb, Basics.flip.
    intros [H1 H2].
    destruct x, x0; intuition.
Qed.

Definition joinb (b1 b2 : bool) : bool :=
    match (b1, b2) with 
        | (false, false) => false
        | (_, _) => true 
        end.

#[global] Instance jl : JoinLattice eqb ltb joinb.
constructor.
-   intros; unfold ltb, joinb.
    destruct x, y; trivial.
-   intros; unfold ltb, joinb.
    destruct x, y; trivial.
- intros; unfold ltb, joinb.
    destruct x, y, z; trivial.
Defined.

Lemma a : forall b1 b2 : bool, ltb b1 (joinb b1 b2).
Proof.
    intros.
    apply join_bound1.
Qed.
