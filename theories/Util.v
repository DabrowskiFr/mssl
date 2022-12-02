Module Option_as_OT (T : OrderedType): OrderedType.

Definition t := option T.t.
Definition eq x y := 
    match (x,y) with 
        |(Some x, Some y) => T.eq x y
        |(None, None) => True
        | _ => False 
    end.
Definition lt x y := 
    match (x,y) with 
        | (Some x, Some y) => T.lt x y
        | (None, Some _) => True
        | _ => False 
    end.
Lemma eq_refl : forall x, eq x x.
Proof.
Admitted.
Lemma eq_sym : forall x y, eq x y -> eq y x.
Admitted.
Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
Admitted.
Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.                  
Admitted. 
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
Definition compare x y : Compare lt eq x y.
Proof.
    destruct x, y.
    -   destruct (T.compare t0 t1); now constructor.
    -   now constructor.
    -   now constructor.
    -   now constructor.
Qed.
Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.
End Option_as_OT.
