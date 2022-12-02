From MSSL Require Import Syntax.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Syntax.
Require Import Relations.


Require Import List.
Import ListNotations.
Require Import String.

Require Import Monoid.
Require Import Functor.
Require Import Coq.Sets.Ensembles.
Open Scope type_scope.

Definition transition (A B : Type) := A -> B -> A -> Prop.

Inductive tr_clos_rt (A B : Type) {MB : Monoid B}(T : transition A B) : transition A B :=   
| tr_close_rt_step : forall x y z,
    T x y z -> tr_clos_rt A B T x y z
| tr_close_rt_refl : forall a,
        tr_clos_rt A B T a mempty a
| tr_close_rt_trans : forall x a y b z,
    T x a y -> T x b z -> tr_clos_rt A B T x (mappend a b) z.

Module Semantics (Lifetime : BoundedOrderedType).

    Module Import S := MSSLSyntax(Lifetime).
    Import S.V.

   

    Definition isValue (e : expression) : Prop :=
            match e with EVal v => True | _ => False end.

    Definition getValue (e : expression) (H : isValue e) : value :=
        match e as e0 return (isValue e0 -> value) with 
            | EVal v => const v
            | e' => False_rect _ 
        end H.




    Coercion EVal : value >-> expression.

    Axiom instantiate : Store.t -> Lifetime.t -> expression -> expression.

    Definition threadId := nat.
    Definition pool := list (threadId * expression * Lifetime.t).


Inductive context : Type :=
    | CEmpty : context 
    | CSeq : context -> expression -> context 
    | CBinding : variable -> context -> context 
    | CAssign : lval -> context -> context 
    | CBox : context -> context 
    | CTrc : context -> context 
    | CSpawn : string -> list value -> context -> list expression -> context.

Fixpoint build (c : context) (e : expression) : expression :=
    match c with 
        | CEmpty => e 
        | CSeq c e' => ESeq (build c e) e' 
        | CBinding x c =>  EBinding x (build c e) 
        | CAssign w c => EAssign w (build c e)
        | CBox c => EBox (build c e)
        | CTrc c => ETrc (build c e)
        | CSpawn f vl c el => ESpawn f ((List.map EVal vl)++[(build c e)]++el)
        end.

    Definition lstate := Store.t * expression.

    Inductive step (p : program) (l : Lifetime.t) :
        transition lstate pool :=
            S_Copy : forall σ ω v m, 
            Store.read σ l ω = Some (Some v, m) ->
            step p l (σ, ERead Copy ω)  [] (σ, EVal v)
        |   S_Move : forall σ ω v σ' m, 
            Store.read σ l ω = Some (Some v, m) ->
            Store.write σ l ω None = Some σ' ->  
            step p l (σ, ERead Move ω) [] (σ', EVal v)
        |   S_Box : forall  (σ σ' : Store.t) (m : nat) (v : value),
            ~ Store.defined σ (inr m) ->
            Store.allocate σ [(inr m, (Some v, inl Lifetime.glob))] = Some σ' -> 
            step p l (σ, EBox v) [] (σ', EVal (Location (inr m) Owned))
        |   S_Trc : forall  (σ σ' : Store.t) (m : nat) (v : value),
            ~ Store.defined σ (inr m) ->
            Store.allocate σ [(inr m, (Some v, inr 1))] = Some σ' -> 
            step p l (σ, ETrc v) [] (σ', EVal (Location (inr m) (Trc true)))
        |   S_Clone : forall  (σ σ' : Store.t) (ω : lval) (m i : nat), 
            Store.read σ l ω = Some (Some (Location (inr m) (Trc true)), inr i) ->
            Store.clone σ l ω = Some σ' ->
            step p l (σ, EClone ω) [] (σ', EVal (Location (inr m) (Trc false)))
        |   S_Borrow : forall σ ω ℓ b,
            Store.loc σ l ω = Some ℓ ->
            step p l (σ, ERef b ω) [] (σ, EVal (Location ℓ Borrowed))
        |   S_Declare : forall (σ σ' : Store.t) (x : variable) (v : value),
            Store.write σ l (LVar x) (Some v) = Some σ' -> 
            step p l (σ, EBinding x v) [] (σ', EVal Unit)
        |   S_Assign : forall (σ σ' σ'' : Store.t) (ω : lval) 
            (v:value) (v' : partialValue) m,
            Store.read σ l ω = Some (v', m) -> 
            Store.drop_val σ (Singleton _ v') = Some σ'' ->
            Store.write σ'' l ω (Some v) = Some σ' ->
            step p l (σ, EAssign ω (EVal v)) [] (σ', EVal Unit)
        |   S_Seq : forall (σ σ' : Store.t) (v :value) (e1 e2  : expression),
            Store.drop_val σ (Singleton _ (Some v)) = Some σ' ->
            step p l (σ, ESeq (EVal v) e2) [] (σ, e2)
        |   S_Block1 : forall ( m : Lifetime.t) (σ σ' : Store.t) (e e' : expression) T,
            step p m (σ, e) T (σ', e') -> 
            step p l (σ, EBlock e m) T (σ', EBlock e' m)
        |   S_Block2 : forall (m : Lifetime.t) (σ σ' : Store.t) (v : value),
            Store.drop_lft σ m = Some σ' ->
            step p l (σ, EBlock (EVal v) m) [] (σ, EVal v)
        |   S_Spawn : forall (m m' : Lifetime.t) (σ σ' : Store.t) (f : String.string) (mth : method)
                (e e' : expression) (el : list expression) (vl : list value) (t :threadId),
            functions p f = Some mth ->
            el = List.map EVal vl ->
            instantiate σ l (EBlock e m) = EBlock e' m' ->
            let xl := List.map (fun x =>  inl (fst x, m')) (params mth) in 
            let vl' := List.map (fun v => (Some v, inl m')) vl in
            let u := List.combine xl vl' in
            Store.allocate σ u = Some σ' ->
            step p l (σ, ESpawn f el) [(t, e', m')] (σ', EVal Unit).

    Definition run (p : program) (l : Lifetime.t) : 
        transition lstate (list (threadId * expression * Lifetime.t)) :=
            tr_clos_rt _ _ (step p l).

    
    Inductive react (p : program) : relation (Store.t * pool) :=
        | react_done : forall σ, react p (σ, []) (σ, [])
        | react_step : forall l t σ σ' σ'' e e' T0 T T',
            step p l (σ, e) T0 (σ', e') -> 
            react p (σ'',T) (σ', T') ->
            react p (σ, (t, e, l)::T) (σ', (t,e',l)::T' ++ T0).

    Inductive reset : relation expression :=
        | reset_val : reset (EVal Unit) (EVal Unit)
        | reset_cooperate : forall e e' C,
            e  = build C ECooperate ->
            e' = build C (EVal Unit) ->
            reset e e'.  

    Definition resetAll : relation pool :=
        fun (l1 l2 : pool) => forall i, 
            match nth_error l1 i, nth_error l2 i with 
                | None, None => True 
                | Some (_, e1, _), Some (_, e2, _) => reset e1 e2 
                | _, _ => False 
            end.

    Definition instant (p : program) : relation (Store.t * pool) :=
        fun st st' =>
        let (σ, T) := st in 
        let (σ', T') := st' in
        exists T'', react p (σ, T) (σ', T') /\ resetAll T'' T'.

    Definition reachable (p : program) : relation (Store.t * pool) :=
        clos_refl_trans _ (instant p).

End Semantics.
