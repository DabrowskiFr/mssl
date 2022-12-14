From MSSL Require Import Syntax.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Syntax.
Require Import Relations.


Require Import List.
Import ListNotations.
Require Import Variables.

Require Import Monoid MonoidExamples.
Require Import Functor.
Require Import Coq.Sets.Ensembles.
Open Scope type_scope.

Require Import Coq.Program.Basics.

Require Import Lifetime Store LVal Value.

Require Import Transition.

Require Import Monad.
Open Scope monad_scope.


Open Scope type_scope.
   
    Import MSSLSyntax.
    Import Value.

    Module D <: StoreDomain. 
        Definition loc := location.
        Definition val := partialValue * sum Lifetime.t nat.
    End D.

    Module S := Store (D).

    Definition isValue (e : expression) : Prop :=
            match e with EVal v => True | _ => False end.

    Definition getValue (e : expression) (H : isValue e) : Value.value :=
        match e as e0 return (isValue e0 -> Value.value) with 
            | EVal v => const v
            | _ => False_rect _ 
        end H.




    Coercion EVal : Value.value >-> expression.

    Axiom instantiate : S.t -> Lifetime.t -> expression -> expression.

    Definition threadId := nat.
    Definition pool := list (threadId * expression * Lifetime.t).


Inductive context : Type :=
    | CEmpty : context 
    | CSeq : context -> expression -> context 
    | CBinding : Var.t -> context -> context 
    | CAssign : lval -> context -> context 
    | CBox : context -> context 
    | CTrc : context -> context 
    | CSpawn : Var.t -> list Value.value -> context -> list expression -> context.

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

    Definition lstate := S.t * expression.


    Definition read (?? : S.t) (l : Lifetime.t) (?? : lval) : 
        option (Value.partialValue * sum Lifetime.t nat) :=
            S.loc ?? l ?? >>= S.get ??.
    
    Definition write (?? : S.t) (l : Lifetime.t) (?? : lval)  (v : Value.partialValue) : 
        option S.t :=
            S.loc ?? l ?? >>= (fun a => S.get ?? a >>= (fun x =>  S.set ?? a (v, snd x))).
    
    Inductive step (p : program) (l : Lifetime.t) :
        transition lstate pool :=
            S_Copy : forall ?? ?? v m, 
            read ?? l ?? = Some (Some v, m) ->
            step p l (??, ERead Copy ??)  [] (??, EVal v)
        |   S_Move : forall ?? ?? v ??' m, 
            read ?? l ?? = Some (Some v, m) ->
            write ?? l ?? None = Some ??' ->  
            step p l (??, ERead Move ??) [] (??', EVal v)
        |   S_Box : forall  (?? ??' : S.t) (m : nat) (v : value),
            ~ S.defined ?? (inr m) ->
            S.allocate ?? [(inr m, (Some v, inl Lifetime.glob))] = Some ??' -> 
            step p l (??, EBox v) [] (??', EVal (Value.Location (inr m) Owned))
        |   S_Trc : forall  (?? ??' : S.t) (m : nat) (v : value),
            ~ S.defined ?? (inr m) ->
            S.allocate ?? [(inr m, (Some v, inr 1))] = Some ??' -> 
            step p l (??, ETrc v) [] (??', EVal (Location (inr m) (Trc true)))
        |   S_Clone : forall  (?? ??' : S.t) (?? : lval) (m i : nat), 
            read ?? l ?? = Some (Some (Location (inr m) (Trc true)), inr i) ->
            S.clone ?? l ?? = Some ??' ->
            step p l (??, EClone ??) [] (??', EVal (Location (inr m) (Trc false)))
        |   S_Borrow : forall ?? ?? ??? b,
            S.loc ?? l ?? = Some ??? ->
            step p l (??, ERef b ??) [] (??, EVal (Location ??? Borrowed))
        |   S_Declare : forall (?? ??' : S.t) (x : Var.t) (v : value),
            write ?? l (LVar x) (Some v) = Some ??' -> 
            step p l (??, EBinding x v) [] (??', EVal Unit)
        |   S_Assign : forall (?? ??' ??'' : S.t) (?? : lval) 
            (v:value) (v' : partialValue) m,
            read ?? l ?? = Some (v', m) -> 
            (* S.drop_val ?? (Singleton _ v') = Some ??'' -> *)
            write ??'' l ?? (Some v) = Some ??' ->
            step p l (??, EAssign ?? (EVal v)) [] (??', EVal Unit)
        |   S_Seq : forall (?? ??' : S.t) (v :value) (e1 e2  : expression),
            (* Store.drop_val ?? (Singleton _ (Some v)) = Some ??' -> *)
            step p l (??, ESeq (EVal v) e2) [] (??, e2)
        |   S_Block1 : forall ( m : Lifetime.t) (?? ??' : S.t) (e e' : expression) T,
            step p m (??, e) T (??', e') -> 
            step p l (??, EBlock e m) T (??', EBlock e' m)
        |   S_Block2 : forall (m : Lifetime.t) (?? ??' : S.t) (v : value),
            (* Store.drop_lft ?? m = Some ??' -> *)
            step p l (??, EBlock (EVal v) m) [] (??, EVal v)
        |   S_Spawn : forall (m m' : Lifetime.t) (?? ??' : S.t) (f : Var.t) (mth : method)
                (e e' : expression) (el : list expression) (vl : list value) (t :threadId),
            functions p f = Some mth ->
            el = List.map EVal vl ->
            instantiate ?? l (EBlock e m) = EBlock e' m' ->
            let xl := List.map (fun x =>  inl (fst x, m')) (params mth) in 
            let vl' := List.map (fun v => (Some v, inl m')) vl in
            let u := List.combine xl vl' in
            S.allocate ?? u = Some ??' ->
            step p l (??, ESpawn f el) [(t, e', m')] (??', EVal Unit).

    Definition run (p : program) (l : Lifetime.t) : 
        transition lstate (list (threadId * expression * Lifetime.t)) :=
            reachable _ _ (step p l).

    
    Inductive react (p : program) : relation (S.t * pool) :=
        | react_done : forall ??, react p (??, []) (??, [])
        | react_step : forall l t ?? ??' ??'' e e' T0 T T',
            step p l (??, e) T0 (??', e') -> 
            react p (??'',T) (??', T') ->
            react p (??, (t, e, l)::T) (??', (t,e',l)::T' ++ T0).

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

    Definition instant (p : program) : relation (S.t * pool) :=
        fun st st' =>
        let (??, T) := st in 
        let (??', T') := st' in
        exists T'', react p (??, T) (??', T') /\ resetAll T'' T'.

    Definition reachable (p : program) : relation (S.t * pool) :=
        clos_refl_trans _ (instant p).