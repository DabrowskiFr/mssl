Require Import String.
Require Import Coq.Structures.OrderedType.
Require Import Ensembles.
Module Value(Lifetime : OrderedType).

Definition variable : Set := string.

Definition location : Type := sum (variable * Lifetime.t) nat.

Inductive lval : Set :=
    | LVar : variable -> lval 
    | LDeref : lval -> lval.

Inductive kind : Set :=
| Owned : kind (* black square *)
| Borrowed : kind (* white circle *)
| Trc : bool -> kind. (* losange *)

Inductive value : Type := 
    | Unit : value
    | Int : nat -> value
    | Location : location -> kind -> value. 

Definition partialValue : Type := option value.

    Module Store.
    (* address -> partialValue * sum lifetime nat *)
    Parameter t : Type.
    Parameter defined : t ->  location -> Prop.
    (* Parameter allocate : t -> location -> partialValue -> option t.*)
    Parameter free : t -> location -> option t.
    
    (* Parameter get : t -> location -> option partialValue.
    Parameter set : t ->location -> partialValue -> option t.*)
    
    (*Parameter fetch : t -> variable -> Lifetime.t -> option (Lifetime.t).*)
    Parameter get : t -> location -> option (partialValue * sum Lifetime.t nat). 
    Parameter allocate : t -> list (location * (partialValue * sum Lifetime.t nat)) -> option t.
    
    Parameter loc : t -> Lifetime.t -> lval -> option location.
    Parameter read : t -> Lifetime.t -> lval -> option (partialValue * sum Lifetime.t nat).
    Parameter write : t -> Lifetime.t -> lval ->  partialValue -> option t.
    Parameter clone : t -> Lifetime.t -> lval -> option t.
    
    Parameter drop_val : t -> Ensemble partialValue -> option t.
    Parameter drop_lft : t -> Lifetime.t -> option t.
    Parameter count : t -> nat -> option nat.
    (* Parameter fetchprop : forall (x : variable) o m S,
        fetch S x o = Some m ->
        Lifetime.lt m o /\
        forall n, defined S (inl (x, n)) -> not (Lifetime.lt n m).*)
    (*   Parameter drop_prop1 : forall phi sigma,
    Same_set value phi (Empty_set value) ->
    drop sigma phi =  Some sigma.*)
    
    (*        Parameter drop_prop2 : forall phi v sigma l v' phi',
    In _ phi (Location l Owned) ->
    get sigma l = Some v' -> 
    drop sigma phi = drop (free sigma l) (Union _ phi' (Singleton _ v')).
    
    Parameter drop_prop2 : forall phi phi' v sigma,
    In _ phi v -> 
    phi' = Subtract _ phi v ->
    drop sigma phi = 
    match v with 
        | Location l Owned =>  
            get sigma l = Some v'
             (free sigma l)
        | Location l Borrowed => Some sigma 
        | Location l (Trc b) => Some (sigma)
        | _ => drop sigma phi'
    end.
    (* we need the thread lifetime to fetch the variable *)
    *)
    End Store.
End Value.