Open Scope type_scope.
Require Import Value.
Require Import String.
Require Import OrderedType.

Module Type BoundedOrderedType <: OrderedType.OrderedType.
    Include OrderedType.OrderedType.
    Parameter glob : t.
    Axiom least_elt : forall x : t, lt glob x.
End BoundedOrderedType.

Module MSSLSyntax(Lifetime : BoundedOrderedType).

Module Import V := Value(Lifetime).

Inductive type : Set := 
    | UnitType : type 
    | IntType : type
    | RefType : bool -> list lval -> type
    | TrcCloneType : list lval -> type 
    | TrcType : type -> type 
    | BoxType : type -> type.

Inductive sem : Set := Copy | Move.

Inductive expression : Type :=
    | EVal : value -> expression  
    | EVar : variable -> expression 
    | ERead : sem -> lval -> expression 
    | ESeq : expression -> expression -> expression
    | EBlock : expression -> Lifetime.t -> expression
    | EBinding : variable -> expression -> expression
    | EBox : expression -> expression
    | ERef : bool -> lval -> expression 
    | EAssign : lval -> expression -> expression
    | ETrc : expression -> expression
    | EClone : lval -> expression
    | ESpawn : string -> list expression -> expression
    | ECooperate : expression.

Inductive signature : Set :=
    | SUnit : signature
    | SInt : signature
    | STrc : signature -> signature  
    | SBox : signature -> signature.

Record method : Type := Mtd {
    params : list (string * signature);
    rtype : signature;
    body : expression;
    m_lft : Lifetime.t
}.

Record program : Type := Prg {
    functions : string -> option method;
    main : expression;
    p_lft : Lifetime.t
}.


End MSSLSyntax.



