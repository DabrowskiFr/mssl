Require Import Variables Value Lifetime LVal.

Open Scope type_scope.

Module MSSLSyntax.

    Inductive sem : Set := Copy | Move.

    Inductive expression : Type :=
        | EVal : Value.value -> expression  
        | EVar : Var.t -> expression 
        | ERead : sem -> lval -> expression 
        | ESeq : expression -> expression -> expression
        | EBlock : expression -> Lifetime.t -> expression
        | EBinding : Var.t -> expression -> expression
        | EBox : expression -> expression
        | ERef : bool -> lval -> expression 
        | EAssign : lval -> expression -> expression
        | ETrc : expression -> expression
        | EClone : lval -> expression
        | ESpawn : Var.t -> list expression -> expression
        | ECooperate : expression.

    Inductive signature : Set :=
        | SUnit : signature
        | SInt : signature
        | STrc : signature -> signature  
        | SBox : signature -> signature.

    Record method : Type := Mtd {
        params : list (Var.t * signature);
        rtype : signature;
        body : expression;
        m_lft : Lifetime.t
    }.

    Record program : Type := Prg {
        functions : Var.t -> option method;
        main : expression;
        p_lft : Lifetime.t
    }.

End MSSLSyntax. 



