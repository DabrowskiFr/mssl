(************************************************************************)
(* Copyright 2022 Frédéric Dabrowski                                    *)
(* 
    This program is free software:: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Foobar is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Foobar.  If not, see <https://www.gnu.org/licenses/>.    *)
(************************************************************************)

Require Import Utf8.
Require Import Program.Basics.
Require Import Program.Tactics.
Require Import Functor.

Set Universe Polymorphism.

Declare Scope monad_scope.

Notation "'return'" := pure : monad_scope.

Class Monad (f : Type -> Type) `(E : Applicative f)  : Type :=
  {
    bind : ∀ {a b : Type}, f a -> (a -> f b) -> f b;
    monad_left_identity : ∀ {a b : Type} (x : a) (k: a -> f b), bind (pure x) k = k x;
    monad_right_identity : forall {a b : Type} (m : f a) , bind m pure = m;
    monad_associative : forall {a b c : Type} (m : f a) (k : a -> f b) (h : b -> f c),
        bind m (fun x => bind (k x) h) = bind (bind m k) h  
  }.

Infix ">>=" := bind (at level 29) : monad_scope.

Infix ">>" := (fun m k => bind m (fun x => k)) (at level 29) : monad_scope. 

Notation "'do' X <- A ; B" := (bind A (fun X => B))
                               (at level 200, X ident, A at level 100, B at level 200).

#[export] Instance functor_option : Functor option.
Admitted.

#[export] Instance applicative_option : Applicative option functor_option.
Admitted.

#[export] Instance monad_option : Monad option applicative_option.
Admitted.