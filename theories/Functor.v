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

Require Import Program.Basics.

Set Universe Polymorphism.

Open Scope program_scope.

Notation "$" := (fun x y => y x) (at level 29).

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {A B : Type}, (A -> B) -> f A-> f B;
    functor_identity   : forall {A : Type}, fmap (@id A) = id;
    functor_compose : forall {A B C : Type} (f : B -> C) (g : A -> B),
        (fmap f ∘ fmap g) = fmap (f ∘ g)
  }.

Class Applicative (f : Type -> Type) `(E : Functor f)  : Type :=
  {
    pure : forall {A : Type}, A -> f A;
    ap : forall {A B : Type}, f (A -> B) -> f A -> f B;
    applicative_identity : forall {A : Type} (x : f A), ap (pure id) x = x;
    applicative_compose : forall {A B C : Type} (u : f (B -> C)) (v : f (A -> B)) (w : f A),
        ap (ap (ap (pure compose) u) v) w = ap u (ap v w);
    applicative_homomorphism :
      forall {A B : Type} (f : A -> B) (x : A), ap (pure f) (pure x) = pure (f x);
    applicative_interchange :
      forall {A B : Type} (u : f ( A -> B)) ( y : A), ap u (pure y) = ap (pure ($ y)) u;
    applicative_fmap : forall {A B : Type} (f : A -> B), fmap f  = ap (pure f)
  }.

(*Arguments fmap {f _ a b} g x.*)

Definition liftA (f : Type -> Type) `{E : Applicative f} (A B : Type) (g : A -> B) (a : f A) :=
  @ap f _ _ _ _ (pure g) a.

Definition liftA2 (f : Type -> Type) `{E : Applicative f} (A B C : Type) (g : A -> B -> C)
           (a : f A) (b : f B) : f C :=
  @ap f _ _ _ _ (fmap g a) b.

Declare Scope functor_scope.

Infix "<$>" := fmap (at level 28, left associativity, only parsing) : functor_scope.

Infix "<&>" := (flip fmap) (at level 28, left associativity, only parsing) : functor_scope.

Infix "<$" := (fmap ∘ const) (at level 28) : functor_scope.

Infix "($>)" := (flip (fmap ∘ const)) (at level 28) : functor_scope.

Infix "<*>" := ap (at level 28) : functor_scope.

