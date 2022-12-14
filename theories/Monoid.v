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

(** * Monoids *)

Require Import List.
Import ListNotations.

Set Universe Polymorphism.

Class Monoid (A : Type) :=
  {
    mempty : A;
    mappend : A -> A -> A;
    
    monoid_left_id  : forall a, mappend mempty a = a;
    monoid_right_id : forall a, mappend a mempty = a;
    monoid_assoc    : forall a b c, mappend a (mappend b c) = mappend (mappend a b) c
  }.

Class CommutativeMonoid (A : Type) `(E : Monoid A) :=
  {
    monoid_commute : forall a b, mappend a b = mappend b a
  }.
