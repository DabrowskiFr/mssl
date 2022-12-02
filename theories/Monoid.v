(************************************************************************)
(* Copyright 2018 Frédéric Dabrowski                                    *)
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
Require Import List.
Import ListNotations.

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

  Axiom a : forall (A : Type) (x : list A), [ ] ++ x = x.
Axiom b : forall (A : Type) (x : list A), x ++ [] = x.
Axiom c : forall (A : Type) (a b c : list A), 
    a ++ (b ++ c) = (a ++ b) ++ c.

Instance ListMonoid (A : Type) : Monoid (list A) :=
{
    mempty := [];
    mappend := @List.app A  ;
    monoid_left_id := a A;
    monoid_right_id := b A ;
    monoid_assoc := c A
}.

