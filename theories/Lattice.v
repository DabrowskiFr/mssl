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

(** * Lattices *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Class JoinLattice {A : Type} (eqA : relation A) `{equ : Equivalence A eqA}
(R : relation A) `{partialOrder : PartialOrder A eqA R} (join : A -> A -> A)  :=
{
    join_bound1 (x y : A) : R x (join x y);
    join_bound2 (x y : A) : R y (join x y);
    join_least_upper_bound (x y z : A) : R x z -> R y z -> R (join x y) z 
}.

Class MeetLattice {A : Type} (eqA : relation A) `{equ : Equivalence A eqA}
(R : relation A) `{partialOrder : PartialOrder A eqA R} (meet : A -> A -> A)  :=
{
    meet_bound1 (x y : A) : R (meet x y) x;
    meet_bound2 (x y : A) : R (meet x y) y;
    meet_greatest_lower_bound (x y z : A) : R z x -> R z y -> R z (meet x y)
}.

Class Lattice {A : Type} (eqA : relation A) `{equ : Equivalence A eqA}
(R : relation A) `{partialOrder : PartialOrder A eqA R}
(join : A -> A -> A) (meet : A -> A -> A): Type :=
{
    Lattice_JoinLattice :> JoinLattice eqA R join; 
    Lattice_MeetLattice :> MeetLattice  eqA R meet
}.