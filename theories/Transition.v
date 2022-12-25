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

Require Import Monoid.

(** * Labelled transition *)

Section Transition.

Variable A B : Type.

(** A labelled transition system is a pair [(A, T)] where [T : A -> B -> A -> Prop] 
for some set of actions [B] *)

Definition transition := A -> B -> A -> Prop.

(** If B is a monoid, we can define the reachability relation of the transition system *)

Inductive reachable {MB : Monoid B} (T : transition) : transition :=   
| reachable_step : forall x y z,
    T x y z -> reachable T x y z
| reachable_refl : forall a,
        reachable T a mempty a
| reachable_trans : forall x a y b z,
    reachable T x a y -> T y b z -> reachable  T x (mappend a b) z.

End Transition.
