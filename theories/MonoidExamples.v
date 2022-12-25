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

(** * Monoid examples *)

    Require Import List Monoid.
Import ListNotations.
 
 #[export] Instance ListMonoid (A : Type) : Monoid (list A) :=
 {
     mempty := [];
     mappend := @List.app A  ;
     monoid_left_id := @app_nil_l A;
     monoid_right_id := @app_nil_r A ;
     monoid_assoc := @app_assoc A
 }.
 
 