Require Import String DecidableType.

Module Var : DecidableType.
    Definition t := String.string.
    Definition eq := @eq String.string.
    Definition eq_refl := @eq_refl String.string.
    Definition eq_sym := @eq_sym String.string.
    Definition eq_trans := @eq_trans String.string.
    Definition eq_dec := String.string_dec.
End Var.
