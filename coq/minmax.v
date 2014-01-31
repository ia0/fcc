Require Import Omega.
Require Import Min.
Require Import Max.

(** This file defines a tactic [minmax] to help with arithmetic
involving [min] and [max].
*)

Lemma le_min_r' : forall m n n', n <= n' -> min m n <= n'.
Proof. intros; apply le_trans with (m := n); auto; apply le_min_r. Qed.

Lemma le_min_l' : forall m n m', m <= m' -> min m n <= m'.
Proof. intros; apply le_trans with (m := m); auto; apply le_min_l. Qed.

Lemma le_max_r' : forall m n n', n' <= n -> n' <= max m n.
Proof. intros; apply le_trans with (m := n); auto; apply le_max_r. Qed.

Lemma le_max_l' : forall m n m', m' <= m -> m' <= max m n.
Proof. intros; apply le_trans with (m := m); auto; apply le_max_l. Qed.

Ltac minmax :=
  repeat (apply min_glb || apply max_lub);
  let rec aux := omega || (apply le_n_S; aux)
                       || (apply le_min_l'; aux) || (apply le_min_r'; aux)
                       || (apply le_max_l'; aux) || (apply le_max_r'; aux)
  in aux.
