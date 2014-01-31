Require Import Omega.
Require Import List.

Require Import ext.

(** This file defines some lemmas for [list]s.
*)

Lemma cut_length : forall A i (xys : list A) j, length xys = i + j -> exists xs ys,
  xys = xs ++ ys /\ length xs = i /\ length ys = j.
Proof.
induction i; simpl; intros xys j l; [exists nil, xys; auto|].
destruct xys as [|x xys]; inversion l.
destruct IHi with (j := j) (xys := xys) as [? [? [? [? ?]]]]; auto.
exists (x :: x0), x1; simpl; split; [|split]; auto.
rewrite H; auto.
Qed.

Lemma Forall_nth : forall A P xs (y : A) n, Forall P xs -> P y -> P (nth n xs y).
Proof. induction xs; intros y [|n] Pxs Py; inversion Pxs; simpl in *; auto. Qed.

Lemma Forall_app : forall A C (xs ys : list A), Forall C (xs ++ ys) <-> Forall C xs /\ Forall C ys.
Proof.
induction xs; simpl; split; intros Cxys;
repeat (simpl; match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : Forall _ (_ :: _) |- _ => inversion H; clear H
  | |- _ /\ _ => split
  | |- Forall _ nil => constructor
  | |- Forall _ (_ :: _) => constructor
  | H : Forall _ (?xs ++ ?ys) |- Forall _ ?xs => apply (IHxs ys)
  | H : Forall _ (?xs ++ ?ys) |- Forall _ ?ys => apply (IHxs ys)
  | |- Forall _ (_ ++ ?ys) => apply (IHxs ys)
end; auto).
Qed.

Lemma Forall_map : forall A B (h : A -> Prop) f (g : B -> Prop), (forall x, g (f x) = h x) ->
  forall xs, Forall g (map f xs) = Forall h xs.
Proof.
induction xs; intros; simpl; apply propositional_extensionality; split; constructor; inversion H0; subst.
rewrite H in H3; auto.
rewrite IHxs in H4; auto.
rewrite <- H in H3; auto.
rewrite <- IHxs in H4; auto.
Qed.

Lemma Forall_map_impl : forall A B (h : A -> Prop) f (g : B -> Prop), (forall x, h x -> g (f x)) ->
  forall xs, Forall h xs -> Forall g (map f xs).
Proof. induction xs; intros; simpl; constructor; inversion H0; subst; auto. Qed.

Lemma replicate : forall A (a : A) n, exists xs, length xs = n /\ forall i, nth i xs a = a.
Proof.
induction n.
(* 2: 0 *)
  exists nil; split; auto.
  intros i; destruct i; auto.
(* 1: 1+ *)
  destruct IHn as [xs [? ?]].
  exists (cons a xs).
  split; simpl; try omega.
  intros i; destruct i; auto.
Qed.

Lemma skipn_overflow : forall A d h, length h < d -> skipn d h = @nil A.
Proof.
induction d; destruct h; simpl; intros; auto.
inversion H.
apply IHd.
omega.
Qed.

Lemma skipn_app_length : forall A (h2 h1 : list A),
  skipn (length h1) (h1 ++ h2) = h2.
Proof. induction h1; simpl; auto. Qed.
