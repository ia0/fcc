Require Import Inclusion. (* wf_incl *)
Require Import Inverse_Image. (* wf_inverse_image *)
Require Import Wf_nat.
Require Import Omega.
Require Import Min.

Require Import minmax.
Require Import Flanguage.

(** * Strong normalization of the untyped Indexed Calculus *)

Definition der b a := red a b.

(** We define a very simple measure on indexed terms. The measure of a
term is its top-level index.
*)
Definition measure a :=
  match a with
    | Var k _ => k
    | Lam k _ => k
    | App k _ _ => k
    | Unit k => k
    | Pair k _ _ => k
    | Fst k _ => k
    | Snd k _ => k
    | Absurd k _ => k
    | Inl k _ => k
    | Inr k _ => k
    | Match k _ _ _ => k
    | Gen k _ => k
    | Inst k _ => k
  end.

(** Lowering by [k] a term [a] forces the measure of the resulting
term to be lower than [k].
*)
Lemma measure_lower : forall k a, measure (lower k a) <= k.
Proof. induction a; simpl; minmax. Qed.

(** The measure strictly decreases by reduction. This is the key of
the proof.
*)
Lemma red_measure : forall a b, red a b -> measure b < measure a.
Proof.
intros a b Hred; induction Hred; [destruct c|..]; simpl; auto;
repeat match goal with
         | H : _ /\ _ |- _ => destruct H
       end;
match goal with
  | |- measure (lower ?k ?a) < _ =>
    apply le_trans with (m := S k); auto; pose proof (measure_lower k a); minmax
end.
Qed.

(** The reduction of the untyped indexed calculus is strongly
normalizing.
*)
Lemma wf_der : well_founded der.
Proof.
eapply wf_incl; [|apply wf_inverse_image with (f := measure); apply lt_wf].
intros b a Hred; apply red_measure; auto.
Qed.

Definition Fix := @Coq.Init.Wf.Fix term der wf_der.

(** Since all indexed term are strongly normalizing, we may prove
properties by induction on the reduction of some indexed term.
*)
Lemma ind_red : forall a (P : term -> Prop),
  (forall a, (forall b, red a b -> P b) -> P a) -> P a.
Proof. intros a P F; induction (wf_der a); apply F; apply H0. Qed.

Ltac induction_red a := let IHa := fresh "IH" a in
  apply (ind_red a); clear a; intros a IHa.

