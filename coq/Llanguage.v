Require Import Omega.
Require Import Min.
Require Import Max.

Require Import set.
Require Import Flanguage.
Module F := Flanguage.

(** * Lambda Calculus *)

(** ** Definition *)

(** Terms are written [a] or [b]. They are defined exactly like
indexed terms without the notion of fuel. They contain variables,
abstractions, applications, pairs, projections, generalization, and
instantiations.
*)
Inductive term : Set :=
| Var (x : nat)
| Lam (a : term)
| App (a : term) (b : term)
| Unit
| Pair (a : term) (b : term)
| Fst (a : term)
| Snd (a : term)
| Absurd (a : term)
| Inl (a : term)
| Inr (a : term)
| Match (a : term) (bl : term) (br : term)
| Gen (a : term)
| Inst (a : term)
.

(** ** Functions *)

(** We define a function to traverse terms and operating on its
variables. The term [traverse f i a] has the same structure as [a] but
for its variables [Var x] that become [f x i]. The level [i] indicates
how deep we are in the term: it is incremented each time we cross a
binder. The only binder of the Lambda Calculus is [Lam] and it binds
only one term, so the recursive call uses the level [1 + i].
*)
Definition traverse f := fix g i a :=
  match a with
  | Var x => f x i
  | Lam a => Lam (g (1 + i) a)
  | App a b => App (g i a) (g i b)
  | Unit => Unit
  | Pair a b => Pair (g i a) (g i b)
  | Fst a => Fst (g i a)
  | Snd a => Snd (g i a)
  | Absurd a => Absurd (g i a)
  | Inl a => Inl (g i a)
  | Inr a => Inr (g i a)
  | Match a bl br => Match (g i a) (g (1 + i) bl) (g (1 + i) br)
  | Gen a => Gen (g i a)
  | Inst a => Inst (g i a)
  end.

(** We define the lifting function [lift] and substitution function
[subst] using the [traverse] function with the [lift_idx] and
[subst_idx] functions, respectively. The term [lift d i a] has the
same structure as [a] but the variables greater or equal than [i] are
incremented by [d]. The term [subst b i a] has the same structure as
[a] but the variables greater than [i] are decremented by one and the
variables equal to [i] are replaced with [b] lifted by [i] from level
[0].
*)
Definition lift_idx d x i := Var (if le_gt_dec i x then d + x else x).
Definition lift d := traverse (lift_idx d).
Definition shift := lift 1.
Hint Unfold lift_idx lift shift.

Definition subst_idx b x i :=
  match lt_eq_lt_dec x i with
    | inleft (left _)  => Var x
    | inleft (right _) => lift x 0 b
    | inright _        => Var (x - 1)
  end.
Definition subst b := traverse (subst_idx b).
Hint Unfold subst_idx subst.

Ltac subst_lift_var := repeat (match goal with
    | |- context[subst_idx] => unfold subst_idx
    | |- context[lift_idx] => unfold lift_idx
    | |- context[lt_eq_lt_dec ?x ?y] =>
      destruct (lt_eq_lt_dec x y) as [[?|?]|?]; try (exfalso; omega); simpl; auto
    | |- context[le_gt_dec ?x ?y] =>
      destruct (le_gt_dec x y); try (exfalso; omega); simpl; auto
  end).

(** We define the [drop] function from indexed terms to lambda terms
by dropping the fuel annotations. We show a few commutation lemmas
with the [lower], [lift], and [subst] functions.
*)
Fixpoint drop a :=
  match a with
    | F.Var _ x => Var x
    | F.Lam _ a => Lam (drop a)
    | F.App _ a b => App (drop a) (drop b)
    | F.Unit _ => Unit
    | F.Pair _ a b => Pair (drop a) (drop b)
    | F.Fst _ a => Fst (drop a)
    | F.Snd _ a => Snd (drop a)
    | F.Absurd _ a => Absurd (drop a)
    | F.Inl _ a => Inl (drop a)
    | F.Inr _ a => Inr (drop a)
    | F.Match _ a bl br => Match (drop a) (drop bl) (drop br)
    | F.Gen _ a => Gen (drop a)
    | F.Inst _ a => Inst (drop a)
  end.

Lemma drop_lower : forall k a, drop (lower k a) = drop a.
Proof.
induction a; simpl;
repeat (match goal with
  | IH : drop (lower _ _) = _ |- _ => rewrite IH; clear IH
end); auto.
Qed.

Lemma drop_lift : forall x a i, drop (F.lift x i a) = lift x i (drop a).
Proof.
induction a; simpl; intros i;
repeat (match goal with
  | IH : forall _, drop (F.lift _ _ _) = _ |- _ => rewrite IH; clear IH
end); auto.
Qed.

Lemma drop_subst : forall b a i, drop (F.subst b i a) = subst (drop b) i (drop a).
Proof.
induction a; simpl; intros i;
repeat (match goal with
  | IH : forall _, drop (F.subst _ _ _) = _ |- _ => rewrite IH; clear IH
end); auto.
(* Var *)
  F.subst_lift_var; unfold subst_idx;
  destruct (lt_eq_lt_dec x i) as [[?|?]|?]; try (exfalso; omega); auto.
  rewrite drop_lower.
  apply drop_lift.
Qed.

(** We define the analog of [drop] in the opposite direction. The
indexed term [kfill k a] is similar to the lambda term [a] where all
fuel annotations are equal to [k]. We show that [kfill k a] is smaller
than [k], and that [drop] neutralizes the effect of [kfill].
*)
Definition kfill k := fix f a :=
  match a with
    | Var x => F.Var k x
    | Lam a => F.Lam k (f a)
    | App a b => F.App k (f a) (f b)
    | Unit => F.Unit k
    | Pair a b => F.Pair k (f a) (f b)
    | Fst a => F.Fst k (f a)
    | Snd a => F.Snd k (f a)
    | Absurd a => F.Absurd k (f a)
    | Inl a => F.Inl k (f a)
    | Inr a => F.Inr k (f a)
    | Match a bl br => F.Match k (f a) (f bl) (f br)
    | Gen a => F.Gen k (f a)
    | Inst a => F.Inst k (f a)
  end.

Lemma term_ge_kfill : forall k a, term_ge (kfill k a) k.
Proof. induction a; simpl; auto. Qed.

Lemma drop_kfill : forall k a, drop (kfill k a) = a.
Proof. induction a; simpl; f_equal; auto. Qed.

Definition set := @set.set term.

(** ** Reduction *)

(** Evaluation contexts [Ctx] contain all one-hole contexts of depth
one, but for [Gen]. This gives us strong reduction for all constructs
but [Gen], because the only role [Gen] is to block reduction. The
meaning of [Ctx] is given by the [fill] function. The term [fill c a]
wraps the term [a] under the context [c]. We show that [drop] and
[fill] commute.
*)
Inductive Ctx : Set :=
| CtxLam
| CtxApp1 (a : term)
| CtxApp2 (a : term)
| CtxPair1 (a : term)
| CtxPair2 (a : term)
| CtxFst
| CtxSnd
| CtxAbsurd
| CtxInl
| CtxInr
| CtxMatch1 (bl : term) (br : term)
| CtxMatch2 (a : term) (br : term)
| CtxMatch3 (a : term) (bl : term)
(* NO CtxGen! *)
| CtxInst
.

Definition fill c a :=
  match c with
    | CtxLam => Lam a
    | CtxApp1 b => App a b
    | CtxApp2 b => App b a
    | CtxPair1 b => Pair a b
    | CtxPair2 b => Pair b a
    | CtxFst => Fst a
    | CtxSnd => Snd a
    | CtxAbsurd => Absurd a
    | CtxInl => Inl a
    | CtxInr => Inr a
    | CtxMatch1 b1 b2 => Match a b1 b2
    | CtxMatch2 b1 b2 => Match b1 a b2
    | CtxMatch3 b1 b2 => Match b1 b2 a
    | CtxInst => Inst a
  end.

Definition cdrop c :=
  match c with
    | F.CtxLam => CtxLam
    | F.CtxApp1 b => CtxApp1 (drop b)
    | F.CtxApp2 b => CtxApp2 (drop b)
    | F.CtxPair1 b => CtxPair1 (drop b)
    | F.CtxPair2 b => CtxPair2 (drop b)
    | F.CtxFst => CtxFst
    | F.CtxSnd => CtxSnd
    | F.CtxAbsurd => CtxAbsurd
    | F.CtxInl => CtxInl
    | F.CtxInr => CtxInr
    | F.CtxMatch1 b1 b2 => CtxMatch1 (drop b1) (drop b2)
    | F.CtxMatch2 b1 b2 => CtxMatch2 (drop b1) (drop b2)
    | F.CtxMatch3 b1 b2 => CtxMatch3 (drop b1) (drop b2)
    | F.CtxInst => CtxInst
  end.

Lemma drop_fill : forall c k a, drop (F.fill c k a) = fill (cdrop c) (drop a).
Proof. induction c; intros; reflexivity. Qed.

(** The reduction relation [red] contains reduction under evaluation
contexts and reduction of redexes. We show how the reduction of the
Indexed Calculus and the reduction of the Lambda Calculus bisimulate.
*)
Inductive red : term -> term -> Prop :=
| RedCtx : forall a a' c, red a a' -> red (fill c a) (fill c a')
| RedApp : forall a b, red (App (Lam a) b) (subst b 0 a)
| RedFst : forall a b, red (Fst (Pair a b)) a
| RedSnd : forall a b, red (Snd (Pair a b)) b
| RedInl : forall a bl br, red (Match (Inl a) bl br) (subst a 0 bl)
| RedInr : forall a bl br, red (Match (Inr a) bl br) (subst a 0 br)
| RedInst : forall a, red (Inst (Gen a)) a
.

(** The reduction of the Lambda Calculus simulates the reduction of
the Indexed Calculus.
*)
Lemma red_drop : forall a b, F.red a b -> red (drop a) (drop b).
Proof.
intros a b Hred; induction Hred; [destruct c|..]; simpl in *;
repeat (match goal with | H : _ /\ _ |- _ => destruct H end).
(* 20: CtxLam *)
  apply RedCtx with (c := CtxLam); auto.
(* 19: CtxApp1 *)
  apply RedCtx with (c := CtxApp1 (drop b)); auto.
(* 18: CtxApp2 *)
  apply RedCtx with (c := CtxApp2 (drop a0)); auto.
(* 17: CtxPair1 *)
  apply RedCtx with (c := CtxPair1 (drop b)); auto.
(* 16: CtxPair2 *)
  apply RedCtx with (c := CtxPair2 (drop a0)); auto.
(* 15: CtxFst *)
  apply RedCtx with (c := CtxFst); auto.
(* 14: CtxSnd *)
  apply RedCtx with (c := CtxSnd); auto.
(* 13: CtxAbsurd *)
  apply RedCtx with (c := CtxAbsurd); auto.
(* 12: CtxInl *)
  apply RedCtx with (c := CtxInl); auto.
(* 11: CtxInr *)
  apply RedCtx with (c := CtxInr); auto.
(* 10: CtxMatch1 *)
  apply RedCtx with (c := CtxMatch1 (drop bl) (drop br)); auto.
(* 9: CtxMatch2 *)
  apply RedCtx with (c := CtxMatch2 (drop a0) (drop br)); auto.
(* 8: CtxMatch3 *)
  apply RedCtx with (c := CtxMatch3 (drop a0) (drop bl)); auto.
(* 7: CtxInst *)
  apply RedCtx with (c := CtxInst); auto.
(* 6: App *) rewrite drop_lower; rewrite drop_subst; apply RedApp.
(* 5: Fst *) rewrite drop_lower; apply RedFst.
(* 4: Snd *) rewrite drop_lower; apply RedSnd.
(* 3: Inl *) rewrite drop_lower; rewrite drop_subst; apply RedInl.
(* 2: Inr *) rewrite drop_lower; rewrite drop_subst; apply RedInr.
(* 1: Inst *) rewrite drop_lower; apply RedInst.
Qed.

(** The reduction of the Indexed Calculus can simulate the reduction
of the Lambda Calculus given that the initial indexed term has enough
fuel (a fuel strictly positive).
*)
Lemma drop_red_exists : forall k a b', term_ge a (1 + k) -> red (drop a) b' ->
  exists b, b' = drop b /\ F.red a b.
Proof.
intros k a b' ak Hred; remember (drop a) as a'.
generalize a ak Heqa'; clear a ak Heqa'; induction Hred; [destruct c|..];
try (rename a into ar); intros a ak Heqa';
destruct a; inversion Heqa'; clear Heqa'; simpl in ak; subst;
repeat (match goal with
  | H : ?k >= S _ |- _ => is_var k; destruct k; [inversion H|]
  | H : _ /\ _ |- _ => destruct H
  | H : term_ge ?a (S k),
    IH : forall _, _ -> drop ?a = _ -> _
      |- _ => destruct (IH a H eq_refl) as [? [? ?]]; clear IH
end); subst; simpl in *.
(* 20: CtxLam *)
  exists (F.Lam k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxLam); auto.
(* 19: CtxApp1 *)
  exists (F.App k0 x a2); split; auto.
  apply F.RedCtx with (c := F.CtxApp1 a2); auto.
(* 18: CtxApp2 *)
  exists (F.App k0 a1 x); split; auto.
  apply F.RedCtx with (c := F.CtxApp2 a1); auto.
(* 17: CtxPair1 *)
  exists (F.Pair k0 x a2); split; auto.
  apply F.RedCtx with (c := F.CtxPair1 a2); auto.
(* 16: CtxPair2 *)
  exists (F.Pair k0 a1 x); split; auto.
  apply F.RedCtx with (c := F.CtxPair2 a1); auto.
(* 15: CtxFst *)
  exists (F.Fst k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxFst); auto.
(* 14: CtxSnd *)
  exists (F.Snd k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxSnd); auto.
(* 13: CtxAbsurd *)
  exists (F.Absurd k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxAbsurd); auto.
(* 12: CtxInl *)
  exists (F.Inl k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxInl); auto.
(* 11: CtxInr *)
  exists (F.Inr k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxInr); auto.
(* 10: CtxMatch1 *)
  exists (F.Match k0 x a2 a3); split; auto.
  apply F.RedCtx with (c := F.CtxMatch1 a2 a3); auto.
(* 9: CtxMatch2 *)
  exists (F.Match k0 a1 x a3); split; auto.
  apply F.RedCtx with (c := F.CtxMatch2 a1 a3); auto.
(* 8: CtxMatch3 *)
  exists (F.Match k0 a1 a2 x); split; auto.
  apply F.RedCtx with (c := F.CtxMatch3 a1 a2); auto.
(* 7: CtxInst *)
  exists (F.Inst k0 x); split; auto.
  apply F.RedCtx with (c := F.CtxInst); auto.
(* 5: App *)
  destruct a1; inversion H0; clear H0; subst.
  destruct H1; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (F.subst a2 0 a1)); simpl; split; auto using F.red.
  rewrite <- drop_subst; rewrite drop_lower; reflexivity.
(* 5: Fst *)
  destruct a; inversion H0; clear H0; subst.
  destruct H1 as [? [? ?]]; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a1); simpl; split; auto using F.red.
  rewrite drop_lower; reflexivity.
(* 4: Snd *)
  destruct a; inversion H0; clear H0; subst.
  destruct H1 as [? [? ?]]; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a2); simpl; split; auto using F.red.
  rewrite drop_lower; reflexivity.
(* 3: Inl *)
  destruct a1; inversion H0; clear H0; subst.
  destruct H1; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (F.subst a1 0 a2)); simpl; split; auto using F.red.
  rewrite <- drop_subst; rewrite drop_lower; reflexivity.
(* 2: Inr *)
  destruct a1; inversion H0; clear H0; subst.
  destruct H1; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (F.subst a1 0 a3)); simpl; split; auto using F.red.
  rewrite <- drop_subst; rewrite drop_lower; reflexivity.
(* 1: Inst *)
  destruct a; inversion H0; clear H0; subst.
  destruct H1; destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a); simpl; split; auto using F.red.
  rewrite drop_lower; reflexivity.
Qed.

(** ** Errors and valid terms *)

(** In order to define the notions of errors and valid terms, we need
to define the notions of neutral terms and head normal forms. Neutral
terms [N] are either variables and destructors, while head normal
forms [CN] are constructors.
*)
Definition N : set := fun a =>
  match a with
    | Var _ => True
    | Lam _ => False
    | App _ _ => True
    | Unit => False
    | Pair _ _ => False
    | Fst _ => True
    | Snd _ => True
    | Absurd _ => True
    | Inl _ => False
    | Inr _ => False
    | Match _ _ _ => True
    | Gen _ => False
    | Inst _ => True
  end.

Definition CN : set := fun a =>
  match a with
    | Var _ => False
    | Lam _ => True
    | App _ _ => False
    | Unit => True
    | Pair _ _ => True
    | Fst _ => False
    | Snd _ => False
    | Absurd _ => False
    | Inl _ => True
    | Inr _ => True
    | Match _ _ _ => False
    | Gen _ => True
    | Inst _ => False
  end.
Hint Unfold N CN.

(** Neutral terms and head normal forms partition the set of terms. A
term is either neutral or in head normal form.
*)
Lemma N_dec : forall a, {CN a} + {N a}.
Proof. destruct a; simpl; auto. Qed.

Lemma CN_N : forall a, CN a -> N a -> False.
Proof. destruct a; auto. Qed.

Lemma CN_red : forall a b, red a b -> CN a -> CN b.
Proof.
induction 1; intros CNa; simpl in CNa; try (exfalso; exact CNa).
destruct c; simpl in *; auto.
Qed.

(** We show that neutral terms and head normal forms commute with
[drop], ie. they correspond between both calculi.
*)
Lemma CN_drop : forall a, F.CN a <-> CN (drop a).
Proof. induction a; split; intros Ha; simpl; auto. Qed.

Lemma N_drop : forall a, F.N a <-> N (drop a).
Proof. induction a; split; intros Ha; simpl; auto. Qed.

(** We define predicates to know when a term is not the constructor of
the arrow type, the product type, or the pi type. And we show that
they correspond to their indexed version.
*)
Definition NotArr a := forall a', a <> Lam a'.
Definition NotProd a := forall a' b', a <> Pair a' b'.
Definition NotSum a := forall a', a <> Inl a' /\ a <> Inr a'.
Definition NotPi a := forall a', a <> Gen a'.
Hint Unfold NotArr NotProd NotSum NotPi.

Lemma NotArr_drop : forall a, F.NotArr a <-> NotArr (drop a).
Proof.
split; intros Ha.
(* *)
  intros a' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha k a eq_refl).
(* *)
  intros k' a' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha (drop a') eq_refl).
Qed.

Lemma NotProd_drop : forall a, F.NotProd a <-> NotProd (drop a).
Proof.
split; intros Ha.
(* *)
  intros a' b' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha k a1 a2 eq_refl).
(* *)
  intros k' a' b' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha (drop a') (drop b') eq_refl).
Qed.

Lemma NotSum_drop : forall a, F.NotSum a <-> NotSum (drop a).
Proof.
split; intros Ha.
(* *)
  intros a'; split; intros Heq;
  destruct a; inversion Heq; clear Heq; subst.
  apply (proj1 (Ha k a) eq_refl).
  apply (proj2 (Ha k a) eq_refl).
(* *)
  intros k' a'; split; intros Heq;
  destruct a; inversion Heq; clear Heq; subst.
  apply (proj1 (Ha (drop a')) eq_refl).
  apply (proj2 (Ha (drop a')) eq_refl).
Qed.

Lemma NotPi_drop : forall a, F.NotPi a <-> NotPi (drop a).
Proof.
split; intros Ha.
(* *)
  intros a' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha k a eq_refl).
(* *)
  intros k' a' Heq.
  destruct a; inversion Heq; clear Heq; subst.
  apply (Ha (drop a') eq_refl).
Qed.

(** We can now define the set of errors [Err]. An error is either an
immediate error or an error under any evaluation context. An immediate
error happens when a destructor is applied to a wrong constructor. For
example, the term [App a b] is an error if the term [a] is a
constructor which is not of the arrow type, because [App] is the
destructor of the arrow type. Lambda errors correspond with their
indexed version.
*)
Inductive Err : set :=
| ErrCtx : forall e c, Err e -> Err (fill c e)
| ErrApp : forall a b, CN a -> NotArr a -> Err (App a b)
| ErrFst : forall a, CN a -> NotProd a -> Err (Fst a)
| ErrSnd : forall a, CN a -> NotProd a -> Err (Snd a)
| ErrAbsurd : forall a, CN a -> Err (Absurd a)
| ErrMatch : forall a bl br, CN a -> NotSum a -> Err (Match a bl br)
| ErrInst : forall a, CN a -> NotPi a -> Err (Inst a)
.

Lemma Err_drop : forall a, F.Err a <-> Err (drop a).
Proof.
split.
(* -> *)
  intros H; induction H; simpl.
  (* ErrCtx *) rewrite drop_fill; apply ErrCtx; auto.
  (* ErrApp *) apply ErrApp; [apply CN_drop|apply NotArr_drop]; auto.
  (* ErrFst *) apply ErrFst; [apply CN_drop|apply NotProd_drop]; auto.
  (* ErrSnd *) apply ErrSnd; [apply CN_drop|apply NotProd_drop]; auto.
  (* ErrAbsurd *) apply ErrAbsurd; apply CN_drop; auto.
  (* ErrMatch *) apply ErrMatch; [apply CN_drop|apply NotSum_drop]; auto.
  (* ErrInst *) apply ErrInst; [apply CN_drop|apply NotPi_drop]; auto.
(* <- *)
  remember (drop a) as b.
  intros H; generalize a Heqb; clear a Heqb.
  induction H; simpl; intros.
  (* ErrCtx *)
    destruct c; destruct a; inversion Heqb; clear Heqb.
    apply F.ErrCtx with (c := F.CtxLam); auto.
    apply F.ErrCtx with (c := F.CtxApp1 a2); auto.
    apply F.ErrCtx with (c := F.CtxApp2 a1); auto.
    apply F.ErrCtx with (c := F.CtxPair1 a2); auto.
    apply F.ErrCtx with (c := F.CtxPair2 a1); auto.
    apply F.ErrCtx with (c := F.CtxFst); auto.
    apply F.ErrCtx with (c := F.CtxSnd); auto.
    apply F.ErrCtx with (c := F.CtxAbsurd); auto.
    apply F.ErrCtx with (c := F.CtxInl); auto.
    apply F.ErrCtx with (c := F.CtxInr); auto.
    apply F.ErrCtx with (c := F.CtxMatch1 a2 a3); auto.
    apply F.ErrCtx with (c := F.CtxMatch2 a1 a3); auto.
    apply F.ErrCtx with (c := F.CtxMatch3 a1 a2); auto.
    apply F.ErrCtx with (c := F.CtxInst); auto.
  (* ErrApp *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrApp; [apply CN_drop|apply NotArr_drop]; auto.
  (* ErrFst *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrFst; [apply CN_drop|apply NotProd_drop]; auto.
  (* ErrSnd *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrSnd; [apply CN_drop|apply NotProd_drop]; auto.
  (* ErrAbsurd *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrAbsurd; apply CN_drop; auto.
  (* ErrMatch *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrMatch; [apply CN_drop|apply NotSum_drop]; auto.
  (* ErrInst *)
    destruct a0; inversion Heqb; clear Heqb; subst.
    apply F.ErrInst; [apply CN_drop|apply NotPi_drop]; auto.
Qed.

(** Valid terms are simply the complementary of errors and they
correspond with their indexed version.
*)
Definition V : set := Cmp Err.
Hint Unfold V.

Lemma V_drop : forall a, F.V a <-> V (drop a).
Proof. induction a; split; intros Ha Erra; apply Err_drop in Erra; auto. Qed.

(** ** Strong normalization *)
Inductive SN : set :=
| SN_ : forall a, (forall b, red a b -> SN b) -> SN a
.

Lemma ExpSN : forall a, SN a -> forall b, red a b -> SN b.
Proof. intros; destruct H; auto. Qed.

(** ** Properties about lift and subst *)

Lemma lift_0 : forall a i, lift 0 i a = a.
Proof. induction a; intros i; simpl; [subst_lift_var|..]; f_equal; auto. Qed.

Lemma lift_lift : forall a d i j l, lift d (j + l) (lift (i + j) l a) = lift (i + d + j) l a.
Proof.
induction a; intros d i j l; simpl; auto; [| |f_equal; auto ..].
(* Var *) subst_lift_var; f_equal; omega.
(* Lam *) f_equal; rewrite plus_n_Sm; apply IHa.
(* Match2 *) rewrite plus_n_Sm; auto.
(* Match3 *) rewrite plus_n_Sm; auto.
Qed.

Lemma lift_subst : forall a b d i j,
  lift d j (subst b (i + j) a) = subst b (i + d + j) (lift d j a).
Proof.
induction a; intros b d i j; simpl; auto; [| |f_equal; auto..].
(* Var *)
  subst_lift_var; [|f_equal; omega].
  replace j with (j + 0) by omega; subst.
  rewrite lift_lift.
  f_equal; omega.
(* Lam *)
  f_equal; rewrite plus_n_Sm; rewrite IHa; f_equal; omega.
(* Match2 *)
  rewrite plus_n_Sm; rewrite IHa2; f_equal; omega.
(* Match2 *)
  rewrite plus_n_Sm; rewrite IHa3; f_equal; omega.
Qed.

Lemma subst_lift : forall a b d i l,
  subst b (i + l) (lift (d + 1 + i) l a) = lift (d + i) l a.
Proof.
induction a; intros b d i l; simpl; auto; [| |f_equal; auto..].
(* Var *) subst_lift_var; f_equal; omega.
(* Lam *) f_equal; rewrite plus_n_Sm; rewrite IHa; auto.
(* Match2 *) rewrite plus_n_Sm; auto.
(* Match3 *) rewrite plus_n_Sm; auto.
Qed.

Lemma subst_lift_0 : forall a b, subst b 0 (lift 1 0 a) = a.
Proof. intros a b; pose proof (subst_lift a b 0 0 0); simpl in *; rewrite H; apply lift_0. Qed.

Lemma subst_subst : forall a b bd d i,
  subst bd (d + i) (subst b i a) = subst (subst bd d b) i (subst bd (1 + d + i) a).
Proof.
induction a; intros b bd d i; simpl; auto;
try solve [f_equal; first [rewrite IHa|rewrite IHa1|rewrite IHa2]; reflexivity].
(* Var *)
  subst_lift_var.
  (* *)
    replace (subst bd d) with (subst bd (d + 0)) by (f_equal; omega).
    rewrite lift_subst; f_equal; omega.
  (* *)
    replace i with (i + 0) by omega.
    replace x with (d + 1 + i) by omega.
    rewrite subst_lift.
    f_equal; omega.
(* Lam *)
  f_equal.
  rewrite plus_n_Sm.
  rewrite IHa; reflexivity.
(* Match *)
  f_equal.
  rewrite IHa1; reflexivity.
  rewrite plus_n_Sm; rewrite IHa2; reflexivity.
  rewrite plus_n_Sm; rewrite IHa3; reflexivity.
Qed.

Lemma subst_subst_0 : forall a b bd d,
  subst bd d (subst b 0 a) = subst (subst bd d b) 0 (subst bd (1 + d) a).
Proof.
intros.
replace d with (d + 0) by omega.
rewrite subst_subst; repeat f_equal; omega.
Qed.

Lemma subst_subst_0_0 : forall a b bd,
  subst bd 0 (subst b 0 a) = subst (subst bd 0 b) 0 (subst bd 1 a).
Proof. intros; rewrite subst_subst_0; repeat f_equal; omega. Qed.

Lemma red_subst : forall a a' b, red a a' -> forall i, red (subst b i a) (subst b i a').
Proof.
intros a a' b Hred; induction Hred; [destruct c|..]; intros i; simpl.
(* 20: CtxLam *)
  eapply RedCtx with (c := CtxLam); auto.
(* 19: CtxApp1 *)
  eapply RedCtx with (c := CtxApp1 (subst b i a0)); auto.
(* 18: CtxApp2 *)
  eapply RedCtx with (c := CtxApp2 (subst b i a0)); auto.
(* 17: CtxPair1 *)
  eapply RedCtx with (c := CtxPair1 (subst b i a0)); auto.
(* 16: CtxPair2 *)
  eapply RedCtx with (c := CtxPair2 (subst b i a0)); auto.
(* 15: CtxFst *)
  eapply RedCtx with (c := CtxFst); auto.
(* 14: CtxSnd *)
  eapply RedCtx with (c := CtxSnd); auto.
(* 13: CtxAbsurd *)
  eapply RedCtx with (c := CtxAbsurd); auto.
(* 12: CtxInl *)
  eapply RedCtx with (c := CtxInl); auto.
(* 11: CtxInr *)
  eapply RedCtx with (c := CtxInr); auto.
(* 10: CtxMatch1 *)
  eapply RedCtx with (c := CtxMatch1 (subst b (S i) bl) (subst b (S i) br)); auto.
(* 9: CtxMatch2 *)
  eapply RedCtx with (c := CtxMatch2 (subst b i a0) (subst b (S i) br)); auto.
(* 8: CtxMatch3 *)
  eapply RedCtx with (c := CtxMatch3 (subst b i a0) (subst b (S i) bl)); auto.
(* 7: CtxInst *)
  eapply RedCtx with (c := CtxInst); auto.
(* 6: App *) rewrite subst_subst_0; apply RedApp.
(* 5: Fst *) apply RedFst.
(* 4: Snd *) apply RedSnd.
(* 3: Inl *) rewrite subst_subst_0; apply RedInl.
(* 2: Inr *) rewrite subst_subst_0; apply RedInr.
(* 1: Inst *) apply RedInst.
Qed.

(** ** Values *)

(** We mutually define the set of prevalues 'value False' and values
'value True'.
*)
Fixpoint value v a :=
  match a with
    | Var _ => True
    | Lam a => v /\ value True a
    | App a b  => value False a /\ value True b
    | Unit => v
    | Pair a b => v /\ value True a /\ value True b
    | Fst a => value False a
    | Snd a => value False a
    | Absurd a => value False a
    | Inl a => v /\ value True a
    | Inr a => v /\ value True a
    | Match a bl br => value False a /\ value True bl /\ value True br
    | Gen a  => v
    | Inst a  => value False a
  end.

(** Irreducible terms. *)
Definition irred a := forall b, red a b -> False.
Hint Unfold irred.

(** Prevalues are values. *)
Lemma prevalue_is_value : forall a, value False a -> value True a.
Proof.
induction a; simpl; intros; auto;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
end; auto).
Qed.

(** Neutral values are prevalues. *)
Lemma Nvalue_is_prevalue : forall a, value True a -> N a -> value False a.
Proof.
induction a; simpl; intros; auto;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
end; auto).
Qed.

(** Head normal form are not prevalues. *)
Lemma CNprevalue_is_absurd : forall a, CN a -> value False a -> False.
Proof.
induction a; simpl; intros; auto;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
end; auto).
Qed.

Ltac progre_aux0 ctx :=
  match goal with
    | |- irred _ => intros b Hred;
        match goal with
          | H1 : irred ?Ta , H2 : red ?a ?b
            |- _ => match Ta with context f[a] => let x := context f[b] in apply (H1 x) end
        end; apply RedCtx with (c := ctx); auto
    | H1 : V _ |- V _ => intros Erra; apply H1; apply ErrCtx with (c := ctx); auto
  end.
Ltac progre_arr err :=
  match goal with
    | Va : V _ |- _ => apply Va; apply err; auto; intros x Heq; inversion Heq
  end.
Ltac progre_prod err :=
  match goal with
    | Va : V _ |- _ => apply Va; apply err; auto; intros x y Heq; inversion Heq
  end.
Ltac progre_sum err :=
  match goal with
    | Va : V _ |- _ => apply Va; apply err; auto; intros x; split; intros Heq; inversion Heq
  end.
Ltac progre_aux1 :=
  match goal with
    | Va : V _, ia : irred _ |- N ?a => destruct a; simpl; auto;
      try solve [eapply ia; auto using red]
  end.

(** Values are irreducible valid terms. *)
Lemma progre : forall a, irred a -> V a -> value True a.
Proof.
induction a; intros ia Va; repeat split; auto.
(* 14: CtxLam *)
  apply IHa; progre_aux0 CtxLam.
(* 13: CtxApp1 *)
  apply Nvalue_is_prevalue;
  [ apply IHa1; progre_aux0 (CtxApp1 a2)
  | progre_aux1; progre_arr ErrApp ].
(* 12: CtxApp2 *)
  apply IHa2; progre_aux0 (CtxApp2 a1).
(* 11: CtxPair1 *)
  apply IHa1; progre_aux0 (CtxPair1 a2).
(* 10: CtxPair2 *)
  apply IHa2; progre_aux0 (CtxPair2 a1).
(* 9: CtxFst *)
  apply Nvalue_is_prevalue;
  [ apply IHa; progre_aux0 CtxFst
  | progre_aux1; progre_prod ErrFst ].
(* 8: CtxSnd *)
  apply Nvalue_is_prevalue;
  [ apply IHa; progre_aux0 CtxSnd
  | progre_aux1; progre_prod ErrSnd ].
(* 7: CtxAbsurd *)
  apply Nvalue_is_prevalue;
  [ apply IHa; progre_aux0 CtxAbsurd
  | progre_aux1; progre_prod ErrAbsurd ].
(* 6: CtxInl *)
  apply IHa; progre_aux0 CtxInl.
(* 5: CtxInr *)
  apply IHa; progre_aux0 CtxInr.
(* 4: CtxMatch1 *)
  apply Nvalue_is_prevalue;
  [ apply IHa1; progre_aux0 (CtxMatch1 a2 a3)
  | progre_aux1; progre_sum ErrMatch ].
(* 3: CtxMatch2 *)
  apply IHa2; progre_aux0 (CtxMatch2 a1 a3).
(* 2: CtxMatch3 *)
  apply IHa3; progre_aux0 (CtxMatch3 a1 a2).
(* 1: CtxInst *)
  apply Nvalue_is_prevalue;
  [ apply IHa; progre_aux0 CtxInst
  | progre_aux1; progre_arr ErrInst ].
Qed.

(** Values are irreducible. *)
Lemma irred_value : forall a, value True a -> irred a.
Proof.
intros a vala b Hred.
induction Hred; [destruct c|..]; simpl in *;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
  | H1 : value False ?a
  , Hx : value True ?a -> _
  |- _ => pose proof (Hx (prevalue_is_value a H1)); clear Hx
end; auto); auto.
Qed.

(** Values are valid. *)
Lemma V_value : forall a, value True a -> V a.
Proof.
intros a vala Erra.
induction Erra; [destruct c|..]; simpl in *;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
  | H1 : value False ?a
  , Hx : value True ?a -> _
  |- _ => pose proof (Hx (prevalue_is_value a H1)); clear Hx
  | H1 : value False ?a
  , H2 : CN ?a
  |- False => apply (CNprevalue_is_absurd a)
end; auto).
Qed.

