Require Import Omega.
Require Import Min.
Require Import Max.

Require Import set.
Require Import minmax.

(** * Indexed Calculus *)

(** ** Definition *)

(** *** Terms *)

(** Terms are written [a] or [b]. They are all indexed with a fuel (or
index) [k] which is the first argument of each construct.
*)
Inductive term : Set :=

(** Variables [Var k x], abstractions [Lam k a], and applications [App
k a b] are constructs related to arrow computational types.
*)
| Var (k : nat) (x : nat)
| Lam (k : nat) (a : term)
| App (k : nat) (a : term) (b : term)

(** Pairs [Pair k a b], and projections [Fst k a] and [Snd k a] are
constructs related to product computational types.
*)
| Unit (k : nat)
| Pair (k : nat) (a : term) (b : term)
| Fst (k : nat) (a : term)
| Snd (k : nat) (a : term)

(* sum *)
| Absurd (k : nat) (a : term)
| Inl (k : nat) (a : term)
| Inr (k : nat) (a : term)
| Match (k : nat) (a : term) (bl : term) (br : term)

(** Finally, generalizations [Gen k a] and instantiations [Inst k a]
are related to incoherent polymorphic types, which are computational.
Generalization is a weak reduction abstraction although it does not
bind anything.
*)
| Gen (k : nat) (a : term)
| Inst (k : nat) (a : term)
.

(** *** Functions *)

(** We define a few manipulations of indices and terms. The term
[map_fuel f a] has the same structure as the [a], but where each index
[k] has been modified to [f k]. We lift predicates form indices to
terms in [unary_fuel] for unary predicates and [binary_fuel] for
binary predicates. For binary predicates, the two terms have to share
a common structure.
*)
Definition map_fuel (f : nat -> nat) := fix g a :=
  match a with
    | Var k x => Var (f k) x
    | Lam k a => Lam (f k) (g a)
    | App k a b => App (f k) (g a) (g b)
    | Unit k => Unit (f k)
    | Pair k a b => Pair (f k) (g a) (g b)
    | Fst k a => Fst (f k) (g a)
    | Snd k a => Snd (f k) (g a)
    | Absurd k a => Absurd (f k) (g a)
    | Inl k a => Inl (f k) (g a)
    | Inr k a => Inr (f k) (g a)
    | Match k a bl br => Match (f k) (g a) (g bl) (g br)
    | Gen k a => Gen (f k) (g a)
    | Inst k a => Inst (f k) (g a)
  end.

Definition unary_fuel f := fix g a :=
  match a with
    | Var k x => f k
    | Lam k a => f k /\ g a
    | App k a b => f k /\ g a /\ g b
    | Unit k => f k
    | Pair k a b => f k /\ g a /\ g b
    | Fst k a => f k /\ g a
    | Snd k a => f k /\ g a
    | Absurd k a => f k /\ g a
    | Inl k a => f k /\ g a
    | Inr k a => f k /\ g a
    | Match k a bl br => f k /\ g a /\ g bl /\ g br
    | Gen k a => f k /\ g a
    | Inst k a => f k /\ g a
  end.

Definition binary_fuel f := fix g a b :=
  match a, b with
    | Var j x, Var k y => f j k /\ x = y
    | Lam j a, Lam k b => f j k /\ g a b
    | App j a1 a2, App k b1 b2 => f j k /\ g a1 b1 /\ g a2 b2
    | Unit j, Unit k => f j k
    | Pair j a1 a2, Pair k b1 b2 => f j k /\ g a1 b1 /\ g a2 b2
    | Fst j a, Fst k b => f j k /\ g a b
    | Snd j a, Snd k b => f j k /\ g a b
    | Absurd j a, Absurd k b => f j k /\ g a b
    | Inl j a, Inl k b => f j k /\ g a b
    | Inr j a, Inr k b => f j k /\ g a b
    | Match j a al ar, Match k b bl br => f j k /\ g a b /\ g al bl /\ g ar br
    | Gen j a, Gen k b => f j k /\ g a b
    | Inst j a, Inst k b => f j k /\ g a b
    | _, _ => False
  end.

(** We define a few common instantiations of these last three
functions. The function [lower k] updates to [k] the indices greater
than [k]. The binary predicate [le_term a b] holds when the term [a]
is pointwise less or equal than the term [b]. Finally, the predicates
[term_le a k], [term_lt a k], and [term_ge a k] say when the indices
of the term [a] are all less or equal, less than, and greater or equal
than [k], respectively.
*)
Definition lower k := map_fuel (fun j => min j k).
Definition le_term := binary_fuel le.
Definition term_le a k := unary_fuel (fun j => j <= k) a.
Definition term_lt a k := unary_fuel (fun j => j < k) a.
Definition term_ge a k := unary_fuel (fun j => j >= k) a.
Hint Unfold lower le_term term_le term_lt term_ge.

Ltac destruct_binary a H :=
  destruct a; simpl in H; try (exfalso; exact H);
  match type of H with
    | _ /\ _ /\ _ /\ _ => destruct H as [? [? [? ?]]]
    | _ /\ _ /\ _ => destruct H as [? [? ?]]
    | _ /\ _ => destruct H
    | _ => idtac
  end.

(** We define a function to traverse terms and operating on its
variables. The term [traverse f i a] has the same structure as [a] but
for its variables [Var k x] that become [f k x i]. The level [i]
indicates how deep we are in the term: it is incremented each time we
cross a binder. The only binder of the Indexed Calculus is [Lam] and
it binds only one term, so the recursive call uses the level [1 + i].
*)
Definition traverse f := fix g i a :=
  match a with
  | Var k x => f k x i
  | Lam k a => Lam k (g (1 + i) a)
  | App k a b => App k (g i a) (g i b)
  | Unit k => Unit k
  | Pair k a b => Pair k (g i a) (g i b)
  | Fst k a => Fst k (g i a)
  | Snd k a => Snd k (g i a)
  | Absurd k a => Absurd k (g i a)
  | Inl k a => Inl k (g i a)
  | Inr k a => Inr k (g i a)
  | Match k a bl br => Match k (g i a) (g (1 + i) bl) (g (1 + i) br)
  | Gen k a => Gen k (g i a)
  | Inst k a => Inst k (g i a)
  end.

(** We define the lifting function [lift] and substitution function
[subst] using the [traverse] function with the [lift_idx] and
[subst_idx] functions, respectively. The term [lift d i a] has the
same structure as [a] but the variables greater or equal than [i] are
incremented by [d]. The term [subst b i a] has the same structure as
[a] but the variables greater than [i] are decremented by one and the
variables equal to [i] are replaced with [b] lifted by [i] from level
[0] and lowered with the index [k] of the variable. This lowering is
necessary for lemma [lower_subst] and [subst_lower].
*)
Definition lift_idx d k x i := Var k (if le_gt_dec i x then d + x else x).
Definition lift d := traverse (lift_idx d).
Definition shift := lift 1.
Hint Unfold lift_idx lift shift.

Definition subst_idx b k x i :=
  match lt_eq_lt_dec x i with
    | inleft (left _)  => Var k x
    | inleft (right _) => lower k (lift x 0 b)
    | inright _        => Var k (x - 1)
  end.
Definition subst b := traverse (subst_idx b).
Hint Unfold subst_idx subst.

Ltac subst_lift_var := repeat (match goal with
    | |- context[subst_idx] => unfold subst_idx
    | |- context[lift_idx] => unfold lift_idx
    | |- context[lt_eq_lt_dec ?x ?y] => destruct (lt_eq_lt_dec x y) as [[?|?]|?]; try (exfalso; omega); simpl; auto
    | |- context[le_gt_dec ?x ?y] => destruct (le_gt_dec x y); try (exfalso; omega); simpl; auto
  end).

Definition set := @set term.

(** *** Reduction *)

(** Evaluation contexts [Ctx] contain all one-hole contexts of depth
one, but for [Gen]. This gives us strong reduction for all constructs
but [Gen], because the only role [Gen] is to block reduction. The
meaning of [Ctx] is given by the [fill] function. The term [fill c k
a] wraps the term [a] under the context [c] with index [k].
*)
Inductive Ctx : Set :=
| CtxLam
| CtxApp1 (b : term)
| CtxApp2 (a : term)
| CtxPair1 (b : term)
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

Definition fill c k a :=
  match c with
    | CtxLam => Lam k a
    | CtxApp1 b => App k a b
    | CtxApp2 b => App k b a
    | CtxPair1 b => Pair k a b
    | CtxPair2 b => Pair k b a
    | CtxFst => Fst k a
    | CtxSnd => Snd k a
    | CtxAbsurd => Absurd k a
    | CtxInl => Inl k a
    | CtxInr => Inr k a
    | CtxMatch1 b1 b2 => Match k a b1 b2
    | CtxMatch2 b1 b2 => Match k b1 a b2
    | CtxMatch3 b1 b2 => Match k b1 b2 a
    | CtxInst => Inst k a
  end.

(** The reduction relation [red] has the usual rule of the Lambda
Calculus modulo the notion of indices. The indices of redex nodes of
the left-hand side of the reduction rule have to be strictly positive.
The right-hand side of the reduction rule is lowered by the minimum of
these first indices minus one. For example, the usual beta-reduction
rule:

[[
  red (App (Lam a) b) (subst b 0 a)
]]

becomes:

[[
  red (App (1 + k') (Lam (1 + k) a) b)
      (lower (min k' k) (subst b 0 a))
]]

Similarly for the context rule RedCtx which lowers the index (which
had to be strictly positive) of context node by one.

This index-manipulation is very brutal: it simplifies greatly the
proof of strong normalization [wf_der] in [Fnormalization_v] of the
untyped Indexed Calculus, but breaks confluence and some other
reduction related properties that we have in the Lambda Calculus.
*)
Inductive red : term -> term -> Prop :=
| RedCtx : forall k a a' c, red a a' -> red (fill c (1 + k) a) (fill c k a')
| RedApp : forall k k' a b, red (App (1 + k') (Lam (1 + k) a) b) (lower (min k' k) (subst b 0 a))
| RedFst : forall k k' a b, red (Fst (1 + k') (Pair (1 + k) a b)) (lower (min k' k) a)
| RedSnd : forall k k' a b, red (Snd (1 + k') (Pair (1 + k) a b)) (lower (min k' k) b)
| RedInl : forall k k' a bl br, red (Match (1 + k') (Inl (1 + k) a) bl br) (lower (min k' k) (subst a 0 bl))
| RedInr : forall k k' a bl br, red (Match (1 + k') (Inr (1 + k) a) bl br) (lower (min k' k) (subst a 0 br))
| RedInst : forall k k' a, red (Inst (1 + k') (Gen (1 + k) a)) (lower (min k' k) a)
.

(** *** Errors and valid terms *)

(** In order to define the notions of errors and valid terms, we need
to define the notions of neutral terms and head normal forms. Neutral
terms [N] are either variables and destructors, while head normal
forms [CN] are constructors.
*)
Definition N : set := fun a =>
  match a with
    | Var _ _ => True
    | Lam _ _ => False
    | App _ _ _ => True
    | Unit _ => False
    | Pair _ _ _ => False
    | Fst _ _ => True
    | Snd _ _ => True
    | Absurd _ _ => True
    | Inl _ _ => False
    | Inr _ _ => False
    | Match _ _ _ _ => True
    | Gen _ _ => False
    | Inst _ _ => True
  end.

Definition CN : set := fun a =>
  match a with
    | Var _ _ => False
    | Lam _ _ => True
    | App _ _ _ => False
    | Unit _ => True
    | Pair _ _ _ => True
    | Fst _ _ => False
    | Snd _ _ => False
    | Absurd _ _ => False
    | Inl _ _ => True
    | Inr _ _ => True
    | Match _ _ _ _ => False
    | Gen _ _ => True
    | Inst _ _ => False
  end.
Hint Unfold N CN.

(** Neutral terms and head normal forms partition the set of terms. A
term is either neutral or in head normal form.
*)
Lemma N_dec : forall a, {CN a} + {N a}.
Proof. destruct a; simpl; auto. Qed.

Lemma CN_N : forall a, CN a -> N a -> False.
Proof. destruct a; auto. Qed.

(** Head normal forms are preserved by substitution, reduction, and
lifting of binary predicates, such as [le_term].
*)
Lemma CN_subst : forall a, CN a -> forall b i, CN (subst b i a).
Proof.
induction a; simpl; intros; auto.
subst_lift_var.
Qed.

Lemma CN_red : forall a b, red a b -> CN a -> CN b.
Proof.
induction 1; intros CNa; simpl in CNa; try (exfalso; exact CNa).
destruct c; simpl in *; auto.
Qed.

Lemma CN_le_term : forall a b, le_term a b -> CN a -> CN b.
Proof.
induction a; simpl; intros b ab CNa; try (exfalso; exact CNa);
destruct_binary b ab; simpl; exact I.
Qed.

(** We define predicates to know when a term is not the constructor of
the arrow type, the product type, or the pi type. And we show that
they are stable by substitution and lifting of binary predicates.
*)
Definition NotArr a := forall k' a', a <> Lam k' a'.
Definition NotProd a := forall k' a' b', a <> Pair k' a' b'.
Definition NotSum a := forall k' a', a <> Inl k' a' /\ a <> Inr k' a'.
Definition NotPi a := forall k' a', a <> Gen k' a'.
Hint Unfold NotArr NotProd NotSum NotPi.

Lemma NotArr_subst : forall a, CN a -> NotArr a -> forall b i, NotArr (subst b i a).
Proof.
induction a; simpl; intro CNa; try (exfalso; exact CNa);
intros; intro k'; intros; intro Heq; auto; inversion Heq; clear Heq; subst.
apply (H k' a eq_refl).
Qed.

Lemma NotArr_le_term : forall a b, le_term a b -> NotArr a -> NotArr b.
Proof.
induction a; simpl; intros b ab NAa; destruct_binary b ab;
intros k' a' Heq; inversion Heq; subst.
apply (NAa k a eq_refl).
Qed.

Lemma NotProd_subst : forall a, CN a -> NotProd a -> forall b i, NotProd (subst b i a).
Proof.
induction a; simpl; intro CNa; try (exfalso; exact CNa);
intros; intro k'; intros; intro Heq; auto; inversion Heq; clear Heq; subst.
apply (H k' a1 a2 eq_refl).
Qed.

Lemma NotProd_le_term : forall a b, le_term a b -> NotProd a -> NotProd b.
Proof.
induction a; simpl; intros b ab NPa; destruct_binary b ab;
intros k' a' b' Heq; inversion Heq; subst.
apply (NPa k a1 a2 eq_refl).
Qed.

Lemma NotSum_subst : forall a, CN a -> NotSum a -> forall b i, NotSum (subst b i a).
Proof.
induction a; simpl; intro CNa; try (exfalso; exact CNa);
intros; intro k'; intros; split; intro Heq; auto; inversion Heq; clear Heq; subst.
apply (proj1 (H k' a) eq_refl).
apply (proj2 (H k' a) eq_refl).
Qed.

Lemma NotSum_le_term : forall a b, le_term a b -> NotSum a -> NotSum b.
Proof.
induction a; simpl; intros b ab NAa; destruct_binary b ab;
intros k' a'; split; intros Heq; inversion Heq; subst.
apply (proj1 (NAa k a) eq_refl).
apply (proj2 (NAa k a) eq_refl).
Qed.

Lemma NotPi_subst : forall a, CN a -> NotPi a -> forall b i, NotPi (subst b i a).
Proof.
induction a; simpl; intro CNa; try (exfalso; exact CNa);
intros; intro k'; intros; intro Heq; auto; inversion Heq; clear Heq; subst.
apply (H k' a eq_refl).
Qed.

Lemma NotPi_le_term : forall a b, le_term a b -> NotPi a -> NotPi b.
Proof.
induction a; simpl; intros b ab NAa; destruct_binary b ab;
intros k' a'; intros Heq; inversion Heq; subst.
apply (NAa k a eq_refl).
Qed.

(** We can now define the set of errors [Err]. An error is either an
immediate error or an error under any evaluation context. An immediate
error happens when a destructor is applied to a wrong constructor. For
example, the term [App k a b] is an error if the term [a] is a
constructor which is not of the arrow type, because [App] is the
destructor of the arrow type.
*)
Inductive Err : set :=
| ErrCtx : forall k e c, Err e -> Err (fill c k e)
| ErrApp : forall k a b, CN a -> NotArr a -> Err (App k a b)
| ErrFst : forall k a, CN a -> NotProd a -> Err (Fst k a)
| ErrSnd : forall k a, CN a -> NotProd a -> Err (Snd k a)
| ErrAbsurd : forall k a, CN a -> Err (Absurd k a)
| ErrMatch : forall k a bl br, CN a -> NotSum a -> Err (Match k a bl br)
| ErrInst : forall k a, CN a -> NotPi a -> Err (Inst k a)
.

(** Valid terms are simply the complementary of errors. We write [NV]
for neutral valid terms.
*)
Definition V : set := Cmp Err.
Hint Unfold V.

Definition NV : set := Inter N V.

(** ** Properties *)

(** Variables are valid neutral terms. Term abstraction are valid if
their body is valid too. Pairs are valid if their components are valid
too.
*)
Lemma V_Var : forall {k n}, V (Var k n).
Proof.
intros k n Herr; inversion Herr.
destruct c; inversion H.
Qed.

Lemma NV_Var : forall {k n}, NV (Var k n).
Proof. split; [exact I|apply V_Var]. Qed.

Lemma V_Unit : forall {k}, V (Unit k).
Proof.
intros k Herr; inversion Herr; auto.
destruct c; inversion H; clear H; subst; auto.
Qed.

Lemma V_Lam : forall {k a}, V a -> V (Lam k a).
Proof.
intros k a H Herr; inversion Herr; auto.
destruct c; inversion H0; clear H0; subst; auto.
Qed.

Lemma V_Pair : forall {k a b}, V a -> V b -> V (Pair k a b).
Proof.
intros k a b Ha Hb Herr; inversion Herr; auto.
destruct c; inversion H; clear H; subst; auto.
Qed.

Lemma V_Inl : forall {k a}, V a -> V (Inl k a).
Proof.
intros k a H Herr; inversion Herr; auto.
destruct c; inversion H0; clear H0; subst; auto.
Qed.

Lemma V_Inr : forall {k a}, V a -> V (Inr k a).
Proof.
intros k a H Herr; inversion Herr; auto.
destruct c; inversion H0; clear H0; subst; auto.
Qed.

(** Neutral terms behave like variables with respect to validity. When
a term is valid after subsittution by a neutral, then it was also
valid before the substitution.
*)
Lemma V_subst_N : forall a b, N b -> forall i, V (subst b i a) -> V a.
Proof.
intros a b Nb; induction a; intros i Va;
try (intros Errb; inversion Errb; clear Errb; subst);
try match goal with
  | H : fill ?c _ _ = _ |- _ => destruct c; inversion H; clear H; subst
end;
try match goal with
  | IH : forall _, _ -> V ?a
  , H : Err ?a |- _ => eapply IH; [|exact H]; intro; apply Va; simpl
end.
(* 20: CtxLam *)
  replace (Lam k (subst b (S i) a)) with (fill CtxLam k (subst b (S i) a)) by reflexivity.
  apply ErrCtx; eauto.
(* 19: CtxApp1 *)
  replace (App k (subst b i a1) (subst b i a2))
    with (fill (CtxApp1 (subst b i a2)) k (subst b i a1)) by reflexivity.
  apply ErrCtx; eauto.
(* 18: CtxApp2 *)
  replace (App k (subst b i a1) (subst b i a2))
    with (fill (CtxApp2 (subst b i a1)) k (subst b i a2)) by reflexivity.
  apply ErrCtx; eauto.
(* 17: App *)
  apply Va; simpl.
  apply ErrApp.
  apply CN_subst; auto.
  apply NotArr_subst; auto.
(* 16: CtxPair1 *)
  replace (Pair k (subst b i a1) (subst b i a2))
    with (fill (CtxPair1 (subst b i a2)) k (subst b i a1)) by reflexivity.
  apply ErrCtx; eauto.
(* 15: CtxPair2 *)
  replace (Pair k (subst b i a1) (subst b i a2))
    with (fill (CtxPair2 (subst b i a1)) k (subst b i a2)) by reflexivity.
  apply ErrCtx; eauto.
(* 14: CtxFst *)
  replace (Fst k (subst b i a)) with (fill CtxFst k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 13: Fst *)
  apply Va; simpl.
  apply ErrFst.
  apply CN_subst; auto.
  apply NotProd_subst; auto.
(* 12: CtxSnd *)
  replace (Snd k (subst b i a)) with (fill CtxSnd k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 11: Snd *)
  apply Va; simpl.
  apply ErrSnd.
  apply CN_subst; auto.
  apply NotProd_subst; auto.
(* 10: CtxAbsurd *)
  replace (Absurd k (subst b i a)) with (fill CtxAbsurd k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 9: Absurd *)
  apply Va; simpl.
  apply ErrAbsurd.
  apply CN_subst; auto.
(* 8: CtxInl *)
  replace (Inl k (subst b i a)) with (fill CtxInl k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 7: CtxInr *)
  replace (Inr k (subst b i a)) with (fill CtxInr k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 6: CtxMatch1 *)
  replace (Match k (subst b i a1) (subst b (S i) a2) (subst b (S i) a3))
    with (fill (CtxMatch1 (subst b (S i) a2) (subst b (S i) a3)) k (subst b i a1)) by reflexivity.
  apply ErrCtx; eauto.
(* 5: CtxMatch2 *)
  replace (Match k (subst b i a1) (subst b (S i) a2) (subst b (S i) a3))
    with (fill (CtxMatch2 (subst b i a1) (subst b (S i) a3)) k (subst b (S i) a2)) by reflexivity.
  apply ErrCtx; eauto.
(* 4: CtxMatch3 *)
  replace (Match k (subst b i a1) (subst b (S i) a2) (subst b (S i) a3))
    with (fill (CtxMatch3 (subst b i a1) (subst b (S i) a2)) k (subst b (S i) a3)) by reflexivity.
  apply ErrCtx; eauto.
(* 3: Match *)
  apply Va; simpl.
  apply ErrMatch.
  apply CN_subst; auto.
  apply NotSum_subst; auto.
(* 2: CtxInst *)
  replace (Inst k (subst b i a)) with (fill CtxInst k (subst b i a)) by reflexivity.
  apply ErrCtx; eauto.
(* 1: Gen *)
  apply Va; simpl.
  apply ErrInst.
  apply CN_subst; auto.
  apply NotPi_subst; auto.
Qed.

(** We now have some commutation and fusion lemma about lifting,
substitution, reduction and indices functions and predicates.
*)
Lemma lift_0 : forall a i, lift 0 i a = a.
Proof. induction a; intros i; simpl; [subst_lift_var|..]; f_equal; auto. Qed.

Lemma unary_fuel_1 : forall (f g : nat -> Prop), (forall j, f j -> g j) ->
  forall a, unary_fuel f a -> unary_fuel g a.
Proof.
intros f g fg; induction a; simpl; intros H;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
end; auto); auto.
Qed.

Lemma unary_fuel_2 : forall (g f1 f2 : nat -> Prop), (forall j, f1 j -> f2 j -> g j) ->
  forall a, unary_fuel f1 a -> unary_fuel f2 a -> unary_fuel g a.
Proof.
intros g f1 f2 fg; induction a; simpl; intros H1 H2;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
end; auto); auto.
Qed.

Lemma unary_fuel_map : forall (f : nat -> Prop) upd,
  (forall k, f k -> f (upd k)) ->
  forall a, unary_fuel f a -> unary_fuel f (map_fuel upd a).
Proof.
intros f upd fupd; induction a; intros H; simpl in *;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
end; auto); auto.
Qed.

Lemma unary_fuel_map_trivial : forall (f : nat -> Prop) upd,
  (forall k, f (upd k)) -> forall a, unary_fuel f (map_fuel upd a).
Proof.
intros f upd fupd; induction a; simpl in *;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
end; auto); auto.
Qed.

Lemma map_fuel_lift : forall d f a i,
  map_fuel f (lift d i a) = lift d i (map_fuel f a).
Proof. intros d f a; induction a; intros i; simpl; f_equal; auto. Qed.

Lemma lower_lift : forall d k a i,
  lower k (lift d i a) = lift d i (lower k a).
Proof. intros d k a i; apply map_fuel_lift. Qed.

Lemma lower_lower : forall k k' a, lower k (lower k' a) = lower (min k' k) a.
Proof. induction a; simpl; f_equal; auto; rewrite min_assoc; reflexivity. Qed.

Lemma lower_subst : forall b k a i,
  lower k (subst b i a) = subst b i (lower k a).
Proof.
intros b k a; induction a; intros i; simpl; f_equal; auto.
unfold subst_idx; destruct (lt_eq_lt_dec x i) as [[?|?]|?]; simpl; auto.
rewrite lower_lower; reflexivity.
Qed.

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
  rewrite <- lower_lift; f_equal.
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
    rewrite <- lower_subst; f_equal.
    replace (subst bd d) with (subst bd (d + 0)) by (f_equal; omega).
    rewrite lift_subst; f_equal; omega.
  (* *)
    rewrite <- lower_subst; f_equal.
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

Lemma binary_fuel_map : forall (op : nat -> nat -> Prop) upd' upd,
  (forall k' k, op k' k -> op (upd' k') (upd k)) ->
  forall a' a, binary_fuel op a' a -> binary_fuel op (map_fuel upd' a') (map_fuel upd a).
Proof.
intros op upd' upd H a'.
induction a'; intros; destruct_binary a H0; simpl; auto.
Qed.

Lemma binary_fuel_map_trivial : forall (op : nat -> nat -> Prop) upd,
  (forall k, op (upd k) k) ->
  forall a, binary_fuel op (map_fuel upd a) a.
Proof. intros op upd H a; induction a; simpl; auto. Qed.

Lemma binary_fuel_trans : forall (op : nat -> nat -> Prop),
  (forall k1 k2 k3, op k1 k2 -> op k2 k3 -> op k1 k3) ->
  forall a1 a2 a3, binary_fuel op a1 a2 -> binary_fuel op a2 a3 -> binary_fuel op a1 a3.
Proof.
intros op H a1.
induction a1; intros; destruct_binary a2 H0; destruct_binary a3 H1; simpl;
repeat split; first [omega|eauto].
Qed.

Lemma binary_fuel_refl : forall (op : nat -> nat -> Prop),
  (forall k, op k k) -> forall a, binary_fuel op a a.
Proof. intros op H a; induction a; simpl; try split; first [omega|eauto]. Qed.

Lemma le_term_lower : forall k' k a' a, k' <= k -> le_term a' a ->
  le_term (lower k' a') (lower k a).
Proof. intros; apply binary_fuel_map; intros; auto; minmax. Qed.

Lemma le_term_lower_trivial : forall k a, le_term (lower k a) a.
Proof. intros; apply binary_fuel_map_trivial; intros; minmax. Qed.

Lemma binary_fuel_lift : forall op d a' a i, binary_fuel op a' a ->
  binary_fuel op (lift d i a') (lift d i a).
Proof. induction a'; intros; destruct_binary a H; subst; simpl; auto. Qed.

Lemma le_term_subst : forall a' a b' b i, le_term b' b -> le_term a' a ->
  le_term (subst b' i a') (subst b i a).
Proof.
induction a'; intros; destruct_binary a H0; subst; simpl; auto.
(* Var *)
  unfold subst_idx.
  destruct (lt_eq_lt_dec x0 i) as [[?|?]|?]; subst; simpl; auto.
  rewrite 2 lower_lift.
  apply binary_fuel_lift.
  apply binary_fuel_map; auto.
  intros; minmax.
Qed.

Lemma le_term_red : forall a a' b', le_term a' a -> red a' b' -> exists b, red a b /\ le_term b' b.
Proof.
intros a a' b' lea Hred'; generalize a lea; clear a lea.
induction Hred'; intros; [destruct c|..]; destruct_binary a0 lea;
try match goal with
  | [ H1 : forall _, le_term ?a _ -> _
    , H2 : le_term ?a _ |- _ ] => destruct (H1 _ H2) as [? [? ?]]; clear H1 H2
end;
try match goal with
  | [ H : S _ <= ?k |- _ ] => destruct k; [inversion H|]
end.
(* 20: CtxLam *)
  exists (Lam k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxLam); auto.
(* 19: CtxApp1 *)
  exists (App k0 x a0_2); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_1 x (CtxApp1 a0_2)); auto.
(* 18: CtxApp2 *)
  exists (App k0 a0_1 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_2 x (CtxApp2 a0_1)); auto.
(* 17: CtxPair1 *)
  exists (Pair k0 x a0_2); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_1 x (CtxPair1 a0_2)); auto.
(* 16: CtxPair2 *)
  exists (Pair k0 a0_1 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_2 x (CtxPair2 a0_1)); auto.
(* 15: CtxFst *)
  exists (Fst k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxFst); auto.
(* 14: CtxSnd *)
  exists (Snd k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxSnd); auto.
(* 13: CtxAbsurd *)
  exists (Absurd k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxAbsurd); auto.
(* 12: CtxInl *)
  exists (Inl k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxInl); auto.
(* 11: CtxInr *)
  exists (Inr k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxInr); auto.
(* 10: CtxMatch1 *)
  exists (Match k0 x a0_2 a0_3); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_1 x (CtxMatch1 a0_2 a0_3)); auto.
(* 9: CtxMatch2 *)
  exists (Match k0 a0_1 x a0_3); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_2 x (CtxMatch2 a0_1 a0_3)); auto.
(* 8: CtxMatch3 *)
  exists (Match k0 a0_1 a0_2 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0_3 x (CtxMatch3 a0_1 a0_2)); auto.
(* 7: CtxInst *)
  exists (Inst k0 x); split; [|simpl; repeat split; first [omega|auto]].
  apply (RedCtx k0 a0 x CtxInst); auto.
(* 6: App *)
  destruct_binary a0_1 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (subst a0_2 0 a0_1)).
  split; [apply RedApp|].
  apply le_term_lower; [minmax|].
  apply le_term_subst; assumption.
(* 5: Fst *)
  destruct_binary a0 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a0_1).
  split; [apply RedFst|].
  apply le_term_lower; [minmax|assumption].
(* 4: Snd *)
  destruct_binary a0 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a0_2).
  split; [apply RedSnd|].
  apply le_term_lower; [minmax; omega|assumption].
(* 3: Inl *)
  destruct_binary a0_1 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (subst a0_1 0 a0_2)).
  split; [apply RedInl|].
  apply le_term_lower; [minmax|].
  apply le_term_subst; assumption.
(* 2: Inr *)
  destruct_binary a0_1 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) (subst a0_1 0 a0_3)).
  split; [apply RedInr|].
  apply le_term_lower; [minmax|].
  apply le_term_subst; assumption.
(* 1: Inst *)
  destruct_binary a0 H0.
  destruct k1; [inversion H0|].
  exists (lower (min k0 k1) a0).
  split; [apply RedInst|].
  apply le_term_lower; [minmax; omega|assumption].
Qed.

Lemma term_ge_dec : forall a k, term_ge a (1 + k) -> term_ge a k.
Proof.
intros a k H.
eapply unary_fuel_1; [|apply H].
simpl; intros; omega.
Qed.

Lemma term_ge_lower : forall k k', k' >= k -> forall a, term_ge a k -> term_ge (lower k' a) k.
Proof.
intros k k' kk' a H.
eapply unary_fuel_map; [|apply H].
intros; apply min_glb; omega.
Qed.

Lemma unary_fuel_traverse : forall (f : nat -> Prop) g, (forall k x i, f k -> unary_fuel f (g k x i)) ->
  forall a i, unary_fuel f a -> unary_fuel f (traverse g i a).
Proof.
intros f g fg; induction a; intros i H; simpl in *;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- _ >= _ => omega
end; auto); auto.
Qed.

Lemma unary_fuel_lift : forall f d a i, unary_fuel f a -> unary_fuel f (lift d i a).
Proof.
intros f d a i H.
apply unary_fuel_traverse; [|apply H].
intros k x l fk; subst_lift_var.
Qed.

Lemma term_ge_lift : forall d a k i, term_ge a k -> term_ge (lift d i a) k.
Proof. intros d a k i H; apply unary_fuel_lift; apply H. Qed.

Lemma unary_fuel_subst : forall (f : nat -> Prop), (forall j k, f j -> f k -> f (min j k)) ->
  forall a b i, unary_fuel f a -> unary_fuel f b -> unary_fuel f (subst b i a).
Proof.
intros f Hf a b i Ha Hb.
apply unary_fuel_traverse; [|apply Ha].
intros k x l fk; subst_lift_var.
apply unary_fuel_map; auto.
apply unary_fuel_lift; apply Hb.
Qed.

Lemma term_ge_subst : forall a k b i, term_ge a k -> term_ge b k -> term_ge (subst b i a) k.
Proof.
intros a k b i Ha Hb.
apply unary_fuel_subst; auto.
intros j1 j2; apply min_glb.
Qed.

Lemma unary_fuel_red : forall (f g : nat -> Prop),
  (forall k, f (S k) -> g k) -> (forall k, f k -> g k) -> (forall j k, g j -> g k -> g (min j k)) ->
  forall a b, red a b -> unary_fuel f a -> unary_fuel g b.
Proof.
intros f g HS Hinc Hmin a b Hred; induction Hred; [destruct c|..]; simpl; intros Ha;
repeat (match goal with
  | H : unary_fuel f ?a |- unary_fuel g ?a => apply unary_fuel_1 with (f := f); [apply Hinc|apply H]
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- _ >= _ => omega
end; auto); auto.
(* App *)
  apply unary_fuel_map; [|apply unary_fuel_subst]; auto; apply unary_fuel_1 with (f := f); auto.
(* Fst *) apply unary_fuel_map; auto; apply unary_fuel_1 with (f := f); auto.
(* Snd *) apply unary_fuel_map; auto; apply unary_fuel_1 with (f := f); auto.
(* Inl *)
  apply unary_fuel_map; [|apply unary_fuel_subst]; auto; apply unary_fuel_1 with (f := f); auto.
(* Inr *)
  apply unary_fuel_map; [|apply unary_fuel_subst]; auto; apply unary_fuel_1 with (f := f); auto.
(* Inst *) apply unary_fuel_map; auto; apply unary_fuel_1 with (f := f); auto.
Qed.

Lemma term_ge_red : forall a b k, red a b -> term_ge a (1 + k) -> term_ge b k.
Proof.
intros a b k Hred Ha.
eapply unary_fuel_red; [| | |apply Hred|apply Ha]; intros.
(* *) simpl in H; omega.
(* *) simpl in H; omega.
(* *) apply min_glb; omega.
Qed.

Lemma term_le_red : forall a b k, red a b -> term_le a k -> term_le b k.
Proof.
intros a b k Hred Ha.
eapply unary_fuel_red; [| | |apply Hred|apply Ha]; intros.
(* *) simpl in H; omega.
(* *) simpl in H; omega.
(* *) minmax.
Qed.

Lemma red_0 : forall a b, term_lt a 0 -> red a b -> False.
Proof.
intros a b H Hred; induction Hred; [destruct c|..]; simpl in *;
repeat (match goal with
  | H : _ < 0 |- _ => inversion H
  | H : _ /\ _ |- _ => destruct H
end; auto); auto.
Qed.

Lemma term_lt_red : forall a b k, red a b -> term_lt a k -> term_lt b k.
Proof.
intros a b k Hred Ha.
destruct k; [exfalso; eapply red_0; eauto|].
eapply unary_fuel_1; [|apply (term_le_red a b k Hred); eapply unary_fuel_1; [|apply Ha]];
instantiate; simpl; intros j H; omega.
Qed.

Lemma red_subst : forall a a' b, red a a' -> forall i, red (subst b i a) (subst b i a').
Proof.
intros a a' b Hred; induction Hred; [destruct c|..]; intros i; simpl.
(* 20: CtxLam *)
  eapply RedCtx with (k := k) (c := CtxLam); auto.
(* 19: CtxApp1 *)
  eapply RedCtx with (k := k) (c := CtxApp1 (subst b i b0)); auto.
(* 18: CtxApp2 *)
  eapply RedCtx with (k := k) (c := CtxApp2 (subst b i a0)); auto.
(* 17: CtxPair1 *)
  eapply RedCtx with (k := k) (c := CtxPair1 (subst b i b0)); auto.
(* 16: CtxPair2 *)
  eapply RedCtx with (k := k) (c := CtxPair2 (subst b i a0)); auto.
(* 15: CtxFst *)
  eapply RedCtx with (k := k) (c := CtxFst); auto.
(* 14: CtxSnd *)
  eapply RedCtx with (k := k) (c := CtxSnd); auto.
(* 13: CtxAbsurd *)
  eapply RedCtx with (k := k) (c := CtxAbsurd); auto.
(* 12: CtxInl *)
  eapply RedCtx with (k := k) (c := CtxInl); auto.
(* 11: CtxInr *)
  eapply RedCtx with (k := k) (c := CtxInr); auto.
(* 10: CtxMatch1 *)
  eapply RedCtx with (k := k) (c := CtxMatch1 (subst b (S i) bl) (subst b (S i) br)); auto.
(* 9: CtxMatch2 *)
  eapply RedCtx with (k := k) (c := CtxMatch2 (subst b i a0) (subst b (S i) br)); auto.
(* 8: CtxMatch3 *)
  eapply RedCtx with (k := k) (c := CtxMatch3 (subst b i a0) (subst b (S i) bl)); auto.
(* 7: CtxInst *)
  eapply RedCtx with (k := k) (c := CtxInst); auto.
(* 6: App *) rewrite <- lower_subst; rewrite subst_subst_0; apply RedApp.
(* 5: Fst *) rewrite <- lower_subst; apply RedFst.
(* 4: Snd *) rewrite <- lower_subst; apply RedSnd.
(* 3: Inl *) rewrite <- lower_subst; rewrite subst_subst_0; apply RedInl.
(* 2: Inr *) rewrite <- lower_subst; rewrite subst_subst_0; apply RedInr.
(* 1: Inst *) rewrite <- lower_subst; apply RedInst.
Qed.

Lemma subst_lower : forall a b i k, subst (lower k b) i (lower k a) = subst b i (lower k a).
Proof.
induction a; intros b i k0; simpl; [|f_equal; auto..].
(* Var *)
  subst_lift_var.
  rewrite <- lower_lift.
  rewrite lower_lower.
  f_equal.
  rewrite min_r; auto.
  apply le_min_r.
Qed.

Lemma red_lower : forall a b k, red a b ->
  exists b', red (lower (1 + k) a) b' /\ le_term (lower k b) b'.
Proof.
intros a b k Hred; induction Hred; [destruct c; destruct IHHred as [? [? ?]]|..]; simpl lower.
(* 20: CtxLam *)
  exists (Lam (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxLam); auto.
(* 19: CtxApp1 *)
  exists (App (min k0 k) x (lower (S k) b)); simpl; repeat split; auto.
  apply RedCtx with (c := CtxApp1 (lower (S k) b)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 18: CtxApp2 *)
  exists (App (min k0 k) (lower (S k) a0) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxApp2 (lower (S k) a0)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 17: CtxPair1 *)
  exists (Pair (min k0 k) x (lower (S k) b)); simpl; repeat split; auto.
  apply RedCtx with (c := CtxPair1 (lower (S k) b)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 16: CtxPair2 *)
  exists (Pair (min k0 k) (lower (S k) a0) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxPair2 (lower (S k) a0)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 15: CtxFst *)
  exists (Fst (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxFst); auto.
(* 14: CtxSnd *)
  exists (Snd (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxSnd); auto.
(* 13: CtxAbsurd *)
  exists (Absurd (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxAbsurd); auto.
(* 12: CtxInl *)
  exists (Inl (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxInl); auto.
(* 11: CtxInr *)
  exists (Inr (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxInr); auto.
(* 10: CtxMatch1 *)
  exists (Match (min k0 k) x (lower (S k) bl) (lower (S k) br)); simpl; repeat split; auto.
  apply RedCtx with (c := CtxMatch1 (lower (S k) bl) (lower (S k) br)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 9: CtxMatch2 *)
  exists (Match (min k0 k) (lower (S k) a0) x (lower (S k) br)); simpl; repeat split; auto.
  apply RedCtx with (c := CtxMatch2 (lower (S k) a0) (lower (S k) br)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 8: CtxMatch3 *)
  exists (Match (min k0 k) (lower (S k) a0) (lower (S k) bl) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxMatch3 (lower (S k) a0) (lower (S k) bl)); auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
  apply le_term_lower; auto; apply binary_fuel_refl; auto.
(* 7: CtxInst *)
  exists (Inst (min k0 k) x); simpl; repeat split; auto.
  apply RedCtx with (c := CtxInst); auto.
(* 6: App *)
  eexists; split; [apply RedApp|].
  rewrite subst_lower; rewrite <- lower_subst.
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
(* 5: Fst *)
  eexists; split; [apply RedFst|].
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
(* 4: Snd *)
  eexists; split; [apply RedSnd|].
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
(* 3: Inl *)
  eexists; split; [apply RedInl|].
  rewrite subst_lower; rewrite <- lower_subst.
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
(* 2: Inr *)
  eexists; split; [apply RedInr|].
  rewrite subst_lower; rewrite <- lower_subst.
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
(* 1: Inst *)
  eexists; split; [apply RedInst|].
  rewrite 2 lower_lower; (apply le_term_lower; [|apply binary_fuel_refl; auto]); minmax.
Qed.

Lemma term_le_lower : forall a k, term_le a k -> a = lower k a.
Proof.
induction a; intros ? H; simpl in *;
repeat (match goal with
  | |- context [min _ _] => rewrite min_l
  | H1 : _ /\ _ |- _ => destruct H1
  | IHa : forall _,_ -> _ = _ |- _ => rewrite <- IHa; clear IHa
end; auto); auto.
Qed.

Lemma term_le_max : forall a k j, term_le a k -> term_le a (max j k).
Proof.
intros; eapply unary_fuel_1; [|apply H]; instantiate; simpl; intros.
eapply le_trans; [apply H0|]; minmax.
Qed.

Lemma term_le_exists : forall a, exists k, term_le a k.
Proof.
induction a; repeat (match goal with
  | IHa : exists _, term_le _ _ |- _ => destruct IHa; clear IHa end).
(* 13: Var *) exists k; simpl; auto.
(* 12: Lam *)
  exists (max k x); simpl; split; [minmax|].
  apply term_le_max; assumption.
(* 11: App *)
  exists (max k (max x x0)); simpl; split; [|split].
  minmax.
  repeat (apply term_le_max); assumption.
  apply term_le_max; rewrite max_comm.
  apply term_le_max; assumption.
(* 10: Unit *)
  exists k; simpl; omega.
(* 9: Pair *)
  exists (max k (max x x0)); simpl; split; [|split].
  apply le_max_l.
  repeat (apply term_le_max); assumption.
  apply term_le_max; rewrite max_comm.
  apply term_le_max; assumption.
(* 8: Fst *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 7: Snd *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 6: Absurd *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 5: Inl *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 4: Inr *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 3: Match *)
  exists (max k (max x (max x0 x1))); simpl; repeat split.
  apply le_max_l.
  repeat (apply term_le_max); assumption.
  apply term_le_max; apply term_le_max; rewrite max_comm.
  apply term_le_max; assumption.
  apply term_le_max; rewrite max_comm; apply term_le_max; assumption.
(* 2: Gen *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
(* 1: Inst *)
  exists (max k x); simpl; split.
  apply le_max_l.
  apply term_le_max; assumption.
Qed.

Lemma term_lt_exists : forall a, exists k, term_lt a k.
Proof.
intros a; destruct (term_le_exists a).
exists (1 + x).
eapply unary_fuel_1; [|apply H].
simpl; intros j ?; omega.
Qed.

Lemma term_le_min : forall a k j, term_le a j -> term_le a k -> term_le a (min j k).
Proof.
intros a k j aj ak; eapply unary_fuel_2; [|apply aj|apply ak]; instantiate; simpl; intros.
apply min_glb; assumption.
Qed.

Lemma term_lt_min : forall a k j, term_lt a j -> term_lt a k -> term_lt a (min j k).
Proof.
intros a k j aj ak; eapply unary_fuel_2; [|apply aj|apply ak]; instantiate; simpl; intros.
apply min_glb; assumption.
Qed.

Lemma binary_fuel_unary : forall (op : nat -> nat -> Prop) (f : nat -> Prop),
  (forall j k, op j k -> f k -> f j) ->
  forall a b, binary_fuel op a b -> unary_fuel f b -> unary_fuel f a.
Proof.
intros op f opf; induction a; intros b ab fb; destruct_binary b ab; subst; simpl in *;
repeat (match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  | Hop : op ?j ?k, Hf : f ?k |- f ?j => apply (opf _ _ Hop Hf)
  | IHa : forall _, _ -> _ -> _ _ ?a
    , Hop : binary_fuel op ?a ?b
    , Hf : unary_fuel f ?b
    |- unary_fuel f ?a => apply (IHa b Hop Hf)
end; auto); auto.
Qed.

Lemma le_term_le : forall a b k, le_term a b -> term_le b k -> term_le a k.
Proof.
intros a b k ab bk; eapply binary_fuel_unary; [|apply ab|apply bk].
intros; omega.
Qed.

Lemma le_term_lt : forall a b k, le_term a b -> term_lt b k -> term_lt a k.
Proof.
intros a b k ab bk; eapply binary_fuel_unary; [|apply ab|apply bk].
intros; omega.
Qed.

Lemma lt_term_le : forall a j k, term_lt a j -> j <= k -> term_lt a k.
Proof.
intros a j k aj jk; eapply unary_fuel_1; [|apply aj].
simpl; intros; omega.
Qed.

Lemma term_lt_0 : forall a, term_lt a 0 -> False.
Proof.
destruct a; simpl; intros; repeat
match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : ?k < 0 |- _ => inversion H
end.
Qed.

