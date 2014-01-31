Require Import Omega.
Require Import List.
Require Import Equality.

Require Import mxx.
Require Import ext.
Require Import list.

(** * System Fcc (common part)

This file formalizes all definitions and typing rules of System Fcc
that are not related terms. The only term related part of the system
is the term judgment, which is described in [Ltypesystem_v] for its
lambda version and [Ltypesystem_v] for its indexed (or fuel) version.
*)

(** ** Syntax

The formalization of the type system syntax differs from its
definition in the manuscript in the sense that the formalization
defines the syntax in two steps. We first define a unique inductive
for all syntactical objects, and then define a judgment to classify
these objects in there syntactical class of the manuscript.
*)

(** *** Objects

We define objects, written [o], in the inductive [obj]. They contain
all syntactical objects of the manuscript: kinds [k], types [t] or
[s], propositions [p], type environments [H], proposition environments
[Y], and term environments [G].
*)
Inductive obj : Set :=
(* kinds *)
| KStar
| KOne
| KProd (k1 : obj) (k2 : obj)
| KRes (k : obj) (p : obj)
(* types *)
| TVar (x : nat)
| TArr (t : obj) (s : obj)
| TOne
| TProd (t : obj) (s : obj)
| TVoid
| TSum (t : obj) (s : obj)
| TFor (k : obj) (t : obj)
| TPi (k : obj) (t : obj)
| TMu (t : obj)
| TBot
| TTop
| TUnit
| TPair (t1 : obj) (t2 : obj)
| TFst (t : obj)
| TSnd (t : obj)
(* props *)
| PTrue
| PAnd (p1 : obj) (p2 : obj)
| PCoer (H : obj) (t : obj) (s : obj)
| PExi (k : obj)
| PFor (k : obj) (p : obj)
(* tenvs *)
| HNil
| HCons (H : obj) (k : obj)
(* penvs *)
| YNil
| YCons (Y : obj) (p : obj)
(* aenvs *)
| GNil
| GCons (G : obj) (t : obj)
.
Notation kind := obj.
Notation type := obj.
Notation prop := obj.
Notation tenv := obj.
Notation penv := obj.
Notation aenv := obj.

(** *** Syntactical classes *)

(** We define in [class] the syntactical classes of the manuscript.
*)
Inductive class :=
| CKind (* kinds *)
| CType (* types *)
| CProp (* propositions *)
| CTEnv (* type environments *)
| CPEnv (* proof environments *)
| CAEnv (* term environments *)
.

(** We write [cobj o c] when the object [o] is in the syntactical
class [c].
*)
Inductive cobj : obj -> class -> Prop :=
(* kinds *)
| CKStar : cobj KStar CKind
| CKOne : cobj KOne CKind
| CKProd : forall k1 k2, cobj k1 CKind -> cobj k2 CKind -> cobj (KProd k1 k2) CKind
| CKRes : forall k p, cobj k CKind -> cobj p CProp -> cobj (KRes k p) CKind
(* types *)
| CTVar : forall x, cobj (TVar x) CType
| CTArr : forall t s, cobj t CType -> cobj s CType -> cobj (TArr t s) CType
| CTOne : cobj TOne CType
| CTProd : forall t s, cobj t CType -> cobj s CType -> cobj (TProd t s) CType
| CTVoid : cobj TVoid CType
| CTSum : forall t s, cobj t CType -> cobj s CType -> cobj (TSum t s) CType
| CTFor : forall k t, cobj k CKind -> cobj t CType -> cobj (TFor k t) CType
| CTPi : forall k t, cobj k CKind -> cobj t CType -> cobj (TPi k t) CType
| CTMu : forall t, cobj t CType -> cobj (TMu t) CType
| CTBot : cobj TBot CType
| CTTop : cobj TTop CType
| CTUnit : cobj TUnit CType
| CTPair : forall t1 t2, cobj t1 CType -> cobj t2 CType -> cobj (TPair t1 t2) CType
| CTFst : forall t, cobj t CType -> cobj (TFst t) CType
| CTSnd : forall t, cobj t CType -> cobj (TSnd t) CType
(* props *)
| CPTrue : cobj PTrue CProp
| CPAnd : forall p1 p2, cobj p1 CProp -> cobj p2 CProp -> cobj (PAnd p1 p2) CProp
| CPCoer : forall H t s, cobj H CTEnv -> cobj t CType -> cobj s CType -> cobj (PCoer H t s) CProp
| CPExi : forall k, cobj k CKind -> cobj (PExi k) CProp
| CPFor : forall k p, cobj k CKind -> cobj p CProp -> cobj (PFor k p) CProp
(* tenvs *)
| CHNil : cobj HNil CTEnv
| CHCons : forall H k, cobj H CTEnv -> cobj k CKind -> cobj (HCons H k) CTEnv
(* penvs *)
| CYNil : cobj YNil CPEnv
| CYCons : forall Y p, cobj Y CPEnv -> cobj p CProp -> cobj (YCons Y p) CPEnv
(* aenvs *)
| CGNil : cobj GNil CAEnv
| CGCons : forall G t, cobj G CAEnv -> cobj t CType -> cobj (GCons G t) CAEnv
.

(** *** Functions

We define a few functions for environments. Due to the fact that the
syntax is unified, pattern matching on a single syntactical class is
not simple: it either needs dependent types or partial functions. As a
consequence, we define most functions as relations instead of Coq
functions.
*)

(** The length of the type environment [H] is written [Hlength H] and
is defined as a Coq function. When the argument is not a type
environment, the return value is undefined (some natural number). The
definition of this function is _partial_ on objects, but total on type
environments.
*)
Fixpoint Hlength H :=
  match H with
    | HNil => 0
    | HCons H k => 1 + Hlength H
    | _ => 0 (* fake value *)
  end.

(** We look up the kind [k] of the [n]th type variable of the type
environment [H] with [Hnth H n k]. This function is defined as a
relation.
*)
Inductive Hnth : tenv -> nat -> kind -> Prop :=
| Hnth0 : forall n, Hnth HNil n KOne
| Hnth1 : forall H k, Hnth (HCons H k) 0 k
| Hnth2 : forall n H k k', Hnth H n k -> Hnth (HCons H k') (1 + n) k
.

Lemma Hnth_eq : forall {a b c}, Hnth a b c -> forall {d}, Hnth a b d -> c = d.
Proof.
induction 1; simpl; intros d Hx; inversion Hx; clear Hx; subst; auto.
Qed.

(** The concatenation [H1H2] of two type environments [H1] and [H2] is
written [Happ H1 H2 H1H2].
*)
Inductive Happ : tenv -> tenv -> tenv -> Prop :=
| Happ0 : forall H, Happ H HNil H
| Happ1 : forall k1 H1 H2 H2H1,
  Happ H2 H1 H2H1 -> Happ H2 (HCons H1 k1) (HCons H2H1 k1)
.

Lemma Happ_eq : forall {a b c}, Happ a b c -> forall {d}, Happ a b d -> c = d.
Proof.
induction 1; simpl; intros d Hx; inversion Hx; clear Hx; subst; auto.
rewrite (IHHapp H2H0); auto.
Qed.

(** We look up the [n]th proposition [p] of the proof environment [Y]
with [Ynth Y n p].
*)
Inductive Ynth : penv -> nat -> prop -> Prop :=
| Ynth0 : forall n, Ynth YNil n PTrue
| Ynth1 : forall Y p, Ynth (YCons Y p) 0 p
| Ynth2 : forall n Y p p', Ynth Y n p -> Ynth (YCons Y p') (1 + n) p
.

(** The concatenation [Y1Y2] of two proof environments [Y1] and [Y2]
is written [Yapp Y1 Y2 Y1Y2].
*)
Inductive Yapp : penv -> penv -> penv -> Prop :=
| Yapp0 : forall Y, Yapp Y YNil Y
| Yapp1 : forall p1 Y1 Y2 Y2Y1,
  Yapp Y2 Y1 Y2Y1 -> Yapp Y2 (YCons Y1 p1) (YCons Y2Y1 p1)
.

(** We look up the type [t] of the [n]th term variable of the term
environment [G] with [Gnth G n t].
*)
Inductive Gnth : aenv -> nat -> type -> Prop :=
| Gnth0 : forall n, Gnth GNil n TTop
| Gnth1 : forall G t, Gnth (GCons G t) 0 t
| Gnth2 : forall n G t t', Gnth G n t -> Gnth (GCons G t') (1 + n) t
.

(** We define a function to traverse objects and operating on their
variables. The object [traverse f i o] has the same structure as [o] but
for its variables [TVar a] that become [f a i]. The level [i] indicates
how deep we are in the object: it is incremented each time we cross a
binder. Objects have several binder constructs:
- [Kres k p] binds a type variable of kind [k] in the proposition [p]
- [TFor k t] binds a type variable of kind [k] in the type [t]
- [TPi k t] binds a type variable of kind [k] in the type [t]
- [TMu t] binds a type variable of kind [KStar] in the type [t]
- [PCoer H t s] extends the environment of the type [t] with the type
  environment [H]
- [PFor k p] binds a type variable of kind [k] in the proposition [p]
- [HCons H k] extends the environment of the kind [k] with the type
  environment [H]
*)
Definition traverse f := fix g i o :=
  match o with
  | KStar => KStar
  | KOne => KOne
  | KProd k1 k2 => KProd (g i k1) (g i k2)
  | KRes k p => KRes (g i k) (g (1 + i) p)
  | TVar a => f a i
  | TArr t s => TArr (g i t) (g i s)
  | TOne => TOne
  | TProd t s => TProd (g i t) (g i s)
  | TVoid => TVoid
  | TSum t s => TSum (g i t) (g i s)
  | TFor k t => TFor (g i k) (g (1 + i) t)
  | TPi k t => TPi (g i k) (g (1 + i) t)
  | TMu t => TMu (g (1 + i) t)
  | TBot => TBot
  | TTop => TTop
  | TUnit => TUnit
  | TPair t s => TPair (g i t) (g i s)
  | TFst t => TFst (g i t)
  | TSnd t => TSnd (g i t)
  | PTrue => PTrue
  | PAnd p1 p2 => PAnd (g i p1) (g i p2)
  | PCoer H t s => PCoer (g i H) (g (Hlength H + i) t) (g i s)
  | PExi k => PExi (g i k)
  | PFor k p => PFor (g i k) (g (1 + i) p)
  | HNil => HNil
  | HCons H k => HCons (g i H) (g (Hlength H + i) k)
  | YNil => YNil
  | YCons Y p => YCons (g i Y) (g i p)
  | GNil => GNil
  | GCons G t => GCons (g i G) (g i t)
  end.

(** We define the lifting function [lift] and substitution function
[subst] using the [traverse] function with the [lift_idx] and
[subst_idx] functions, respectively. The object [lift d i o] has the
same structure as [o] but the variables greater or equal than [i] are
incremented by [d]. The object [subst t i o] has the same structure as
[o] but the variables greater than [i] are decremented by one and the
variables equal to [i] are replaced with the type [t] lifted by [i]
from level [0]. This function permits to substitute objects, but only
type substitution preserves the syntactical class.
*)
Definition lift_idx d x i := TVar (if le_gt_dec i x then d + x else x).
Definition lift d := traverse (lift_idx d).
Definition shift := lift 1.
Hint Unfold lift_idx lift shift.

Definition subst_idx t x i :=
  match lt_eq_lt_dec x i with
    | inleft (left _)  => TVar x
    | inleft (right _) => lift x 0 t
    | inright _        => TVar (x - 1)
  end.
Definition subst t := traverse (subst_idx t).
Hint Unfold subst_idx subst.

Ltac subst_lift_var := repeat (match goal with
    | |- context[subst_idx] => unfold subst_idx
    | |- context[lift_idx] => unfold lift_idx
    | |- context[lt_eq_lt_dec ?x ?y] =>
      destruct (lt_eq_lt_dec x y) as [[?|?]|?]; try (exfalso; omega); simpl; auto
    | |- context[le_gt_dec ?x ?y] =>
      destruct (le_gt_dec x y); try (exfalso; omega); simpl; auto
  end).

Lemma lift_0 : forall t i, lift 0 i t = t.
Proof.
induction t; intros i; simpl; f_equal; auto.
subst_lift_var.
Qed.

Lemma Hlength_lift : forall d H i, Hlength (lift d i H) = Hlength H.
Proof. induction H; simpl; intros; auto. Qed.

Lemma Hlength_subst : forall b, cobj b CType ->
  forall H i, Hlength (subst b i H) = Hlength H.
Proof.
intros b cb H.
induction H; simpl; intros; auto.
subst_lift_var.
rewrite Hlength_lift.
clear x i e.
remember CType as c.
destruct cb; inversion Heqc; reflexivity.
Qed.

Lemma lift_fusion : forall d1 d2 a i j, j >= i -> j <= d2 + i ->
  lift d1 j (lift d2 i a) = lift (d1 + d2) i a.
Proof.
induction a; intros; simpl;
repeat match goal with
  | |- ?x = ?x => reflexivity
  | |- context[Hlength (lift ?d ?i ?H)] => rewrite (Hlength_lift d H i)
  | IH : forall i j, _ -> _ -> lift ?d1 j (lift ?d2 i ?a) = _
    |- context[lift ?d1 ?j (lift ?d2 ?i ?a)] =>
    rewrite (IH i j); [clear IH|omega|omega]
end.
subst_lift_var; f_equal; omega.
Qed.

Lemma lift_lift : forall d1 d2 a i j, j >= i ->
  lift d1 i (lift d2 j a) = lift d2 (j + d1) (lift d1 i a).
Proof.
induction a; intros; simpl;
repeat match goal with
  | |- ?x = ?x => reflexivity
  | |- context[Hlength (lift ?d ?i ?H)] => rewrite (Hlength_lift d H i)
  | IH : forall i j, _ -> lift ?d1 i (lift ?d2 j ?a) = _
    |- context[lift ?d1 ?i (lift ?d2 ?j ?a)] =>
    rewrite (IH i j); [clear IH; simpl|omega]
end.
subst_lift_var; f_equal; omega.
rewrite plus_assoc; reflexivity.
rewrite plus_assoc; reflexivity.
Qed.

Lemma lift_lift_0 : forall d2 d1 j a,
  lift d1 0 (lift d2 j a) = lift d2 (d1 + j) (lift d1 0 a).
Proof.
intros.
pose proof (lift_lift d1 d2 a 0 j).
rewrite H; [|omega].
f_equal; omega.
Qed.

Lemma lift_shift_0 : forall d i a,
  lift 1 0 (lift d i a) = lift d (1 + i) (lift 1 0 a).
Proof. intros; pose proof (lift_lift_0 d 1 i a); auto. Qed.

Lemma lift_subst1 : forall b, cobj b CType ->
  forall d j a i,
  lift d (j + i) (subst b i a) = subst (lift d j b) i (lift d (j + 1 + i) a).
Proof.
intros b cb.
induction a; intros i; simpl;
repeat match goal with
  | |- ?x = ?x => reflexivity
  | IH : forall i, lift ?d (?j + i) (subst ?b i ?a) = _
    |- context[ lift ?d (?j + ?i) (subst ?b ?i ?a) ] =>
    rewrite (IH i); clear IH
  | IH : forall i, lift ?d (?j + i) (subst ?b i ?a) = _
    |- context[ lift ?d (?f (?j + ?i)) (subst ?b (?f ?i) ?a) ] =>
    repeat rewrite plus_n_Sm; rewrite (IH (f i)); clear IH
end.
subst_lift_var; subst; [rewrite lift_lift_0|]; f_equal; omega.
(* *)
  rewrite (Hlength_subst b cb).
  rewrite Hlength_lift.
  pose proof (IHa2 (Hlength a1 + i)).
  replace (Hlength a1 + (j + i)) with (j + (Hlength a1 + i)) by omega.
  rewrite H.
  f_equal.
  replace (j + 1 + (Hlength a1 + i)) with (Hlength a1 + (j + 1 + i)) by omega.
  reflexivity.
(* *)
  rewrite (Hlength_subst b cb).
  rewrite Hlength_lift.
  pose proof (IHa2 (Hlength a1 + i)).
  replace (Hlength a1 + (j + i)) with (j + (Hlength a1 + i)) by omega.
  rewrite H.
  f_equal.
  replace (j + 1 + (Hlength a1 + i)) with (Hlength a1 + (j + 1 + i)) by omega.
  reflexivity.
Qed.

Lemma lift_subst1_0 : forall d i b a, cobj b CType ->
  lift d i (subst b 0 a) = subst (lift d i b) 0 (lift d (1 + i) a).
Proof.
intros d i b a cb.
pose proof (lift_subst1 b cb d i a 0).
repeat rewrite plus_0_r in H.
replace (i + 1) with (1 + i) in H by omega.
assumption.
Qed.

Lemma lift_subst2 : forall b, cobj b CType ->
  forall d a i j, i >= j ->
  lift d j (subst b i a) = subst b (d + i) (lift d j a).
Proof.
intros b cb.
induction a; intros i j Hij; simpl; auto;
repeat match goal with
  | H : ?x |- ?x => exact H
  | H : ?i >= ?j |- ?f ?i >= ?f ?j => omega
  | |- ?x = ?x => reflexivity
  | IH : forall i j, i >= j -> lift ?d j (subst ?b i ?a) = _
    |- context[ lift ?d ?j (subst ?b ?i ?a) ] =>
    rewrite (IH i); clear IH
  | IH : forall i, i >= ?j -> lift ?d ?j (subst ?b i ?a) = _
    |- context[ lift ?d (?f ?j) (subst ?b (?f ?i) ?a) ] =>
    rewrite (IH (f i)); clear IH
  | |- context[ S (?a + ?b) ] => rewrite (plus_n_Sm a b)
  | cb : cobj ?b CType |- context[ Hlength (subst ?b _ _) ] => rewrite (Hlength_subst b cb)
  | |- context[ Hlength (lift _ _ _) ] => rewrite Hlength_lift
end.
subst_lift_var; subst; [rewrite lift_fusion; auto|]; f_equal; omega.
(* *)
  f_equal.
  f_equal.
  omega.
(* *)
  f_equal.
  f_equal.
  omega.
Qed.

Lemma lift_subst2_0 : forall a b i, cobj b CType ->
  lift 1 0 (subst b i a) = subst b (1 + i) (lift 1 0 a).
Proof.
intros.
pose proof (lift_subst2 b H 1 a i 0) as Hx.
apply Hx; omega.
Qed.

Lemma subst_lift : forall b d a i l, i >= l -> i <= d + l ->
  subst b i (lift (S d) l a) = lift d l a.
Proof.
induction a; intros i l H1 H2; simpl; auto;
repeat match goal with
  | H : ?x |- ?x => exact H
  | H : ?i >= ?j |- ?f ?i >= ?f ?j => omega
  | H : ?i <= ?d + ?l |- ?f ?i <= ?d + ?f ?l => omega
  | |- ?x = ?x => reflexivity
  | IH : forall i l, _ -> _ -> subst ?b i (lift (S ?d) l ?a) = _
    |- context[ subst ?b ?i (lift (S ?d) ?l ?a) ] =>
    rewrite (IH i l); clear IH
  | |- context[ Hlength (lift _ _ _) ] => rewrite Hlength_lift
end.
subst_lift_var.
f_equal; omega.
Qed.

Lemma subst_lift_0 : forall a b, subst b 0 (lift 1 0 a) = a.
Proof. intros a b; pose proof (subst_lift b 0 a 0 0); simpl in *; rewrite H; auto; apply lift_0. Qed.

Lemma subst_subst : forall bd b d, cobj bd CType -> cobj b CType -> forall a i,
  subst bd (d + i) (subst b i a) = subst (subst bd d b) i (subst bd (1 + d + i) a).
Proof.
induction a; intros i; simpl; auto;
repeat match goal with
  | H : ?x |- ?x => exact H
  | |- ?x = ?x => reflexivity
  | |- context[ S (?n + ?m) ] => rewrite (plus_n_Sm n m)
  | |- context[ Hlength ?a + (?d + ?i) ] =>
    replace (Hlength a + (d + i)) with (d + (Hlength a + i)) by omega
  | IH : forall i, subst ?bd (?d + i) (subst ?b i ?a) = _
    |- context[ subst ?bd (?d + ?i) (subst ?b ?i ?a) ] =>
    rewrite (IH i); clear IH; simpl
  | IH : forall i, subst ?bd (?d + i) (subst ?b i ?a) = _
    |- context[ subst ?bd (?d + (?f ?i)) (subst ?b (?f ?i) ?a) ] =>
    rewrite (IH (f i)); clear IH; simpl
  | cb : cobj ?b CType |- context[ Hlength (subst ?b _ _) ] => rewrite (Hlength_subst b cb)
end.
subst_lift_var.
(* *)
  subst.
  replace (subst bd d) with (subst bd (d + 0)) by (f_equal; omega).
  rewrite lift_subst2; [|auto|omega].
  f_equal; omega.
(* *)
  subst.
  replace (d + S i) with (S (d + i)) by omega.
  rewrite subst_lift; [|omega..].
  f_equal; omega.
Qed.

Lemma subst_subst_0 : forall a b bd d, cobj bd CType -> cobj b CType ->
  subst bd d (subst b 0 a) = subst (subst bd d b) 0 (subst bd (1 + d) a).
Proof.
intros.
replace d with (d + 0) by omega.
rewrite subst_subst; auto; repeat f_equal; omega.
Qed.

Lemma subst_subst_0_0 : forall a b bd, cobj bd CType -> cobj b CType ->
  subst bd 0 (subst b 0 a) = subst (subst bd 0 b) 0 (subst bd 1 a).
Proof. intros; rewrite subst_subst_0; auto; repeat f_equal; omega. Qed.

(** ** Judgments *)

(** *** Well-foundness *)

(** We define the well-foundness tokens [WF] and [NE] for well-founded
functors and non-expansive ones, respectively.
*)
Inductive recsort := WF | NE.

(** We write [jrec a t rec] when the type [t] has the well-foundness
[rec] with respect to the type variable [a].
*)
Inductive jrec : nat -> type -> recsort -> Prop :=
| RECVar : forall a, jrec a (TVar a) NE
| RECArr : forall a t s, jrec a t NE -> jrec a s NE -> jrec a (TArr t s) WF
| RECProd : forall a t s, jrec a t NE -> jrec a s NE -> jrec a (TProd t s) WF
| RECSum : forall a t s, jrec a t NE -> jrec a s NE -> jrec a (TSum t s) WF
| RECFor : forall rec a k k' t, k = shift a k' -> jrec (1 + a) t rec -> jrec a (TFor k t) rec
| RECPi : forall a k k' t, k = shift a k' -> jrec (1 + a) t NE -> jrec a (TPi k t) WF
| RECMu : forall rec a t, jrec 0 t WF -> jrec (1 + a) t rec -> jrec a (TMu t) rec
| RECwf : forall a t t', t = shift a t' -> jrec a t WF
| RECne : forall a t, jrec a t WF -> jrec a t NE
.

(** *** Equality *)

(** We write [jeq o1 o2] when objects [o1] and [o2] are equal. The
soundness of the transitivity rule needs the intermediate object [o2]
to be syntactically well-formed. See the discussion for the definition
of the inductive [jobj] later in this file.
*)
Inductive jeq : type -> type -> class -> Prop :=
| EQrefl : forall o c, cobj o c -> jeq o o c
| EQsym : forall o1 o2 c, jeq o1 o2 c -> jeq o2 o1 c
| EQtrans : forall o1 o2 o3 c, jeq o1 o2 c -> jeq o2 o3 c -> jeq o1 o3 c
| EQcongrKProd :  forall k11 k12 k21 k22,
  jeq k11 k12 CKind -> jeq k21 k22 CKind -> jeq (KProd k11 k21) (KProd k12 k22) CKind
| EQcongrKRes : forall k1 k2 p1 p2,
  jeq k1 k2 CKind -> jeq p1 p2 CProp -> jeq (KRes k1 p1) (KRes k2 p2) CKind
| EQcongrTArr : forall t1 t2 s1 s2,
  jeq t1 t2 CType -> jeq s1 s2 CType -> jeq (TArr t1 s1) (TArr t2 s2) CType
| EQcongrTProd : forall t1 t2 s1 s2,
  jeq t1 t2 CType -> jeq s1 s2 CType -> jeq (TProd t1 s1) (TProd t2 s2) CType
| EQcongrTSum : forall t1 t2 s1 s2,
  jeq t1 t2 CType -> jeq s1 s2 CType -> jeq (TSum t1 s1) (TSum t2 s2) CType
| EQcongrTFor : forall k1 k2 t1 t2,
  jeq k1 k2 CKind -> jeq t1 t2 CType -> jeq (TFor k1 t1) (TFor k2 t2) CType
| EQcongrTPi : forall k1 k2 t1 t2,
  jeq k1 k2 CKind -> jeq t1 t2 CType -> jeq (TPi k1 t1) (TPi k2 t2) CType
| EQcongrTMu : forall t1 t2, jeq t1 t2 CType -> jeq (TMu t1) (TMu t2) CType
| EQcongrTPair : forall t1 t2 s1 s2,
  jeq t1 t2 CType -> jeq s1 s2 CType -> jeq (TPair t1 s1) (TPair t2 s2) CType
| EQcongrTFst : forall t1 t2, jeq t1 t2 CType -> jeq (TFst t1) (TFst t2) CType
| EQcongrTSnd : forall t1 t2, jeq t1 t2 CType -> jeq (TSnd t1) (TSnd t2) CType
| EQcongrPAnd : forall p11 p12 p21 p22,
  jeq p11 p12 CProp -> jeq p21 p22 CProp -> jeq (PAnd p11 p21) (PAnd p12 p22) CProp
| EQcongrPCoer : forall H1 H2 t1 t2 s1 s2,
  jeq H1 H2 CTEnv -> jeq t1 t2 CType -> jeq s1 s2 CType -> jeq (PCoer H1 t1 s1) (PCoer H2 t2 s2) CProp
| EQcongrPExi : forall k1 k2, jeq k1 k2 CKind -> jeq (PExi k1) (PExi k2) CProp
| EQcongrPFor : forall k1 k2 p1 p2,
  jeq k1 k2 CKind -> jeq p1 p2 CProp -> jeq (PFor k1 p1) (PFor k2 p2) CProp
| EQcongrHCons : forall H1 H2 k1 k2,
  jeq H1 H2 CTEnv -> jeq k1 k2 CKind -> jeq (HCons H1 k1) (HCons H2 k2) CTEnv
| EQcongrYCons : forall Y1 Y2 p1 p2,
  jeq Y1 Y2 CPEnv -> jeq p1 p2 CProp -> jeq (YCons Y1 p1) (YCons Y2 p2) CPEnv
| EQcongrGCons : forall G1 G2 t1 t2,
  jeq G1 G2 CAEnv -> jeq t1 t2 CType -> jeq (GCons G1 t1) (GCons G2 t2) CAEnv
| EQTFstPair : forall t s, cobj t CType -> cobj s CType -> jeq (TFst (TPair t s)) t CType
| EQTSndPair : forall t s, cobj t CType -> cobj s CType -> jeq (TSnd (TPair t s)) s CType
.

(** *** Objects

We can finally define the main judgment, which is the judgment for
objects.
*)

(** We first define the judgments of the manuscript:
- [JK k] for the kind coherence judgment
- [JT t k] for the type judgment
- [JP Y0 Y1 p] for the proposition judgment
- [JH H'] for the type environment coherence judgment
- [JG G] for the term environment judgment
- [Jwf c o] for the well-formedness judgment

This last judgment is only necessary in the manuscript version. We
discuss this notion in the next paragraph (inductive [jobj]).
*)
Inductive judg : Set :=
| JK (k : kind)
| JT (t : type) (k : kind)
| JP (Y0 : penv) (Y1 : penv) (p : prop)
| JC (Y0 : penv) (Y1 : penv) (H' : tenv) (t' : type) (t : type)
| JH (H' : tenv)
| JG (G : aenv)
| Jwf (o : obj) (c : class)
.

Definition jlift d i j :=
  match j with
    | JK k => JK (lift d i k)
    | JT t k => JT (lift d i t) (lift d i k)
    | JP Y0 Y1 p => JP (lift d i Y0) (lift d i Y1) (lift d i p)
    | JC Y0 Y1 H' t' t => JC (lift d i Y0) (lift d i Y1)
                             (lift d i H') (lift d (Hlength H' + i) t') (lift d i t)
    | JH H' => JH (lift d i H')
    | JG G => JG (lift d i G)
    | Jwf o c => Jwf (lift d i o) c
  end.

Lemma jlift_0 : forall j, jlift 0 0 j = j.
Proof. destruct j; simpl; repeat rewrite lift_0; reflexivity. Qed.

Lemma jlift_lift : forall d1 d2 a i j, j >= i ->
  jlift d1 i (jlift d2 j a) = jlift d2 (j + d1) (jlift d1 i a).
Proof.
destruct a; simpl; intros;
repeat (rewrite (lift_lift d1 d2); [|omega]); try reflexivity.
repeat rewrite Hlength_lift.
repeat (rewrite (lift_lift d1 d2); [|omega]).
f_equal; f_equal; omega.
Qed.

Lemma jlift_lift_0 : forall d1 d2 i j,
  jlift d1 0 (jlift d2 i j) = jlift d2 (d1 + i) (jlift d1 0 j).
Proof.
intros.
pose proof (jlift_lift d1 d2 j 0 i).
rewrite H; [|omega].
f_equal; omega.
Qed.

Lemma jlift_fusion : forall d1 d2 i j a,
  j >= i -> j <= d2 + i -> jlift d1 j (jlift d2 i a) = jlift (d1 + d2) i a.
Proof.
destruct a; simpl; intros; repeat (rewrite lift_fusion; [|omega..]); try reflexivity.
rewrite Hlength_lift.
repeat (rewrite lift_fusion; [|omega..]).
reflexivity.
Qed.

Definition jsubst s i j :=
  match j with
    | JK k => JK (subst s i k)
    | JT t k => JT (subst s i t) (subst s i k)
    | JP Y0 Y1 p => JP (subst s i Y0) (subst s i Y1) (subst s i p)
    | JC Y0 Y1 H' t' t => JC (subst s i Y0) (subst s i Y1)
                             (subst s i H') (subst s (Hlength H' + i) t') (subst s i t)
    | JH H' => JH (subst s i H')
    | JG G => JG (subst s i G)
    | Jwf o c => Jwf (subst s i o) c
  end.

Lemma jlift_subst2 : forall b, cobj b CType ->
  forall d a i j, i >= j ->
  jlift d j (jsubst b i a) = jsubst b (d + i) (jlift d j a).
Proof.
destruct a; simpl; intros; repeat (rewrite lift_subst2; [|auto|omega]); try reflexivity.
rewrite Hlength_lift.
rewrite Hlength_subst; auto.
repeat (rewrite lift_subst2; [|auto|omega]).
f_equal.
f_equal.
omega.
Qed.

Lemma jlift_subst2_0 : forall a b i, cobj b CType ->
  jlift 1 0 (jsubst b i a) = jsubst b (1 + i) (jlift 1 0 a).
Proof.
intros.
pose proof (jlift_subst2 b H 1 a i 0) as Hx.
apply Hx; omega.
Qed.

(** We write [jobj j] when the judgment [j] holds. The formalization
differs from the manuscript in the sense that it requires additional
but redundant premises. This redundancy comes from the extraction
lemma and is needed for inductions, because the proof of soundness
needs sometimes more than the soundness of the premises of the
manuscript, it also needs the soundness of some judgments extracted
from the premises. In the definition of [jobj] we will explicitly
state when a premise is required for soundness (and thus redundant)
with the letter [S], and we will also state when a premise is not
needed for soundness but present in the manuscript with the letter [E]
(like extraction). Ideally, we would parametrize the formalization
whether we are in the [E] or [S] version of the type system, and show
that the [E] version implies the [S] version.

Soundness alse needs some objects to be in the correct syntactical
class. In the manuscript, this holds by syntactical well-formedness,
but in the formalization, since objects are unified, we need to state
it explicitly. We write such premises with the letter [C] (like
syntactical class).

The premises marked with [E] are commented, since they are not
necessary for soundness. And premises marked with [C] are [cobj]
judgments, since they are about syntactical well-formedness.
*)
Inductive jobj v : tenv -> judg -> Prop :=
(* kinds *)
| JKexi : forall H k,
  jobj v H (JP YNil YNil (PExi k)) ->
  (mE v -> jobj v H (Jwf k CKind)) ->
  jobj v H (JK k)
(* types *)
| JTeq : forall H t k k',
  jobj v H (JT t k) ->
  jeq k k' CKind ->
  (mE v -> jobj v H (Jwf k' CKind)) ->
  jobj v H (JT t k')
| JTVar : forall H a k,
  cobj H CTEnv ->
  Hnth H a k ->
  jobj v H (JT (TVar a) (lift (1 + a) 0 k))
| JTArr : forall H t s,
  jobj v H (JT t KStar) ->
  jobj v H (JT s KStar) ->
  jobj v H (JT (TArr t s) KStar)
| JTOne : forall H,
  cobj H CTEnv ->
  jobj v H (JT TOne KStar)
| JTProd : forall H t s,
  jobj v H (JT t KStar) ->
  jobj v H (JT s KStar) ->
  jobj v H (JT (TProd t s) KStar)
| JTVoid : forall H,
  cobj H CTEnv ->
  jobj v H (JT TVoid KStar)
| JTSum : forall H t s,
  jobj v H (JT t KStar) ->
  jobj v H (JT s KStar) ->
  jobj v H (JT (TSum t s) KStar)
| JTFor : forall H k t,
  (mE v -> jobj v H (Jwf k CKind)) ->
  jobj v (HCons H k) (JT t KStar) ->
  jobj v H (JT (TFor k t) KStar)
| JTPi : forall H k t,
  (mE v -> jobj v H (Jwf k CKind)) ->
  jobj v (HCons H k) (JT t KStar) ->
  jobj v H (JT (TPi k t) KStar)
| JTMu : forall H t,
  jrec 0 t WF ->
  jobj v (HCons H KStar) (JT t KStar) ->
  mR v -> jobj v H (JT (TMu t) KStar)
| JTBot : forall H,
  cobj H CTEnv ->
  jobj v H (JT TBot KStar)
| JTTop : forall H,
  cobj H CTEnv ->
  jobj v H (JT TTop KStar)
| JTUnit : forall H,
  cobj H CTEnv ->
  jobj v H (JT TUnit KOne)
| JTPair : forall H t1 t2 k1 k2,
  jobj v H (JT t1 k1) ->
  jobj v H (JT t2 k2) ->
  jobj v H (JT (TPair t1 t2) (KProd k1 k2))
| JTFst : forall H t k1 k2,
  jobj v H (JT t (KProd k1 k2)) ->
  jobj v H (JT (TFst t) k1)
| JTSnd : forall H t k1 k2,
  jobj v H (JT t (KProd k1 k2)) ->
  jobj v H (JT (TSnd t) k2)
| JTPack : forall H t k p,
  (mE v -> jobj v (HCons H k) (Jwf p CProp)) ->
  jobj v H (JT t k) ->
  jobj v H (JP YNil YNil (subst t 0 p)) ->
  jobj v H (JT t (KRes k p))
| JTUnpack : forall H t k p,
  jobj v H (JT t (KRes k p)) ->
  jobj v H (JT t k)
(* props (logic) *)
| JPeq : forall H Y0 Y1 p p',
  jobj v H (JP Y0 Y1 p) ->
  jeq p p' CProp ->
  (mE v -> jobj v H (Jwf p' CProp)) ->
  jobj v H (JP Y0 Y1 p')
| JPVar : forall H Y0 Y1 n p,
  cobj H CTEnv ->
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  Ynth Y0 n p ->
  mR v -> jobj v H (JP Y0 Y1 p)
| JPTrue : forall H Y0 Y1,
  cobj H CTEnv ->
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  jobj v H (JP Y0 Y1 PTrue)
| JPAndPair : forall H Y0 Y1 p1 p2,
  jobj v H (JP Y0 Y1 p1) ->
  jobj v H (JP Y0 Y1 p2) ->
  jobj v H (JP Y0 Y1 (PAnd p1 p2))
| JPAndFst : forall H Y0 Y1 p1 p2,
  jobj v H (JP Y0 Y1 (PAnd p1 p2)) ->
  jobj v H (JP Y0 Y1 p1)
| JPAndSnd : forall H Y0 Y1 p1 p2,
  jobj v H (JP Y0 Y1 (PAnd p1 p2)) ->
  jobj v H (JP Y0 Y1 p2)
| JPExi : forall H Y0 Y1 t k,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  jobj v H (JT t k) ->
  jobj v H (JP Y0 Y1 (PExi k))
| JPForIntro : forall H Y0 Y1 k p,
  (mE v -> jobj v H (Jwf k CKind)) ->
  jobj v (HCons H k) (JP (lift 1 0 Y0) (lift 1 0 Y1) p) ->
  jobj v H (JP Y0 Y1 (PFor k p))
| JPForElim : forall H Y0 Y1 t k p,
  jobj v H (JT t k) ->
  jobj v H (JP Y0 Y1 (PFor k p)) ->
  jobj v H (JP Y0 Y1 (subst t 0 p))
| JPRes : forall H Y0 Y1 t k p,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  jobj v H (JT t (KRes k p)) ->
  jobj v H (JP Y0 Y1 (subst t 0 p))
| JPFix : forall H Y0 Y1 p,
  (mE v -> jobj v H (Jwf p CProp)) ->
  jobj v H (JP Y0 (YCons Y1 p) p) ->
  mR v -> jobj v H (JP Y0 Y1 p)
| JPCoer : forall H Y0 Y1 H' HH' t' t,
  Happ H H' HH' ->
  jobj v H (JC Y0 Y1 H' t' t) ->
  jobj v HH' (JT t' KStar) ->
  jobj v H (JP Y0 Y1 (PCoer H' t' t))
(* props (coercions) *)
| JCProp : forall H Y0 Y1 H' t' t,
  jobj v H (JP Y0 Y1 (PCoer H' t' t)) ->
  jobj v H (JC Y0 Y1 H' t' t)
| JCRefl : forall H Y0 Y1 t,
  cobj H CTEnv ->
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  cobj t CType ->
  jobj v H (JC Y0 Y1 HNil t t)
| JCTrans : forall H H2 H1 Y0 Y1 t1 t2 t3 HH2 H2H1,
  Happ H H2 HH2 ->
  Happ H2 H1 H2H1 ->
  jobj v HH2 (JC (lift (Hlength H2) 0 Y0) (lift (Hlength H2) 0 Y1) H1 t1 t2) ->
  jobj v H (JC Y0 Y1 H2 t2 t3) ->
  jobj v H (JC Y0 Y1 H2H1 t1 t3)
| JCWeak : forall H H' Y0 Y1 t s,
  jobj v H (JC Y0 Y1 H' (lift (Hlength H') 0 t) s) ->
  jobj v H (JC Y0 Y1 HNil t s)
| JCArr : forall H H' Y0 Y1 t' s' t s Y0Y1 HH',
  Yapp Y0 Y1 Y0Y1 ->
  Happ H H' HH' ->
  (mS v -> jobj v H (JH H')) ->
  (mS v -> jobj v HH' (JT t' KStar)) ->
  (mS v -> jobj v HH' (JT s' KStar)) ->
  (mE v -> jobj v H (JT t KStar)) ->
  jobj v HH' (JC (lift (Hlength H') 0 Y0Y1) YNil HNil (lift (Hlength H') 0 t) t') ->
  jobj v H (JC Y0Y1 YNil H' s' s) ->
  jobj v H (JC Y0 Y1 H' (TArr t' s') (TArr t s))
| JCProd : forall H H' HH' Y0 Y1 t' s' t s Y0Y1,
  Yapp Y0 Y1 Y0Y1 ->
  Happ H H' HH' ->
  (mS v -> jobj v H (JH H')) ->
  (mS v -> jobj v HH' (JT t' KStar)) ->
  (mS v -> jobj v HH' (JT s' KStar)) ->
  jobj v H (JC Y0Y1 YNil H' t' t) ->
  jobj v H (JC Y0Y1 YNil H' s' s) ->
  jobj v H (JC Y0 Y1 H' (TProd t' s') (TProd t s))
| JCSum : forall H H' HH' Y0 Y1 t' s' t s Y0Y1,
  Yapp Y0 Y1 Y0Y1 ->
  Happ H H' HH' ->
  (mS v -> jobj v H (JH H')) ->
  (mS v -> jobj v HH' (JT t' KStar)) ->
  (mS v -> jobj v HH' (JT s' KStar)) ->
  jobj v H (JC Y0Y1 YNil H' t' t) ->
  jobj v H (JC Y0Y1 YNil H' s' s) ->
  jobj v H (JC Y0 Y1 H' (TSum t' s') (TSum t s))
| JCPi : forall H H' HH' HaH' Y0 Y1 k k' s' t' t Y0Y1,
  Yapp Y0 Y1 Y0Y1 ->
  Happ H H' HH' ->
  Happ (HCons H k) (lift 1 0 H') HaH' ->
  (mE v -> jobj v H (Jwf k CKind)) ->
  jobj v H (JH H') ->
  (mS v -> jobj v (HCons HH' k') (JT t' KStar)) ->
  jobj v HaH' (JT s' (lift 1 (Hlength H') k')) ->
  jobj v (HCons H k) (JC (lift 1 0 Y0Y1) YNil
                         (lift 1 0 H') (subst s' 0 (lift 1 (1 + Hlength H') t')) t) ->
  jobj v H (JC Y0 Y1 H' (TPi k' t') (TPi k t))
| JCGen : forall H Y0 Y1 k t,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  cobj t CType ->
  jobj v H (JK k) ->
  (mS v -> jobj v (HCons H k) (JT t KStar)) ->
  jobj v H (JC Y0 Y1 (HCons HNil k) t (TFor k t))
| JCInst : forall H Y0 Y1 k t s,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  cobj t CType ->
  (mS v -> jobj v (HCons H k) (JT t KStar)) ->
  jobj v H (JT s k) ->
  jobj v H (JC Y0 Y1 HNil (TFor k t) (subst s 0 t))
| JCUnfold : forall H Y0 Y1 t,
  cobj H CTEnv ->
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  cobj t CType ->
  (mS v -> jrec 0 t WF) ->
  (mS v -> jobj v (HCons H KStar) (JT t KStar)) ->
  mR v -> jobj v H (JC Y0 Y1 HNil (TMu t) (subst (TMu t) 0 t))
| JCFold : forall H Y0 Y1 t,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  jrec 0 t WF ->
  jobj v (HCons H KStar) (JT t KStar) ->
  mR v -> jobj v H (JC Y0 Y1 HNil (subst (TMu t) 0 t) (TMu t))
| JCTop : forall H Y0 Y1 t,
  cobj H CTEnv ->
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  cobj t CType ->
  (mS v -> jobj v H (JT t KStar)) ->
  jobj v H (JC Y0 Y1 HNil t TTop)
| JCBot : forall H Y0 Y1 t,
  cobj Y0 CPEnv ->
  cobj Y1 CPEnv ->
  jobj v H (JT t KStar) ->
  jobj v H (JC Y0 Y1 HNil TBot t)
(* tenvs *)
| JHNil : forall H,
  cobj H CTEnv ->
  jobj v H (JH HNil)
| JHCons : forall H H' HH' k,
  Happ H H' HH' ->
  jobj v H (JH H') ->
  jobj v HH' (JK k) ->
  jobj v H (JH (HCons H' k))
(* aenvs *)
| JGNil : forall H,
  cobj H CTEnv ->
  jobj v H (JG GNil)
| JGCons : forall H G t,
  jobj v H (JG G) ->
  jobj v H (JT t KStar) ->
  jobj v H (JG (GCons G t))
(* well-formedness *)
| WKStar : forall H,
  cobj H CTEnv ->
  jobj v H (Jwf KStar CKind)
| WKOne : forall H,
  cobj H CTEnv ->
  jobj v H (Jwf KOne CKind)
| WKProd : forall H k1 k2,
  jobj v H (Jwf k1 CKind) ->
  jobj v H (Jwf k2 CKind) ->
  jobj v H (Jwf (KProd k1 k2) CKind)
| WKRes : forall H k p,
  jobj v H (Jwf k CKind) ->
  jobj v (HCons H k) (Jwf p CProp) ->
  jobj v H (Jwf (KRes k p) CKind)
| WPTrue : forall H,
  cobj H CTEnv ->
  jobj v H (Jwf PTrue CProp)
| WPAnd : forall H p1 p2,
  jobj v H (Jwf p1 CProp) ->
  jobj v H (Jwf p2 CProp) ->
  jobj v H (Jwf (PAnd p1 p2) CProp)
| WPCoer : forall H H' HH' t' t,
  Happ H H' HH' ->
  jobj v H (JH H') ->
  jobj v HH' (JT t' KStar) ->
  jobj v H (JT t KStar) ->
  jobj v H (Jwf (PCoer H' t' t) CProp)
| WPExi : forall H k,
  jobj v H (Jwf k CKind) ->
  jobj v H (Jwf (PExi k) CProp)
| WPFor : forall H k p,
  jobj v H (Jwf k CKind) ->
  jobj v (HCons H k) (Jwf p CProp) ->
  jobj v H (Jwf (PFor k p) CProp)
| WHNil : forall H,
  cobj H CTEnv ->
  jobj v H (Jwf HNil CTEnv)
| WHCons : forall H H' HH' k',
  Happ H H' HH' ->
  jobj v H (Jwf H' CTEnv) ->
  jobj v HH' (Jwf k' CKind) ->
  jobj v H (Jwf (HCons H' k') CTEnv)
| WYNil : forall H,
  cobj H CTEnv ->
  jobj v H (Jwf YNil CPEnv)
| WYCons : forall H Y p,
  jobj v H (Jwf Y CPEnv) ->
  jobj v H (Jwf p CProp) ->
  jobj v H (Jwf (YCons Y p) CPEnv)
.
