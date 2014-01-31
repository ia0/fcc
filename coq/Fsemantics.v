Require Import Omega.
Require Import Min.
Require Import List.

Require Import ext.
Require Import set.
Require Import minmax.
Require Import Flanguage.
Require Import Fnormalization.

(** * Semantics of the Indexed Calculus *)

(** ** Definition of types *)

(** *** Set properties *)

(** We define the _interior_ of a set of terms [R] as the set of terms
smaller than a term in [R].
*)
Definition Dec (R : set) : set := fun b => exists a, R a /\ le_term b a.
Hint Unfold Dec.

(** We define the _contraction_ of a set of terms [R] as the set of
direct reducts of a term of [R].
*)
Definition Red (R : set) : set := fun b => exists a, R a /\ red a b.
Hint Unfold Red.

(** We define the _expansion_ of a set of terms [R] with respect to
the property [P], the set of terms satisfying [P] and for which all
their direct reducts are in [R].
*)
Definition Exp (P : set) (R : set) : set := fun a => P a /\ forall b, red a b -> R b.
Hint Unfold Exp.

Definition ExpFix (P : set) (a : term) (R : forall b, red a b -> Prop) : Prop :=
  P a /\ forall b (H : red a b), R b H.

(** Neutral and valid terms are stable by interior, while head normal
forms are stable by both interior and contraction.
*)
Lemma DecN : Inc (Dec N) N.
Proof.
intros b [a [Na ba]].
destruct b; destruct a; simpl in ba; try (exfalso; exact ba); try exact I; inversion Na.
Qed.

Lemma DecCN : Inc (Dec CN) CN.
Proof.
intros b [a [CNa ba]].
destruct b; destruct a; simpl in ba; try (exfalso; exact ba); try exact I; inversion CNa.
Qed.

Lemma RedCN : Inc (Red CN) CN.
Proof. intros b [a [CNa Hred]]. apply CN_red with a; auto. Qed.

Definition DecV : Inc (Dec V) V.
Proof.
intros b [a [Va ba]] Eb; apply Va; clear Va; generalize a ba Eb; clear a ba Eb.
induction b; intros a ba Eb; destruct_binary a ba; inversion Eb;
try match goal with
  | H : fill ?c _ _ = _ |- _ => destruct c; simpl in *; inversion H; clear H
end; subst.
(* 20: CtxLam *)
  apply ErrCtx with (c := CtxLam); auto.
(* 19: CtxApp1 *)
  apply ErrCtx with (c := CtxApp1 a2); auto.
(* 18: CtxApp2 *)
  apply ErrCtx with (c := CtxApp2 a1); auto.
(* 17: App *)
  apply ErrApp.
  apply CN_le_term with b1; auto.
  apply NotArr_le_term with b1; auto.
(* 16: CtxPair1 *)
  apply ErrCtx with (c := CtxPair1 a2); auto.
(* 15: CtxPair2 *)
  apply ErrCtx with (c := CtxPair2 a1); auto.
(* 14: CtxFst *)
  apply ErrCtx with (c := CtxFst); auto.
(* 13: Fst *)
  apply ErrFst.
  apply CN_le_term with b; auto.
  apply NotProd_le_term with b; auto.
(* 12: CtxSnd *)
  apply ErrCtx with (c := CtxSnd); auto.
(* 11: Snd *)
  apply ErrSnd.
  apply CN_le_term with b; auto.
  apply NotProd_le_term with b; auto.
(* 10: CtxAbsurd *)
  apply ErrCtx with (c := CtxAbsurd); auto.
(* 9: Absurd *)
  apply ErrAbsurd.
  apply CN_le_term with b; auto.
(* 8: CtxInl *)
  apply ErrCtx with (c := CtxInl); auto.
(* 7: CtxInr *)
  apply ErrCtx with (c := CtxInr); auto.
(* 6: CtxMatch1 *)
  apply ErrCtx with (c := CtxMatch1 a2 a3); auto.
(* 5: CtxMatch2 *)
  apply ErrCtx with (c := CtxMatch2 a1 a3); auto.
(* 4: CtxMatch3 *)
  apply ErrCtx with (c := CtxMatch3 a1 a2); auto.
(* 3: Match *)
  apply ErrMatch.
  apply CN_le_term with b1; auto.
  apply NotSum_le_term with b1; auto.
(* 2: CtxInst *)
  apply ErrCtx with (c := CtxInst); auto.
(* 1: Inst *)
  apply ErrInst.
  apply CN_le_term with b; auto.
  apply NotPi_le_term with b; auto.
Qed.

Lemma DecNV : Inc (Dec NV) NV.
Proof.
intros b [a [[Na Va] ba]].
split; [apply DecN|apply DecV]; exists a; auto.
Qed.

(** *** Sound terms *)

(** We say that a term is sound if all its reduction paths lead to a
valid term. Said otherwise, we coinductively define the set of sound
terms as the set of terms equal to its expansion with respect to valid
terms.
*)
Definition OK : set := Fix _ (ExpFix V).

Lemma OK_def : OK = Exp V OK.
Proof.
apply extEq; split; intros a Ha.
(* -> *)
  unfold OK, Fix in Ha.
  rewrite Init.Wf.Fix_eq in Ha; [exact Ha|intros].
  f_equal.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality_dep; intros.
  apply H.
(* <- *)
  unfold OK, Fix.
  rewrite Init.Wf.Fix_eq; [exact Ha|intros].
  f_equal.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality_dep; intros.
  apply H.
Qed.

Lemma fold_OK : forall a, Exp V OK a -> OK a.
Proof. intros; rewrite OK_def; auto. Qed.

Lemma unfold_OK : forall a, OK a -> Exp V OK a.
Proof. intros; rewrite <- OK_def; auto. Qed.

(** *** The closure operator *)

(** We define the _closure_ of a set [R], the closure of [R] by
expansion with respect to valid neutral terms.
*)
Definition Cl (R : set) : set := Fix _ (fun a ClR => R a \/ ExpFix NV a ClR).

Lemma Cl_def : forall R, Cl R = Union R (Exp NV (Cl R)).
Proof.
intros R; apply extEq; split; intros a Ha.
(* -> *)
  unfold Cl, Fix in Ha.
  rewrite Init.Wf.Fix_eq in Ha; [exact Ha|intros].
  repeat f_equal.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality_dep; intros.
  apply H.
(* <- *)
  unfold Cl, Fix.
  rewrite Init.Wf.Fix_eq; [exact Ha|intros].
  repeat f_equal.
  apply functional_extensionality_dep; intros.
  apply functional_extensionality_dep; intros.
  apply H.
Qed.

Lemma fold_Cl : forall R a, (R a \/ Exp NV (Cl R) a) -> Cl R a.
Proof. intros; rewrite Cl_def; auto. Qed.

Lemma unfold_Cl : forall R a, Cl R a -> (R a \/ Exp NV (Cl R) a).
Proof. intros; rewrite Cl_def in H; auto. Qed.

Lemma Cl_monotone : forall (R S : set), (forall a, R a -> S a) -> forall a, Cl R a -> Cl S a.
Proof.
intros R S RS a.
induction_red a; rewrite Cl_def; intros [Ha|[NVa Expa]]; rewrite Cl_def; [left|right]; auto.
Qed.

(** *** Pretype and types *)

(** We define predicates for sets of sound terms or sets stable by
interior, contraction, or expansion with respect to valid neutral
terms.
*)
Definition Pok R := Inc R OK.
Definition Pdec R := Inc (Dec R) R.
Definition Pred R := Inc (Red R) R.
Definition Pexp R := Inc (Exp NV R) R.
Hint Unfold Pok Pdec Pred Pexp.

(** We define [C] the set of pretypes, which are sets of sound terms
stable by interior and contraction. We define [CE] the set of types,
which are pretypes stable by expansion (with respect to valid neutral
terms). These two notions are very close to the notion of reducibility
candidates, which is why we write them [C] and [CE].
*)
Record C (R : set) : Prop := C_ {
  Cok : Pok R ;
  Cdec : Pdec R ;
  Cred : Pred R }.
Arguments Cok [R] _ _ _.
Arguments Cdec [R] _ _ _.
Arguments Cred [R] _ _ _.

Record CE (R : set) : Prop := CE_ {
  CEok : Pok R ;
  CEdec : Pdec R ;
  CEred : Pred R ;
  CEexp : Pexp R }.
Arguments CEok [R] _ _ _.
Arguments CEdec [R] _ _ _.
Arguments CEred [R] _ _ _.
Arguments CEexp [R] _ _ _.

Lemma CE_CPexp : forall R, Pexp R -> C R -> CE R.
Proof.
intros R PR CR; apply CE_.
apply (Cok CR).
apply (Cdec CR).
apply (Cred CR).
apply PR.
Qed.

Lemma C_CE : forall {R}, CE R -> C R.
Proof. intros ? [? ? ? ?]; apply C_; auto. Qed.

(** *** Properties *)

(** We can show that the set of sound terms is a type.
*)
Lemma Pdec_OK : Pdec OK.
Proof.
intros b; intros [a [OKa ba]].
generalize b OKa ba; clear b OKa ba; induction_red a; intros b OKa ba.
rewrite OK_def in OKa; rewrite OK_def.
destruct OKa as [Va Expa].
split; [apply DecV; exists a; auto|intros b' redb].
destruct (le_term_red _ _ _ ba redb) as [a' [? ?]].
apply IHa with (b := a'); auto.
Qed.

Lemma Pred_OK : Pred OK.
Proof.
intros b [a [OKa Hred]].
rewrite OK_def in OKa.
destruct OKa as [_ Expa].
apply Expa; auto.
Qed.

Lemma Pexp_OK : Pexp OK.
Proof. intros a [[Na Va] Expa]; rewrite OK_def; auto. Qed.

Lemma C_OK : C OK.
Proof.
apply C_.
- intros a OKa; exact OKa.
- apply Pdec_OK.
- apply Pred_OK.
Qed.

(** The closure operator preserves the pretype property and adds by
definition the expansion property. As a consequence, the closure of a
pretype is a type.
*)
Lemma OKV : forall a, OK a -> V a.
Proof. intros a OKa; rewrite OK_def in OKa; destruct OKa; assumption. Qed.

Lemma Cv : forall {R a}, Pok R -> R a -> V a.
Proof. intros R a CR Ra; apply OKV; apply CR; assumption. Qed.

Lemma Pexp_Cl : forall R, Pexp (Cl R).
Proof. intros R a Ha; rewrite Cl_def; right; exact Ha. Qed.

Lemma C_Cl : forall {R}, C R -> C (Cl R).
Proof.
intros R CR; apply C_.
(* 3: Cok *)
  intros a; induction_red a.
  intros Cla; rewrite Cl_def in Cla.
  destruct Cla as [Pa|[[Na Va] Expa]].
  (* 4: Pa *) apply (Cok CR); exact Pa.
  (* 3: Expa *)
    rewrite OK_def.
    split; [exact Va|intros b Hred].
    apply IHa; [|apply Expa]; assumption.
(* 2: Cdec *)
  intros b; induction_red b. intros [a [Cla ba]].
  rewrite Cl_def in Cla; rewrite Cl_def.
  destruct Cla as [Pa|[NVa Expa]]; [left|right].
  (* 3: Pb *)
    apply (Cdec CR); exists a; split; assumption.
  (* 2: Expb *)
    split; [apply DecNV; exists a; split; assumption|].
    intros; apply IHb; try assumption.
    destruct (le_term_red _ _ _ ba H) as [a0 [? ?]].
    exists a0; auto.
(* 1: Cred *)
  intros b [a [Cla Hred]]; rewrite Cl_def in Cla.
  destruct Cla as [Pa|[[Na Va] Expa]]; auto.
  rewrite Cl_def; left; apply (Cred CR); exists a; auto.
Qed.

Lemma CE_Cl : forall {R}, C R -> CE (Cl R).
Proof.
intros R CR.
pose proof (C_Cl CR) as [? ? ?].
apply CE_; auto.
apply Pexp_Cl.
Qed.

(** The closure operator is also idempotent on types.
*)
Lemma destruct_Cl_CN : forall R a, CN a -> Cl R a -> R a.
Proof.
intros R a CNa Ha; apply unfold_Cl in Ha as [Ha|[[Na _] _]]; auto.
exfalso; apply (CN_N a); auto.
Qed.

Lemma split_Cl : forall (R : set) a, (CN a -> R a) -> (N a -> Exp NV (Cl R) a) -> Cl R a.
Proof. intros R a H1 H2; destruct (N_dec a); apply fold_Cl; [left|right]; auto. Qed.

Lemma Cl_CE : forall R, CE R -> Cl R = R.
Proof.
intros R CR; apply extEq; split; intros a Ha; [|rewrite Cl_def; left; auto].
generalize Ha; clear Ha; induction_red a; intros Ha.
destruct (N_dec a); [apply destruct_Cl_CN; auto|].
apply (CEexp CR).
repeat split; auto; [apply (Cv (Cok (C_Cl (C_CE CR)))); auto|].
intros b Hred.
apply IHa; auto.
apply (Cred (C_Cl (C_CE CR))).
exists a; auto.
Qed.

(** ** The arrow and product operators *)

(** We define the arrow pretype operator [PArr R S] from type [R] to
type [S] as the set of sound term abstractions satisfying a
substitution property directly related to the reduction rule of the
arrow type. If the term abstraction [Lam k a] has no fuel, then it is
in all arrow types. If it has some strictly positive fuel [k], then we
consider [k - 1] to be the current level of observation. For all
argument [b] in [R], the substitution [subst b 0 a] has to be in [S].
Because we only observe at level [k - 1], we lower the term before
checking membership. This explains why the arrow (pre)type operator is
well-founded (Lemma [WF_PArr]): level [k] only looks at level [k - 1].

We then define the arrow type operator [EArr] as the closure of its
pretype version.
*)
Definition PArr (R S : set) : set := fun lam =>
  exists k a, lam = Lam k a /\ OK a /\
  (k > 0 -> forall b, R (lower (k - 1) b) -> S (lower (k - 1) (subst b 0 a))).
Definition EArr (R S : set) : set := Cl (PArr R S).
Hint Unfold PArr EArr.

(** We similarly define the product pretype operator [PProd R S] of
types [R] and [S] as the set of sound pairs satisfying a projection
property directly related to the reduction rules of the product type.
If a pair [Pair k a b] has no fuel, then it is in all product types.
If it has some strictly positive fuel [k], then we consider [k - 1] to
be the current level of observation and each component (or projection
of the pair) has to be in the correct type.

We then define the product type operator [EProd] as the closure of its
pretype version.
*)
Definition POne : set := fun unit => exists k, unit = Unit k.
Definition EOne : set := Cl POne.
Hint Unfold POne EOne.

Definition PProd (R S : set) : set := fun pair =>
  exists k a b, pair = Pair k a b /\ (OK a /\ OK b) /\
  (k > 0 -> (R (lower (k - 1) a) /\ S (lower (k - 1) b))).
Definition EProd (R S : set) : set := Cl (PProd R S).
Hint Unfold PProd EProd.

Definition PVoid : set := fun void => False.
Definition EVoid : set := Cl PVoid.
Hint Unfold PVoid EVoid.

Definition PSum (R S : set) : set := fun sum =>
  exists k a, ((sum = Inl k a /\ OK a /\ (k > 0 -> (R (lower (k - 1) a))))
            \/ (sum = Inr k a /\ OK a /\ (k > 0 -> (S (lower (k - 1) a))))).
Definition ESum (R S : set) : set := Cl (PSum R S).
Hint Unfold PSum ESum.

(** In order to show that the arrow and product operators preserve
pretypes and types, we show a few lemmas. Variables are sound and in
all sets stable by expansion. Term abstractions and pairs are sound,
if their components are sound.
*)
Lemma OK_Var : forall k n, OK (Var k n).
Proof.
intros k n; rewrite OK_def.
split; [apply V_Var|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H.
Qed.

Lemma R_Var : forall {R k n}, Pexp R -> R (Var k n).
Proof.
intros R k n CR; apply CR.
split; [apply NV_Var|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H.
Qed.

Lemma OK_Unit : forall {k}, OK (Unit k).
Proof.
intros k.
rewrite OK_def.
split; [apply V_Unit|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H; clear H; subst.
Qed.

Lemma OK_Lam : forall {k a}, OK a -> OK (Lam k a).
Proof.
intros k a; induction_red a.
rewrite OK_def; intros [Va Expa].
split; [apply V_Lam; exact Va|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H; clear H; subst.
apply Pdec_OK.
exists (Lam (S k0) a'); split; [apply IHa; auto|].
simpl; split; auto.
apply binary_fuel_refl; auto.
Qed.

Lemma OK_Pair : forall {k a b}, OK a -> OK b -> OK (Pair k a b).
Proof.
intros k a; induction_red a; intros b; induction_red b.
intros OKa OKb; generalize OKa OKb; rewrite OK_def; intros [Va Expa] [Vb Expb].
split; [apply V_Pair; assumption|].
intros b0 Hred; inversion Hred.
destruct c; simpl in *; inversion H; clear H; subst;
apply Pdec_OK;
repeat (match goal with
  | |- Dec OK (Pair ?k ?a ?b) => exists (Pair (S k) a b)
  | |- _ /\ _ => split
  | |- OK (Pair _ _ _) => first [apply IHa|apply IHb]
  | |- le_term _ _ => simpl; split; [|split]
  | |- le_term ?x ?x => apply binary_fuel_refl
end; auto).
Qed.

Lemma OK_Inl : forall {k a}, OK a -> OK (Inl k a).
Proof.
intros k a; induction_red a.
rewrite OK_def; intros [Va Expa].
split; [apply V_Inl; exact Va|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H; clear H; subst.
apply Pdec_OK.
exists (Inl (S k0) a'); split; [apply IHa; auto|].
simpl; split; auto.
apply binary_fuel_refl; auto.
Qed.

Lemma OK_Inr : forall {k a}, OK a -> OK (Inr k a).
Proof.
intros k a; induction_red a.
rewrite OK_def; intros [Va Expa].
split; [apply V_Inr; exact Va|].
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H; clear H; subst.
apply Pdec_OK.
exists (Inr (S k0) a'); split; [apply IHa; auto|].
simpl; split; auto.
apply binary_fuel_refl; auto.
Qed.

Lemma R_lower : forall R a k, Pdec R -> R a -> R (lower k a).
Proof.
intros R a k CR Ra.
apply CR.
exists a; split; auto.
apply le_term_lower_trivial.
Qed.

(** We also show that term soundness does not look at the actual names
of free variables. Free variables are just inert objects.
*)
Lemma OK_subst_Var : forall a i x, OK (subst (Var 0 x) i a) -> OK a.
Proof.
intros a; induction_red a; intros i x OKa.
apply fold_OK.
pose proof (unfold_OK _ OKa) as [Va Expa].
split; [apply V_subst_N with (b := Var 0 x) (i := i); simpl; auto|].
intros b Hred; eapply IHa; [assumption|].
apply Expa; apply red_subst; assumption.
Qed.

(** The arrow pretype operator preserves pretypes.
*)
Lemma C_PArr : forall R {S}, C S -> C (PArr R S).
Proof.
intros R S CS.
apply C_.
(* 3: Cok *)
  intros lam [k [a [Heq [Hok Hsub]]]]; subst.
  apply OK_Lam; auto.
(* 2: Cdec *)
  intros a' [lam [[k [a [Heq [Hok Hsub]]]] lea]]; subst.
  destruct_binary a' lea.
  rename k0 into k'; exists k'; exists a'; split; [reflexivity|split].
  (* 3: Hok *)
    apply Pdec_OK; exists a; auto.
  (* 2: Hsub *)
    intros Hk' b Rb.
    rewrite lower_subst; rewrite <- subst_lower; rewrite <- lower_subst.
    apply (Cdec CS); exists (lower (k - 1) (subst (lower (k' - 1) b) 0 a)).
    split; [apply Hsub; [omega|]|].
    (* 3 *)
      rewrite lower_lower.
      rewrite Min.min_l; auto; omega.
    (* 2 *)
      apply le_term_lower; [omega|].
      apply le_term_subst; [apply binary_fuel_refl|]; auto.
(* 1: Cred *)
  intros a' [lam [[k [a [Heq [Hok Hsub]]]] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H; clear H; subst;
  rename a'0 into a', k0 into k.
  exists k; exists a'; split; [reflexivity|split].
  (* 2: Hok *)
    apply Pred_OK; exists a; auto.
  (* 1: Hsub *)
    intros Hk b Rb.
    rewrite lower_subst; rewrite <- subst_lower; rewrite <- lower_subst.
    destruct k; [inversion Hk|clear Hk]; simpl in *.
    pose proof (red_subst _ _ (lower k b) H0 0).
    pose proof (red_lower _ _ k H) as [? [? ?]].
    rewrite <- minus_n_O in *.
    apply (Cdec CS).
    exists x; split; auto.
    apply (Cred CS).
    eexists; split; [|eassumption].
    apply Hsub; [omega|].
    rewrite lower_lower.
    rewrite Min.min_l; auto; omega.
Qed.

(** The arrow operator builds a type if its return set is a pretype.
*)
Lemma CE_EArr : forall R {S}, C S -> CE (EArr R S).
Proof.
intros; apply CE_Cl.
apply C_PArr; auto.
Qed.

(** This result is not necessary for the proof of soundness, but we
discuss it in the manuscript.
*)
Lemma Push_right_Arr : forall R' S' R S, C S' -> Pexp R -> Inc (EArr R' S') (EArr R S) -> Inc S' S.
Proof.
intros R' S' R S CS' CR Hinc a S'a.
destruct (term_le_exists a) as [k ak].
remember (Lam (1 + k) (shift 0 a)) as a'.
assert (EArr R S a').
(* 2 *)
- apply Hinc.
  subst; apply fold_Cl; left.
  exists (1 + k), (shift 0 a); repeat split; auto.
  (* +1: ok *)
    apply OK_subst_Var with 0 0.
    unfold shift; rewrite subst_lift_0.
    apply (Cok CS'); auto.
  (* +0 *)
  simpl; intros Hk b Rb; rewrite <- minus_n_O in *.
  unfold shift; rewrite subst_lift_0.
  apply (Cdec CS'); exists a; repeat split; auto.
  apply le_term_lower_trivial.
(* 1 *)
- subst.
  unfold EArr in H; apply destruct_Cl_CN in H; simpl; auto.
  destruct H as [? [? [Heq [Hok Hsub]]]]; inversion Heq; clear Heq; subst.
  simpl in *; rewrite <- minus_n_O in *.
  rewrite (term_le_lower a k); auto.
  unfold shift in Hsub; rewrite <- (subst_lift_0 a (Var 0 0)).
  apply Hsub; try omega.
  apply R_Var.
  apply CR.
Qed.

(** The one pretype operator is a type.
*)
Lemma C_POne : C POne.
Proof.
apply C_.
(* Cok *)
  intros a [k ?]; subst; apply OK_Unit.
(* Cdec *)
  intros a [one [[k ?] lea]]; subst.
  destruct_binary a lea.
  exists k0; reflexivity.
(* Cred *)
  intros a [one [[k ?] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H.
Qed.

Lemma CE_EOne : CE EOne.
Proof.
intros; apply CE_Cl.
apply C_POne; auto.
Qed.

(** The product pretype operator preserves prettypes.
*)
Lemma C_PProd : forall {R S}, C R -> C S -> C (PProd R S).
Proof.
intros R S CR CS.
apply C_.
(* 3: Cok *)
  intros pair [k [a [b [Heq [[Hoka Hokb] Hproj]]]]]; subst.
  apply OK_Pair; auto.
(* 2: Cdec *)
  intros a' [pair [[k [a [b [Heq [[Hoka Hokb] Hproj]]]]] lea]]; subst.
  destruct_binary a' lea.
  rename k0 into k', a'1 into a', a'2 into b'; exists k'; exists a'; exists b';
  split; [reflexivity|split].
  (* 3: Hok *) split; apply Pdec_OK; [exists a|exists b]; split; auto.
  (* 2: Hsub *)
    intros Hk'; assert (k > 0) as Hk by omega; destruct (Hproj Hk).
    split; [apply (Cdec CR); exists (lower (k - 1) a)|apply (Cdec CS); exists (lower (k - 1) b)];
    split; auto; apply le_term_lower; first [omega|auto].
(* 1: Cred *)
  intros a' [pair [[k [a [b [Heq [[Hoka Hokb] Hproj]]]]] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H; clear H; subst;
  [rename a'0 into a'|rename a'0 into b']; rename k0 into k;
  exists k; [exists a'; exists b|exists a; exists b']; (split; [reflexivity|split]).
  (* CtxPair1 *)
    (* 4: Hok *)
      split; auto; apply Pred_OK; exists a; split; auto.
    (* 3: Hsub *)
      intros Hk; assert (1 + k > 0) as Hk' by omega; destruct (Hproj Hk').
      destruct k; [inversion Hk|clear Hk]; simpl in *; rewrite <- minus_n_O.
      split; [apply (Cdec CR)|apply (Cdec CS)].
      (* 4: R *)
        pose proof (red_lower _ _ k H0) as [? [? ?]].
        exists x; split; auto.
        apply (Cred CR); eexists; eauto.
      (* 3: S *)
        exists (lower (1 + k) b); split; auto.
        apply le_term_lower; auto.
        apply binary_fuel_refl; auto.
  (* CtxPair2 *)
    (* 2: Hok *)
      split; auto; apply Pred_OK; exists b; split; auto.
    (* 1: Hsub *)
      intros Hk; assert (1 + k > 0) as Hk' by omega; destruct (Hproj Hk').
      destruct k; [inversion Hk|clear Hk]; simpl in *; rewrite <- minus_n_O.
      split; [apply (Cdec CR)|apply (Cdec CS)].
      (* 2: R *)
        exists (lower (1 + k) a); split; auto.
        apply le_term_lower; auto.
        apply binary_fuel_refl; auto.
      (* 1: S *)
        pose proof (red_lower _ _ k H0) as [? [? ?]].
        exists x; split; auto.
        apply (Cred CS); eexists; eauto.
Qed.

(** The product operator builds a type if its arguments are types.
*)
Lemma CE_EProd : forall {R S}, C R -> C S -> CE (EProd R S).
Proof.
intros; apply CE_Cl.
apply C_PProd; auto.
Qed.

(** The void pretype operator is a type.
*)
Lemma C_PVoid : C PVoid.
Proof.
apply C_.
(* Cok *)
  intros a Ha; destruct Ha.
(* Cdec *)
  intros a [void [Hvoid lea]]; destruct Hvoid.
(* Cred *)
  intros a [void [Hvoid Hred]]; destruct Hvoid.
Qed.

Lemma CE_EVoid : CE EVoid.
Proof.
intros; apply CE_Cl.
apply C_PVoid; auto.
Qed.

(** The sum pretype operator preserves prettypes.
*)
Lemma C_PSum : forall {R S}, C R -> C S -> C (PSum R S).
Proof.
intros R S CR CS.
apply C_.
(* 3: Cok *)
  intros sum [k [a [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]]; subst.
  apply OK_Inl; auto.
  apply OK_Inr; auto.
(* 2: Cdec *)
  intros a' [sum [[k [a [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]] lea]]; subst;
  destruct_binary a' lea; rename k0 into k'; exists k'; exists a'; [left|right];
  (split; [reflexivity|split; [apply Pdec_OK; exists a; auto|]]);
  intros Hk'; assert (k > 0) as Hk by omega;
  [apply (Cdec CR)|apply (Cdec CS)]; exists (lower (k - 1) a);
  split; auto; apply le_term_lower; first [omega|auto].
(* 1: Cred *)
  intros a' [sum [[k [a [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]] Hred]]; subst;
  inversion Hred; destruct c; simpl in *; inversion H; clear H; subst;
  rename a'0 into a'; rename k0 into k; exists k; exists a'; [left|right];
  (split; [reflexivity|split; [apply Pred_OK; exists a; auto|]]);
  intros Hk; assert (1 + k > 0) as Hk' by omega;
  (destruct k; [inversion Hk|clear Hk]); simpl in *; rewrite <- minus_n_O;
  [apply (Cdec CR)|apply (Cdec CS)]; pose proof (red_lower _ _ k H0) as [? [? ?]];
  exists x; split; auto; [apply (Cred CR)|apply (Cred CS)]; eexists; eauto.
Qed.

(** The sum operator builds a type if its arguments are types.
*)
Lemma CE_ESum : forall {R S}, C R -> C S -> CE (ESum R S).
Proof.
intros; apply CE_Cl.
apply C_PSum; auto.
Qed.

(** ** The forall operator *)

(** We define [For I cond func] as the intersection of a family of
sets [func] indexed with the Coq elements of [I] satisfying the
condition [cond]. The forall operator [EFor I cond func] is then the
set of sound terms in the intersection [For I cond func].

The forall operator preserves the property [P], written [EFor_preserve
P], if given that for all valid indices [i H] the indexed set [func i
H] satisfies the property [P], the forall type [EFor I cond func]
satisfies the property [P] too.
*)
Definition For I (cond : I -> Prop) (func : forall i, cond i -> set) : set := fun a =>
  forall i H, func i H a.
Definition EFor I (cond : I -> Prop) (func : forall i, cond i -> set) : set := fun a =>
  OK a /\ For I cond func a.
Definition EFor_preserve P := forall Ix cond func,
  (forall i H, P (func i H)) -> P (EFor Ix cond func).
Hint Unfold For EFor EFor_preserve.

(** The forall operator preserves pretypes.
*)
Lemma C_EFor : EFor_preserve C.
Proof.
intros Ix cond func Hfor; apply C_.
(* Cok *)
  intros a [OKa Ha]; exact OKa.
(* Cdec *)
  intros b [a [[OKa Ha] ba]].
  split; [apply Pdec_OK; exists a; auto|].
  intros i ci.
  apply (Cdec (Hfor i ci)).
  exists a; auto.
(* Cred *)
  intros b [a [[OKa Ha] Hred]].
  split; [apply Pred_OK; exists a; auto|].
  intros i ci.
  apply (Cred (Hfor i ci)); exists a; auto.
Qed.

(** The forall operator preserves stability by expansion.
*)
Lemma Pexp_EFor : EFor_preserve Pexp.
Proof.
intros Ix cond func Hfor a [NVa Expa].
split.
- apply Pexp_OK.
  split; auto.
  intros b Hred; apply (Expa b Hred).
- intros i ci.
  apply (Hfor i ci).
  split; auto.
  intros b Hred.
  apply (Expa b Hred).
Qed.

(** The forall operator preserves types.
*)
Lemma CE_EFor : EFor_preserve CE.
Proof.
intros Ix cond func Hfor.
apply CE_CPexp.
apply Pexp_EFor; auto; intros; apply CEexp; auto.
apply C_EFor; auto; intros; apply C_CE; auto.
Qed.

(** ** The pi operator *)

(** We define the pi pretype operator [PPi I cond func], as the set of
type abstractions satisfying an intersection property related to its
destruction with type application. Type abstractions are always sound,
which is why we do not explicitly state it. A type abstraction [Gen k
a] with no fuel is in all pi pretypes. If it has some strictly
positive fuel, then the body (lower with [k - 1]) has to be in all
possible semantic instantiations.

The pi type operator [EPi I cond func] is simply the closure of its
pretype version [PPUi I cond func].
*)
Definition PPi I (cond : I -> Prop) (func : forall i, cond i -> set) : set := fun gen =>
  exists k a, gen = Gen k a /\
  (k > 0 -> forall i H, func i H (lower (k - 1) a)).
Definition EPi I cond func : set := Cl (PPi I cond func).
Hint Unfold PPi EPi.

Lemma OK_Gen : forall k a, OK (Gen k a).
Proof.
intros k a; induction_red a.
rewrite OK_def; split.
- intros Erra; inversion Erra.
  destruct c; simpl in H; inversion H; clear H.
- intros b Hred; inversion Hred.
  destruct c; simpl in *; inversion H; clear H.
Qed.

(** The pi pretype operator preserves pretypes.
*)
Lemma C_PPi : forall I cond func, (forall i H, C (func i H)) -> C (PPi I cond func).
Proof.
intros I cond func Cfunc.
apply C_.
(* 3: Cok *)
  intros gen [k [a [Heq Hfor]]]; subst.
  apply OK_Gen; auto.
(* 2: Cdec *)
  intros a' [gen [[k [a [Heq Hfor]]] lea]]; subst.
  destruct_binary a' lea.
  rename k0 into k'; exists k'; exists a'; split; [reflexivity|].
  intros Hk' i Hi.
  apply (Cdec (Cfunc i Hi)).
  exists (lower (k - 1) a); split; [apply Hfor; omega|].
  apply le_term_lower; auto; omega.
(* 1: Cred *)
  intros a' [gen [[k [a [Heq Hfor]]] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H; clear H.
Qed.

(** The pi type operator builds a type if its family of sets are
pretypes.
*)
Lemma CE_EPi : forall I cond func, (forall i H, C (func i H)) -> CE (EPi I cond func).
Proof.
intros; apply CE_Cl.
apply C_PPi; auto.
Qed.

(** ** The exists operator

This operator is actually problematic, which explains why the
following definition and properties are not natural. Existential types
cannot be simply expressed as erasable types. In System F, the
soundness of erasable existential types actually relies on the
standardization of the Lambda Calculus.
*)

(** We define the exists pretype operator [PExi I cond func], as the
union of its indexed sets. The exists type operator [EExi I cond func]
is simply the closure of its pretype version.

The exists pretype operator preserves the property [P], written
[PExi_preserve P], if given that all indexed sets satisfy [P], the
exists pretype operator satisfies [P] too.

The preservation property for the exists type operator is different.
We write, [EExi_preserve P Q], when the exists type operator satisfies
the property [Q] whenever all its indexed sets satisfy [P].
*)
Definition PExi I (cond : I -> Prop) (func : forall i, cond i -> set) : set :=
  fun a => exists i H, func i H a.
Definition PExi_preserve P := forall Ix cond func,
  (forall i H, P (func i H)) -> P (PExi Ix cond func).
Definition EExi I cond func := Cl (PExi I cond func).
Definition EExi_preserve P Q := forall Ix cond func,
  (forall i H, P (func i H)) -> Q (EExi Ix cond func).
Hint Unfold PExi PExi_preserve EExi EExi_preserve.

(** The exists pretype operator preserves pretypes.
*)
Lemma C_PExi : PExi_preserve C.
Proof.
intros Ix cond func Hfor; apply C_.
(* Cok *) intros a [i [Ci Ha]]; apply (Cok (Hfor i Ci)); apply Ha.
(* Cdec *)
  intros b [a [[i [Ci Hb]] ba]]; exists i, Ci.
  apply (Cdec (Hfor i Ci)); exists a; auto.
(* Cred *)
  intros b [a [[i [Ci Hb]] ba]]; exists i, Ci.
  apply (Cred (Hfor i Ci)); exists a; auto.
Qed.

(** The exists type operator is always stable by expansion.
*)
Lemma Pexp_EExi : EExi_preserve (fun _ => True) Pexp.
Proof.
intros Ix cond func Hexi a [NVa Expa].
apply fold_Cl; right; auto.
Qed.

(** The exists type operator builds a type when its indexed sets are
pretypes.
*)
Lemma CE_EExi : EExi_preserve C CE.
Proof.
intros Ix cond func Hexi.
apply CE_CPexp.
apply Pexp_EExi; auto.
apply C_Cl; apply C_PExi; auto.
Qed.

(** ** The top and bottom operators *)

(** We define the top operator [ETop] as the exists type operator of
all types. It is a type, and thus a pretype.
*)
Definition ETop : set := EExi set CE (fun R _ => R).

Lemma CE_ETop : CE ETop.
Proof. apply CE_EExi; intros i H; apply C_CE; auto. Qed.

Lemma C_ETop : C ETop.
Proof. apply C_CE; apply CE_ETop. Qed.

(** We define the bottom operator [EBot] as the forall type operator
of all types. It is a type, and thus a pretype.
*)
Definition EBot : set := EFor set CE (fun R _ => R).

Lemma CE_EBot : CE EBot.
Proof.
apply CE_EFor.
intros i H; exact H.
Qed.

Lemma C_EBot : C EBot.
Proof. apply C_CE; apply CE_EBot. Qed.

Lemma EVoid_EBot : EVoid = EBot.
Proof.
apply extEq; split; intros a.
(* -> *)
  induction_red a.
  intros Ha.
  unfold EVoid in Ha; apply unfold_Cl in Ha as [Ha|[NVa Expa]].
  { destruct Ha. }
  apply (CEexp CE_EBot).
  split; auto.
(* <- *)
  intros [OKa Fora].
  apply Fora.
  apply CE_EVoid.
Qed.

(** ** Recursive types

Recursive types explain why we need to use an indexed semantics
instead of a usual semantic of types as sets of lambda terms.
Reduction may not always terminate and some proofs relying on strong
normalization do not hold. Using indices permits to recover the proof
step using induction on strong normalization of terms. See for example
the proof of Lemma [EApp_sem].
*)

(** We write [iter F k X] the [k]-iteration of a functor [F] (a
function on sets) on the set [X] and show a few simple properties. In
particular, if a property [P] holds for [X] and is preserved by [F]
(which we write [CF P F]), then it holds for all iterations of [F] on
[X].
*)
Fixpoint iter (F : set -> set) k X : set :=
  match k with
    | O => X
    | S k => F (iter F k X)
  end.

Definition CF (P : set -> Prop) (F : set -> set) : Prop := forall R, P R -> P (F R).
Hint Unfold CF.

Lemma CF_iter_F : forall P F R, CF P F -> P R -> forall k, P (iter F k R).
Proof.
intros P F R CFF CR k; induction k; auto.
apply (CFF (iter F k R)); apply IHk.
Qed.

Lemma iter_dec : forall F X k, iter F (1 + k) X = iter F k (F X).
Proof. intros F X k; induction k; simpl in *; [|rewrite IHk]; reflexivity. Qed.

Lemma iter_le : forall F X k j, j <= k -> iter F k X = iter F j (iter F (k - j) X).
Proof.
intros F X k; induction k; intros j Hjk; [inversion Hjk; reflexivity|simpl in *].
destruct j as [|j]; [reflexivity|].
rewrite (IHk j); [reflexivity|omega].
Qed.

(** *** The mu operator *)

(** We define the mu pretype operator [Mu Bot F] as the iteration of
[F] on [Bot] controlled by indices. A term [a] is in the pretype
operator [Mu Bot F] if it is in the [k]-iteration of [F] on [Bot] for
all indices [k] greater than [a], ie. all indices [k] greater than all
the indices of [a].

An alternative version [Mu' Bot F] of the mu pretype operator is to
see it as the limit of the [k]-iterations of [F] on [Bot] when [k]
approaches infinity. The limit is defined as a monotone union indexed
by [k] of some approximation (see [approx]) of the [k]-iteration of
[F] on [Bot]. The proof is done in Lemma [Mu_Mu'] and requires the
functor [F] to be well-founded.

The mu type operator is its pretype version instantiated with [EBot]
as the starting set.
*)
Definition Mu Bot (F : set -> set) : set := fun a =>
  forall k, term_lt a k -> iter F k Bot a.
Definition EMu := Mu EBot.
Hint Unfold Mu EMu.

Definition Mu' Bot (F : set -> set) : set := fun a =>
  exists k, term_lt a k /\ iter F k Bot a.

(** *** The notion of k-approximation *)

(** We define the [k]-approximation of a set [R], written [approx R
k], the subset of [R] of terms smaller than [k]. This permits to talk
about a set [R] at level [k]. At level 0, [approx R 0] is empty
because no term are smaller than zero. And the limit of [approx R k]
when [k] reaches infinity is the set [R] itself. Because this level
relies on terms, it is common to all sets and we can thus show
properties about sets only by looking at fixed but arbitrary levels. A
typical example will be the proof that the mu operator is equal to its
unfolding (Lemmas [Mu_approx_iter], [Mu_unfold], and [Mu_fold]).

We then show a few simple commutation properties about [approx].
*)
Definition approx (R : set) k : set := fun a => term_lt a k /\ R a.
Hint Unfold approx.

Lemma approx_unfold : forall k R a, approx R k a -> R a.
Proof. intros R k a [Hk Ha]; exact Ha. Qed.

Lemma approx_fold : forall (R : set) k a, R a -> term_lt a k -> approx R k a.
Proof. intros R k a Ha ak; auto. Qed.

Lemma approx_approx : forall R j k, j <= k -> approx R j = approx (approx R k) j.
Proof.
intros R j k jk.
apply extEq; split; intros a [? ?]; repeat split; auto.
(* 2 *)
  eapply unary_fuel_1; [|apply H].
  simpl; intros; omega.
(* 1 *)
  destruct H0; auto.
Qed.

Lemma approx_min : forall R j k, approx (approx R k) j = approx R (min j k).
Proof.
intros R j k.
apply extEq; split; intros a [? ?]; repeat split; auto.
destruct H0; apply term_lt_min; auto.
destruct H0; auto.
apply lt_term_le with (min j k); auto.
minmax.
apply lt_term_le with (min j k); auto.
minmax.
Qed.

Lemma approx_swap : forall R j k, approx (approx R k) j = approx (approx R j) k.
Proof.
intros R j k.
apply extEq; split; intros a [? [? ?]]; repeat split; auto.
Qed.

Lemma approx0 : forall R S, Inc (approx R 0) (approx S 0).
Proof. intros R S a [? ?]; exfalso; apply (term_lt_0 a); auto. Qed.

Lemma approx0_eq : forall R S, approx R 0 = approx S 0.
Proof. intros R S; apply extEq; split; intros a Ha; apply (approx0 _ _ a Ha). Qed.

Lemma approx_inc : forall R S, (forall k a, approx R k a -> approx S k a) -> forall a, R a -> S a.
Proof.
intros R S H a Ra.
destruct (term_lt_exists a) as [k ak].
apply approx_unfold with (k := k); auto.
Qed.

Lemma approx_eq : forall R S, (forall k, approx R k = approx S k) -> R = S.
Proof.
intros R S H.
apply extEq; split; intros a Ha; (eapply approx_inc; [|apply Ha]); intros.
rewrite <- H; auto.
rewrite H; auto.
Qed.

Lemma Cl_approx : forall R k a, approx (Cl R) k a -> Cl (approx R k) a.
Proof.
intros R k a.
induction_red a; intros [ak Ha].
apply unfold_Cl in Ha as [Ha|[NVa Expa]]; apply fold_Cl; [left|right]; auto.
split; auto; intros b Hred.
apply IHa; auto; split; auto.
apply term_lt_red with (a := a); auto.
Qed.

Lemma Cl_approx_eq : forall R k, approx (Cl R) k = approx (Cl (approx R k)) k.
Proof.
intros R k; apply extEq; split.
(* -> *)
  intros a [ak Ha]; split; auto.
  apply Cl_approx; auto.
(* <- *)
  intros a; induction_red a; intros [ak Ha].
  split; auto.
  apply unfold_Cl in Ha as [[_ Ha]|[NVa Expa]]; apply fold_Cl; [left|right]; auto.
  split; auto; intros b Hred.
  apply IHa; auto; split; auto.
  apply term_lt_red with (a := a); auto.
Qed.

Lemma Inc_approx : forall R k a, approx R k a -> R a.
Proof. intros; apply (approx_unfold k); auto. Qed.

(** *** The notion of well-foundness and non-expansiveness

The mu type operator has good properties only if its iterated functor
is well-founded. This notion is introduced in this section.
*)

(** We define the set [CST] of constant type functors, the set [WFj j]
of [j]-well-founded functors, the set [WF] of well-founded functors,
and the set [NE] of non-expansiveness functors.

A functor is constant if it returns always the same set. A functor is
[j]-well-founded, if [F] only uses level [k - j] of [R] to builds the
level [k] of [F R]. A functor is well-founded if it is
[1]-well-founded, and it is non-expansive if it is [0]-well-founded.
*)
Definition CST (F : set -> set) : Prop := exists C, forall R, F R = C.
Definition WFj j (F : set -> set) : Prop :=
  forall R k, approx (F R) k = approx (F (approx R (k - j))) k.
Definition WF F :=
  forall R k, approx (F R) (1 + k) = approx (F (approx R k)) (1 + k).
Definition NE := WFj 0.
Hint Unfold CST WFj WF NE.

Lemma WFj_WF : forall F, WFj 1 F <-> WF F.
Proof.
intros; split; intros ? R k.
(* 2 *)
  rewrite (H R (1 + k)).
  destruct k; simpl; auto.
(* 1 *)
  destruct k; simpl; [apply approx0_eq|].
  replace (k - 0) with k by omega.
  apply H.
Qed.

(** A constant functor is [j]-well-founded for all level [j], and
reciprocally.
*)
Lemma WF_CST : forall F, CST F -> forall j, WFj j F.
Proof. intros F [C HF] j R k; rewrite 2 HF; reflexivity. Qed.

Lemma CST_WF : forall F, (forall j, WFj j F) -> CST F.
Proof.
intros F HF; exists (F EBot); intros R.
apply approx_eq; intros k.
rewrite (HF k R k).
rewrite (HF k EBot k).
replace (k - k) with 0 by omega.
rewrite approx0_eq with (S := EBot).
reflexivity.
Qed.

(** If a functor is [i]-well-founded, then it is [j]-well-founded for
all level [j] smaller than [i].
*)
Lemma WFj_dec : forall F i j, i >= j -> WFj i F -> WFj j F.
Proof.
intros F ij j Hij HF R k.
rewrite (HF R k).
rewrite (HF (approx R (k - j)) k).
rewrite <- (approx_approx R (k - ij) (k - j)); [|omega].
reflexivity.
Qed.

(** The identity functor is non-expansive.
*)
Lemma NE_id : forall F, (forall R, F R = R) -> NE F.
Proof. intros F H R k; repeat rewrite H; rewrite <- approx_approx; auto; omega. Qed.

(** The starting set of the [k]-iteration of a well-founded functor
[F] does not matter at level [k].
*)
Lemma WF_swap : forall F R S k, WF F -> approx (iter F k R) k = approx (iter F k S) k.
Proof.
intros F R S k WFF; induction k.
(* 0 *)
  apply extEq; split; simpl; apply approx0; assumption.
(* 1+ *)
  rewrite (WFF (iter F k R)); rewrite (WFF (iter F k S)); simpl.
  replace (k - 0) with k by omega.
  rewrite IHk; reflexivity.
Qed.

(** Approximation preserves pretypes.
*)
Lemma C_approx : forall R k, C R -> C (approx R k).
Proof.
intros R k CR.
apply C_.
(* Pok *) intros a [_ Ha]; apply (Cok CR); auto.
(* Pdec *)
  intros b [a [[ak Ha] ba]].
  split; [apply le_term_lt with a; auto|].
  apply (Cdec CR); exists a; auto.
(* Pred *)
  intros b [a [[ak Ha] Hred]].
  split; [apply term_lt_red with a; auto|].
  apply (Cred CR); exists a; auto.
Qed.

(** All [k]-iterations of a well-founded functor [F] are equal at
level [j] for all [k] greater or equal to [j].
*)
Lemma WF_approx_le : forall F R j k, WF F -> j <= k ->
  approx (iter F k R) j = approx (iter F j R) j.
Proof.
intros F R j k WFF Hjk.
rewrite iter_le with (j := j) (k := k); [|exact Hjk].
apply WF_swap; auto.
Qed.

(** If a term [a] is smaller than [k] and [j], then it is the the
[k]-iteration of a well-founded functor [F] whenever it is in the
[j]-iteration of [F].
*)
Lemma WF_iter_lt : forall F R j k a, WF F -> term_lt a k -> term_lt a j ->
  iter F j R a -> iter F k R a.
Proof.
intros F R j k a WFF ak aj Fja.
remember (min k j) as x.
assert (x <= k); [subst; apply le_min_l|].
assert (x <= j); [subst; apply le_min_r|].
apply (approx_unfold x).
rewrite WF_approx_le; auto.
rewrite <- WF_approx_le with (k := j); auto.
apply approx_fold; auto; subst.
apply term_lt_min; assumption.
Qed.

(** The mu operator preserves types when the functor is well-founded
and preserves types.
*)
Lemma CE_EMu : forall F, CF CE F -> WF F -> CE (EMu F).
Proof.
pose proof CE_EBot as CEBot.
intros F CFF WFF; apply CE_.
(* Cok *)
  intros a Ha.
  destruct (term_lt_exists a).
  pose proof (Ha x H).
  apply (CEok (CF_iter_F CE F EBot CFF CEBot x)); assumption.
(* Cdec *)
  intros b [a [Ha ba]] j bj.
  destruct (term_lt_exists a) as [k ak].
  pose proof (le_term_lt b a k ba ak) as bk.
  apply WF_iter_lt with (j := k); auto.
  apply CEdec; [apply CF_iter_F; auto|].
  exists a; split; auto.
(* Cred *)
  intros b [a [Ha Hred]] j bj.
  destruct (term_lt_exists a) as [k ak].
  pose proof (term_lt_red a b k Hred ak) as bk.
  apply WF_iter_lt with (j := k); auto.
  apply CEred; [apply CF_iter_F; auto|].
  exists a; split; auto.
(* Cexp *)
  intros a [NVa Expa] j aj.
  apply CEexp; [apply CF_iter_F; auto|].
  split; auto; intros b Hred.
  apply (Expa b Hred).
  apply term_lt_red with a; auto.
Qed.

(** We show that for well-founded functors, the mu operator is
actually the [k]-iteration at level [k]. This permits to show that the
mu operator is equal to its unfolding for well-founded functors.
*)
Lemma Mu_approx_iter : forall F k Bot, WF F -> approx (Mu Bot F) k = approx (iter F k Bot) k.
Proof.
intros F k Bot WFF; apply extEq; split; intros a [ak Ha]; split; auto.
intros j aj.
eapply WF_iter_lt; auto; [apply ak|apply Ha].
Qed.

Lemma Mu_unfold : forall F Bot, WF F -> Inc (Mu Bot F) (F (Mu Bot F)).
Proof.
intros F Bot WFF a Ha.
destruct (term_lt_exists a) as [k ak].
assert (term_lt a (1 + k)); [eapply unary_fuel_1; [|apply ak]; instantiate; simpl; intros j H; omega|clear ak].
apply approx_unfold with (k := 1 + k).
rewrite WFF.
rewrite Mu_approx_iter; [|assumption].
rewrite <- WFF.
apply approx_fold; auto.
apply (Ha (1 + k)); auto.
Qed.

Lemma Mu_fold : forall F Bot, WF F -> Inc (F (Mu Bot F)) (Mu Bot F).
Proof.
intros F Bot WFF a Ha k ak.
destruct k; [exfalso; apply (term_lt_0 a ak)|].
apply approx_unfold with (k := 1 + k); simpl.
rewrite WFF.
rewrite <- Mu_approx_iter; [|assumption].
rewrite <- WFF.
apply approx_fold; auto.
Qed.

Lemma Mu_Mu' : forall F Bot, WF F -> Mu Bot F = Mu' Bot F.
Proof.
intros F Bot WFF; apply extEq; split; intros a Ha.
(* -> *)
  destruct (term_lt_exists a) as [k ak].
  exists k; auto.
(* <- *)
  destruct Ha as [k [ak Ha]].
  intros j aj.
  apply WF_iter_lt with k; auto.
Qed.

(** *** Computational types are well-founded

Computational types are well-founded in the sense that, they increase
by one the level of well-foundness of their arguments. For example, if
[F] is [j]-well-founded and [G] is [k]-well-founded, then

[[
  fun X => EArr (F X) (G X)
]]

is [(1 + min j k)]-well-founded.
*)

(** The arrow pretype and type operators are well-founded.
*)
Lemma WF_PArr : forall R S k,
  approx (PArr R S) (1 + k) = approx (PArr (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k; apply extEq; split; intros a [ak Ha]; split; auto.
(* -> *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  destruct Ha as [j [a' [Heq [Hok Hsub]]]].
  rename a into lam, a' into a; exists j; exists a; split; [|split]; auto; subst lam.
  intros Hj b Rb.
  split; destruct ak as [jk ak].
  (* 3 *)
    apply unary_fuel_map_trivial; intros.
    destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]; omega.
  (* 2 *)
    apply Hsub; auto.
    apply (Inc_approx R k); auto.
(* <- *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  destruct Ha as [j [a' [Heq [Hok Hsub]]]].
  rename a into lam, a' into a; exists j; exists a; split; [|split]; auto; subst lam.
  intros Hj b Rb; destruct ak as [jk ak].
  apply Hsub; auto.
  split; auto.
  apply unary_fuel_map_trivial; intros.
  destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]; omega.
Qed.

Lemma WF_EArr : forall R S k,
  approx (EArr R S) (1 + k) = approx (EArr (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k.
unfold EArr.
rewrite Cl_approx_eq.
rewrite WF_PArr.
rewrite <- Cl_approx_eq.
reflexivity.
Qed.

Lemma WFj_EArr : forall R S k,
  approx (EArr R S) k = approx (EArr (approx R (k - 1)) (approx S (k - 1))) k.
Proof.
intros R S k.
destruct k; [apply approx0_eq|]; simpl; rewrite <- minus_n_O.
apply WF_EArr.
Qed.

(** The product pretype and type operators are well-founded.
*)
Lemma WF_PProd : forall R S k,
  approx (PProd R S) (1 + k) = approx (PProd (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k; apply extEq; split; intros a [ak Ha]; split; auto.
(* 2: -> *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  destruct Ha as [j [a' [b' [Heq [Hok Hproj]]]]].
  rename a into pair, a' into a, b' into b; exists j, a, b; split; [|split]; auto; subst pair.
  intros Hj; split.
  (* 3: R *)
    split; destruct ak as [jk [ak bk]]; [|apply Hproj; auto].
    apply unary_fuel_map_trivial; intros.
    destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]; omega.
  (* 2: S *)
    split; destruct ak as [jk [ak bk]]; [|apply Hproj; auto].
    apply unary_fuel_map_trivial; intros.
    destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]; omega.
(* 1: <- *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  destruct Ha as [j [a' [b' [Heq [Hok Hproj]]]]].
  rename a into pair, a' into a, b' into b; exists j, a, b; split; [|split]; auto; subst pair.
  intros Hj; destruct ak as [jk [ak bk]].
  split; apply Hproj; auto.
Qed.

Lemma WF_EProd : forall R S k,
  approx (EProd R S) (1 + k) = approx (EProd (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k.
unfold EProd.
rewrite Cl_approx_eq.
rewrite WF_PProd.
rewrite <- Cl_approx_eq.
reflexivity.
Qed.

Lemma WFj_EProd : forall R S k,
  approx (EProd R S) k = approx (EProd (approx R (k - 1)) (approx S (k - 1))) k.
Proof.
intros R S k.
destruct k; [apply approx0_eq|]; simpl; rewrite <- minus_n_O.
apply WF_EProd.
Qed.

(** The sum pretype and type operators are well-founded.
*)
Lemma WF_PSum : forall R S k,
  approx (PSum R S) (1 + k) = approx (PSum (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k; apply extEq; split; intros a [ak Ha]; split; auto.
(* 2: -> *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha;
  destruct Ha as [j [a' [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]];
  rename a into sum, a' into a; exists j, a; [left|right];
  (split; [|split]); auto; subst sum; intros Hj; split; auto;
  destruct ak as [jk ak]; apply unary_fuel_map_trivial; intros;
  (destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]); omega.
(* 1: <- *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha;
  destruct Ha as [j [a' [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]];
  rename a into sum, a' into a; exists j, a; [left|right];
  (split; [|split]); auto; subst sum; intros Hj; destruct ak as [jk ak];
  apply Hin; auto.
Qed.

Lemma WF_ESum : forall R S k,
  approx (ESum R S) (1 + k) = approx (ESum (approx R k) (approx S k)) (1 + k).
Proof.
intros R S k.
unfold ESum.
rewrite Cl_approx_eq.
rewrite WF_PSum.
rewrite <- Cl_approx_eq.
reflexivity.
Qed.

Lemma WFj_ESum : forall R S k,
  approx (ESum R S) k = approx (ESum (approx R (k - 1)) (approx S (k - 1))) k.
Proof.
intros R S k.
destruct k; [apply approx0_eq|]; simpl; rewrite <- minus_n_O.
apply WF_ESum.
Qed.

(** The pi pretype and type operators are well-founded.
*)
Lemma WF_PPi : forall I cond func k,
  approx (PPi I cond func) (1 + k) = approx (PPi I cond (fun i H => approx (func i H) k)) (1 + k).
Proof.
intros I cond func k; apply extEq; split; intros a [ak Ha]; split; auto.
(* -> *)
  destruct Ha as [j [a' [Heq Hpi]]].
  rename a into gen, a' into a; exists j; exists a; split; auto.
  intros Hj i H; subst gen.
  destruct ak as [jk ak].
  split; [|apply Hpi; auto].
  apply unary_fuel_map_trivial; intros.
  destruct (lt_dec k0 (j - 1)); [rewrite min_l|rewrite min_r]; omega.
(* <- *)
  destruct Ha as [j [a' [Heq Hpi]]].
  rename a into gen, a' into a; exists j; exists a; split; auto.
  intros Hj i H; subst gen.
  destruct ak as [jk ak].
  apply Hpi; auto.
Qed.

Lemma WF_EPi : forall I cond func k,
  approx (EPi I cond func) (1 + k) = approx (EPi I cond (fun i H => approx (func i H) k)) (1 + k).
Proof.
intros I cond func k.
unfold EPi.
rewrite Cl_approx_eq.
rewrite WF_PPi.
rewrite <- Cl_approx_eq.
reflexivity.
Qed.

Lemma WFj_EPi : forall I cond func k,
  approx (EPi I cond func) k = approx (EPi I cond (fun i H => approx (func i H) (k - 1))) k.
Proof.
intros I cond func k.
destruct k; [apply approx0_eq|]; simpl; rewrite <- minus_n_O.
apply WF_EPi.
Qed.

(** *** Erasable types are non-expansive

Erasable types are non-expansive in the sense that they preserve the
level of well-foundness of their arguments. For example, if the
indexed sets [func X] are [j]-well-founded according to [X], then the
forall operator [EFor I cond (func X)] is [j]-well-founded according
to [X].
*)

(** The forall operator is non-expansive.
*)
Lemma WFj_EFor : forall j F Ix cond func, (forall i H, WFj j (fun X => func X i H)) ->
  (forall X, F X = EFor Ix cond (func X)) -> WFj j F.
Proof.
intros j F Ix cond func H HF R k; repeat rewrite HF.
apply extEq; split; intros a [ak [OKa Ha]]; split; auto; split; auto; intros i ci.
(* 2: -> *)
  apply approx_unfold with k.
  rewrite <- H.
  apply approx_fold; auto.
(* 1: -> *)
  apply approx_unfold with k.
  rewrite H.
  apply approx_fold; auto.
Qed.

(** The exists pretype and type operators are non-expansive.
*)
Lemma WFj_PExi : forall j F Ix cond func, (forall i H, WFj j (fun X => func X i H)) ->
  (forall X, F X = PExi Ix cond (func X)) -> WFj j F.
Proof.
intros j F Ix cond func H HF R k; repeat rewrite HF.
apply extEq; split; intros a [ak [i [ci Ha]]]; split; auto; exists i, ci.
(* 2: -> *)
  apply approx_unfold with k.
  rewrite <- H.
  apply approx_fold; auto.
(* 1: -> *)
  apply approx_unfold with k.
  rewrite H.
  apply approx_fold; auto.
Qed.

Lemma WFj_EExi : forall j F Ix cond func, (forall i H, WFj j (fun X => func X i H)) ->
  (forall X, F X = EExi Ix cond (func X)) -> WFj j F.
Proof.
intros j F Ix cond func H HF R k; repeat rewrite HF.
apply extEq; split; intros a [ak Ha]; split; auto.
(* -> *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  unfold EExi in Ha; apply unfold_Cl in Ha as [?|[? ?]]; apply fold_Cl; [left|right].
  (* +1 *)
    apply approx_unfold with k.
    rewrite <- (WFj_PExi j (fun X => PExi Ix cond (func X)) Ix cond func); auto.
  (* +0 *)
    split; auto; intros b Hred.
    apply IHa; auto.
    apply term_lt_red with a; auto.
(* <- *)
  generalize ak Ha; clear ak Ha; induction_red a; intros ak Ha.
  unfold EExi in Ha; apply unfold_Cl in Ha as [?|[? ?]]; apply fold_Cl; [left|right].
  (* +1 *)
    apply approx_unfold with k.
    rewrite (WFj_PExi j (fun X => PExi Ix cond (func X)) Ix cond func); auto.
  (* +0 *)
    split; auto; intros b Hred.
    apply IHa; auto.
    apply term_lt_red with a; auto.
Qed.

(** The mu operator of a well-founded functor is non-expansive.
*)
Lemma WFj_min : forall F R jk k, WFj (jk - k) F ->
  approx (F R) jk = approx (F (approx R k)) jk.
Proof.
intros F R jk k HF.
destruct (le_gt_dec jk k).
(* 2 *)
  replace (jk - k) with 0 in HF by omega.
  rewrite HF.
  rewrite (HF (approx R k)).
  replace (jk - 0) with jk by omega.
  rewrite (approx_approx R jk k); auto.
(* 1 *)
  rewrite HF.
  replace (jk - (jk - k)) with k by omega.
  reflexivity.
Qed.

Lemma WFj_Mu : forall j F Bot, (forall X, WF (F X)) ->
  (forall Y, WFj j (fun X => F X Y)) ->
  WFj j (fun X => (Mu Bot (fun Y => F X Y))).
Proof.
intros j F Bot HX HY R k.
rewrite 2 Mu_approx_iter; auto.
assert (forall i,
  approx (iter (fun Y : set => F R Y) k Bot) k =
  approx (iter (fun Y : set => F (approx R (i + (k - j))) Y) k Bot) k); [|apply (H 0)].
induction k; intros i; [apply approx0_eq|].
destruct (le_gt_dec j k).
(* 2: j <= k *)
  replace (i + (S k - j)) with (1 + i + (k - j)) by omega.
  simpl; rewrite HX; simpl.
  rewrite IHk with (1 + i); simpl.
  rewrite <- HX; simpl.
  apply (WFj_min (fun X => F X _) R).
  apply WFj_dec with j; auto; omega.
(* 1 *)
  replace (i + (S k - j)) with i by omega.
  simpl; rewrite HX; simpl.
  rewrite IHk with i.
  replace (i + (k - j)) with i by omega.
  rewrite <- HX; simpl.
  apply (WFj_min (fun X => F X _) R).
  apply WFj_dec with j; auto; omega.
Qed.

(** ** Semantic judgment

We define a notion of semantic judgment and show the soundness of the
usual rules of the simply typed lambda calculus. We also show a type
coercion rule and distributivity rule, that together show a typing
coercion rule.
*)

(** The judgment operator uses a substitution operator. We write
[Subst R S] the set of term [a] such that for all argument [b] in [R],
the substitution [subst b 0 a] is in [S].

The judgment operator [EJudg G S], where [G] is a list of sets for the
free variables, is defined inductively on the list [G], using [S] for
the nil case and [Subst] for the substitution of the last free
variable. A term [a] is thus in [EJudg G S] if its substitution with
terms in [G] is in [S].

Another solution for the definition of the inductive case, closer to a
simultaneous substitution, could have been:

[[
  Subst (Map (lift (length G) 0) R) (EJudg G S)
]]

where [Map f R] is the set of terms of the form [f a] whenever [a] is
in the set [R]. Our version is closer to a telescope. Each
substitution may use the preceding free variables, and not have to
refer to the top-level.
*)
Definition Subst (R S : set) : set := fun a => forall b, R b -> S (subst b 0 a).
Fixpoint EJudg (G : list set) (S : set) : set :=
  match G with
    | nil => S
    | cons R G => Subst (EJudg G R) (EJudg G S)
  end.
Hint Unfold Subst EJudg.

(** We show that the judgment [EJudg G S] is a pretype whenever the
set [S] is a pretype and the sets [G] are stable by expansion.
*)
Lemma Pdec_EJudg : forall G S, C S -> Pdec (EJudg G S).
Proof.
induction G as [|R G]; intros S CS a' [a [Ha ba]]; simpl in *.
(* nil *)
  apply (Cdec CS); exists a; auto.
(* cons *)
  intros b Hb; apply IHG; auto.
  exists (subst b 0 a); split; auto.
  apply le_term_subst; auto.
  apply binary_fuel_refl; auto.
Qed.

Lemma Pred_EJudg : forall G S, C S -> Pred (EJudg G S).
Proof.
induction G as [|R G]; intros S CS a' [a [Ha ba]]; simpl in *.
(* nil *)
  apply (Cred CS); exists a; auto.
(* cons *)
  intros b Hb; apply IHG; auto.
  exists (subst b 0 a); split; auto.
  apply red_subst; auto.
Qed.

Lemma EJudg_Var : forall G S, Pexp S -> EJudg G S (Var 0 (length G + 1)).
Proof.
intros G S CS; induction G; simpl.
(* 2: nil *) apply R_Var; auto.
(* 1: cons *)
  intros b Hb.
  simpl; subst_lift_var.
  rewrite <- minus_n_O.
  apply IHG.
Qed.

Lemma Pok_EJudg : forall G S, Forall Pexp G -> C S -> Pok (EJudg G S).
Proof.
induction G as [|R G]; intros S CG CS a Ha; simpl in *.
(* 2: nil *)
  apply (Cok CS); auto.
(* 1: cons *)
  apply OK_subst_Var with (x := (length G + 1)) (i := 0).
  inversion CG; subst.
  apply (IHG S H2 CS _).
  apply Ha; apply EJudg_Var; auto.
Qed.

Lemma C_EJudg : forall G S, Forall Pexp G -> C S -> C (EJudg G S).
Proof.
intros G S CG CS; apply C_.
(* CPok *) apply Pok_EJudg; auto.
(* CPdec *) apply Pdec_EJudg; auto.
(* CPred *) apply Pred_EJudg; auto.
Qed.

(** *** Soundness of the computational typing rules

We show that the typing rules for variables, abstractions,
applications, pairs, projections, type abstractions, and type
applications are sound.

All the proofs proceed by induction on the environment [G].
Constructors use the definition of the associated type operator, while
destructors proceed by induction on the strong normalization of the
conclusion term and stability by expansion of types.
*)

Lemma EVar_sem : forall R k x G, C R ->
  nth x G ETop = R ->
  EJudg G R (Var k x).
Proof.
induction x; intros G CR Hx;
(destruct G as [|R0 G]; simpl in *; subst; [apply R_Var; apply Pexp_Cl|]).
(* 0 *)
  intros b Rb; simpl; subst_lift_var; rewrite lift_0.
  apply Pdec_EJudg; auto.
  eexists; split; [apply Rb|].
  apply le_term_lower_trivial.
(* 1+ *)
  intros b0 Rb0.
  simpl; subst_lift_var; rewrite <- minus_n_O.
  apply IHx; auto.
Qed.

Lemma ELam_sem : forall G R S k a, Pexp R -> C S ->
  EJudg (R :: G) S a ->
  EJudg G (EArr R S) (Lam k a).
Proof.
induction G as [|R0 G]; intros R S k a CR CS Ha; simpl in *.
(* 2: nil *)
  apply fold_Cl; left.
  exists k; exists a; split; [|split]; auto.
  (* 3: Hok *)
    apply OK_subst_Var with 0 0.
    apply (Cok CS); apply Ha; apply R_Var; auto.
  (* 2: Hsub *)
    intros Hk b Rb.
    rewrite lower_subst; rewrite <- subst_lower; rewrite <- lower_subst.
    apply (Cdec CS).
    exists (subst (lower (k - 1) b) 0 a).
    split; [apply Ha; auto|].
    apply le_term_lower_trivial.
(* 1: cons *)
  intros b0 Rb0; subst; simpl.
  apply IHG; auto.
  intros b Rb.
  replace b with (subst b0 0 (shift 0 b)); [|apply subst_lift_0].
  rewrite <- subst_subst_0; apply Ha; auto.
  intros ? ?; rewrite subst_lift_0; auto.
Qed.

Lemma EApp_sem : forall G R S k a b, C R -> CE S ->
  EJudg G (EArr R S) a ->
  EJudg G R b ->
  EJudg G S (App k a b).
Proof.
induction G as [|R0 G]; intros R S k a b CR CS Ha Hb; simpl in *.
(* 2: nil *)
  generalize Ha b Hb k; clear Ha b Hb k; induction_red a; intros Ha b; induction_red b; intros Hb k.
  apply (CEexp CS); split; [split|]; simpl; auto.
  (* 3: V *)
    intros Errab; inversion Errab; [destruct c; simpl in *; inversion H; clear H|]; subst.
    (* 5: CtxApp1 *) generalize H0; apply (Cv (CEok (CE_EArr R (C_CE CS)))); auto.
    (* 4: CtxApp2 *) generalize H0; apply (Cv (Cok CR)); auto.
    (* 3: App *)
      unfold EArr in Ha; apply unfold_Cl in Ha.
      destruct Ha.
      (* 4: PArr *)
        destruct H as [? [? [? ?]]]; subst; apply (H3 x x0 eq_refl).
      (* 3: Exp *)
        destruct H as [[? ?] ?].
        apply CN_N with a; auto.
  (* 2: Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H; clear H; subst.
    (* 4: CtxApp1 *) apply IHa; auto; apply (CEred (CE_EArr R (C_CE CS))); exists a; auto.
    (* 3: CtxApp2 *) apply IHb; auto; apply (Cred CR); exists b; auto.
    (* 2: App *)
      subst.
      unfold EArr in Ha; apply unfold_Cl in Ha as [[? [? [? [? ?]]]]|Expa]; subst.
      (* 3: PArr *)
        inversion H; clear H; subst; simpl in *.
        rewrite <- minus_n_O in H1.
        apply (CEdec CS); auto.
        exists (lower k0 (subst b 0 x0)); split; [apply H1; auto; [omega|]|].
        (* 4 *)
          apply (Cdec CR).
          exists b; split; auto.
          apply le_term_lower_trivial.
        (* 3 *) apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax.
      (* 2: Exp *)
        destruct Expa as [[? ?] ?].
        inversion H.
(* 1: cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma EUnit_sem : forall G k, EJudg G EOne (Unit k).
Proof.
induction G as [|R0 G]; intros k; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists k; reflexivity.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EPair_sem : forall G R S k a b, C R -> C S ->
  EJudg G R a ->
  EJudg G S b ->
  EJudg G (EProd R S) (Pair k a b).
Proof.
induction G as [|R0 G]; intros R S k a b CR CS Ha Hb; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists k, a, b; split; [|split]; auto.
  (* Hok *)
    split; [apply (Cok CR)|apply (Cok CS)]; auto.
  (* Hproj *)
    intros Hk; split; [apply (Cdec CR); exists a|apply (Cdec CS); exists b];
    split; auto; apply le_term_lower_trivial.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EFst_sem : forall G R S k a, CE R -> C S ->
  EJudg G (EProd R S) a ->
  EJudg G R (Fst k a).
Proof.
induction G as [|R0 G]; intros R S k a CR CS Ha; simpl in *.
(* nil *)
  generalize Ha k; clear Ha k; induction_red a; intros Ha k.
  apply (CEexp CR); split; [split|]; simpl; auto.
  (* V *)
    intros Errab; inversion Errab; [destruct c; simpl in *; inversion H; clear H|]; subst.
    (* CtxFst *) generalize H0; apply (Cv (CEok (CE_EProd (C_CE CR) CS))); auto.
    (* Fst *)
      unfold EProd in Ha; apply unfold_Cl in Ha.
      destruct Ha.
      (* 4: PProd *)
        destruct H as [? [? [? [? ?]]]]; subst.
        apply (H2 x x0 x1 eq_refl).
      (* 3: Exp *)
        destruct H as [[? ?] ?].
        apply CN_N with a; auto.
  (* Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H; clear H; subst.
    (* CtxFst *) apply IHa; auto; apply (CEred (CE_EProd (C_CE CR) CS)); exists a; auto.
    (* Fst *)
      subst.
      unfold EProd in Ha; apply unfold_Cl in Ha as [[? [? [? [? [? ?]]]]]|Expa]; subst.
      (* PProd *)
        inversion H; clear H; subst; simpl in *.
        rewrite <- minus_n_O in H1.
        apply (CEdec CR); auto.
        exists (lower k0 x0); split; [apply H1; auto; omega|].
        apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax.
      (* Exp *)
        destruct Expa as [[? ?] ?]; inversion H.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma ESnd_sem : forall G R S k a, C R -> CE S ->
  EJudg G (EProd R S) a ->
  EJudg G S (Snd k a).
Proof.
induction G as [|R0 G]; intros R S k a CR CS Ha; simpl in *.
(* nil *)
  generalize Ha k; clear Ha k; induction_red a; intros Ha k.
  apply (CEexp CS); split; [split|]; simpl; auto.
  (* V *)
    intros Errab; inversion Errab; [destruct c; simpl in *; inversion H; clear H|]; subst.
    (* CtxSnd *) generalize H0; apply (Cv (CEok (CE_EProd CR (C_CE CS)))); auto.
    (* Snd *)
      unfold EProd in Ha; apply unfold_Cl in Ha.
      destruct Ha.
      (* 4: PProd *)
        destruct H as [? [? [? [? ?]]]]; subst.
        apply (H2 x x0 x1 eq_refl).
      (* 3: Exp *)
        destruct H as [[? ?] ?].
        apply CN_N with a; auto.
  (* Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H; clear H; subst.
    (* CtxSnd *) apply IHa; auto; apply (CEred (CE_EProd CR (C_CE CS))); exists a; auto.
    (* Snd *)
      subst.
      unfold EProd in Ha; apply unfold_Cl in Ha as [[? [? [? [? [? ?]]]]]|Expa]; subst.
      (* PProd *)
        inversion H; clear H; subst; simpl in *.
        rewrite <- minus_n_O in H1.
        apply (CEdec CS); auto.
        exists (lower k0 x1); split; [apply H1; auto; omega|].
        apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax.
      (* Exp *)
        destruct Expa as [[? ?] ?]; inversion H.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma EAbsurd_sem : forall G S k a, CE S ->
  EJudg G EVoid a ->
  EJudg G S (Absurd k a).
Proof.
induction G as [|R0 G]; intros S k a CS Ha; simpl in *.
(* nil *)
  generalize Ha k; clear Ha k; induction_red a; intros Ha k.
  apply (CEexp CS); split; [split|]; simpl; auto.
  (* V *)
    intros Errab; inversion Errab; [destruct c; simpl in *; inversion H; clear H|]; subst.
    (* CtxAbsurd *) generalize H0; apply (Cv (CEok CE_EVoid)); auto.
    (* Absurd *)
    apply (destruct_Cl_CN PVoid a); auto.
  (* Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H; clear H; subst.
    (* CtxAbsurd *) apply IHa; auto; apply (CEred CE_EVoid); exists a; auto.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG S); auto.
Qed.

Lemma EInl_sem : forall G R S k a, C R ->
  EJudg G R a ->
  EJudg G (ESum R S) (Inl k a).
Proof.
induction G as [|R0 G]; intros R S k a CR Ha; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists k, a; left; split; [|split]; auto.
  (* Hok *) apply (Cok CR); auto.
  (* Hin *)
    intros Hk; apply (Cdec CR); exists a;
    split; auto; apply le_term_lower_trivial.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EInr_sem : forall G R S k a, C S ->
  EJudg G S a ->
  EJudg G (ESum R S) (Inr k a).
Proof.
induction G as [|R0 G]; intros R S k a CS Ha; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists k, a; right; split; [|split]; auto.
  (* Hok *) apply (Cok CS); auto.
  (* Hin *)
    intros Hk; apply (Cdec CS); exists a;
    split; auto; apply le_term_lower_trivial.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EMatch_sem : forall G Rl Rr S k a bl br, CE Rl -> CE Rr -> CE S ->
  EJudg G (ESum Rl Rr) a ->
  EJudg (Rl :: G) S bl ->
  EJudg (Rr :: G) S br ->
  EJudg G S (Match k a bl br).
Proof.
induction G as [|R0 G]; intros Rl Rr S k a bl br CRl CRr CS Ha Hbl Hbr; simpl in *.
(* 2: nil *)
  generalize Ha bl Hbl br Hbr k; clear Ha bl Hbl br Hbr k;
  induction_red a; intros Ha bl; induction_red bl; intros Hbl br; induction_red br; intros Hbr k.
  apply (CEexp CS); split; [split|]; simpl; auto.
  (* +1: V *)
    intros Errab; inversion Errab; [destruct c; simpl in *; inversion H; clear H|]; subst.
    (* +3: CtxMatch1 *) generalize H0; apply (Cv (CEok (CE_ESum (C_CE CRl) (C_CE CRr)))); auto.
    (* +2: CtxMatch2 *)
      generalize H0; apply @Cv with (R := Subst Rl S); auto.
      apply (Pok_EJudg (Rl :: nil) S); auto using C_CE, CEexp.
    (* +1: CtxMatch3 *)
      generalize H0; apply @Cv with (R := Subst Rr S); auto.
      apply (Pok_EJudg (Rr :: nil) S); auto using C_CE, CEexp.
    (* +0: Match *)
      unfold ESum in Ha; apply unfold_Cl in Ha.
      destruct Ha as [Ha|Ha].
      (* +1: PSum *)
        destruct Ha as [k' [a' [[Heq [Hok Hin]]|[Heq [Hok Hin]]]]]; subst.
        apply (proj1 (H4 k' a') eq_refl).
        apply (proj2 (H4 k' a') eq_refl).
      (* +0: Exp *)
        destruct Ha as [[? ?] ?].
        apply CN_N with a; auto.
  (* +0: Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H; clear H; subst.
    (* +4: CtxMatch1 *)
      apply IHa; auto; apply (CEred (CE_ESum (C_CE CRl) (C_CE CRr))); exists a; auto.
    (* +3: CtxMatch2 *)
      apply IHbl; auto.
      apply (Pred_EJudg (Rl :: nil) S); auto using C_CE.
      exists bl; auto.
    (* +2: CtxMatch3 *)
      apply IHbr; auto.
      apply (Pred_EJudg (Rr :: nil) S); auto using C_CE.
      exists br; auto.
    (* +1: Inl *)
      subst; unfold ESum in Ha;
      apply unfold_Cl in Ha as [[k [a Hsum]]|Expa]; subst.
      (* +1: PSum *)
        destruct Hsum as [[Heq [Hok Hin]]|[Heq [Hok Hin]]];
        inversion Heq; clear Heq; subst; simpl in *.
        rewrite <- minus_n_O in Hin.
        apply (CEdec CS); auto.
        exists (subst (lower k0 a) 0 bl); split; [apply Hbl; apply Hin; omega|].
        rewrite lower_subst. rewrite <- subst_lower.
        apply le_term_subst; [apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax|].
        apply le_term_lower_trivial.
      (* +0: Exp *)
        destruct Expa as [[? ?] ?].
        inversion H.
    (* +0: Inr *)
      subst; unfold ESum in Ha;
      apply unfold_Cl in Ha as [[k [a Hsum]]|Expa]; subst.
      (* +1: PSum *)
        destruct Hsum as [[Heq [Hok Hin]]|[Heq [Hok Hin]]];
        inversion Heq; clear Heq; subst; simpl in *.
        rewrite <- minus_n_O in Hin.
        apply (CEdec CS); auto.
        exists (subst (lower k0 a) 0 br); split; [apply Hbr; apply Hin; omega|].
        rewrite lower_subst. rewrite <- subst_lower.
        apply le_term_subst; [apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax|].
        apply le_term_lower_trivial.
      (* +0: Exp *)
        destruct Expa as [[? ?] ?].
        inversion H.
(* 1: cons *)
  intros b0 Rb0; subst; simpl.
  apply (IHG Rl Rr S); auto.
  (* +1: *)
    intros b Rb.
    replace b with (subst b0 0 (shift 0 b)); [|apply subst_lift_0].
    rewrite <- subst_subst_0; apply Hbl; auto.
    intros ? ?; rewrite subst_lift_0; auto.
  (* +0: *)
    intros b Rb.
    replace b with (subst b0 0 (shift 0 b)); [|apply subst_lift_0].
    rewrite <- subst_subst_0; apply Hbr; auto.
    intros ? ?; rewrite subst_lift_0; auto.
Qed.

Lemma EGen_sem : forall I cond func G k a, (forall i H, C (func i H)) ->
  (forall i H, EJudg G (func i H) a) ->
  EJudg G (EPi I cond func) (Gen k a).
Proof.
induction G as [|R0 G]; intros k a Cfunc Ha; simpl in *.
(* 2: nil *)
  apply fold_Cl; left.
  exists k; exists a; split; auto.
  intros Hk i Hi.
  apply (Cdec (Cfunc i Hi)).
  exists a; split; auto.
  apply le_term_lower_trivial.
(* 1: cons *)
  intros b0 Rb0; subst; simpl.
  apply IHG; auto.
  intros i Hi.
  apply Ha; auto.
Qed.

Lemma EInst_sem : forall I cond func G k a, (forall i H, CE (func i H)) ->
  EJudg G (EPi I cond func) a ->
  forall i H, EJudg G (func i H) (Inst k a).
Proof.
induction G as [|R0 G]; intros k a Cfunc Ha i H; simpl in *.
(* 2: nil *)
  generalize Ha k; clear Ha k; induction_red a; intros Ha k.
  apply (CEexp (Cfunc i H)); split; [split|]; simpl; auto.
  (* 3: V *)
    intros Erra; inversion Erra; [destruct c; simpl in *; inversion H0; clear H0|]; subst.
    (* 4: CtxInst *)
      generalize H1; apply (@Cv (EPi I cond func)); auto.
      apply CEok; apply (CE_EPi I cond func); auto.
      intros i0 H0; apply C_CE; auto.
    (* 3: Inst *)
      unfold EPi in Ha; apply unfold_Cl in Ha.
      destruct Ha.
      (* 4: PPi *)
        destruct H0 as [j [a' [Heq Hpi]]]; subst.
        apply (H3 j a' eq_refl).
      (* 3: Exp *)
        destruct H0 as [[? ?] ?].
        apply CN_N with a; auto.
  (* 2: Exp *)
    intros b0 Hred; inversion Hred.
    destruct c; simpl in *; inversion H0; clear H0; subst.
    (* 4: CtxInst *)
      apply IHa; auto.
      apply CEred; [apply (CE_EPi I cond func); intros i0 H0; apply C_CE; auto|].
      exists a; auto.
    (* 2: Inst *)
      subst.
      unfold EPi in Ha; apply unfold_Cl in Ha as [[? [? [? ?]]]|Expa]; subst.
      (* 3: PPi *)
        inversion H0; clear H0; subst; simpl in *.
        rewrite <- minus_n_O in H1.
        apply (CEdec (Cfunc i H)); auto.
        exists (lower k0 x0); split; [apply H1; omega|].
        apply le_term_lower; [|apply binary_fuel_refl; auto]; minmax.
      (* 2: Exp *)
        destruct Expa as [[? ?] ?].
        inversion H0.
(* 1: cons *)
  intros b0 Rb0; simpl.
  apply IHG; auto.
Qed.

(** *** Soundness of erasable rules *)

(** The usual type coercion rule is sound: when a set [R] is a subset
of another set [S], then the judgment [EJudg G R] is a subset of
[EJudg G S]. Notice that this works for all kinds of sets, not only
types or pretypes.
*)
Lemma ECoer_sem : forall G R S, Inc R S -> forall a, EJudg G R a -> EJudg G S a.
Proof.
induction G as [|R0 G]; intros R S RS a Ha; simpl in *; auto.
intros b0 Rb0.
apply (IHG R S); auto.
Qed.

(** The distributivity rule says that the intersection operator (not
the forall operator) and the judgment operator commute, given that the
intersection is not empty and contains only types.
*)
Lemma Edistrib : forall I cond func G a,
  (exists i, cond i) -> (forall i H, CE (func i H)) ->
  For I cond (fun i H => EJudg G (func i H)) a ->
  EJudg G (For I cond func) a.
Proof.
induction G as [|R G]; intros a Hexi CEfunc H; auto; simpl.
intros b0 Rb0; match goal with | |- ?J _ _ _ => replace J with EJudg by reflexivity end.
apply IHG; auto; intros i Hi; apply H; auto.
Qed.

(** This last lemma helps to deal with typing coercions of closures.
It is typically used to prove the eta-expansion rules of computational
types.
*)
Lemma Cl_approx_For : forall Ix cond func (R : set) k,
  (exists i, cond i) -> (forall i H, C (func i H)) ->
  (forall a, term_lt a k -> For Ix cond func a -> R a) ->
  forall a, term_lt a k -> For Ix cond (fun i H => Cl (func i H)) a -> Cl R a.
Proof.
intros Ix cond func R k Hexi Cfunc Hinc a.
induction_red a; intros ak Ha.
destruct (N_dec a); apply fold_Cl; [left|right].
(* 2: CN *)
  apply Hinc; auto.
  intros i ci.
  apply (destruct_Cl_CN _ _ c (Ha i ci)).
(* 1: N *)
  repeat split; auto.
  (* 2 *)
    destruct Hexi as [i ci].
    apply (Cv (Cok (C_Cl (Cfunc i ci)))); auto.
  (* 1 *)
    intros b Hred.
    apply IHa; auto; [apply term_lt_red with a; auto|].
    intros i ci.
    apply (Cred (C_Cl (Cfunc i ci))).
    exists a; auto.
Qed.

