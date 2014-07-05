Require Import Omega.
Require Import List.
Require Import Equality.

Require Import mxx.
Require Import minmax.
Require Import ext.
Require Import set.
Require Import list.
Require Import Flanguage.
Require Import Fnormalization.
Require Import Fsemantics.
Require Import Ftypesystem.
Require Import typesystem.
Require Import typesystemextra.

(** * Soundness of the indexed version of System Fcc *)

(** ** Interpretation *)

(** We interpret objects as semantical objects [sobj]. They are
written [so] and contain sets [SSet R], the unit object [SUnit], and
pairs [SPair so1 so2].
*)
Inductive sobj :=
| SSet (R : set)
| SUnit
| SPair (so1 : sobj) (so2 : sobj)
.

(** Semantic environments are lists of semantic objects.
*)
Definition semenv := list sobj.

(** The interpretation of objects depends on their syntactical class.
We use the inductive [sem] to categorize their interpretation. They
are all parametrized by a semantical environment. Kinds are sets of
semantical objects. Types are semantical objects. Propositions are
indexed Coq propositions. Type environments are sets of semantic
environments. Proof environments are indexed Coq propositions. And
finally, term environments are lists of sets (of terms), those of
[Fsemantics_v].
*)
Inductive sem :=
| SKind : (semenv -> sobj -> Prop) -> sem
| SType : (semenv -> sobj) -> sem
| SProp : (semenv -> nat -> Prop) -> sem
| STEnv : (semenv -> semenv -> Prop) -> sem
| SPEnv : (semenv -> nat -> Prop) -> sem
| SAEnv : (semenv -> list set) -> sem
.

(** We define some helpers to define the interpretation of objects.
*)
Definition sstar f so :=
  match so with
    | SSet R => f R
    | SUnit => False
    | SPair _ _ => False
  end.

Definition sunit so :=
  match so with
    | SSet _ => False
    | SUnit => True
    | SPair _ _ => False
  end.

Definition sprod f1 f2 so :=
  match so with
    | SPair so1 so2 => f1 so1 /\ f2 so2
    | _ => f1 SUnit /\ f2 SUnit
  end.

Definition getstar so :=
  match so with
    | SSet R => R
    | _ => ETop
  end.

Definition lt2 f x y := SSet (f (getstar x) (getstar y)).

Definition sfst so :=
  match so with
    | SPair x _ => x
    | _ => SUnit
  end.

Definition ssnd so :=
  match so with
    | SPair _ y => y
    | _ => SUnit
  end.
Hint Unfold sstar sunit sprod getstar lt2 sfst snd.

(** *** Object interpretation *)

(** We write [semobj o so] when the object [o] is interpreted to [so].
We use a relation instead of a Coq function because only syntactically
well-formed objects have an interpretation. We show in [semobj_eq]
that this relation is actually a partial function.
*)
Inductive semobj : obj -> sem -> Prop :=
(* kinds *)
| semKStar : semobj KStar (SKind (fun _ => sstar CE))
| semKOne : semobj KOne (SKind (fun _ => sunit))
| semKProd : forall f1 f2 k1 k2,
  semobj k1 (SKind f1) ->
  semobj k2 (SKind f2) ->
  semobj (KProd k1 k2) (SKind (fun h => sprod (f1 h) (f2 h)))
| semKRes : forall p k fk fp,
  semobj k (SKind fk) ->
  semobj p (SProp fp) ->
  semobj (KRes k p) (SKind (fun h x => fk h x /\ forall k, fp (x :: h) k))
(* types *)
| semTVar : forall x,
  semobj (TVar x) (SType (fun h => nth x h SUnit))
| semTArr : forall t s ft fs,
  semobj t (SType ft) ->
  semobj s (SType fs) ->
  semobj (TArr t s) (SType (fun h => lt2 EArr (ft h) (fs h)))
| semTOne : semobj TOne (SType (fun h => SSet EOne))
| semTProd : forall t s ft fs,
  semobj t (SType ft) ->
  semobj s (SType fs) ->
  semobj (TProd t s) (SType (fun h => lt2 EProd (ft h) (fs h)))
| semTVoid : semobj TVoid (SType (fun h => SSet EVoid))
| semTSum : forall t s ft fs,
  semobj t (SType ft) ->
  semobj s (SType fs) ->
  semobj (TSum t s) (SType (fun h => lt2 ESum (ft h) (fs h)))
| semTFor : forall k t fk ft,
  semobj k (SKind fk) ->
  semobj t (SType ft) ->
  semobj (TFor k t) (SType (fun h => SSet (EFor sobj (fk h) (fun x _ => getstar (ft (x :: h))))))
| semTPi : forall k t fk ft,
  semobj k (SKind fk) ->
  semobj t (SType ft) ->
  semobj (TPi k t) (SType (fun h => SSet (EPi sobj (fk h) (fun x _ => getstar (ft (x :: h))))))
| semTMu : forall t ft,
  semobj t (SType ft) ->
  semobj (TMu t) (SType (fun h => SSet (EMu (fun x => getstar (ft (SSet x :: h))))))
| semTBot : semobj TBot (SType (fun _ => SSet EBot))
| semTTop : semobj TTop (SType (fun _ => SSet ETop))
| semTUnit : semobj TUnit (SType (fun _ => SUnit))
| semTPair : forall t1 t2 f1 f2,
  semobj t1 (SType f1) ->
  semobj t2 (SType f2) ->
  semobj (TPair t1 t2) (SType (fun h => SPair (f1 h) (f2 h)))
| semTFst : forall t ft,
  semobj t (SType ft) ->
  semobj (TFst t) (SType (fun h => sfst (ft h)))
| semTSnd : forall t ft,
  semobj t (SType ft) ->
  semobj (TSnd t) (SType (fun h => ssnd (ft h)))
(* props *)
| semPTrue : semobj PTrue (SProp (fun _ _ => True))
| semPAnd : forall p1 p2 f1 f2,
  semobj p1 (SProp f1) ->
  semobj p2 (SProp f2) ->
  semobj (PAnd p1 p2) (SProp (fun h k => f1 h k /\ f2 h k))
| semPCoer : forall H' t' t fH' ft ft',
  semobj H' (STEnv fH') ->
  semobj t' (SType ft') ->
  semobj t (SType ft) ->
  semobj (PCoer H' t' t) (SProp (fun h k => forall a, term_lt a k -> (forall h',
     fH' h h' -> getstar (ft' (h' ++ h)) a) -> getstar (ft h) a))
| semPExi : forall k fk,
  semobj k (SKind fk) ->
  semobj (PExi k) (SProp (fun h _ => exists x, fk h x))
| semPFor : forall k p fk fp,
  semobj k (SKind fk) ->
  semobj p (SProp fp) ->
  semobj (PFor k p) (SProp (fun h k => forall x, fk h x -> fp (x :: h) k))
(* tenvs *)
| semHNil : semobj HNil (STEnv (fun h h' => h' = nil))
| semHCons : forall H k fH fk,
  semobj H (STEnv fH) ->
  semobj k (SKind fk) ->
  semobj (HCons H k) (STEnv (fun h h'' => exists h' x, fH h h' /\ fk (h' ++ h) x /\ h'' = x :: h'))
(* penvs *)
| semYNil : semobj YNil (SPEnv (fun _ _ => True))
| semYCons : forall Y p fY fp,
  semobj Y (SPEnv fY) ->
  semobj p (SProp fp) ->
  semobj (YCons Y p) (SPEnv (fun h k => fY h k /\ fp h k))
(* aenvs *)
| semGNil : semobj GNil (SAEnv (fun _ => nil))
| semGCons : forall G t fG ft,
  semobj G (SAEnv fG) ->
  semobj t (SType ft) ->
  semobj (GCons G t) (SAEnv (fun h => getstar (ft h) :: fG h))
.

(** We use the [dep] tactic very often. It is actually a copy-paste of
[dependent destruction] of the [Equality] Coq library taking an
hypothesis as argument instead of an identifier.
*)
Tactic Notation "dep" hyp(H) :=
  do_depelim' ltac:(fun hyp => idtac) ltac:(fun hyp => do_case hyp) H.

(** The relation for the semantic interpretation of objects is
actually a partial function.
*)
Lemma semobj_eq : forall o s1,
  semobj o s1 -> forall s2, semobj o s2 -> s1 = s2.
Proof.
Ltac step :=
match goal with
  | |- ?x = ?x => reflexivity
  | Hx : forall _,  _ -> ?x = _
  , H1 : semobj _ ?x |- _ => clear H1
  | Hx : forall _, semobj ?k _ -> _
  , H1 : semobj ?k _ |- _ =>
    pose proof (Hx _ H1); clear Hx
  | H : SKind _ = SKind _ |- _ => dep H
  | H : SType _ = SType _ |- _ => dep H
  | H : SProp _ = SProp _ |- _ => dep H
  | H : STEnv _ = STEnv _ |- _ => dep H
  | H : SPEnv _ = SPEnv _ |- _ => dep H
  | H : SAEnv _ = SAEnv _ |- _ => dep H
end.
induction 1; intros s2 Hs; dep Hs; repeat step.
Qed.

(** This tactic is very useful. It simplifies the hypotheses by
removing and unifying redundant semantic interpretations.
*)
Ltac semobjeq o :=
  match goal with
    | H1 : semobj o _
    , H2 : semobj o _
      |- _ => let H := fresh "H" in
              pose proof (semobj_eq _ _ H1 _ H2) as H; clear H1; dep H
  end.

(** This tactic simplifies the hypotheses by destruction of the
semantic interpretation.
*)
Ltac semobj_cstr :=
  repeat match goal with
           | H : semobj KStar _ |- _ => dep H
           | H : semobj KOne _ |- _ => dep H
           | H : semobj (KProd _ _) _ |- _ => dep H
           | H : semobj (KRes _ _) _ |- _ => dep H
           | H : semobj (TVar _) _ |- _ => dep H
           | H : semobj (TArr _ _) _ |- _ => dep H
           | H : semobj TOne _ |- _ => dep H
           | H : semobj (TProd _ _) _ |- _ => dep H
           | H : semobj TVoid _ |- _ => dep H
           | H : semobj (TSum _ _) _ |- _ => dep H
           | H : semobj (TFor _ _) _ |- _ => dep H
           | H : semobj (TPi _ _) _ |- _ => dep H
           | H : semobj (TMu _) _ |- _ => dep H
           | H : semobj TBot _ |- _ => dep H
           | H : semobj TTop _ |- _ => dep H
           | H : semobj TUnit _ |- _ => dep H
           | H : semobj (TPair _ _) _ |- _ => dep H
           | H : semobj (TFst _) _ |- _ => dep H
           | H : semobj (TSnd _) _ |- _ => dep H
           | H : semobj PTrue _ |- _ => dep H
           | H : semobj (PAnd _ _) _ |- _ => dep H
           | H : semobj (PCoer _ _ _) _ |- _ => dep H
           | H : semobj (PExi _) _ |- _ => dep H
           | H : semobj (PFor _ _) _ |- _ => dep H
           | H : semobj HNil _ |- _ => dep H
           | H : semobj (HCons _ _) _ |- _ => dep H
           | H : semobj YNil _ |- _ => dep H
           | H : semobj (YCons _ _) _ |- _ => dep H
           | H : semobj GNil _ |- _ => dep H
           | H : semobj (GCons _ _) _ |- _ => dep H
         end.

(** *** Semantic lifting *)

(** We need a few helpers to define the semantic lifting lemmas. If an
environment has an interpretation (it is syntactically well-formed),
then its elements have an interpretation too. This lemma can be proved
with [cobj] and transfered to [semobj] if we show that [semobj] and
[cobj] are equivalent: an object is syntactically well-formed if it
has an interpretation and reciprocally.
*)
Lemma Ynth_prop :
  forall Y n p, Ynth Y n p ->
  forall fY, semobj Y (SPEnv fY) ->
  exists fp, semobj p (SProp fp).
Proof.
induction 1; intros.
dep H; exists fp; auto.
dep H0.
destruct (IHYnth fY0 H0_) as [fp0 ?].
exists fp0; auto.
Qed.

(** The semantic environment [deln d i h] removes [d] semantic objects
after [i] elemnts from the head of the semantic environment [h].
*)
Definition deln d := fix f i h : semenv :=
  match i with
    | O => skipn d h
    | S i =>
        match h with
          | nil => nil
          | cons x h => cons x (f i h)
        end
  end.

(** The [(d + x)]th element of [h] is the same as the [x]th element of
[deln d i h] if [x] is greater or equal to [i].
*)
Lemma nth_deln2 : forall d y i x h, i <= x ->
  nth (d + x) h y = nth x (deln d i h) y.
Proof.
induction i; simpl; intros.
(* -2: nil *)
  rewrite <- (firstn_skipn d h).
  rewrite app_nth2.
  (* +1 *)
    rewrite (firstn_skipn d h).
    rewrite firstn_length.
    destruct (le_gt_dec d (length h)).
    (* +1 *)
      rewrite min_l; [|auto].
      f_equal; omega.
    (* +0 *)
      rewrite min_r; [|omega].
      rewrite skipn_overflow; [|omega].
      rewrite nth_overflow; [|simpl; omega].
      destruct x; auto.
  (* +0 *)
    rewrite firstn_length.
    minmax.
(* -1: cons *)
  destruct x; [inversion H|].
  rewrite <- plus_n_Sm.
  destruct h; auto; simpl.
  apply IHi; omega.
Qed.

(** The [x]th element of [h] is the same as the [x]th element of
[deln d i h] if [x] is smaller than [i].
*)
Lemma nth_deln1 : forall d y i x h, i > x ->
  nth x h y = nth x (deln d i h) y.
induction i; simpl; intros; [inversion H|].
destruct h; auto; simpl.
destruct x; auto.
apply IHi; omega.
Qed.

Lemma app_deln_length : forall h2 h1, deln (length h1) 0 (h1 ++ h2) = h2.
Proof. induction h1; simpl; intros; auto. Qed.

Lemma app_deln2 : forall d h2 h1 i, i >= length h1 ->
  deln d i (h1 ++ h2) = h1 ++ deln d (i - length h1) h2.
Proof.
induction h1; simpl; intros;
[rewrite <- minus_n_O; reflexivity|].
destruct i; [inversion H|]; simpl.
f_equal.
apply IHh1.
omega.
Qed.

(** We link the [length] function on lists and the [Hlength] function
on type environments through the interpretation relation. The elements
of the interpretation of the type environment [H] have the length of
[H].
*)
Lemma stenv_length : forall H' fH', semobj H' (STEnv fH') ->
  forall h h', fH' h h' -> Hlength H' = length h'.
Proof.
intros H' fH' HfH'.
dependent induction HfH'; intros; subst; simpl; auto.
destruct H0 as [h0' [k' [? [? ?]]]]; subst; simpl.
f_equal.
apply IHHfH'1 with h; auto.
Qed.

(** The lifting of size [d] at level [i] of a semantic interpretation
simply calls the old interpretation with [deln d i h] instead of [h].
*)
Definition slift d i s :=
  match s with
    | SKind fk => SKind (fun h => fk (deln d i h))
    | SType ft => SType (fun h => ft (deln d i h))
    | SProp fp => SProp (fun h => fp (deln d i h))
    | STEnv fH => STEnv (fun h => fH (deln d i h))
    | SPEnv fY => SPEnv (fun h => fY (deln d i h))
    | SAEnv fG => SAEnv (fun h => fG (deln d i h))
  end.

(** If the object [o] is interpreted to [s] then, its lifted version
is interpreted to the lifted version of [s].
*)
Lemma semobj_lift : forall d o s, semobj o s ->
  forall i, semobj (lift d i o) (slift d i s).
Proof.
induction 1; simpl in *; intros; eauto using semobj.
(* 8: KRes *)
  pose proof (semKRes _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H1; auto.
(* 7: TVar *)
  subst_lift_var.
  (* +1 *)
    pose proof (semTVar (d + x)).
    match goal with
      | H1 : semobj _ (SType ?x) |- semobj _ (SType ?y) =>
        let H := fresh "H" in
        assert (x = y) as H; [|rewrite <- H; auto]
    end.
    apply functional_extensionality; intros h.
    rewrite <- nth_deln2; auto.
  (* +0 *)
    pose proof (semTVar x).
    match goal with
      | H1 : semobj _ (SType ?x) |- semobj _ (SType ?y) =>
        let H := fresh "H" in
        assert (x = y) as H; [|rewrite <- H; auto]
    end.
    apply functional_extensionality; intros h.
    rewrite <- nth_deln1; auto.
(* 6: TFor *)
  pose proof (semTFor _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H1; auto.
(* 5: TFor *)
  pose proof (semTPi _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H1; auto.
(* 4: TMu *)
  pose proof (semTMu _ _ (IHsemobj (1 + i))).
  simpl in H0; auto.
(* 3: PCoer *)
  pose proof (semPCoer _ _ _ _ _ _
    (IHsemobj1 i) (IHsemobj2 (Hlength H' + i)) (IHsemobj3 i)).
  simpl in H2.
  match goal with
    | H1 : semobj _ (SProp ?x) |- semobj _ (SProp ?y) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite <- H; auto]
  end.
  clear H0 H1 H2 IHsemobj1 IHsemobj2 IHsemobj3.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros k.
  apply forall_extensionality; apply functional_extensionality; intros a.
  apply arrow_extensionality; intros.
  match goal with
    | |- (?x -> _) = (?y -> _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  apply forall_extensionality; apply functional_extensionality; intros h'.
  apply arrow_extensionality; intros fHh'.
  repeat f_equal.
  rewrite (stenv_length _ _ H _ _ fHh').
  rewrite app_deln2; [|omega].
  repeat f_equal.
  omega.
(* 2: PFor *)
  pose proof (semPFor _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H1; auto.
(* 1: HCons *)
  pose proof (semHCons _ _ _ _ (IHsemobj1 i) (IHsemobj2 (Hlength H + i))).
  simpl in H2.
  match goal with
    | H1 : semobj _ (STEnv ?x) |- semobj _ (STEnv ?y) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite <- H; auto]
  end.
  clear H1 H2 IHsemobj1 IHsemobj2.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros h''.
  apply exists_extensionality; apply functional_extensionality; intros h'.
  apply exists_extensionality; apply functional_extensionality; intros x.
  apply and_extensionality; intros fHh.
  repeat f_equal.
  rewrite (stenv_length _ _ H0 _ _ fHh).
  rewrite app_deln2; [|omega].
  repeat f_equal.
  omega.
Qed.

(** Reciprocally, the interpretation of a lifted object is the lifting
of the interpretation of the unlifted object.
*)
Lemma semobj_lift_rev : forall d o ss i, semobj (lift d i o) ss ->
  exists s, semobj o s /\ ss = slift d i s.
Proof.
induction o; simpl; intros.
(* 30: KStar *)
  dep H.
  exists (SKind (fun _ => sstar CE)).
  split; eauto using semobj.
(* 29: KOne *)
  dep H.
  exists (SKind (fun _ => sunit)).
  split; eauto using semobj.
(* 28: KProd *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  exists (SKind (fun h => sprod (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 27: KRes *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  exists (SKind (fun h x => fi1 h x /\ forall k, fi2 (x :: h) k)).
  split; eauto using semobj.
(* 26: TVar *)
  unfold lift_idx in H.
  destruct (le_gt_dec i x).
  (* +1 *)
    dep H.
    exists (SType (fun h => nth x h SUnit)).
    split; eauto using semobj; simpl.
    f_equal.
    apply functional_extensionality; intros h.
    apply nth_deln2; auto.
  (* +1 *)
    dep H.
    exists (SType (fun h => nth x h SUnit)).
    split; eauto using semobj; simpl.
    f_equal.
    apply functional_extensionality; intros h.
    apply nth_deln1; auto.
(* 25: TArr *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename s into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => lt2 EArr (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 24: TOne *)
  semobj_cstr.
  eexists; split; eauto using semobj.
(* 23: TProd *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename s into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => lt2 EProd (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 22: TVoid *)
  semobj_cstr.
  eexists; split; eauto using semobj.
(* 21: TSum *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename s into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => lt2 ESum (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 20: TFor *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => SSet (EFor sobj (fi1 h) (fun x _ => getstar (fi2 (x :: h)))))).
  split; eauto using semobj.
(* 19: TPi *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => SSet (EPi sobj (fi1 h) (fun x _ => getstar (fi2 (x :: h)))))).
  split; eauto using semobj.
(* 18: TMu *)
  dep H.
  destruct (IHo _ _ H) as [s [? ?]].
  destruct s; simpl in H1; inversion H1.
  rename s into fi.
  exists (SType (fun h => SSet (EMu (fun x => getstar (fi (SSet x :: h)))))).
  split; eauto using semobj.
(* 17: TBot *)
  dep H.
  exists (SType (fun _ => SSet EBot)).
  split; eauto using semobj.
(* 16: TTop *)
  dep H.
  exists (SType (fun _ => SSet ETop)).
  split; eauto using semobj.
(* 15: TUnit *)
  dep H.
  exists (SType (fun _ => SUnit)).
  split; eauto using semobj.
(* 14: TPair *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename s into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  exists (SType (fun h => SPair (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 13: TFst *)
  dep H.
  destruct (IHo _ _ H) as [s [? ?]].
  destruct s; simpl in H1; inversion H1.
  rename s into fi.
  exists (SType (fun h => sfst (fi h))).
  split; eauto using semobj.
(* 12: TSnd *)
  dep H.
  destruct (IHo _ _ H) as [s [? ?]].
  destruct s; simpl in H1; inversion H1.
  rename s into fi.
  exists (SType (fun h => ssnd (fi h))).
  split; eauto using semobj.
(* 11: PTrue *)
  dep H.
  exists (SProp (fun _ _ => True)).
  split; eauto using semobj.
(* 10: PAnd *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  exists (SProp (fun h k => fi1 h k /\ fi2 h k)).
  split; eauto using semobj.
(* 9: PCoer *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct (IHo3 _ _ H1) as [s3 [? ?]].
  destruct s1; simpl in H3; inversion H3.
  rename P into fi1.
  destruct s2; simpl in H5; inversion H5.
  rename s into fi2.
  destruct s3; simpl in H7; inversion H7.
  rename s into fi3.
  eexists.
  split; eauto using semobj; simpl.
  f_equal.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros k.
  apply forall_extensionality; apply functional_extensionality; intros a.
  apply arrow_extensionality; intros.
  match goal with
    | |- (?x -> _) = (?y -> _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  apply forall_extensionality; apply functional_extensionality; intros h'.
  apply arrow_extensionality; intros fHh'.
  repeat f_equal.
  rewrite (stenv_length _ _ H2 _ _ fHh').
  rewrite app_deln2; [|omega].
  repeat f_equal.
  omega.
(* 8: PExi *)
  dep H.
  destruct (IHo _ _ H) as [s1 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  eexists; split; eauto using semobj.
(* 7: PFor *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  eexists; split; eauto using semobj.
(* 6: HNil *)
  dep H.
  exists (STEnv (fun h h' => h' = nil)).
  split; eauto using semobj.
(* 5: HCons *)
  dep H.
  destruct (IHo1 _ _ H0) as [s1 [? ?]].
  destruct (IHo2 _ _ H1) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  exists (STEnv (fun h h'' => exists h' x, fi1 h h' /\ fi2 (h' ++ h) x /\ h'' = x :: h')).
  split; eauto using semobj; simpl.
  f_equal.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros h''.
  apply exists_extensionality; apply functional_extensionality; intros h'.
  apply exists_extensionality; apply functional_extensionality; intros x0.
  apply and_extensionality; intros.
  match goal with
    | |- (?x /\ _) = (?y /\ _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  repeat f_equal.
  rewrite (stenv_length _ _ H _ _ H5).
  rewrite app_deln2; [|omega].
  repeat f_equal.
  omega.
(* 4: YNil *)
  dep H.
  eexists.
  split; eauto using semobj.
(* 3: YCons *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename P into fi2.
  eexists.
  split; eauto using semobj.
(* 2: GNil *)
  dep H.
  eexists.
  split; eauto using semobj.
(* 1: GCons *)
  dep H.
  destruct (IHo1 _ _ H) as [s1 [? ?]].
  destruct (IHo2 _ _ H0) as [s2 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename l into fi1.
  destruct s2; simpl in H4; inversion H4.
  rename s into fi2.
  eexists.
  split; eauto using semobj.
Qed.

(** This tactic replace in the hypotheses the interpretation of lifted
objects by their unlifted version.
*)
Ltac semobj_unlift :=
  repeat match goal with
           | H : semobj (lift _ _ _) _ |- _ =>
             let x := fresh "x" in
             let Hx := fresh "H" in
             destruct (semobj_lift_rev _ _ _ _ H) as [x [? Hx]]; clear H;
             destruct x; simpl in Hx; inversion Hx; clear Hx; subst
         end.

(** *** Semantic substitution *)

(** The semantic environment [insn x i h] adds the semantic object [x
(skipn i h)] at position [i] from the head of the semantic environment
[h]. If [h] is too short, some [SUnit] are added to reach length [i].
*)
Definition insn x := fix f i h : semenv :=
  match i with
    | O => x h :: h
    | S i =>
        match h with
          | nil => cons SUnit (f i nil)
          | cons x h => cons x (f i h)
        end
  end.

(** The [i] first elements of the semantic environment [insn x i h]
are the same as those of [h].
*)
Lemma nth_insn1 : forall i n, n < i ->
  forall x h, nth n h SUnit = nth n (insn x i h) SUnit.
Proof.
induction i; simpl; intros; [inversion H|].
destruct n; destruct h; simpl; auto.
(* +1 *)
  rewrite <- IHi; [|omega].
  destruct n; reflexivity.
(* +0 *)
  apply IHi.
  omega.
Qed.

(** The [i]th element of [insn x i h] is [x (skipn i h)].
*)
Lemma nth_insneq : forall i x h y,
  x (skipn i h) = nth i (insn x i h) y.
Proof.
induction i; simpl; intros; auto.
destruct h; simpl; auto.
clear IHi.
induction i; simpl; auto.
Qed.

Lemma nth_insn2_nil : forall i n, i <= n ->
  forall x, SUnit = nth (1 + n) (insn x i nil) SUnit.
Proof.
induction i; simpl; intros.
destruct n; auto.
destruct n; [inversion H|].
apply IHi.
omega.
Qed.

(** The elements after the position [i] of are those after the
position [1 + i] of [insn x i h].
*)
Lemma nth_insn2 : forall i n, i <= n ->
  forall x h, nth n h SUnit = nth (1 + n) (insn x i h) SUnit.
Proof.
induction i; simpl; intros; auto.
destruct n; simpl; [inversion H|].
destruct h; simpl.
apply nth_insn2_nil; omega.
apply IHi; omega.
Qed.

Lemma nth_insn2_minus : forall n i, i < n ->
  forall x h, nth (n - 1) h SUnit = nth n (insn x i h) SUnit.
Proof.
induction n; simpl; intros; [inversion H|].
rewrite <- minus_n_O.
apply nth_insn2; omega.
Qed.

Lemma app_insn2 : forall d h2 h1 i, i >= length h1 ->
  insn d i (h1 ++ h2) = h1 ++ insn d (i - length h1) h2.
Proof.
induction h1; simpl; intros;
[rewrite <- minus_n_O; reflexivity|].
destruct i; [inversion H|]; simpl.
f_equal.
apply IHh1.
omega.
Qed.

(** The substitution by [t] at level [i] of a semantic interpretation
simply calls the old interpretation with [insn t i h] instead of [h].
*)
Definition ssubst t i s :=
  match s with
    | SKind fk => SKind (fun h => fk (insn t i h))
    | SType ft => SType (fun h => ft (insn t i h))
    | SProp fp => SProp (fun h => fp (insn t i h))
    | STEnv fH => STEnv (fun h => fH (insn t i h))
    | SPEnv fY => SPEnv (fun h => fY (insn t i h))
    | SAEnv fY => SAEnv (fun h => fY (insn t i h))
  end.

(** If the type [t] is interpreted to [x] and the object [o] is
interpreted to [s] then, the substituted object [subst t i o] is
interpreted to [ssubst x i s].
*)
Lemma semobj_subst : forall t x, semobj t (SType x) ->
  forall o s, semobj o s ->
  forall i, semobj (subst t i o) (ssubst x i s).
Proof.
induction 2; simpl in *; intros; eauto using semobj.
(* 8: KRes *)
  pose proof (semKRes _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H0; auto.
(* 7: TVar *)
  subst_lift_var.
  (* +2 *)
    pose proof (semTVar x0).
    match goal with
      | H1 : semobj _ (SType ?x) |- semobj _ (SType ?y) =>
        let H := fresh "H" in
        assert (x = y) as H; [|rewrite <- H; auto]
    end.
    apply functional_extensionality; intros h.
    apply nth_insn1; auto.
  (* +1 *)
    subst.
    pose proof (semobj_lift i _ _ H 0).
    simpl in H0.
    match goal with
      | H1 : semobj _ (SType ?x) |- semobj _ (SType ?y) =>
        let H := fresh "H" in
        assert (x = y) as H; [|rewrite <- H; auto]
    end.
    apply functional_extensionality; intros h.
    apply nth_insneq.
  (* +0 *)
    pose proof (semTVar (x0 - 1)).
    match goal with
      | H1 : semobj _ (SType ?x) |- semobj _ (SType ?y) =>
        let H := fresh "H" in
        assert (x = y) as H; [|rewrite <- H; auto]
    end.
    apply functional_extensionality; intros h.
    apply nth_insn2_minus; auto.
(* 6: TFor *)
  pose proof (semTFor _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H0; auto.
(* 5: TPi *)
  pose proof (semTPi _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H0; auto.
(* 4: TMu *)
  pose proof (semTMu _ _ (IHsemobj (1 + i))).
  simpl in H0; auto.
(* 3: PCoer *)
  pose proof (semPCoer _ _ _ _ _ _
    (IHsemobj1 i) (IHsemobj2 (Hlength H' + i)) (IHsemobj3 i)).
  simpl in H0.
  match goal with
    | H1 : semobj _ (SProp ?x) |- semobj _ (SProp ?y) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite <- H; auto]
  end.
  clear H0 H0_0 H0_1 IHsemobj1 IHsemobj2 IHsemobj3.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros k.
  apply forall_extensionality; apply functional_extensionality; intros a.
  apply arrow_extensionality; intros.
  match goal with
    | |- (?x -> _) = (?y -> _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  apply forall_extensionality; apply functional_extensionality; intros h'.
  apply arrow_extensionality; intros fHh'.
  repeat f_equal.
  rewrite (stenv_length _ _ H0_ _ _ fHh').
  rewrite app_insn2; [|omega].
  repeat f_equal.
  omega.
(* 2: PFor *)
  pose proof (semPFor _ _ _ _ (IHsemobj1 i) (IHsemobj2 (1 + i))).
  simpl in H0; auto.
(* 1: HCons *)
  pose proof (semHCons _ _ _ _ (IHsemobj1 i) (IHsemobj2 (Hlength H0 + i))).
  simpl in H1.
  match goal with
    | H1 : semobj _ (STEnv ?x) |- semobj _ (STEnv ?y) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite <- H; auto]
  end.
  clear H1 H0_0 IHsemobj1 IHsemobj2.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros h''.
  apply exists_extensionality; apply functional_extensionality; intros h'.
  apply exists_extensionality; apply functional_extensionality; intros x0.
  apply and_extensionality; intros fHh.
  repeat f_equal.
  rewrite (stenv_length _ _ H0_ _ _ fHh).
  rewrite app_insn2; [|omega].
  repeat f_equal.
  omega.
Qed.

(** Reciprocally, the interpretation of a substituted object is the
substitution of the interpretation of the unsubstituted object.
*)
Lemma semobj_subst_rev : forall t x, semobj t (SType x) ->
  forall o i ss, semobj (subst t i o) ss ->
  exists s, semobj o s /\ ss = ssubst x i s.
Proof.
induction o; simpl; intros.
(* 30: KStar *)
  dep H0.
  exists (SKind (fun _ => sstar CE)).
  split; eauto using semobj.
(* 29: KOne *)
  dep H0.
  exists (SKind (fun _ => sunit)).
  split; eauto using semobj.
(* 28: KProd *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  exists (SKind (fun h => sprod (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 27: KRes *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  exists (SKind (fun h x => fi1 h x /\ forall k, fi2 (x :: h) k)).
  split; eauto using semobj.
(* 26: TVar *)
  unfold subst_idx in H0.
  destruct (lt_eq_lt_dec x0 i) as [[?|?]|?].
  (* +2 *)
    dep H0.
    exists (SType (fun h => nth x0 h SUnit)).
    split; eauto using semobj; simpl.
    f_equal.
    apply functional_extensionality; intros h.
    apply nth_insn1; auto.
  (* +1 *)
    subst.
    exists (SType (fun h => nth i h SUnit)).
    split; eauto using semobj; simpl.
    pose proof (semobj_lift i _ _ H 0).
    semobjeq (lift i 0 t).
    simpl.
    f_equal.
    apply functional_extensionality; intros h.
    apply nth_insneq.
  (* +0 *)
    dep H0.
    exists (SType (fun h => nth x0 h SUnit)).
    split; eauto using semobj; simpl.
    f_equal.
    apply functional_extensionality; intros h.
    apply nth_insn2_minus; auto.
(* 25: TArr *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename s into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => lt2 EArr (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 24: TOne *)
  semobj_cstr.
  eexists; split; eauto using semobj.
(* 23: TProd *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename s into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => lt2 EProd (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 22: TVoid *)
  semobj_cstr.
  eexists; split; eauto using semobj.
(* 21: TSum *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename s into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => lt2 ESum (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 20: TFor *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => SSet (EFor sobj (fi1 h) (fun x _ => getstar (fi2 (x :: h)))))).
  split; eauto using semobj.
(* 19: TPi *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => SSet (EPi sobj (fi1 h) (fun x _ => getstar (fi2 (x :: h)))))).
  split; eauto using semobj.
(* 18: TMu *)
  dep H0.
  destruct (IHo _ _ H0) as [s [? ?]].
  destruct s; simpl in H2; inversion H2.
  rename s into fi.
  exists (SType (fun h => SSet (EMu (fun x => getstar (fi (SSet x :: h)))))).
  split; eauto using semobj.
(* 17: TBot *)
  dep H0.
  exists (SType (fun _ => SSet EBot)).
  split; eauto using semobj.
(* 16: TTop *)
  dep H0.
  exists (SType (fun _ => SSet ETop)).
  split; eauto using semobj.
(* 15: TUnit *)
  dep H0.
  exists (SType (fun _ => SUnit)).
  split; eauto using semobj.
(* 14: TPair *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename s into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  exists (SType (fun h => SPair (fi1 h) (fi2 h))).
  split; eauto using semobj.
(* 13: TFst *)
  dep H0.
  destruct (IHo _ _ H0) as [s [? ?]].
  destruct s; simpl in H2; inversion H2.
  rename s into fi.
  exists (SType (fun h => sfst (fi h))).
  split; eauto using semobj.
(* 12: TSnd *)
  dep H0.
  destruct (IHo _ _ H0) as [s [? ?]].
  destruct s; simpl in H2; inversion H2.
  rename s into fi.
  exists (SType (fun h => ssnd (fi h))).
  split; eauto using semobj.
(* 11: PTrue *)
  dep H0.
  exists (SProp (fun _ _ => True)).
  split; eauto using semobj.
(* 10: PAnd *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  exists (SProp (fun h k => fi1 h k /\ fi2 h k)).
  split; eauto using semobj.
(* 9: PCoer *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct (IHo3 _ _ H0_1) as [s3 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  destruct s3; simpl in H5; inversion H5.
  rename s into fi3.
  eexists.
  split; eauto using semobj; simpl.
  f_equal.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros k.
  apply forall_extensionality; apply functional_extensionality; intros a.
  apply arrow_extensionality; intros.
  match goal with
    | |- (?x -> _) = (?y -> _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  apply forall_extensionality; apply functional_extensionality; intros h'.
  apply arrow_extensionality; intros fHh'.
  repeat f_equal.
  rewrite (stenv_length _ _ H0 _ _ fHh').
  rewrite app_insn2; [|omega].
  repeat f_equal.
  omega.
(* 8: PExi *)
  dep H0.
  destruct (IHo _ _ H0) as [s1 [? ?]].
  destruct s1; simpl in H2; inversion H2.
  rename P into fi1.
  eexists; split; eauto using semobj.
(* 7: PFor *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  eexists; split; eauto using semobj.
(* 6: HNil *)
  dep H0.
  exists (STEnv (fun h h' => h' = nil)).
  split; eauto using semobj.
(* 5: HCons *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  exists (STEnv (fun h h'' => exists h' x, fi1 h h' /\ fi2 (h' ++ h) x /\ h'' = x :: h')).
  split; eauto using semobj; simpl.
  f_equal.
  apply functional_extensionality; intros h.
  apply functional_extensionality; intros h''.
  apply exists_extensionality; apply functional_extensionality; intros h'.
  apply exists_extensionality; apply functional_extensionality; intros x0.
  apply and_extensionality; intros.
  match goal with
    | |- (?x /\ _) = (?y /\ _) =>
      let H := fresh "H" in
      assert (x = y) as H; [|rewrite H; reflexivity]
  end.
  repeat f_equal.
  rewrite (stenv_length _ _ H0 _ _ H4).
  rewrite app_insn2; [|omega].
  repeat f_equal.
  omega.
(* 4: YNil *)
  dep H0.
  eexists.
  split; eauto using semobj.
(* 3: YCons *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename P into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename P into fi2.
  eexists.
  split; eauto using semobj.
(* 2: GNil *)
  dep H0.
  eexists.
  split; eauto using semobj.
(* 1: GCons *)
  dep H0.
  destruct (IHo1 _ _ H0_) as [s1 [? ?]].
  destruct (IHo2 _ _ H0_0) as [s2 [? ?]].
  destruct s1; simpl in H1; inversion H1.
  rename l into fi1.
  destruct s2; simpl in H3; inversion H3.
  rename s into fi2.
  eexists.
  split; eauto using semobj.
Qed.

Ltac semobj_unsubst :=
  repeat match goal with
           | H1 : semobj ?s _ , H2 : semobj (subst ?s _ _) _ |- _ =>
             let x := fresh "x" in
             let Hx := fresh "H" in
             destruct (semobj_subst_rev _ _ H1 _ _ _ H2) as [x [? Hx]]; clear H2;
             destruct x; simpl in Hx; inversion Hx; clear Hx; subst
         end.

(** ** Soundness

We need a few helpers to prove the soundness lemmas.
*)

(** Lemmas [Hnth_mem] and [Ynth_mem] give us the semantic
interpretation of [Hnth] and [Ynth]. If an element is in an
environment for which the interpretation holds, then the
interpretation of the element holds.
*)
Lemma Hnth_mem : forall {H a k}, Hnth H a k ->
  forall {fH fk h}, semobj H (STEnv fH) -> semobj k (SKind fk) ->
  fH nil h -> fk (deln (1 + a) 0 h) (nth a h SUnit).
Proof.
induction 1; intros.
(* 2: *)
  dep H0.
  destruct H2 as [? [? [? [? ?]]]]; subst; simpl.
  rewrite app_nil_r in H2.
  semobjeq k; auto.
(* 1: *)
  dep H1.
  destruct H3 as [? [? [? [? ?]]]]; subst; simpl.
  rewrite app_nil_r in H3.
  pose proof (IHHnth _ _ _ H1_ H2 H1).
  auto.
Qed.

Lemma Ynth_mem : forall Y n p, Ynth Y n p ->
  forall H fH fY fp h, semobj H (STEnv fH) ->
  semobj Y (SPEnv fY) -> semobj p (SProp fp) ->
  fH nil h -> forall k, fY h k -> fp h k.
Proof.
induction 1; intros.
(* 2: *)
  dep H1.
  semobjeq p.
  destruct H4; auto.
(* 1: *)
  dep H2.
  destruct H5.
  apply (IHYnth _ _ _ _ _ H1 H2_ H3 H4 k H2).
Qed.

(** The interpretation of the concatenation of two proof environments
is equivalent to the interpretation of both environments.
*)
Lemma Yapp_semobj_rev : forall Y0 Y1 Y0Y1, Yapp Y0 Y1 Y0Y1 ->
  forall fY0Y1, semobj Y0Y1 (SPEnv fY0Y1) ->
  exists fY0 fY1, semobj Y0 (SPEnv fY0) /\ semobj Y1 (SPEnv fY1) /\
    forall h k, fY0Y1 h k <-> (fY0 h k /\ fY1 h k).
Proof.
induction 1; simpl; intros.
exists fY0Y1, (fun _ _ => True); repeat split; eauto using semobj.
intros [? _]; auto.
dep H0.
destruct (IHYapp _ H0_) as [fY0 [fY1 [? [? ?]]]].
exists fY0, (fun h k => fY1 h k /\ fp h k).
split; auto.
split; eauto using semobj.
intros h k.
pose proof (H2 h k) as [? ?].
clear H2 IHYapp H.
Ltac tmp :=
  match goal with
    | H : ?P |- ?P => exact H
    | H : _ /\ _ |- _ => destruct H
    | |- _ /\ _ => split
    | |- _ -> _ => intro
    | Hx : ?P -> _, H0 : ?P |- _ => pose proof (Hx H0); clear Hx
  end.
split; repeat tmp.
apply H4.
split; tmp.
Qed.

Lemma Happ_semobj : forall H2 H1 H2H1, Happ H2 H1 H2H1 ->
  forall fH2, semobj H2 (STEnv fH2) ->
  forall fH1, semobj H1 (STEnv fH1) ->
  exists fH2H1, semobj H2H1 (STEnv fH2H1).
Proof.
induction 1; simpl; intros; [exists fH2; auto|].
dep H3.
destruct (IHHapp fH2 H0 fH H3_) as [fH2H1 ?].
pose proof (semHCons H2H1 k1 fH2H1 fk H3 H3_0).
eexists; eauto.
Qed.

Lemma Happ_semobj_rev2 : forall H H' HH', Happ H H' HH' ->
  forall fHH', semobj HH' (STEnv fHH') ->
  exists fH', semobj H' (STEnv fH').
Proof.
induction 1; simpl; intros; [eexists; econstructor|].
dep H.
destruct (IHHapp _ H3).
eexists; econstructor; eauto.
Qed.

(** The interpretation of the concatenation of two type environments
contains the concatenation of the interpretations of these
environments.
*)
Lemma Happ_fH : forall H2 H3 H2H3, Happ H2 H3 H2H3 ->
  forall fH2, semobj H2 (STEnv fH2) ->
  forall fH3, semobj H3 (STEnv fH3) ->
  forall fH2H3, semobj H2H3 (STEnv fH2H3) ->
  forall h1 h2 h3, fH2 h1 h2 -> fH3 (h2 ++ h1) h3 -> fH2H3 h1 (h3 ++ h2).
Proof.
induction 1; simpl; intros.
dep H1; subst; simpl; semobjeq H; auto.
dep H3; dep H4.
semobjeq k1.
destruct H6 as [xh3 [x [? [? ?]]]]; subst.
rename H3 into H3', H1 into H3, fH into fH3, fH0 into fH2H1, fk0 into fk, k1 into k.
exists (xh3 ++ h2), x.
repeat split; auto.
apply IHHapp with fH2 fH3; auto.
rewrite <- app_assoc; auto.
Qed.

Lemma Happ_fH_nil : forall H2 H3 H2H3, Happ H2 H3 H2H3 ->
  forall fH2, semobj H2 (STEnv fH2) ->
  forall fH3, semobj H3 (STEnv fH3) ->
  forall fH2H3, semobj H2H3 (STEnv fH2H3) ->
  forall h2 h3, fH2 nil h2 -> fH3 h2 h3 -> fH2H3 nil (h3 ++ h2).
Proof.
intros.
apply (Happ_fH _ _ _ H _ H0 _ H1 _ H4 nil _ _ H5).
rewrite app_nil_r; auto.
Qed.

(** And reciprocally, the interpretation of the concatenation of two
type environments is a concatenation of the interpretations of these
environments.
*)
Lemma Happ_fH_rev : forall H H' HH', Happ H H' HH' ->
  forall fH, semobj H (STEnv fH) ->
  forall fH', semobj H' (STEnv fH') ->
  forall fHH', semobj HH' (STEnv fHH') ->
  forall hh', fHH' nil hh' ->
  exists h h', hh' = h' ++ h /\ fH nil h /\ fH' h h'.
Proof.
induction 1; simpl; intros.
(* 2: *)
  semobj_cstr.
  semobjeq H. rename fHH' into fH.
  rename hh' into h.
  exists h, nil; auto.
(* 1: *)
  rename H into HfH, k1 into k, H2 into H, H1 into H', H2H1 into HH'.
  semobj_cstr.
  semobjeq k. rename fk0 into fk.
  rename fH0 into fH', fH1 into fHH'.
  rename hh' into xhh'.
  destruct H5 as [hh' [x [? [? ?]]]]; subst.
  rewrite app_nil_r in H2.
  destruct (IHHapp _ HfH _ H3_ _ H4_ _ H1) as [h [h' [? [? ?]]]]; subst.
  exists h, (x :: h').
  repeat split; auto.
  exists h', x; auto.
Qed.

(** *** Well-foundness *)

(** We interpret well-foundness tokens as well-foundness levels (see
[WFj]).
*)
Definition srecsort rec :=
  match rec with
    | WF => 1
    | NE => 0
  end.

(** The interpretation of the well-foundness judgment [jrec a t rec]
is [srec a t rec] and simply says that the interpretation of the
functor [t] with respect to [a] is well-founded at the interpretation
of [rec].
*)
Definition srec a t rec :=
  forall ft, semobj t (SType ft) ->
  forall h' h, length h' = a ->
    WFj (srecsort rec) (fun X => getstar (ft (h' ++ SSet X :: h))).

Hint Unfold srecsort srec.

(** Soundness of the well-foundness judgment. *)
Lemma jrec_sound : forall {a t rec}, jrec a t rec -> srec a t rec.
Proof.
induction 1; intros ft Hft h' h ?; simpl.
(* 9: RECVar *)
  dep Hft.
  apply NE_id; intros R.
  rewrite app_nth2 by omega.
  replace (a - length h') with 0 by omega.
  reflexivity.
(* 8: RECArr *)
  dep Hft; simpl.
  rename ft0 into ft.
  apply WFj_WF.
  intros R k.
  rewrite WF_EArr.
  rewrite (IHjrec1 ft); auto.
  rewrite (IHjrec2 fs); auto.
  simpl; replace (k - 0) with k by omega.
  rewrite <- WF_EArr.
  reflexivity.
(* 7: RECProd *)
  dep Hft; simpl.
  rename ft0 into ft.
  apply WFj_WF.
  intros R k.
  rewrite WF_EProd.
  rewrite (IHjrec1 ft); auto.
  rewrite (IHjrec2 fs); auto.
  simpl; replace (k - 0) with k by omega.
  rewrite <- WF_EProd.
  reflexivity.
(* 6: RECSum *)
  dep Hft; simpl.
  rename ft0 into ft.
  apply WFj_WF.
  intros R k.
  rewrite WF_ESum.
  rewrite (IHjrec1 ft); auto.
  rewrite (IHjrec2 fs); auto.
  simpl; replace (k - 0) with k by omega.
  rewrite <- WF_ESum.
  reflexivity.
(* 5: RECFor *)
  dep Hft; simpl.
  rename ft0 into ft.
  subst k.
  pose proof (semobj_lift_rev _ _ _ _ Hft1) as [x [? Heq]].
  destruct x; simpl in Heq; inversion Heq; clear Heq; subst.
  rename P into fk'.
  apply WFj_EFor with sobj (fk' (h' ++ h)) (fun X x _ => getstar (ft (x :: h' ++ SSet X :: h))).
  (* +1 *)
    intros x fkx.
    replace (fun X => getstar (ft (x :: h' ++ SSet X :: h)))
      with (fun X => getstar (ft ((x :: h') ++ SSet X :: h))) by reflexivity.
    apply IHjrec; auto.
  (* +0 *)
    intros X.
    apply functional_extensionality_dep; intros a.
    apply and_extensionality; intros OKa.
    apply forall_extensionality.
    apply functional_extensionality_dep; intros x.
    match goal with
      | |- (?R -> _) = (?S -> _) => replace R with S; [reflexivity|]
    end.
    rewrite app_deln2; auto.
    replace (length h' - length h') with 0 by omega.
    reflexivity.
(* 4: RECPi *)
  dep Hft; simpl.
  rename ft0 into ft.
  subst k.
  pose proof (semobj_lift_rev _ _ _ _ Hft1) as [x [? Heq]].
  destruct x; simpl in Heq; inversion Heq; clear Heq; subst.
  rename P into fk'.
  apply WFj_WF.
  intros R k.
  assert (forall x, deln 1 (length h') (h' ++ x :: h) = h' ++ h) as Hr.
  (* begin assert *)
    intros x.
    rewrite app_deln2; auto.
    replace (length h' - length h') with 0 by omega.
    reflexivity.
  (* end assert *)
  repeat rewrite Hr.
  rewrite WF_EPi.
  eapply eq_trans; [|rewrite WF_EPi; reflexivity].
  repeat f_equal.
  apply functional_extensionality_dep; intros x.
  apply functional_extensionality_dep; intros _.
  replace (x :: h' ++ SSet R :: h) with ((x :: h') ++ SSet R :: h) by reflexivity.
  rewrite (IHjrec ft); auto.
  simpl; replace (k - 0) with k by omega.
  reflexivity.
(* 3: RECMu *)
  dep Hft; simpl.
  rename ft0 into ft.
  apply WFj_Mu.
  (* +1 *)
    intros X.
    apply WFj_WF.
    apply (IHjrec1 ft Hft nil (h' ++ SSet X :: h)); auto.
  (* +0 *)
    intros Y.
    pose proof (IHjrec2 ft Hft (SSet Y :: h') h).
    simpl in H2; auto.
(* 2: RECwf *)
  subst t.
  pose proof (semobj_lift_rev _ _ _ _ Hft) as [x [? Heq]].
  destruct x; simpl in Heq; inversion Heq; clear Heq; subst.
  rename s into ft'.
  apply WF_CST; exists (getstar (ft' (h' ++ h))); intros R.
  rewrite app_deln2; auto.
  replace (length h' - length h') with 0 by omega.
  reflexivity.
(* 1: RECne *)
  apply WFj_dec with 1; auto.
Qed.

(** *** Semantic class *)

(** The interpretation of the syntactical well-formedness judgment
[cobj o c] is [semclass o c] and says that the object [o] has an
interpretation of class [c].
*)
Definition semclass o c :=
  match c with
    | CKind => exists fk, semobj o (SKind fk)
    | CType => exists ft, semobj o (SType ft)
    | CProp => exists fp, semobj o (SProp fp)
    | CTEnv => exists fH, semobj o (STEnv fH)
    | CPEnv => exists fY, semobj o (SPEnv fY)
    | CAEnv => exists fG, semobj o (SAEnv fG)
  end.
Hint Unfold semclass.

(** Soundness of the syntactical well-formedness judgment. *)
Lemma cobj_sound : forall {o c}, cobj o c -> semclass o c.
Proof.
induction 1; unfold semclass in *;
repeat match goal with
  | H : exists _, _ |- _ => destruct H
end; eexists; eauto using semobj.
Qed.

(** *** Equality *)

(** The interpretation of the equality judgment [jeq t s] is [seq t s]
and says that the interpretations of [t] and [s] are equal.
*)
Definition seq t s := forall x y, semobj t x -> semobj s y -> x = y.
Hint Unfold seq.

(** Soundness of the equality judgment. *)
Lemma jeq_sound : forall {t s c}, jeq t s c -> seq t s.
Proof.
induction 1; intros x y Hx Hy; try
(semobj_cstr; f_equal;
apply functional_extensionality; intros h;
repeat match goal with
  | IH : seq ?a ?b, Ha : semobj ?a _, Hb : semobj ?b _ |- _ =>
    pose proof (IH _ _ Ha Hb) as Heq; clear IH Ha Hb; inversion Heq; clear Heq; subst
end; reflexivity).
(* 5: EQeq *) semobjeq t; auto.
(* 4: EQsym *) rewrite (IHjeq y x); auto.
(* 3: EQtrans *)
  pose proof (jeq_class H) as [_ co2].
  pose proof (cobj_sound co2) as Ht2.
  destruct c; destruct Ht2 as [? Hc];
  rewrite (IHjeq1 _ _ Hx Hc); auto.
(* 2: EQTFstPair *)
  semobj_cstr.
  simpl. semobjeq t.
  reflexivity.
(* 1: EQTSndPair *)
  semobj_cstr.
  simpl. semobjeq s.
  reflexivity.
Qed.

(** *** Objects *)

(** The interpretation of the object judgment [jobj J] is [semjudg J].
This interpretation depends on [J] and they all occur under a semantic
environment in the interpretation of their type environment:
- [JK H k] says that [k] is inhabited
- [JT H t k] says that [t] is a member of [k]
- [JP H Y0 Y1 p] says that [p] holds at index [k] if [Y0] holds for
  indices smaller or equal to [k] and [Y1] holds for indices smaller
  than [k] (for all index [k])
- [JH H H'] says that [H'] is inhabited
- [JG H G] says that [G] contains types and not just sets.
*)
Definition semjudg H J :=
  match J with
    | JK k =>
      exists fH fk,
      semobj H (STEnv fH) /\
      semobj k (SKind fk) /\
      (forall h, fH nil h -> exists x, fk h x)
    | JT t k =>
      exists fH ft fk,
      semobj H (STEnv fH) /\
      semobj k (SKind fk) /\
      semobj t (SType ft) /\
      forall h, fH nil h -> fk h (ft h)
    | JP Y0 Y1 p =>
      exists fH fY0 fY1 fp,
      semobj H (STEnv fH) /\
      semobj Y0 (SPEnv fY0) /\
      semobj Y1 (SPEnv fY1) /\
      semobj p (SProp fp) /\
      forall h, fH nil h ->
      forall k, (forall j, j <= k -> fY0 h j) ->
                (forall j, j < k -> fY1 h j) -> fp h k
    | JC Y0 Y1 H' t' t =>
      exists fH fY0 fY1 fp,
      semobj H (STEnv fH) /\
      semobj Y0 (SPEnv fY0) /\
      semobj Y1 (SPEnv fY1) /\
      semobj (PCoer H' t' t) (SProp fp) /\
      forall h, fH nil h ->
      forall k, (forall j, j <= k -> fY0 h j) ->
                (forall j, j < k -> fY1 h j) -> fp h k
    | JH H' =>
      exists fH fH',
      semobj H (STEnv fH) /\
      semobj H' (STEnv fH') /\
      forall h, fH nil h -> exists h', fH' h h'
    | JG G =>
      exists fH fG,
      semobj H (STEnv fH) /\
      semobj G (SAEnv fG) /\
      forall h, fH nil h -> Forall CE (fG h)
    | Jwf _ _ => True
  end.
Hint Unfold semjudg.

Ltac semobjeq_rename o fo so :=
  repeat semobjeq o;
  match goal with
    | H : semobj o (_ fo) |- _ => rename H into so
    | H : semobj o (_ ?x) |- _ => rename H into so, x into fo
  end.

(** Soundness of the object judgment. *)
Lemma jobj_sound : forall {b H J}, jobj (b, vS) H J -> semjudg H J.
Proof.
induction 1; unfold semjudg in *; try exact I.
(* 49: JKexi *)
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? Cp]]]]]]]].
  semobj_cstr.
  exists fH, fk.
  repeat split; auto.
  intros h fHh.
  apply (Cp h fHh 0); auto.
(* 48: JTeq *)
  destruct IHjobj as [fH [ft [fk [sH [sk [st ?]]]]]].
  destruct (jeq_class H1) as [_ ck'].
  destruct (cobj_sound ck') as [fk' sk'].
  pose proof (jeq_sound H1 _ _ sk sk') as Heq; inversion Heq; clear Heq; subst.
  exists fH, ft, fk'; auto.
(* 47: JTVar *)
  destruct (cobj_sound H0) as [fH sH].
  pose proof (Hnth_cobj H1 H0) as ck.
  destruct (cobj_sound ck) as [fk sk].
  pose proof (semobj_lift (1 + a) _ _ sk 0).
  exists fH. do 2 eexists.
  repeat split; eauto using semobj.
  intros h fHh; simpl.
  exact (Hnth_mem H1 sH sk fHh).
(* 46: JTArr *)
  destruct IHjobj1 as [fH1 [ft [fk1 [? [? [? ?]]]]]].
  destruct IHjobj2 as [fH2 [fs [fk2 [? [? [? ?]]]]]].
  semobjeq H; rename fH2 into fH.
  pose proof semKStar as sKS; repeat semobjeq KStar; clear sKS.
  exists fH, (fun h => lt2 EArr (ft h) (fs h)), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  pose proof (H3 h fHh).
  pose proof (H7 h fHh).
  destruct (ft h); simpl in *; try (exfalso; assumption).
  destruct (fs h); simpl in *; try (exfalso; assumption).
  apply CE_EArr; apply C_CE; auto.
(* 45: TOne *)
  destruct (cobj_sound H0) as [fH sH].
  exists fH; do 2 eexists.
  repeat split; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EOne.
(* 44: JTProd *)
  destruct IHjobj1 as [fH1 [ft [fk1 [? [? [? ?]]]]]].
  destruct IHjobj2 as [fH2 [fs [fk2 [? [? [? ?]]]]]].
  semobjeq H; rename fH2 into fH.
  pose proof semKStar as sKS; repeat semobjeq KStar; clear sKS.
  exists fH, (fun h => lt2 EProd (ft h) (fs h)), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  pose proof (H3 h fHh).
  pose proof (H7 h fHh).
  destruct (ft h); simpl in *; try (exfalso; assumption).
  destruct (fs h); simpl in *; try (exfalso; assumption).
  apply CE_EProd; apply C_CE; auto.
(* 43: TVoid *)
  destruct (cobj_sound H0) as [fH sH].
  exists fH; do 2 eexists.
  repeat split; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EVoid.
(* 42: JTSum *)
  destruct IHjobj1 as [fH1 [ft [fk1 [? [? [? ?]]]]]].
  destruct IHjobj2 as [fH2 [fs [fk2 [? [? [? ?]]]]]].
  semobjeq H; rename fH2 into fH.
  pose proof semKStar as sKS; repeat semobjeq KStar; clear sKS.
  exists fH, (fun h => lt2 ESum (ft h) (fs h)), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  pose proof (H3 h fHh).
  pose proof (H7 h fHh).
  destruct (ft h); simpl in *; try (exfalso; assumption).
  destruct (fs h); simpl in *; try (exfalso; assumption).
  apply CE_ESum; apply C_CE; auto.
(* 41: JTFor *)
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  rename fH0 into fH.
  exists fH, (fun h => SSet (EFor sobj (fk h) (fun x _ => getstar (ft (x :: h))))), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EFor.
  intros x ?.
  apply_clear Ck (x :: h).
  assert_clear Ck c1.
  { exists h, x; rewrite app_nil_r; repeat split; auto. }
  destruct (ft (x :: h)); simpl in Ck; try (exfalso; assumption).
  exact Ck.
(* 40: JTPi *)
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename k fk sk.
  semobjeq_rename t ft st.
  exists fH, (fun h => SSet (EPi sobj (fk h) (fun x _ => getstar (ft (x :: h))))), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EPi.
  intros x fx.
  apply_clear Ck (x :: h).
  assert_clear Ck c1.
  { exists h, x; rewrite app_nil_r; repeat split; auto. }
  destruct (ft (x :: h)); simpl in Ck; try (exfalso; assumption).
  exact (C_CE Ck).
(* 39: JTMu *)
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  exists fH, (fun h => SSet (EMu (fun x => getstar (ft (SSet x :: h))))), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EMu.
  2: pose proof (jrec_sound H0 ft st nil h eq_refl).
  2: apply WFj_WF; auto.
  intros R x.
  apply_clear Ck (SSet R :: h).
  assert_clear Ck c1.
  { exists h, (SSet R); auto. }
  destruct (ft (SSet R :: h)); simpl in Ck; try (exfalso; assumption).
  exact Ck.
(* 38: JTBot *)
  destruct (cobj_sound H0) as [fH sH].
  exists fH, (fun _ => SSet EBot), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  apply CE_EBot.
(* 37: JTTop *)
  destruct (cobj_sound H0) as [fH sH]; clear H0.
  exists fH, (fun _ => SSet ETop), (fun _ => sstar CE).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl.
  apply CE_ETop.
(* 36: JTUnit *)
  destruct (cobj_sound H0) as [fH sH]; clear H0.
  exists fH, (fun _ => SUnit), (fun _ => sunit).
  split; [|split; [|split]]; eauto using semobj.
(* 35: JTPair *)
  destruct IHjobj1 as [fH1 [ft1 [fk1 [? [? [? C1]]]]]].
  destruct IHjobj2 as [fH2 [ft2 [fk2 [? [? [? C2]]]]]].
  semobjeq_rename H fH sH.
  exists fH, (fun h => SPair (ft1 h) (ft2 h)), (fun h => sprod (fk1 h) (fk2 h)).
  split; [|split; [|split]]; eauto using semobj.
(* 35bis: JTPairEta *)
  {
  destruct IHjobj1 as [fH1 [ft1 [fk1 [? [? [? C1]]]]]].
  destruct IHjobj2 as [fH2 [ft2 [fk2 [? [? [? C2]]]]]].
  semobjeq_rename H fH sH.
  inversion H2; clear H2; subst.
  inversion H5; clear H5; subst.
  semobjeq t.
  exists fH, (fun h => ft0 h), (fun h => sprod (fk1 h) (fk2 h)).
  repeat split;  eauto using semobj.
  intros.
  unfold sprod.
  remember (ft0 h) as obj.
  pose (C1 h H0) as C1'.
  pose (C2 h H0) as C2'.
  rewrite <- Heqobj in C1'.
  rewrite <- Heqobj in C2'.
  destruct obj; simpl in C1'; simpl in C2'; split; auto.
  }
  (* 34: JTFst *)
  {
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  exists fH, (fun h => sfst (ft h)), f1.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply_clear Ck h.
  apply_clear Ck fHh.
  destruct (ft h); destruct Ck; assumption.
  }
(* 33: JTSnd *)
  {
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  exists fH, (fun h => ssnd (ft h)), f2.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply_clear Ck h.
  apply_clear Ck fHh.
  destruct (ft h); destruct Ck; assumption.
  }
(* 32: JTPack *)
  destruct IHjobj1 as [fH1 [ft [fk [? [? [? Ck]]]]]].
  destruct IHjobj2 as [fH2 [fY0 [fY1 [fp [? [? [? [? Cp]]]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename k fk sk.
  semobjeq_rename t ft st.
  semobj_unsubst.
  semobjeq_rename p fp sp.
  exists fH, ft; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh; simpl; auto.
(* 31: JTUnpack *)
  destruct IHjobj as [fH [ft [fk [? [? [? Ck]]]]]].
  semobj_cstr.
  exists fH, ft, fk0.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  destruct (Ck h fHh); auto.
(* 30: JPeq *)
  pose proof (jeq_class H1) as [cp cp'].
  destruct (cobj_sound cp') as [fp' ?].
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? ?]]]]]]]].
  exists fH, fY0, fY1, fp.
  pose proof (jeq_sound H1 _ _ H8 H4) as Heq; inversion Heq; clear Heq; subst.
  auto.
(* 29: JPVar *)
  destruct (cobj_sound H0) as [fH ?]; clear H0.
  destruct (cobj_sound H1) as [fY0 ?]; clear H1.
  destruct (cobj_sound H2) as [fY1 ?]; clear H2.
  destruct (Ynth_prop Y0 n p H3 fY0 H0) as [fp ?].
  exists fH, fY0, fY1, fp.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh ? ? ?.
  apply (Ynth_mem Y0 n p H3 H fH fY0 fp h); auto.
(* 28: JPTrue *)
  destruct (cobj_sound H0) as [fH ?]; clear H0.
  destruct (cobj_sound H1) as [fY0 ?]; clear H1.
  destruct (cobj_sound H2) as [fY1 ?]; clear H2.
  exists fH, fY0, fY1, (fun _ _ => True).
  split; [|split; [|split]]; eauto using semobj.
(* 27: JPAndPair *)
  destruct IHjobj1 as [fH1 [fY01 [fY11 [fp1 [? [? [? [? ?]]]]]]]].
  destruct IHjobj2 as [fH2 [fY02 [fY12 [fp2 [? [? [? [? ?]]]]]]]].
  semobjeq H; rename fH2 into fH.
  semobjeq Y0; rename fY02 into fY0.
  semobjeq Y1; rename fY12 into fY1.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; auto.
(* 26: JPAndFst *)
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? ?]]]]]]]].
  dep H4.
  exists fH, fY0, fY1, f1.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh k fY0k fY1k.
  apply (H5 h fHh); auto.
(* 25: JPAndSnd *)
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? ?]]]]]]]].
  dep H4.
  exists fH, fY0, fY1, f2.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh k fY0k fY1k.
  apply (H5 h fHh); auto.
(* 24: JPExi *)
  destruct (cobj_sound H0) as [fY0 ?]; clear H0.
  destruct (cobj_sound H1) as [fY1 ?]; clear H1.
  destruct IHjobj as [fH [ft [fk [? [? [? ?]]]]]].
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh k0 fY0k fY1k; simpl.
  exists (ft h); auto.
(* 23: JPForIntro *)
  destruct IHjobj as [fH [? [? [fp [? [? [? [? ?]]]]]]]].
  semobj_cstr.
  semobj_unlift.
  rename P into fY1, P0 into fY0, fH0 into fH.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh k0 fY0k fY1k; simpl; intros x fkx.
  apply (H7 (x :: h)); auto.
  exists h, x; rewrite app_nil_r; auto.
(* 22: JPForElim *)
  destruct IHjobj1 as [fH1 [ft [fk [? [? [? ?]]]]]].
  destruct IHjobj2 as [fH2 [? [? [fp [? [? [? [? ?]]]]]]]].
  semobj_cstr.
  semobjeq H. rename fH2 into fH.
  semobjeq k. rename fk0 into fk.
  rename fp0 into fp, x0 into fY1, x into fY0.
  pose proof (semobj_subst _ _ H2 _ _ H7_0 0).
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh k0 fY0k fY1k; simpl.
  apply H8; auto.
(* 21: JPRes *)
  destruct (cobj_sound H0) as [fY0 ?]; clear H0.
  destruct (cobj_sound H1) as [fY1 ?]; clear H1.
  destruct IHjobj as [fH [ft [fk [? [? [? ?]]]]]].
  dep H4; rename fk0 into fk.
  pose proof (semobj_subst t ft H5 p (SProp fp) H4_0 0).
  simpl in H4.
  exists fH, fY0, fY1, (fun h : semenv => fp (ft h :: h)).
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh.
  destruct (H6 h fHh); clear H6.
  auto.
(* 20: JPFix *)
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? ?]]]]]]]].
  semobj_cstr.
  semobjeq p.
  rename fY into fY1.
  exists fH, fY0, fY1, fp.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh.
  pose proof (H8 h fHh); clear H8.
  match goal with
    |- forall k, ?P =>
      let H := fresh "H" in
      assert (forall n k, k < n -> P) as H; [|intros k; apply (H (1 + k) k); auto]
  end.
  induction n; intros; [exfalso; omega|].
  apply H6; auto.
  intros; split; auto.
  apply IHn; intros; [|apply H9|apply H10]; omega.
(* 19: JPCoer *)
  destruct IHjobj1 as [? [? [? [? [? [? [? [? Cp]]]]]]]].
  destruct IHjobj2 as [? [? [? [? [? [? Ck]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename Y0 fY0 sY0.
  semobjeq_rename Y1 fY1 sY1.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename t' ft' st'.
  semobjeq_rename t ft st.
  exists fH, fY0, fY1. eexists.
  repeat split; eauto using semobj.
(* 18: JCProp *)
  destruct IHjobj1 as [? [? [? [? [? [? [? [? Cp]]]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename Y0 fY0 sY0.
  semobjeq_rename Y1 fY1 sY1.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename t' ft' st'.
  semobjeq_rename t ft st.
  exists fH, fY0, fY1. eexists.
  repeat split; eauto using semobj.
(* 17: JCRefl *)
  destruct (cobj_sound H0) as [fH sH]; clear H0.
  destruct (cobj_sound H1) as [fY0 sY0]; clear H1.
  destruct (cobj_sound H2) as [fY1 sY1]; clear H2.
  destruct (cobj_sound H3) as [ft st]; clear H3.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  apply (Ha nil eq_refl).
(* 16: JCTrans *)
  destruct IHjobj1 as [fH1 [? [? [fp1 [? [? [? [? ?]]]]]]]].
  destruct IHjobj2 as [fH2 [fY0 [fY1 [fp2 [? [? [? [? ?]]]]]]]].
  semobj_cstr.
  repeat semobjeq H; rename fH2 into fH.
  semobjeq t2; rename ft'0 into ft2, ft0 into ft3.
  rename fH1 into fHH2, fH' into fH1, fH'0 into fH2.
  pose proof (semobj_lift (Hlength H2) _ _ H10 0).
  semobjeq (lift (Hlength H2) 0 Y0).
  pose proof (semobj_lift (Hlength H2) _ _ H11 0).
  semobjeq (lift (Hlength H2) 0 Y1).
  destruct (Happ_semobj H2 H1 _ H3 _ H12_ _ H7_) as [fH2H1 ?].
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh. simpl; intros.
  apply H13 with k; auto; intros h' fH2h.
  pose proof (Happ_fH_nil H H2 _ H0 _ H9 _ H12_ _ H4 h h' fHh fH2h) as fHH2h.
  pose proof (H8 (h' ++ h) fHH2h).
  rewrite (stenv_length _ _ H12_ _ _ fH2h) in *.
  rewrite (skipn_app_length _ h h') in *.
  apply H17 with k; auto.
  intros h'' fH1h.
  rewrite app_assoc.
  apply H16.
  apply (Happ_fH _ _ _ H3 _ H12_ _ H7_ _ H6 h h' h''); auto.
(* 15: JCWeak *)
  destruct IHjobj as [fH [fY0 [fY1 [fp [? [? [? [? ?]]]]]]]].
  dep H4.
  destruct (semobj_lift_rev _ _ _ _ H4_0) as [x [? Heq]].
  destruct x; simpl in Heq; inversion Heq; clear Heq.
  rename ft into fs, s0 into ft; subst ft'.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros.
  apply H5 with k; auto.
  intros h' fH'h.
  rewrite (stenv_length _ _ H4_ _ _ fH'h).
  rewrite skipn_app_length.
  apply (H9 nil eq_refl).
(* 14: JCArr *)
  rename H0 into aY0Y1, H1 into aHH'.
  destruct (H3 I) as [fH1 [fH' [? [? CH']]]].
  destruct (H5 I) as [fH2 [ft' [? [? [? [? Ct']]]]]].
  destruct (H7 I) as [fH3 [fs' [? [? [? [? Cs']]]]]].
  destruct IHjobj1 as [fH4 [fY01 [fY11 [fpt [? [? [? [? Cpt]]]]]]]].
  destruct IHjobj2 as [fH5 [fY02 [fY12 [fps [? [? [? [? Cps]]]]]]]].
  semobj_cstr.
  semobj_unlift.
  repeat match goal with H : jobj _ |- _ => clear H end.
  semobjeq_rename H fH sH.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename s' fs' ss'.
  semobjeq_rename t' ft' st'.
  semobjeq_rename t ft st.
  semobjeq_rename Y0Y1 fY0Y1 sY0Y1.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename s fs ss.
  destruct (Yapp_semobj_rev Y0 Y1 Y0Y1 aY0Y1 fY0Y1 sY0Y1) as [fY0 [fY1 [sY0 [sY1 eqY0Y1]]]].
  exists fH, fY0, fY1. eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  match type of Ha with
    forall h', ?cond -> EArr ?R ?S a => apply Cl_approx_For with semenv
      (fun h' => cond) (fun h' _ => PArr R S) k; auto
  end.
  (* +1 well-formedness *)
    intros h' fH'h.
    pose proof (Happ_fH_nil H H' HH' aHH' fH sH fH' sH' fHH' sHH' h h' fHh fH'h) as fHH'h.
    pose proof (Ct' (h' ++ h) fHH'h) as xCt'.
    pose proof (Cs' (h' ++ h) fHH'h) as xCs'.
    destruct (ft' (h' ++ h)); simpl in xCt'; try (exfalso; assumption).
    destruct (fs' (h' ++ h)); simpl in xCs'; try (exfalso; assumption).
    simpl; apply C_PArr; apply C_CE; auto.
  (* +0 inclusion *)
  clear a ak Ha.
  intros a ak Ha.
  destruct (CH' h fHh) as [wh' wfH'h].
  destruct (Ha wh' wfH'h) as [j [a' [Heq [Hok _]]]].
  exists j, a'; repeat split; auto.
  intros Hj b' Rb'.
  apply Cps with (k - 1); auto.
  (* +2 *)
    intros.
    apply eqY0Y1.
    split; [apply fY0j; omega|].
    destruct k; [exfalso; apply term_lt_0 with a; auto|].
    apply fY1j; omega.
  (* +1 *)
    subst a; destruct ak.
    apply unary_fuel_map_trivial.
    intros.
    destruct j; [inversion Hj|]; simpl.
    rewrite <- minus_n_O.
    apply le_trans with (1 + j).
    minmax.
    omega.
  (* +0 *)
  intros h' fH'h.
  destruct (Ha h' fH'h) as [k2 [a2' [Heq2 [_ Hsub]]]].
  rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
  apply Hsub; auto; clear Hsub.
  pose proof (Happ_fH_nil H H' HH' aHH' fH sH fH' sH' fHH' sHH' h h' fHh fH'h) as fHH'h.
  apply Cpt with (k - 1); auto.
  (* +2 *)
    intros.
    rewrite (stenv_length _ _ sH' _ _ fH'h).
    rewrite skipn_app_length.
    apply eqY0Y1.
    split; [apply fY0j; omega|].
    destruct k; [exfalso; apply term_lt_0 with a; auto|].
    apply fY1j; omega.
  (* +1 *)
    subst a; destruct ak.
    apply unary_fuel_map_trivial.
    intros.
    destruct j; [inversion Hj|]; simpl.
    rewrite <- minus_n_O.
    apply le_trans with (1 + j).
    minmax.
    omega.
  (* +0 *)
  intros h0 ?; subst h0.
  rewrite (stenv_length _ _ sH' _ _ fH'h).
  simpl; rewrite skipn_app_length.
  exact Rb'.
(* 13: JCProd *)
  rename H0 into aY0Y1, H1 into aHH'.
  destruct (H3 I) as [fH1 [fH' [? [? CH']]]].
  destruct (H5 I) as [fH2 [ft' [? [? [? [? Ct']]]]]].
  destruct (H7 I) as [fH3 [fs' [? [? [? [? Cs']]]]]].
  destruct IHjobj1 as [fH4 [fY01 [fY11 [fpt [? [? [? [? Cpt]]]]]]]].
  destruct IHjobj2 as [fH5 [fY02 [fY12 [fps [? [? [? [? Cps]]]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename Y0Y1 fY0Y1 sY0Y1.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename t' ft' st'.
  semobjeq_rename s' fs' ss'.
  repeat match goal with H : jobj _ |- _ => clear H end.
  destruct (Yapp_semobj_rev _ _ _ aY0Y1 _ sY0Y1) as [fY0 [fY1 [sY0 [sY1 eqY0Y1]]]].
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  match type of Ha with
    forall h', ?cond -> EProd ?R ?S a => apply Cl_approx_For with semenv
      (fun h' => cond) (fun h' _ => PProd R S) k; auto
  end.
  (* +1 well-formedness *)
    intros h' fH'h.
    pose proof (Happ_fH_nil _ _ _ aHH' _ sH _ sH' _ sHH' h h' fHh fH'h) as fHH'h.
    pose proof (Ct' (h' ++ h) fHH'h) as xCt'.
    pose proof (Cs' (h' ++ h) fHH'h) as xCs'.
    destruct (ft' (h' ++ h)); simpl in xCt'; try (exfalso; assumption).
    destruct (fs' (h' ++ h)); simpl in xCs'; try (exfalso; assumption).
    simpl; apply C_PProd; apply C_CE; auto.
  (* +0 inclusion *)
  clear a ak Ha.
  intros a ak Ha.
  destruct (CH' h fHh) as [wh' wfH'h].
  destruct (Ha wh' wfH'h) as [j [a' [b' [Heq [[Hoka Hokb] _]]]]].
  exists j, a', b'; repeat split; auto; rename H0 into Hj.
  (* +1 R *)
    apply Cpt with (k - 1); auto.
    (* +2 *)
      intros.
      apply eqY0Y1.
      split; [apply fY0j; omega|].
      destruct k; [exfalso; apply term_lt_0 with a; auto|].
      apply fY1j; omega.
    (* +1 *)
      subst a; destruct ak.
      apply unary_fuel_map_trivial.
      intros.
      destruct j; [inversion Hj|]; simpl.
      rewrite <- minus_n_O.
      apply le_trans with (1 + j).
      minmax.
      omega.
    (* +0 *)
    intros h' fH'h.
    destruct (Ha h' fH'h) as [k2 [a2' [b2' [Heq2 [_ Hproj]]]]].
    rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
    apply Hproj; auto.
  (* +0 S *)
    apply Cps with (k - 1); auto.
    (* +2 *)
      intros.
      apply eqY0Y1.
      split; [apply fY0j; omega|].
      destruct k; [exfalso; apply term_lt_0 with a; auto|].
      apply fY1j; omega.
    (* +1 *)
      subst a; destruct ak.
      apply unary_fuel_map_trivial.
      intros.
      destruct j; [inversion Hj|]; simpl.
      rewrite <- minus_n_O.
      apply le_trans with (1 + j).
      minmax.
      omega.
    (* +0 *)
    intros h' fH'h.
    destruct (Ha h' fH'h) as [k2 [a2' [b2' [Heq2 [_ Hproj]]]]].
    rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
    apply Hproj; auto.
(* 12: JCSum *)
  rename H0 into aY0Y1, H1 into aHH'.
  destruct (H3 I) as [fH1 [fH' [? [? CH']]]].
  destruct (H5 I) as [fH2 [ft' [? [? [? [? Ct']]]]]].
  destruct (H7 I) as [fH3 [fs' [? [? [? [? Cs']]]]]].
  destruct IHjobj1 as [fH4 [fY01 [fY11 [fpt [? [? [? [? Cpt]]]]]]]].
  destruct IHjobj2 as [fH5 [fY02 [fY12 [fps [? [? [? [? Cps]]]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename Y0Y1 fY0Y1 sY0Y1.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename t' ft' st'.
  semobjeq_rename s' fs' ss'.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  repeat match goal with H : jobj _ |- _ => clear H end.
  destruct (Yapp_semobj_rev _ _ _ aY0Y1 _ sY0Y1) as [fY0 [fY1 [sY0 [sY1 eqY0Y1]]]].
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  match type of Ha with
    forall h', ?cond -> ESum ?R ?S a => apply Cl_approx_For with semenv
      (fun h' => cond) (fun h' _ => PSum R S) k; auto
  end.
  (* +1 well-formedness *)
    intros h' fH'h.
    pose proof (Happ_fH_nil _ _ _ aHH' _ sH _ sH' _ sHH' h h' fHh fH'h) as fHH'h.
    pose proof (Ct' (h' ++ h) fHH'h) as xCt'.
    pose proof (Cs' (h' ++ h) fHH'h) as xCs'.
    destruct (ft' (h' ++ h)); simpl in xCt'; try (exfalso; assumption).
    destruct (fs' (h' ++ h)); simpl in xCs'; try (exfalso; assumption).
    simpl; apply C_PSum; apply C_CE; auto.
  (* +0 inclusion *)
  clear a ak Ha.
  intros a ak Ha.
  destruct (CH' h fHh) as [wh' wfH'h].
  destruct (Ha wh' wfH'h) as [j [a' [[Heq [Hok _]]|[Heq [Hok _]]]]];
  exists j, a'; [left|right]; repeat split; auto; intros Hj.
  (* +1 R *)
    apply Cpt with (k - 1); auto.
    (* +2 *)
      intros.
      apply eqY0Y1.
      split; [apply fY0j; omega|].
      destruct k; [exfalso; apply term_lt_0 with a; auto|].
      apply fY1j; omega.
    (* +1 *)
      subst a; destruct ak.
      apply unary_fuel_map_trivial.
      intros.
      destruct j; [inversion Hj|]; simpl.
      rewrite <- minus_n_O.
      apply le_trans with (1 + j).
      minmax.
      omega.
    (* +0 *)
    intros h' fH'h.
    destruct (Ha h' fH'h) as [k2 [a2' [[Heq2 [_ Hin]]|[Heq2 [_ Hin]]]]];
    rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
    apply Hin; auto.
  (* +0 S *)
    apply Cps with (k - 1); auto.
    (* +2 *)
      intros.
      apply eqY0Y1.
      split; [apply fY0j; omega|].
      destruct k; [exfalso; apply term_lt_0 with a; auto|].
      apply fY1j; omega.
    (* +1 *)
      subst a; destruct ak.
      apply unary_fuel_map_trivial.
      intros.
      destruct j; [inversion Hj|]; simpl.
      rewrite <- minus_n_O.
      apply le_trans with (1 + j).
      minmax.
      omega.
    (* +0 *)
    intros h' fH'h.
    destruct (Ha h' fH'h) as [k2 [a2' [[Heq2 [_ Hin]]|[Heq2 [_ Hin]]]]];
    rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
    apply Hin; auto.
(* 11: JCPi *)
  rename H0 into aY0Y1, H1 into aHH', H2 into aHaH'.
  destruct IHjobj1 as [fH1 [fH' [? [? CH']]]].
  destruct (H6 I) as [fH2 [ft' [fk [? [? [? Ct']]]]]].
  destruct IHjobj2 as [fH3 [fs' [fk' [? [? [? Cs']]]]]].
  destruct IHjobj3 as [fH4 [fY0 [fY1 [fp [? [? [? [? Cp]]]]]]]].
  semobj_cstr.
  semobj_unsubst.
  semobj_unlift.
  repeat match goal with H : jobj _ |- _ => clear H end.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename H fH sH.
  semobjeq_rename k' fk' sk'.
  semobjeq_rename k fk sk.
  semobjeq_rename t' ft' st'.
  semobjeq_rename t ft st.
  semobjeq_rename Y0Y1 fY0Y1 sY0Y1.
  semobjeq_rename HaH' fHaH' sHaH'.
  semobjeq_rename s' fs' ss'.
  destruct (Yapp_semobj_rev _ _ _ aY0Y1 _ sY0Y1) as [fY0 [fY1 [sY0 [sY1 eqY0Y1]]]].
  exists fH, fY0, fY1. eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k0 fY0j fY1j a ak Ha.
  match type of Ha with
    forall h', ?condh' -> EPi ?Ix ?cond ?func a => apply Cl_approx_For
      with semenv (fun h' => condh') (fun h' _ => PPi Ix cond func) k0; auto
  end.
  (* +1 well-formedness *)
    intros h' fH'h.
    apply C_PPi; intros.
    apply C_CE.
    assert (sstar CE (ft' (i :: h' ++ h))).
    (* begin assert *)
      apply Ct'.
      exists (h' ++ h), i; rewrite app_nil_r.
      repeat split; auto.
      apply (Happ_fH_nil _ _ _ aHH' _ sH _ sH' _ sHH'); auto.
    (* end assert *)
    destruct (ft' (i :: h' ++ h)); try (exfalso; assumption).
    assumption.
  (* +0 inclusion *)
  clear a ak Ha.
  intros a ak Ha.
  destruct (CH' h fHh) as [wh' wfH'h].
  destruct (Ha wh' wfH'h) as [j [a' [Heq _]]].
  exists j, a'; repeat split; auto.
  intros Hj x fkx.
  apply Cp with (k0 - 1); auto.
  (* +3 *)
    exists h, x; rewrite app_nil_r; auto.
  (* +2 *)
    intros.
    apply eqY0Y1.
    split; [apply fY0j; omega|].
    destruct k0; [exfalso; apply term_lt_0 with a; auto|].
    apply fY1j; omega.
  (* +1 *)
    subst a; destruct ak.
    apply unary_fuel_map_trivial.
    intros.
    destruct j; [inversion Hj|]; simpl.
    rewrite <- minus_n_O.
    apply le_trans with (1 + j).
    minmax.
    omega.
  (* +0 *)
  intros h' fH'h.
  destruct (Ha h' fH'h) as [k2 [a2' [Heq2 Hpi]]].
  rewrite Heq in Heq2; inversion Heq2; subst k2 a2'.
  pose proof (Cs' (h' ++ x :: h)) as xCs'.
  rewrite (stenv_length _ _ sH' _ _ fH'h) in *.
  rewrite app_deln2 in *; try omega.
  replace (length h' - length h') with 0 in * by omega; simpl in *.
  apply Hpi; auto; clear Hpi.
  apply xCs'.
  pose proof (semHCons H k fH fk sH sk) as sHk.
  pose proof (semobj_lift 1 _ _ sH' 0) as xsH'.
  apply (Happ_fH_nil _ _ _ aHaH' _ sHk _ xsH'); auto.
  exists h, x; rewrite app_nil_r; auto.
(* 10: JCGen *)
  destruct (cobj_sound H0) as [fY0 sY0]; clear H0.
  destruct (cobj_sound H1) as [fY1 sY1]; clear H1.
  destruct IHjobj as [fH [fk [? [? Ck]]]].
  destruct (H5 I) as [fH1 [ft [fk1 [? [? [? Ct]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename k fk sk.
  exists fH, fY0, fY1. eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k0 fY0j fY1j a ak Ha.
  split.
  (* +1 *)
    destruct (Ck h fHh) as [x fx].
    assert (sstar CE (ft (x :: h))) as xCt.
    { apply (Ct (x :: h)).
      exists h, x.
      rewrite app_nil_r; auto. }
    assert (getstar (ft (x :: h)) a) as xHa.
    { apply (Ha (x :: nil)).
      exists nil, x; auto. }
    destruct (ft (x :: h)); try (exfalso; assumption).
    simpl in xCt, xHa.
    apply (CEok xCt); auto.
  (* +0 *)
  intros x fx.
  apply (Ha (x :: nil)).
  exists nil, x; auto.
(* 9: JCInst *)
  destruct (cobj_sound H0) as [fY0 sY0]; clear H0.
  destruct (cobj_sound H1) as [fY1 sY1]; clear H1.
  destruct (H4 I) as [fH1 [ft [? [? [? [? Ct]]]]]].
  destruct IHjobj as [fH2 [fs [fk [? [? [? Cs]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename k fk sk.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  (* +1 *)
    apply semPCoer; eauto using semobj.
    apply (semobj_subst s fs ss t (SType ft) st 0).
  (* +0 *)
  intros h fHh; simpl; intros k0 fY0j fY1j a ak Ha.
  apply (proj2 (Ha nil eq_refl) (fs h)).
  simpl; auto.
(* 8: JCUnfold *)
  destruct (cobj_sound H1) as [fY0 sY0]; clear H1.
  destruct (cobj_sound H2) as [fY1 sY1]; clear H2.
  destruct (H6 I) as [fH [ft [fk [? [? [? Ct]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  (* +1 *)
    apply semPCoer; eauto using semobj.
    apply (semobj_subst _ _ (semTMu t ft st) t (SType ft) st 0).
  (* +0 *)
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  pose proof (Ha nil eq_refl) as xHa; clear Ha; rename xHa into Ha.
  simpl in *.
  match type of Ha with
    EMu ?func a => remember func as F
  end.
  match goal with
    |- ?P a => replace P with (F (EMu F)) by (subst F; reflexivity)
  end.
  apply (Mu_unfold F); auto.
  apply WFj_WF.
  subst F.
  apply (jrec_sound (H4 I) ft st nil h eq_refl).
(* 7: JCFold *)
  destruct (cobj_sound H0) as [fY0 sY0]; clear H0.
  destruct (cobj_sound H1) as [fY1 sY1]; clear H1.
  destruct IHjobj as [fH [ft [fk [? [? [? Ct]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  (* +1 *)
    apply semPCoer; eauto using semobj.
    apply (semobj_subst _ _ (semTMu t ft st) t (SType ft) st 0).
  (* +0 *)
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  pose proof (Ha nil eq_refl) as xHa; clear Ha; rename xHa into Ha.
  simpl in *.
  match goal with
    |- EMu ?func a => remember func as F
  end.
  match type of Ha with
    ?P a => replace P with (F (EMu F)) in Ha by (subst F; reflexivity)
  end.
  apply (Mu_fold F); auto.
  apply WFj_WF.
  subst F.
  apply (jrec_sound H2 ft st nil h eq_refl).
(* 6: JCTop *)
  destruct (cobj_sound H1) as [fY0 sY0]; clear H1.
  destruct (cobj_sound H2) as [fY1 sY1]; clear H2.
  destruct (H5 I) as [fH [ft [fk [? [? [? Ct]]]]]].
  semobj_cstr.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  pose proof (Ha nil eq_refl) as xHa; clear Ha; rename xHa into Ha.
  simpl in Ha.
  apply fold_Cl; left.
  pose proof (Ct h fHh) as xCt.
  destruct (ft h); try (exfalso; assumption).
  simpl in *.
  exists R; split; auto.
(* 5: JCBot *)
  destruct (cobj_sound H0) as [fY0 sY0]; clear H0.
  destruct (cobj_sound H1) as [fY1 sY1]; clear H1.
  destruct IHjobj as [fH [ft [fk [? [? [? Ct]]]]]].
  semobj_cstr.
  exists fH, fY0, fY1; eexists.
  split; [|split; [|split; [|split]]]; eauto using semobj.
  intros h fHh; simpl; intros k fY0j fY1j a ak Ha.
  pose proof (Ha nil eq_refl) as xHa; clear Ha; rename xHa into Ha.
  pose proof (Ct h fHh) as xCt.
  destruct (ft h); try (exfalso; assumption).
  simpl in *.
  apply Ha; auto.
(* 4: JHNil *)
  destruct (cobj_sound H0) as [fH sH]; clear H0.
  exists fH. eexists.
  split; [|split]; eauto using semobj.
(* 3: JHCons *)
  destruct IHjobj1 as [fH [fH' [? [? CH']]]].
  destruct IHjobj2 as [fHH' [fk [? [? Ck]]]].
  exists fH. eexists.
  split; [|split]; eauto using semobj.
  intros h fHh; simpl.
  destruct (CH' h fHh) as [h' fH'h].
  destruct (Ck (h' ++ h)) as [x fx].
  apply (Happ_fH_nil H H' HH') with fH fH'; auto.
  exists (x :: h'), h', x; auto.
(* 2: JGNil *)
  destruct (cobj_sound H0) as [fH sH]; clear H0.
  exists fH. eexists.
  split; [|split]; eauto using semobj.
  intros h fHh; constructor.
(* 1: JGCons *)
  destruct IHjobj1 as [fH1 [fG [? [? CG]]]].
  destruct IHjobj2 as [fH2 [ft [? [? [? [? Ct]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  exists fH. eexists.
  split; [|split]; eauto using semobj.
  intros h fHh; constructor; auto.
  pose proof (Ct h fHh) as xCt.
  destruct (ft h); try (exfalso; assumption).
  assumption.
Qed.

(** *** Terms *)

(** The interpretation of the term judgment [jterm H G a t] is [sterm
H G a t] and says that for all semantic environment of [H], the term
[a] is in the semantic judgment of [G] and [t].
*)
Definition sterm H G a t :=
  exists fH fG ft, semobj H (STEnv fH) /\ semobj G (SAEnv fG) /\ semobj t (SType ft) /\
  forall h, fH nil h ->
  EJudg (fG h) (getstar (ft h)) a.
Hint Unfold sterm.

Lemma Gnth_type :
  forall G n t, Gnth G n t ->
  forall fG, semobj G (SAEnv fG) ->
  exists ft, semobj t (SType ft) /\ forall h, nth n (fG h) ETop = getstar (ft h).
Proof.
induction 1; intros.
(* 2: *)
  dep H; exists ft; auto.
(* 1: *)
dep H0.
destruct (IHGnth fG0 H0_) as [ft0 ?].
exists ft0; auto.
Qed.

(** Soundness of the term judgment. *)
Lemma jterm_sound : forall {b H G a t}, jterm (b, vS) H G a t -> sterm H G a t.
Proof.
intros b H G a t HGat; induction HGat.
(* 14: JVar *)
  pose proof (cobj_sound H0) as [fG sG]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH [ft1 [? [sH [? [? Ct1]]]]]]; clear H1.
  semobj_cstr.
  destruct (Gnth_type _ _ _ H2 _ sG) as [ft2 [st2 Ct2]].
  semobjeq_rename t ft st.
  exists fH, fG, ft.
  split; [|split; [|split]]; auto.
  intros h fHh.
  apply EVar_sem; auto.
  apply C_CE.
  pose proof (Ct1 h fHh) as Ct.
  destruct (ft h); try (exfalso; assumption).
  assumption.
(* 13: JLam *)
  destruct IHHGat as [fH1 [fG [fs1 [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH2 [fs2 [? [? [? [? Cs]]]]]]; clear H0.
  pose proof (jobj_sound H1) as [fH3 [ft2 [? [? [? [? Ct]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply ELam_sem; auto.
  (* +1 *)
    apply CEexp.
    pose proof (Ct h fHh) as xCt.
    destruct (ft h); try (exfalso; exact xCt).
    exact xCt.
  (* +0 *)
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs).
    apply C_CE.
    exact xCs.
(* 12: JApp *)
  destruct IHHGat1 as [fH1 [fG1 [fts [? [? [? Ca]]]]]].
  destruct IHHGat2 as [fH2 [fG2 [ft1 [? [? [? Cb]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH3 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH4 [fs [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  simpl in Ca.
  apply EApp_sem with (getstar (ft h)); auto.
  (* +1 *)
    pose proof (Ct h fHh) as xCt.
    destruct (ft h); try (exfalso; exact xCt).
    apply C_CE.
    exact xCt.
  (* +0 *)
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs).
    exact xCs.
(* 11: JUnit *)
  destruct (cobj_sound H0) as [fH sH].
  destruct (cobj_sound H1) as [fG sG].
  exists fH, fG; eexists.
  repeat split; eauto using semobj.
  intros h fHh.
  apply EUnit_sem.
(* 10: JPair *)
  destruct IHHGat1 as [fH1 [fG1 [ft1 [? [? [? Ca]]]]]].
  destruct IHHGat2 as [fH2 [fG2 [fs1 [? [? [? Cb]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH3 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH4 [fs2 [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply EPair_sem; auto.
  (* +1 *)
    apply C_CE.
    pose proof (Ct h fHh) as xCt.
    destruct (ft h); try (exfalso; exact xCt); exact xCt.
  (* +0 *)
    apply C_CE.
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 9: JFst *)
  destruct IHHGat as [fH1 [fG [fts [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH3 [fs2 [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  simpl in Ca.
  apply EFst_sem with (getstar (fs h)); auto.
  (* +1 *)
    pose proof (Ct h fHh) as xCt.
    destruct (ft h); try (exfalso; exact xCt); exact xCt.
  (* +0 *)
    apply C_CE.
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 8: JSnd *)
  destruct IHHGat as [fH1 [fG [fts [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH3 [fs2 [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  simpl in Ca.
  apply ESnd_sem with (getstar (ft h)); auto.
  (* +1 *)
    apply C_CE.
    pose proof (Ct h fHh) as xCt.
    destruct (ft h); try (exfalso; exact xCt); exact xCt.
  (* +0 *)
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 7: JAbsurd *)
  destruct IHHGat as [? [? [? [? [? [? Ca]]]]]].
  pose proof (jobj_sound H0) as [? [? [? [? [? [? Cs]]]]]].
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename G fG sG.
  semobjeq_rename s fs ss.
  exists fH, fG, fs.
  repeat split; auto.
  intros h fHh.
  apply EAbsurd_sem; auto.
  pose proof (Cs h fHh) as xCs.
  destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 6: JInl *)
  destruct IHHGat as [fH1 [fG [fts [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound H1) as [fH3 [fs2 [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply EInl_sem; auto.
  apply C_CE.
  pose proof (Ct h fHh) as xCt.
  destruct (ft h); try (exfalso; exact xCt); exact xCt.
(* 5: JInr *)
  destruct IHHGat as [fH1 [fG [fts [? [? [? Ca]]]]]].
  pose proof (jobj_sound H0) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH3 [fs2 [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply EInr_sem; auto.
  apply C_CE.
  pose proof (Cs h fHh) as xCs.
  destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 4: JMatch *)
  destruct IHHGat1 as [fH1 [fG1 [ftlr [? [? [? Ca]]]]]].
  destruct IHHGat2 as [fH2 [fG2 [fs1 [? [? [? Cbl]]]]]].
  destruct IHHGat3 as [fH3 [fG3 [fs2 [? [? [? Cbr]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH4 [ftl [? [? [? [? Ctl]]]]]]; clear H0.
  pose proof (jobj_sound (H1 I)) as [fH5 [ftr [? [? [? [? Ctr]]]]]]; clear H1.
  pose proof (jobj_sound (H2 I)) as [fH6 [fs [? [? [? [? Cs]]]]]]; clear H2.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename tl ftl stl.
  semobjeq_rename tr ftr str.
  semobjeq_rename s fs ss.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  simpl in Ca.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply EMatch_sem with (Rl := getstar (ftl h)) (Rr := getstar (ftr h)); auto.
  (* +2 *)
    pose proof (Ctl h fHh) as xCtl.
    destruct (ftl h); try (exfalso; exact xCtl); exact xCtl.
  (* +1 *)
    pose proof (Ctr h fHh) as xCtr.
    destruct (ftr h); try (exfalso; exact xCtr); exact xCtr.
  (* +0 *)
    pose proof (Cs h fHh) as xCs.
    destruct (fs h); try (exfalso; exact xCs); exact xCs.
(* 3: JGen *)
  destruct IHHGat as [fH1 [fG [ft1 [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H1 I)) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H1.
  semobj_cstr.
  semobj_unlift.
  semobjeq_rename H fH sH.
  semobjeq_rename k' fk' sk'.
  semobjeq_rename t ft st.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply EGen_sem; intros.
  (* +1 *)
    apply C_CE.
    assert (sstar CE (ft (i :: h))) as xCt.
    (* begin assert *)
      apply Ct.
      exists h, i; repeat split; auto.
      rewrite app_nil_r; auto.
    (* end assert *)
    destruct (ft (i :: h)); try (exfalso; exact xCt); exact xCt.
  (* +0 *)
  pose proof (Ca (i :: h)) as xCa.
  apply xCa.
  exists h, i; repeat split; auto.
  rewrite app_nil_r; auto.
(* 2: JInst *)
  destruct IHHGat as [fH1 [fG [ft1 [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H0 I)) as [fH2 [ft2 [? [? [? [? Ct]]]]]]; clear H0.
  pose proof (jobj_sound H1) as [fH3 [fs [? [? [? [? Cs]]]]]]; clear H1.
  semobj_cstr.
  semobjeq_rename H fH sH.
  semobjeq_rename k' fk' sk'.
  semobjeq_rename t ft st.
  semobjeq_rename s fs ss.
  exists fH, fG; eexists.
  pose proof (semobj_subst s fs ss t (SType ft) st 0).
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  simpl in Ca; pose proof (Ca h fHh) as xCa; clear Ca; rename xCa into Ca.
  apply (EInst_sem sobj (fk' h) (fun x _ => getstar (ft (x :: h)))); auto.
  intros.
  assert (sstar CE (ft (i :: h))) as xCt.
  (* begin assert *)
    apply Ct.
    exists h, i; repeat split; auto.
    rewrite app_nil_r; auto.
  (* end assert *)
  destruct (ft (i :: h)); try (exfalso; exact xCt); exact xCt.
(* 1: JCoer *)
  destruct IHHGat as [fH1 [fG [ft1 [? [? [? Ca]]]]]].
  pose proof (jobj_sound (H1 I)) as [fH2 [fH' [? [? CH']]]]; clear H1.
  pose proof (jobj_sound (H2 I)) as [fH3 [ft2 [? [? [? [? Ct]]]]]]; clear H2.
  pose proof (jobj_sound H3) as [fH4 [fY0 [fY1 [fp [? [? [? [? Cp]]]]]]]]; clear H3.
  semobj_cstr.
  semobj_unlift.
  semobjeq_rename HH' fHH' sHH'.
  semobjeq_rename H' fH' sH'.
  semobjeq_rename H fH sH.
  semobjeq_rename s fs ss.
  semobjeq_rename t ft st.
  semobjeq_rename G fG sG.
  exists fH, fG; eexists.
  split; [|split; [|split]]; eauto using semobj.
  intros h fHh.
  apply ECoer_sem with (For semenv (fH' h) (fun h' _ => getstar (ft (h' ++ h)))).
  (* +1 *)
    intros b0 Hb0.
    destruct (term_lt_exists b0) as [k bk].
    apply Cp with k; auto.
  (* +0 *)
    apply Edistrib; auto.
    (* +1 *)
      intros h' fH'h.
      pose proof (Happ_fH_nil H H' HH' H0 fH sH fH' sH' fHH' sHH' h h' fHh fH'h) as fHH'h.
      pose proof (Ct (h' ++ h) fHH'h) as xCt.
      destruct (ft (h' ++ h)); try (exfalso; exact xCt); exact xCt.
    (* +0 *)
    intros h' fH'h.
    pose proof (Happ_fH_nil H H' HH' H0 fH sH fH' sH' fHH' sHH' h h' fHh fH'h) as fHH'h.
    pose proof (Ca (h' ++ h) fHH'h) as Ha.
    rewrite (stenv_length H' fH' sH' h h' fH'h) in Ha.
    rewrite skipn_app_length in Ha; auto.
Qed.
