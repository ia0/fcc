Require Import List.

Require Import mxx.
Require Import ext.
Require Import list.
Require Import Flanguage.
Require Import Fsemantics.
Require Import Ftypesystem.
Require Import Fsoundness.
Require Import Llanguage.
Require Import Ltypesystem.
Require Import typesystemextra.

(** * Soundness of the lambda version of System Fcc *)

(** ** Sound terms *)

(** We say that a term [a] is sound for at least [k] steps, written
[OKstep k a], if all its reduction paths smaller or equal to [k] steps
lead to a valid term.
*)
Fixpoint OKstep k a :=
  match k with
    | O => V a
    | S k => V a /\ forall b, red a b -> OKstep k b
  end.

(** We say that a term [a] is sound, written [OK a], if all its
reduction paths lead to a valid term. This definition is coinductive
to permit non-terminating terms to be sound.
*)
CoInductive OK a : Prop :=
| OK_ : V a -> (forall b, red a b -> OK b) -> OK a.

(** A term is sound if it is sound for all numbers of steps.
*)
Lemma OKOKstep : forall a, (forall k, OKstep k a) -> OK a.
Proof.
cofix.
intros a Ha.
apply OK_; [apply (Ha 0)|].
intros b Hred.
apply OKOKstep; intros k.
pose proof (Ha (1 + k)) as [_ Hrec]; auto.
Qed.

(** Reciprocally, if a term is sound, then it is sound for all numbers
of steps.
*)
Lemma OKstepOK : forall a, OK a -> forall k, OKstep k a.
Proof.
intros a Ha k.
generalize a Ha; clear a Ha.
induction k; intros a Ha; inversion Ha; auto.
split; auto.
Qed.

(** If a sound indexed term has more that [k] fuel (all its indices
are greater or equal to [k]), then its lambda version is sound for at
least [k] steps.
*)
Lemma term_ge_OK : forall k a, term_ge a k -> Fsemantics.OK a -> OKstep k (drop a).
Proof.
induction k; simpl; intros a ak OKa; [|split]; [apply V_drop; apply OKV; auto..|].
intros b Hred.
destruct (drop_red_exists _ _ _ ak Hred) as [? [? ?]]; subst.
apply IHk.
apply term_ge_red with (a := a); auto.
apply (Pred_OK); exists a; auto.
Qed.

(** ** Term judgments equivalence

The lambda and index versions of the term judgment are equivalent. If
a lambda term is well-typed, then all its annotated versions are
well-typed with the same typing. And reciprocally, if a indexed term
is well-typed, then its lambda version is well-typed with the same
typing. Only the first direction is necessary to transfer soundess
from the indexed version to the lambda version.
*)

Lemma jterm_aux : forall {v H G a t}, jterm v H G a t ->
  forall Fa, drop Fa = a -> Ftypesystem.jterm v H G Fa t.
Proof.
intros v H G a t HGat; induction HGat; intros Fa Faa;
destruct Fa; inversion Faa; eauto using Ftypesystem.jterm.
Qed.

Lemma jterm_aux_rev : forall v H G a t,
  Ftypesystem.jterm v H G a t -> jterm v H G (drop a) t.
Proof. intros v H G a t HGat; induction HGat; simpl; eauto using jterm. Qed.

(** ** Soundness *)

(** A well-typed term [a] is sound, if its type environment is
coherent and its term environment is well-formed. We also ask its type
to be of kind star, but this is redundant with extraction, hence the
[S] annotation.
*)
Lemma soundness_aux : forall b H G a t,
  jobj (b, vS) HNil (JH H) ->
  jobj (b, vS) H (JG G) ->
  jobj (b, vS) H (JT t KStar) ->
  jterm (b, vS) H G a t ->
  OK a.
Proof.
intros b H G a t HH HG Ht HGat; apply OKOKstep; intros k.
pose proof (jobj_sound HH) as [? [fH1 [? [? ?]]]].
dep H0.
pose proof (jobj_sound HG) as [fH2 [fG1 [? [? ?]]]]; clear HG.
pose proof (jobj_sound Ht) as [fH3 [ft1 [? [? [? [? ?]]]]]]; clear Ht.
pose proof (jterm_sound (jterm_aux HGat (kfill k a)
  (drop_kfill k a))) as [fH4 [fG2 [ft2 [? [? [? ?]]]]]]; clear HGat.
semobj_cstr.
repeat semobjeq H; rename fH4 into fH.
repeat semobjeq t; rename ft2 into ft.
repeat semobjeq G. rename fG2 into fG.
destruct (H2 nil eq_refl) as [h fHh]; clear H2.
pose proof (H4 h fHh); clear H4.
pose proof (H8 h fHh); clear H8.
pose proof (H12 h fHh); clear H12.
rewrite <- (drop_kfill k a).
apply term_ge_OK; [apply term_ge_kfill|].
apply (Pok_EJudg (fG h) (getstar (ft h))); auto.
apply (Forall_impl _ CEexp); auto.
apply C_CE.
destruct (ft h); try (exfalso; exact H1); exact H1.
Qed.

Lemma soundness : forall b H G a t,
  jobj (b, vP) HNil (JH H) ->
  jobj (b, vP) H (JG G) ->
  jterm (b, vP) H G a t ->
  OK a.
Proof.
intros b H G a t HH HG HGat.
assert (jobj (b, vF) HNil (Jwf HNil CTEnv)) as wHNilF by (apply WHNil; auto using cobj).
assert (jobj (b, vP) HNil (Jwf H CTEnv)) as wHP.
{ apply ((fun x => JH_extra x HH) I); auto using jobj_FP. }
assert (jobj (b, vF) HNil (Jwf H CTEnv)) as wHF by (apply jobj_PF; auto).
assert (jobj (b, vP) H (JT t KStar)) as jtP. { apply ((fun x => jterm_extra x HGat wHP HG) I). }
assert (jobj (b, vS) HNil (JH H)) by (apply jobj_FS; apply jobj_PF; auto).
assert (jobj (b, vS) H (JG G)) by (apply jobj_FS; apply jobj_PF; auto).
assert (jobj (b, vS) H (JT t KStar)) by (apply jobj_FS; apply jobj_PF; auto).
apply soundness_aux with b H G t; auto.
apply jterm_FS; apply jterm_PF; auto.
apply jobj_PF; auto.
Qed.

(** The list of Coq axioms we used:
[[
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
(forall x : A, f x = g x) -> f = g
ext.propositional_extensionality : ClassicalFacts.prop_extensionality
]]
*)
Print Assumptions soundness.
