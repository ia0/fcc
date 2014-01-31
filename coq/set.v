Require Import ext.

(** This file defines the notion of sets we will use in the
formalization.
*)

(** A [set] of elements of type [A] is a predicate in [Prop] over [A].
*)
Definition set {A} := A -> Prop.

(** We define intersections [Inter], complements [Cmp], unions
[Union], inclusions [Inc], and equalities [Eq].
*)
Definition Inter {A} (R S : @set A) : set := fun a => R a /\ S a.
Hint Unfold Inter.

Definition Cmp {A} (R : @set A) : set := fun a => ~ R a.
Hint Unfold Cmp.

Definition Union {A} (R S : @set A) : set := fun a => R a \/ S a.
Hint Unfold Union.

Definition Inc {A} (R S : @set A) := forall a, R a -> S a.
Hint Unfold Inc.

Definition Eq {A} (R S : @set A) := Inc R S /\ Inc S R.
Hint Unfold Eq.

(** We define the extensionality on [set]s which lifts the [set]
equality [Eq] to the equality of Coq.
*)
Lemma extEq : forall {A} (R S : @set A), Eq R S -> R = S.
Proof.
intros A R S [RS SR].
apply functional_extensionality; intros x.
apply propositional_extensionality; split; auto.
Qed.
