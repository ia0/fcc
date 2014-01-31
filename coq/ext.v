Require Export FunctionalExtensionality.
Require Import ClassicalFacts.

(** This file defines the extensionality properties we use in the
formalization. They rely on two axioms of the Coq standard libraries:

- [prop_extensionality] for propositions and
- [functional_extensionality] for dependent products.

*)

Axiom propositional_extensionality : prop_extensionality.

Lemma and_extensionality : forall (P Q1 Q2 : Prop), (P -> Q1 = Q2) -> (P /\ Q1) = (P /\ Q2).
Proof.
intros; apply propositional_extensionality; split; intros [HP HQ].
rewrite <- (H HP); auto.
rewrite (H HP); auto.
Qed.

Lemma arrow_extensionality : forall (P Q1 Q2 : Prop), (P -> Q1 = Q2) -> (P -> Q1) = (P -> Q2).
Proof.
intros; apply propositional_extensionality; split; intros HQ HP.
rewrite <- (H HP); auto.
rewrite (H HP); auto.
Qed.

Lemma forall_extensionality : forall A (P Q : A -> Prop), P = Q -> (forall x, P x) = (forall x, Q x).
Proof. intros A P Q Heq; rewrite Heq; reflexivity. Qed.

Lemma exists_extensionality : forall A (P Q : A -> Prop), P = Q -> (exists x, P x) = (exists x, Q x).
Proof. intros A P Q Heq; rewrite Heq; reflexivity. Qed.
