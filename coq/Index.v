(**

* Presentation of the formalization

** General notice

Some generated links do not point to the right place because of
ambiguities: several files define the same name. A typical example is
[term] which is defined in both [Flanguage_v] and [Llanguage_v]. The
documentation does not assume these links to be correct, but still
uses the syntax to enhance these names.

The links of the form [<name>_v] are unique and thus well-defined.
They point to an empty inductive at the beginning of the file named
[<name>.v].

** Quick pointers

A list of the files used in the formalization:
- [ext_v] helps for extensionality
- [set_v] helps for sets
- [minmax_v] helps for min and max arithmetic
- [list_v] helps for lists
- [mxx_v] defines the type system parametrization
- [Flanguage_v] defines the Indexed Calculus
- [Fnormalization_v] proves the strong normalization of the Indexed Calculus
- [Fsemantics_v] defines a semantics for the Indexed Calculus
- [Llanguage_v] defines the Lambda Calculus
- [typesystem_v] defines the erasable judgments of System Fcc
- [Ltypesystem_v] defines the computational judgment of System Fcc
- [Ftypesystem_v] is a copy of [Ltypesystem_v] with indices
- [typesystemextra_v] links the different versions
- [Fsoundness_v] proves the soundness of System Fcc with indices
- [Lsoundness_v] proves the soundness of System Fcc
- [Lsemantics_v] defines a normalizing semantics for the Lambda Calculus
- [Lnormalization_v] proves the strong normalization of System Fcc


** Excerpt from the manuscript

This formalization has been developed with Coq version 8.4pl2. It can
be found online at #<a
href="http://phd.ia0.fr/">http://phd.ia0.fr/</a>#. There is a
Makefile, so it suffices to run [make] to compile the Coq files or
[make html] to also build the html version.

The formalization merges ideas from strong normalization proofs of
System F and step-indexed techniques. The strong normalization proof
techniques is initially inspired from _A formalization of strong
normalization for simply-typed lambda-calculus and system F_ but
adapted for soundness proofs and step-indices. The step-indexed
techniques are inspired from _An indexed model of recursive types for
foundational proof-carrying code_ but modified for strong reduction.

The main differences between the version of System Fcc presented in
this chapter and its formalization in Coq are the use of de Bruijn
indices and the parametrization of the type system. Using de Bruijn
indices makes it a lot easier and cleaner to deal with binders. The
parametrization is necessary to state the results and for the
induction to go well.

We will now give a small glimpse of the Coq code for the reader to
find its way through the files, definitions, and lemma. Files prefixed
with the capital letter [F] refer to the indexed calculus: this letter
stands for fuel. Files prefixed with the capital letter [L] refer to
the lambda calculus. Files without a prefix letter are more general,
like [typesystem_v] which factorizes the type systems for both the
indexed calculus and the lambda calculus. We describe the files in
dependency order.

We first have a few independent files. The file [ext_v] defines the
extensionality axioms we use. Propositional and functional
extensionality are the only axioms used. The other extensionality
rules are lemmas. The file [set_v] defines a type for potentially
infinite sets as predicates in [Prop]. The file [minmax_v] defines the
tactic [minmax] to deal with indices. The file [list_v] defines useful
lemmas about lists, which we use for environments and mappings.

Finally, the file [mxx_v] defines the parametrization of the type
system using a value of type [Mode], which is the pair of a boolean
and a version. The boolean tells whether we allow recursive types or
not. The soundness proof does not constrain this boolean while the
normalization proof requires the boolean to be false. The version is
defined by the inductive [Version] and contains three possible values:
[vP], [vF], and [vS]. This manuscript corresponds to the [vP] version,
which is the natural presentation. The [vF] version contains
additional premises that are redundant by extraction but necessary for
the soundness induction. Finally, the [vS] version removes some
premises from the [vF] version which are required for extraction but
not for soundness. The proof of soundness is thus done in the [vS]
version. We define two helpers to tell whether a premise is required
for extraction with [mE] or for soundness with [mS]. Finally, the [mR]
helper tells which rules are about recursive types.

We can now define the indexed calculus in file [Flanguage_v]. We
define the inductive [term] for terms. All constructors of this
inductive are prefixed with a [nat] representing the index of the
node. We then define a few functions to traverse terms, from which we
define lifting of index predicates to term, and the [lift] and [subst]
functions for de Bruijn lifting and substitution. We then define the
reduction relation in the inductive [red]. We finally define errors in
[Err] and valid terms [V]. What follows is a list of lemmas about
lifting, substitutions, lowering, and other functions over indices.

We prove the strong normalization of the pure indexed calculus in file
[Fnormalization_v]. This file is quite simple to follow: we define a
[measure], prove that it strictly decreases with reduction in
[red_measure], and finally prove that reduction is well founded in
[wf_der].

We can now define a semantics for this indexed calculus in file
[Fsemantics_v]. We define the notion of interior in [Dec], the notion
of contraction in [Red], and the notion of expansion in [Exp]. Using
expansion, we can define the set of sound terms [OK]. We define
pretypes in [C] and types in [CE]. We define the closure of a set in
[Cl], in order to define the arrow operator [EArr], product operator
[EProd], and incoherent abstraction operator [EPi]. We show that these
operators preserve types in [CE_EArr], [CE_EProd], and [CE_EPi]. We
also define erasable types such as the coherent polymorphic type
[EFor], the top type [ETop], the bottom type [EBot], or recursive
types [EMu]. We then define the notions we need to show that recursive
types are equal to their unfolding. And we finally define the semantic
judgment [EJudg] and the semantic typing rules of the STLC, such as
[ELam_sem]. We also define a subtyping rule [ECoer_sem] and a
distributivity rule [Edistrib] which will be used together to prove
rule [JCoer].

Once that the indexed calculus is defined, we may define the lambda
calculus and the functions to go back and forth between them in file
[Llanguage_v]. The structure of this file is similar to [Flanguage_v]
with the difference that it now contains a [drop] and [kfill] function
to translate terms from one language to the other. It also contains
the key lemma [drop_red_exists] for the bisimulation between the
reduction relation of both languages.

Independently from the indexed calculus and the lambda calculus, we
can define the type part of System Fcc: everything but the term
judgment. This is done in [typesystem_v] and is actually shared by
both [Ftypesystem_v] and [Ltypesystem_v], which define the term
judgment for the indexed type system and lambda type system
respectively. The last two files are exactly the same up to indices.
All the syntax is gathered is a single Coq inductive, namely [obj].
This simplifies a lot the treatment of operations on the syntax, such
as lifting or substitution, which are defined only once. In order to
keep track of syntactical classes, we define a judgment [cobj] to
classify each object in its grammatical class. In the paper version,
we naturally assume that everything is syntactically well-formed,
while we have to state it explicitly in Coq.

We prove the weakening, substitution, and extraction lemmas in
[typesystemextra_v]. This file also contains the proof that the [vP]
and [vF] version are equivalent and that the [vS] version is a
consequence. This explains why the properties of the [vS] version also
hold for the [vP] version.

The proof that each judgment of the indexed type system is sound lies
in [Fsoundness_v]. We start by defining a notion of semantic objects
[sobj]. A semantic object is either a set of indexed terms, the unit
object, or a pair of objects. We then define the signature of the
interpretation of each syntactical class in [sem]. Kinds are
interpreted as sets of semantic objects, types as semantic objects,
propositions as indexed propositions, type environments as sets of
semantic environments (lists of semantics objects because we use de
Bruijn indices), coinduction environments as indexed propositions, and
finally term environments as semantic term environments (lists of
semantic types, when the syntactical environment is valid). All these
interpretation are parametrized by an surrounding semantic
environment. We define the interpretation function [semobj] as a
binary relation, but we show in [semobj_eq] that it behaves as a
function. We then prove semantic lifting and substitution properties.
And we finally prove the soundness of each judgment. The soundness of
[jfoo] is proved in [jfoo_sound].

We finally lift this soundness proof from the indexed type system to
the lambda type system in [Lsoundness_v]. We first define when a term
[a] is sound for a least [k] steps in [OKstep] and when it is sound
for all number of steps in [OK] by coinduction. We prove that these
two notions coincide. We then show how to transpose soundness from the
indexed calculus to the lambda calculus in [term_ge_OK]. We prove that
both type systems coincide and finally prove the soundness of System
Fcc in [soundness].

The Coq files [Lsemantics_v] and [Lnormalization_v] are similar to the
files [Fsemantics_v], [Fsoundness_v], and [Lsoundness_v] but deal with
the strong normalization result instead of the soundness result.

*)
