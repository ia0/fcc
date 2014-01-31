Require Import Omega.
Require Import Min.
Require Import List.

Require Import ext.
Require Import set.
Require Import minmax.
Require Import Llanguage.

(** * Semantics of the Lambda Calculus *)

(** ** Definition of types *)

(** *** Set properties *)

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

(** Head normal forms are stable by contraction.
*)
Lemma RedCN : Inc (Red CN) CN.
Proof. intros b [a [CNa Hred]]. apply CN_red with a; auto. Qed.

(** *** The closure operator *)

(** We define the _closure_ of a set [R], the closure of [R] by
expansion with respect to valid neutral terms.
*)
Inductive Cl (R : set) : set :=
| ClR : forall a, R a -> Cl R a
| ClExp : forall a, N a -> (forall b, red a b -> Cl R b) -> Cl R a
.

Lemma Cl_def : forall R, Cl R = Union R (Exp N (Cl R)).
Proof.
intros R; apply extEq; split; intros a Ha.
(* -> *)
  induction Ha; [left|right]; auto.
(* <- *)
  destruct Ha as [Ha|[Na Ha]]; auto using Cl.
Qed.

Lemma fold_Cl : forall R a, (R a \/ Exp N (Cl R) a) -> Cl R a.
Proof. intros; rewrite Cl_def; auto. Qed.

Lemma unfold_Cl : forall R a, Cl R a -> (R a \/ Exp N (Cl R) a).
Proof. intros; rewrite Cl_def in H; auto. Qed.

(** *** Pretype and types *)

(** We define predicates for sets of sound terms or sets stable by
interior, contraction, or expansion with respect to valid neutral
terms.
*)
Definition Psn R := Inc R SN.
Definition Pred R := Inc (Red R) R.
Definition Pexp R := Inc (Exp N R) R.
Hint Unfold Psn Pred Pexp.

(** We define [C] the set of pretypes, which are sets of sound terms
stable by interior and contraction. We define [CE] the set of types,
which are pretypes stable by expansion (with respect to valid neutral
terms). These two notions are very close to the notion of reducibility
candidates, which is why we write them [C] and [CE].
*)
Record C (R : set) : Prop := C_ {
  Csn : Psn R ;
  Cred : Pred R }.
Arguments Csn [R] _ _ _.
Arguments Cred [R] _ _ _.

Record CE (R : set) : Prop := CE_ {
  CEsn : Psn R ;
  CEred : Pred R ;
  CEexp : Pexp R }.
Arguments CEsn [R] _ _ _.
Arguments CEred [R] _ _ _.
Arguments CEexp [R] _ _ _.

Lemma CE_CPexp : forall R, Pexp R -> C R -> CE R.
Proof.
intros R PR CR; apply CE_.
apply (Csn CR).
apply (Cred CR).
apply PR.
Qed.

Lemma C_CE : forall {R}, CE R -> C R.
Proof. intros ? [? ? ?]; apply C_; auto. Qed.

(** *** Properties *)

(** We can show that the set of sound terms is a type.
*)
Lemma Pred_SN : Pred SN.
Proof.
intros b [a [SNa Hred]].
apply ExpSN with a; auto.
Qed.

Lemma Pexp_SN : Pexp SN.
Proof. intros a [Na Expa]; apply SN_; auto. Qed.

Lemma C_SN : C SN.
Proof.
apply C_; auto.
apply Pred_SN.
Qed.

Lemma CE_SN : CE SN.
Proof.
apply CE_; auto.
apply Pred_SN.
apply Pexp_SN.
Qed.

(** The closure operator preserves the pretype property and adds by
definition the expansion property. As a consequence, the closure of a
pretype is a type.
*)
Lemma Pexp_Cl : forall R, Pexp (Cl R).
Proof. intros R a Ha; rewrite Cl_def; right; exact Ha. Qed.

Lemma C_Cl : forall {R}, C R -> C (Cl R).
Proof.
intros R CR; apply C_.
(* 2: Csn *)
  intros a Cla.
  induction Cla; auto using SN.
  apply (Csn CR); auto.
(* 1: Cred *)
  intros b [a [Cla Hred]]; rewrite Cl_def in Cla.
  destruct Cla as [Pa|[Na Expa]]; auto.
  rewrite Cl_def; left; apply (Cred CR); exists a; auto.
Qed.

Lemma CE_Cl : forall {R}, C R -> CE (Cl R).
Proof.
intros R CR.
pose proof (C_Cl CR) as [? ?].
apply CE_; auto.
apply Pexp_Cl.
Qed.

(** The closure operator is also idempotent on types.
*)
Lemma destruct_Cl_CN : forall R a, CN a -> Cl R a -> R a.
Proof.
intros R a CNa Ha; apply unfold_Cl in Ha as [Ha|[Na _]]; auto.
exfalso; apply (CN_N a); auto.
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
  exists a, lam = Lam a /\ SN a /\ (forall b, R b -> S (subst b 0 a)).
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
Definition POne : set := fun unit => unit = Unit.
Definition EOne : set := Cl POne.
Hint Unfold POne EOne.

Definition PProd (R S : set) : set := fun pair =>
  exists a b, pair = Pair a b /\ (R a /\ S b).
Definition EProd (R S : set) : set := Cl (PProd R S).
Hint Unfold PProd EProd.

Definition PVoid : set := fun void => False.
Definition EVoid : set := Cl PVoid.
Hint Unfold PVoid EVoid.

Definition PSum (R S : set) : set := fun sum =>
  exists a, ((sum = Inl a /\ R a)
          \/ (sum = Inr a /\ S a)).
Definition ESum (R S : set) : set := Cl (PSum R S).
Hint Unfold PSum ESum.

(** In order to show that the arrow and product operators preserve
pretypes and types, we show a few lemmas. Variables are sound and in
all sets stable by expansion. Term abstractions and pairs are sound,
if their components are sound.
*)
Lemma SN_Var : forall n, SN (Var n).
Proof.
intros n.
apply SN_.
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H.
Qed.

Lemma R_Var : forall {R n}, Pexp R -> R (Var n).
Proof.
intros R n CR; apply CR.
split; auto.
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H.
Qed.

Lemma SN_Lam : forall {a}, SN a -> SN (Lam a).
Proof.
intros a SNa; induction SNa.
apply SN_.
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H1; clear H1; subst.
apply H0; auto.
Qed.

Lemma SN_Pair : forall {a}, SN a -> forall {b}, SN b -> SN (Pair a b).
Proof.
induction 1; induction 1.
apply SN_.
intros ? Hred; inversion Hred.
destruct c; simpl in *; inversion H3; clear H3; subst.
(* 2: *)
  apply H0; auto.
  apply SN_; auto.
(* 1: *)
  apply H2; auto.
Qed.

Lemma SN_Inl : forall {a}, SN a -> SN (Inl a).
Proof.
intros a SNa; induction SNa.
apply SN_.
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H1; clear H1; subst.
apply H0; auto.
Qed.

Lemma SN_Inr : forall {a}, SN a -> SN (Inr a).
Proof.
intros a SNa; induction SNa.
apply SN_.
intros b Hred; inversion Hred.
destruct c; simpl in *; inversion H1; clear H1; subst.
apply H0; auto.
Qed.

(** We also show that term soundness does not look at the actual names
of free variables. Free variables are just inert objects.
*)
Lemma SN_subst_Var : forall a i x, SN (subst (Var x) i a) -> SN a.
Proof.
intros a i x H.
remember (subst (Var x) i a) as b.
generalize i x a Heqb; clear i x a Heqb.
induction H; intros i x a' Heqb; subst.
apply SN_.
intros b' Hred.
apply H0 with (b := subst (Var x) i b') (a := b') (i := i) (x := x).
apply red_subst; auto.
reflexivity.
Qed.

(** The arrow pretype operator preserves pretypes.
*)
Lemma C_PArr : forall R {S}, C S -> C (PArr R S).
Proof.
intros R S CS.
apply C_.
(* 2: Csn *)
  intros lam [a [Heq [Hsn Hsub]]]; subst.
  apply SN_Lam; auto.
(* 1: Cred *)
  intros a' [lam [[a [Heq [Hsn Hsub]]] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H; clear H; subst;
  rename a'0 into a'.
  exists a'; split; [reflexivity|split].
  (* 2: Hsn *)
    apply Pred_SN; exists a; auto.
  (* 1: Hsub *)
    intros b Rb.
    apply (Cred CS).
    exists (subst b 0 a); split; auto.
    apply red_subst; auto.
Qed.

(** The arrow operator builds a type if its return set is a pretype.
*)
Lemma CE_EArr : forall R {S}, C S -> CE (EArr R S).
Proof.
intros; apply CE_Cl.
apply C_PArr; auto.
Qed.

(** The one pretype operator is a type.
*)
Lemma C_POne : C POne.
Proof.
apply C_.
(* Csn *)
  intros a Heq; rewrite Heq; clear Heq.
  apply SN_.
  intros b Hred.
  inversion Hred.
  destruct c; simpl in *; inversion H.
(* Cred *)
  intros a [one [Heq Hred]]; rewrite Heq in *; clear Heq.
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
(* 2: Csn *)
  intros pair [a [b [Heq [Ha Hb]]]]; subst.
  apply SN_Pair; [apply (Csn CR)|apply (Csn CS)]; auto.
(* 1: Cred *)
  intros a' [pair [[a [b [Heq [Ha Hb]]]] Hred]]; subst.
  inversion Hred.
  destruct c; simpl in *; inversion H; clear H; subst;
  [rename a'0 into a'|rename a'0 into b'];
  [exists a'; exists b|exists a; exists b']; (split; [reflexivity|split]); auto;
  apply Cred; auto; [exists a|exists b]; auto.
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
(* 2: Csn *)
  intros pair [a [[Heq Ha]|[Heq Ha]]]; subst.
  apply SN_Inl; apply (Csn CR); auto.
  apply SN_Inr; apply (Csn CS); auto.
(* 1: Cred *)
  intros a' [sum [[a [[Heq Ha]|[Heq Ha]]] Hred]]; subst;
  inversion Hred; destruct c; simpl in *; inversion H; clear H; subst;
  rename a'0 into a'; exists a'; [left|right];
  (split; [reflexivity|]); auto;
  apply Cred; auto; exists a; auto.
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
  SN a /\ For I cond func a.
Definition EFor_preserve P := forall Ix cond func,
  (forall i H, P (func i H)) -> P (EFor Ix cond func).
Hint Unfold For EFor EFor_preserve.

(** The forall operator preserves pretypes.
*)
Lemma C_EFor : EFor_preserve C.
Proof.
intros Ix cond func Hfor; apply C_.
(* Csn *)
  intros a [SNa Ha]; exact SNa.
(* Cred *)
  intros b [a [[SNa Ha] Hred]].
  split; [apply Pred_SN; exists a; auto|].
  intros i ci.
  apply (Cred (Hfor i ci)); exists a; auto.
Qed.

(** The forall operator preserves stability by expansion.
*)
Lemma Pexp_EFor : EFor_preserve Pexp.
Proof.
intros Ix cond func Hfor a [NVa Expa].
split.
- apply Pexp_SN.
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
  exists a, gen = Gen a /\ (forall i H, func i H a).
Definition EPi I cond func : set := Cl (PPi I cond func).
Hint Unfold PPi EPi.

Lemma SN_Gen : forall a, SN (Gen a).
Proof.
intros a.
apply SN_.
intros b Hred.
inversion Hred.
destruct c; simpl in H; inversion H; clear H.
Qed.

(** The pi pretype operator preserves pretypes.
*)
Lemma C_PPi : forall I cond func, (forall i H, C (func i H)) -> C (PPi I cond func).
Proof.
intros I cond func Cfunc.
apply C_.
(* 2: Csn *)
  intros gen [a [Heq Hfor]]; subst.
  apply SN_Gen; auto.
(* 1: Cred *)
  intros a' [gen [[a [Heq Hfor]] Hred]]; subst.
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
(* Csn *) intros a [i [Ci Ha]]; apply (Csn (Hfor i Ci)); apply Ha.
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

Lemma EJudg_Var : forall G S, Pexp S -> EJudg G S (Var (length G + 1)).
Proof.
intros G S CS; induction G; simpl.
(* 2: nil *) apply R_Var; auto.
(* 1: cons *)
  intros b Hb.
  simpl; subst_lift_var.
  rewrite <- minus_n_O.
  apply IHG.
Qed.

Lemma Psn_EJudg : forall G S, Forall Pexp G -> C S -> Psn (EJudg G S).
Proof.
induction G as [|R G]; intros S CG CS a Ha; simpl in *.
(* 2: nil *)
  apply (Csn CS); auto.
(* 1: cons *)
  apply SN_subst_Var with (x := (length G + 1)) (i := 0).
  inversion CG; subst.
  apply (IHG S H2 CS _).
  apply Ha; apply EJudg_Var; auto.
Qed.

Lemma C_EJudg : forall G S, Forall Pexp G -> C S -> C (EJudg G S).
Proof.
intros G S CG CS; apply C_.
(* CPsn *) apply Psn_EJudg; auto.
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

Lemma EVar_sem : forall R x G, C R ->
  nth x G ETop = R ->
  EJudg G R (Var x).
Proof.
induction x; intros G CR Hx;
(destruct G as [|R0 G]; simpl in *; subst; [apply R_Var; apply Pexp_Cl|]).
(* 0 *)
  intros b Rb; simpl; subst_lift_var; rewrite lift_0; auto.
(* 1+ *)
  intros b0 Rb0.
  simpl; subst_lift_var; rewrite <- minus_n_O.
  apply IHx; auto.
Qed.

Lemma ELam_sem : forall G R S a, Pexp R -> C S ->
  EJudg (R :: G) S a ->
  EJudg G (EArr R S) (Lam a).
Proof.
induction G as [|R0 G]; intros R S a CR CS Ha; simpl in *.
(* 2: nil *)
  apply fold_Cl; left.
  exists a; split; [|split]; auto.
  apply SN_subst_Var with 0 0.
  apply (Csn CS); apply Ha; apply R_Var; auto.
(* 1: cons *)
  intros b0 Rb0; subst; simpl.
  apply IHG; auto.
  intros b Rb.
  replace b with (subst b0 0 (shift 0 b)); [|apply subst_lift_0].
  rewrite <- subst_subst_0; apply Ha; auto.
  intros ? ?; rewrite subst_lift_0; auto.
Qed.

Lemma EApp_sem : forall G R S a b, C R -> CE S ->
  EJudg G (EArr R S) a ->
  EJudg G R b ->
  EJudg G S (App a b).
Proof.
induction G as [|R0 G]; intros R S a b CR CS Ha Hb; simpl in *.
(* 2: nil *)
  pose proof (CEsn (CE_EArr R (C_CE CS)) a Ha) as SNa.
  pose proof (Csn CR b Hb) as SNb.
  generalize Ha b SNb Hb; clear Ha b SNb Hb.
  induction SNa; intros Ha b SNb.
  induction SNb; intros Rb.
  apply (CEexp CS); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  (* +1: RedCtx *)
    destruct c; simpl in *; inversion H3; clear H3; subst.
    (* +1: CtxApp1 *)
      apply H0; auto.
      (* +1 *) apply (CEred (CE_EArr R (C_CE CS))); exists a; auto.
      (* +0 *) apply (Csn CR); auto.
    (* +0: CtxApp2 *) apply H2; auto; apply (Cred CR); exists a0; auto.
  (* +0: RedApp *)
    subst.
    pose proof (destruct_Cl_CN _ (Lam a1) I Ha) as [? [? [? ?]]].
    inversion H3; clear H3; subst; simpl in *.
    auto.
(* 1: cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma EUnit_sem : forall G, EJudg G EOne Unit.
Proof.
induction G as [|R0 G]; simpl in *.
(* nil *)
  apply fold_Cl; left; apply eq_refl.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EPair_sem : forall G R S a b, C R -> C S ->
  EJudg G R a ->
  EJudg G S b ->
  EJudg G (EProd R S) (Pair a b).
Proof.
induction G as [|R0 G]; intros R S a b CR CS Ha Hb; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists a, b; split; [|split]; auto.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EFst_sem : forall G R S a, CE R -> C S ->
  EJudg G (EProd R S) a ->
  EJudg G R (Fst a).
Proof.
induction G as [|R0 G]; intros R S a CR CS Ha; simpl in *.
(* 2: nil *)
  pose proof (CEsn (CE_EProd (C_CE CR) CS) a Ha) as SNa.
  generalize Ha; clear Ha; induction SNa; intros Ha.
  apply (CEexp CR); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  (* +1: *)
    destruct c; simpl in *; inversion H1; clear H1; subst.
    apply H0; auto; apply (CEred (CE_EProd (C_CE CR) CS)); exists a; auto.
  (* +0: *)
    subst.
    pose proof (destruct_Cl_CN _ (Pair b0 b) I Ha) as [? [? [? [? ?]]]].
    inversion H1; clear H1; subst; simpl in *.
    auto.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma ESnd_sem : forall G R S a, C R -> CE S ->
  EJudg G (EProd R S) a ->
  EJudg G S (Snd a).
Proof.
induction G as [|R0 G]; intros R S a CR CS Ha; simpl in *.
(* 2: nil *)
  pose proof (CEsn (CE_EProd CR (C_CE CS)) a Ha) as SNa.
  generalize Ha; clear Ha; induction SNa; intros Ha.
  apply (CEexp CS); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  (* +1: *)
    destruct c; simpl in *; inversion H1; clear H1; subst.
    apply H0; auto; apply (CEred (CE_EProd CR (C_CE CS))); exists a; auto.
  (* +0: *)
    subst.
    pose proof (destruct_Cl_CN _ (Pair a0 b0) I Ha) as [? [? [? [? ?]]]].
    inversion H1; clear H1; subst; simpl in *.
    auto.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG R S); auto.
Qed.

Lemma EAbsurd_sem : forall G S a, CE S ->
  EJudg G EVoid a ->
  EJudg G S (Absurd a).
Proof.
induction G as [|R0 G]; intros S a CS Ha; simpl in *.
(* nil *)
  pose proof (CEsn CE_EVoid a Ha) as SNa.
  generalize Ha; clear Ha; induction SNa; intros Ha.
  apply (CEexp CS); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  destruct c; simpl in *; inversion H1; clear H1; subst.
  apply H0; auto; apply (CEred CE_EVoid); exists a; auto.
(* cons *)
  intros b0 Rb0; simpl.
  apply (IHG S); auto.
Qed.

Lemma EInl_sem : forall G R S a,
  EJudg G R a ->
  EJudg G (ESum R S) (Inl a).
Proof.
induction G as [|R0 G]; intros R S a Ha; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists a; left; split; auto.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EInr_sem : forall G R S a,
  EJudg G S a ->
  EJudg G (ESum R S) (Inr a).
Proof.
induction G as [|R0 G]; intros R S a Ha; simpl in *.
(* nil *)
  apply fold_Cl; left.
  exists a; right; split; auto.
(* cons *)
  intros b0 Rb0; simpl; apply IHG; auto.
Qed.

Lemma EMatch_sem : forall G Rl Rr S a bl br, CE Rl -> CE Rr -> CE S ->
  EJudg G (ESum Rl Rr) a ->
  EJudg (Rl :: G) S bl ->
  EJudg (Rr :: G) S br ->
  EJudg G S (Match a bl br).
Proof.
induction G as [|R0 G]; intros Rl Rr S a bl br CRl CRr CS Ha Hbl Hbr; simpl in *.
(* 2: nil *)
  pose proof (CEsn (CE_ESum (C_CE CRl) (C_CE CRr)) a Ha) as SNa.
  assert (SN bl) as SNbl.
  { apply (Psn_EJudg (Rl :: nil) S); auto using C_CE, CEexp. }
  assert (SN br) as SNbr.
  { apply (Psn_EJudg (Rr :: nil) S); auto using C_CE, CEexp. }
  generalize Ha bl SNbl Hbl br SNbr Hbr; clear Ha bl SNbl Hbl br SNbr Hbr.
  induction SNa; intros Ha bl SNbl.
  induction SNbl; intros Hbl br SNbr.
  induction SNbr; intros Hbr.
  apply (CEexp CS); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  destruct c; simpl in *; inversion H5; clear H5; subst.
  (* +4: CtxMatch1 *)
    apply H0; auto.
    (* +2 *) apply (CEred (CE_ESum (C_CE CRl) (C_CE CRr))); exists a; auto.
    (* +1 *) apply (Psn_EJudg (Rl :: nil) S); auto using C_CE, CEexp.
    (* +0 *) apply (Psn_EJudg (Rr :: nil) S); auto using C_CE, CEexp.
  (* +3: CtxMatch2 *)
    apply H2; auto.
    (* +1 *) apply (Pred_EJudg (Rl :: nil) S); auto using C_CE; exists a0; auto.
    (* +0 *) apply (Psn_EJudg (Rr :: nil) S); auto using C_CE, CEexp.
  (* +2: CtxMatch3 *)
    apply H4; auto.
    apply (Pred_EJudg (Rr :: nil) S); auto using C_CE; exists a1; auto.
  (* +1: Inl *)
    subst; unfold ESum in Ha;
    apply unfold_Cl in Ha as [[a Hsum]|Expa]; subst.
    (* +1: PSum *)
      destruct Hsum as [[Heq Hin]|[Heq Hin]];
      inversion Heq; clear Heq; subst; simpl in *.
      apply Hbl; apply Hin.
    (* +0: Exp *)
      destruct Expa as [Na ?]; inversion Na.
  (* +0: In9 *)
    subst; unfold ESum in Ha;
    apply unfold_Cl in Ha as [[a Hsum]|Expa]; subst.
    (* +1: PSum *)
      destruct Hsum as [[Heq Hin]|[Heq Hin]];
      inversion Heq; clear Heq; subst; simpl in *.
      apply Hbr; apply Hin.
    (* +0: Exp *)
      destruct Expa as [Na ?]; inversion Na.
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

Lemma EGen_sem : forall I cond func G a, (forall i H, C (func i H)) ->
  (forall i H, EJudg G (func i H) a) ->
  EJudg G (EPi I cond func) (Gen a).
Proof.
induction G as [|R0 G]; intros a Cfunc Ha; simpl in *.
(* 2: nil *)
  apply fold_Cl; left.
  exists a; split; auto.
(* 1: cons *)
  intros b0 Rb0; subst; simpl.
  apply IHG; auto.
  intros i Hi.
  apply Ha; auto.
Qed.

Lemma EInst_sem : forall Ix cond func G a, (forall i H, CE (func i H)) ->
  EJudg G (EPi Ix cond func) a ->
  forall i H, EJudg G (func i H) (Inst a).
Proof.
induction G as [|R0 G]; intros a Cfunc Ha i H; simpl in *.
(* 2: nil *)
  pose proof (CEsn (CE_EPi Ix cond func (fun i ci => C_CE (Cfunc i ci))) a Ha) as SNa.
  generalize Ha; clear Ha; induction SNa; intros Ha.
  apply (CEexp (Cfunc i H)); split; [split|]; simpl; auto.
  intros b0 Hred; inversion Hred.
  (* +1: *)
    destruct c; simpl in *; inversion H2; clear H2; subst.
    apply H1; auto.
    apply CEred; [apply (CE_EPi Ix cond func); intros; apply C_CE; auto|].
    exists a; auto.
  (* +0: *)
    subst.
    pose proof (destruct_Cl_CN _ (Gen b0) I Ha) as [? [? ?]].
    inversion H2; clear H2; subst; simpl in *.
    auto.
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
Lemma Cl_For : forall Ix cond func (R : set),
  (exists i, cond i) -> (forall i H, C (func i H)) ->
  (forall a, For Ix cond func a -> R a) ->
  forall a, For Ix cond (fun i H => Cl (func i H)) a -> Cl R a.
Proof.
intros Ix cond func R Hexi Cfunc Hinc a Ha.
assert (SN a) as SNa.
{ destruct Hexi as [i ci].
  apply (Csn (C_Cl (Cfunc i ci))); auto. }
generalize Ha; clear Ha.
induction SNa; intros Ha.
destruct (N_dec a); apply fold_Cl; [left|right].
(* 2: CN *)
  apply Hinc; auto.
  intros i ci.
  apply (destruct_Cl_CN _ _ c (Ha i ci)).
(* 1: N *)
  repeat split; auto.
  intros b Hred.
  apply H0; auto.
  intros i ci.
  apply (Cred (C_Cl (Cfunc i ci))).
  exists a; auto.
Qed.

