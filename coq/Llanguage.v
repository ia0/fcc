Require Import Omega.
Require Import Min.
Require Import Max.

Require Import set.

(** * Lambda Calculus *)

(** ** Definition *)

(** Terms are written [a] or [b]. They are defined exactly like
indexed terms without the notion of fuel. They contain variables,
abstractions, applications, pairs, projections, generalization, and
instantiations.

Scoping is informally described by "a : I J" where I (resp. J) is a
partial function from natural numbers to term (resp. proposition)
binding points. Both functions are defined from 0 up to a natural
number, which is excluded and written |I| (resp. |J|), and undefined
from this number.
*)
Inductive term : Set :=
(* x < |I|
   -------
   x : I J
*)
| Var (x : nat)
(* a : (0 => bind | S i => I i) J
   ------------------------------
   Lam a : I J
*)
| Lam (a : term)
(* a : I J
   b : I J
   -------------
   App a b : I J
*)
| App (a : term) (b : term)
| Unit
| Pair (a : term) (b : term)
| Fst (a : term)
| Snd (a : term)
| Absurd (a : term)
| Inl (a : term)
| Inr (a : term)
(* a : I J
   bl : (0 => bind | S i => I i) J
   br : (0 => bind | S i => I i) J
   -------------------------------
   Match a bl br : I J
*)
| Match (a : term) (bl : term) (br : term)
| Witness
(* a : I J
   b : I (0 => bind | S j => J j)
   ------------------------------
   Assume a b : I J
*)
| Assume (a : term) (b : term)
(* a : I (j when j < n => J j | j => J (S j))
   ------------------------------------------
   Hide n a : I J
*)
| Hide (p : nat) (a : term)
.

(** ** Functions *)

(** We define a function to traverse terms and operating on its
variables. The term [traverse f i a] has the same structure as [a] but
for its variables [Var x] that become [f x i]. The level [i] indicates
how deep we are in the term: it is incremented each time we cross a
binder. The only binder of the Lambda Calculus is [Lam] and it binds
only one term, so the recursive call uses the level [1 + i]. The level
[j] is similar but for proposition variables.

Note that substitution and lifting will never encounter an outer Hide
since no proposition variables are visible in the redex context. In
other words, we use this function only on proposition-closed terms.
*)
Definition traverse f := fix g i j a :=
  match a with
  | Var x => f x i j
  | Lam a => Lam (g (1 + i) j a)
  | App a b => App (g i j a) (g i j b)
  | Unit => Unit
  | Pair a b => Pair (g i j a) (g i j b)
  | Fst a => Fst (g i j a)
  | Snd a => Snd (g i j a)
  | Absurd a => Absurd (g i j a)
  | Inl a => Inl (g i j a)
  | Inr a => Inr (g i j a)
  | Match a bl br => Match (g i j a) (g (1 + i) j bl) (g (1 + i) j br)
  | Witness => Witness
  | Assume a b => Assume (g i j a) (g i (1 + j) b)
  | Hide p a => Hide p (g i (j - 1) a) (* assumes proposition-closed term *)
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
Definition lift_idx d x i (j : nat) := Var (if le_gt_dec i x then d + x else x).
Definition lift d := traverse (lift_idx d).
Definition shift := lift 1.
Hint Unfold lift_idx lift shift.

Fixpoint hide j a :=
  match j with
    | O => a
    | S j => Hide j (hide j a)
      (* Alternative versions:
         - hide j (Hide 0 a)
         - Hide 0 (hide j a) *)
  end.

Fixpoint unhide j a :=
  match a with
  | Var x => Var x
  | Lam a => Lam (unhide j a)
  | App a b => App (unhide j a) (unhide j b)
  | Unit => Unit
  | Pair a b => Pair (unhide j a) (unhide j b)
  | Fst a => Fst (unhide j a)
  | Snd a => Snd (unhide j a)
  | Absurd a => Absurd (unhide j a)
  | Inl a => Inl (unhide j a)
  | Inr a => Inr (unhide j a)
  | Match a bl br => Match (unhide j a) (unhide j bl) (unhide j br)
  | Witness => Witness
  | Assume a b => Assume (unhide j a) (unhide (1 + j) b)
  | Hide p a =>
    match lt_eq_lt_dec p j with
      | inleft (left _)  => Hide p (unhide (j - 1) a)
      | inleft (right _) => a
      | inright _        => Hide (p - 1) (unhide j a)
    end
  end.

Definition subst_idx b x i j :=
  match lt_eq_lt_dec x i with
    | inleft (left _)  => Var x
    | inleft (right _) => hide j (lift x 0 0 b)
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

Definition set := @set.set term.

(** ** Reduction *)

(** Evaluation contexts [Ctx] contain all one-hole contexts. This
gives us strong reduction for all constructs. The meaning of [Ctx] is
given by the [fill] function. The term [fill c a] wraps the term [a]
under the context [c].
*)
Inductive Ctx : Set :=
| CtxHole
| CtxLam (c : Ctx)
| CtxApp1 (c : Ctx) (a : term)
| CtxApp2 (a : term) (c : Ctx)
| CtxPair1 (c : Ctx) (a : term)
| CtxPair2 (a : term) (c : Ctx)
| CtxFst (c : Ctx)
| CtxSnd (c : Ctx)
| CtxAbsurd (c : Ctx)
| CtxInl (c : Ctx)
| CtxInr (c : Ctx)
| CtxMatch1 (c : Ctx) (bl : term) (br : term)
| CtxMatch2 (a : term) (c : Ctx) (br : term)
| CtxMatch3 (a : term) (bl : term) (c : Ctx)
| CtxAssume1 (c : Ctx) (a : term)
| CtxAssume2 (a : term) (c : Ctx)
| CtxHide (p : nat) (c : Ctx)
.

Fixpoint fill c a :=
  match c with
    | CtxHole => a
    | CtxLam c => Lam (fill c a)
    | CtxApp1 c b => App (fill c a) b
    | CtxApp2 b c => App b (fill c a)
    | CtxPair1 c b => Pair (fill c a) b
    | CtxPair2 b c => Pair b (fill c a)
    | CtxFst c => Fst (fill c a)
    | CtxSnd c => Snd (fill c a)
    | CtxAbsurd c => Absurd (fill c a)
    | CtxInl c => Inl (fill c a)
    | CtxInr c => Inr (fill c a)
    | CtxMatch1 c b1 b2 => Match (fill c a) b1 b2
    | CtxMatch2 b1 c b2 => Match b1 (fill c a) b2
    | CtxMatch3 b1 b2 c => Match b1 b2 (fill c a)
    | CtxAssume1 c b => Assume (fill c a) b
    | CtxAssume2 b c => Assume b (fill c a)
    | CtxHide p c => Hide p (fill c a)
  end.

Fixpoint guard c s :=
  match c with
    | CtxHole => s
    | CtxLam c => guard c s
    | CtxApp1 c b => guard c s
    | CtxApp2 b c => guard c s
    | CtxPair1 c b => guard c s
    | CtxPair2 b c => guard c s
    | CtxFst c => guard c s
    | CtxSnd c => guard c s
    | CtxAbsurd c => guard c s
    | CtxInl c => guard c s
    | CtxInr c => guard c s
    | CtxMatch1 c b1 b2 => guard c s
    | CtxMatch2 b1 c b2 => guard c s
    | CtxMatch3 b1 b2 c => guard c s
    | CtxAssume1 c b => guard c s
    | CtxAssume2 b c => guard c (1 + s)
    | CtxHide p c => guard c (s - 1) (* We only care about [guard c 0 = 0]. *)
  end.

Definition unguarded c := if eq_nat_dec (guard c 0) 0 then True else False.

(** The reduction relation [hred] contains head reduction.
*)
Inductive hred : term -> term -> Prop :=
| HRedApp : forall a b, hred (App (Lam a) b) (subst b 0 0 a)
| HRedFst : forall a b, hred (Fst (Pair a b)) a
| HRedSnd : forall a b, hred (Snd (Pair a b)) b
| HRedInl : forall a bl br, hred (Match (Inl a) bl br) (subst a 0 0 bl)
| HRedInr : forall a bl br, hred (Match (Inr a) bl br) (subst a 0 0 br)
| HRedProp : forall a, hred (Assume Witness a) (unhide 0 a)
.

Inductive cred : term -> term -> Prop :=
| CRed : forall a b c, hred a b -> unguarded c -> cred (fill c a) (fill c b)
.

(** ** Errors and valid terms *)

(** In order to define the notions of errors and valid terms, we need
to define the notions of neutral terms and head normal forms. Neutral
terms [N] are either variables or destructors, while head normal forms
[CN] are constructors.
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
    | Witness => False
    | Assume _ _ => True
    | Hide _ _ => True
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
    | Witness => True
    | Assume _ _ => False
    | Hide _ _ => False
  end.
Hint Unfold N CN.

(** Neutral terms and head normal forms partition the set of terms. A
term is either neutral or in head normal form.
*)
Lemma N_dec : forall a, {CN a} + {N a}.
Proof. destruct a; simpl; auto. Qed.

Lemma CN_N : forall a, CN a -> N a -> False.
Proof. destruct a; auto. Qed.

Lemma CN_hred : forall a b, hred a b -> CN a -> False.
Proof.
induction 1; intros CNa; simpl in CNa; assumption.
Qed.

Lemma CN_cred : forall a b, cred a b -> CN a -> CN b.
Proof.
induction 1; intros CNa; simpl in CNa; try (exfalso; exact CNa).
destruct c; simpl in *; auto.
exfalso; apply (CN_hred _ _ H CNa).
Qed.

(** We define predicates to know when a term is not the constructor of
the arrow type, the product type, or the proposition type.
*)
Definition NotArr a := forall a', a <> Lam a'.
Definition NotProd a := forall a' b', a <> Pair a' b'.
Definition NotSum a := forall a', a <> Inl a' /\ a <> Inr a'.
Definition NotProp a := a <> Witness.
Hint Unfold NotArr NotProd NotSum NotProp.

(** We can now define the set of head errors [HErr]. A head error
happens when a destructor is applied to a wrong constructor. For
example, the term [App a b] is an error if the term [a] is a
constructor which is not of the arrow type, because [App] is the
destructor of the arrow type.
*)
Inductive HErr : set :=
| HErrApp : forall a b, CN a -> NotArr a -> HErr (App a b)
| HErrFst : forall a, CN a -> NotProd a -> HErr (Fst a)
| HErrSnd : forall a, CN a -> NotProd a -> HErr (Snd a)
| HErrAbsurd : forall a, CN a -> HErr (Absurd a)
| HErrMatch : forall a bl br, CN a -> NotSum a -> HErr (Match a bl br)
| HErrInst : forall a b, CN a -> NotProp a -> HErr (Assume a b)
.

Inductive CErr : set :=
| CErrCtx : forall a c, HErr a -> unguarded c -> CErr (fill c a)
.

(** Valid terms are simply the complementary of errors.
*)
Definition V : set := Cmp CErr.
Hint Unfold V.

(** ** Strong normalization *)
Inductive SN : set :=
| SN_ : forall a, (forall b, cred a b -> SN b) -> SN a
.

Lemma ExpSN : forall a, SN a -> forall b, cred a b -> SN b.
Proof. intros; destruct H; auto. Qed.

(** ** Properties about lift and subst *)

Lemma lift_0 : forall a i j, lift 0 i j a = a.
Proof. induction a; intros i j; simpl; [subst_lift_var|..]; f_equal; auto. Qed.
(*
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
*)
(** ** Values *)

(** We mutually define the set of prevalues 'value False' and values
'value True'.
*)
Inductive value_guard :=
| VClosed (v : Prop)
| VGuarded (g : value_guard)
.

Definition vn v j :=
  match j with
    | VClosed _ => VClosed v
    | j => j
  end.

Definition vx j :=
  match j with
    | VClosed v => v
    | j => True
  end.

Fixpoint value j a :=
  match a with
    | Var _ => True
    | Lam a => vx j /\ value (vn True j) a
    | App a b  => value (vn False j) a /\ value (vn True j) b
    | Unit => vx j
    | Pair a b => vx j /\ value (vn True j) a /\ value (vn True j) b
    | Fst a => value (vn False j) a
    | Snd a => value (vn False j) a
    | Absurd a => value (vn False j) a
    | Inl a => vx j /\ value (vn True j) a
    | Inr a => vx j /\ value (vn True j) a
    | Match a bl br => value (vn False j) a /\ value (vn True j) bl /\ value (vn True j) br
    | Witness  => vx j
    | Assume a b  => value (vn False j) a /\ value (VGuarded j) b
    | Hide _ a  =>
      match j with
        | VClosed _ => value (VClosed True) a
        | VGuarded (VClosed _) => value (VClosed True) a
        | VGuarded j => value j a
      end
  end.

(** Irreducible terms. *)
Definition irred a := forall b, cred a b -> False.
Hint Unfold irred.

(** Prevalues are values. *)
Lemma prevalue_is_value : forall a, value (VClosed False) a -> value (VClosed True) a.
Proof.
induction a; simpl; intros; auto;
repeat (match goal with
  | H1 : _ /\ _ |- _ => destruct H1
end; auto).
split; auto.
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
(*
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
*)
(** Values are irreducible valid terms. *)
Lemma progre : forall a, irred a -> V a -> value True a.
Proof.
induction a; intros ia Va; repeat split; auto.
{ (* CtxLam *)
  apply IHa.
  intros b Hred.
  inversion Hred.

; progre_aux0 CtxLam. }
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
