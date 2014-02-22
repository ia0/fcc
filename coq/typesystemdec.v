Require Import Omega.
Require Import Bool.

Require Import mxx.
Require Import typesystem.

Definition obj_dec : forall (o1 o2 : obj), {o1 = o2} + {o1 <> o2}.
Proof.
decide equality.
apply eq_nat_dec.
Defined.

Definition class_dec : forall (c1 c2 : class), {c1 = c2} + {c1 <> c2}.
Proof.
decide equality.
Defined.

Definition cobj_dec : obj -> option class := fix f o :=
  match o with
  | KStar | KOne => Some CKind
  | KProd k1 k2 =>
      match f k1, f k2 with
        | Some CKind, Some CKind => Some CKind
        | _, _ => None
      end
  | KRes k p =>
      match f k, f p with
        | Some CKind, Some CProp => Some CKind
        | _, _ => None
      end
  | TVar _ | TOne | TVoid | TBot | TTop | TUnit => Some CType
  | TMu t | TFst t | TSnd t =>
      match f t with
        | Some CType => Some CType
        | _ => None
      end
  | TArr t s | TProd t s | TSum t s | TPair t s =>
      match f t, f s with
        | Some CType, Some CType => Some CType
        | _, _ => None
      end
  | TFor k t | TPi k t =>
      match f k, f t with
        | Some CKind, Some CType => Some CType
        | _, _ => None
      end
  | PTrue => Some CProp
  | PAnd p1 p2 =>
      match f p1, f p2 with
        | Some CProp, Some CProp => Some CProp
        | _, _ => None
      end
  | PCoer H t s =>
      match f H, f t, f s with
        | Some CTEnv, Some CType, Some CType => Some CProp
        | _, _, _ => None
      end
  | PExi k =>
      match f k with
        | Some CKind => Some CProp
        | _ => None
      end
  | PFor k p =>
      match f k, f p with
        | Some CKind, Some CProp => Some CProp
        | _, _ => None
      end
  | HNil => Some CTEnv
  | HCons H k =>
      match f H, f k with
        | Some CTEnv, Some CKind => Some CTEnv
        | _, _ => None
      end
  | YNil => Some CPEnv
  | YCons Y p =>
      match f Y, f p with
        | Some CPEnv, Some CProp => Some CPEnv
        | _, _ => None
      end
  | GNil => Some CAEnv
  | GCons G t =>
      match f G, f t with
        | Some CAEnv, Some CType => Some CAEnv
        | _, _ => None
      end
  end.

Lemma cobj_dec_cobj : forall o c, cobj_dec o = Some c <-> cobj o c.
Proof.
intros; split; intros H.
(* -> *)
  generalize c H; clear c H.
  induction o; simpl; intros c H; repeat
  match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    | H : match ?x with _ => _ end = _ |- _ =>
        destruct x; try solve [inversion H]
  end; auto using cobj.
(* <- *)
  induction H; simpl; repeat
  match goal with
    | H : ?x = ?y |- match ?x with _ => _ end = _ =>
        rewrite H
  end; auto.
Qed.

Definition get_cobj : forall o, option (sigT (cobj o)).
Proof.
intros o.
remember (cobj_dec o) as e.
destruct e as [c|]; [apply Some|exact None].
apply (existT _ c).
apply cobj_dec_cobj.
apply eq_sym; assumption.
Defined.

Definition Hnth_dec : tenv -> nat -> option kind := fix f H a :=
  match a with
    | O =>
      match H with
        | HCons _ k => Some k
        | _ => None
      end
    | S a =>
      match H with
        | HCons H _ => f H a
        | _ => None
      end
  end.

Lemma Hnth_dec_Hnth : forall H a k, Hnth_dec H a = Some k <-> Hnth H a k.
Proof.
intros; split; intros Ha.
(* -> *)
  generalize H k Ha; clear H k Ha.
  induction a; simpl; intros H k Ha;
  destruct H; simpl in Ha; repeat
  match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    | H : None = Some _ |- _ => solve [inversion H]
  end; auto using Hnth.
(* <- *)
  induction Ha; simpl; auto.
Qed.

Definition get_Hnth : forall H a, option (sigT (Hnth H a)).
Proof.
intros H a.
remember (Hnth_dec H a) as e.
destruct e as [k|]; [apply Some|exact None].
apply (existT _ k).
apply Hnth_dec_Hnth.
apply eq_sym; assumption.
Defined.

Definition Gnth_dec : aenv -> nat -> option type := fix f G x :=
  match x with
    | O =>
      match G with
        | GCons _ t => Some t
        | _ => None
      end
    | S x =>
      match G with
        | GCons G _ => f G x
        | _ => None
      end
  end.

Lemma Gnth_dec_Gnth : forall G x t, Gnth_dec G x = Some t <-> Gnth G x t.
Proof.
intros; split; intros Hx.
(* -> *)
  generalize G t Hx; clear G t Hx.
  induction x; simpl; intros G t Hx;
  destruct G; simpl in Hx; repeat
  match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    | H : None = Some _ |- _ => solve [inversion H]
  end; auto using Gnth.
(* <- *)
  induction Hx; simpl; auto.
Qed.

Definition get_Gnth : forall G x, option (sigT (Gnth G x)).
Proof.
intros G x.
remember (Gnth_dec G x) as e.
destruct e as [t|]; [apply Some|exact None].
apply (existT _ t).
apply Gnth_dec_Gnth.
apply eq_sym; assumption.
Defined.

Definition is_free := fix f a o :=
  (match o with
  | KStar | KOne => true
  | KProd k1 k2 => f a k1 && f a k2
  | KRes k p => f a k && f (1 + a) p
  | TVar b => negb (beq_nat a b)
  | TOne | TVoid | TBot | TTop | TUnit => true
  | TMu t => f (1 + a) t
  | TFst t | TSnd t => f a t
  | TArr t s | TProd t s | TSum t s | TPair t s => f a t && f a s
  | TFor k t | TPi k t => f a k && f (1 + a) t
  | PTrue => true
  | PAnd p1 p2 => f a p1 && f a p2
  | PCoer H t s => f a H && f (Hlength H + a) t && f a s
  | PExi k => f a k
  | PFor k p => f a k && f (1 + a) p
  | HNil => true
  | HCons H k => f a H && f (Hlength H + a) k
  | YNil => true
  | YCons Y p => f a Y && f a p
  | GNil => true
  | GCons G t => f a G && f a t
  end)%bool.

Lemma is_free_sound : forall a o, is_free a o = true -> exists o', o = shift a o'.
Proof.
intros a o.
generalize a; clear a.
induction o; intros a Heq; inversion Heq; clear Heq; subst;
repeat match goal with
  | H : ?x && ?y = true |- _ => destruct (proj1 (andb_true_iff x y) H); clear H
  | IH : forall a, is_free a ?o = true -> _ , H : is_free ?a ?o = true |- _ =>
    destruct (IH a H); clear IH; subst o
end.
exists KStar; reflexivity.
exists KOne; reflexivity.
exists (KProd x0 x); reflexivity.
exists (KRes x0 x); reflexivity.
{ apply eq_sym, negb_sym, beq_nat_false_iff in H0.
  destruct (lt_eq_lt_dec a x) as [[?|?]|?]; [|exfalso; omega|].
  - destruct x; [inversion l|].
    exists (TVar x); simpl; subst_lift_var.
  - exists (TVar x); simpl; subst_lift_var. }
exists (TArr x0 x); reflexivity.
exists TOne; reflexivity.
exists (TProd x0 x); reflexivity.
exists TVoid; reflexivity.
exists (TSum x0 x); reflexivity.
exists (TFor x0 x); reflexivity.
exists (TPi x0 x); reflexivity.
exists (TMu x); reflexivity.
exists TBot; reflexivity.
exists TTop; reflexivity.
exists TUnit; reflexivity.
exists (TPair x0 x); reflexivity.
exists (TFst x); reflexivity.
exists (TSnd x); reflexivity.
exists PTrue; reflexivity.
exists (PAnd x0 x); reflexivity.
exists (PCoer x0 x x1); simpl; unfold shift; rewrite Hlength_lift; reflexivity.
exists (PExi x); reflexivity.
exists (PFor x0 x); reflexivity.
exists HNil; reflexivity.
exists (HCons x0 x); simpl; unfold shift; rewrite Hlength_lift; reflexivity.
exists YNil; reflexivity.
exists (YCons x0 x); reflexivity.
exists GNil; reflexivity.
exists (GCons x0 x); reflexivity.
Qed.

Definition jrec_dec : nat -> type -> recsort -> bool := fix f a t rec :=
  (match t with
  | TVar b => is_free a t ||
      match rec with
        | NE => true
        | WF => false
      end
  | TBot | TTop => true
  | TArr t s | TProd t s | TSum t s => f a t NE && f a s NE
  | TMu t => f (1 + a) t rec && f 0 t WF
  | TFor k t => is_free a k && f (1 + a) t rec
  | TPi k t => is_free a k && f (1 + a) t NE
  | _ => false
  end)%bool.

Lemma jrec_dec_jrec : forall a t rec, jrec_dec a t rec = true -> jrec a t rec.
Proof.
intros a t.
generalize a; clear a.
induction t; intros a rec Heq; inversion Heq; clear Heq; subst;
repeat match goal with
  | H : ?x && ?y = true |- _ => destruct (proj1 (andb_true_iff x y) H); clear H
end.
{ remember (negb (beq_nat a x)) as e; apply eq_sym in Heqe.
  destruct e.
  { destruct (is_free_sound a (TVar x) Heqe) as [w ?].
    destruct rec; [|apply RECne]; apply RECwf with w; auto. }
  destruct rec; inversion H0; clear H0.
  apply eq_sym, negb_sym, beq_nat_true_iff in Heqe; subst.
  apply RECVar. }
destruct rec; [|apply RECne]; apply RECArr; auto.
destruct rec; [|apply RECne]; apply RECProd; auto.
destruct rec; [|apply RECne]; apply RECSum; auto.
destruct (is_free_sound _ _ H) as [w ?]; apply RECFor with w; auto.
destruct rec; [|apply RECne]; destruct (is_free_sound _ _ H) as [w ?]; apply RECPi with w; auto.
apply RECMu; auto.
destruct rec; [|apply RECne]; apply RECwf with TBot; auto.
destruct rec; [|apply RECne]; apply RECwf with TTop; auto.
Qed.

Definition get_jrec a t rec : option (jrec a t rec) :=
  match jrec_dec a t rec return _ with
    | true => fun Heq => Some (jrec_dec_jrec a t rec Heq)
    | false => fun _ => None
  end eq_refl.

(* Definition rmin r1 r2 := *)
(*   match r1, r2 with *)
(*     | NE, _ | _, NE => NE *)
(*     | _, _ => WF *)
(*   end. *)

(* Definition rinc (r : recsort) := WF. *)

(* Definition jrec_dec : nat -> type -> option recsort := fix f a t := *)
(*   match t with *)
(*     | TVar b => if beq_nat a b then Some NE else Some CST *)
(*     | TArr t s | TProd t s | TSum t s => *)
(*         match f a t, f a s with *)
(*           | Some r1, Some r2 => Some (rinc (rmin r1 r2)) *)
(*           | _, _ => None *)
(*         end *)
(*     | TFor k t => *)
(*         match f a k, f (1 + a) t with *)
(*           | Some CST, Some rec => Some rec *)
(*           | _, _ => None *)
(*         end *)
(*     | TPi k t => *)
(*         match f a k, f (1 + a) t with *)
(*           | Some CST, Some r => Some (rinc r) *)
(*           | _, _ => None *)
(*         end *)
(*     | TMu t => *)
(*         match f 0 t, f (1 + a) t with *)
(*           | Some WF, Some rec => Some rec *)
(*           | _, _ => None *)
(*         end *)
(*     | _ => None *)
(*   end. *)

(* Definition le_recsort r1 r2 := *)
(*   match r1, r2 with *)
(*     | CST, _ => True *)
(*     | WF, CST => False *)
(*     | WF, _ => True *)
(*     | NE, NE => True *)
(*     | NE, _ => False *)
(*   end. *)
(* Hint Unfold le_recsort. *)

(* Lemma jrec_le : forall a t r1 r2, le_recsort r1 r2 -> jrec a t r1 -> jrec a t r2. *)
(* Proof. *)
(* intros; destruct r1; destruct r2; auto using RECne, RECwf; inversion H. *)
(* Qed. *)

(* Lemma jrec_NE : forall a t r, jrec a t r -> jrec a t NE. *)
(* Proof. *)
(* intros; apply (jrec_le a t r NE); auto. *)
(* destruct r; auto. *)
(* Qed. *)

(* Lemma jrec_dec_dir : forall t a rec, jrec_dec a t = Some rec -> jrec a t rec. *)
(* Proof. *)
(* induction t; simpl; intros a rec H; repeat *)
(* match goal with *)
(*   | |- jrec _ (TVar _) _ => fail 1 *)
(*   | |- jrec _ (TMu _) _ => fail 1 *)
(*   | H : None = Some _ |- _ => inversion H *)
(*   | H : Some _ = Some _ |- _ => inversion H; clear H; subst *)
(*   | H1 : match jrec_dec ?a ?t with _ => _ end = _ *)
(*   , H2 : forall _ _, jrec_dec _ ?t = _ -> _ |- _ => *)
(*       pose proof (H2 a); clear H2; *)
(*       destruct (jrec_dec a t); try solve [inversion H] *)
(*   | H : forall rec, Some ?r = Some rec -> _ |- _ => *)
(*       pose proof (H r eq_refl); clear H *)
(*   | H : match ?x with _ => _ end = _ |- _ => *)
(*       destruct x; try solve [inversion H] *)
(* end. *)
(* (* 7: TVar *) *)
(*   remember (beq_nat a x) as y. *)
(*   destruct y; inversion H; clear H; subst. *)
(*   (* +1: a = x *) *)
(*     pose proof (beq_nat_true a x (eq_sym Heqy)); subst. *)
(*     apply RECVar. *)
(*   (* +0: a <> x *) *)
(*     pose proof (beq_nat_false a x (eq_sym Heqy)). *)
(*     destruct (le_gt_dec a x). *)
(*     (* +1: a < x *) *)
(*       destruct x as [|x]; [exfalso; omega|]. *)
(*       apply RECcst with (TVar x); simpl. *)
(*       subst_lift_var. *)
(*     (* +0: a > x *) *)
(*       apply RECcst with (TVar x); simpl. *)
(*       subst_lift_var. *)
(* (* 6: TArr *) apply RECArr; eapply jrec_NE; eassumption. *)
(* (* 5: TProd *) apply RECProd; eapply jrec_NE; eassumption. *)
(* (* 4: TSum *) apply RECSum; eapply jrec_NE; eassumption. *)
(* (* 3: TFor *) apply RECFor; auto. *)
(* (* 2: TPi *) apply RECPi; [|eapply jrec_NE]; eassumption. *)
(* (* 1: TMu *) *)
(*   pose proof (IHt 0). *)
(*   pose proof (IHt (1 + a) rec); clear IHt. *)
(*   simpl in H1. *)
(*   destruct (jrec_dec 0 t); try solve [inversion H]. *)
(*   destruct r; try solve [inversion H]. *)
(*   destruct (jrec_dec (S a) t); try solve [inversion H]. *)
(*   apply RECMu; auto. *)
(* Qed. *)

(* Lemma jrec_dec_rev : forall t a r2, jrec a t r2 -> *)
(*   exists r1, (forall r, jrec a t r -> le_recsort r1 r) /\ jrec_dec a t = Some r1. *)
(* Proof. *)
(* intros. *)
(* induction H; simpl in *; repeat *)
(* match goal with *)
(*   | H : exists _, _ /\ _ |- _ => destruct H as [? [? ?]] *)
(*   | H : ?x = ?y |- _ => rewrite H *)
(* end. *)
(* (* 10: RECVar *) *)
(*   rewrite <- beq_nat_refl. *)
(*   exists NE; split; auto. *)
(*   intros. *)
(*   destruct r; simpl in H; auto. *)
(*   (* +1: *) *)
(*     inversion H; clear H; subst. *)
(*     destruct s; inversion H0; clear H0. *)
(*     exfalso; destruct (le_gt_dec a x); omega. *)
(*   (* +0: *) *)
(*     inversion H; clear H; subst. *)
(*     inversion H0; clear H0; subst. *)
(*     destruct s; inversion H; clear H. *)
(*     exfalso; destruct (le_gt_dec a x); omega. *)
(* (* 9: RECArr *) *)
(*   exists WF; split; auto. *)
(*   intros. *)
(*   destruct r *)
(* (* 8: RECProd *) exists WF; auto. *)
(* (* 7: RECSum *) exists WF; auto. *)
(* (* 6: RECFor *) *)
(*   exists x. *)
(*   split; auto. *)
(*   destruct x0; auto; inversion H3. *)
(* (* 5: RECPi *) *)
(*   exists WF. *)
(*   split; auto. *)
(*   destruct x0; auto; inversion H3. *)
(* (* 4: RECMu *) *)
(*   destruct x0; inversion H3. *)
(*   exists x. *)
(*   split; auto. *)
(* Qed. *)

(* Definition jeq_norm := fix f o := *)
(*   match o with *)
(*   | KStar => KStar *)
(*   | KOne => KOne *)
(*   | KProd k1 k2 => KProd (f k1) (f k2) *)
(*   | KRes k p => KRes (f k) (f p) *)
(*   | TVar a => TVar a *)
(*   | TArr t s => TArr (f t) (f s) *)
(*   | TProd t s => TProd (f t) (f s) *)
(*   | TSum t s => TSum (f t) (f s) *)
(*   | TFor k t => TFor (f k) (f t) *)
(*   | TPi k t => TPi (f k) (f t) *)
(*   | TMu t => TMu (f t) *)
(*   | TBot => TBot *)
(*   | TTop => TTop *)
(*   | TUnit => TUnit *)
(*   | TPair t s => TPair (f t) (f s) *)
(*   | TFst t => *)
(*       match f t with *)
(*         | TPair t s => t *)
(*         | t => TFst t *)
(*       end *)
(*   | TSnd t => *)
(*       match f t with *)
(*         | TPair t s => s *)
(*         | t => TSnd t *)
(*       end *)
(*   | TPack t => TPack (f t) *)
(*   | TUnpack t => *)
(*       match f t with *)
(*         | TPack t => t *)
(*         | t => TUnpack t *)
(*       end *)
(*   | PTrue => PTrue *)
(*   | PAnd p1 p2 => PAnd (f p1) (f p2) *)
(*   | PCoer H t s => PCoer (f H) (f t) (f s) *)
(*   | PExi k => PExi (f k) *)
(*   | PFor k p => PFor (f k) (f p) *)
(*   | HNil => HNil *)
(*   | HCons H k => HCons (f H) (f k) *)
(*   | YNil => YNil *)
(*   | YCons Y p => YCons (f Y) (f p) *)
(*   | GNil => GNil *)
(*   | GCons G t => GCons (f G) (f t) *)
(*   end. *)

