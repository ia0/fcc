Require Import Omega.

Require Import mxx.
Require Import Llanguage.
Require Import typesystem.
Require Import Ltypesystem.

Lemma cobj_lift : forall {o c}, cobj o c -> forall d i, cobj (lift d i o) c.
Proof.
induction 1; simpl; intros; auto using cobj.
subst_lift_var; auto using cobj.
Qed.

Lemma cobj_unlift : forall {o c d i}, cobj (lift d i o) c -> cobj o c.
Proof.
induction o; simpl; intros; inversion H; clear H; subst; eauto using cobj.
Qed.

Lemma cobj_subst : forall {t}, cobj t CType -> forall {o c}, cobj o c ->
  forall i, cobj (subst t i o) c.
Proof.
induction 2; simpl; intros; auto using cobj.
subst_lift_var; auto using cobj; subst.
apply cobj_lift; auto.
Qed.

Lemma cobj_eq : forall {o c1 c2}, cobj o c1 -> cobj o c2 -> c1 = c2.
Proof. destruct 1; intros Ho; inversion Ho; clear Ho; reflexivity. Qed.

Lemma cobj_unsubst : forall {t}, cobj t CType ->
  forall {o i c}, cobj (subst t i o) c ->  cobj o c.
Proof.
intros t Ht o;induction o; simpl; intros i c Ho;
try solve [inversion Ho; clear Ho; subst; eauto using cobj].
generalize Ho; clear Ho.
subst_lift_var; subst; intros Ho; [|inversion Ho; subst; auto using cobj].
pose proof (cobj_unlift Ho) as Hs; clear Ho.
rewrite (cobj_eq Hs Ht); auto using cobj.
Qed.

Lemma Hnth_cobj : forall {H a k}, Hnth H a k -> cobj H CTEnv -> cobj k CKind.
Proof.
induction 1; simpl; intros.
inversion H0; clear H0; subst; assumption.
inversion H1; clear H1; subst; auto.
Qed.

Lemma Ynth_cobj : forall {Y n p}, Ynth Y n p -> cobj Y CPEnv -> cobj p CProp.
Proof.
induction 1; simpl; intros.
inversion H; clear H; subst; assumption.
inversion H0; clear H0; subst; auto.
Qed.

Lemma Happ_cobj : forall {H1 H2 H1H2}, Happ H1 H2 H1H2 ->
  cobj H1 CTEnv -> cobj H2 CTEnv -> cobj H1H2 CTEnv.
Proof.
induction 1; simpl; intros; auto.
inversion H3; clear H3; subst.
auto using cobj.
Qed.

Lemma Happ_cobj_rev : forall {H1 H2 H1H2}, Happ H1 H2 H1H2 ->
  cobj H1H2 CTEnv -> cobj H1 CTEnv /\ cobj H2 CTEnv.
Proof.
induction 1; simpl; intros; auto using cobj.
inversion H0; clear H0; subst.
destruct (IHHapp H6).
auto using cobj.
Qed.

Lemma Yapp_cobj : forall {Y1 Y2 Y1Y2}, Yapp Y1 Y2 Y1Y2 ->
  cobj Y1 CPEnv -> cobj Y2 CPEnv -> cobj Y1Y2 CPEnv.
Proof.
induction 1; simpl; intros; auto.
inversion H1; clear H1; subst.
auto using cobj.
Qed.

Lemma Yapp_cobj_rev : forall {Y1 Y2 Y1Y2}, Yapp Y1 Y2 Y1Y2 ->
  cobj Y1Y2 CPEnv -> cobj Y1 CPEnv /\ cobj Y2 CPEnv.
Proof.
induction 1; simpl; intros; auto using cobj.
inversion H0; clear H0; subst.
pose proof (IHYapp H3) as [? ?].
auto using cobj.
Qed.

Lemma jeq_Hlength : forall {H1 H2}, jeq H1 H2 CTEnv -> Hlength H1 = Hlength H2.
Proof.
intros H1 H2 Hjeq.
remember CTEnv as c.
induction Hjeq; simpl; subst; try inversion Heqc.
(* EQrefl *) reflexivity.
(* EQsym *) apply eq_sym; auto.
(* EQtrans *) apply eq_trans with (Hlength o2); auto.
(* EQcongrHCons *) f_equal; auto.
Qed.

Lemma jeq_lift : forall {o1 o2 c}, jeq o1 o2 c ->
  forall d i, jeq (lift d i o1) (lift d i o2) c.
Proof.
induction 1; simpl; intros;
try match goal with
  | H : jeq _ _ CTEnv |- _ => repeat rewrite (jeq_Hlength H); clear H
end; eauto using jeq, cobj_lift.
Qed.

Lemma jeq_subst : forall {o1 o2 c}, jeq o1 o2 c ->
  forall s i, cobj s CType -> jeq (subst s i o1) (subst s i o2) c.
Proof.
induction 1; simpl; intros;
try match goal with
  | H : jeq _ _ CTEnv |- _ => repeat rewrite (jeq_Hlength H); clear H
end; eauto using jeq, cobj_lift, cobj_subst.
Qed.

Lemma jeq_class : forall {o1 o2 c}, jeq o1 o2 c -> cobj o1 c /\ cobj o2 c.
Proof.
induction 1; repeat
match goal with
  | H : jeq _ _ _ |- _ => clear H
  | H : _ /\ _ |- _ => destruct H
end; repeat
match goal with
  | H : ?P |- ?P => exact H
  | |- _ /\ _ => split
end; auto using cobj.
Qed.

Definition classjudg J :=
  match J with
    | JK k => cobj k CKind
    | JT t k => cobj t CType /\ cobj k CKind
    | JP Y0 Y1 p => cobj Y0 CPEnv /\ cobj Y1 CPEnv /\ cobj p CProp
    | JC Y0 Y1 H' t' t => cobj Y0 CPEnv /\ cobj Y1 CPEnv
                       /\ cobj H' CTEnv /\ cobj t' CType /\ cobj t CType
    | JH H' => cobj H' CTEnv
    | JG G => cobj G CAEnv
    | Jwf o c => cobj o c
  end.
Hint Unfold classjudg.

Lemma jobj_class : forall {v H J}, jobj v H J -> cobj H CTEnv /\ classjudg J.
Proof.
Ltac destruct_class :=
match goal with
  | H : jobj _ _ _ |- _ => clear H
  | H : jeq _ _ _ |- _ => destruct (jeq_class H); clear H
  | H : _ /\ _ |- _ => destruct H
end.
Ltac inversion_class :=
match goal with
  | H : cobj KStar _ |- _ => clear H
  | H : cobj KOne _ |- _ => clear H
  | H : cobj (KProd _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (KRes _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TVar _) _ |- _ => clear H
  | H : cobj (TArr _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TProd _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TFor _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TPi _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TMu _) _ |- _ => inversion H; clear H; subst
  | H : cobj TUnit _ |- _ => clear H
  | H : cobj (TPair _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TFst _) _ |- _ => inversion H; clear H; subst
  | H : cobj (TSnd _) _ |- _ => inversion H; clear H; subst
  | H : cobj PTrue _ |- _ => clear H
  | H : cobj (PAnd _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (PCoer _ _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (PExi _) _ |- _ => inversion H; clear H; subst
  | H : cobj (PFor _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj HNil _ |- _ => clear H
  | H : cobj (HCons _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj YNil _ |- _ => clear H
  | H : cobj (YCons _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj GNil _ |- _ => clear H
  | H : cobj (GCons _ _) _ |- _ => inversion H; clear H; subst
  | H : cobj (lift _ _ _) _ |- _ => pose proof (cobj_unlift H); clear H
  | H1 : cobj ?t CType, H2 : cobj (subst ?t _ _) _ |- _ =>
    pose proof (cobj_unsubst H1 H2); clear H2
  | H1 : Hnth ?H _ _, H2 : cobj ?H CTEnv |- _ =>
    pose proof (Hnth_cobj H1 H2); clear H1
  | H1 : Ynth ?Y _ _, H2 : cobj ?Y CPEnv |- _ =>
    pose proof (Ynth_cobj H1 H2); clear H1
  | Hx : Happ ?H1 ?H2 ?H1H2, Hy1 : cobj ?H1 CTEnv, Hy2 : cobj ?H2 CTEnv |- _ =>
    pose proof (Happ_cobj Hx Hy1 Hy2); clear Hx
  | Hx : Yapp ?Y1 ?Y2 ?Y1Y2, Hy : cobj ?Y1Y2 CPEnv |- _ =>
    pose proof (Yapp_cobj_rev Hx Hy) as [? ?]; clear Hx
end.
Ltac clean_class :=
match goal with
  | H1 : ?P, H2 : ?P |- _ => clear H2
  | H : _ -> _ |- _ => clear H (* warning *)
end.
Ltac solve_class :=
match goal with
  | H : ?P |- ?P => exact H
  | |- _ /\ _ => split
end.
Ltac crush_class :=
  repeat destruct_class; repeat inversion_class; repeat clean_class;
  try solve [repeat solve_class; auto using cobj, cobj_lift, cobj_subst].
induction 1; unfold classjudg in *; crush_class.
Qed.

Lemma Happ_HNil : forall H, cobj H CTEnv -> Happ HNil H H.
Proof.
intros H cH.
remember CTEnv as c.
induction cH; inversion Heqc; auto using Happ.
Qed.

Lemma Happ_HNil_eq : forall {H1 H2}, Happ HNil H1 H2 -> H1 = H2.
Proof.
intros H1 H2 H.
remember HNil as e.
induction H; subst; [reflexivity|].
rewrite (IHHapp eq_refl); reflexivity.
Qed.

Lemma Hnth_Hlength_exact : forall H1 k H2 HkH, Happ (HCons H1 k) H2 HkH ->
  Hnth HkH (Hlength H2) k.
Proof.
intros.
remember (HCons H1 k).
induction H; subst; simpl; auto using Hnth.
Qed.

Lemma Happ_HCons_move : forall {H2}, cobj H2 CTEnv ->
  forall {k H1 HkH}, Happ (HCons H1 k) H2 HkH -> cobj k CKind ->
  exists kH2, Happ H1 kH2 HkH /\ Hlength kH2 = 1 + Hlength H2 /\ cobj kH2 CTEnv.
Proof.
intros H2 ?.
remember CTEnv as c.
induction H; inversion Heqc; clear Heqc; simpl; intros.
{ inversion H; clear H; subst; exists (HCons HNil k); simpl; auto using Happ, cobj. }
inversion H3; clear H3; subst; clear IHcobj2.
destruct (IHcobj1 eq_refl _ _ _ H11 H4) as [? [? [? ?]]].
exists (HCons x k); simpl; auto using Happ, cobj.
Qed.

Lemma Hnth_lift : forall {a H1H3 k}, Hnth H1H3 a k ->
  forall {H1 H2 H1H2}, Happ H1 H2 H1H2 ->
  forall H3 H1H2H3, Happ H1 H3 H1H3 -> Happ H1H2 (lift (Hlength H2) 0 H3) H1H2H3 ->
  cobj H1 CTEnv -> cobj H2 CTEnv -> Hlength H3 <= a ->
  Hnth H1H2H3 (Hlength H2 + a) k.
Proof.
induction 1; simpl; intros.
- rewrite plus_0_r.
  inversion H4; clear H4; subst; simpl in *; [|exfalso; omega].
  inversion H5; clear H5; subst.
  apply Hnth_Hlength_exact with H; auto.
- rewrite <- plus_n_Sm.
  inversion H5; clear H5; subst; simpl in *.
  * inversion H6; clear H6; subst.
    inversion H7; clear H7; subst.
    destruct (Happ_HCons_move H8 H3 H10) as [kH2 [? [? ?]]].
    pose proof (IHHnth H kH2 H1H2H3 H1 HNil H1H2H3 (Happ0 H) (Happ0 H1H2H3) H6 H5).
    rewrite H4 in H7.
    apply H7; simpl; omega.
  * rewrite plus_0_r in H6.
    inversion H6; clear H6; subst.
    apply Hnth2.
    eapply IHHnth; eauto; omega.
Qed.

Lemma Hnth_Happ_lift : forall H1H3 a k, Hnth H1H3 a k ->
  forall H1 H2 H3 H1H2 H1H2H3, a < Hlength H3 ->
  Happ H1 H3 H1H3 ->
  Happ H1 H2 H1H2 ->
  Happ H1H2 (lift (Hlength H2) 0 H3) H1H2H3 ->
  Hnth H1H2H3 a (lift (Hlength H2) (Hlength H3 - (1 + a)) k).
Proof.
induction 1; simpl; intros.
{ inversion H4; clear H4; subst; simpl in *; try (exfalso; omega).
  rewrite <- minus_n_O.
  rewrite plus_0_r in H6.
  inversion H6; clear H6; subst.
  auto using Hnth. }
{ inversion H5; clear H5; subst; simpl in *; try (exfalso; omega).
  rewrite plus_0_r in H7.
  inversion H7; clear H7; subst.
  apply Hnth2.
  eapply IHHnth; eauto.
  omega. }
Qed.

Lemma Hnth_Happ_subst : forall H a k, Hnth H a k ->
  forall a0 b ab s k0, a < Hlength b ->
  Happ (HCons a0 k0) b H ->
  Happ a0 (subst s 0 b) ab ->
  Hnth ab a (subst s (Hlength b - (1 + a)) k).
Proof.
induction 1; simpl; intros.
{ inversion H1; clear H1; subst; simpl in *; try (exfalso; omega).
  rewrite <- minus_n_O.
  rewrite plus_0_r in H2.
  inversion H2; clear H2; subst.
  auto using Hnth. }
{ inversion H2; clear H2; subst; simpl in *; try (exfalso; omega).
  rewrite plus_0_r in H3.
  inversion H3; clear H3; subst.
  apply Hnth2.
  eapply IHHnth; eauto.
  omega. }
Qed.

Lemma jrec_lift : forall {d a t rec},
  jrec a t rec -> forall i, jrec a (lift d (a + 1 + i) t) rec.
Proof.
induction 1; simpl; intros; eauto using jrec.
(* RECVar *) subst_lift_var; eauto using jrec.
(* RECFor *)
  apply RECFor with (lift d (a + i) k'); [|apply IHjrec].
  subst k; unfold shift.
  rewrite lift_lift with (d1:=1); [|omega].
  f_equal; omega.
(* RECPi *)
  apply RECPi with (lift d (a + i) k'); [|apply IHjrec].
  subst k; unfold shift.
  rewrite lift_lift with (d1:=1); [|omega].
  f_equal; omega.
(* RECMu *)
  apply RECMu; auto.
  apply IHjrec2.
(* RECwf *)
  subst; unfold shift.
  replace (a + 1 + i) with (a + i + 1) by omega.
  rewrite <- lift_lift; [|omega].
  eapply RECwf; reflexivity.
Qed.

Lemma jrec_lift_0 : forall {d t rec},
  jrec 0 t rec -> forall i, jrec 0 (lift d (1 + i) t) rec.
Proof. intros; exact (jrec_lift H i). Qed.

Lemma jrec_subst : forall {s a t rec}, cobj s CType ->
  jrec a t rec -> forall i, jrec a (subst s (a + 1 + i) t) rec.
Proof.
induction 2; simpl; intros; eauto using jrec.
(* RECVar *) subst_lift_var; eauto using jrec.
(* RECFor *)
  apply RECFor with (subst s (a + i) k'); [|apply IHjrec].
  subst k; unfold shift.
  rewrite lift_subst2; [|auto|omega].
  f_equal; omega.
(* RECPi *)
  apply RECPi with (subst s (a + i) k'); [|apply IHjrec].
  subst k; unfold shift.
  rewrite lift_subst2; [|auto|omega].
  f_equal; omega.
(* RECMu *)
  apply RECMu; auto.
  apply IHjrec2.
(* RECwf *)
  subst; unfold shift.
  replace (a + 1 + i) with (1 + (a + i)) by omega.
  rewrite <- lift_subst2; [|auto|omega].
  eapply RECwf; reflexivity.
Qed.

Lemma jrec_subst_0 : forall {s t rec}, cobj s CType ->
  jrec 0 t rec -> forall i, jrec 0 (subst s (1 + i) t) rec.
Proof. intros. exact (jrec_subst H H0 i). Qed.

Lemma Ynth_lift : forall {Y n p}, Ynth Y n p -> forall d i, Ynth (lift d i Y) n (lift d i p).
Proof. induction 1; simpl; intros; auto using Ynth. Qed.

Lemma Ynth_subst : forall {Y n p}, Ynth Y n p ->
  forall s i, Ynth (subst s i Y) n (subst s i p).
Proof. induction 1; simpl; intros; auto using Ynth. Qed.

Lemma Hlength_Happ : forall {a b ab}, Happ a b ab -> Hlength ab = Hlength a + Hlength b.
Proof. induction 1; simpl; [|rewrite IHHapp]; omega. Qed.

Lemma Happ_lift : forall {a b ab}, Happ a b ab ->
  forall d i, Happ (lift d i a) (lift d (Hlength a + i) b) (lift d i ab).
Proof.
induction 1; simpl; intros; auto using Happ.
rewrite (Hlength_Happ H).
replace (Hlength H1 + (Hlength H2 + i)) with (Hlength H2 + Hlength H1 + i) by omega.
auto using Happ.
Qed.

Lemma Happ_subst : forall {a b ab}, Happ a b ab ->
  forall s i, Happ (subst s i a) (subst s (Hlength a + i) b) (subst s i ab).
Proof.
induction 1; simpl; intros; auto using Happ.
rewrite (Hlength_Happ H).
replace (Hlength H1 + (Hlength H2 + i)) with (Hlength H2 + Hlength H1 + i) by omega.
auto using Happ.
Qed.

Lemma Yapp_lift : forall {a b ab}, Yapp a b ab ->
  forall d i, Yapp (lift d i a) (lift d i b) (lift d i ab).
Proof. induction 1; simpl; intros; auto using Yapp. Qed.

Lemma Yapp_subst : forall {a b ab}, Yapp a b ab ->
  forall s i, Yapp (subst s i a) (subst s i b) (subst s i ab).
Proof. induction 1; simpl; intros; auto using Yapp. Qed.

Lemma Happ_exists : forall {b}, cobj b CTEnv -> forall a, exists ab, Happ a b ab.
Proof.
intros b cb.
remember CTEnv as e.
induction cb; inversion Heqe; clear Heqe; simpl; intros.
exists a; auto using Happ.
clear IHcb2.
destruct (IHcb1 eq_refl a) as [x Hx]; auto.
eauto using Happ.
Qed.

Lemma Happ_assoc_right : forall c, cobj c CTEnv ->
  forall a b ab bc abc, Happ a b ab -> Happ ab c abc -> Happ b c bc -> Happ a bc abc.
Proof.
intros c cc.
remember CTEnv as e.
induction cc; inversion Heqe; clear Heqe; intros.
inversion H1; clear H1; subst; inversion H0; clear H0; subst; assumption.
inversion H1; clear H1; subst; inversion H2; clear H2; subst.
eauto using Happ.
Qed.

Lemma Happ_assoc_left : forall c, cobj c CTEnv ->
  forall a b ab bc abc, Happ a b ab -> Happ a bc abc -> Happ b c bc -> Happ ab c abc.
Proof.
intros c cc.
remember CTEnv as e.
induction cc; inversion Heqe; clear Heqe; intros.
inversion H1; clear H1; subst; rewrite (Happ_eq H H0) in *; apply Happ0.
inversion H2; clear H2; subst; inversion H1; clear H1; subst.
eauto using Happ.
Qed.

Ltac apply_clear H I := let H' := fresh "H" in
  pose proof (H I) as H'; clear H; rename H' into H.

Ltac assert_clear H Hp :=
  match type of H with ?P -> _ => assert P as Hp; [clear H|apply_clear H Hp] end.

Ltac assert_goal H :=
  let Heq := fresh "Heq" in
  let Q := type of H in
  match goal with |- ?P => assert (P = Q) as Heq; [clear H|rewrite Heq; exact H] end.

Lemma Happ_Hlength_eq : forall d, cobj d CTEnv ->
  forall a b c e, cobj b CTEnv -> Happ a b e -> Happ c d e -> Hlength b = Hlength d ->
  a = c /\ b = d.
Proof.
intros d cd.
remember CTEnv as y.
induction cd; inversion Heqy; clear Heqy; simpl; intros.
{ inversion H1; clear H1; subst.
  inversion H; clear H; subst; inversion H2.
  inversion H0; clear H0; subst; auto. }
inversion H2; clear H2; subst.
inversion H0; clear H0; subst; inversion H3; clear H3; subst.
inversion H1; clear H1; subst.
destruct (IHcd1 eq_refl _ _ _ _ H4 H9 H10); subst; auto.
Qed.

Lemma Happ_Hlength_lt : forall z, cobj z CTEnv ->
  forall x b a e, cobj b CTEnv -> Happ x z e -> Happ a b e -> Hlength z < Hlength b ->
  exists w aw wz, Happ a w aw /\ Happ w z wz /\ x = aw /\ wz = b.
Proof.
intros z cz.
remember CTEnv as y.
induction cz; inversion Heqy; clear Heqy; simpl; intros.
{ inversion H0; clear H0; subst.
  exists b, e, b; auto using Happ. }
inversion H1; clear H1; subst.
inversion H0; clear H0; subst; [inversion H3|simpl in H3].
inversion H2; clear H2; subst.
destruct (IHcz1 eq_refl _ _ _ _ H4 H10 H9) as [w [aw [wz [? [? [? ?]]]]]]; [omega|].
exists w, aw, (HCons wz k); subst; auto using Happ.
Qed.

Lemma jobj_lift : forall {H1 H2 H1H2}, Happ H1 H2 H1H2 -> cobj H1H2 CTEnv ->
  forall {v H1H3 j}, jobj v H1H3 j ->
  forall H3 H1H2H3, Happ H1 H3 H1H3 -> cobj H3 CTEnv -> Happ H1H2 (lift (Hlength H2) 0 H3) H1H2H3 ->
  jobj v H1H2H3 (jlift (Hlength H2) (Hlength H3) j).
Proof.
induction 3; simpl in *; intros.
(* 62: JKexi *)
  apply JKexi.
  { apply IHjobj; auto. }
  intros mEv; apply (H6 mEv); auto.
(* 61: JTeq *)
  apply JTeq with (lift (Hlength H2) (Hlength H8) k); auto.
  apply (jeq_lift H5).
(* 60: JTVar *)
  subst_lift_var.
  (* 5: Hlength H6 <= a *)
    rewrite lift_fusion; [|omega..].
    rewrite <- plus_n_Sm.
    apply JTVar; eauto using Happ_cobj, cobj_lift.
    destruct (Happ_cobj_rev H H0).
    eapply Hnth_lift; eauto.
  (* 4: Hlength H6 > a *)
    remember (Hlength H6 - (1 + a)) as b.
    replace (Hlength H6) with (1 + a + b) by (subst b; omega).
    rewrite <- lift_lift_0.
    apply JTVar; eauto using Happ_cobj, cobj_lift.
    subst b.
    eapply Hnth_Happ_lift; eauto.
(* 59: JTArr *) apply JTArr; auto.
(* 58: JTOne *)
  apply JTOne; auto.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 57: JTProd *) apply JTProd; auto.
(* 58: JTVoid *)
  apply JTVoid; auto.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 55: JTSum *) apply JTSum; auto.
(* 54: JTFor *)
  apply JTFor; auto.
  apply (IHjobj (HCons H7 k)); simpl; eauto using Happ.
  destruct (jobj_class H6).
  inversion H11; clear H11; subst.
  auto using cobj.
  rewrite plus_0_r; auto using Happ.
(* 53: JTPi *)
  apply JTPi; auto.
  apply (IHjobj (HCons H7 k)); simpl; eauto using Happ.
  destruct (jobj_class H6).
  inversion H11; clear H11; subst.
  auto using cobj.
  rewrite plus_0_r; auto using Happ.
(* 52: JTMu *)
  apply JTMu; auto using jrec_lift_0.
  apply (IHjobj (HCons H7 KStar)); simpl; eauto using Happ, cobj.
(* 51: JTBot *)
  apply JTBot.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 50: JTTop *)
  apply JTTop.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 49: JTUnit *)
  apply JTUnit.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 48: JTPair *) apply JTPair; auto.
(* 47: JTFst *) eapply JTFst; eauto.
(* 46: JTSnd *) eapply JTSnd; eauto.
(* 45: JTPack *)
  destruct (jobj_class H3_) as [_ [? ?]].
  apply JTPack; auto.
  (* +3: *)
    intros mEv.
    apply (H5 mEv (HCons H6 k)); simpl; auto using Happ, cobj.
    rewrite plus_0_r; apply Happ1; auto.
  (* +2: *)
    rewrite <- lift_subst1_0; auto.
(* 44: JTUnpack *)
  apply JTUnpack with (lift (Hlength H2) (1 + Hlength H5) p); auto.
(* 43: JPeq *)
  apply JPeq with (lift (Hlength H2) (Hlength H8) p); auto using jeq_lift.
(* 42: JPVar *)
  apply JPVar with n; eauto using cobj_lift, Happ_cobj, Ynth_lift.
(* 41: JPTrue *)
  apply JPTrue; eauto using cobj_lift, Happ_cobj.
(* 40: JPAndPair *) apply JPAndPair; auto.
(* 39: JPAndFst *) apply JPAndFst with (lift (Hlength H2) (Hlength H5) p2); auto.
(* 38: JPAndSnd *) apply JPAndSnd with (lift (Hlength H2) (Hlength H5) p1); auto.
(* 37: JPExi *)
  apply JPExi with (lift (Hlength H2) (Hlength H7) t); auto using cobj_lift.
(* 36: JPForIntro *)
  apply JPForIntro; auto.
  pose proof (IHjobj (HCons H7 k) (HCons H1H2H3 (lift (Hlength H2) (Hlength H7) k))) as Hx.
  simpl in Hx.
  repeat rewrite <- lift_shift_0 in Hx.
  destruct (jobj_class H6) as [? _].
  inversion H11; clear H11; subst.
  apply Hx; auto using Happ, cobj.
  rewrite plus_0_r.
  apply Happ1; assumption.
(* 35: JPForElim *)
  destruct (jobj_class H3_) as [_ [? _]].
  rewrite lift_subst1_0; auto.
  apply JPForElim with (lift (Hlength H2) (Hlength H4) k); auto.
(* 34: JPRes *)
  destruct (jobj_class H6) as [_ [? _]].
  rewrite lift_subst1_0; auto using cobj.
  apply JPRes with (lift (Hlength H2) (Hlength H7) k); auto using cobj_lift.
(* 33: JPFix *) apply JPFix; auto.
(* 32: JPCoer *)
  destruct (jobj_class H3_) as [_ [_ [_ [cH' _]]]].
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H5) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  apply JPCoer with x; auto.
  destruct (@Happ_exists H') with (a := H5) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength H5 + Hlength H') with (Hlength H' + Hlength H5) in Heqy by omega.
  rewrite <- Heqy.
  assert (cobj y CTEnv) as cy.
  { apply (Happ_cobj Hy); auto. }
  apply IHjobj2; auto.
  { apply Happ_assoc_right with (ab:=H3) (b:=H5) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H5)
    (c:=lift (Hlength H2) (Hlength H5) H'); auto using cobj_lift.
  pose proof (Happ_lift Hy (Hlength H2) 0) as c1.
  rewrite plus_0_r in c1.
  exact c1.
(* 31: JCProp *) apply JCProp; auto.
(* 30: JCRefl *)
  apply JCRefl; eauto using cobj_lift, Happ_cobj.
(* 29: JCTrans *)
  destruct (jobj_class H3_0) as [_ [_ [_ ?]]].
  inversion H12; clear H12; subst.
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H8) H4)) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  apply JCTrans with (H2 := lift (Hlength H2) (Hlength H8) H4)
                      (H1 := lift (Hlength H2) (Hlength H4 + Hlength H8) H5)
                      (t2 := lift (Hlength H2) (Hlength H4 + Hlength H8) t2)
                      (HH2 := x); auto.
  { apply Happ_lift; auto. }
  clear IHjobj2.
  repeat rewrite lift_lift_0; repeat rewrite Hlength_lift.
  rewrite (Hlength_Happ H7).
  replace (Hlength H4 + Hlength H5 + Hlength H8)
          with (Hlength H5 + (Hlength H4 + Hlength H8)) by omega.
  destruct (@Happ_exists H4) with (a := H8); auto.
  replace (Hlength H4 + Hlength H8) with (Hlength x0); [|rewrite (Hlength_Happ H12); omega].
  apply IHjobj1; eauto using Happ_cobj, cobj_lift; [eapply Happ_assoc_right; eauto|].
  apply Happ_assoc_right with (c := lift (Hlength H2) (Hlength H8) H4)
        (b := lift (Hlength H2) 0 H8) (ab := H1H2H3); auto using cobj_lift.
  pose proof (Happ_lift H12 (Hlength H2) 0) as Hy.
  rewrite plus_0_r in Hy; exact Hy.
(* 28: JCWeak *)
  apply JCWeak with (H' := lift (Hlength H2) (Hlength H5) H').
  rewrite Hlength_lift.
  rewrite lift_lift_0.
  auto.
(* 27: JCArr *)
  destruct (jobj_class H3_0) as [_ [_ [_ cH's]]].
  inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H14) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists H') with (a := H14) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength H14 + Hlength H') with (Hlength H' + Hlength H14) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ H1 y HH') by (eapply Happ_assoc_right; eauto).
  assert (cobj y CTEnv) by (eapply Happ_cobj; eauto).
  pose proof (Happ_lift Hy (Hlength H2) 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ H1H2 (lift (Hlength H2) 0 y) x).
  { apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H14)
        (c:=lift (Hlength H2) (Hlength H14) H'); auto using cobj_lift. }
  apply JCArr with (Y0Y1 := lift (Hlength H2) (Hlength H14) Y0Y1) (HH' := x); auto.
  { apply Yapp_lift; auto. }
  { rewrite Hlength_lift.
    repeat rewrite lift_lift_0.
    rewrite <- Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 26: JCProd *)
  destruct (jobj_class H3_0) as [_ [_ [_ cH's]]].
  inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H12) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists H') with (a := H12) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength H12 + Hlength H') with (Hlength H' + Hlength H12) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ H1 y HH') by (eapply Happ_assoc_right; eauto).
  assert (cobj y CTEnv) by (eapply Happ_cobj; eauto).
  pose proof (Happ_lift Hy (Hlength H2) 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ H1H2 (lift (Hlength H2) 0 y) x).
  { apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H12)
        (c:=lift (Hlength H2) (Hlength H12) H'); auto using cobj_lift. }
  apply JCProd with (Y0Y1 := lift (Hlength H2) (Hlength H12) Y0Y1) (HH' := x); auto.
  { apply Yapp_lift; auto. }
  { rewrite Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 25: JCSum *)
  destruct (jobj_class H3_0) as [_ [_ [_ cH's]]].
  inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H12) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists H') with (a := H12) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength H12 + Hlength H') with (Hlength H' + Hlength H12) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ H1 y HH') by (eapply Happ_assoc_right; eauto).
  assert (cobj y CTEnv) by (eapply Happ_cobj; eauto).
  pose proof (Happ_lift Hy (Hlength H2) 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ H1H2 (lift (Hlength H2) 0 y) x).
  { apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H12)
        (c:=lift (Hlength H2) (Hlength H12) H'); auto using cobj_lift. }
  apply JCSum with (Y0Y1 := lift (Hlength H2) (Hlength H12) Y0Y1) (HH' := x); auto.
  { apply Yapp_lift; auto. }
  { rewrite Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 24: JCPi *)
  destruct (jobj_class H3_) as [_ cH'].
  destruct (jobj_class H3_0) as [_ [cs' ck']].
  apply cobj_unlift in ck'.
  destruct (jobj_class H3_1) as [ck _]; inversion ck; clear ck; subst.
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H11) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists (lift 1 0 (lift (Hlength H2) (Hlength H11) H'))) with
    (a := HCons H1H2H3 (lift (Hlength H2) (Hlength H11) k)) as [z Hz]; auto using cobj_lift.
  destruct (@Happ_exists H') with (a := H11) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength H11 + Hlength H') with (Hlength H' + Hlength H11) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ H1 y HH').
  { apply Happ_assoc_right with (ab:=H3) (b:=H11) (c:=H'); auto. }
  assert (cobj y CTEnv) by (eapply Happ_cobj; eauto).
  pose proof (Happ_lift Hy (Hlength H2) 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ H1H2 (lift (Hlength H2) 0 y) x).
  { apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H11)
        (c:=lift (Hlength H2) (Hlength H11) H'); auto using cobj_lift. }
  apply JCPi with (Y0Y1 := lift (Hlength H2) (Hlength H11) Y0Y1) (HH' := x)
    (HaH' := z) (s' := lift (Hlength H2) (1 + Hlength y) s') ; auto.
  { apply Yapp_lift; auto. }
  { intros mSv.
    replace (S (Hlength y)) with (Hlength (HCons y k')) by (simpl; omega).
    apply (H10 mSv); auto using cobj, cobj_lift, Happ.
    simpl; rewrite plus_0_r.
    apply Happ1; auto. }
  { rewrite Hlength_lift.
    rewrite lift_lift; [|rewrite Heqy; omega].
    destruct (@Happ_exists (lift 1 0 H')) with (a := HCons H11 k) as [w Hw]; auto using cobj_lift.
    pose proof (Hlength_Happ Hw) as Heqw.
    rewrite Hlength_lift in Heqw.
    replace (1 + Hlength y) with (Hlength w) by (rewrite Heqw; simpl; omega).
    replace (Hlength y + 1) with (Hlength w) by (rewrite Heqw; simpl; omega).
    assert (cobj w CTEnv) by (eapply Happ_cobj; eauto using cobj, cobj_lift).
    apply IHjobj2; auto.
    { apply Happ_assoc_right with (ab:=HCons H3 k) (b:=HCons H11 k) (c:=lift 1 0 H');
        auto using Happ, cobj_lift. }
    apply Happ_assoc_right with (ab:=HCons H1H2H3 (lift (Hlength H2) (Hlength H11) k))
          (b:=HCons (lift (Hlength H2) 0 H11) (lift (Hlength H2) (Hlength H11) k))
          (c:=lift 1 0 (lift (Hlength H2) (Hlength H11) H'));
      auto using Happ, cobj_lift.
    pose proof (Happ_lift Hw (Hlength H2) 0) as Hwl.
    simpl in Hwl.
    rewrite plus_0_r in Hwl.
    rewrite lift_lift_0.
    exact Hwl. }
  { apply_clear IHjobj3 (HCons H11 k).
    apply_clear IHjobj3 (HCons H1H2H3 (lift (Hlength H2) (Hlength H11) k)).
    assert_clear IHjobj3 Hp1; [auto using Happ|].
    assert_clear IHjobj3 cH11k; [auto using cobj|].
    assert_clear IHjobj3 Hp2; [simpl; rewrite plus_0_r; auto using Happ|].
    assert_goal IHjobj3; simpl.
    f_equal.
    f_equal; [rewrite lift_lift_0; reflexivity..|].
    repeat rewrite Hlength_lift.
    rewrite lift_subst1_0; auto.
    rewrite Heqy.
    f_equal; [f_equal; omega|].
    rewrite lift_lift; [|omega].
    f_equal; omega. }
(* 23: JCGen *)
  apply JCGen; auto using cobj_lift.
  intros mSv.
  apply_clear H9 mSv.
  apply_clear H9 (HCons H10 k).
  apply_clear H9 (HCons H1H2H3 (lift (Hlength H2) (Hlength H10) k)).
  assert_clear H9 Ha1; [auto using Happ|].
  destruct (jobj_class H7) as [_ ck].
  assert_clear H9 cH10k; [auto using cobj|].
  apply H9.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 22: JCInst *)
  destruct (jobj_class H9) as [_ [cs ck]].
  rewrite lift_subst1_0; auto.
  apply JCInst; auto using cobj_lift.
  intros mSv.
  apply_clear H8 mSv.
  apply_clear H8 (HCons H10 k).
  apply_clear H8 (HCons H1H2H3 (lift (Hlength H2) (Hlength H10) k)).
  assert_clear H8 Ha1; [auto using Happ|].
  assert_clear H8 cH10k; [auto using cobj|].
  apply H8.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 21: JCUnfold *)
  rewrite lift_subst1_0; auto using cobj.
  destruct (Happ_cobj_rev H13 H4).
  assert (cobj H1H2H3 CTEnv).
  { apply (Happ_cobj H15); auto using cobj_lift. }
  apply JCUnfold; auto using cobj_lift, jrec_lift_0.
  intros mSv.
  apply_clear H10 mSv.
  apply_clear H10 (HCons H12 KStar).
  apply H10; auto using Happ, cobj.
  simpl; auto using Happ.
(* 20: JCFold *)
  destruct (jobj_class H7) as [_ [ct _]].
  rewrite lift_subst1_0; auto using cobj.
  apply JCFold; auto using cobj_lift, jrec_lift_0.
  apply_clear IHjobj (HCons H9 KStar).
  apply IHjobj; auto using Happ, cobj.
  simpl; auto using Happ.
(* 19: JCTop *)
  destruct (Happ_cobj_rev H11 H4).
  assert (cobj H1H2H3 CTEnv).
  { apply (Happ_cobj H13); auto using cobj_lift. }
  apply JCTop; auto using cobj_lift.
(* 18: JCBot *)
  apply JCBot; auto using cobj_lift.
(* 17: JHNil *)
  apply JHNil.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 16: JHCons *)
  destruct (jobj_class H3_) as [_ ?].
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H5) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists  H') with (a := H5) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength H5 + Hlength H') with (Hlength H' + Hlength H5) in Heqw by omega.
  apply JHCons with (HH':=x); auto.
  rewrite <- Heqw.
  apply IHjobj2; eauto using Happ_cobj.
  { apply Happ_assoc_right with (ab:=H3) (b:=H5) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H5)
        (c:=lift (Hlength H2) (Hlength H5) H'); auto using cobj_lift.
  pose proof (Happ_lift Hw (Hlength H2) 0) as Hwl.
  rewrite plus_0_r in Hwl; exact Hwl.
(* 15: JGNil *)
  apply JGNil.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 14: JGCons *)
  apply JGCons; auto.
(* 13: WKStar *)
  apply WKStar.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 12: WKOne *)
  apply WKOne.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 11: WKProd *)
  apply WKProd; auto.
(* 10: WKRes *)
  apply WKRes; auto.
  apply_clear IHjobj2 (HCons H4 k).
  apply_clear IHjobj2 (HCons H1H2H3 (lift (Hlength H2) (Hlength H4) k)).
  assert_clear IHjobj2 Ha1; [auto using Happ|].
  destruct (jobj_class H3_) as [_ ?].
  assert_clear IHjobj2 cH4k; [auto using cobj|].
  apply IHjobj2.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 9: WPTrue *)
  apply WPTrue.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 8: WPAnd *)
  apply WPAnd; auto.
(* 7: WPCoer *)
  destruct (jobj_class H3_) as [_ cH'].
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H7) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists H') with (a := H7) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength H7 + Hlength H') with (Hlength H' + Hlength H7) in Heqw by omega.
  assert (Happ H1 w HH').
  { apply Happ_assoc_right with (ab:=H3) (b:=H7) (c:=H'); auto. }
  assert (Happ H1H2 (lift (Hlength H2) 0 w) x).
  { apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H7)
          (c:=lift (Hlength H2) (Hlength H7) H'); auto using cobj_lift.
    pose proof (Happ_lift Hw (Hlength H2) 0) as Hwl.
    rewrite plus_0_r in Hwl; exact Hwl. }
  rewrite <- Heqw.
  apply WPCoer with (HH':=x); eauto using Happ_cobj.
(* 6: WPExi *)
  apply WPExi; auto.
(* 5: WPFor *)
  apply WPFor; auto.
  apply_clear IHjobj2 (HCons H4 k).
  apply_clear IHjobj2 (HCons H1H2H3 (lift (Hlength H2) (Hlength H4) k)).
  assert_clear IHjobj2 Ha1; [auto using Happ|].
  destruct (jobj_class H3_) as [_ ck].
  assert_clear IHjobj2 cH4k; [auto using cobj|].
  apply IHjobj2.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 4: WHNil *)
  apply WHNil.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 3: WHCons *)
  destruct (jobj_class H3_) as [_ ?].
  destruct (@Happ_exists (lift (Hlength H2) (Hlength H5) H')) with (a := H1H2H3) as [x Hx];
    auto using cobj_lift.
  destruct (@Happ_exists  H') with (a := H5) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength H5 + Hlength H') with (Hlength H' + Hlength H5) in Heqw by omega.
  apply WHCons with (HH':=x); auto.
  rewrite <- Heqw.
  apply IHjobj2; eauto using Happ_cobj.
  { apply Happ_assoc_right with (ab:=H3) (b:=H5) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=H1H2H3) (b:=lift (Hlength H2) 0 H5)
        (c:=lift (Hlength H2) (Hlength H5) H'); auto using cobj_lift.
  pose proof (Happ_lift Hw (Hlength H2) 0) as Hwl.
  rewrite plus_0_r in Hwl; exact Hwl.
(* 2: WYNil *)
  apply WYNil.
  apply (Happ_cobj H8); auto using cobj_lift.
(* 1: WYCons *)
  apply WYCons; auto.
Qed.

Lemma jobj_lift_0 : forall {H1 H2 H1H2 v j}, Happ H1 H2 H1H2 -> cobj H1H2 CTEnv ->
  jobj v H1 j -> jobj v H1H2 (jlift (Hlength H2) 0 j).
Proof.
intros.
replace 0 with (Hlength HNil) by reflexivity.
apply (jobj_lift H H0 H3); auto using Happ, cobj.
Qed.

Lemma jobj_shift_0 : forall {H k v j}, jobj v H j -> cobj k CKind ->
  jobj v (HCons H k) (jlift 1 0 j).
Proof.
intros.
replace 1 with (Hlength (HCons HNil k)) by reflexivity.
replace 0 with (Hlength HNil) by reflexivity.
destruct (jobj_class H0) as [? _].
apply (@jobj_lift_0 H (HCons HNil k) (HCons H k)); auto using Happ, cobj.
Qed.

Lemma Hnth_HCons_Hlength : forall b, cobj b CTEnv ->
  forall H a0 k0 a k s ab, Hnth H (S a) k -> Happ (HCons a0 k0) b H ->
  Happ a0 (subst s 0 b) ab -> Hlength b <= a ->
  Hnth ab a k.
Proof.
intros b cb.
remember CTEnv as c.
induction cb; inversion Heqc; clear Heqc; simpl; intros.
{ inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  assumption. }
{ rewrite plus_0_r in H3.
  inversion H3; clear H3; subst.
  destruct a; [inversion H4|].
  apply Hnth2.
  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  eapply IHcb1; eauto.
  omega. }
Qed.

Lemma jeq_KStar_rev_aux : forall o1 o2 c, jeq o1 o2 c -> c = CKind -> (o1 = KStar <-> o2 = KStar).
Proof.
induction 1; intros Heqc; inversion Heqc; clear Heqc;
split; intros Heq; inversion Heq; clear Heq; subst;
repeat match goal with
  | H : CKind = CKind -> (_ <-> _) |- _ => destruct (H eq_refl); clear H
end; auto.
Qed.

Lemma jeq_KStar_rev : forall k, jeq KStar k CKind -> k = KStar.
Proof.
intros k jk.
apply (jeq_KStar_rev_aux KStar k CKind jk eq_refl); auto.
Qed.

Lemma jeq_KOne_rev_aux : forall o1 o2 c, jeq o1 o2 c -> c = CKind -> (o1 = KOne <-> o2 = KOne).
Proof.
induction 1; intros Heqc; inversion Heqc; clear Heqc;
split; intros Heq; inversion Heq; clear Heq; subst;
repeat match goal with
  | H : CKind = CKind -> (_ <-> _) |- _ => destruct (H eq_refl); clear H
end; auto.
Qed.

Lemma jeq_KOne_rev : forall k, jeq KOne k CKind -> k = KOne.
Proof.
intros k jk.
apply (jeq_KOne_rev_aux KOne k CKind jk eq_refl); auto.
Qed.

Definition jeq_agree_KProd o1 o2 :=
  match o1, o2 with
    | KProd a1 b1, KProd a2 b2 => jeq a1 a2 CKind /\ jeq b1 b2 CKind
    | KProd _ _, _ => False
    | _, KProd _ _ => False
    | _, _ => True
  end.

Lemma jeq_KProd_rev_aux : forall o1 o2 c, jeq o1 o2 c -> c = CKind -> jeq_agree_KProd o1 o2.
Proof.
induction 1; intros Heqc; inversion Heqc; clear Heqc; subst; simpl; auto.
{ destruct o; try exact I.
  inversion H; clear H; subst.
  split; apply EQrefl; auto. }
{ apply_clear IHjeq (eq_refl CKind).
  destruct o1; destruct o2; try first [exact I|exfalso; exact IHjeq].
  destruct IHjeq.
  split; apply EQsym; auto. }
apply_clear IHjeq1 (eq_refl CKind).
apply_clear IHjeq2 (eq_refl CKind).
destruct o1; destruct o3; try exact I;
destruct o2; simpl in *; try (exfalso; assumption).
destruct IHjeq1.
destruct IHjeq2.
split; eapply EQtrans; eauto.
Qed.

Lemma jeq_KProd_rev : forall k' k1 k2, jeq (KProd k1 k2) k' CKind ->
  exists k1' k2', k' = KProd k1' k2' /\ jeq k1 k1' CKind /\ jeq k2 k2' CKind.
Proof.
intros k' k1 k2 jk.
pose proof (jeq_KProd_rev_aux (KProd k1 k2) k' CKind jk eq_refl).
destruct k'; try (exfalso; exact H).
destruct H.
exists k'1, k'2; auto.
Qed.

Definition jeq_agree_KRes o1 o2 :=
  match o1, o2 with
    | KRes a1 b1, KRes a2 b2 => jeq a1 a2 CKind /\ jeq b1 b2 CProp
    | KRes _ _, _ => False
    | _, KRes _ _ => False
    | _, _ => True
  end.

Lemma jeq_KRes_rev_aux : forall o1 o2 c, jeq o1 o2 c -> c = CKind -> jeq_agree_KRes o1 o2.
Proof.
induction 1; intros Heqc; inversion Heqc; clear Heqc; subst; simpl; auto.
{ destruct o; try exact I.
  inversion H; clear H; subst.
  split; apply EQrefl; auto. }
{ apply_clear IHjeq (eq_refl CKind).
  destruct o1; destruct o2; try first [exact I|exfalso; exact IHjeq].
  destruct IHjeq.
  split; apply EQsym; auto. }
apply_clear IHjeq1 (eq_refl CKind).
apply_clear IHjeq2 (eq_refl CKind).
destruct o1; destruct o3; try exact I;
destruct o2; simpl in *; try (exfalso; assumption).
destruct IHjeq1.
destruct IHjeq2.
split; eapply EQtrans; eauto.
Qed.

Lemma jeq_KRes_rev : forall k0 k p, jeq (KRes k p) k0 CKind ->
  exists k' p', k0 = KRes k' p' /\ jeq k k' CKind /\ jeq p p' CProp.
Proof.
intros k0 k p jk.
pose proof (jeq_KRes_rev_aux (KRes k p) k0 CKind jk eq_refl).
destruct k0; try (exfalso; exact H).
destruct H.
exists k0_1, k0_2; auto.
Qed.

Lemma jobj_subst_aux1 : forall H ab a k b s, cobj H CTEnv ->
  Happ (HCons a k) b H -> Happ a (subst s 0 b) ab -> cobj s CType ->
  cobj ab CTEnv.
Proof.
intros.
destruct (Happ_cobj_rev H1 H0) as [c1 ?].
inversion c1; clear c1; subst.
apply (Happ_cobj H2); auto using cobj_subst.
Qed.

Lemma jobj_subst : forall {v a k s akb j}, jobj v a (JT s k) -> jobj v akb j -> cobj akb CTEnv ->
  forall {b ab}, Happ (HCons a k) b akb -> Happ a (subst s 0 b) ab ->
  jobj v ab (jsubst s (Hlength b) j).
Proof.
intros v a k s akb j Hs.
destruct (jobj_class Hs) as [_ [cs _]].
induction 1; simpl in *; intros.
(* 62: JKexi *)
  apply JKexi.
  { eapply IHjobj; eauto. }
  intros mEv; apply (H2 mEv); auto.
(* 61: JTeq *)
  apply JTeq with (k:= subst s (Hlength b) k0); eauto.
  destruct (jobj_class Hs) as [_ [? _]].
  apply (jeq_subst H1); auto.
(* 60: JTVar *)
  destruct (Happ_cobj_rev H3 H0) as [_ ?].
  assert (cobj ab CTEnv) as cab by eauto using jobj_subst_aux1.
  subst_lift_var.
  (* 6: a0 < Hlength b *)
    remember (Hlength b - (1 + a0)) as c.
    replace (Hlength b) with (1 + a0 + c) by (subst c; omega).
    rewrite <- lift_subst2; [|assumption|omega].
    apply JTVar; auto.
    subst c.
    eapply Hnth_Happ_subst; eauto.
  (* 5: a0 = Hlength b *)
    subst a0.
    pose proof (jobj_lift_0 H4 cab Hs) as Hx.
    rewrite (Hlength_subst s cs) in Hx.
    simpl in Hx.
    pose proof (Hnth_Hlength_exact _ _ _ _ H3).
    rewrite (Hnth_eq H1 H6) in *.
    rewrite subst_lift; [assumption|omega..].
  (* 4: Hlength b < a0 *)
    rewrite subst_lift; [|omega..].
    destruct a0; [inversion l|].
    replace (S a0 - 1) with a0 by omega.
    apply JTVar; auto.
    apply (Hnth_HCons_Hlength b H5 H a k a0 k0 s ab); auto; omega.
(* 59: JTArr *) apply JTArr; auto.
(* 58: JTOne *) apply JTOne; eauto using jobj_subst_aux1.
(* 57: JTProd *) apply JTProd; auto.
(* 56: JTVoid *) apply JTVoid; eauto using jobj_subst_aux1.
(* 55: JTSum *) apply JTSum; auto.
(* 54: JTFor *)
  apply JTFor; auto.
  destruct (jobj_class H2) as [c1 _]; inversion c1; clear c1; subst.
  assert_clear IHjobj Hc1; [auto using cobj|].
  apply (IHjobj (HCons b k0)); simpl; eauto using Happ.
  rewrite plus_0_r; auto using Happ.
(* 53: JTPi *)
  apply JTPi; auto.
  destruct (jobj_class H2) as [c1 _]; inversion c1; clear c1; subst.
  assert_clear IHjobj Hc1; [auto using cobj|].
  apply (IHjobj (HCons b k0)); simpl; eauto using Happ.
  rewrite plus_0_r; auto using Happ.
(* 52: JTMu *)
  apply JTMu; auto using jrec_subst_0.
  assert_clear IHjobj Hc1; [auto using cobj|].
  apply (IHjobj (HCons b KStar)); simpl; eauto using Happ, cobj.
(* 51: JTBot *)
  apply JTBot; eauto using jobj_subst_aux1.
(* 50: JTTop *)
  apply JTTop; eauto using jobj_subst_aux1.
(* 49: JTUnit *)
  apply JTUnit; eauto using jobj_subst_aux1.
(* 48: JTPair *) apply JTPair; auto.
(* 47: JTFst *) eapply JTFst; eauto.
(* 46: JTSnd *) eapply JTSnd; eauto.
(* 45: JTPack *)
  destruct (jobj_class H2) as [_ [ct ck0]].
  apply JTPack; auto.
  (* +3: *)
    intros mEv.
    apply_clear H1 mEv.
    assert_clear H1 c1; [auto using cobj|].
    apply_clear H1 (HCons b k0).
    apply H1; simpl; auto using Happ, cobj.
    rewrite plus_0_r; apply Happ1; auto.
  (* +2: *)
    rewrite <- subst_subst_0; auto.
(* 44: JTUnpack *)
  apply JTUnpack with (subst s (1 + Hlength b) p); auto.
(* 43: JPeq *)
  apply JPeq with (subst s (Hlength b) p); auto using jeq_subst.
(* 42: JPVar *)
  apply JPVar with n; eauto using cobj_subst, Happ_cobj, jobj_subst_aux1, Ynth_subst.
(* 41: JPTrue *)
  apply JPTrue; eauto using cobj_subst, Happ_cobj, jobj_subst_aux1.
(* 40: JPAndPair *) apply JPAndPair; auto.
(* 39: JPAndFst *) apply JPAndFst with (subst s (Hlength b) p2); auto.
(* 38: JPAndSnd *) apply JPAndSnd with (subst s (Hlength b) p1); auto.
(* 37: JPExi *)
  apply JPExi with (subst s (Hlength b) t); auto using cobj_subst.
(* 36: JPForIntro *)
  destruct (jobj_class H2) as [c1 _]; inversion c1; clear c1; subst.
  apply JPForIntro; auto.
  assert_clear IHjobj c2; [auto using cobj|].
  pose proof (IHjobj (HCons b k0) (HCons ab (subst s (Hlength b) k0))) as Hx.
  simpl in Hx.
  rewrite plus_0_r in Hx.
  do 2 rewrite <- lift_subst2_0 in Hx; auto.
  apply Hx; auto using Happ.
(* 35: JPForElim *)
  destruct (jobj_class H0) as [_ [ct _]].
  rewrite subst_subst_0; auto.
  apply JPForElim with (subst s (Hlength b) k0); auto.
(* 34: JPRes *)
  destruct (jobj_class H2) as [_ [ct _]].
  rewrite subst_subst_0; auto using cobj.
  apply JPRes with (subst s (Hlength b) k0); auto using cobj_subst.
(* 33: JPFix *) apply JPFix; auto.
(* 32: JPCoer *)
  destruct (jobj_class H1) as [_ [_ [_ [cH' _]]]].
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  apply JPCoer with x; auto.
  destruct (@Happ_exists H') with (a := b) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqy by omega.
  rewrite <- Heqy.
  assert (cobj HH' CTEnv) as cHH'.
  { apply (Happ_cobj H0); auto. }
  apply IHjobj2; auto.
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
    (c:=subst s (Hlength b) H'); auto using cobj_subst.
  pose proof (Happ_subst Hy s 0) as c1.
  rewrite plus_0_r in c1.
  exact c1.
(* 31: JCProp *) apply JCProp; auto.
(* 30: JCRefl *)
  apply JCRefl; eauto using cobj_subst, Happ_cobj, jobj_subst_aux1.
(* 29: JCTrans *)
  destruct (jobj_class H5) as [_ [_ [_ c1]]]; inversion c1; clear c1; subst.
  destruct (@Happ_exists (subst s (Hlength b) H2)) with (a := ab) as [x Hx];
    auto using cobj_subst.
  apply JCTrans with (H2 := subst s (Hlength b) H2)
                      (H1 := subst s (Hlength H2 + Hlength b) H1)
                      (t2 := subst s (Hlength H2 + Hlength b) t2)
                      (HH2 := x); auto.
  { apply Happ_subst; auto. }
  clear IHjobj2.
  repeat (rewrite Hlength_subst; auto).
  do 2 (rewrite lift_subst2; [|auto|omega]).
  rewrite (Hlength_Happ H3).
  replace (Hlength H2 + Hlength H1 + Hlength b)
          with (Hlength H1 + (Hlength H2 + Hlength b)) by omega.
  destruct (@Happ_exists H2) with (a := b) as [y Hy]; auto.
  replace (Hlength H2 + Hlength b) with (Hlength y); [|rewrite (Hlength_Happ Hy); omega].
  apply IHjobj1; eauto using Happ_cobj, cobj_subst; [eapply Happ_assoc_right; eauto|].
  apply Happ_assoc_right with (c := subst s (Hlength b) H2)
        (b := subst s 0 b) (ab := ab); auto using cobj_subst.
  pose proof (Happ_subst Hy s 0) as c1.
  rewrite plus_0_r in c1; exact c1.
(* 28: JCWeak *)
  apply JCWeak with (H' := subst s (Hlength b) H').
  rewrite Hlength_subst; auto.
  rewrite lift_subst2; [|auto|omega].
  auto.
(* 27: JCArr *)
  destruct (jobj_class H11) as [_ [_ [_ cH's]]]; inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ (HCons a k) y HH') by (eapply Happ_assoc_right; eauto).
  assert (cobj HH' CTEnv) by (apply (Happ_cobj H1); auto).
  pose proof (Happ_subst Hy s 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ a (subst s 0 y) x).
  { apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst. }
  apply JCArr with (Y0Y1 := subst s (Hlength b) Y0Y1) (HH' := x); auto.
  { apply Yapp_subst; auto. }
  { rewrite Hlength_subst; auto.
    repeat (rewrite lift_subst2; [|auto|omega]).
    rewrite <- Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 26: JCProd *)
  destruct (jobj_class H9) as [_ [_ [_ cH's]]]; inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ (HCons a k) y HH') by (eapply Happ_assoc_right; eauto).
  assert (cobj HH' CTEnv) by (apply (Happ_cobj H1); auto).
  pose proof (Happ_subst Hy s 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ a (subst s 0 y) x).
  { apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst. }
  apply JCProd with (Y0Y1 := subst s (Hlength b) Y0Y1) (HH' := x); auto.
  { apply Yapp_subst; auto. }
  { rewrite Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 25: JCSum *)
  destruct (jobj_class H9) as [_ [_ [_ cH's]]]; inversion cH's; clear cH's; subst.
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ (HCons a k) y HH').
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  assert (cobj HH' CTEnv) by (apply (Happ_cobj H1); auto).
  pose proof (Happ_subst Hy s 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ a (subst s 0 y) x).
  { apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst. }
  apply JCSum with (Y0Y1 := subst s (Hlength b) Y0Y1) (HH' := x); auto.
  { apply Yapp_subst; auto. }
  { rewrite Heqy.
    apply IHjobj1; auto. }
  { rewrite Heqy.
    apply IHjobj2; auto. }
(* 24: JCPi *)
  destruct (jobj_class H5) as [_ cH'].
  destruct (jobj_class H8) as [_ [cs' ck']].
  apply cobj_unlift in ck'.
  destruct (jobj_class H9) as [ck0 _]; inversion ck0; clear ck0; subst.
  destruct (Happ_cobj_rev H11) as [_ cb]; auto.
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists (lift 1 0 (subst s (Hlength b) H'))) with
    (a := HCons ab (subst s (Hlength b) k0)) as [z Hz]; auto using cobj_lift, cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [y Hy]; auto.
  pose proof (Hlength_Happ Hy) as Heqy.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqy by omega.
  rewrite <- Heqy.
  assert (Happ (HCons a k) y HH') as HHH'.
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  assert (cobj HH' CTEnv) by (apply (Happ_cobj H1); eauto).
  pose proof (Happ_subst Hy s 0) as Hyl.
  rewrite plus_0_r in Hyl.
  assert (Happ a (subst s 0 y) x).
  { apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst. }
  apply JCPi with (Y0Y1 := subst s (Hlength b) Y0Y1) (HH' := x)
    (HaH' := z) (s' := subst s (1 + Hlength y) s') ; auto.
  { apply Yapp_subst; auto. }
  { intros mSv.
    replace (S (Hlength y)) with (Hlength (HCons y k')) by (simpl; omega).
    apply (H7 mSv); auto using cobj, cobj_subst, Happ.
    simpl; rewrite plus_0_r.
    apply Happ1; auto. }
  { rewrite Hlength_subst; auto.
    rewrite lift_subst2; [|auto|omega].
    destruct (@Happ_exists (lift 1 0 H')) with (a := HCons b k0) as [w Hw]; auto using cobj_lift.
    pose proof (Hlength_Happ Hw) as Heqw.
    rewrite Hlength_lift in Heqw.
    replace (1 + Hlength y) with (Hlength w) by (rewrite Heqw; simpl; omega).
    assert (cobj HaH' CTEnv) by (eapply Happ_cobj; eauto using cobj, cobj_lift).
    apply IHjobj2; auto.
    { apply Happ_assoc_right with (ab:=HCons H k0) (b:=HCons b k0) (c:=lift 1 0 H');
        auto using Happ, cobj_lift. }
    apply Happ_assoc_right with (ab:=HCons ab (subst s (Hlength b) k0))
          (b:=HCons (subst s 0 b) (subst s (Hlength b) k0))
          (c:=lift 1 0 (subst s (Hlength b) H'));
      auto using Happ, cobj_lift, cobj_subst.
    pose proof (Happ_subst Hw s 0) as Hwl.
    simpl in Hwl.
    rewrite plus_0_r in Hwl.
    rewrite lift_subst2; [|auto|omega].
    exact Hwl. }
  { assert_clear IHjobj3 c1; [auto using cobj|].
    apply_clear IHjobj3 (HCons b k0).
    apply_clear IHjobj3 (HCons ab (subst s (Hlength b) k0)).
    assert_clear IHjobj3 Hp1; [auto using Happ|].
    assert_clear IHjobj3 Hp2; [simpl; rewrite plus_0_r; auto using Happ|].
    assert_goal IHjobj3; simpl.
    f_equal.
    f_equal; [rewrite lift_subst2; auto; omega..|].
    repeat (rewrite Hlength_subst; auto).
    repeat rewrite Hlength_lift.
    rewrite subst_subst_0; auto.
    rewrite Heqy.
    f_equal; [f_equal; omega|].
    rewrite lift_subst2; [|auto|omega].
    f_equal; omega. }
(* 23: JCGen *)
  apply JCGen; auto using cobj_subst.
  intros mSv.
  destruct (jobj_class H3) as [_ ck0].
  apply_clear H5 mSv.
  assert_clear H5 c1; [auto using cobj|].
  apply_clear H5 (HCons b k0).
  apply_clear H5 (HCons ab (subst s (Hlength b) k0)).
  assert_clear H5 Ha1; [auto using Happ|].
  apply H5.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 22: JCInst *)
  destruct (jobj_class H5) as [_ [cs0 ck0]].
  rewrite subst_subst_0; auto.
  apply JCInst; auto using cobj_subst.
  intros mSv.
  apply_clear H4 mSv.
  assert_clear H4 c1; [auto using cobj|].
  apply_clear H4 (HCons b k0).
  apply_clear H4 (HCons ab (subst s (Hlength b) k0)).
  assert_clear H4 Ha1; [auto using Happ|].
  apply H4.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 21: JCUnfold *)
  rewrite subst_subst_0; auto using cobj.
  apply JCUnfold; eauto using cobj_subst, jrec_subst_0, jobj_subst_aux1.
  intros mSv.
  apply_clear H6 mSv.
  assert_clear H6 c1; [auto using cobj|].
  apply_clear H6 (HCons b KStar).
  apply H6; auto using Happ, cobj.
  simpl; auto using Happ.
(* 20: JCFold *)
  destruct (jobj_class H3) as [_ [ct _]].
  rewrite subst_subst_0; auto using cobj.
  apply JCFold; auto using cobj_subst, jrec_subst_0.
  assert_clear IHjobj c1; [auto using cobj|].
  apply_clear IHjobj (HCons b KStar).
  apply IHjobj; auto using Happ, cobj.
  simpl; auto using Happ.
(* 19: JCTop *)
  apply JCTop; eauto using cobj_subst, jobj_subst_aux1.
(* 18: JCBot *)
  apply JCBot; auto using cobj_subst.
(* 17: JHNil *)
  apply JHNil; eauto using jobj_subst_aux1.
(* 16: JHCons *)
  destruct (jobj_class H1) as [_ cH'].
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqw by omega.
  apply JHCons with (HH':=x); auto.
  rewrite <- Heqw.
  apply IHjobj2; eauto using Happ_cobj.
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst.
  pose proof (Happ_subst Hw s 0) as Hwl.
  rewrite plus_0_r in Hwl; exact Hwl.
(* 15: JGNil *)
  apply JGNil; eauto using jobj_subst_aux1.
(* 14: JGCons *)
  apply JGCons; eauto using jobj_subst_aux1.
(* 13: WKStar *)
  apply WKStar; eauto using jobj_subst_aux1.
(* 12: WKOne *)
  apply WKOne; eauto using jobj_subst_aux1.
(* 11: WKProd *)
  apply WKProd; auto.
(* 10: WKRes *)
  apply WKRes; auto.
  destruct (jobj_class H0) as [_ ck0].
  assert_clear IHjobj2 c1; [auto using cobj|].
  apply_clear IHjobj2 (HCons b k0).
  apply_clear IHjobj2 (HCons ab (subst s (Hlength b) k0)).
  assert_clear IHjobj2 Ha1; [auto using Happ|].
  apply IHjobj2.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 9: WPTrue *)
  apply WPTrue; eauto using jobj_subst_aux1.
(* 8: WPAnd *)
  apply WPAnd; auto.
(* 7: WPCoer *)
  destruct (jobj_class H3) as [_ cH'].
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqw by omega.
  rewrite <- Heqw.
  assert (Happ (HCons a k) w HH').
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  assert (Happ a (subst s 0 w) x).
  { apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
          (c:=subst s (Hlength b) H'); auto using cobj_subst.
    pose proof (Happ_subst Hw s 0) as Hwl.
    rewrite plus_0_r in Hwl; exact Hwl. }
  apply WPCoer with (HH':=x); eauto using Happ_cobj.
(* 6: WPExi *)
  apply WPExi; auto.
(* 5: WPFor *)
  apply WPFor; auto.
  destruct (jobj_class H0) as [_ ck0].
  assert_clear IHjobj2 c1; [auto using cobj|].
  apply_clear IHjobj2 (HCons b k0).
  apply_clear IHjobj2 (HCons ab (subst s (Hlength b) k0)).
  assert_clear IHjobj2 Ha1; [auto using Happ|].
  apply IHjobj2.
  simpl; rewrite plus_0_r.
  auto using Happ.
(* 4: WHNil *)
  apply WHNil; eauto using jobj_subst_aux1.
(* 3: WHCons *)
  destruct (jobj_class H1) as [_ cH'].
  destruct (@Happ_exists (subst s (Hlength b) H')) with (a := ab) as [x Hx];
    auto using cobj_subst.
  destruct (@Happ_exists H') with (a := b) as [w Hw]; auto.
  pose proof (Hlength_Happ Hw) as Heqw.
  replace (Hlength b + Hlength H') with (Hlength H' + Hlength b) in Heqw by omega.
  apply WHCons with (HH':=x); auto.
  rewrite <- Heqw.
  apply IHjobj2; eauto using Happ_cobj.
  { apply Happ_assoc_right with (ab:=H) (b:=b) (c:=H'); auto. }
  apply Happ_assoc_right with (ab:=ab) (b:=subst s 0 b)
        (c:=subst s (Hlength b) H'); auto using cobj_subst.
  pose proof (Happ_subst Hw s 0) as Hwl.
  rewrite plus_0_r in Hwl; exact Hwl.
(* 2: WYNil *)
  apply WYNil; eauto using jobj_subst_aux1.
(* 1: WYCons *)
  apply WYCons; auto.
Qed.

Lemma jobj_subst_0 : forall {v H s k j},
  jobj v (HCons H k) j -> jobj v H (JT s k) -> jobj v H (jsubst s 0 j).
Proof.
intros.
destruct (jobj_class H0) as [cH _].
pose proof (@jobj_subst v H k s (HCons H k) j H1 H0 cH HNil H).
apply H2; auto using Happ.
Qed.

Lemma Hnth_extra : forall {v H a k}, Hnth H a k -> jobj v HNil (Jwf H CTEnv) ->
  jobj v H (Jwf (lift (1 + a) 0 k) CKind).
Proof.
induction 1; simpl; intros; eauto using jobj, cobj.
(* *)
  inversion H0; clear H0; subst.
  rewrite <- (Happ_HNil_eq H4) in H7.
  destruct (jobj_class H7) as [_ ?].
  apply (jobj_shift_0 H7); auto.
(* *)
  inversion H1; clear H1; subst.
  destruct (jobj_class H8) as [_ ?].
  pose proof (@jobj_shift_0 _ k' _ _ (IHHnth H7) H1).
  simpl in H2.
  rewrite lift_fusion in H2; [|omega..].
  assumption.
Qed.

Lemma Ynth_extra : forall {v H Y n p}, Ynth Y n p -> cobj H CTEnv ->
  jobj v H (Jwf Y CPEnv) -> jobj v H (Jwf p CProp).
Proof.
induction 1; simpl; intros; eauto using jobj, cobj.
inversion H1; clear H1; subst; auto.
inversion H2; clear H2; subst; auto.
Qed.

Lemma Happ_Jwf : forall v {a b ab c bc}, Happ a b ab -> Happ b c bc -> cobj bc CTEnv ->
  jobj v a (Jwf b CTEnv) -> jobj v ab (Jwf c CTEnv) -> jobj v a (Jwf bc CTEnv).
Proof.
induction 2; simpl; intros; auto.
inversion H3; clear H3; subst.
inversion H5; clear H5; subst.
destruct (Happ_cobj_rev H0 H9).
apply WHCons with HH'; auto.
apply Happ_assoc_right with (ab:=ab) (b:=H2) (c:=H1); auto.
Qed.

Lemma Happ_Jwf_0 : forall v {a b ab}, Happ a b ab -> cobj ab CTEnv ->
  jobj v HNil (Jwf a CTEnv) -> jobj v a (Jwf b CTEnv) -> jobj v HNil (Jwf ab CTEnv).
Proof.
intros.
destruct (Happ_cobj_rev H H0).
apply Happ_Jwf with (b:=a) (ab:=a) (c:=b); auto using Happ_HNil.
Qed.

Lemma Happ_jobj : forall v {a b ab c bc}, Happ a b ab -> Happ b c bc -> cobj bc CTEnv ->
  jobj v a (JH b) -> jobj v ab (JH c) -> jobj v a (JH bc).
Proof.
induction 2; simpl; intros; auto.
inversion H3; clear H3; subst.
inversion H5; clear H5; subst.
destruct (Happ_cobj_rev H0 H9).
apply JHCons with HH'; auto.
apply Happ_assoc_right with (ab:=ab) (b:=H2) (c:=H1); auto.
Qed.

Lemma Yapp_Jwf : forall {v H Y0 Y1 Y0Y1}, Yapp Y0 Y1 Y0Y1 ->
  jobj v H (Jwf Y0 CPEnv) -> jobj v H (Jwf Y1 CPEnv) ->
  jobj v H (Jwf Y0Y1 CPEnv).
Proof.
induction 1; simpl; intros; auto.
inversion H2; clear H2; subst.
apply WYCons; auto.
Qed.

Inductive KRes_ctx : obj -> Prop :=
| KRes0 : KRes_ctx KStar
| KRes1 : forall k p, KRes_ctx k -> KRes_ctx (KRes k p)
.

Lemma KRes_ctx_jeq : forall k1, KRes_ctx k1 -> forall k2, jeq k1 k2 CKind -> KRes_ctx k2.
Proof.
induction 1; simpl; intros.
{ rewrite (jeq_KStar_rev k2); auto using KRes_ctx. }
destruct (jeq_KRes_rev _ _ _ H0) as [k' [p' [? [? _]]]]; subst.
apply KRes1; auto.
Qed.

Lemma jobj_TArr_inversion_ctx : forall v H t s k, mE v -> jobj v H (JT (TArr t s) k) ->
  KRes_ctx k -> jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof.
intros v H t s k mEv Hts.
remember (JT (TArr t s) k) as j.
generalize t s k Heqj; clear t s k Heqj.
induction Hts; intros t0 s0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHts with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHts1 with k; auto. }
apply IHHts with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TArr_inversion : forall {v H t s}, mE v -> jobj v H (JT (TArr t s) KStar) ->
  jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof. intros. apply jobj_TArr_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma jobj_TProd_inversion_ctx : forall v H t s k, mE v -> jobj v H (JT (TProd t s) k) ->
  KRes_ctx k -> jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof.
intros v H t s k mEv Hts.
remember (JT (TProd t s) k) as j.
generalize t s k Heqj; clear t s k Heqj.
induction Hts; intros t0 s0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHts with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHts1 with k; auto. }
apply IHHts with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TProd_inversion : forall {v H t s}, mE v -> jobj v H (JT (TProd t s) KStar) ->
  jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof. intros. apply jobj_TProd_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma jobj_TSum_inversion_ctx : forall v H t s k, mE v -> jobj v H (JT (TSum t s) k) ->
  KRes_ctx k -> jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof.
intros v H t s k mEv Hts.
remember (JT (TSum t s) k) as j.
generalize t s k Heqj; clear t s k Heqj.
induction Hts; intros t0 s0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHts with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHts1 with k; auto. }
apply IHHts with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TSum_inversion : forall {v H t s}, mE v -> jobj v H (JT (TSum t s) KStar) ->
  jobj v H (JT t KStar) /\ jobj v H (JT s KStar).
Proof. intros. apply jobj_TSum_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma jobj_TFor_inversion_ctx : forall v H k' t k, mE v -> jobj v H (JT (TFor k' t) k) ->
  KRes_ctx k -> jobj v (HCons H k') (JT t KStar).
Proof.
intros v H k' t k mEv Ht.
remember (JT (TFor k' t) k) as j.
generalize k' t k Heqj; clear k' t k Heqj.
induction Ht; intros k'0 t0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHt with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHt1 with k; auto. }
apply IHHt with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TFor_inversion : forall {v H k t}, mE v -> jobj v H (JT (TFor k t) KStar) ->
  jobj v (HCons H k) (JT t KStar).
Proof. intros. apply jobj_TFor_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma jobj_TMu_inversion_ctx : forall v H t k, mE v -> jobj v H (JT (TMu t) k) ->
  KRes_ctx k -> jobj v (HCons H KStar) (JT t KStar) /\ jrec 0 t WF.
Proof.
intros v H t k mEv Ht.
remember (JT (TMu t) k) as j.
generalize t k Heqj; clear t k Heqj.
induction Ht; intros t0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHt with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHt1 with k; auto. }
apply IHHt with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TMu_inversion : forall {v H t}, mE v -> jobj v H (JT (TMu t) KStar) ->
  jobj v (HCons H KStar) (JT t KStar) /\ jrec 0 t WF.
Proof. intros. apply jobj_TMu_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma jobj_TPi_inversion_ctx : forall v H k' t k, mE v -> jobj v H (JT (TPi k' t) k) ->
  KRes_ctx k -> jobj v (HCons H k') (JT t KStar).
Proof.
intros v H k' t k mEv Ht.
remember (JT (TPi k' t) k) as j.
generalize k' t k Heqj; clear k' t k Heqj.
induction Ht; intros k'0 t0 k0 Heqj krc; inversion Heqj; clear Heqj; subst; auto.
{ apply IHHt with k; auto.
  apply KRes_ctx_jeq with k0; auto using EQsym. }
{ inversion krc; clear krc; subst.
  apply IHHt1 with k; auto. }
apply IHHt with (KRes k0 p); auto using KRes_ctx.
Qed.

Lemma jobj_TPi_inversion : forall {v H k t}, mE v -> jobj v H (JT (TPi k t) KStar) ->
  jobj v (HCons H k) (JT t KStar).
Proof. intros. apply jobj_TPi_inversion_ctx with KStar; auto using KRes_ctx. Qed.

Lemma JH_extra : forall {v H H'}, mE v -> jobj v H (JH H') -> jobj v H (Jwf H' CTEnv).
Proof.
intros v H H' mEv j.
remember (JH H') as e.
generalize H' Heqe; clear H' Heqe.
induction j; intros ? Heq; inversion Heq; clear Heq; subst.
apply WHNil; auto.
inversion j2; clear j2; subst.
apply WHCons with HH'; auto.
Qed.

Definition extrajudg v H J :=
  match J with
    | JK k => jobj v H (Jwf k CKind)
    | JT t k => jobj v H (Jwf k CKind)
    | JP Y0 Y1 p =>
      jobj v H (Jwf Y0 CPEnv) -> jobj v H (Jwf Y1 CPEnv) -> jobj v H (Jwf p CProp)
    | JC Y0 Y1 H' t' t =>
      jobj v H (Jwf Y0 CPEnv) -> jobj v H (Jwf Y1 CPEnv) ->
      ( jobj v H (JH H') /\ forall HH', Happ H H' HH' ->
        jobj v HH' (JT t' KStar) -> jobj v H (JT t KStar) )
    | JH H' => True
    | JG _ => True
    | Jwf _ _ => True
  end.
Hint Unfold extrajudg.

Lemma jobj_extra : forall {v H J}, mE v -> jobj v H J ->
  jobj v HNil (Jwf H CTEnv) -> extrajudg v H J.
Proof.
Ltac destruct_extra :=
match goal with
  | |- _ -> _ => intro
  | Hx : ?P -> _, Hy : ?P |- _ => pose proof (Hx Hy); clear Hx
end.
Ltac inversion_extra :=
match goal with
  | H : jobj _ _ (Jwf KStar _) |- _ => clear H
  | H : jobj _ _ (Jwf KOne _) |- _ => clear H
  | H : jobj _ _ (Jwf (KProd _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (KRes _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TVar _) _) |- _ => clear H
  | H : jobj _ _ (Jwf (TArr _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TProd _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TFor _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TPi _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TMu _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf TUnit _) |- _ => clear H
  | H : jobj _ _ (Jwf (TPair _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TFst _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (TSnd _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf PTrue _) |- _ => clear H
  | H : jobj _ _ (Jwf (PAnd _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (PCoer _ _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (PExi _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf (PFor _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf HNil _) |- _ => clear H
  | H : jobj _ _ (Jwf (HCons _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf YNil _) |- _ => clear H
  | H : jobj _ _ (Jwf (YCons _ _) _) |- _ => inversion H; clear H; subst
  | H : jobj _ _ (Jwf GNil _) |- _ => clear H
  | H : jobj _ _ (Jwf (GCons _ _) _) |- _ => inversion H; clear H; subst
end.
Ltac clean_extra :=
match goal with
  | H1 : ?P, H2 : ?P |- _ => clear H2
end.
Ltac assert_extra :=
match goal with
  | Hx : ?P -> _ |- _ => assert P as Hy; [clear Hx|pose proof (Hx Hy); clear Hx]
end.
Ltac crush_extra := repeat destruct_extra; repeat inversion_extra; repeat clean_extra.
Ltac cobj_extra :=
  match goal with
    | Hx : jobj ?v HNil (Jwf ?H CTEnv) |- cobj ?H CTEnv => apply (jobj_class Hx)
  end.
intros v H J mEv.
induction 1; intro;
try match goal with
  | |- extrajudg _ _ (JG _) => exact I
  | |- extrajudg _ _ (JH _) => exact I
  | |- extrajudg _ _ (Jwf _ _) => exact I
end; unfold extrajudg in *; crush_extra.
(* 45: JKexi *) assumption.
(* 44: JTeq *) assumption.
(* 43: JTVar *) apply Hnth_extra; auto.
(* 42: JTArr *) apply WKStar; cobj_extra.
(* 41: JTOne *) apply WKStar; cobj_extra.
(* 40: JTProd *) apply WKStar; cobj_extra.
(* 39: JTVoid *) apply WKStar; cobj_extra.
(* 38: JTSum *) apply WKStar; cobj_extra.
(* 37: JTFor *) apply WKStar; cobj_extra.
(* 36: JTPi *) apply WKStar; cobj_extra.
(* 35: JTMu *) apply WKStar; cobj_extra.
(* 34: JTBot *) apply WKStar; cobj_extra.
(* 33: JTTop *) apply WKStar; cobj_extra.
(* 32: JTUnit *) apply WKOne; cobj_extra.
(* 31: JTPair *) apply WKProd; assumption.
(* 30: JTFst *) assumption.
(* 29: JTSnd *) assumption.
(* 28: JTPack *) apply WKRes; assumption.
(* 27: JTUnpack *) assumption.
(* 26: JPeq *) assumption.
(* 25: JPVar *) eapply Ynth_extra; eassumption.
(* 24: JPTrue *) apply WPTrue; cobj_extra.
(* 23: JPAndPair *) apply WPAnd; assumption.
(* 22: JPAndFst *) assumption.
(* 21: JPAndSnd *) assumption.
(* 20: JPExi *) eauto using jobj.
(* 19: JPForIntro *)
  apply WPFor; auto.
  destruct (jobj_class H6) as [cH ck].
  pose proof (jobj_shift_0 H4 ck).
  pose proof (jobj_shift_0 H5 ck).
  apply IHjobj; auto.
  apply WHCons with (HH':=H); auto.
  apply Happ_HNil; auto.
(* 18: JPForElim *)
  apply (jobj_subst_0 H10 H0_).
(* 17: JPRes *)
  apply (jobj_subst_0 H12).
  eapply JTUnpack; eauto.
(* 16: JPFix *) assumption.
(* 15: JPCoer *)
  match goal with Hyp: jobj v H (JH H') /\ _ |- _ => destruct Hyp as [jH' Ht] end.
  { apply WPCoer with HH'; auto.
    - apply (JH_extra mEv jH').
    - apply (Ht HH'); auto. }
(* 14: JCProp *)
  split; auto using JHNil.
(* 13: JCRefl *)
  split; auto using JHNil.
  intros ? Ha; inversion Ha; clear Ha; subst; auto.
(* 12: JCTrans *)
  destruct H7 as [jH2 jt3].
  pose proof (JH_extra mEv jH2) as wH2.
  destruct (jobj_class wH2) as [cH cH2].
  assert (cobj HH2 CTEnv) as cHH2 by (apply (Happ_cobj H0); auto).
  assert_clear IHjobj1 jHH2; [apply (Happ_Jwf_0 _ H0); auto|].
  assert_clear IHjobj1 c1; [apply (jobj_lift_0 H0 cHH2 H5); auto|].
  assert_clear IHjobj1 c2; [apply (jobj_lift_0 H0 cHH2 H6); auto|].
  destruct IHjobj1 as [jH1 jt2].
  pose proof (JH_extra mEv jH1) as wH1.
  destruct (jobj_class wH1) as [_ cH1].
  assert (cobj H2H1 CTEnv) by eauto using Happ_cobj.
  split. { apply Happ_jobj with (b:=H2) (ab:=HH2) (c:=H1); auto. }
  intros ? Ha jt1.
  apply (jt3 HH2); auto.
  apply (jt2 HH'); auto.
  apply Happ_assoc_left with (a:=H) (b:=H2) (bc:=H2H1); auto.
(* 11: JCWeak *)
  destruct H4 as [jH' js].
  destruct (jobj_class jH') as [cH cH'].
  split; auto using JHNil.
  intros Htmp Ha jt; inversion Ha; clear Ha; subst; rename Htmp into H.
  destruct (Happ_exists cH' H) as [HH' aHH'].
  apply (js HH'); auto.
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  apply (jobj_lift_0 aHH' cHH' jt).
(* 10: JCArr *)
  assert_clear H13 wY0Y1; [apply (Yapp_Jwf H0); auto|].
  destruct (jobj_class wY0Y1) as [cH _].
  assert_clear H13 wYNil; [apply WYNil; auto|].
  destruct H13 as [jH' js].
  split; auto.
  intros Htmp Ha jts'; rewrite (Happ_eq Ha H1) in *; clear Htmp Ha.
  destruct (jobj_TArr_inversion mEv jts') as [jt' js'].
  apply JTArr; eauto.
(* 9: JCProd *)
  assert_clear H12 wY0Y1; [apply (Yapp_Jwf H0); auto|].
  destruct (jobj_class wY0Y1) as [cH _].
  assert_clear H12 wYNil; [apply WYNil; auto|].
  destruct H12 as [jH' jt].
  apply_clear H11 wY0Y1.
  apply_clear H11 wYNil.
  destruct H11 as [_ js].
  split; auto.
  intros Htmp Ha jts'; rewrite (Happ_eq Ha H1) in *; clear Htmp Ha.
  destruct (jobj_TProd_inversion mEv jts') as [jt' js'].
  apply JTProd; eauto.
(* 8: JCSum *)
  assert_clear H12 wY0Y1; [apply (Yapp_Jwf H0); auto|].
  destruct (jobj_class wY0Y1) as [cH _].
  assert_clear H12 wYNil; [apply WYNil; auto|].
  destruct H12 as [jH' jt].
  apply_clear H11 wY0Y1.
  apply_clear H11 wYNil.
  destruct H11 as [_ js].
  split; auto.
  intros Htmp Ha jts'; rewrite (Happ_eq Ha H1) in *; clear Htmp Ha.
  destruct (jobj_TSum_inversion mEv jts') as [jt' js'].
  apply JTSum; eauto.
(* 7: JCPi *)
  destruct (jobj_class H11) as [cH ck].
  assert_clear IHjobj3 wHk; [apply WHCons with H; auto using Happ_HNil|].
  assert_clear IHjobj3 wY0Y1l.
  { apply (@jobj_shift_0 H k v (Jwf Y0Y1 CPEnv)); auto.
    apply (Yapp_Jwf H0); auto. }
  assert_clear IHjobj3 wYNilHk; [apply WYNil; auto using cobj|].
  destruct IHjobj3 as [_ jt].
  split; auto.
  intros Htmp Ha jkt'; rewrite (Happ_eq Ha H1) in *; clear Htmp Ha.
  pose proof (jobj_TPi_inversion mEv jkt') as jt'.
  apply JTPi; auto.
  apply (jt HaH'); auto.
  apply @jobj_subst_0 with (s:=s') (k:=lift 1 (Hlength H') k')
        (j:=JT (lift 1 (1 + Hlength H') t') KStar); auto.
  destruct (jobj_class H0_) as [_ cH'].
  destruct (jobj_class jt') as [ck' _]; inversion ck'; clear ck'; subst.
  apply @jobj_lift with (H1:=H) (H2:=HCons HNil k) (H3:=HCons H' k')
        (j:=JT t' KStar) (H1H2:=HCons H k) (H1H3:= HCons HH' k'); auto using cobj, Happ.
  simpl; rewrite plus_0_r; auto using Happ1.
(* 6: JCGen *)
  destruct (jobj_class H3) as [cH ck].
  split; [apply JHCons with H; auto using Happ0, JHNil|].
  intros ? Ha jt; inversion Ha; clear Ha; subst.
  inversion H16; clear H16; subst.
  rename H2H1 into H.
  apply JTFor; auto.
(* 5: JCInst *)
  destruct (jobj_class H9) as [cH ck].
  split; auto using JHNil.
  intros Htmp Ha jkt; inversion Ha; clear Ha; subst; rename Htmp into H.
  pose proof (jobj_TFor_inversion mEv jkt) as jt.
  apply (jobj_subst_0 jt); auto.
(* 4: JCUnfold *)
  split; auto using JHNil.
  intros Htmp Ha jkt; inversion Ha; clear Ha; subst; rename Htmp into H.
  pose proof (jobj_TMu_inversion mEv jkt) as [jt _].
  apply (jobj_subst_0 jt); auto.
(* 3: JCFold *)
  destruct (jobj_class H5) as [_ cH].
  split; auto using JHNil.
  intros Htmp Ha _; inversion Ha; clear Ha; subst; rename Htmp into H.
  apply JTMu; auto.
(* 2: JCTop *)
  split; auto using JHNil.
  intros Htmp Ha _; inversion Ha; clear Ha; subst; rename Htmp into H.
  apply JTTop; auto.
(* 1: JCBot *)
  destruct (jobj_class H3) as [_ cH].
  split; auto using JHNil.
Qed.

Lemma Gnth_extra : forall {v H G x t}, Gnth G x t -> jobj v H (JG G) -> jobj v H (JT t KStar).
Proof.
induction 1; simpl; intros Hj; destruct (jobj_class Hj) as [cH _]; eauto using jobj;
inversion Hj; auto.
Qed.

Lemma jterm_extra : forall {v H G a t}, mE v -> jterm v H G a t ->
  jobj v HNil (Jwf H CTEnv) -> jobj v H (JG G) ->
  jobj v H (JT t KStar).
Proof.
Ltac destruct_extra ::=
match goal with
  | |- _ -> _ => intro
  | Hx : ?P -> _, Hy : ?P |- _ => pose proof (Hx Hy); clear Hx
end.
intros v H G a t mEv.
induction 1; intros; repeat destruct_extra.
(* 14: JVar *) apply (Gnth_extra H2); auto.
(* 13: JLam *) apply JTArr; eauto using jobj.
(* 12: JApp *) apply (jobj_TArr_inversion mEv H6).
(* 11: JUnit *) apply JTOne; auto.
(* 10: JPair *) apply JTProd; eauto using jobj.
(* 9: JFst *) apply (jobj_TProd_inversion mEv H6).
(* 8: JSnd *) apply (jobj_TProd_inversion mEv H6).
(* 7: JAbsurd *) assumption.
(* 6: JInl *) apply JTSum; eauto using jobj.
(* 5: JInr *) apply JTSum; eauto using jobj.
(* 4: JMatch *)
  destruct (jobj_TSum_inversion mEv H8).
  apply H6; apply JGCons; auto.
(* 3: JGen *)
  destruct (jobj_class H3) as [_ cH].
  apply JTPi; auto.
  apply IHjterm.
  { apply WHCons with H; auto using Happ_HNil. }
  destruct (jobj_class H5) as [_ ck'].
  apply (jobj_shift_0 H4 ck').
(* 2: JInst *)
  pose proof (jobj_TPi_inversion mEv H6).
  apply (jobj_subst_0 H5 H2).
(* 1: JCoer *)
  destruct (jobj_class H4) as [cH _].
  pose proof (jobj_extra mEv H4 H5) as eC; unfold extrajudg in eC.
  assert_clear eC wYNil; [apply WYNil; auto|].
  apply_clear eC wYNil.
  destruct eC as [jH' js].
  pose proof (JH_extra mEv jH') as wH'.
  apply (js HH'); auto.
  destruct (jobj_class jH') as [_ cH'].
  assert (cobj HH' CTEnv) as cHH'; [apply (Happ_cobj H0); auto|].
  apply IHjterm; [apply (Happ_Jwf_0 v H0); auto|].
  apply (jobj_lift_0 H0 cHH' H6).
Qed.

Lemma jobj_FS : forall {b H J}, jobj (b, vF) H J -> jobj (b, vS) H J.
Proof.
intros b H J Hj.
remember (b, vF) as v.
induction Hj; subst v.
eapply JKexi; eauto; intro Hf; exfalso; exact Hf.
eapply JTeq; eauto; intro Hf; exfalso; exact Hf.
eapply JTVar; eauto.
eapply JTArr; eauto.
eapply JTOne; eauto.
eapply JTProd; eauto.
eapply JTVoid; eauto.
eapply JTSum; eauto.
eapply JTFor; eauto; intro Hf; exfalso; exact Hf.
eapply JTPi; eauto; intro Hf; exfalso; exact Hf.
eapply JTMu; eauto.
eapply JTBot; eauto.
eapply JTTop; eauto.
eapply JTUnit; eauto.
eapply JTPair; eauto.
eapply JTFst; eauto.
eapply JTSnd; eauto.
eapply JTPack; eauto; intro Hf; exfalso; exact Hf.
eapply JTUnpack; eauto.
eapply JPeq; eauto; intro Hf; exfalso; exact Hf.
eapply JPVar; eauto.
eapply JPTrue; eauto.
eapply JPAndPair; eauto.
eapply JPAndFst; eauto.
eapply JPAndSnd; eauto.
eapply JPExi; eauto.
eapply JPForIntro; eauto; intro Hf; exfalso; exact Hf.
eapply JPForElim; eauto.
eapply JPRes; eauto.
eapply JPFix; eauto; intro Hf; exfalso; exact Hf.
eapply JPCoer; eauto.
eapply JCProp; eauto; intro Hf; exfalso; exact Hf.
eapply JCRefl; eauto; intro Hf; exfalso; exact Hf.
eapply JCTrans; eauto.
eapply JCWeak; eauto.
eapply JCArr; eauto; intro Hf; exfalso; exact Hf.
eapply JCProd; eauto.
eapply JCSum; eauto.
eapply JCPi; eauto; intro Hf; exfalso; exact Hf.
eapply JCGen; eauto.
eapply JCInst; eauto.
eapply JCUnfold; eauto.
eapply JCFold; eauto.
eapply JCTop; eauto.
eapply JCBot; eauto.
eapply JHNil; eauto.
eapply JHCons; eauto.
eapply JGNil; eauto.
eapply JGCons; eauto.
eapply WKStar; eauto.
eapply WKOne; eauto.
eapply WKProd; eauto.
eapply WKRes; eauto.
eapply WPTrue; eauto.
eapply WPAnd; eauto.
eapply WPCoer; eauto.
eapply WPExi; eauto.
eapply WPFor; eauto.
eapply WHNil; eauto.
eapply WHCons; eauto.
eapply WYNil; eauto.
eapply WYCons; eauto.
Qed.

Lemma jterm_FS : forall {b H G a t}, jterm (b, vF) H G a t -> jterm (b, vS) H G a t.
Proof.
intros b H G a t Hj.
remember (b, vF) as v.
induction Hj; subst v;
repeat match goal with
  | H : _ (_, vF) -> _ |- _ => let H' := fresh "H" in
      pose proof (H I) as H'; clear H; rename H' into H
end.
eapply JVar; eauto; intros; apply jobj_FS; auto.
eapply JLam; eauto; intros; apply jobj_FS; auto.
eapply JApp; eauto; intros; apply jobj_FS; auto.
eapply JUnit; eauto; intros; apply jobj_FS; auto.
eapply JPair; eauto; intros; apply jobj_FS; auto.
eapply JFst; eauto; intros; apply jobj_FS; auto.
eapply JSnd; eauto; intros; apply jobj_FS; auto.
eapply JAbsurd; eauto; intros; apply jobj_FS; auto.
eapply JInl; eauto; intros; apply jobj_FS; auto.
eapply JInr; eauto; intros; apply jobj_FS; auto.
eapply JMatch; eauto; intros; apply jobj_FS; auto.
eapply JGen; eauto; intros; apply jobj_FS; auto.
eapply JInst; eauto; intros; apply jobj_FS; auto.
eapply JCoer; eauto; intros; apply jobj_FS; auto.
Qed.

Lemma jobj_FP : forall {b H J}, jobj (b, vF) H J -> jobj (b, vP) H J.
Proof.
intros b H J Hj.
remember (b, vF) as v.
induction Hj; subst v.
eapply JKexi; eauto.
eapply JTeq; eauto.
eapply JTVar; eauto.
eapply JTArr; eauto.
eapply JTOne; eauto.
eapply JTProd; eauto.
eapply JTVoid; eauto.
eapply JTSum; eauto.
eapply JTFor; eauto.
eapply JTPi; eauto.
eapply JTMu; eauto.
eapply JTBot; eauto.
eapply JTTop; eauto.
eapply JTUnit; eauto.
eapply JTPair; eauto.
eapply JTFst; eauto.
eapply JTSnd; eauto.
eapply JTPack; eauto.
eapply JTUnpack; eauto.
eapply JPeq; eauto.
eapply JPVar; eauto.
eapply JPTrue; eauto.
eapply JPAndPair; eauto.
eapply JPAndFst; eauto.
eapply JPAndSnd; eauto.
eapply JPExi; eauto.
eapply JPForIntro; eauto.
eapply JPForElim; eauto.
eapply JPRes; eauto.
eapply JPFix; eauto.
eapply JPCoer; eauto.
eapply JCProp; eauto.
eapply JCRefl; eauto.
eapply JCTrans; eauto.
eapply JCWeak; eauto.
eapply JCArr; eauto; intro Hf; exfalso; exact Hf.
eapply JCProd; eauto; intro Hf; exfalso; exact Hf.
eapply JCSum; eauto; intro Hf; exfalso; exact Hf.
eapply JCPi; eauto; intro Hf; exfalso; exact Hf.
eapply JCGen; eauto; intro Hf; exfalso; exact Hf.
eapply JCInst; eauto; intro Hf; exfalso; exact Hf.
eapply JCUnfold; eauto; intro Hf; exfalso; exact Hf.
eapply JCFold; eauto.
eapply JCTop; eauto; intro Hf; exfalso; exact Hf.
eapply JCBot; eauto.
eapply JHNil; eauto.
eapply JHCons; eauto.
eapply JGNil; eauto.
eapply JGCons; eauto.
eapply WKStar; eauto.
eapply WKOne; eauto.
eapply WKProd; eauto.
eapply WKRes; eauto.
eapply WPTrue; eauto.
eapply WPAnd; eauto.
eapply WPCoer; eauto.
eapply WPExi; eauto.
eapply WPFor; eauto.
eapply WHNil; eauto.
eapply WHCons; eauto.
eapply WYNil; eauto.
eapply WYCons; eauto.
Qed.

Lemma jterm_FP : forall {b H G a t}, jterm (b, vF) H G a t -> jterm (b, vP) H G a t.
Proof.
intros b H G a t Hj.
remember (b, vF) as v.
induction Hj; subst v;
repeat match goal with
  | H : _ (_, vF) -> _ |- _ => let H' := fresh "H" in
      pose proof (H I) as H'; clear H; rename H' into H
end.
eapply JVar; eauto; intros; apply jobj_FP; auto.
eapply JLam; eauto; intros; apply jobj_FP; auto.
eapply JApp; eauto; intros; apply jobj_FP; auto.
eapply JUnit; eauto; intros; apply jobj_FP; auto.
eapply JPair; eauto; intros; apply jobj_FP; auto.
eapply JFst; eauto; intros; apply jobj_FP; auto.
eapply JSnd; eauto; intros; apply jobj_FP; auto.
eapply JAbsurd; eauto; intros; apply jobj_FP; auto.
eapply JInl; eauto; intros; apply jobj_FP; auto.
eapply JInr; eauto; intros; apply jobj_FP; auto.
eapply JMatch; eauto; intros; apply jobj_FP; auto.
eapply JGen; eauto; intros; apply jobj_FP; auto.
eapply JInst; eauto; intros; apply jobj_FP; auto.
eapply JCoer; eauto; intros; apply jobj_FP; auto.
Qed.

Definition hypjudg1 b H J :=
  match J with
    | JK k => True
    | JT t k => True
    | JP Y0 Y1 p => jobj (b, vF) H (Jwf Y0 CPEnv) /\ jobj (b, vF) H (Jwf Y1 CPEnv)
    | JC Y0 Y1 H' t' t => jobj (b, vF) H (Jwf Y0 CPEnv) /\ jobj (b, vF) H (Jwf Y1 CPEnv)
    | JH H' => True
    | JG _ => True
    | Jwf _ _ => True
  end.
Definition ccljudg1 b H J :=
  match J with
    | JK k => True
    | JT t k => True
    | JP Y0 Y1 p => True
    | JC Y0 Y1 H' t' t => jobj (b, vF) H (Jwf H' CTEnv)
    | JH H' => True
    | JG _ => True
    | Jwf _ _ => True
  end.
Definition hypjudg2 b H J :=
  match J with
    | JK k => True
    | JT t k => True
    | JP Y0 Y1 p => True
    | JC Y0 Y1 H' t' t => exists HH', Happ H H' HH' /\ jobj (b, vF) HH' (JT t' KStar)
    | JH H' => True
    | JG _ => True
    | Jwf _ _ => True
  end.
Hint Unfold hypjudg1 ccljudg1 hypjudg2.

Ltac curry H := let H' := fresh "H" in
  pose proof (fun a b => H (conj a b)) as H'; clear H; rename H' into H.

Lemma jobj_PF : forall {b H J}, jobj (b, vF) HNil (Jwf H CTEnv) -> jobj (b, vP) H J ->
  hypjudg1 b H J -> ( ccljudg1 b H J
                   /\ (hypjudg2 b H J -> jobj (b, vF) H J) ).
Proof.
Ltac clear_True := repeat match goal with
  | H : True |- _ => clear H
  | |- True /\ _ => split; [exact I|]
  | H : True /\ _ |- _ => destruct H as [_ H]
  | |- True -> _ => intros _
  | H : True -> _ |- _ => let H' := fresh "H" in
      pose proof (H I) as H'; clear H; rename H' into H
  end.
intros b H J Hwf Hj.
remember (b, vP) as v.
induction Hj; subst v; simpl in *; intros Hh;
assert (cobj H CTEnv) as cH by apply (jobj_class Hwf);
repeat match goal with
  | H : mE (_, vP) -> _ |- _ => let H' := fresh "H" in
      pose proof (H I) as H'; clear H; rename H' into H
  | H : mS (_, vP) -> _ |- _ => clear H
  | Hx : ?P -> _, Hy : ?P |- _ => apply_clear Hx Hy
  | H : (?x /\ ?y) -> _ |- _ => let H' := fresh "H" in
    pose proof (fun a b => H (conj a b)) as H'; clear H; rename H' into H
  | cH : cobj ?H CTEnv , Hx : jobj (b, vF) ?H (Jwf YNil CPEnv) -> _ |- _ =>
    apply_clear Hx (WYNil (b, vF) H cH)
end; clear_True.
eapply JKexi; eauto.
eapply JTeq; eauto.
eapply JTVar; eauto.
eapply JTArr; eauto.
eapply JTOne; eauto.
eapply JTProd; eauto.
eapply JTVoid; eauto.
eapply JTSum; eauto.
{ eapply JTFor; eauto.
  apply IHHj; auto.
  apply WHCons with (HH':=H); auto using Happ_HNil. }
{ eapply JTPi; eauto.
  apply IHHj; auto.
  apply WHCons with (HH':=H); auto using Happ_HNil. }
{ eapply JTMu; eauto.
  apply IHHj; auto.
  apply WHCons with (HH':=H); eauto using Happ_HNil, jobj. }
eapply JTBot; eauto.
eapply JTTop; eauto.
eapply JTUnit; eauto.
eapply JTPair; eauto.
eapply JTFst; eauto.
eapply JTSnd; eauto.
{ eapply JTPack; eauto.
  intros _.
  apply H1; auto.
  pose proof (@jobj_extra (b, vF) _ _ I IHHj1 Hwf).
  apply WHCons with (HH':=H); auto using Happ_HNil. }
eapply JTUnpack; eauto.
eapply JPeq; eauto.
eapply JPVar; eauto.
eapply JPTrue; eauto.
eapply JPAndPair; eauto.
eapply JPAndFst; eauto.
eapply JPAndSnd; eauto.
eapply JPExi; eauto.
{ eapply JPForIntro; eauto.
  apply IHHj; auto.
  { apply WHCons with (HH':=H); eauto using Happ_HNil. }
  destruct (jobj_class H1) as [_ ?].
  destruct Hh as [Hl Hr].
  split; [apply (jobj_shift_0 Hl)|apply (jobj_shift_0 Hr)]; auto. }
eapply JPForElim; eauto.
eapply JPRes; eauto.
{ eapply JPFix; eauto.
  destruct Hh.
  apply IHHj; auto.
  eauto using jobj. }
{ (* JPCoer *)
  destruct Hh as [wY0 wY1].
  destruct (jobj_class Hj1) as [_ [_ [_ [cH' _]]]].
  assert (cobj HH' CTEnv) as cHH'; [apply (Happ_cobj H0); auto|].
  destruct IHHj1 as [jH' jc].
  assert_clear IHHj2 wHH'.
  { apply (Happ_Jwf_0 (b, vF) H0); auto. }
  clear_True.
  eapply JPCoer; eauto. }
{ (* JCProp *)
  destruct Hh as [wY0 wY1].
  pose proof ((fun x => jobj_extra x IHHj1) I Hwf wY0 wY1) as wC.
  inversion wC; clear wC; subst.
  split; auto.
  intros [Htmp [Ha jt']]; rewrite (Happ_eq Ha H4) in *; clear Htmp Ha.
  eapply JCProp; eauto. }
{ (* JCRefl *)
  split; auto using WHNil.
  intros [Htmp [Ha jt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  eapply JCRefl; eauto. }
{ (* JCTrans *)
  rename H0 into aHH2.
  rename H3 into aH2H1.
  destruct Hh as [wY0 wY1].
  destruct IHHj2 as [wH2 IHHj2].
  destruct (jobj_class wH2) as [_ cH2].
  assert (cobj HH2 CTEnv) as cHH2. { apply (Happ_cobj aHH2); auto. }
  assert_clear IHHj1 wHH2. { apply (Happ_Jwf_0 (b, vF) aHH2); auto. }
  curry IHHj1.
  assert_clear IHHj1 wY0l. { apply (jobj_lift_0 aHH2 cHH2 wY0). }
  assert_clear IHHj1 wY1l. { apply (jobj_lift_0 aHH2 cHH2 wY1). }
  destruct IHHj1 as [wH1 IHHj1].
  destruct (jobj_class wH1) as [_ cH1].
  assert (cobj H2H1 CTEnv) as cH2H1. { apply (Happ_cobj aH2H1); auto. }
  split. { apply (Happ_Jwf (b, vF) aHH2 aH2H1 cH2H1); auto. }
  intros [HH' [aHH' jt1]].
  assert (Happ HH2 H1 HH') as aHH'L.
  { apply Happ_assoc_left with (a:=H) (b:=H2) (bc:=H2H1); auto. }
  assert_clear IHHj1 c1; [|clear c1]. { exists HH'; auto. }
  pose proof ((fun x => jobj_extra x IHHj1 wHH2 wY0l wY1l) I) as [jH1 jt2] .
  apply_clear jt2 HH'.
  apply_clear jt2 aHH'L.
  apply_clear jt2 jt1.
  apply JCTrans with (H2:=H2) (H1:=H1) (t2:=t2) (HH2:=HH2); auto.
  apply IHHj2.
  exists HH2; auto. }
{ (* JCWeak *)
  destruct Hh as [wY0 wY1].
  destruct IHHj as [wH' IHHj].
  split. { auto using WHNil. }
  intros [Htmp [Ha jt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  apply JCWeak with H'.
  apply IHHj.
  destruct (jobj_class wH') as [_ cH'].
  destruct (Happ_exists cH' H) as [HH' aHH'].
  exists HH'; split; auto.
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  apply (jobj_lift_0 aHH' cHH' jt). }
{ (* JCArr *)
  rename H0 into aY0Y1, H1 into aHH', H9 into jt.
  destruct Hh as [wY0 wY1].
  assert_clear IHHj2 wY0Y1. { apply (Yapp_Jwf aY0Y1 wY0 wY1). }
  assert_clear IHHj2 wYNil. { apply WYNil; auto. }
  destruct IHHj2 as [wH' IHHj2].
  destruct (jobj_class wH') as [_ cH'].
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  assert_clear IHHj1 wHH'. { apply Happ_Jwf_0 with (a:=H) (b:=H'); auto. }
  curry IHHj1.
  assert_clear IHHj1 wY0Y1l. { apply (jobj_lift_0 aHH' cHH' wY0Y1). }
  assert_clear IHHj1 c1; [|clear c1]. { apply WYNil; auto. }
  destruct IHHj1 as [_ IHHj1].
  split; auto.
  intros [Htmp [Ha jts']]; rewrite (Happ_eq Ha aHH') in *; clear Htmp Ha.
  destruct ((fun x => jobj_TArr_inversion x jts') I) as [jt' js'].
  assert_clear IHHj2 c1; [|clear c1]. { exists HH'; auto. }
  assert_clear IHHj1 c1; [|clear c1].
  { exists HH'.
    split. { apply Happ0. }
    apply (jobj_lift_0 aHH' cHH' jt). }
  pose proof ((fun x => jobj_extra x IHHj2 Hwf wY0Y1 wYNil) I) as [jH'  _].
  apply JCArr with Y0Y1 HH'; auto. }
{ (* JCProd *)
  rename H0 into aY0Y1, H1 into aHH'.
  destruct Hh as [wY0 wY1].
  assert_clear IHHj2 wY0Y1. { apply (Yapp_Jwf aY0Y1 wY0 wY1). }
  apply_clear IHHj1 wY0Y1.
  assert_clear IHHj2 wYNil. { apply WYNil; auto. }
  apply_clear IHHj1 wYNil.
  destruct IHHj2 as [wH' IHHj2].
  destruct IHHj1 as [_ IHHj1].
  destruct (jobj_class wH') as [_ cH'].
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  split; auto.
  intros [Htmp [Ha jts']]; rewrite (Happ_eq Ha aHH') in *; clear Htmp Ha.
  destruct ((fun x => jobj_TProd_inversion x jts') I) as [jt' js'].
  assert_clear IHHj1 c1; [|clear c1]. { exists HH'; auto. }
  assert_clear IHHj2 c1; [|clear c1]. { exists HH'; auto. }
  pose proof ((fun x => jobj_extra x IHHj1 Hwf wY0Y1 wYNil) I) as [jH' _].
  apply JCProd with HH' Y0Y1; auto. }
{ (* JCSum *)
  rename H0 into aY0Y1, H1 into aHH'.
  destruct Hh as [wY0 wY1].
  assert_clear IHHj2 wY0Y1. { apply (Yapp_Jwf aY0Y1 wY0 wY1). }
  apply_clear IHHj1 wY0Y1.
  assert_clear IHHj2 wYNil. { apply WYNil; auto. }
  apply_clear IHHj1 wYNil.
  destruct IHHj2 as [wH' IHHj2].
  destruct IHHj1 as [_ IHHj1].
  destruct (jobj_class wH') as [_ cH'].
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  split; auto.
  intros [Htmp [Ha jts']]; rewrite (Happ_eq Ha aHH') in *; clear Htmp Ha.
  destruct ((fun x => jobj_TSum_inversion x jts') I) as [jt' js'].
  assert_clear IHHj1 c1; [|clear c1]. { exists HH'; auto. }
  assert_clear IHHj2 c1; [|clear c1]. { exists HH'; auto. }
  pose proof ((fun x => jobj_extra x IHHj1 Hwf wY0Y1 wYNil) I) as [jH' _].
  apply JCSum with HH' Y0Y1; auto. }
{ (* JCPi *)
  rename H0 into aY0Y1, H1 into aHH', H2 into aHaH', H4 into wk.
  destruct Hh as [wY0 wY1].
  pose proof ((fun x => JH_extra x IHHj1) I) as wH'.
  destruct (jobj_class wH') as [_ cH'].
  destruct (jobj_class wk) as [_ ck].
  assert (cobj HaH' CTEnv) as cHaH'.
  { apply (Happ_cobj aHaH'); auto using cobj, cobj_lift. }
  assert (jobj (b, vF) HNil (Jwf (HCons H k) CTEnv)) as wHk.
  { apply WHCons with H; auto using Happ_HNil. }
  assert (jobj (b, vF) (HCons H k) (Jwf (lift 1 0 H') CTEnv)) as wH'l.
  { apply (jobj_shift_0 wH' ck). }
  assert_clear IHHj2 wHaH'.
  { apply (Happ_Jwf_0 (b, vF) aHaH' cHaH'); auto. }
  clear_True.
  split; auto.
  intros [Htmp [Ha jkt']]; rewrite (Happ_eq Ha aHH') in *; clear Htmp Ha.
  pose proof ((fun x => jobj_TPi_inversion x jkt') I) as jt'.
  apply_clear IHHj3 wHk.
  curry IHHj3.
  assert (jobj (b, vF) H (Jwf Y0Y1 CPEnv)) as wY0Y1. { apply (Yapp_Jwf aY0Y1); auto. }
  assert_clear IHHj3 wY0Y1l. { apply (jobj_shift_0 wY0Y1); auto. }
  assert_clear IHHj3 c1; [|clear c1]. { apply WYNil; auto using cobj. }
  destruct IHHj3 as [_ IHHj3].
  apply JCPi with HH' HaH' s' Y0Y1; auto.
  apply IHHj3.
  exists HaH'.
  split; auto.
  destruct (jobj_class jt') as [ck' _]; inversion ck'; clear ck'; subst.
  apply @jobj_subst_0 with (s:=s') (k:=lift 1 (Hlength H') k')
        (j:=JT (lift 1 (1 + Hlength H') t') KStar); auto.
  apply @jobj_lift with (H1:=H) (H2:=HCons HNil k) (H3:=HCons H' k')
        (j:=JT t' KStar) (H1H2:=HCons H k) (H1H3:= HCons HH' k'); auto using cobj, Happ.
  simpl; rewrite plus_0_r; auto using Happ1. }
{ (* JCGen *)
  rename H0 into cY0, H1 into cY1, H2 into ct.
  pose proof ((fun x => jobj_extra x IHHj Hwf) I) as wk.
  split. { apply WHCons with H; auto using Happ0, WHNil. }
  intros [? [Ha jt]]; inversion Ha; clear Ha; subst.
  inversion H6; clear H6; subst.
  rename H2H1 into H.
  apply JCGen; auto. }
{ (* JCInst *)
  rename H0 into cY0, H1 into cY1, H2 into ct.
  split. { apply WHNil; auto. }
  intros [Htmp [Ha jkt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  pose proof ((fun x => jobj_TFor_inversion x jkt) I) as jt.
  apply JCInst; auto. }
{ (* JCUnfold *)
  clear H0.
  rename H1 into cY0, H2 into cY1, H3 into ct.
  split. { apply WHNil; auto. }
  intros [Htmp [Ha jkt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  pose proof ((fun x => jobj_TMu_inversion x jkt) I) as [jt rt].
  apply JCUnfold; auto. }
{ (* JCFold *)
  rename H0 into cY0, H1 into cY1, H2 into rt.
  split. { apply WHNil; auto. }
  intros [Htmp [Ha jkt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  assert_clear IHHj wHs.
  { apply WHCons with H; auto using Happ_HNil, WKStar. }
  clear_True.
  apply JCFold; auto. }
{ (* JCTop *)
  clear H0.
  rename H1 into cY0, H2 into cY1, H3 into ct.
  split. { apply WHNil; auto. }
  intros [Htmp [Ha jkt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  apply JCTop; auto. }
{ (* JCBot *)
  rename H0 into cY0, H1 into cY1.
  split. { apply WHNil; auto. }
  intros [Htmp [Ha jkt]]; inversion Ha; clear Ha; subst; rename Htmp into H.
  apply JCBot; auto. }
eapply JHNil; eauto.
{ (* JHCons *)
  rename H0 into aHH'.
  pose proof ((fun x => JH_extra x IHHj1) I) as wH'.
  destruct (jobj_class wH') as [_ cH'].
  assert (cobj HH' CTEnv) as cHH'. { apply (Happ_cobj aHH'); auto. }
  assert_clear IHHj2 wHH'. { apply (Happ_Jwf_0 (b, vF) aHH'); auto. }
  clear_True.
  apply JHCons with HH'; auto. }
eapply JGNil; eauto.
eapply JGCons; eauto.
eapply WKStar; eauto.
eapply WKOne; eauto.
eapply WKProd; eauto.
{ (* WKRes *)
  assert_clear IHHj2 wHk. { apply WHCons with H; auto using Happ_HNil. }
  clear_True.
  apply WKRes; auto. }
eapply WPTrue; eauto.
eapply WPAnd; eauto.
{ (* WPCoer *)
  rename H0 into aHH'.
  destruct (jobj_class Hj1) as [_ cH'].
  assert (cobj HH' CTEnv) as cHH'. { apply (Happ_cobj aHH'); auto. }
  assert_clear IHHj2 wHH'. { apply (Happ_Jwf_0 (b, vF) aHH' cHH'); auto. }
  clear_True.
  apply WPCoer with HH'; tauto.  }
eapply WPExi; eauto.
{ (* WPFor *)
  assert_clear IHHj2 wHk. { apply WHCons with H; auto using Happ_HNil. }
  clear_True.
  apply WPFor; auto. }
eapply WHNil; eauto.
{ (* WHCons *)
  rename H0 into aHH'.
  destruct (jobj_class IHHj1) as [_ cH'].
  assert (cobj HH' CTEnv) as cHH'. { apply (Happ_cobj aHH'); auto. }
  assert_clear IHHj2 wHH'. { apply (Happ_Jwf_0 (b, vF) aHH' cHH'); auto. }
  clear_True.
  apply WHCons with HH'; auto. }
eapply WYNil; eauto.
eapply WYCons; eauto.
Qed.

Lemma jterm_PF : forall {b H G a t}, jobj (b, vF) HNil (Jwf H CTEnv) ->
  jobj (b, vF) H (JG G) -> jterm (b, vP) H G a t -> jterm (b, vF) H G a t.
Proof.
intros b H G a t Hwf HG Hj.
remember (b, vP) as v.
induction Hj; subst v; assert (cobj H CTEnv) by apply (jobj_class Hwf);
repeat match goal with
  | H : True |- _ => clear H
  | H : mE (_, vP) -> _ |- _ => let H' := fresh "H" in
      pose proof (H I) as H'; clear H; rename H' into H
  | H : mS (_, vP) -> _ |- _ => clear H
  | Hx : ?P -> _, Hy : ?P |- _ => apply_clear Hx Hy
end.
(* 14: JVar *)
  apply JVar; auto.
  intros _.
  apply (Gnth_extra H2); auto.
(* 13: JLam *)
  pose proof (proj2 (jobj_PF Hwf H1 I) I) as jt.
  assert_clear IHHj c1; [auto using JGCons|].
  pose proof ((fun x => jterm_extra x IHHj Hwf) I c1).
  apply JLam; auto.
(* 12: JApp *)
  pose proof ((fun x => jterm_extra x IHHj1 Hwf) I HG) as Hts.
  destruct ((fun x => jobj_TArr_inversion x Hts) I).
  apply JApp with t; auto.
(* 11: JUnit *)
  apply JUnit; auto.
(* 10: JPair *)
  pose proof ((fun x => jterm_extra x IHHj1 Hwf) I HG).
  pose proof ((fun x => jterm_extra x IHHj2 Hwf) I HG).
  apply JPair; auto.
(* 9: JFst *)
  pose proof ((fun x => jterm_extra x IHHj Hwf) I HG) as Hts.
  destruct ((fun x => jobj_TProd_inversion x Hts) I).
  apply JFst with s; auto.
(* 8: JSnd *)
  pose proof ((fun x => jterm_extra x IHHj Hwf) I HG) as Hts.
  destruct ((fun x => jobj_TProd_inversion x Hts) I).
  apply JSnd with t; auto.
(* 7: JAbsurd *)
  pose proof (proj2 (jobj_PF Hwf H0 I) I).
  apply JAbsurd; auto.
(* 6: JInl *)
  pose proof ((fun x => jterm_extra x IHHj Hwf) I HG).
  pose proof (proj2 (jobj_PF Hwf H1 I) I).
  apply JInl; auto.
(* 5: JInr *)
  pose proof ((fun x => jterm_extra x IHHj Hwf) I HG).
  pose proof (proj2 (jobj_PF Hwf H0 I) I).
  apply JInr; auto.
(* 4: JMatch *)
  pose proof ((fun x => jterm_extra x IHHj1 Hwf) I HG) as Hts.
  destruct ((fun x => jobj_TSum_inversion x Hts) I).
  assert_clear IHHj3 c3; [auto using JGCons|].
  assert_clear IHHj2 c2; [auto using JGCons|].
  pose proof ((fun x => jterm_extra x IHHj2 Hwf) I c2).
  apply JMatch with tl tr; auto.
(* 3: JGen *)
  pose proof (proj2 (jobj_PF Hwf H0 I) I) as wk'.
  destruct (jobj_class wk') as [_ ck'].
  assert_clear IHHj c1.
  { apply WHCons with H; auto using Happ_HNil. }
  assert_clear IHHj c2.
  { apply (jobj_shift_0 HG ck'). }
  pose proof ((fun x => jterm_extra x IHHj c1) I c2) as eHHj.
  apply JGen; auto.
(* 2: JInst *)
  pose proof ((fun x => jterm_extra x IHHj Hwf) I HG) as Ht.
  pose proof ((fun x => jobj_TPi_inversion x Ht) I) as jt.
  pose proof (proj2 (jobj_PF Hwf H1 I) I).
  apply JInst with k'; auto.
(* 1: JCoer *)
  rename H0 into aHH', H4 into cH, H3 into jcP.
  destruct (jobj_class jcP) as [_ [_ [_ [cH' [ct cs]]]]].
  assert (cobj HH' CTEnv) as cHH' by (apply (Happ_cobj aHH'); auto).
  pose proof (jobj_PF Hwf jcP) as jcF; simpl in jcF.
  curry jcF.
  assert_clear jcF wYNil. { apply WYNil; auto. }
  apply_clear jcF wYNil.
  destruct jcF as [wH' jcF].
  assert_clear IHHj wHH'. { apply (Happ_Jwf_0 (b, vF) aHH'); auto. }
  assert_clear IHHj HGl. { apply (jobj_lift_0 aHH' cHH' HG). }
  pose proof ((fun x => jterm_extra x IHHj wHH' HGl) I).
  assert_clear jcF c1; [|clear c1]. { exists HH'; auto. }
  pose proof ((fun x => jobj_extra x jcF Hwf) I) as eC; simpl in eC.
  apply_clear eC wYNil.
  apply_clear eC wYNil.
  destruct eC as [jH' _].
  apply JCoer with H' HH' t; auto.
Qed.
