Require Import Omega.
Require Import String.

Require Import mxx.
Require Import Llanguage.
Require Import typesystem.
Require Import Ltypesystem.
Require Import typesystemdec.

Open Scope string_scope.

Inductive eobj : Set :=
(* k kinds coherence *)
| kexi (p : eobj) (K : eobj)
(* t types *)
| teq (t : eobj) (K : eobj)
| tVar (a : nat)
| tArr (t : eobj) (s : eobj)
| tProd (t : eobj) (s : eobj)
| tSum (t : eobj) (s : eobj)
| tFor (K : eobj) (t : eobj)
| tPi (K : eobj) (t : eobj)
| tMu (t : eobj)
| tBot
| tTop
| tUnit
| tPair (t1 : eobj) (t2 : eobj)
| tFst (t : eobj)
| tSnd (t : eobj)
| tPack (t : eobj) (p : eobj) (P : eobj)
| tUnpack (t : eobj)
(* p proofs *)
| peq (p : eobj) (P : eobj)
| pVar (c : nat)
| pTrue
| pPair (p1 : eobj) (p2 : eobj)
| pFst (p : eobj)
| pSnd (p : eobj)
| pExi (t : eobj)
| pLam (K : eobj) (p : eobj)
| pApp (p : eobj) (t : eobj)
| pRes (t : eobj)
| pFix (P : eobj) (p : eobj)
| pCoer (g : eobj) (t : eobj)
(* g coercions *)
| gProp (p : eobj)
| gRefl
| gTrans (g2 : eobj) (g1 : eobj)
| gWeak (g : eobj)
| gArr (g1 : eobj) (t : eobj) (g2 : eobj)
| gProd (g1 : eobj) (g2 : eobj)
| gSum (g1 : eobj) (g2 : eobj)
| gPi (h : eobj) (K : eobj) (g : eobj) (s : eobj)
| gGen (p : eobj)
| gInst (s : eobj)
| gUnfold
| gFold (t : eobj)
| gTop
| gBot (t : eobj)
(* h type environments coherence *)
| hNil
| hCons (h : eobj) (k : eobj)
(* G term environments *)
(* | wGNil *)
(* | wGCons (G : eobj) (t : eobj) *)
(* K kinds *)
| wKStar
| wKOne
| wKProd (K1 : eobj) (K2 : eobj)
| wKRes (K : eobj) (P : eobj)
(* P propositions *)
| wPTrue
| wPAnd (P1 : eobj) (P2 : eobj)
| wPCoer (h : eobj) (t : eobj) (s : eobj)
| wPExi (K : eobj)
| wPFor (K : eobj) (P : eobj)
(* H type environments wf *)
(* | wHNil *)
(* | wHCons (H' : eobj) (K' : eobj) *)
(* Y proposition environments wf *)
(* | wYNil *)
(* | wYCons (Y : eobj) (P : eobj) *)
.

Inductive eterm : Set :=
| eVar (x : nat)
| eLam (t : eobj) (a : eterm)
| eApp (a : eterm) (b : eterm)
| ePair (a : eterm) (b : eterm)
| eFst (a : eterm)
| eSnd (a : eterm)
| eInl (a : eterm) (S : eobj)
| eInr (T : eobj) (a : eterm)
| eMatch (a : eterm) (bl : eterm) (br : eterm)
| eGen (K : eobj) (a : eterm)
| eInst (a : eterm) (s : eobj)
| eCoer (g : eobj) (a : eterm)
.

Inductive jenv :=
| EK
| ET
| EP (Y0 : penv) (Y1 : penv)
| EC1 (Y0 : penv) (Y1 : penv)
| EC2 (Y0 : penv) (Y1 : penv) (H' : tenv) (t' : type)
| EH
| EG
| Ewf
.

Inductive message :=
| Empty : message
| Todo : message
| Impossible : message
| String : string -> message
| BadSyntax : obj -> message
| ExpectedGotClass : obj -> class -> class -> message
| ExpectedJEnv : jenv -> message
| ExpectedGotJudg : jenv -> judg -> message
| ExpectedGotObj : obj -> obj -> message
| ExpectedGotJwf : class -> class -> message
| GotTermType : term -> type -> message
| NotWellFounded : type -> message
| NoRecTypes : message
| Obj : eobj -> message -> message
| Term : eterm -> message -> message
.

Inductive exn A :=
| OK : A -> exn A
| Err : message -> exn A
.
Arguments OK [A] _.
Arguments Err [A] _.

Definition bind {A B} (x : exn A) (f : A -> exn B) :=
  match x with
    | OK a => f a
    | Err m => Err m
  end.
Notation "x >>= f" := (bind x f) (at level 60, right associativity).

Definition do_cobj f o c : exn (cobj o c) :=
  match get_cobj o with
    | Some (existT c' co) =>
      match class_dec c' c with
        | left Heq => OK (eq_rect c' _ co c Heq)
        | right _ => Err (f (ExpectedGotClass o c c'))
      end
    | _ => Err (f (BadSyntax o))
  end.

Definition xS {rec A} : mS (rec, vP) -> A.
Proof. intros mSv; exfalso; assumption. Defined.

Inductive agree : jenv -> judg -> Prop :=
| AK : forall {k}, agree EK (JK k)
| AT : forall {t k}, agree ET (JT t k)
| AP : forall {Y0 Y1 p}, agree (EP Y0 Y1) (JP Y0 Y1 p)
| AC2 : forall {Y0 Y1 H' t' t}, agree (EC2 Y0 Y1 H' t') (JC Y0 Y1 H' t' t)
| AH : forall {H'}, agree EH (JH H')
| AG : forall {G}, agree EG (JG G)
| Awf : forall {o c}, agree Ewf (Jwf o c)
.

Inductive Asig H H' := Acheck : forall HH', Happ H H' HH' -> Asig H H'.
Arguments Acheck [H H'] _ _.

Fixpoint Atc H H' : exn (Asig H H') :=
  match H' with
    | HNil => OK (Acheck H (Happ0 _))
    | HCons H' k' =>
      match Atc H H' with
        | OK (Acheck HH' aHH') =>
          OK (Acheck (HCons HH' k') (Happ1 k' _ _ _ aHH'))
        | Err x => Err x
      end
    | _ => Err (BadSyntax H')
  end.

Lemma JPCoer_aux : forall {H Y0 Y1 Y02 Y12 xt'2 H' xt' xt H'2 rec},
  agree (EC2 Y0 Y1 H' xt') (JC Y02 Y12 H'2 xt'2 xt) ->
  jobj (rec, vP) H (JC Y02 Y12 H'2 xt'2 xt) ->
  jobj (rec, vP) H (JC Y0 Y1 H' xt' xt).
Proof.
intros.
inversion H0; clear H0; subst.
assumption.
Qed.

Lemma JCProp_aux : forall {H Y0 Y1 Y02 Y12 xH' xt' H' t' xt rec},
  xt' = t' -> xH' = H' ->
  agree (EP Y0 Y1) (JP Y02 Y12 (PCoer xH' xt' xt)) ->
  jobj (rec, vP) H (JP Y02 Y12 (PCoer xH' xt' xt)) ->
  jobj (rec, vP) H (JP Y0 Y1 (PCoer H' t' xt)).
Proof.
intros; subst.
inversion H2; clear H2; subst.
assumption.
Qed.

Inductive optb A : bool -> Type :=
| Nob : optb A false
| Yesb : A -> optb A true
.
Arguments Nob [A].
Arguments Yesb [A] _.

Definition getb {A} (x : optb A true) : A :=
  match x with
    | Yesb x => x
  end.

Definition mapb0 {B b} (f : B) : optb B b :=
  match b with
    | false => Nob
    | true => Yesb f
  end.

Definition mapb1 {A1 B b} (f : A1 -> B) :=
  match b return optb _ b -> _ with
    | false => fun _ => Nob
    | true => fun x1 => Yesb (f (getb x1))
  end.

Definition mapb2 {A1 A2 B b} (f : A1 -> A2 -> B) :=
  match b return optb _ b -> optb _ b -> _ with
    | false => fun _ _ => Nob
    | true => fun x1 x2 => Yesb (f (getb x1) (getb x2))
  end.

Definition mapb3 {A1 A2 A3 B b} (f : A1 -> A2 -> A3 -> B) :=
  match b return optb _ b -> optb _ b -> optb _ b -> _ with
    | false => fun _ _ _ => Nob
    | true => fun x1 x2 x3 => Yesb (f (getb x1) (getb x2) (getb x3))
  end.

Definition mapb4 {A1 A2 A3 A4 B b} (f : A1 -> A2 -> A3 -> A4 -> B) :=
  match b return optb _ b -> optb _ b -> optb _ b -> optb _ b -> _ with
    | false => fun _ _ _ _ => Nob
    | true => fun x1 x2 x3 x4 => Yesb (f (getb x1) (getb x2) (getb x3) (getb x4))
  end.

Notation "!0 f" := (mapb0 f) (at level 80, no associativity).
Notation "!1 x1 f" := (mapb1 f x1) (at level 80, x1 at level 0, no associativity).
Notation "!2 x1 x2 f" := (mapb2 f x1 x2) (at level 80, x1, x2 at level 0, no associativity).
Notation "!3 x1 x2 x3 f" := (mapb3 f x1 x2 x3) (at level 80, x1, x2, x3 at level 0, no associativity).
Notation "!4 x1 x2 x3 x4 f" := (mapb4 f x1 x2 x3 x4) (at level 80, x1, x2, x3, x4 at level 0, no associativity).

Inductive osig b rec H ej :=
| ocheck : forall j, optb (jobj (rec, vP) H j) b -> optb (agree ej j) b -> osig b rec H ej
| Hcheck : forall H' HH', optb (Happ H H' HH') b -> osig b rec H ej
.
Arguments ocheck [b rec H ej] _ _ _.
Arguments Hcheck [b rec H ej] _ _ _.

Fixpoint otc b rec H j (o : eobj) : exn (osig b rec H j) :=
  match o, j with
    | kexi p K, EK =>
      match otc b rec H (EP YNil YNil) p with
        | OK (ocheck (JP YNil YNil (PExi k)) jp _) =>
            match otc b rec H Ewf K with
              | OK (ocheck (Jwf k' CKind) wk' _) =>
                  match obj_dec k' k with
                    | left Heq =>
                        OK (ocheck _ (!2 jp wk' fun jp wk' => JKexi _ H k jp
                         (fun _ => eq_rect k' (fun x => jobj _ _ (Jwf x _)) wk' k Heq)) (!0 AK))
                    | right _ => Err Impossible
                  end
              | OK (ocheck j _ _) => Err (Obj K (ExpectedGotJudg Ewf j))
              | OK (Hcheck _ _ _) => Err Impossible
              | Err x => Err x
            end
        | OK (ocheck j _ _) => Err (Obj p (ExpectedGotJudg (EP YNil YNil) j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | kexi _ _, g => Err (Obj o (ExpectedJEnv g))
    | tVar a, ET =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      match get_Hnth H a with
        | Some (existT k nHak) => OK (ocheck _ (!0 JTVar _ H a k cH nHak) (!0 AT))
        | _ => Err Impossible
      end
    | tVar _, g => Err (Obj o (ExpectedJEnv g))
    | tArr t s, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt KStar) jt _) =>
          match otc b rec H ET s with
            | OK (ocheck (JT xs KStar) js _) =>
              OK (ocheck _ (!2 jt js JTArr _ H xt xs) (!0 AT))
            | OK (ocheck (JT _ k) _ _) => Err (Obj s (ExpectedGotObj KStar k))
            | OK (ocheck j _ _) => Err (Obj s (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tArr _ _, g => Err (Obj o (ExpectedJEnv g))
    | tProd t s, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt KStar) jt _) =>
          match otc b rec H ET s with
            | OK (ocheck (JT xs KStar) js _) =>
              OK (ocheck _ (!2 jt js JTProd _ H xt xs) (!0 AT))
            | OK (ocheck (JT _ k) _ _) => Err (Obj s (ExpectedGotObj KStar k))
            | OK (ocheck j _ _) => Err (Obj s (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tProd _ _, g => Err (Obj o (ExpectedJEnv g))
    | tSum t s, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt KStar) jt _) =>
          match otc b rec H ET s with
            | OK (ocheck (JT xs KStar) js _) =>
              OK (ocheck _ (!2 jt js JTSum _ H xt xs) (!0 AT))
            | OK (ocheck (JT _ k) _ _) => Err (Obj s (ExpectedGotObj KStar k))
            | OK (ocheck j _ _) => Err (Obj s (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tSum _ _, g => Err (Obj o (ExpectedJEnv g))
    | tFor K t, ET =>
      match otc b rec H Ewf K with
        | OK (ocheck (Jwf k CKind) wk _) =>
          match otc b rec (HCons H k) ET t with
            | OK (ocheck (JT xt KStar) jt _) =>
              OK (ocheck _ (!2 wk jt fun wk => JTFor _ H k xt (fun _ => wk)) (!0 AT))
            | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
            | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck (Jwf o c) _ _) => Err (Obj K (ExpectedGotJwf CKind c))
        | OK (ocheck j _ _) => Err (Obj K (ExpectedGotJudg Ewf j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tFor _ _, g => Err (Obj o (ExpectedJEnv g))
    | tMu t, ET =>
      match rec with
        | true =>
          match otc b true (HCons H KStar) ET t with
            | OK (ocheck (JT t KStar) jt _) =>
              match get_jrec 0 t WF with
                | Some jr =>
                  OK (ocheck _ (!1 jt fun jt => JTMu (true, vP) H t jr jt I) (!0 AT))
                | None => Err (NotWellFounded t)
              end
            | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
            | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | false => Err (Obj o NoRecTypes)
      end
    | tMu _, g => Err (Obj o (ExpectedJEnv g))
    | tBot, ET =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 JTBot _ H cH) (!0 AT))
    | tBot, g => Err (Obj o (ExpectedJEnv g))
    | tTop, ET =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 JTTop _ H cH) (!0 AT))
    | tTop, g => Err (Obj o (ExpectedJEnv g))
    | tUnit, ET =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 JTUnit _ H cH) (!0 AT))
    | tUnit, g => Err (Obj o (ExpectedJEnv g))
    | tPair t1 t2, ET =>
      match otc b rec H ET t1 with
        | OK (ocheck (JT x1 k1) j1 _) =>
          match otc b rec H ET t2 with
            | OK (ocheck (JT x2 k2) j2 _) =>
              OK (ocheck _ (!2 j1 j2 JTPair _ H x1 x2 k1 k2) (!0 AT))
            | OK (ocheck j _ _) => Err (Obj t2 (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj t1 (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tPair _ _, g => Err (Obj o (ExpectedJEnv g))
    | tFst t, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT x (KProd k1 k2)) j _) =>
          OK (ocheck _ (!1 j JTFst _ H x k1 k2) (!0 AT))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tFst _, g => Err (Obj o (ExpectedJEnv g))
    | tSnd t, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT x (KProd k1 k2)) j _) =>
          OK (ocheck _ (!1 j JTSnd _ H x k1 k2) (!0 AT))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tSnd _, g => Err (Obj o (ExpectedJEnv g))
    | tPack t p P, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt k) jt _) =>
          match otc b rec H (EP YNil YNil) p with
            | OK (ocheck (JP YNil YNil xtp) jp _) =>
              match otc b rec (HCons H k) Ewf P with
                | OK (ocheck (Jwf xp CProp) jP _) =>
                  match obj_dec xtp (subst xt 0 xp) with
                    | left Heq =>
                      OK (ocheck _ (!3 jP jt jp fun jP jt jp => JTPack _ H xt k xp (fun _ => jP) jt
                                   (eq_rect xtp (fun x => jobj _ _ (JP _ _ x)) jp _ Heq)) (!0 AT))
                    | right _ => Err (Obj p (ExpectedGotObj (subst xt 0 xp) xtp))
                  end
                | OK (ocheck j _ _) => Err (Obj P (ExpectedGotJudg Ewf j))
                | OK (Hcheck _ _ _) => Err Impossible
                | Err x => Err x
              end
            | OK (ocheck j _ _) => Err (Obj p (ExpectedGotJudg (EP YNil YNil) j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tPack _ _ _, g => Err (Obj o (ExpectedJEnv g))
    | tUnpack t, ET =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt (KRes k p)) jt _) =>
          OK (ocheck _ (!1 jt JTUnpack _ H xt k p) (!0 AT))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | tUnpack _, g => Err (Obj o (ExpectedJEnv g))
    (* | pTrue *)
    (* | pPair (p1 : eobj) (p2 : eobj) *)
    (* | pFst (p : eobj) *)
    (* | pSnd (p : eobj) *)
    | pExi t, EP Y0 Y1 =>
      do_cobj (Obj o) Y0 CPEnv >>= fun cY0 =>
      do_cobj (Obj o) Y1 CPEnv >>= fun cY1 =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt xk) jt _) =>
          OK (ocheck _ (!1 jt JPExi _ H Y0 Y1 xt xk cY0 cY1) (!0 AP))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | pExi _, g => Err (Obj o (ExpectedJEnv g))
    | pRes t, EP Y0 Y1 =>
      do_cobj (Obj o) Y0 CPEnv >>= fun cY0 =>
      do_cobj (Obj o) Y1 CPEnv >>= fun cY1 =>
      match otc b rec H ET t with
        | OK (ocheck (JT xt (KRes k p)) jt _) =>
          OK (ocheck _ (!1 jt JPRes _ H Y0 Y1 xt k p cY0 cY1) (!0 AP))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | pRes _, g => Err (Obj o (ExpectedJEnv g))
    | pCoer g t', EP Y0 Y1 =>
      match otc b rec H (EC1 Y0 Y1) g with
        | OK (Hcheck H' HH' aHH') =>
          match otc b rec HH' ET t' with
            | OK (ocheck (JT xt' KStar) jt' _) =>
              match otc b rec H (EC2 Y0 Y1 H' xt') g with
                | OK (ocheck (JC Y02 Y12 H'2 xt'2 xt) jg gr) =>
                  OK (ocheck _ (!4 aHH' jg gr jt' fun aHH' jg gr jt' =>
                                JPCoer _ H Y0 Y1 H' HH' xt' xt aHH'
                                       (JPCoer_aux gr jg) jt') (!0 AP))
                | OK (ocheck j _ _) => Err (Obj g (ExpectedGotJudg (EC2 Y0 Y1 H' xt') j))
                | OK (Hcheck _ _ _) => Err Impossible
                | Err x => Err x
              end
            | OK (ocheck j _ _) => Err (Obj t' (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | pCoer _ _, g => Err (Obj o (ExpectedJEnv g))
    | gProp p, EC1 Y0 Y1 =>
      match otc b rec H (EP Y0 Y1) p with
        | OK (ocheck (JP _ _ (PCoer H' _ _)) _ _) =>
          match Atc H H' with
            | OK (Acheck HH' aHH') => OK (Hcheck H' HH' (!0 aHH'))
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj p (ExpectedGotJudg (EP Y0 Y1) j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | gProp p, EC2 Y0 Y1 H' t' =>
      match otc b rec H (EP Y0 Y1) p with
        | OK (ocheck (JP Y02 Y12 (PCoer xH' xt' xt)) jp gr) =>
            match obj_dec xH' H', obj_dec xt' t' with
              | left Heq1, left Heq2 =>
                  OK (ocheck _ (!2 jp gr fun jp gr => JCProp _ H Y0 Y1 H' t' xt
                               (JCProp_aux Heq2 Heq1 gr jp)) (!0 AC2))
              | _, _ => Err (String "otc gProp EC2")
            end
        | OK (ocheck j _ _) => Err (Obj p (ExpectedGotJudg (EP Y0 Y1) j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | gProp _, g => Err (Obj o (ExpectedJEnv g))
    | gRefl, EC1 _ _ => OK (Hcheck HNil H (!0 Happ0 _))
    | gRefl, EC2 Y0 Y1 HNil t =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      do_cobj (Obj o) Y0 CPEnv >>= fun cY0 =>
      do_cobj (Obj o) Y1 CPEnv >>= fun cY1 =>
      do_cobj (Obj o) t CType >>= fun ct =>
      OK (ocheck _ (!0 JCRefl _ H Y0 Y1 t cH cY0 cY1 ct) (!0 AC2))
    | gRefl, g => Err (Obj o (ExpectedJEnv g))
    (* | gTrans (g2 : eobj) (g1 : eobj) *)
    (* | gWeak (g : eobj) *)
    (* | gArr (g1 : eobj) (t : eobj) (g2 : eobj) *)
    | gGen k, EC1 Y0 Y1 =>
      match otc b rec H EK k with
        | OK (ocheck (JK k) _ _) =>
          OK (Hcheck (HCons HNil k) (HCons H k) (!0 Happ1 k _ _ _ (Happ0 _)))
        | OK (ocheck j _ _) => Err (Obj k (ExpectedGotJudg EK j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | gGen pk, EC2 Y0 Y1 (HCons HNil k) t =>
      do_cobj (Obj o) Y0 CPEnv >>= fun cY0 =>
      do_cobj (Obj o) Y1 CPEnv >>= fun cY1 =>
      do_cobj (Obj o) t CType >>= fun ct =>
      match otc b rec H EK pk with
        | OK (ocheck (JK k') jk _) =>
          match obj_dec k' k with
            | left Heq =>
              OK (ocheck _ (!1 jk fun jk => JCGen _ H Y0 Y1 k t cY0 cY1 ct
                           (eq_rect k' (fun x => jobj _ _ (JK x)) jk k Heq) xS) (!0 AC2))
            | right _ => Err Impossible
          end
        | OK (ocheck j _ _) => Err (Obj pk (ExpectedGotJudg EK j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | gGen _, g => Err (Obj o (ExpectedJEnv g))
    | gInst s, EC1 Y0 Y1 => OK (Hcheck HNil H (!0 Happ0 _))
    | gInst s, EC2 Y0 Y1 HNil (TFor k t) =>
      do_cobj (Obj o) Y0 CPEnv >>= fun cY0 =>
      do_cobj (Obj o) Y1 CPEnv >>= fun cY1 =>
      do_cobj (Obj o) t CType >>= fun ct =>
      match otc b rec H ET s with
        | OK (ocheck (JT xs k') js _) =>
          match obj_dec k' k with
            | left Heq =>
              OK (ocheck _ (!1 js fun js => JCInst _ H Y0 Y1 k t xs cY0 cY1 ct xS
                           (eq_rect k' (fun k => jobj _ _ (JT _ k)) js k Heq)) (!0 AC2))
            | right _ => Err (Obj s (ExpectedGotObj k k'))
          end
        | OK (ocheck j _ _) => Err (Obj s (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | gInst _, g => Err (Obj o (ExpectedJEnv g))
    (* | gTop *)
    (* | gBot (t : eobj) *)
    | wKStar, Ewf =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 WKStar _ H cH) (!0 Awf))
    | wKStar, g => Err (Obj o (ExpectedJEnv g))
    | wKOne, Ewf =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 WKOne _ H cH) (!0 Awf))
    | wKOne, g => Err (Obj o (ExpectedJEnv g))
    | wKProd K1 K2, Ewf =>
      match otc b rec H Ewf K1 with
        | OK (ocheck (Jwf k1 CKind) j1 _) =>
          match otc b rec H Ewf K2 with
            | OK (ocheck (Jwf k2 CKind) j2 _) =>
              OK (ocheck _ (!2 j1 j2 WKProd _ H k1 k2) (!0 Awf))
            | OK (ocheck j _ _) => Err (Obj K2 (ExpectedGotJudg Ewf j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj K1 (ExpectedGotJudg Ewf j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | wKProd _ _, g => Err (Obj o (ExpectedJEnv g))
    | wKRes K P, Ewf =>
      match otc b rec H Ewf K with
        | OK (ocheck (Jwf k CKind) jk _) =>
          match otc b rec (HCons H k) Ewf P with
            | OK (ocheck (Jwf p CProp) jp _) =>
              OK (ocheck _ (!2 jk jp WKRes _ H k p) (!0 Awf))
            | OK (ocheck j _ _) => Err (Obj P (ExpectedGotJudg Ewf j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj K (ExpectedGotJudg Ewf j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | wKRes _ _, g => Err (Obj o (ExpectedJEnv g))
    | wPTrue, Ewf =>
      do_cobj (Obj o) H CTEnv >>= fun cH =>
      OK (ocheck _ (!0 WPTrue _ H cH) (!0 Awf))
    | wPTrue, g => Err (Obj o (ExpectedJEnv g))
    | wPAnd P1 P2, Ewf =>
      match otc b rec H Ewf P1 with
        | OK (ocheck (Jwf p1 CProp) j1 _) =>
          match otc b rec H Ewf P2 with
            | OK (ocheck (Jwf p2 CProp) j2 _) =>
              OK (ocheck _ (!2 j1 j2 WPAnd _ H p1 p2) (!0 Awf))
            | OK (ocheck j _ _) => Err (Obj P2 (ExpectedGotJudg Ewf j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj P1 (ExpectedGotJudg Ewf j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | wPAnd _ _, g => Err (Obj o (ExpectedJEnv g))
    | wPCoer h t' t, Ewf =>
      match otc b rec H EH h with
        | OK (ocheck (JH H') jH' _) =>
          match otc b rec H ET t with
            | OK (ocheck (JT xt KStar) jt _) =>
              match Atc H H' with
                | OK (Acheck HH' aHH') =>
                  match otc b rec HH' ET t' with
                    | OK (ocheck (JT xt' KStar) jt' _) =>
                      OK (ocheck _ (!3 jH' jt' jt WPCoer _ H H' HH' xt' xt aHH') (!0 Awf))
                    | OK (ocheck j _ _) => Err (Obj t' (ExpectedGotJudg ET j))
                    | OK (Hcheck _ _ _) => Err Impossible
                    | Err x => Err x
                  end
                | Err x => Err x
              end
            | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
            | OK (Hcheck _ _ _) => Err Impossible
            | Err x => Err x
          end
        | OK (ocheck j _ _) => Err (Obj h (ExpectedGotJudg EH j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | wPCoer _ _ _, g => Err (Obj o (ExpectedJEnv g))
    (* | wPExi (K : eobj) *)
    (* | wPFor (K : eobj) (P : eobj) *)
    | _, _ => Err (Obj o Todo)
  end.

Definition otcj rec H j o : exn judg :=
  match otc false rec H j o with
    | OK (ocheck j _ _) => OK j
    | OK (Hcheck _ _ _) => Err Impossible
    | Err x => Err x
  end.

(*
Eval compute in (otcj true (HCons HNil KStar) ET (tVar 0)).
Eval compute in (otcj true (HCons HNil KStar) ET (tArr (tVar 0) (tVar 0))).
Eval compute in (otcj true HNil ET (tFor wKStar (tVar 0))).
Eval compute in (otcj true HNil ET tBot).
Eval compute in (otcj true HNil (EC2 YNil YNil HNil TTop) gRefl).
Eval compute in (otcj true HNil (EC2 YNil YNil (HCons HNil KStar) (TVar 0)) (gGen (pExi tTop))).
*)

Lemma JCoer_aux : forall {H H' xt H'2 xt2 xs rec},
  agree (EC2 YNil YNil H' xt) (JC YNil YNil H'2 xt2 xs) ->
  jobj (rec, vP) H (JC YNil YNil H'2 xt2 xs) ->
  jobj (rec, vP) H (JC YNil YNil H' xt xs).
Proof.
intros.
inversion H0; clear H0; subst.
assumption.
Qed.

Inductive asig b rec H G := acheck : forall a t, optb (jterm (rec, vP) H G a t) b -> asig b rec H G.
Arguments acheck [b rec H G] _ _ _.

Fixpoint atc z rec H G (a : eterm) : exn (asig z rec H G) :=
  match a with
    | eVar x =>
      match (get_cobj G, get_Gnth G x) with
        | (Some (existT CAEnv cG), Some (existT t nGxt)) =>
           OK (acheck (Var x) t (!0 JVar _ H G x t cG xS nGxt))
        | _ => Err (Term a Impossible)
      end
    | eLam t a =>
      match otc z rec H ET t with
        | OK (ocheck (JT xt KStar) jt _) =>
          match atc z rec H (GCons G xt) a with
            | OK (acheck xa xs ja) =>
              OK (acheck (Lam xa) (TArr xt xs) (!2 jt ja JLam _ H G xa xt xs xS))
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | eApp a b =>
      match atc z rec H G a with
        | OK (acheck xa (TArr xt xs) ja) =>
          match atc z rec H G b with
            | OK (acheck xb xt' jb) =>
              match obj_dec xt' xt with
                | left Heq =>
                  OK (acheck (App xa xb) xs (!2 ja jb fun ja jb =>
                             JApp _ H G xa xb xt xs xS xS ja (eq_rect xt' _ jb xt Heq)))
                | right _ => Err (Term b (GotTermType xb xt'))
              end
            | Err x => Err x
          end
        | OK (acheck ra rt _) => Err (Term a (GotTermType ra rt))
        | Err x => Err x
      end
    | eInl a s =>
      match otc z rec H ET s with
        | OK (ocheck (JT xs KStar) js _) =>
          match atc z rec H G a with
            | OK (acheck xa xt ja) =>
              OK (acheck (Inl xa) (TSum xt xs) (!2 js ja JInl _ H G xa xt xs xS))
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj s (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj s (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | eInr t a =>
      match otc z rec H ET t with
        | OK (ocheck (JT xt KStar) jt _) =>
          match atc z rec H G a with
            | OK (acheck xa xs ja) =>
              OK (acheck (Inr xa) (TSum xt xs) (!2 jt ja fun jt => JInr _ H G xa xt xs jt xS))
            | Err x => Err x
          end
        | OK (ocheck (JT _ k) _ _) => Err (Obj t (ExpectedGotObj KStar k))
        | OK (ocheck j _ _) => Err (Obj t (ExpectedGotJudg ET j))
        | OK (Hcheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | eCoer g a =>
      match otc z rec H (EC1 YNil YNil) g with
        | OK (Hcheck H' HH' aHH') =>
          match atc z rec HH' (lift (Hlength H') 0 G) a with
            | OK (acheck xa xt ja) =>
              match otc z rec H (EC2 YNil YNil H' xt) g with
                | OK (ocheck (JC YNil YNil H'2 xt2 xs) jg gr) =>
                  OK (acheck xa xs (!4 aHH' ja jg gr fun aHH' ja jg gr =>
                        JCoer _ H H' HH' G xa xt xs aHH' xS xS ja (JCoer_aux gr jg)))
                | OK (ocheck j _ _) => Err (Obj g (ExpectedGotJudg (EC2 YNil YNil H' xt) j))
                | OK (Hcheck _ _ _) => Err Impossible
                | Err x => Err x
              end
            | Err x => Err x
          end
        | OK (ocheck _ _ _) => Err Impossible
        | Err x => Err x
      end
    | _ => Err (Term a Todo)
  end.

Definition atcj b H G a : exn (term * type) :=
  match atc false b H G a with
    | OK (acheck ra rt _) => OK (ra, rt)
    | Err x => Err x
  end.

(*
Eval compute in (atcj true HNil GNil (eVar 0)).
Eval compute in (atcj true (HCons HNil KStar) GNil (eLam (tVar 0) (eVar 0))).
Eval compute in (atcj true (HCons HNil KStar) GNil
                      (eLam (tArr (tVar 0) (tVar 0)) (eLam (tVar 0) (eApp (eVar 1) (eVar 0))))).
Eval compute in (atcj true HNil GNil
  (eCoer (gGen (pExi tTop)) (eLam (tVar 0) (eVar 0)))).
Eval compute in (atcj true HNil GNil
  (eCoer (gInst tBot) (eCoer (gGen (pExi tTop)) (eLam (tVar 0) (eVar 0))))).
*)

