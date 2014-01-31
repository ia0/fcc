Require Import Omega.
Require Import List.

Require Import mxx.
Require Import Flanguage.
Require Export typesystem.

(** * System Fcc (indexed version) *)

(** We write [jterm H G a t] the indexed term judgment. It is exactly
like the lambda term judgment in [Ltypesystem_v] with index
annotations.
*)
Inductive jterm v : tenv -> aenv -> term -> type -> Prop :=
| JVar : forall H G k x t,
  cobj G CAEnv ->
  (mS v -> jobj v H (JT t KStar)) ->
  Gnth G x t ->
  jterm v H G (Var k x) t
| JLam : forall H G k a t s,
  (mS v -> jobj v H (JT s KStar)) ->
  jobj v H (JT t KStar) ->
  jterm v H (GCons G t) a s ->
  jterm v H G (Lam k a) (TArr t s)
| JApp : forall H G k a b t s,
  (mS v -> jobj v H (JT t KStar)) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a (TArr t s) ->
  jterm v H G b t ->
  jterm v H G (App k a b) s
| JUnit : forall H G k,
  cobj H CTEnv ->
  cobj G CAEnv ->
  jterm v H G (Unit k) TOne
| JPair : forall H G k a b t s,
  (mS v -> jobj v H (JT t KStar)) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a t ->
  jterm v H G b s ->
  jterm v H G (Pair k a b) (TProd t s)
| JFst : forall H G k a t s,
  (mS v -> jobj v H (JT t KStar)) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a (TProd t s) ->
  jterm v H G (Fst k a) t
| JSnd : forall H G k a t s,
  (mS v -> jobj v H (JT t KStar)) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a (TProd t s) ->
  jterm v H G (Snd k a) s
| JAbsurd : forall H G k a s,
  jterm v H G a TVoid ->
  jobj v H (JT s KStar) ->
  jterm v H G (Absurd k a) s
| JInl : forall H G k a t s,
  (mS v -> jobj v H (JT t KStar)) ->
  jobj v H (JT s KStar) ->
  jterm v H G a t ->
  jterm v H G (Inl k a) (TSum t s)
| JInr : forall H G k a t s,
  jobj v H (JT t KStar) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a s ->
  jterm v H G (Inr k a) (TSum t s)
| JMatch : forall H G k a bl br tl tr s,
  (mS v -> jobj v H (JT tl KStar)) ->
  (mS v -> jobj v H (JT tr KStar)) ->
  (mS v -> jobj v H (JT s KStar)) ->
  jterm v H G a (TSum tl tr) ->
  jterm v H (GCons G tl) bl s ->
  jterm v H (GCons G tr) br s ->
  jterm v H G (Match k a bl br) s
| JGen : forall H G k k' a t,
  (mE v -> jobj v H (Jwf k' CKind)) ->
  (mS v -> jobj v (HCons H k') (JT t KStar)) ->
  jterm v (HCons H k') (lift 1 0 G) a t ->
  jterm v H G (Gen k a) (TPi k' t)
| JInst : forall H G k k' a t s,
  (mS v -> jobj v (HCons H k') (JT t KStar)) ->
  jterm v H G a (TPi k' t) ->
  jobj v H (JT s k') ->
  jterm v H G (Inst k a) (subst s 0 t)
| JCoer : forall H H' HH' G a t s,
  Happ H H' HH' ->
  (mS v -> jobj v H (JH H')) ->
  (mS v -> jobj v HH' (JT t KStar)) ->
  jterm v HH' (lift (Hlength H') 0 G) a t ->
  jobj v H (JC YNil YNil H' t s) ->
  jterm v H G a s
.
