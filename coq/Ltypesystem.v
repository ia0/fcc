Require Import Omega.
Require Import List.

Require Import mxx.
Require Import Llanguage.
Require Export typesystem.

(** * System Fcc (lambda version) *)

(** We write [jterm H G a t] the lambda term judgment. The [C], [E],
and [S] annotations follow the description given before the definition
of the object judgment (inductive [jobj]).
*)
Inductive jterm v : tenv -> aenv -> term -> type -> Prop :=
| JVar : forall H G x t,
  cobj G CAEnv ->
  (mS v -> jobj v H (JT t t KStar)) ->
  Gnth G x t ->
  jterm v H G (Var x) t
| JLam : forall H G a t s,
  (mS v -> jobj v H (JT s s KStar)) ->
  jobj v H (JT t t KStar) ->
  jterm v H (GCons G t) a s ->
  jterm v H G (Lam a) (TArr t s)
| JApp : forall H G a b t s,
  (mS v -> jobj v H (JT t t KStar)) ->
  (mS v -> jobj v H (JT s s KStar)) ->
  jterm v H G a (TArr t s) ->
  jterm v H G b t ->
  jterm v H G (App a b) s
(* | JUnit : forall H G, *)
(*   cobj H CTEnv -> *)
(*   cobj G CAEnv -> *)
(*   jterm v H G (Unit) TOne *)
(* | JPair : forall H G a b t s, *)
(*   (mS v -> jobj v H (JT t KStar)) -> *)
(*   (mS v -> jobj v H (JT s KStar)) -> *)
(*   jterm v H G a t -> *)
(*   jterm v H G b s -> *)
(*   jterm v H G (Pair a b) (TProd t s) *)
(* | JFst : forall H G a t s, *)
(*   (mS v -> jobj v H (JT t KStar)) -> *)
(*   (mS v -> jobj v H (JT s KStar)) -> *)
(*   jterm v H G a (TProd t s) -> *)
(*   jterm v H G (Fst a) t *)
(* | JSnd : forall H G a t s, *)
(*   (mS v -> jobj v H (JT t KStar)) -> *)
(*   (mS v -> jobj v H (JT s KStar)) -> *)
(*   jterm v H G a (TProd t s) -> *)
(*   jterm v H G (Snd a) s *)
(* | JAbsurd : forall H G a s, *)
(*   jterm v H G a TVoid -> *)
(*   jobj v H (JT s KStar) -> *)
(*   jterm v H G (Absurd a) s *)
(* | JInl : forall H G a t s, *)
(*   (mS v -> jobj v H (JT t KStar)) -> *)
(*   jobj v H (JT s KStar) -> *)
(*   jterm v H G a t -> *)
(*   jterm v H G (Inl a) (TSum t s) *)
(* | JInr : forall H G a t s, *)
(*   jobj v H (JT t KStar) -> *)
(*   (mS v -> jobj v H (JT s KStar)) -> *)
(*   jterm v H G a s -> *)
(*   jterm v H G (Inr a) (TSum t s) *)
(* | JMatch : forall H G a bl br tl tr s, *)
(*   (mS v -> jobj v H (JT tl KStar)) -> *)
(*   (mS v -> jobj v H (JT tr KStar)) -> *)
(*   (mS v -> jobj v H (JT s KStar)) -> *)
(*   jterm v H G a (TSum tl tr) -> *)
(*   jterm v H (GCons G tl) bl s -> *)
(*   jterm v H (GCons G tr) br s -> *)
(*   jterm v H G (Match a bl br) s *)
(* | JGen : forall H G k' a t, *)
(*   (mE v -> jobj v H (Jwf k' CKind)) -> *)
(*   (mS v -> jobj v (HCons H k') (JT t KStar)) -> *)
(*   jterm v (HCons H k') (lift 1 0 G) a t -> *)
(*   jterm v H G (Gen a) (TPi k' t) *)
(* | JInst : forall H G k' a t s, *)
(*   (mS v -> jobj v (HCons H k') (JT t KStar)) -> *)
(*   jterm v H G a (TPi k' t) -> *)
(*   jobj v H (JT s k') -> *)
(*   jterm v H G (Inst a) (subst s 0 t) *)
| JCoer : forall H H' HH' G a t s,
  Happ H H' HH' ->
  (mS v -> jobj v H (JH H')) ->
  (mS v -> jobj v HH' (JT t t KStar)) ->
  jterm v HH' (lift (Hlength H') 0 G) a t ->
  jobj v H (JC YNil YNil H' t s) ->
  jterm v H G a s
.
