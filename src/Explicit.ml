open Printf
open List

exception Resolve of string list * string list
exception NotFound of string

type ('bind, 'var) cokind =
  | Kexi of ('bind, 'var) proof * ('bind, 'var) kind
and ('bind, 'var) typ =
  | Teq of ('bind, 'var) typ * ('bind, 'var) kind
  | TVar of 'var
  | TArr of ('bind, 'var) typ * ('bind, 'var) typ
  | TProd of ('bind, 'var) typ * ('bind, 'var) typ
  | TSum of ('bind, 'var) typ * ('bind, 'var) typ
  | TFor of 'bind * ('bind, 'var) kind * ('bind, 'var) typ
  | TPi of 'bind * ('bind, 'var) kind * ('bind, 'var) typ
  | TMu of 'bind * ('bind, 'var) typ
  | TBot
  | TTop
  | TUnit
  | TPair of ('bind, 'var) typ * ('bind, 'var) typ
  | TFst of ('bind, 'var) typ
  | TSnd of ('bind, 'var) typ
  | TPack of 'bind * ('bind, 'var) typ * ('bind, 'var) proof * ('bind, 'var) prop
  | TUnpack of ('bind, 'var) typ
and ('bind, 'var) proof =
  | Peq of ('bind, 'var) proof * ('bind, 'var) prop
  | PVar of 'var
  | PTrue
  | PPair of ('bind, 'var) proof * ('bind, 'var) proof
  | PFst of ('bind, 'var) proof
  | PSnd of ('bind, 'var) proof
  | PExi of ('bind, 'var) typ
  | PLam of 'bind * ('bind, 'var) kind * ('bind, 'var) proof
  | PApp of ('bind, 'var) proof * ('bind, 'var) typ
  | PRes of ('bind, 'var) typ
  | PFix of 'bind * ('bind, 'var) prop * ('bind, 'var) proof
  | PCoer of ('bind, 'var) coer * ('bind, 'var) typ
and ('bind, 'var) coer =
  | GProp of ('bind, 'var) proof
  | GRefl
  | GTrans of ('bind, 'var) coer * ('bind, 'var) coer
  | GWeak of ('bind, 'var) coer
  | GArr of ('bind, 'var) coer * ('bind, 'var) typ * ('bind, 'var) coer
  | GProd of ('bind, 'var) coer * ('bind, 'var) coer
  | GSum of ('bind, 'var) coer * ('bind, 'var) coer
  | GPi of ('bind, 'var) cotenv * 'bind * ('bind, 'var) kind * ('bind, 'var) coer * ('bind, 'var) typ
  | GGen of 'bind * ('bind, 'var) cokind
  | GInst of ('bind, 'var) typ
  | GUnfold
  | GFold of 'bind * ('bind, 'var) typ
  | GTop
  | GBot of ('bind, 'var) typ
and ('bind, 'var) cotenv =
  | HNil
  | HCons of ('bind, 'var) cotenv * 'bind * ('bind, 'var) cokind
and ('bind, 'var) kind =
  | WKStar
  | WKOne
  | WKProd of ('bind, 'var) kind * ('bind, 'var) kind
  | WKRes of 'bind * ('bind, 'var) kind * ('bind, 'var) prop
and ('bind, 'var) prop =
  | WPTrue
  | WPAnd of ('bind, 'var) prop * ('bind, 'var) prop
  | WPCoer of ('bind, 'var) cotenv * ('bind, 'var) typ * ('bind, 'var) typ
  | WPExi of ('bind, 'var) kind
  | WPFor of 'bind * ('bind, 'var) kind * ('bind, 'var) prop
and ('bind, 'var) tenv =
  | WHNil
  | WHCons of ('bind, 'var) tenv * 'bind * ('bind, 'var) kind

type ('bind, 'var) term =
  | EVar of 'var
  | ELam of 'bind * ('bind, 'var) typ * ('bind, 'var) term
  | EApp of ('bind, 'var) term * ('bind, 'var) term
  | EPair of ('bind, 'var) term * ('bind, 'var) term
  | EFst of ('bind, 'var) term
  | ESnd of ('bind, 'var) term
  | EInl of ('bind, 'var) term * ('bind, 'var) typ
  | EInr of ('bind, 'var) typ * ('bind, 'var) term
  | EMatch of ('bind, 'var) term * 'bind * ('bind, 'var) term * 'bind * ('bind, 'var) term
  | EGen of ('bind, 'var) term
  | EInst of ('bind, 'var) term
  | ECoer of ('bind, 'var) coer * ('bind, 'var) term

type ncokind = (string, string) cokind
type ntyp = (string, string) typ
type nproof = (string, string) proof
type ncoer = (string, string) coer
type ncotenv = (string, string) cotenv
type nkind = (string, string) kind
type nprop = (string, string) prop
type ntenv = (string, string) tenv
type nterm = (string, string) term

type dcokind = (unit, int) cokind
type dtyp = (unit, int) typ
type dproof = (unit, int) proof
type dcoer = (unit, int) coer
type dcotenv = (unit, int) cotenv
type dkind = (unit, int) kind
type dprop = (unit, int) prop
type dtenv = (unit, int) tenv
type dterm = (unit, int) term

let rec print_cokind (k : dcokind) =
  match k with
  | Kexi (p, k) -> sprintf "(kexi %s %s)" (print_proof p) (print_kind k)
and print_typ (t : dtyp) =
  match t with
  | Teq (t, k) -> sprintf "(teq %s %s)" (print_typ t) (print_kind k)
  | TVar i -> sprintf "(tVar %d)" i
  | TArr (t, s) -> sprintf "(tArr %s %s)" (print_typ t) (print_typ s)
  | TProd (t, s) -> sprintf "(tProd %s %s)" (print_typ t) (print_typ s)
  | TSum (t, s) -> sprintf "(tSum %s %s)" (print_typ t) (print_typ s)
  | TFor (_, k, t) -> sprintf "(tFor %s %s)" (print_kind k) (print_typ t)
  | TPi (_, k, t) -> sprintf "(tPi %s %s)" (print_kind k) (print_typ t)
  | TMu (_, t) -> sprintf "(tMu %s)" (print_typ t)
  | TBot -> "tBot"
  | TTop -> "tTop"
  | TUnit -> "tUnit"
  | TPair (t, s) -> sprintf "(tPair %s %s)" (print_typ t) (print_typ s)
  | TFst t -> sprintf "(tFst %s)" (print_typ t)
  | TSnd t -> sprintf "(tSnd %s)" (print_typ t)
  | TPack (_, t, pf, pp) -> sprintf "(tPack %s %s %s)" (print_typ t) (print_proof pf) (print_prop pp)
  | TUnpack t -> sprintf "(tUnpack %s)" (print_typ t)
and print_proof (p : dproof) =
  match p with
  | Peq (pf, pp) -> sprintf "(peq %s %s)" (print_proof pf) (print_prop pp)
  | PVar i -> sprintf "(pVar %d)" i
  | PTrue -> "pTrue"
  | PPair (p1, p2) -> sprintf "(pPair %s %s)" (print_proof p1) (print_proof p2)
  | PFst p -> sprintf "(pFst %s)" (print_proof p)
  | PSnd p -> sprintf "(pSnd %s)" (print_proof p)
  | PExi t -> sprintf "(pExi %s)" (print_typ t)
  | PLam (_, k, p) -> sprintf "(pLam %s %s)" (print_kind k) (print_proof p)
  | PApp (p, t) -> sprintf "(pApp %s %s)" (print_proof p) (print_typ t)
  | PRes t -> sprintf "(pRes %s)" (print_typ t)
  | PFix (_, pp, pf) -> sprintf "(pFix %s %s)" (print_prop pp) (print_proof pf)
  | PCoer (g, t) -> sprintf "(pCoer %s %s)" (print_coer g) (print_typ t)
and print_coer (g : dcoer) =
  match g with
  | GProp p -> sprintf "(gProp %s)" (print_proof p)
  | GRefl -> "gRefl"
  | GTrans (g1, g2) -> sprintf "(gTrans %s %s)" (print_coer g1) (print_coer g2)
  | GWeak g -> sprintf "(gWeak %s)" (print_coer g)
  | GArr (g1, t, g2) -> sprintf "(gArr %s %s %s)" (print_coer g1) (print_typ t) (print_coer g2)
  | GProd (g1, g2) -> sprintf "(gProd %s %s)" (print_coer g1) (print_coer g2)
  | GSum (g1, g2) -> sprintf "(gSum %s %s)" (print_coer g1) (print_coer g2)
  | GPi (h, _, k, g, t) -> sprintf "(gPi %s %s %s %s)" (print_cotenv h) (print_kind k) (print_coer g) (print_typ t)
  | GGen (_, k) -> sprintf "(gGen %s)" (print_cokind k)
  | GInst t -> sprintf "(gInst %s)" (print_typ t)
  | GUnfold -> "gUnfold"
  | GFold (_, t) -> sprintf "(gFold %s)" (print_typ t)
  | GTop -> "gTop"
  | GBot t -> sprintf "(gBot %s)" (print_typ t)
and print_cotenv (h : dcotenv) =
  match h with
  | HNil -> "hNil"
  | HCons (h, _, k) -> sprintf "(hCons %s %s)" (print_cotenv h) (print_cokind k)
and print_kind (k : dkind) =
  match k with
  | WKStar -> "wKStar"
  | WKOne -> "wKOne"
  | WKProd (k1, k2) -> sprintf "(wKProd %s %s)" (print_kind k1) (print_kind k2)
  | WKRes (_, k, p) -> sprintf "(wKRes %s %s)" (print_kind k) (print_prop p)
and print_prop (p : dprop) =
  match p with
  | WPTrue -> "wPTrue"
  | WPAnd (p1, p2) -> sprintf "(wPAnd %s %s)" (print_prop p1) (print_prop p2)
  | WPCoer (h, t, s) -> sprintf "(wPCoer %s %s %s)" (print_cotenv h) (print_typ t) (print_typ s)
  | WPExi k -> sprintf "(wPExi %s)" (print_kind k)
  | WPFor (_, k, p) -> sprintf "(wKFor %s %s)" (print_kind k) (print_prop p)
and print_tenv (h : dtenv) =
  match h with
  | WHNil -> "wHNil"
  | WHCons (h, _, k) -> sprintf "(wHCons %s %s)" (print_tenv h) (print_kind k)

let rec print_term (a : dterm) =
  match a with
  | EVar i -> sprintf "eVar %d" i
  | ELam (_, t, a) -> sprintf "eLam (%s) (%s)" (print_typ t) (print_term a)
  | EApp (a, b) -> sprintf "eApp (%s) (%s)" (print_term a) (print_term b)
  | EPair (a, b) -> sprintf "ePair (%s) (%s)" (print_term a) (print_term b)
  | EFst a -> sprintf "eFst (%s)" (print_term a)
  | ESnd a -> sprintf "eSnd (%s)" (print_term a)
  | EInl (a, t) -> sprintf "eInl (%s) (%s)" (print_term a) (print_typ t)
  | EInr (t, a) -> sprintf "eInr (%s) (%s)" (print_typ t) (print_term a)
  | EMatch (a, _, bl, _, br) -> sprintf "eMatch (%s) (%s) (%s)" (print_term a) (print_term bl) (print_term br)
  | EGen a -> sprintf "eGen (%s)" (print_term a)
  | EInst a -> sprintf "eInst (%s)" (print_term a)
  | ECoer (g, a) -> sprintf "eCoer (%s) (%s)" (print_coer g) (print_term a)

let rec get n x lx =
  match lx with
  | [] -> raise (NotFound x)
  | y :: lx -> if x = y then n else get (n + 1) x lx

let rec resolve_cokind la (k : ncokind) : dcokind =
  match k with
  | Kexi (p, k) -> Kexi (resolve_proof la [] [] p, resolve_kind la k)
and resolve_typ la (t : ntyp) : dtyp =
  match t with
  | Teq (t, k) -> Teq (resolve_typ la t, resolve_kind la k)
  | TVar a -> TVar (get 0 a la)
  | TArr (t, s) -> TArr (resolve_typ la t, resolve_typ la s)
  | TProd (t, s) -> TProd (resolve_typ la t, resolve_typ la s)
  | TSum (t, s) -> TSum (resolve_typ la t, resolve_typ la s)
  | TFor (a, k, t) -> TFor ((), resolve_kind la k, resolve_typ (a :: la) t)
  | TPi (a, k, t) -> TPi ((), resolve_kind la k, resolve_typ (a :: la) t)
  | TMu (a, t) -> TMu ((), resolve_typ (a :: la) t)
  | TBot -> TBot
  | TTop -> TTop
  | TUnit -> TUnit
  | TPair (t, s) -> TPair (resolve_typ la t, resolve_typ la s)
  | TFst t -> TFst (resolve_typ la t)
  | TSnd t -> TSnd (resolve_typ la t)
  | TPack (a, t, pf, pp) -> TPack ((), resolve_typ la t, resolve_proof la [] [] pf, resolve_prop (a :: la) pp)
  | TUnpack t -> TUnpack (resolve_typ la t)
and resolve_proof la lc0 lc1 (p : nproof) : dproof =
  match p with
  | Peq (pf, pp) -> Peq (resolve_proof la lc0 lc1 pf, resolve_prop la pp)
  | PVar c -> PVar (get 0 c lc0)
  | PTrue -> PTrue
  | PPair (p1, p2) -> PPair (resolve_proof la lc0 lc1 p1, resolve_proof la lc0 lc1 p2)
  | PFst p -> PFst (resolve_proof la lc0 lc1 p)
  | PSnd p -> PSnd (resolve_proof la lc0 lc1 p)
  | PExi t -> PExi (resolve_typ la t)
  | PLam (a, k, p) -> PLam ((), resolve_kind la k, resolve_proof (a :: la) lc0 lc1 p)
  | PApp (p, t) -> PApp (resolve_proof la lc0 lc1 p, resolve_typ la t)
  | PRes t -> PRes (resolve_typ la t)
  | PFix (c, pp, pf) -> PFix ((), resolve_prop la pp, resolve_proof la lc0 (c :: lc1) pf)
  | PCoer (g, t) ->
    let (la', g') = resolve_coer la lc0 lc1 g in
    PCoer (g', resolve_typ (la' @ la) t)
and resolve_coer la lc0 lc1 (g : ncoer) : string list * dcoer =
  match g with
  | GProp p ->
    let (la', h') = resolve_tenv la h in
    (la', GProp (resolve_proof la lc0 lc1 p, h'))
  | GRefl -> ([], GRefl)
  | GTrans (g2, g1) ->
    let (la2', g2') = resolve_coer la lc0 lc1 g2 in
    let (la1', g1') = resolve_coer (la2' @ la) lc0 lc1 g1 in
    (la1' @ la2', GTrans (g2', g1'))
  | GWeak g ->
    let (_, g') = resolve_coer la lc0 lc1 g in
    ([], GWeak g')
  | GArr (g1, t, g2) ->
    let (la', g2') = resolve_coer la (lc1 @ lc0) [] g2 in
    let (_, g1') = resolve_coer (la' @ la) (lc1 @ lc0) [] g1 in
    (la', GArr (g1', resolve_typ la t, g2'))
  | GProd (g1, g2) ->
    let (la2', g2') = resolve_coer la (lc1 @ lc0) [] g2 in
    let (la1', g1') = resolve_coer la (lc1 @ lc0) [] g1 in
    if la1' <> la2' then raise (Resolve (la1', la2')) else (la1', GProd (g1', g2'))
  | GSum (g1, g2) ->
    let (la2', g2') = resolve_coer la (lc1 @ lc0) [] g2 in
    let (la1', g1') = resolve_coer la (lc1 @ lc0) [] g1 in
    if la1' <> la2' then raise (Resolve (la1', la2')) else (la1', GSum (g1', g2'))
  | GPi (h, a, k, g, t) ->
    let (la', g') = resolve_coer (a :: la) (lc1 @ lc0) [] g in
    let (lah, h') = resolve_cotenv la h in
    if la' <> lah then raise (Resolve (la', lah)) else
    (la', GPi (h', (), resolve_kind la k, g', resolve_typ (la' @ a :: la) t))
  | GGen (a, k) -> ([a], GGen ((), resolve_cokind la k))
  | GInst t -> ([], GInst (resolve_typ la t))
  | GUnfold -> ([], GUnfold)
  | GFold (a, t) -> ([], GFold ((), resolve_typ (a :: la) t))
  | GTop -> ([], GTop)
  | GBot t -> ([], GBot (resolve_typ la t))
and resolve_cotenv la (h : ncotenv) : string list * dcotenv =
  match h with
  | HNil -> ([], HNil)
  | HCons (h, a, k) ->
    let (la', h') = resolve_cotenv la h in
    (a :: la', HCons (h', (), resolve_cokind (la' @ la) k))
and resolve_kind la (k : nkind) : dkind =
  match k with
  | WKStar -> WKStar
  | WKOne -> WKOne
  | WKProd (k1, k2) -> WKProd (resolve_kind la k1, resolve_kind la k2)
  | WKRes (a, k, p) -> WKRes ((), resolve_kind la k, resolve_prop (a :: la) p)
and resolve_prop la (p : nprop) : dprop =
  match p with
  | WPTrue -> WPTrue
  | WPAnd (p1, p2) -> WPAnd (resolve_prop la p1, resolve_prop la p2)
  | WPCoer (h, t, s) ->
    let (la', h') = resolve_cotenv la h in
    WPCoer (h', resolve_typ (la' @ la) t, resolve_typ la s)
  | WPExi k -> WPExi (resolve_kind la k)
  | WPFor (a, k, p) -> WPFor ((), resolve_kind la k, resolve_prop (a :: la) p)
and resolve_tenv la (h : ntenv) : string list * dtenv =
  match h with
  | WHNil -> ([], WHNil)
  | WHCons (h, a, k) ->
    let (la', h') = resolve_tenv la h in
    (a :: la', WHCons (h', (), resolve_kind (la' @ la) k))

let rec resolve_term la lx (a : nterm) : dterm =
  match a with
  | EVar x -> EVar (get 0 x lx)
  | ELam (x, t, a) -> ELam ((), resolve_typ la t, resolve_term la (x :: lx) a)
  | EApp (a, b) -> EApp (resolve_term la lx a, resolve_term la lx b)
  | EPair (a, b) -> EPair (resolve_term la lx a, resolve_term la lx b)
  | EFst a -> EFst (resolve_term la lx a)
  | ESnd a -> ESnd (resolve_term la lx a)
  | EInl (a, t) -> EInl (resolve_term la lx a, resolve_typ la t)
  | EInr (t, a) -> EInr (resolve_typ la t, resolve_term la lx a)
  | EMatch (a, xl, bl, xr, br) -> EMatch (resolve_term la lx a, (), resolve_term la (xl :: lx) bl, (), resolve_term la (xr :: lx) br)
  | EGen a -> EGen (resolve_term la lx a)
  | EInst a -> EInst (resolve_term la lx a)
  | ECoer (g, a) ->
    let (la', g') = resolve_coer la [] [] g in
    ECoer (g', resolve_term (la' @ la) lx a)
