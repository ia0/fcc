open Printf

type kind =
  | KStar
  | KOne
  | KProd of kind * kind
and typ =
  | TVar of int
  | TArr of typ * typ
  | TFor of kind * typ

type term =
  | Var of int
  | Lam of term
  | App of term * term

let rec print_kind k =
  match k with
  | KProd (k1, k2) -> sprintf "%s * %s" (print_kindatom k1) (print_kind k2)
  | _ -> print_kindatom k
and print_kindatom k =
  match k with
  | KStar -> sprintf "*"
  | KOne -> sprintf "1"
  | _ -> sprintf "(%s)" (print_kind k)

and print_typ t =
  match t with
  | TFor (k, t) -> sprintf "forall %s %s" (print_kindatom k) (print_typ t)
  | _ -> print_typarr t
and print_typarr t =
  match t with
  | TArr (t, s) -> sprintf "%s -> %s" (print_typatom t) (print_typarr s)
  | _ -> print_typatom t
and print_typatom t =
  match t with
  | TVar i -> sprintf "%d" i
  | _ -> sprintf "(%s)" (print_typ t)

let rec print_term a =
  match a with
    | Lam a -> sprintf "fun %s" (print_term a)
    | _ -> print_termapp a
and print_termapp a =
  match a with
    | App (a, b) -> sprintf "%s %s" (print_termapp a) (print_termatom b)
    | _ -> print_termatom a
and print_termatom a =
  match a with
    | Var i -> sprintf "%d" i
    | _ -> sprintf "(%s)" (print_term a)
