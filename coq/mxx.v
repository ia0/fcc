(** The versions of the type system:
- [P] is the paper versions,
- [F] is the full version, and
- [S] is the soundness version.

Versions [E] and [S] have the same rules, but [S] may ask less
premises. Version [P] does not have the same rules as [E] and may have
less premises for the common rules. We want [P] to have small
derivations. From [P] to [E] we push non-syntax directed rules (to the
leaves for equality and to the top for strengthening) and add the
redundant [S] premises. And from [E] to [S], we remove the unnecessary
[E] premises.

[[
      | P | F | S |
   mE |<--:-->:   |
   mS |   :<--:-->|
]]
*)
Inductive Version :=
| vP (* paper *)
| vF (* full *)
| vS (* soundness *)
.

Definition Mode := (bool * Version)%type.

(** The condition [mE v] is used for premises of [P] not used in [S].
These premises are thus available in both [P] and [E] and necessary
for extraction.
*)
Definition mE (v : Mode) :=
  match snd v with
    | vP => True
    | vF => True
    | vS => False
  end.

(** The condition [mS v] is used for redundant premises of [S] and
rules of [E] not in [P].
*)
Definition mS (v : Mode) :=
  match snd v with
    | vP => False
    | vF => True
    | vS => True
  end.

Definition mR (v : Mode) :=
  match fst v with
    | true => True
    | false => False
  end.

Hint Unfold Mode mE mS mR.
