/-
Display layer for player-facing goals.

This file teaches Lean how to print syntactic positions in linguistic notation
even after the notation pretty-printer has missed them. It works at the
expression level, so it is not confused by the separate notation that prints
`Pos.C` as `C`.

Three exports:
* `goalColon` — the display-only `<label> ： <string>` notation shared by the
  level-goal delaborator (`Parses`, in `Tactics.lean`) and the lexicon
  delaborator below.
* `xTreeLabel?` — maps `(bar, pos)` to the ACTUAL phrase-type notation token
  (`` `(DP) ``, `` `(N′) ``…). Emitting the notation, not `mkIdent "DP"`, is what
  keeps the panel showing a clean `DP` instead of the escaped `«DP»` (`DP` is a
  reserved notation token, so an identifier by that name prints with guillemets).
* `delabXTree` / `delabLexicon` — the delaborators that use them.
-/

import Lean
import XSyntax.TypeNotation

open Lean
open PrettyPrinter.Delaborator SubExpr

namespace XSyntax

/-- Display-only: `<label> ： <string>`, e.g. `DP ： "my house"` or `N ： "cat"`.
    Never parsed from source (`:max`, fullwidth colon). Shared so both the goal
    delaborator and the lexicon delaborator render through one notation. -/
syntax:max (name := goalColon) term:max " ： " str : term

private def posBase? (e : Expr) : Option String :=
  if      e.isConstOf ``Pos.N    then some "N"
  else if e.isConstOf ``Pos.V    then some "V"
  else if e.isConstOf ``Pos.A    then some "A"
  else if e.isConstOf ``Pos.P    then some "P"
  else if e.isConstOf ``Pos.Adv  then some "Adv"
  else if e.isConstOf ``Pos.T    then some "T"
  else if e.isConstOf ``Pos.D    then some "D"
  else if e.isConstOf ``Pos.C    then some "C"
  else if e.isConstOf ``Pos.Conj then some "Conj"
  else none

/-- The phrase-type label for `(bar, pos)` AS THE NOTATION TOKEN itself
    (`` `(DP) ``, `` `(N′) ``, `` `(C⁰) ``…). Because these are the very tokens
    `TypeNotation` registers, they pretty-print as `DP`/`N′`/`C⁰` — no `«…»`
    escaping. Any `MonadQuotation` (every delaborator is one) can call it. -/
def xTreeLabel? [Monad m] [MonadQuotation m] (bar pos : Expr) : m (Option Term) := do
  if bar.isConstOf ``Bar.two then
    if      pos.isConstOf ``Pos.N    then return some (← `(NP))
    else if pos.isConstOf ``Pos.V    then return some (← `(VP))
    else if pos.isConstOf ``Pos.A    then return some (← `(AP))
    else if pos.isConstOf ``Pos.P    then return some (← `(PP))
    else if pos.isConstOf ``Pos.Adv  then return some (← `(AdvP))
    else if pos.isConstOf ``Pos.T    then return some (← `(TP))
    else if pos.isConstOf ``Pos.D    then return some (← `(DP))
    else if pos.isConstOf ``Pos.C    then return some (← `(CP))
    else if pos.isConstOf ``Pos.Conj then return some (← `(ConjP))
    else return none
  else if bar.isConstOf ``Bar.one then
    if      pos.isConstOf ``Pos.N    then return some (← `(N′))
    else if pos.isConstOf ``Pos.V    then return some (← `(V′))
    else if pos.isConstOf ``Pos.A    then return some (← `(A′))
    else if pos.isConstOf ``Pos.P    then return some (← `(P′))
    else if pos.isConstOf ``Pos.Adv  then return some (← `(Adv′))
    else if pos.isConstOf ``Pos.T    then return some (← `(T′))
    else if pos.isConstOf ``Pos.D    then return some (← `(D′))
    else if pos.isConstOf ``Pos.C    then return some (← `(C′))
    else if pos.isConstOf ``Pos.Conj then return some (← `(Conj′))
    else return none
  else if bar.isConstOf ``Bar.zero then
    if      pos.isConstOf ``Pos.N    then return some (← `(N⁰))
    else if pos.isConstOf ``Pos.V    then return some (← `(V⁰))
    else if pos.isConstOf ``Pos.A    then return some (← `(A⁰))
    else if pos.isConstOf ``Pos.P    then return some (← `(P⁰))
    else if pos.isConstOf ``Pos.Adv  then return some (← `(Adv⁰))
    else if pos.isConstOf ``Pos.T    then return some (← `(T⁰))
    else if pos.isConstOf ``Pos.D    then return some (← `(D⁰))
    else if pos.isConstOf ``Pos.C    then return some (← `(C⁰))
    else if pos.isConstOf ``Pos.Conj then return some (← `(Conj⁰))
    else return none
  else return none

/-- Print a bare position `XTree bar pos` as its phrase-type label. -/
@[delab app.XSyntax.XTree]
def delabXTree : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let some stx ← xTreeLabel? (e.getArg! 0) (e.getArg! 1) | failure
  pure stx

/-- Print a lexicon hypothesis `Lexicon .N "cat"` as `N ： "cat"` (`C ： "∅"`
    for a null head), so the given vocabulary reads linguistically in the
    assumptions panel. The category is delaborated from the argument (so the
    bare-category notation renders it `N`, not `Pos.N`). -/
@[delab app.XSyntax.Lexicon]
def delabLexicon : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let some _ := posBase? (e.getArg! 0) | failure
  let catStx ← withNaryArg 0 delab
  match e.getArg! 1 with
  | .lit (.strVal s) =>
    let shown := if s == "" then "∅" else s
    `($catStx ： $(Syntax.mkStrLit shown))
  | _ => failure

end XSyntax
