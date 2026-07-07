/-
Display layer for player-facing goals.

This file teaches Lean how to print syntactic positions in linguistic notation
even after the notation pretty-printer has missed them. It works at the
expression level, so it is not confused by the separate notation that prints
`Pos.C` as `C`.
-/

import Lean
import XSyntax.TypeNotation

open Lean
open PrettyPrinter.Delaborator SubExpr

namespace XSyntax

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

private def barSuffix? (e : Expr) : Option String :=
  if      e.isConstOf ``Bar.two  then some "P"
  else if e.isConstOf ``Bar.one  then some "′"
  else if e.isConstOf ``Bar.zero then some "⁰"
  else none

def xTreeDisplayName? (bar pos : Expr) : Option Name := do
  let base ← posBase? pos
  let suffix ← barSuffix? bar
  pure (Name.mkSimple (base ++ suffix))

@[delab app.XSyntax.XTree]
def delabXTree : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let some displayName := xTreeDisplayName? (e.getArg! 0) (e.getArg! 1)
    | failure
  pure (mkIdent displayName)

end XSyntax
