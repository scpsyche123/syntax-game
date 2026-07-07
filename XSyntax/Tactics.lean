/-
The player's instruction set. Each X-bar rule becomes a tactic named after
the rule itself — the textbook's rule table and the player's key bindings
are the same table.

v3: every command now fails in linguistic vocabulary. The diagnostic
pattern is uniform: probe the goal (and the player's declaration, where
there is one) BEFORE running the real tactic; if the probe finds a
linguistic mistake, name it; otherwise run the tactic and let deeper
layers speak for themselves (selection violations surface from `license!`
untouched — layering by NOT catching).

Player vocabulary (seven commands, one per X-bar rule):
  nospec · nocomp · specifier · complement · adjoinL · adjoinR · head
`license!` is internal machinery, not player vocabulary. `tree` and
`pronounce` are gone (v3): grammaticality theorems are now stated in term
mode, with the built tree as the witness — see Playground Scene 5.

Known gap, on the books: `head` does not consult the lexicon, so a word's
category is dictated by the position it is planted in ("sleeps" happily
becomes an N⁰ at an N⁰ goal). Fix requires bringing `Lexicon` to the
construction side — a design decision, pending.
-/

import Lean
import XSyntax.TypeNotation

open Lean Elab Tactic

namespace XSyntax

/-! ### Internal machinery -/

/-- INTERNAL. Decompose a type of the form `XTree bar pos` into its two
    index expressions. `none` if the type is not a syntactic position. -/
private def asXTree? (t : Expr) : Option (Expr × Expr) :=
  let fn := t.getAppFn
  let args := t.getAppArgs
  if fn.isConstOf ``XTree && args.size == 2 then
    some (args[0]!, args[1]!)
  else
    none

/-- INTERNAL. The current goal's type, metavariables instantiated. -/
private def goalType : TacticM Expr := do
  instantiateMVars (← (← getMainGoal).getType)

/-- INTERNAL. Elaborate a declared position and insist it is a full
    phrase (XP). Used by `specifier` / `complement` / `adjoinL` / `adjoinR`. -/
private def checkDeclaredXP (stx : Term) (who : String) : TacticM Unit := do
  let d ← elabTerm stx none
  match asXTree? d with
  | some (b, _) =>
    unless b.isConstOf ``Bar.two do
      throwError "✗ {who} must be a full phrase (XP); you declared {d}"
  | none =>
    throwError "✗ {who} must be a syntactic position (an XP); you declared {d}"

/-- INTERNAL. Discharge a `Selects` goal from the licensing table, or fail
    in linguistic vocabulary, naming the two offending categories. -/
elab "license!" : tactic => do
  let t ← goalType
  let fn := t.getAppFn
  let args := t.getAppArgs
  if fn.isConstOf ``Selects && args.size == 2 then
    try
      evalTactic (← `(tactic| constructor))
    catch _ =>
      throwError "✗ selection violation: {args[0]!} does not select {args[1]!}"
  else
    throwError "license!: not a selection goal"

/-! ### Player vocabulary -/

/-- `XP → X′` (no specifier). Vacuous top projection, made explicit. -/
elab "nospec" : tactic => do
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.two then
      evalTactic (← `(tactic| apply XTree.bareX1))
    else
      throwError "✗ nospec closes off a full phrase (XP); the position here is {t}"
  | none => throwError "nospec: the goal is not a syntactic position"

/-- `X′ → X⁰` (no complement). Vacuous bar projection, made explicit. -/
elab "nocomp" : tactic => do
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      evalTactic (← `(tactic| apply XTree.bareX0))
    else
      throwError "✗ nocomp projects a head to bar level (X′); the position here is {t}"
  | none => throwError "nocomp: the goal is not a syntactic position"

/-- Plant a word (or `""` for a null head) at an `X⁰` goal. -/
elab "head" w:str : tactic => do
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.zero then
      evalTactic (← `(tactic| exact XTree.word ⟨$w⟩))
    else
      throwError "✗ a bare head cannot stand at {t} — project it first (nocomp / nospec)"
  | none => throwError "head: the goal is not a syntactic position"

/-- `XP → Spec X′`. Usage: `specifier DP` — declare the specifier. -/
elab "specifier" t:term : tactic => do
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.two then
      checkDeclaredXP t "a specifier"
      evalTactic (← `(tactic| refine XTree.Spec (?_ : $t) ?_))
    else
      throwError "✗ a specifier merges at the phrase level (XP); the position here is {g}"
  | none => throwError "specifier: the goal is not a syntactic position"

/-- `X′ → X⁰ Compl`. Usage: `complement NP` — declare the complement.
    Selection is checked here, at the moment of combination: an unlicensed
    pair makes this very command fail, in the licensing layer's own words. -/
elab "complement" t:term : tactic => do
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "a complement"
      evalTactic (← `(tactic| refine XTree.compl ?_ (?_ : $t) (by license!)))
    else
      throwError "✗ a complement merges at the bar level (X′); the position here is {g}"
  | none => throwError "complement: the goal is not a syntactic position"

/-- `X′ → Adjunct X′` (left adjunction). Usage: `adjoinL AP`. -/
elab "adjoinL" t:term : tactic => do
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "an adjunct"
      evalTactic (← `(tactic| refine XTree.adjunctL (?_ : $t) ?_))
    else
      throwError "✗ an adjunct merges at the bar level (X′); the position here is {g}"
  | none => throwError "adjoinL: the goal is not a syntactic position"

/-- `X′ → X′ Adjunct` (right adjunction). Usage: `adjoinR AdvP`. -/
elab "adjoinR" t:term : tactic => do
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "an adjunct"
      evalTactic (← `(tactic| refine XTree.adjunctR ?_ (?_ : $t)))
    else
      throwError "✗ an adjunct merges at the bar level (X′); the position here is {g}"
  | none => throwError "adjoinR: the goal is not a syntactic position"

end XSyntax
