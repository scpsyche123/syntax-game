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
import XSyntax.Display

open Lean Elab Tactic Meta

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

/-! ### Yield-checked level goals

A level's goal is `Utters b c s`: build a tree of bar `b`, category `c`, that
pronounces the target string `s`. The player still types ONLY the seven
tree-building commands — the string check rides along invisibly:

* `enterUtters`, run at the START of every command, cracks an `Utters` goal
  into `⟨tree, proof⟩` and PARKS the `yield t = s` proof off the visible goal
  list. So the panel shows one clean linguistic goal, never a bare equation.
* `closeUtters`, run at the END of every command, watches the parked proof.
  While the tree is unfinished its type still carries metavariables → nothing
  happens. The instant the tree is complete it discharges the proof if the
  yield matches, or REFUSES in linguistics if the tree pronounces something
  else. A wrong word therefore cannot pass — it is caught at the final move. -/

/-- Level goal: a tree of bar `b`, category `c`, pronouncing `s`. -/
def Utters (b : Bar) (c : Pos) (s : String) : Type := { t : XTree b c // yield t = s }

private structure UttersGoal where
  bar : Expr
  pos : Expr
  target : String

private def asUtters? (t : Expr) : Option UttersGoal :=
  let fn := t.getAppFn
  let args := t.getAppArgs
  if fn.isConstOf ``Utters && args.size == 3 then
    match args[2]! with
    | .lit (.strVal s) => some { bar := args[0]!, pos := args[1]!, target := s }
    | _ => none
  else
    none

private def barTerm? (e : Expr) : Option (TSyntax `term) :=
  if      e.isConstOf ``Bar.two  then some (mkIdent ``Bar.two)
  else if e.isConstOf ``Bar.one  then some (mkIdent ``Bar.one)
  else if e.isConstOf ``Bar.zero then some (mkIdent ``Bar.zero)
  else none

private def posTerm? (e : Expr) : Option (TSyntax `term) :=
  if      e.isConstOf ``Pos.N    then some (mkIdent ``Pos.N)
  else if e.isConstOf ``Pos.V    then some (mkIdent ``Pos.V)
  else if e.isConstOf ``Pos.A    then some (mkIdent ``Pos.A)
  else if e.isConstOf ``Pos.P    then some (mkIdent ``Pos.P)
  else if e.isConstOf ``Pos.Adv  then some (mkIdent ``Pos.Adv)
  else if e.isConstOf ``Pos.T    then some (mkIdent ``Pos.T)
  else if e.isConstOf ``Pos.D    then some (mkIdent ``Pos.D)
  else if e.isConstOf ``Pos.C    then some (mkIdent ``Pos.C)
  else if e.isConstOf ``Pos.Conj then some (mkIdent ``Pos.Conj)
  else none

private def words (s : String) : List String :=
  (s.split (·.isWhitespace)).filter (· != "")

private def joinWords : List String → String
  | [] => ""
  | w :: ws => ws.foldl (fun acc x => acc ++ " " ++ x) w

private def splitFirstWord (s : String) : String × String :=
  match words s with
  | [] => ("", "")
  | w :: ws => (w, joinWords ws)

private def splitLastWord (s : String) : String × String :=
  let ws := words s
  match ws.reverse with
  | [] => ("", "")
  | w :: rest => (joinWords rest.reverse, w)

private def isDeterminer (s : String) : Bool :=
  ["my", "the", "a", "an", "this", "that", "these", "those"].contains s

private def splitHeadComplementTarget (headPos compPos : Expr) (target : String) : String × String :=
  if headPos.isConstOf ``Pos.C && compPos.isConstOf ``Pos.T then
    ("", target)
  else if headPos.isConstOf ``Pos.T && compPos.isConstOf ``Pos.V then
    ("", target)
  else if headPos.isConstOf ``Pos.D && compPos.isConstOf ``Pos.N then
    let (first, rest) := splitFirstWord target
    if isDeterminer first then (first, rest) else ("", target)
  else
    splitFirstWord target

private def splitLeftAdjunctTarget (target : String) : String × String :=
  splitFirstWord target

private def splitRightAdjunctTarget (target : String) : String × String :=
  splitLastWord target

private def splitSpecifierTarget (target : String) : String × String :=
  let rec go (before after : List String) : String × String :=
    match after with
    | [] => splitFirstWord target
    | w :: rest =>
      if ["sleep", "sleeps", "see", "sees"].contains w then
        (joinWords before, joinWords after)
      else
        go (before ++ [w]) rest
  go [] (words target)

/-- INTERNAL. If the main goal is `Utters …`, split it and hide the
    yield-proof, leaving only the tree goal visible. No-op otherwise. -/
private def enterUtters : TacticM Unit := do
  let ty ← goalType
  if ty.getAppFn.isConstOf ``Utters then
    evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
    match ← getGoals with
    | treeG :: _prf :: rest => setGoals (treeG :: rest)
    | _ => pure ()

/-- INTERNAL. Once the tree is complete, discharge the parked `yield t = s`;
    if the tree pronounces something other than the target, refuse by name. -/
private def closeUtters : TacticM Unit := do
  for (mvarId, decl) in (← getMCtx).decls.toList do
    unless (← mvarId.isAssigned) do
      let dty ← instantiateMVars decl.type
      let args := dty.getAppArgs
      if dty.isAppOf ``Eq && args.size == 3 && args[1]!.getAppFn.isConstOf ``yield then
        unless dty.hasExprMVar do
          try
            mvarId.refl
          catch _ =>
            let said ← unsafe Meta.evalExpr String (.const ``String []) args[1]!
            throwError "✗ 这棵树念作 \"{said}\",不是目标 {args[2]!}"

private def hasWhitespace (s : String) : Bool :=
  s.any (fun c => c.isWhitespace)

/-! Display an `Utters` goal as e.g. `DP：my house`. Expression-level constant
    checks (`isConstOf`) — immune to the notation-rewriting pitfall that breaks
    pattern-based unexpanders. Any mismatch → `failure` → default printing. -/

/-- Display-only notation: `<phrase> ： <target>`. Never parsed from source. -/
syntax:max (name := uttersDisplay) term:max " ： " str : term

open PrettyPrinter.Delaborator SubExpr in
@[delab app.XSyntax.Utters]
def delabUtters : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some displayName := xTreeDisplayName? (e.getArg! 0) (e.getArg! 1)
    | failure
  let str ← match e.getArg! 2 with
    | .lit (.strVal v) => pure v
    | _ => failure
  let catStx := mkIdent displayName
  let strStx := Syntax.mkStrLit str
  `($catStx ： $strStx)

private def tryTargetNospec : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.two do
    throwError "✗ nospec closes off a full phrase (XP); the position here is {← goalType}"
  let some posStx := posTerm? u.pos | return false
  let targetStx := Syntax.mkStrLit u.target
  evalTactic (← `(tactic|
    refine
      (fun child : XSyntax.Utters .one $posStx $targetStx =>
        ⟨XTree.bareX1 child.1, by
          simpa [XSyntax.Utters, XSyntax.yield] using child.2⟩) ?_))
  return true

private def tryTargetNocomp : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ nocomp projects a head to bar level (X′); the position here is {← goalType}"
  let some posStx := posTerm? u.pos | return false
  let targetStx := Syntax.mkStrLit u.target
  evalTactic (← `(tactic|
    refine
      (fun child : XSyntax.Utters .zero $posStx $targetStx =>
        ⟨XTree.bareX0 child.1, by
          simpa [XSyntax.Utters, XSyntax.yield] using child.2⟩) ?_))
  return true

private def tryTargetHead (w : TSyntax `str) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.zero do
    throwError "✗ a bare head cannot stand at {← goalType} — project it first (nocomp / nospec)"
  let word := w.getString
  if word != u.target then
    throwError "✗ 这个位置要念作 \"{u.target}\",不能种 \"{word}\""
  evalTactic (← `(tactic| exact ⟨XTree.word ⟨$w⟩, rfl⟩))
  return true

private def declaredXPPos (stx : Term) (who : String) : TacticM Expr := do
  let d ← elabTerm stx none
  match asXTree? d with
  | some (b, pos) =>
    unless b.isConstOf ``Bar.two do
      throwError "✗ {who} must be a full phrase (XP); you declared {d}"
    return pos
  | none =>
    throwError "✗ {who} must be a syntactic position (an XP); you declared {d}"

private def tryTargetComplement (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ a complement merges at the bar level (X′); the position here is {← goalType}"
  let compPos ← declaredXPPos t "a complement"
  let some headPosStx := posTerm? u.pos | return false
  let some compPosStx := posTerm? compPos | return false
  let (headTarget, compTarget) := splitHeadComplementTarget u.pos compPos u.target
  let headTargetStx := Syntax.mkStrLit headTarget
  let compTargetStx := Syntax.mkStrLit compTarget
  evalTactic (← `(tactic|
    refine
      (fun head : XSyntax.Utters .zero $headPosStx $headTargetStx =>
       fun comp : XSyntax.Utters .two $compPosStx $compTargetStx =>
        ⟨XTree.compl head.1 comp.1 (by license!), by
          simp [XSyntax.Utters, XSyntax.yield, XSyntax.StrAdd, head.2, comp.2]⟩) ?_ ?_))
  return true

private def tryTargetAdjoinL (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ an adjunct merges at the bar level (X′); the position here is {← goalType}"
  let adjPos ← declaredXPPos t "an adjunct"
  let some parentPosStx := posTerm? u.pos | return false
  let some adjPosStx := posTerm? adjPos | return false
  let (adjTarget, restTarget) := splitLeftAdjunctTarget u.target
  let adjTargetStx := Syntax.mkStrLit adjTarget
  let restTargetStx := Syntax.mkStrLit restTarget
  evalTactic (← `(tactic|
    refine
      (fun adj : XSyntax.Utters .two $adjPosStx $adjTargetStx =>
       fun rest : XSyntax.Utters .one $parentPosStx $restTargetStx =>
        ⟨XTree.adjunctL adj.1 rest.1, by
          simp [XSyntax.Utters, XSyntax.yield, XSyntax.StrAdd, adj.2, rest.2]⟩) ?_ ?_))
  return true

private def tryTargetAdjoinR (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ an adjunct merges at the bar level (X′); the position here is {← goalType}"
  let adjPos ← declaredXPPos t "an adjunct"
  let some parentPosStx := posTerm? u.pos | return false
  let some adjPosStx := posTerm? adjPos | return false
  let (restTarget, adjTarget) := splitRightAdjunctTarget u.target
  let restTargetStx := Syntax.mkStrLit restTarget
  let adjTargetStx := Syntax.mkStrLit adjTarget
  evalTactic (← `(tactic|
    refine
      (fun rest : XSyntax.Utters .one $parentPosStx $restTargetStx =>
       fun adj : XSyntax.Utters .two $adjPosStx $adjTargetStx =>
        ⟨XTree.adjunctR rest.1 adj.1, by
          simp [XSyntax.Utters, XSyntax.yield, XSyntax.StrAdd, rest.2, adj.2]⟩) ?_ ?_))
  return true

private def tryTargetSpecifier (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.two do
    throwError "✗ a specifier merges at the phrase level (XP); the position here is {← goalType}"
  let specPos ← declaredXPPos t "a specifier"
  let some parentPosStx := posTerm? u.pos | return false
  let some specPosStx := posTerm? specPos | return false
  let (specTarget, restTarget) := splitSpecifierTarget u.target
  let specTargetStx := Syntax.mkStrLit specTarget
  let restTargetStx := Syntax.mkStrLit restTarget
  evalTactic (← `(tactic|
    refine
      (fun spec : XSyntax.Utters .two $specPosStx $specTargetStx =>
       fun rest : XSyntax.Utters .one $parentPosStx $restTargetStx =>
        ⟨XTree.Spec spec.1 rest.1, by
          simp [XSyntax.Utters, XSyntax.yield, XSyntax.StrAdd, spec.2, rest.2]⟩) ?_ ?_))
  return true

/-! ### Player vocabulary -/

/-- `XP → X′` (no specifier). Vacuous top projection, made explicit. -/
elab "nospec" : tactic => do
  if ← tryTargetNospec then return
  enterUtters
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.two then
      evalTactic (← `(tactic| apply XTree.bareX1))
    else
      throwError "✗ nospec closes off a full phrase (XP); the position here is {t}"
  | none => throwError "nospec: the goal is not a syntactic position"
  closeUtters

/-- `X′ → X⁰` (no complement). Vacuous bar projection, made explicit. -/
elab "nocomp" : tactic => do
  if ← tryTargetNocomp then return
  enterUtters
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      evalTactic (← `(tactic| apply XTree.bareX0))
    else
      throwError "✗ nocomp projects a head to bar level (X′); the position here is {t}"
  | none => throwError "nocomp: the goal is not a syntactic position"
  closeUtters

/-- Plant a word (or `""` for a null head) at an `X⁰` goal. -/
elab "head" w:str : tactic => do
  let word := w.getString
  if word != "" && hasWhitespace word then
    throwError "✗ head 一次只能种一个词；多个词必须各自占一个 head，空头才写 `head \"\"`"
  if ← tryTargetHead w then return
  enterUtters
  let t ← goalType
  match asXTree? t with
  | some (b, _) =>
    if b.isConstOf ``Bar.zero then
      evalTactic (← `(tactic| exact XTree.word ⟨$w⟩))
    else
      throwError "✗ a bare head cannot stand at {t} — project it first (nocomp / nospec)"
  | none => throwError "head: the goal is not a syntactic position"
  closeUtters

/-- `XP → Spec X′`. Usage: `specifier DP` — declare the specifier. -/
elab "specifier" t:term : tactic => do
  if ← tryTargetSpecifier t then return
  enterUtters
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.two then
      checkDeclaredXP t "a specifier"
      evalTactic (← `(tactic| refine XTree.Spec (?_ : $t) ?_))
    else
      throwError "✗ a specifier merges at the phrase level (XP); the position here is {g}"
  | none => throwError "specifier: the goal is not a syntactic position"
  closeUtters

/-- `X′ → X⁰ Compl`. Usage: `complement NP` — declare the complement.
    Selection is checked here, at the moment of combination: an unlicensed
    pair makes this very command fail, in the licensing layer's own words. -/
elab "complement" t:term : tactic => do
  if ← tryTargetComplement t then return
  enterUtters
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "a complement"
      evalTactic (← `(tactic| refine XTree.compl ?_ (?_ : $t) (by license!)))
    else
      throwError "✗ a complement merges at the bar level (X′); the position here is {g}"
  | none => throwError "complement: the goal is not a syntactic position"
  closeUtters

/-- `X′ → Adjunct X′` (left adjunction). Usage: `adjoinL AP`. -/
elab "adjoinL" t:term : tactic => do
  if ← tryTargetAdjoinL t then return
  enterUtters
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "an adjunct"
      evalTactic (← `(tactic| refine XTree.adjunctL (?_ : $t) ?_))
    else
      throwError "✗ an adjunct merges at the bar level (X′); the position here is {g}"
  | none => throwError "adjoinL: the goal is not a syntactic position"
  closeUtters

/-- `X′ → X′ Adjunct` (right adjunction). Usage: `adjoinR AdvP`. -/
elab "adjoinR" t:term : tactic => do
  if ← tryTargetAdjoinR t then return
  enterUtters
  let g ← goalType
  match asXTree? g with
  | some (b, _) =>
    if b.isConstOf ``Bar.one then
      checkDeclaredXP t "an adjunct"
      evalTactic (← `(tactic| refine XTree.adjunctR ?_ (?_ : $t)))
    else
      throwError "✗ an adjunct merges at the bar level (X′); the position here is {g}"
  | none => throwError "adjoinR: the goal is not a syntactic position"
  closeUtters

end XSyntax
