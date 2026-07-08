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

v4 (commitment-driven segmentation): a split (`complement`/`adjoinL`/
`adjoinR`/`specifier`) NO LONGER pre-computes where the parent string breaks.
It opens the two children with UNDECIDED targets and remembers, in a parked
`SplitLink` marker, that one child's target is the parent span minus the
other child's surface string. The instant the player commits the reference
child (e.g. `head "my"` at the D⁰), `closeUtters` reduces that child's yield
to a literal, subtracts it from the parent span IN META CODE (compiled
`residual`, never the kernel), and pins the sibling's target. So the panel
shows `NP ： "house"` only as a CONSEQUENCE of the player's own choice — the
boundary is never handed to them.

v5 (immediate feedback, 小红): a wrong commit no longer waits for the final
combination proof. The instant the reference child is built, `closeUtters`
checks its yield is a prefix of the parent span and REFUSES on the spot if not;
`nocomp` refuses immediately if its X⁰ span is multiword. Since the XBar
solution is unique, every wrong word / order / structure breaks a prefix or a
structural invariant at the moment it is committed. The non-spoiler property is
kept: before the commit both children still show bare `D⁰` / `NP`.

Player vocabulary (eight commands): the seven X-bar rules
  nospec · nocomp · specifier · complement · adjoinL · adjoinR · head
plus `CannotSelect`, which PROVES a head–complement pairing is unlicensed
(goal `¬ Selects c d`). `license!` is internal machinery, not player
vocabulary. `tree` and `pronounce` are gone (v3): grammaticality theorems are
now stated in term mode, with the built tree as the witness — see Playground.

Known gap, on the books: `head` does not consult the lexicon, so a word's
category is dictated by the position it is planted in ("sleeps" happily
becomes an N⁰ at an N⁰ goal). Fix requires bringing `Lexicon` to the
construction side — a design decision, pending.
-/

import Lean
import XSyntax.Display
import XSyntax.Vocabulary

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

/-- INTERNAL, META-ONLY. The parent span `whole` with the reference child's
    surface string `prefixStr` removed from its front (with the joining space).
    Runs as compiled code inside the tactic — never as a type index, so the
    kernel never has to reduce `String.take`/`drop`. A non-prefix leaves the
    span unchanged, so a wrong commit surfaces as the phrase mispronouncing. -/
def residual (whole prefixStr : String) : String :=
  if whole == prefixStr then ""
  else
    let p := prefixStr ++ " "
    if whole.take p.length == p then whole.drop p.length
    else whole

/-- INTERNAL, META-ONLY MARKER. Parked by a split tactic. Definitionally
    `True`, so it never obstructs a proof and is discharged the moment it
    fires. Its INDICES carry the data `closeUtters` needs: the parent span
    `whole`, the reference child's surface string `ref` (an expression that
    becomes a literal once that child is built), and the sibling's target
    metavariable, which gets pinned to `residual whole ref`. -/
def SplitLink (_whole _ref _rest : String) : Prop := True

/-- INTERNAL. If the main goal is `Utters …`, split it and hide the
    yield-proof, leaving only the tree goal visible. No-op otherwise. -/
private def enterUtters : TacticM Unit := do
  let ty ← goalType
  if ty.getAppFn.isConstOf ``Utters then
    evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
    match ← getGoals with
    | treeG :: _prf :: rest => setGoals (treeG :: rest)
    | _ => pure ()

/-- INTERNAL, META-ONLY. Fully evaluate a `yield …` expression to its surface
    string, or `none` if the tree still has holes. `.all` reduction strips the
    `Subtype.val ⟨tree, ?proof⟩` projections (so parked PROOF mvars drop out);
    any metavariable that survives is a genuine unbuilt TREE part → `none`.
    Compiled `evalExpr` turns the reduced form into a clean `String` literal
    (avoiding the `String.mk [chars…]` shape a raw `.all` whnf leaves behind). -/
private def reduceYield? (e : Expr) : TacticM (Option String) := do
  let r ← withTransparency .all (whnf e)
  if r.hasExprMVar then return none
  return some (← unsafe Meta.evalExpr String (.const ``String []) r)

/-- INTERNAL. Run after every command. Two sweeps over the metavariable
    context:

    1. `SplitLink whole ref ?rest`: once `ref` (a reference child's yield)
       evaluates to a literal, subtract it from `whole` in meta code and pin
       the sibling target `?rest`. This is the commitment-driven segmentation.
    2. `yield t = s`: once the tree is fully built (every leftover mvar in it
       is a PROOF, not an unbuilt subtree), discharge the parked proof —
       assigning an open `?_` target, or refl-checking a fixed literal, or
       REFUSING in linguistics if the tree pronounces the wrong string.
       `refl` closes via the kernel's own (cheap, string-accelerated) defeq;
       we deliberately do NOT pre-reduce the whole tree here — on the big L05
       sentence that blows the heartbeat budget out from under `refl`. -/
private def closeUtters : TacticM Unit :=
  -- A generous, reset budget: the final sweep on the big L05 sentence reduces
  -- several subtrees AND refl-checks the whole tree; the default 200k window
  -- (already partly spent by earlier tactics) would starve the closing `refl`
  -- and misreport the timeout as a mispronunciation.
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 10000000 }) do
  for (mvarId, decl) in (← getMCtx).decls.toList do
    unless (← mvarId.isAssigned) do
      let dty ← instantiateMVars decl.type
      -- Sweep 1: resolve a pending segmentation.
      if dty.getAppFn.isConstOf ``SplitLink && dty.getAppNumArgs == 3 then
        let a := dty.getAppArgs
        match a[0]! with
        | .lit (.strVal whole) =>
          match ← reduceYield? a[1]! with
          | some r =>
            let restE := a[2]!
            -- IMMEDIATE FEEDBACK (小红): the reference child's surface string
            -- must be a prefix of the parent span. `residual` would silently
            -- return the span unchanged on a non-prefix, deferring the error to
            -- the final combination proof (小蓝's original behaviour). Instead
            -- refuse the moment the reference is committed — the mistake surfaces
            -- at THIS step, not deep downstream. Because the XBar solution here
            -- is unique, a wrong word / wrong constituent order breaks the prefix
            -- exactly when the player commits it.
            -- `r == ""` is a NULL head (silent C/T/D): it contributes nothing,
            -- so the sibling legitimately gets the whole span — accept it, don't
            -- mistake the empty string for a non-prefix.
            let p := r ++ " "
            if r == "" || r == whole || whole.take p.length == p then
              if restE.isMVar then
                restE.mvarId!.assign (toExpr (residual whole r))
              mvarId.assign (mkConst ``True.intro)
            else
              throwError "✗ 你在这里种下的 \"{r}\" 念不出目标 \"{whole}\" 的开头——这一步的用词或结构不对"
          | none => pure ()
        | _ => pure ()
      -- Sweep 2: discharge a parked yield proof.
      else
        let args := dty.getAppArgs
        if dty.isAppOf ``Eq && args.size == 3 && args[1]!.getAppFn.isConstOf ``yield then
          let lhs ← instantiateMVars args[1]!
          let rhs := args[2]!
          -- Tree is ready ⇔ every surviving mvar in it is a proof (`Prop`);
          -- an unbuilt subtree mvar has a `Type` (`XTree …`/`Utters …`) type.
          let ready ← (lhs.collectMVars {}).result.allM fun mv => do
            isProp (← mv.getType)
          if ready then
            -- Decide the surface string with COMPILED evaluation (fast, native
            -- string ops), then hand the kernel an `Eq.refl` to verify. We do
            -- NOT use the elaborator's `isDefEq`/`refl`: symbolically reducing
            -- the whole L05 sentence's `yield` blows up there, whereas the
            -- kernel reduces it fine (as the original per-node proofs relied on).
            match ← reduceYield? lhs with
            | none => pure ()
            | some said =>
              if rhs.isMVar then
                -- Open target (a `?_` placeholder): pin it to the tree's yield
                -- so the panel shows `D⁰ ： "my"`, then close.
                rhs.mvarId!.assign (toExpr said)
                mvarId.assign (← mkEqRefl (toExpr said))
              else
                let want := match rhs with | .lit (.strVal s) => s | _ => said
                if said == want then
                  mvarId.assign (← mkEqRefl (toExpr want))
                else
                  throwError "✗ 这棵树念作 \"{said}\",不是目标 \"{want}\""

private def hasWhitespace (s : String) : Bool :=
  s.any (fun c => c.isWhitespace)

/-! Display an `Utters` goal as e.g. `DP：my house`. Expression-level constant
    checks (`isConstOf`) — immune to the notation-rewriting pitfall that breaks
    pattern-based unexpanders. A still-undecided target (a metavariable, before
    the player's commitment resolves it) shows the bare category label. -/

/-- Display-only notation: `<phrase> ： <target>`. Never parsed from source. -/
syntax:max (name := uttersDisplay) term:max " ： " str : term

open PrettyPrinter.Delaborator SubExpr in
@[delab app.XSyntax.Utters]
def delabUtters : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some displayName := xTreeDisplayName? (e.getArg! 0) (e.getArg! 1)
    | failure
  let catStx := mkIdent displayName
  match e.getArg! 2 with
  | .lit (.strVal str) => `($catStx ： $(Syntax.mkStrLit str))
  | _                  => `($catStx)

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
  -- IMMEDIATE STRUCTURAL CHECK (小红): `nocomp` sends the whole span down to a
  -- single X⁰ head, but a head pronounces exactly one word. A multiword span
  -- here is already doomed — refuse now with a structural hint, instead of
  -- letting it fail one step later at `head`.
  if hasWhitespace u.target then
    throwError "✗ 这个中心语位置只能念一个词,但 \"{u.target}\" 是多个词——它不能直接投射到 X⁰(也许这里该用附加语或补足语?)"
  let some posStx := posTerm? u.pos | return false
  let targetStx := Syntax.mkStrLit u.target
  evalTactic (← `(tactic|
    refine
      (fun child : XSyntax.Utters .zero $posStx $targetStx =>
        ⟨XTree.bareX0 child.1, by
          simpa [XSyntax.Utters, XSyntax.yield] using child.2⟩) ?_))
  return true

/-- FOREGROUND vocabulary check (小红): refuse a word the game vocabulary does
    not license for THIS position's category. Consults `Vocabulary` via compiled
    evaluation (single source of truth — the tactic never re-lists the words).
    With commitment-driven segmentation this is where `head` earns its keep: the
    player supplies the word (not copied from a pre-shown split), so its category
    is genuinely checked here. -/
private def checkVocab (word : String) (posE : Expr) : TacticM Unit := do
  let ok ← unsafe Meta.evalExpr Bool (.const ``Bool [])
    (mkApp2 (.const ``licitWord []) (toExpr word) posE)
  unless ok do
    let report ← unsafe Meta.evalExpr String (.const ``String [])
      (mkApp (.const ``vocabReport []) (toExpr word))
    let catLabel ← unsafe Meta.evalExpr String (.const ``String [])
      (mkApp (.const ``PlotPos []) posE)
    if report == "" then
      throwError "✗ \"{word}\" 不在词汇表里——只能种词汇表登记过的词"
    else
      throwError "✗ \"{word}\" 在词汇表里是 {report},不能作 {catLabel}"

private def tryTargetHead (w : TSyntax `str) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.zero do
    throwError "✗ a bare head cannot stand at {← goalType} — project it first (nocomp / nospec)"
  let word := w.getString
  if word != u.target then
    throwError "✗ 这个位置要念作 \"{u.target}\",不能种 \"{word}\""
  checkVocab word u.pos
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

/-- INTERNAL. After a split `refine` has opened goals tagged `front`/`back`
    (and parked a `comb` proof), park a `SplitLink` recording that `back`'s
    target is the parent span `whole` minus `front`'s yield, then show only
    `front` and `back` (in that order). `others` are the pre-existing sibling
    goals, preserved. -/
private def installSplitLink (whole : String) (others : List MVarId) : TacticM Unit := do
  let after ← getGoals
  let fresh := after.filter (fun g => !(others.any (fun o => o.name == g.name)))
  let mut front? : Option MVarId := none
  let mut back? : Option MVarId := none
  for g in fresh do
    -- `?front`/`?back` come back with hygiene scopes appended (`front._@…hyg.88`),
    -- so match the root component, not the full mangled name.
    match (← g.getTag).eraseMacroScopes with
    | `front => front? := some g
    | `back  => back? := some g
    | _      => pure ()
  match front?, back? with
  | some front, some back =>
    let backTy ← instantiateMVars (← back.getType)
    let restTarget := backTy.getAppArgs[2]!
    let frontVal ← mkAppM ``Subtype.val #[mkMVar front]
    let refExpr ← mkAppM ``yield #[frontVal]
    let linkTy ← mkAppM ``SplitLink #[toExpr whole, refExpr, restTarget]
    let _ ← mkFreshExprMVar linkTy (userName := `splitLink)
    setGoals (front :: back :: others)
  | _, _ => setGoals (fresh ++ others)

private def tryTargetComplement (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ a complement merges at the bar level (X′); the position here is {← goalType}"
  let compPos ← declaredXPPos t "a complement"
  let some headPosStx := posTerm? u.pos | return false
  let some compPosStx := posTerm? compPos | return false
  let others := (← getGoals).drop 1
  evalTactic (← `(tactic|
    refine ⟨XTree.compl
              (?front : XSyntax.Utters .zero $headPosStx ?_).1
              (?back : XSyntax.Utters .two $compPosStx ?_).1
              (by license!), ?comb⟩))
  installSplitLink u.target others
  return true

private def tryTargetAdjoinL (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ an adjunct merges at the bar level (X′); the position here is {← goalType}"
  let adjPos ← declaredXPPos t "an adjunct"
  let some parentPosStx := posTerm? u.pos | return false
  let some adjPosStx := posTerm? adjPos | return false
  let others := (← getGoals).drop 1
  evalTactic (← `(tactic|
    refine ⟨XTree.adjunctL
              (?front : XSyntax.Utters .two $adjPosStx ?_).1
              (?back : XSyntax.Utters .one $parentPosStx ?_).1, ?comb⟩))
  installSplitLink u.target others
  return true

private def tryTargetAdjoinR (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.one do
    throwError "✗ an adjunct merges at the bar level (X′); the position here is {← goalType}"
  let adjPos ← declaredXPPos t "an adjunct"
  let some parentPosStx := posTerm? u.pos | return false
  let some adjPosStx := posTerm? adjPos | return false
  let others := (← getGoals).drop 1
  evalTactic (← `(tactic|
    refine ⟨XTree.adjunctR
              (?front : XSyntax.Utters .one $parentPosStx ?_).1
              (?back : XSyntax.Utters .two $adjPosStx ?_).1, ?comb⟩))
  installSplitLink u.target others
  return true

private def tryTargetSpecifier (t : Term) : TacticM Bool := do
  let some u := asUtters? (← goalType) | return false
  unless u.bar.isConstOf ``Bar.two do
    throwError "✗ a specifier merges at the phrase level (XP); the position here is {← goalType}"
  let specPos ← declaredXPPos t "a specifier"
  let some parentPosStx := posTerm? u.pos | return false
  let some specPosStx := posTerm? specPos | return false
  let others := (← getGoals).drop 1
  evalTactic (← `(tactic|
    refine ⟨XTree.Spec
              (?front : XSyntax.Utters .two $specPosStx ?_).1
              (?back : XSyntax.Utters .one $parentPosStx ?_).1, ?comb⟩))
  installSplitLink u.target others
  return true

/-! ### Player vocabulary -/

/-- `XP → X′` (no specifier). Vacuous top projection, made explicit. -/
elab "nospec" : tactic => do
  if ← tryTargetNospec then
    closeUtters
    return
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
  if ← tryTargetNocomp then
    closeUtters
    return
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
  if ← tryTargetHead w then
    closeUtters
    return
  enterUtters
  let t ← goalType
  match asXTree? t with
  | some (b, pos) =>
    if b.isConstOf ``Bar.zero then
      checkVocab word pos
      evalTactic (← `(tactic| exact XTree.word ⟨$w⟩))
    else
      throwError "✗ a bare head cannot stand at {t} — project it first (nocomp / nospec)"
  | none => throwError "head: the goal is not a syntactic position"
  closeUtters

/-- `XP → Spec X′`. Usage: `specifier DP` — declare the specifier. -/
elab "specifier" t:term : tactic => do
  if ← tryTargetSpecifier t then
    closeUtters
    return
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
  if ← tryTargetComplement t then
    closeUtters
    return
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
  if ← tryTargetAdjoinL t then
    closeUtters
    return
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
  if ← tryTargetAdjoinR t then
    closeUtters
    return
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

/-! ### Refutation (the eighth command) -/

/-- INTERNAL. The licensing table in `Tree.lean`, mirrored by hand: `Selects`
    has exactly these five constructors. Checking membership BEFORE running
    `cases` lets `CannotSelect` refuse in linguistics on an actually-licensed
    pair, rather than leaking Lean's generic "unsolved goals" (which is what a
    bare `cases` leaves behind when the pair IS licensed). -/
private def isLicensedPair (c d : Expr) : Bool :=
  (c.isConstOf ``Pos.D && d.isConstOf ``Pos.N) ||
  (c.isConstOf ``Pos.T && d.isConstOf ``Pos.V) ||
  (c.isConstOf ``Pos.C && d.isConstOf ``Pos.T) ||
  (c.isConstOf ``Pos.P && d.isConstOf ``Pos.D) ||
  (c.isConstOf ``Pos.V && d.isConstOf ``Pos.D)

/-- Prove a head–complement pairing has NO license, on a goal `¬ Selects c d`.
    Mirrors `license!`: exhaust `Selects`'s constructors — none match an
    unlicensed pair, so the case split closes the goal vacuously. If the pair
    IS licensed, refuse in the same linguistic register as every other command. -/
elab "CannotSelect" : tactic => do
  let t ← goalType
  if t.getAppFn.isConstOf ``Not && t.getAppArgs.size == 1 then
    let selectsTy := t.getAppArgs[0]!
    let fn := selectsTy.getAppFn
    let args := selectsTy.getAppArgs
    if fn.isConstOf ``Selects && args.size == 2 then
      if isLicensedPair args[0]! args[1]! then
        throwError "✗ {args[0]!} 确实选择 {args[1]!}——这个组合合法,证明不了它不存在"
      else
        evalTactic (← `(tactic| intro h; cases h))
    else
      throwError "CannotSelect: 目标不是一个「¬ Selects _ _」形式的否定许可命题"
  else
    throwError "CannotSelect: 目标不是一个否定命题"

end XSyntax
