Agent: 小蓝
Role: side window (worktree .claude/worktrees/xiaolan, branch agent/xiaolan)
Date: 2026-07-07

## Task

Fix the spoiler introduced by 小绿's target-span display: on a split (e.g.
`complement NP`), the goal panel pre-computed and showed WHICH words are the
head vs. the complement (`D⁰ ： "my"`, `NP ： "house"`). That hands the player
the segmentation they are supposed to work out themselves. Maintainer approved
a commitment-driven redesign: children open with UNDECIDED targets; the split
is computed only as a CONSEQUENCE of what the player commits.

## Files Touched

- `XSyntax/Tactics.lean` (rewrite of the split machinery + `closeUtters`)

## What Changed (mechanism)

The four split tactics (`complement` / `adjoinL` / `adjoinR` / `specifier`) no
longer call a heuristic string-splitter. Instead:

1. They open the two children with FRESH, undecided target metavariables and
   park a combination proof `yield (constructor …) = whole`.
2. They park a `SplitLink whole (yield frontChild) ?restTarget` marker — a
   meta-only `Prop` (definitionally `True`) whose indices carry the parent
   span, the reference child's yield, and the sibling's target mvar.
3. `closeUtters` (runs after every command) sweeps the marker: once the
   reference child is built, it evaluates that child's yield with COMPILED
   code (`reduceYield?` = `.all` whnf + `evalExpr`), subtracts it from the
   parent span with the compiled `residual` function, and pins the sibling's
   target to the resulting literal.

Key design point (this is the crux the maintainer asked about): the string
subtraction happens entirely in META CODE and the result is assigned to a
plain metavariable — it is NEVER a type index, so the kernel never has to
reduce `String.take`/`drop`. That is what makes "type `head "my"` → the NP
auto-resolves to `"house"`" possible without hitting the kernel's opaque-
string-literal wall.

Deleted the whole heuristic splitter (`isDeterminer`, the determiner list, the
predicate list `sleep/sees`, `splitFirstWord/splitLastWord/…`) — this pays off
the "Utters 子目标字符串分配是启发式" debt bullet in CLAUDE.md.

## Behaviour (verified by scratch tests, before deletion)

- Correct play: all five levels build (the intended solutions still go
  through). `lake build` green, 54 jobs, no `No world …` gate warnings.
- Before committing the head: BOTH children show bare `D⁰` / `NP` — no
  boundary is revealed.
- After `head "my"`: the sibling resolves to `NP ： "house"` on the panel.
- Wrong determiner (`head "the"`): accepted as the player's choice, and the
  mistake surfaces downstream as the phrase mispronouncing
  (`✗ 这个位置要念作 "my house",不能种 "house"`) rather than an immediate
  "should be my" spoiler.

## Landmines hit while implementing (durable, for future work)

- `?_` in a LATER binder's type captures the earlier binder → the sibling
  target became `?m applied to head`, not a bare mvar. Fixed by dropping the
  `fun a => fun b => …` nesting and writing the refine as one flat
  `⟨constructor (?front : Utters …).1 (?back : Utters …).1 …, ?comb⟩`.
- `?front`/`?back` goal tags come back with hygiene scopes
  (`front._@…hyg.88`); match with `(← g.getTag).eraseMacroScopes`.
- `Subtype.val ⟨tree, ?proof⟩` textually carries the parked proof mvar, so
  `hasExprMVar` on a `yield …` expression is `true` even when the tree is
  complete. Judge tree-completeness by CLASSIFYING leftover mvars (a proof mvar
  has a `Prop` type; an unbuilt subtree mvar has a `Type` type), not by
  reducing.
- Do NOT close the yield proof with the elaborator's `refl`/`isDefEq`:
  symbolically reducing the whole L05 sentence's `yield` blows up there. Decide
  the string with compiled `reduceYield?`, then `mvarId.assign (← mkEqRefl …)`
  and let the KERNEL verify (it reduces native string ops fine — this is what
  the original per-node `simp` proofs implicitly relied on).

## For the main window (小红) to fold into CLAUDE.md if it agrees

- Invariant update: the `Utters` child-target assignment is no longer a
  per-level heuristic; it is commitment-driven residual subtraction done in
  `closeUtters` (meta code), plus a global combination-proof check.
- The "Utters 子目标字符串分配是启发式" debt bullet can be marked resolved.

## NOT done / caveats

- Static build is green, but per CLAUDE.md landmine 8 this MUST be playtested
  on the live server (goal-panel loading, per-move error rendering) before it
  is trusted — Windows can't run the frontend locally.
- Not pushed (side window). Branch `agent/xiaolan`, commit on top of `main`.
- `.i18n/en/Game.pot` regenerates on build; not committed (translations
  deferred per maintainer).
