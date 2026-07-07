# Target Span Display Handoff - 2026-07-07

Agent: 小绿
Role: main window
Date: 2026-07-07

## Task

Improve goal display so each active subgoal shows both its syntactic position
and the remaining surface string segment it is responsible for. The previous
version showed only the category after the outer `Utters` goal was split.

## Files Touched

- `XSyntax/Tactics.lean`
- `CLAUDE.md`
- `docs/HANDOFF-2026-07-07-target-spans.md`

## Change

`Utters` is now propagated into child goals instead of immediately hiding the
target string after the first tactic. Player-facing goals now display like:

- `D⁰ ： "my"`
- `NP ： "house"`
- `C⁰ ： ""`
- `TP ： "Colorless green ideas sleep furiously"`

The seven player commands still have the same names. For non-`Utters` goals
such as old `Playground` examples, they keep the previous behavior.

## Splitting Rules

The current implementation uses deterministic XBar-world heuristics:

- `nospec` and `nocomp` pass the same target string downward.
- `complement`:
  - C selecting TP gets an empty C head.
  - T selecting VP gets an empty T head.
  - D selecting NP uses a small determiner list; otherwise D is empty.
  - other heads take the first word.
- `adjoinL` gives the adjunct the first word.
- `adjoinR` gives the adjunct the last word.
- `specifier` splits before known predicate words such as `sleep`.
- `head` now checks the local target segment directly.

These rules cover the current five XBar levels. They are not a full parser or
lexicon; future richer levels should review this splitter before adding new
sentence patterns.

## Validation

- `lake build` passed.
- Manual Lean trace showed:
  - after `complement NP` in Level 3: `D⁰ ： "my"` and `NP ： "house"`.
  - after `complement TP` in Level 5: `C⁰ ： ""` and
    `TP ： "Colorless green ideas sleep furiously"`.
- Wrong local word test rejected `head "the"` at `D⁰ ： "my"` with:
  `✗ 这个位置要念作 "my",不能种 "the"`.

## Risks

This improves player guidance but adds another place where future level design
can outgrow the current heuristics. If a new level uses multiword APs,
non-null C/T, complex subjects, or verbs outside the small predicate list,
the splitting rules need to be extended deliberately.
