# Handoff: live tree marker merged

- Agent: 小绿
- Role: integrator/main checkout
- Date: 2026-07-08
- Source worktree: `.claude/worktrees/xiaolv-tree-widget`

## What changed

- Added `XSyntax.TreeView`, a visible `syntax_tree "..."` proof-state marker.
- Instrumented the seven tree-building commands to append successful command events:
  - `nospec`
  - `nocomp`
  - `head`
  - `specifier`
  - `complement`
  - `adjoinL`
  - `adjoinR`
- Kept `CannotSelect` uppercase, matching the current main-line design.
- Added `XSyntax.treeView.enabled`, defaulting to `true` for interactive/player states.
- Disabled that option in authored level sample proofs, because `Statement` proofs and `Hint` extraction should not persist the display-only `treeView` marker.

## Why the option exists

The live tree marker is useful for the player-facing goal panel, but authored `Statement` proofs are also used to generate game metadata and hints. Leaving the marker in those sample proofs can disturb hidden proof placeholders in GameServer's `Statement` expansion.

Therefore:

- player/interactively typed proofs keep tree markers by default;
- level source files turn the marker off before their sample `Statement`;
- future frontend work can recognize `syntax_tree "..."` and render it as SVG/HTML.

## Validation

- `lake build XSyntax.Tactics` passed.
- Manual temporary proof confirmed visible output such as:
  `treeView : syntax_tree "nospec\ttwo\tN\t\t\tideas"`.
- Manual temporary proof confirmed uppercase `CannotSelect` still works.
- Full `lake build` passed.

## Follow-up

This is still a data hook, not the final beautiful tree renderer. The next step is a frontend renderer that detects `syntax_tree "..."` in the goal/hypothesis data and draws an aligned SVG tree in the game panel.
