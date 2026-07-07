# Multi-Agent Workflow

This project can use multiple AI assistants or Codex windows, but one window
must remain the integrator. Parallelism is useful for exploration and
disjoint patches; it is dangerous when multiple agents edit the same Lean
files without a clear owner.

## Roles

- **Main window**: owns integration, final review, `lake build`, commit, push,
  CI/adam verification, and updates to `CLAUDE.md`.
- **Side windows**: own bounded subtasks. They may investigate, draft, or edit
  only their assigned files. They do not push directly.
- **Read-only explorers**: answer specific questions without changing files.
  These are safe to run in parallel.

## Ownership Rule

Split parallel work by file ownership, not by theme.

Themes overlap in this repo. For example, "teaching design" and "Lean
technical fix" can both touch `Game/Levels/XBar/*.lean`: the prose/hints are
teaching design, while `Statement` lines and inventory commands are technical.
If two tasks need the same file family, do them sequentially or appoint one
owner for that file family.

Good parallel slices:

- `XSyntax/Display.lean` only
- `docs/*.md` only
- `.github/workflows/build.yml` only
- read-only GameServer source investigation

Risky parallel slices:

- two agents both editing `Game/Levels/XBar/*.lean`
- one agent changing `Game/Metadata.lean` docs while another changes its
  registration keys
- one agent changing `XSyntax/Tactics.lean` while another changes goal types
  that depend on its behavior

## Worktree Rule

Git worktrees share Git history, but they do not share ignored dependency
directories. In this project, `.lake/packages` is large and the machine's
external network is unreliable.

When creating a side worktree:

1. Create it under `.claude/worktrees/` or another ignored workspace.
2. Reuse the existing `.lake` directory before running `lake build`, either by
   copying it or by creating a junction/symlink.
3. Do not delete `.lake` or force dependency re-downloads unless explicitly
   approved.

The repo ignores `.claude/worktrees/` for this purpose.

## Handoff Rule

Every side window should end with a short handoff file instead of relying on
chat history:

- Path format: `docs/HANDOFF-YYYY-MM-DD-topic.md`
- Include: AI nickname/source, task, files touched, decisions, tests run,
  risks, and next step.
- Start each handoff with a short metadata block:

  ```text
  Agent: <nickname>
  Role: main window | side window | read-only explorer
  Date: YYYY-MM-DD
  ```

- Do not paste raw chat logs unless there is a specific archival reason.

The main window then extracts only durable facts into `CLAUDE.md`: new
architecture invariants, new landmines, changed deployment facts, or updated
top-priority tasks. `CLAUDE.md` should stay compact and current, not become a
chronological log.

When a handoff summarizes work from another AI window whose nickname is
unknown, record both facts: the summarizing agent's nickname and the source as
"another AI window, nickname unknown". Do not invent nicknames retroactively.

## Integration Checklist

Before the main window commits:

1. Run `git status --short --branch`.
2. Inspect staged and unstaged diffs.
3. Confirm no side-window work is being overwritten.
4. Run the narrowest useful validation; for shared Lean behavior, prefer
   `lake build`.
5. Commit with an English conventional prefix: `fix:`, `feat:`, `docs:`,
   `chore:`, or `ci:`.
6. Push from the main window only.
7. Confirm CI/adam import. If online behavior seems stale, compare the commit
   shown in the game Info panel with `git log -1 --oneline`.

## Default Policy

- Exploration can be parallel.
- Documentation can be parallel if files are disjoint.
- Implementation can be parallel only with explicit file ownership.
- `Game/Levels/XBar/*.lean` changes are usually sequential unless one agent
  owns the entire level-file slice for that round.
