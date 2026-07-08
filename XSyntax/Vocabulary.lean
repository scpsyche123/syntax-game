/-
FOREGROUND game vocabulary — NOT part of the theory core.

The theory (`Basic`/`Tree`/`Operations`) stays lexicon-agnostic: `LexicalEntry c`
is inhabited by any string, and `XTree.word` takes any `LexicalEntry c`. Which
WORD may realise which CATEGORY is a contingent fact about a particular
language — foreground game content, revisable without touching the theory (and
the schema will grow: POS today, features later). So the check is enforced at
the FOREGROUND (the `head` tactic consults this table), not baked into the
type of `LexicalEntry` the way `Selects` is baked into `XTree.compl`.

Layering (per maintainer): the tactics + this vocabulary are GAME content, one
layer above the theory core; `Tactics.lean` imports this. No env extension and
no `Game/`-folder placement is needed — the vocabulary just sits below `head`
in the import graph. A future "per-level vocabulary" / "vocabulary panel" would
promote this to a registration command whose data lives in level files.

Null heads: only the FUNCTIONAL categories C/T/D may be silent (`head ""`).
No null N/V/A — a deliberate, stated theoretical commitment.
-/

import XSyntax.Basic

namespace XSyntax

/-- The registered game vocabulary: which word may realise which category.
    Multi-category words simply appear more than once (enables ambiguity). -/
def vocabulary : List (String × Pos) :=
  [ -- determiners (D)
    ("the", .D), ("my", .D), ("hers", .D),
    -- nouns (N)
    ("ideas", .N), ("cat", .N), ("house", .N), ("dog", .N), ("cats", .N),
    -- verbs (V)
    ("sees", .V), ("sleep", .V),
    -- adjectives (A)
    ("big", .A), ("strange", .A), ("green", .A), ("Colorless", .A),
    -- adverbs (Adv)
    ("quickly", .Adv), ("furiously", .Adv),
    -- tense (T)
    ("will", .T),
    -- null heads: only functional C/T/D may be silent
    ("", .C), ("", .T), ("", .D) ]

/-- The categories a word may realise (empty = not in the vocabulary). -/
def wordCats (w : String) : List Pos :=
  (vocabulary.filter (fun e => e.1 == w)).map (fun e => e.2)

/-- Is `w` licensed to realise category `c`? -/
def licitWord (w : String) (c : Pos) : Bool :=
  (wordCats w).any (fun p => decide (p = c))

/-- Human report of a word's registered categories, `""` if unregistered.
    Used only to build the tactic's linguistic error message. -/
def vocabReport (w : String) : String :=
  match wordCats w with
  | [] => ""
  | cs => String.intercalate "/" (cs.map PlotPos)

end XSyntax
