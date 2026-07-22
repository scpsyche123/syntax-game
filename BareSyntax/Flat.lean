/-
Flat (non-recursive) grammar layer — v2 baseline (spec §2).

SEMANTIC AUDIT (spec §2, §17.1): the recursive `Deriv`/`applyRule` in
`Basic.lean`/`Linear.lean` interprets a slot as a full SUB-DERIVATION
(`DerivList` holds `Deriv`s), so an `N` slot accepts ANY `N`-tree — including
another `N→D N`. That is RECURSIVE-slot semantics: `linear₁` there generates
the infinite language {D N, D D N, …}. v2 requires FLAT semantics: each slot
consumes exactly ONE lexical word, so `linear₁` is the finite template set
{[D,N], [D,A,N]}.

Design choice: **Spec §2.3 Option A** — a separate `FlatLicensed` relation,
kept distinct from the recursive `Deriv` (which stays, as W3 material). The two
never share one ambiguous `Licensed`. (Friction of A vs B in REPORT.)

Lexical-ambiguity hook (spec §8): the lexicon is `List (String × Cat)`, so a
word may appear under several categories; `FlatLicensed` matches a slot against
ANY lexical category of the word. Every general interface here quantifies over
all readings, even though the current lexicon gives each word one category.
-/
import Lean
import BareSyntax.Linear

open Lean Elab Tactic

namespace BareSyntax

/-- A flat template: an output category and one lexical category per word slot. -/
structure FlatTemplate (Cat : Type) where
  result : Cat
  slots  : List Cat

/-- A flat grammar as data: category type, a word↦category lexicon (a word may
    recur under several categories — the ambiguity hook), a finite template set. -/
structure FlatGrammar where
  Cat       : Type
  decCat    : DecidableEq Cat
  lexicon   : List (String × Cat)
  templates : List (FlatTemplate Cat)

instance (priority := low) (G : FlatGrammar) : DecidableEq G.Cat := G.decCat

/-- Words license a template iff they pair one-for-one with its slots (explicit
    length agreement) and each `(word, slot)` pair is a lexicon entry. The length
    conjunct is what `close length` contradicts; the pair conjunct (over `zip`)
    is what `close category/lexical at i` contradicts. A word may match its slot
    at ANY of its lexical categories (the §8 ambiguity hook). -/
def FlatLicensed (G : FlatGrammar) (t : FlatTemplate G.Cat) (words : List String) : Prop :=
  words.length = t.slots.length ∧ ∀ p ∈ words.zip t.slots, p ∈ G.lexicon

/-- Flat generation: some template of the right result category is licensed by
    the words. Negative goals `¬ CanYieldFlat …` are the v2 refutation target. -/
def CanYieldFlat (G : FlatGrammar) (words : List String) (C : G.Cat) : Prop :=
  ∃ t ∈ G.templates, t.result = C ∧ FlatLicensed G t words

/-- The flat W2 grammar (reuses `Linear1Cat`). Finite templates, closed lexicon. -/
def linear₁flat : FlatGrammar where
  Cat       := Linear1Cat
  decCat    := inferInstance
  lexicon   := [("a", Linear1Cat.D), ("very", Linear1Cat.Adv), ("good", Linear1Cat.A),
                ("day", Linear1Cat.N), ("house", Linear1Cat.N), ("room", Linear1Cat.N)]
  templates := [⟨Linear1Cat.N, [Linear1Cat.D, Linear1Cat.N]⟩,
                ⟨Linear1Cat.N, [Linear1Cat.D, Linear1Cat.A, Linear1Cat.N]⟩]

/-! ### Level 1 (length mismatch) — RAW proof, validates the math before the
    player tactics wrap it. `a house good room` = D N A N (length 4); both
    templates have length 2 and 3, so every route dies on length. -/
theorem level1_length_raw :
    ¬ CanYieldFlat linear₁flat ["a", "house", "good", "room"] Linear1Cat.N := by
  rintro ⟨t, ht, _, hlic⟩
  simp only [linear₁flat, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact absurd hlic.1 (by decide)
  · exact absurd hlic.1 (by decide)

/-! ### Player tactics (spec §3–§5, §15–§16)

`suppose` / `expand` / `close`. Red line: automation only VERIFIES the player's
declared mismatch; the player chooses the route and the mismatch TYPE. The
player never writes `rfl`/`simp`/`decide`; those live only in the compiled proof
term. Each `close` REFUSES a wrong declaration (the `decide` that verifies fails
→ an error), so the player cannot bluff.

The tactics locate their working hypotheses BY TYPE (macro hygiene hides names
introduced by one tactic from the next), so no fragile naming contract. -/

/-- INTERNAL. First non-internal hypothesis whose type satisfies `pred`, as an
    ident that refers back to it. -/
def findHypIdent (pred : Lean.Expr → Bool) : TacticM Ident := do
  (← getMainGoal).withContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        if pred (← instantiateMVars ldecl.type) then
          return mkIdent ldecl.userName
    throwError "close/expand: 找不到所需的假设(先 suppose?)"

/-- Assume the sentence IS generable and unpack the claim into a route + its
    licence. (Pure Lean plumbing: intro + destructure the ∃.) -/
elab "suppose" : tactic => do
  evalTactic (← `(tactic| intro hCY))
  evalTactic (← `(tactic| simp only [CanYieldFlat] at hCY))
  evalTactic (← `(tactic| obtain ⟨route, route_mem, _route_res, route_lic⟩ := hCY))

/-- List every route (template) the claim could come from — one goal each.
    (Plumbing: enumerate the finite template table.) -/
elab "expand" : tactic => do
  let h ← findHypIdent (·.isAppOf ``Membership.mem)
  -- unfold the (projected) template list to a literal, turn `∈` into a
  -- disjunction of equalities, then one goal per route.
  -- (Grammar `linear₁flat` is named here; generalising = read the grammar
  -- const off the membership hypothesis. Noted in REPORT.)
  evalTactic (← `(tactic|
    simp only [linear₁flat, List.mem_cons, List.not_mem_nil, or_false] at $h:ident))
  evalTactic (← `(tactic| rcases $h:term with rfl | rfl <;> subst_vars))

/-- `close length`: the PLAYER declares this route dies on a length mismatch;
    the system verifies the word count differs from the slot count (and refuses
    if it does not — the `decide` fails, surfacing an error). -/
elab "close " "length" : tactic => do
  let h ← findHypIdent (·.getAppFn.isConstOf ``FlatLicensed)
  evalTactic (← `(tactic| exact absurd ($h).1 (by decide)))

/-- **Level 1 — the player's move sequence** (`a house good room`, D N A N):
    `suppose` → `expand` (two routes) → `close length` on each. -/
theorem level1 :
    ¬ CanYieldFlat linear₁flat ["a", "house", "good", "room"] Linear1Cat.N := by
  suppose          -- assume it generates; unpack the route + licence  (plumbing)
  expand           -- JUDGMENT: enumerate the routes — [D,N] and [D,A,N]
  · close length   -- JUDGMENT: route [D,N] fails on length (4 words ≠ 2 slots)
  · close length   -- JUDGMENT: route [D,A,N] fails on length (4 words ≠ 3 slots)

end BareSyntax
