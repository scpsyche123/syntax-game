/-
CannotYield vertical slice.

Grammar `linear₁`: lexicon a:D, very:Adv, good:A, day:N; rule table
`N → (D) (A)* N`, the star expanded (closed lexicon ⇒ faithful) to two
variants: `N → D N` and `N → D A N`.

Target: `¬ CanYield linear₁ ⟨a very good day⟩ N`.

Mathematical root of impossibility: `very`'s category `Adv` occurs at NO
position of ANY rule, so `very` can never be an input to a rule — it can only
stand alone as its own lexicon leaf. The target string contains `very` but is
not that lone leaf, so no derivation exists.

Three proof routes, in order: A (reusable dead-category lemma + decidable table
check — the player-facing route), B (bare cases inversion, verbose baseline),
C (decidability feasibility note).
-/
import BareSyntax.Basic

namespace BareSyntax

inductive Linear1Cat | D | Adv | A | N
  deriving DecidableEq

def ruleDN  : Rule Linear1Cat :=
  { name := "N→D N",   posCat := [.D, .N],     result := .N, build := List.flatten }
def ruleDAN : Rule Linear1Cat :=
  { name := "N→D A N", posCat := [.D, .A, .N], result := .N, build := List.flatten }

def linear₁ : BareGrammar where
  Cat     := Linear1Cat
  decCat  := inferInstance
  lexicon := [(["a"], .D), (["very"], .Adv), (["good"], .A), (["day"], .N)]
  rules   := [ruleDN, ruleDAN]

/-! ### Route A — the player LIVES THROUGH the dead-category argument

Redesign (maintainer ruling): a single `dead_category Adv` tactic that
recognises the category, scans the whole table, and concludes is a **god key**
— it does the linguistic judgment FOR the player. Forbidden. A custom tactic
may only absorb Lean plumbing + humanise errors; every syntactic judgment stays
a player move.

So the "dead category" fact is NOT proved inside the plumbing and NOT scanned by
one `decide`. It is a HYPOTHESIS the player builds **rule by rule**. The author
proves only the pure structural plumbing (`deadYield`): "if a category is
accepted at no rule position, a word whose only lexicon category is that one
cannot appear in any derivation". Given that plumbing, the player's proof is a
sequence of genuine judgments (annotated in `route_A` and REPORT §2). -/

/-- The categories at some position of some rule — the rule table as data. Used
    for display/tooling, NOT as a whole-table `decide` in the player proof (that
    would be the banned god-key). -/
def usedCats (G : BareGrammar) : List G.Cat := G.rules.flatMap Rule.posCat

/- **PLUMBING (author-proved, pure Lean — no linguistic judgment).** For ANY
   grammar and dead category `c`: if `c` is accepted at no rule position
   (`hdead`, supplied by the player) and `w`'s only lexicon category is `c`
   (`hw`), then no derivation whose category is not `c` yields `w`. The
   `hdead`/`hw` hypotheses are exactly where the player's judgments plug in.
   Mutual structural recursion (match, no `induction` tactic). -/
mutual
def deadYield {G : BareGrammar} {c : G.Cat} {w : String}
    (hdead : ∀ r ∈ G.rules, c ∉ r.posCat)
    (hw : ∀ e ∈ G.lexicon, w ∈ e.1 → e.2 = c)
    (hbuild : ∀ r ∈ G.rules, r.build = List.flatten) :
    {s : List String} → {C : G.Cat} → Deriv G (s, C) → C ≠ c → w ∉ s
  | _, _, .lex hmem, hC => fun hws => hC (hw _ hmem hws)
  | _, _, .app hr dl happly, _ => by
      intro hws
      simp only [applyRule] at happly
      split at happly
      · rename_i hcat
        rw [Option.some.injEq, Prod.mk.injEq] at happly
        obtain ⟨hs, _⟩ := happly
        rw [hbuild _ hr] at hs
        subst hs
        refine deadYieldL hdead hw hbuild dl (fun e he heq => ?_) hws
        have hm := List.mem_map_of_mem (f := Prod.snd) he
        rw [hcat] at hm
        exact hdead _ hr (heq ▸ hm)
      · exact absurd happly (by simp)
def deadYieldL {G : BareGrammar} {c : G.Cat} {w : String}
    (hdead : ∀ r ∈ G.rules, c ∉ r.posCat)
    (hw : ∀ e ∈ G.lexicon, w ∈ e.1 → e.2 = c)
    (hbuild : ∀ r ∈ G.rules, r.build = List.flatten) :
    {inputs : List (Expr G.Cat)} → DerivList G inputs →
    (∀ e ∈ inputs, (Prod.snd e) ≠ c) → w ∉ (List.map Prod.fst inputs).flatten
  | _, .nil, _ => by simp
  | _, .cons d rest, h => by
      simp only [List.map_cons, List.flatten_cons, List.mem_append, not_or]
      exact ⟨deadYield hdead hw hbuild d (h _ (by simp)),
             deadYieldL hdead hw hbuild rest (fun e he => h e (by simp [he]))⟩
end

/-- PLUMBING: every `linear₁` rule concatenates its inputs' strings. (Author
    fact about the rule table, not a per-derivation judgment.) -/
theorem linear₁_concat : ∀ r ∈ linear₁.rules, r.build = List.flatten := by
  intro r hr
  simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rfl

/-- Specialisation used by Route B's baseline (author convenience — hides the
    per-rule check, which is fine there since Route B is the anti-example). -/
theorem noVery {s C} (d : Deriv linear₁ (s, C)) (hC : C ≠ Linear1Cat.Adv) : "very" ∉ s :=
  deadYield
    (fun r hr => by
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide)
    (by decide) linear₁_concat d hC

/-- **Route A result — the player's judgment sequence.** Each `?case` is a
    genuine syntactic judgment the player makes; `deadYield` is the only thing
    hidden, and it is pure Lean plumbing (no judgment). See REPORT §2 for the
    step-by-step annotation of judgment vs. hidden-plumbing. -/
theorem route_A : ¬ CanYield linear₁ ["a", "very", "good", "day"] Linear1Cat.N := by
  rintro ⟨d⟩
  refine deadYield (c := Linear1Cat.Adv) (w := "very")
    ?dead ?veryCat linear₁_concat d ?tgtCat ?inTarget
  -- JUDGMENT: check the rule table ONE RULE AT A TIME (never a whole-table scan)
  case dead =>
    intro r hr
    simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl        -- "the table has two rules; I inspect each"
    · decide                        -- rule N→D N: positions are D, N — no Adv
    · decide                        -- rule N→D A N: positions are D, A, N — no Adv
  -- JUDGMENT: what category can "very" be? only Adv (from the lexicon)
  case veryCat =>
    intro e he hwe
    simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp_all
  -- plumbing: the goal category N is not Adv (trivial, hidden)
  case tgtCat => exact fun h => Linear1Cat.noConfusion h
  -- JUDGMENT: locate "very" in the target string
  case inTarget => decide

/-! ### Route B — bare cases inversion (verbose baseline)

No reusable category lemma; invert `Deriv` and close each branch by pinning
leaves and hitting a word mismatch. Helper `derivDA`: a D/A derivation is its
lexicon leaf (no rule produces D or A). -/

/-- A derivation at `D` or `A` is forced to be its lexicon leaf. -/
theorem derivDA {s C} (d : Deriv linear₁ (s, C)) :
    (C = Linear1Cat.D → s = ["a"]) ∧ (C = Linear1Cat.A → s = ["good"]) := by
  cases d with
  | lex h =>
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;>
        · rw [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩ <;> intro hh <;> first | rfl | contradiction
  | app hr dl happly =>
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        · simp only [applyRule, ruleDN, ruleDAN] at happly
          split at happly
          · rw [Option.some.injEq, Prod.mk.injEq] at happly
            obtain ⟨_, hres⟩ := happly
            refine ⟨fun hh => ?_, fun hh => ?_⟩ <;> (rw [hh] at hres; contradiction)
          · exact absurd happly (by simp)

/-- **Route B result.** By raw inversion. The `N→D A N` rule branch is unrolled
    fully and independently (an immediate word mismatch, no recursion). The
    `N→D N` branch pins its D leaf and hands the object-N sub-derivation to the
    Route-A lemma to stay bounded — a fully-independent inversion recurses one
    more level here (see REPORT step count). -/
theorem route_B : ¬ CanYield linear₁ ["a", "very", "good", "day"] Linear1Cat.N := by
  rintro ⟨d⟩
  cases d with
  | lex h => simp [linear₁] at h
  | app hr dl happly =>
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · -- N→D N : pin the D leaf, then the object N holds `very` (dead) → ⊥.
        cases dl with
        | nil => simp [applyRule, ruleDN] at happly
        | cons d1 dl1 => cases dl1 with
          | nil => simp [applyRule, ruleDN] at happly
          | cons d2 dl2 => cases dl2 with
            | cons _ _ => simp [applyRule, ruleDN] at happly
            | nil =>
                simp only [applyRule, ruleDN] at happly
                split at happly
                · rename_i hcat
                  rw [Option.some.injEq, Prod.mk.injEq] at happly
                  obtain ⟨hstr, _⟩ := happly
                  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcat
                  obtain ⟨hc1, hc2⟩ := hcat
                  have h1 := (derivDA d1).1 hc1
                  simp only [h1, List.map_cons, List.map_nil, List.flatten_cons,
                    List.flatten_nil, List.append_nil, List.cons_append, List.nil_append,
                    List.cons.injEq, true_and] at hstr
                  have hv := noVery d2 (by rw [hc2]; exact fun h => Linear1Cat.noConfusion h)
                  rw [hstr] at hv
                  exact hv (by decide)
                · exact absurd happly (by simp)
      · -- N→D A N : pin the D and A leaves → immediate `good ≠ very` mismatch.
        cases dl with
        | nil => simp [applyRule, ruleDAN] at happly
        | cons d1 dl1 => cases dl1 with
          | nil => simp [applyRule, ruleDAN] at happly
          | cons d2 dl2 => cases dl2 with
            | nil => simp [applyRule, ruleDAN] at happly
            | cons d3 dl3 => cases dl3 with
              | cons _ _ => simp [applyRule, ruleDAN] at happly
              | nil =>
                  simp only [applyRule, ruleDAN] at happly
                  split at happly
                  · rename_i hcat
                    rw [Option.some.injEq, Prod.mk.injEq] at happly
                    obtain ⟨hstr, _⟩ := happly
                    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcat
                    obtain ⟨hc1, hc2, _⟩ := hcat
                    have h1 := (derivDA d1).1 hc1
                    have h2 := (derivDA d2).2 hc2
                    simp [h1, h2] at hstr
                  · exact absurd happly (by simp)

/-! ### Route C — decidability feasibility

In v1 the empty-context `Lexicon` made membership decidable and a whole goal
`decide`-able; here `Deriv` is a genuine inductive family over data, and
`Decidable (CanYield G s C)` needs a terminating ENUMERATOR of derivations.
That enumerator needs the "rules strictly grow string length ⇒ finitely many
derivations" theorem — explicitly out of scope this round (see brief). So
Route C is NOT a one-line `decide`: the blocker is exactly that missing
generation-decidability theorem, and a `Decidable` instance without it would be
circular. Verdict: deferred to the generation-decidability milestone; the
finiteness scaffolding (`List` / `DecidableEq` everywhere) is already in place,
so nothing here blocks it. -/

end BareSyntax
