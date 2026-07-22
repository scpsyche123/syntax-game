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

/-! ### Route A — reusable dead-category lemma (the player-facing route)

Player action: claim "the category Adv appears at no rule position, so any word
of category Adv is unusable"; the system rechecks the rule table (decidable)
and the structural lemma discharges the goal. -/

/-- The categories at some position of some rule — the rule table read as data. -/
def usedCats (G : BareGrammar) : List G.Cat := G.rules.flatMap Rule.posCat

/-- Decidable witness of the player's claim: `Adv` occurs at no rule position. -/
example : Linear1Cat.Adv ∉ usedCats linear₁ := by decide

/- **Core structural lemma.** Any `linear₁` derivation whose category is not
   `Adv` yields a string without `very`. Mutual structural recursion with
   `noVeryL` (match on constructors — no `induction` tactic, per project rule). -/
mutual
def noVery : {s : List String} → {C : Linear1Cat} →
    Deriv linear₁ (s, C) → C ≠ Linear1Cat.Adv → "very" ∉ s
  | _, _, .lex hmem, hC => by
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h <;>
        · rw [Prod.mk.injEq] at h
          obtain ⟨rfl, hc⟩ := h
          first | decide | exact absurd hc hC
  | _, _, .app hr dl happly, _ => by
      simp only [linear₁, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        · simp only [applyRule, ruleDN, ruleDAN] at happly
          split at happly
          · rename_i hcat
            rw [Option.some.injEq, Prod.mk.injEq] at happly
            obtain ⟨hs, _⟩ := happly
            subst hs
            refine noVeryL dl (fun e he heq => ?_)
            have hm := List.mem_map_of_mem (f := Prod.snd) he
            rw [hcat, heq] at hm
            exact absurd hm (by decide)
          · exact absurd happly (by simp)
def noVeryL : {inputs : List (Expr Linear1Cat)} →
    DerivList linear₁ inputs → (∀ e ∈ inputs, (Prod.snd e) ≠ Linear1Cat.Adv) →
    "very" ∉ (List.map Prod.fst inputs).flatten
  | _, .nil, _ => by simp
  | _, .cons d rest, h => by
      simp only [List.map_cons, List.flatten_cons, List.mem_append, not_or]
      exact ⟨noVery d (h _ (by simp)), noVeryL rest (fun e he => h e (by simp [he]))⟩
end

/-- **Route A result.** `very` is a dead-category word, so the target is not
    derivable. Two conceptual player steps: assert the reason, recheck the table. -/
theorem route_A : ¬ CanYield linear₁ ["a", "very", "good", "day"] Linear1Cat.N := by
  rintro ⟨d⟩
  exact noVery d (by decide) (by decide)

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
