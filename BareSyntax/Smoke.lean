/-
Forward smoke test: a toy grammar can do a positive construction proof.
Grammar: lexicon `the : D`, `ideas : N`; one rule `N → (D) N`.
Goal: `CanYield toyG ⟨the ideas⟩ N`.
-/
import BareSyntax.Basic

namespace BareSyntax

inductive ToyCat | D | N
  deriving DecidableEq

/-- `N → (D) N`: a determiner then a noun makes a noun; output string is the
    concatenation of the inputs' strings. -/
def nRule : Rule ToyCat :=
  { name := "N_rule", posCat := [.D, .N], result := .N, build := List.flatten }

def toyG : BareGrammar where
  Cat     := ToyCat
  decCat  := inferInstance
  lexicon := [(["the"], .D), (["ideas"], .N)]
  rules   := [nRule]

/-- `the ideas` is an N: apply `nRule` to the two lexicon entries. -/
theorem smoke : CanYield toyG ["the", "ideas"] .N := by
  refine ⟨.app (r := nRule) (inputs := [(["the"], ToyCat.D), (["ideas"], ToyCat.N)]) ?_ ?_ ?_⟩
  · simp [toyG]                                   -- nRule is in the table
  · exact .cons (.lex (by decide)) (.cons (.lex (by decide)) .nil)   -- both inputs are lexicon items
  · decide                                        -- applyRule yields ⟨the ideas⟩ N

end BareSyntax
