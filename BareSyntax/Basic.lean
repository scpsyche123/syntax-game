/-
Bare Grammar — minimal base (rebase slice, branch `bg-base-slice`).

The whole grammar is DATA: a category type, a finite lexicon, and a finite
rule table. No theory lives in the constructors (contrast v1's `XTree`, where
X-bar was baked into an inductive). Generation is a separate inductive
`Deriv`; grammaticality is `CanYield := Nonempty (Deriv …)`.

Design notes (frictions logged for the rule-representation final review — see
REPORT.md):
* A rule keeps its DOMAIN as explicit, checkable data (`posCat : List Cat`,
  one required category per position) — NOT hidden inside an opaque apply
  function. The apply function is DERIVED from that data (`applyRule`), so the
  domain and the behaviour can never disagree, and a negation proof can walk
  the rule table as data ("does category c occur at any position?").
* String construction is direct (`build : List (List String) → List String`),
  no global yield: for the concatenative rules here, `build = List.flatten`.
-/

namespace BareSyntax

/-- Lexemes are globally shared plain strings. An expression is a lexeme
    string (a `List String`) paired with a category. Categories are
    per-grammar, so `Expr` is parameterised by the category type. -/
abbrev Expr (Cat : Type) := List String × Cat

/-- A named rule over category type `Cat`. Its domain (`posCat`) is explicit
    data so the rule table is checkable; `build` says how the output string is
    assembled from the inputs' strings. -/
structure Rule (Cat : Type) where
  name    : String
  posCat  : List Cat                      -- required category at each position; arity = length
  result  : Cat                           -- output category
  build   : List (List String) → List String   -- how to assemble the output string

/-- A grammar as data: a category type (decidable), a finite lexicon, a finite
    rule table. -/
structure BareGrammar where
  Cat     : Type
  decCat  : DecidableEq Cat
  lexicon : List (Expr Cat)
  rules   : List (Rule Cat)

/-- Expose each grammar's `decCat` field to instance search, so `decide`/`∈`
    over `G.Cat` work without a manual `haveI := G.decCat` at every call site.
    (Friction note for REPORT: category decidability lives in a struct field,
    not a class, precisely because categories are per-grammar data.) -/
instance (priority := low) instDecEqCat (G : BareGrammar) : DecidableEq G.Cat := G.decCat

/-- Apply a rule to a list of input expressions. DERIVED from the explicit
    domain: succeeds iff the inputs' categories match `r.posCat` exactly, and
    then builds the output string and stamps `r.result`. -/
def applyRule (G : BareGrammar) (r : Rule G.Cat)
    (inputs : List (Expr G.Cat)) : Option (Expr G.Cat) :=
  haveI := G.decCat
  if inputs.map Prod.snd = r.posCat then
    some (r.build (inputs.map Prod.fst), r.result)
  else
    none

/- Generation. Two ways to derive an expression:
   * `lex`  — it is a lexicon entry.
   * `app`  — it is `applyRule r inputs`, where `r` is in the table and every
              input is itself derivable (`DerivList`, the paired inductive
              that sidesteps nested positivity).
   Mutual with `DerivList`; recurse with match/cases, never `induction`. -/
mutual
inductive Deriv (G : BareGrammar) : Expr G.Cat → Type where
  | lex {e : Expr G.Cat} : e ∈ G.lexicon → Deriv G e
  | app {r : Rule G.Cat} {inputs : List (Expr G.Cat)} {out : Expr G.Cat} :
      r ∈ G.rules → DerivList G inputs → applyRule G r inputs = some out → Deriv G out

inductive DerivList (G : BareGrammar) : List (Expr G.Cat) → Type where
  | nil  : DerivList G []
  | cons {e : Expr G.Cat} {es : List (Expr G.Cat)} :
      Deriv G e → DerivList G es → DerivList G (e :: es)
end

/-- Grammaticality: the string `s` yields category `C` iff some derivation
    exists. Negation goals (`¬ CanYield …`) are the vertical slice's target. -/
def CanYield (G : BareGrammar) (s : List String) (C : G.Cat) : Prop :=
  Nonempty (Deriv G (s, C))

end BareSyntax
