/-
The type layer: bar levels as an index (`Bar`), the two licensing predicates
(`Selects`, `Lexicon`), and the doubly-indexed tree family (`XTree`).

Church style, three times over — an illformed tree is not "marked bad", it is
unrepresentable:
* GEOMETRY  — the constructors' index discipline forbids a wrong bar level.
* SELECTION — `compl` demands `Selects c d`; unlicensed head–complement pairs
  have no evidence (an uninhabited Prop).
* LEXICON   — `word` demands `Lexicon c e.word`; a word may only sit at a
  category the current lexicon licenses it for. `Lexicon` is empty globally, so
  the licenses come from the level's hypotheses (universal-grammar `Selects` is
  baked in; language-particular lexical facts are handed to the player).
-/

import XSyntax.Basic

namespace XSyntax

/-- Bar levels. The former three type names X0type/X1type/X2type,
    retired into three index VALUES of one family. -/
inductive Bar where
  | zero
  | one
  | two
  deriving Repr, DecidableEq

/-- The SELECTION licensing table. Each constructor is one licensed
    head–complement selection. Anything not listed (e.g. `Selects .D .V`) has NO
    inhabitant: not licensed = no evidence. These pairs are UNIVERSAL GRAMMAR,
    so they are baked in as constructors. -/
inductive Selects : Pos → Pos → Prop where
  | DN : Selects .D .N     -- determiners select nominal complements
  | TV : Selects .T .V     -- T selects VP
  | CT : Selects .C .T     -- C selects TP
  | PD : Selects .P .D     -- prepositions select DP
  | VD : Selects .V .D     -- transitive verbs select DP (unused yet; awaits per-item features)

/-- The LEXICAL licensing predicate: `Lexicon c w` witnesses that word `w` may
    realise category `c` IN THE LANGUAGE UNDER STUDY.

    Deliberately EMPTY — no constructors. `Selects`'s licit pairs are universal
    grammar (baked in); but which WORDS realise which categories is a contingent
    fact about a particular language, so `Lexicon` carries no global evidence. A
    level HANDS the player its lexicon as hypotheses (`the : Lexicon .D "the"`)
    and the player reasons FROM them. Consequence: in the empty context no
    word-tree exists at all (`word` demands a license) — grammaticality is
    always relative to a given lexicon, never free-floating. -/
inductive Lexicon : Pos → String → Prop

/-- One doubly-indexed family replaces the old mutual block. Two constructors
    demand a licence beyond geometry: `compl` a `Selects c d` (selection), and
    `word` a `Lexicon c e.word` (this word may realise this category). -/
inductive XTree : Bar → Pos → Type where
  | word     : (e : LexicalEntry c) → Lexicon c e.word → XTree .zero c
  | adjunctL : XTree .two d → XTree .one c → XTree .one c
  | adjunctR : XTree .one c → XTree .two d → XTree .one c
  | compl    : XTree .zero c → XTree .two d → Selects c d → XTree .one c
  | bareX0   : XTree .zero c → XTree .one c
  | bareX1   : XTree .one c → XTree .two c
  | Spec     : XTree .two d → XTree .one c → XTree .two c

end XSyntax
