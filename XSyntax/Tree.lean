/-
The type layer: bar levels as an index (`Bar`), the licensing table
(`Selects`), and the doubly-indexed tree family (`XTree`).

Church style, twice over:
* GEOMETRY  — a tree at the wrong bar level is not "marked bad", it is
  unrepresentable: the constructors' index discipline forbids it.
* SELECTION — a head taking an unlicensed complement is unrepresentable:
  `compl` demands evidence of type `Selects c d`, and unlicensed pairs
  have no evidence (an uninhabited Prop).
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

/-- The licensing table. Each constructor is one licensed head–complement
    selection. Anything not listed (e.g. `Selects .D .V`) has NO
    inhabitant: not licensed = no evidence. -/
inductive Selects : Pos → Pos → Prop where
  | DN : Selects .D .N     -- determiners select nominal complements
  | TV : Selects .T .V     -- T selects VP
  | CT : Selects .C .T     -- C selects TP
  | PD : Selects .P .D     -- prepositions select DP
  | VD : Selects .V .D     -- transitive verbs select DP (unused yet; awaits per-item features)

/-- One doubly-indexed family replaces the old mutual block.
    `compl` demands a third argument: a license of type `Selects c d`. -/
inductive XTree : Bar → Pos → Type where
  | word     : LexicalEntry c → XTree .zero c
  | adjunctL : XTree .two d → XTree .one c → XTree .one c
  | adjunctR : XTree .one c → XTree .two d → XTree .one c
  | compl    : XTree .zero c → XTree .two d → Selects c d → XTree .one c
  | bareX0   : XTree .zero c → XTree .one c
  | bareX1   : XTree .one c → XTree .two c
  | Spec     : XTree .two d → XTree .one c → XTree .two c

end XSyntax
