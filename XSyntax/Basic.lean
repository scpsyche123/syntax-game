/-
Basic vocabulary: syntactic categories (`Pos`), their two renderings, the
space-aware concatenation used by `yield`/`plot`, and the category-indexed
`LexicalEntry`.

Second-generation design: the category is a *parameter* of `LexicalEntry`,
not a field. `LexicalEntry .D` and `LexicalEntry .V` are different types;
category mismatches die in the lexicon, before any tree is built.
-/

namespace XSyntax

-- ᴀ ʙ ᴄ ᴅ ᴇ ꜰ ɢ ʜ ɪ ᴊ ᴋ ʟ ᴍ ɴ ᴏ ᴘ -Q ʀ ꜱ ᴛ ᴜ ᴠ ᴡ -X ʏ ᴢ

/-- Syntactic categories (parts of speech). -/
inductive Pos where
  | N
  | V
  | A
  | P
  | Adv
  | T
  | D
  | C
  | Conj
--   | Trace
  deriving Repr, DecidableEq

/-- Ordinary `ToString` of `Pos`. -/
def PlotPos (PP : Pos) : String :=
  match PP with
  | .N    => "N"
  | .V    => "V"
  | .A    => "A"
  | .P    => "P"
  | .Adv  => "Adv"
  | .T    => "T"
  | .D    => "D"
  | .C    => "C"
  | .Conj => "Conj"
--   | _     => "X"

/-- Small-caps `ToString` of `Pos`, used when labelling phrases. -/
def PlotPosSpecialFont (PP : Pos) : String :=
  match PP with
  | .N    => "ɴ"
  | .V    => "ᴠ"
  | .A    => "ᴀ"
  | .P    => "ᴘ"
  | .Adv  => "ᴀᴅᴠ"
  | .T    => "ᴛ"
  | .D    => "ᴅ"
  | .C    => "ᴄ"
  | .Conj => "ᴄᴏɴᴊ"
--   | _     => "X"

/-- Space-aware concatenation: empty operands don't introduce stray spaces. -/
def StrAdd (a b : String) : String :=
    if a == "" then b
    else if b == "" then a
    else a ++ " " ++ b

/-- A lexical entry at category `c`. The category lives on the TYPE
    (`LexicalEntry .D`), not inside the value. -/
structure LexicalEntry (c : Pos) where
  word : String
  deriving Repr

end XSyntax
