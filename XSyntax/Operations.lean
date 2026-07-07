/-
The function layer. Three plain recursive functions — no `mutual`, no type
classes: the index family dissolved the reason those existed.

* `cat` / `bar` — former COMPUTATIONS, now PROJECTIONS: what used to need a
  recursive walk is read off a type-level annotation, O(1).
* `Head`  — its return type `LexicalEntry c` IS the endocentricity theorem:
  the head's category equals the tree's category, by signature.
* `yield` — the surface string.
* `plot`  — labelled bracketing; returns a plain `String` now, because the
  index carries the category the old plot had to haul upward itself.
-/

import XSyntax.Tree

namespace XSyntax

/-- The category of a tree: a projection of its type-level annotation. -/
def cat {b : Bar} {c : Pos} (_ : XTree b c) : Pos := c

/-- The bar level of a tree: a projection of its type-level annotation. -/
def bar {b : Bar} {c : Pos} (_ : XTree b c) : Bar := b

/-- The head a tree projects from. The return type states endocentricity. -/
def Head : XTree b c → LexicalEntry c
  | .word BP        => BP
  | .adjunctL _ pp  => Head pp
  | .adjunctR pp _  => Head pp
  | .compl pp _ _   => Head pp
  | .bareX0 pp      => Head pp
  | .bareX1 pp      => Head pp
  | .Spec _ pp      => Head pp

/-- The surface string. The license in `compl` is discarded with `_`. -/
def yield : XTree b c → String
  | .word BP        => BP.word
  | .adjunctL x2 x1 => StrAdd (yield x2) (yield x1)
  | .adjunctR x1 x2 => StrAdd (yield x1) (yield x2)
  | .compl x0 x2 _  => StrAdd (yield x0) (yield x2)
  | .bareX0 x0      => yield x0
  | .bareX1 x1      => yield x1
  | .Spec x2 x1     => StrAdd (yield x2) (yield x1)

/-- Labelled bracketing. Where a label is needed, we just ask `cat`. -/
def plot : XTree b c → String
  | .word BP        => BP.word
  | .adjunctL x2 x1 => StrAdd (plot x2) (plot x1)
  | .adjunctR x1 x2 => StrAdd (plot x1) (plot x2)
  | .compl x0 x2 _  => StrAdd (plot x0) (plot x2)
  | .bareX0 x0      => plot x0
  | .bareX1 x1      => "[" ++ PlotPosSpecialFont (cat x1) ++ "ᴘ " ++ plot x1 ++ "]"
  | .Spec x2 x1     => "[" ++ PlotPosSpecialFont (cat x1) ++ "ᴘ "
                           ++ StrAdd (plot x2) (plot x1) ++ "]"

#check @Head    -- XTree b c → LexicalEntry c  ← this line IS endocentricity

end XSyntax
