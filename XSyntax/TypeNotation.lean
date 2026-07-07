/-
Linguistic notation for the goal panel.

`notation` is BIDIRECTIONAL: it registers a parser *and* a pretty-printer.
So `XTree Bar.two Pos.D` not only can be written `DP` — Lean will also
DISPLAY it as `DP` in the infoview. The audience sees linguistics; the
type theory stays backstage. (This is why `notation` and not `abbrev`:
`abbrev` only reads, it doesn't print.)

Two groups:
1. 27 phrase-structure types: `NP`, `N′`, `N⁰`, … for all nine categories.
2. 9 bare-category displays: `D` for `Pos.D`, so a licensing goal renders
   as `Selects D N` instead of `Selects Pos.D Pos.N`.

⚠ Group 2 reserves single capital letters as global tokens. Inside this
project that is intended (they are the player's vocabulary); but it means
downstream files should not use `N`, `V`, `A`, `P`, `T`, `D`, `C` as
identifiers (e.g. binder names). If that ever bites, comment group 2 out —
group 1 is unaffected.
-/

import XSyntax.Operations

namespace XSyntax

/-! ### Group 1: phrase-structure types -/

notation "NP"    => XTree Bar.two Pos.N
notation "VP"    => XTree Bar.two Pos.V
notation "AP"    => XTree Bar.two Pos.A
notation "PP"    => XTree Bar.two Pos.P
notation "AdvP"  => XTree Bar.two Pos.Adv
notation "TP"    => XTree Bar.two Pos.T
notation "DP"    => XTree Bar.two Pos.D
notation "CP"    => XTree Bar.two Pos.C
notation "ConjP" => XTree Bar.two Pos.Conj

notation "N′"    => XTree Bar.one Pos.N
notation "V′"    => XTree Bar.one Pos.V
notation "A′"    => XTree Bar.one Pos.A
notation "P′"    => XTree Bar.one Pos.P
notation "Adv′"  => XTree Bar.one Pos.Adv
notation "T′"    => XTree Bar.one Pos.T
notation "D′"    => XTree Bar.one Pos.D
notation "C′"    => XTree Bar.one Pos.C
notation "Conj′" => XTree Bar.one Pos.Conj

notation "N⁰"    => XTree Bar.zero Pos.N
notation "V⁰"    => XTree Bar.zero Pos.V
notation "A⁰"    => XTree Bar.zero Pos.A
notation "P⁰"    => XTree Bar.zero Pos.P
notation "Adv⁰"  => XTree Bar.zero Pos.Adv
notation "T⁰"    => XTree Bar.zero Pos.T
notation "D⁰"    => XTree Bar.zero Pos.D
notation "C⁰"    => XTree Bar.zero Pos.C
notation "Conj⁰" => XTree Bar.zero Pos.Conj

/-! ### Group 2: bare-category displays (for `Selects` goals) -/

notation "N"    => Pos.N
notation "V"    => Pos.V
notation "A"    => Pos.A
notation "P"    => Pos.P
notation "Adv"  => Pos.Adv
notation "T"    => Pos.T
notation "D"    => Pos.D
notation "C"    => Pos.C
notation "Conj" => Pos.Conj

end XSyntax
