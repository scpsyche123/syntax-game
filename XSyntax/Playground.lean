/-
The presentation walkthrough. Five scenes. Run in VS Code; the infoview's
goal panel is the game screen.

v3: player vocabulary is purely linguistic (seven X-bar commands, nothing
else), and every mistake answers in linguistics — feel free to improvise
errors live: any command at any wrong position now has a line to say.
-/

import XSyntax.Tactics

namespace XSyntax

/-! ## Scene 1 · Warm-up: a bare noun phrase, three keystrokes

    Every projection is an explicit move. `head` alone cannot close an
    `NP` goal — the audience watches the levels get climbed. -/

example : NP := by
  nospec              -- ⊢ N′
  nocomp              -- ⊢ N⁰
  head "ideas"        -- 🎉

/-! ## Scene 2 · "my big house": build it as a `def`, then hear it

    Built by tactics, then handed to `yield` and `plot` — the tree is a
    first-class object, not just a proof. Note `complement NP`: selection
    is checked at that keystroke; on success the license is already in
    the tree, and two goals remain. -/

def my_big_house : DP := by
  nospec              -- ⊢ D′
  complement NP       -- ⊢ D⁰   ⊢ NP     (license checked & filed)
  head "my"           -- ⊢ NP
  nospec              -- ⊢ N′
  adjoinL AP          -- ⊢ AP   ⊢ N′
  nospec              -- ⊢ A′   …
  nocomp              -- ⊢ A⁰   …
  head "big"          -- ⊢ N′
  nocomp              -- ⊢ N⁰
  head "house"        -- 🎉

#eval yield my_big_house    -- "my big house"
#eval plot my_big_house     -- "[ᴅᴘ my [ɴᴘ [ᴀᴘ big] house]]"

/-! ## Scene 3 · Geometry violation (uncomment live)

    Planting a head directly at a bar-level goal. The rejection speaks
    linguistics:

        ✗ a bare head cannot stand at N′ — project it first (nocomp / nospec)
-/

-- example : N′ := by
--   head "house"     -- ✗ dies here, in the words above

/-! ## Scene 4 · Selection violation (uncomment live)

    "the sleeps". ONE keystroke. The error lands on the exact move where
    the linguistic mistake is made:

        ✗ selection violation: D does not select V

    Ungrammaticality = no license exists = the combination is
    unrepresentable. -/

-- example : D′ := by
--   complement VP    -- ✗ dies here, immediately

/-! ## Scene 5 · Finale: the famous sentence

    Build the tree with the seven rules — nothing else. Then hear it.
    Then state grammaticality, Church-style, as a one-line corollary:
    the sentence is grammatical BECAUSE a tree exists, and the witness
    is the tree just built. -/

def colorless_tree : CP := by
  -- the CP shell
  nospec                  -- ⊢ C′
  complement TP           -- ⊢ C⁰   ⊢ TP        (C–T license filed)
  head ""                 -- null C
  -- the TP: subject in Spec, T′ to come
  specifier DP            -- ⊢ DP   ⊢ T′
  -- the subject DP
  nospec                  -- ⊢ D′
  complement NP           -- ⊢ D⁰   ⊢ NP        (D–N license filed)
  head ""                 -- null D
  nospec                  -- ⊢ N′
  adjoinL AP              -- ⊢ AP   ⊢ N′
  nospec
  nocomp
  head "Colorless"        -- first adjunct done
  adjoinL AP              -- ⊢ AP   ⊢ N′
  nospec
  nocomp
  head "green"            -- second adjunct done
  nocomp                  -- ⊢ N⁰
  head "ideas"            -- subject DP done      ⊢ T′
  -- the T′
  complement VP           -- ⊢ T⁰   ⊢ VP        (T–V license filed)
  head ""                 -- null T
  nospec                  -- ⊢ V′
  adjoinR AdvP            -- ⊢ V′   ⊢ AdvP
  nocomp                  -- ⊢ V⁰
  head "sleep"            -- ⊢ AdvP
  nospec
  nocomp
  head "furiously"        -- 🎉

#eval yield colorless_tree   -- "Colorless green ideas sleep furiously"
#eval plot colorless_tree    -- labelled bracketing of the full CP

/-- Grammaticality, Church-style. The proof is: exhibit the tree. -/
theorem colorless_is_grammatical :
    ∃ t : CP, yield t = "Colorless green ideas sleep furiously" :=
  ⟨colorless_tree, rfl⟩

/-! ## Regression pins · one solution per level, yield checked against the
    level's target sentence.

    L04 (`my_big_house`) and L05 (`colorless_tree`) are the defs built in the
    scenes above; L01–L03 get their own solution defs here so all five level
    targets are pinned in one place. These do NOT constrain players — a player
    may still build any well-formed phrase (grammaticality = a tree exists).
    They guard OUR intended solutions against silent drift: change a level's
    tactics and break its target string, and the build fails here. -/

def l01_head : N⁰ := by head "ideas"
def l02_np   : NP := by nospec; nocomp; head "ideas"
def l03_dp   : DP := by nospec; complement NP; head "my"; nospec; nocomp; head "house"

#guard yield l01_head       == "ideas"                                    -- L01
#guard yield l02_np         == "ideas"                                    -- L02
#guard yield l03_dp         == "my house"                                 -- L03
#guard yield my_big_house   == "my big house"                             -- L04
#guard yield colorless_tree == "Colorless green ideas sleep furiously"    -- L05

end XSyntax
