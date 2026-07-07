import GameServer.Commands
import XSyntax.Tactics

/-! Tactic documentation for the player's instruction set.
    Each command is one X-bar rule. -/

/-- `head "词"` —— 在 X⁰ 目标上种下一个词。空头(不发音的功能中心语)写 `head ""`。 -/
TacticDoc head

/-- `nospec` —— 规则 XP → X′:这个短语没有 specifier,由 X′ 直接封顶。
    空洞投射的上半层。 -/
TacticDoc nospec

/-- `nocomp` —— 规则 X′ → X⁰:这个中心语没有补足语,直接投射到 bar 层。
    空洞投射的下半层。 -/
TacticDoc nocomp

/-- `complement XP` —— 规则 X′ → X⁰ + 补足语:宣告中心语选择一个什么范畴的补足语。
    选择在此刻当场检查:无许可的搭配会被立即拒绝。 -/
TacticDoc complement

/-- `adjoinL XP` —— 左附接:在 X′ 的左侧挂一个附加语,层级不变(X′ → 附加语 + X′)。 -/
TacticDoc adjoinL

/-- `adjoinR XP` —— 右附接:在 X′ 的右侧挂一个附加语,层级不变(X′ → X′ + 附加语)。 -/
TacticDoc adjoinR

/-- `specifier XP` —— 规则 XP → Spec + X′:宣告这个短语带一个什么范畴的 specifier。 -/
TacticDoc specifier
