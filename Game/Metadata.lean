import GameServer.Commands
import XSyntax.Tactics

/-! Tactic documentation for the player's instruction set.
    Each command is one X-bar rule. -/

/-- `head "词"` —— 在 X⁰ 目标上种下一个词；引号里只能是一个词。空头(不发音的功能中心语)写 `head ""`。 -/
TacticDoc head

/-- `nospec` —— 规则 XP → X′:这个短语没有 specifier,由 X′ 直接封顶。
    空洞投射的上半层。 -/
TacticDoc nospec

/-- `nocomp` —— 规则 X′ → X⁰:这个中心语没有补足语,直接投射到 bar 层。
    空洞投射的下半层。 -/
TacticDoc nocomp

/-- `complement XP` —— 规则 X′ → X⁰ + 补足语:宣告中心语要选择一个什么范畴的补足语。
    选择在此刻当场检查:无许可的搭配会被立即拒绝。 -/
TacticDoc complement

/-- `adjoinL XP` —— 左附接:在 X′ 的左侧挂一个附加语,层级不变(X′ → 附加语 + X′)。 -/
TacticDoc adjoinL

/-- `adjoinR XP` —— 右附接:在 X′ 的右侧挂一个附加语,层级不变(X′ → X′ + 附加语)。 -/
TacticDoc adjoinR

/-- `specifier XP` —— 规则 XP → Spec + X′:宣告这个短语带一个什么范畴的 specifier。 -/
TacticDoc specifier

/-- `cannotSelect` —— 在「¬ Selects c d」目标上证明这样的许可证不存在:穷尽
    选择表的构造子,没有一个匹配就直接判定。如果这对组合其实合法,会被拒绝。 -/
TacticDoc cannotSelect

/-! Definition docs: the phrase-type vocabulary players use in declarations.

Registered under `*Def`-suffixed keys, NOT the bare `NP`/`VP`/… tokens. Reason:
`NewHiddenTactic «NP» …` (in L03) also registers bare `NP` etc. under the
Tactic inventory (needed so `complement NP` clears the tactic-availability
gate — see L03's own comment). GameServer's `MakeGame` pools every level's
hidden-item names into ONE flat, type-blind `HashSet Name` before deciding
what to hide in the JSON output: if a Definition entry has the SAME bare
name as a hidden Tactic entry, it gets hidden too, even though `NewDefinition`
never asked for that. Using a distinct key (`NPDef`, not `NP`) side-steps the
collision; the player-visible label (`as "NP"`) is unaffected — this is a
backstage bookkeeping key, not something a player ever types or sees. -/

/-- **NP**(名词短语):以名词为中心语的完整短语,如 *ideas*、*big house*。 -/
DefinitionDoc «NPDef» as "NP"

/-- **VP**(动词短语):以动词为中心语的完整短语,如 *sleep furiously*。 -/
DefinitionDoc «VPDef» as "VP"

/-- **AP**(形容词短语):以形容词为中心语的完整短语,如 *big*、*colorless*。 -/
DefinitionDoc «APDef» as "AP"

/-- **PP**(介词短语):以介词为中心语的完整短语。 -/
DefinitionDoc «PPDef» as "PP"

/-- **AdvP**(副词短语):以副词为中心语的完整短语,如 *furiously*。 -/
DefinitionDoc «AdvPDef» as "AdvP"

/-- **TP**(时制短语):以 T(时制/一致)为中心语的短语,主语住在它的 specifier 里。 -/
DefinitionDoc «TPDef» as "TP"

/-- **DP**(限定词短语):以限定词为中心语的短语,如 *my house*。 -/
DefinitionDoc «DPDef» as "DP"

/-- **CP**(标句词短语):以 C 为中心语的短语——整句的最外层。 -/
DefinitionDoc «CPDef» as "CP"

/-- **ConjP**(连词短语):以连词为中心语的短语。 -/
DefinitionDoc «ConjPDef» as "ConjP"
