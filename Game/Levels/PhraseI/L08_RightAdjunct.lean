import Game.Metadata

World "PhraseI"
Level 8

Title "右附接与副词"

Introduction "
目标:*sleep quickly*,一个 VP。

新范畴:**副词**(adverb,Adv)。*quickly* 修饰动词,和形容词修饰名词是平行的——
副词短语 AdvP 作附加语,挂在 V′ 上。

但这次挂在**右边**。前面的形容词 *big*/*strange* 都是左附接(`adjoinL`),挂在
中心语前面;而英语里副词常常跟在动词后面。新规则 `adjoinR XP`:在 X′ 的右侧
挂附加语,层级同样不变。

为什么 *big* 在左、*quickly* 在右?这是英语这门语言的**词序**决定的——附加语
挂在 X′ 的哪一侧,不同语言、不同附加语类型有不同的默认。X-bar 几何两边都允许,
具体哪边由语言的参数(和词项)敲定。这一关你先把「右附接」这个动作练熟。
"

/-- 为 *sleep quickly* 建一个 VP。 -/
Statement : XSyntax.Utters .two .V "sleep quickly" := by
  Hint "`nospec` 开顶到 V′。"
  nospec
  Hint "*quickly* 在 V′ 右侧:`adjoinR AdvP`。会开出 V′ 和 AdvP 两个目标。"
  adjoinR AdvP
  Hint "先收 V′:`nocomp` 到 V⁰,种 `head \"sleep\"`。"
  nocomp
  head "sleep"
  Hint "再把 AdvP 走完全程投射,种 `head \"quickly\"`。"
  nospec
  nocomp
  head "quickly"

Conclusion "
🎉 Phrase I 通关!

你现在能独立操作全部六条**短语内部**指令——`nospec`、`nocomp`、`head`、
`complement`、`adjoinL`、`adjoinR`——分得清补足语和附加语,还亲手证明过一次
不合法的选择根本不存在(`cannotSelect`)。

到目前为止,你搭的都是**短语**(NP、DP、VP……)。但短语怎么组成**句子**?
下一个世界「Phrase II」,你会认识两个撑起整句的功能中心语:T(时态)和 C(标句),
并第一次用到 specifier——主语的位置。
"

NewTactic adjoinR
NewDefinition «AdvPDef»
NewHiddenTactic «AdvP»
