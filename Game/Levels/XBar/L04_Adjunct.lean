import Game.Metadata

World "XBar"
Level 4

Title "附加语:可有可无,层级不变"

Introduction "
目标:*my big house*。比上一关多了一个 *big*——形容词短语,作**附加语**(adjunct)。

附加语和补足语的区别是 X-bar 理论的辨析核心:补足语被中心语选择、改变层级
(X⁰ + 补足语 → X′);附加语不被选择、**不改变层级**(X′ + 附加语 → 还是 X′)。
所以附加语可以堆叠,也可以不出现。

新规则 `adjoinL XP`:在 X′ 的左侧挂一个附加语。
注意挂上去的必须是**完整的短语**——*big* 要先自己投射成 AP。
"

/-- 为 *my big house* 建一个 DP。 -/
Statement : XSyntax.Utters .two .D "my big house" := by
  nospec
  complement NP
  head "my"
  Hint "NP 里要先挂附加语再放中心语:`nospec` 之后 `adjoinL AP`。"
  nospec
  adjoinL AP
  Hint "先把 AP 搭完(它自己也要走全程投射),回头再处理 N′。"
  nospec
  nocomp
  head "big"
  nocomp
  head "house"

Conclusion "
注意 `adjoinL AP` 前后:目标从 `N′` 变成 `AP` 和 `N′`——层级没有升,
附加语只是横向挂载。这就是\"附接不改变 bar 级别\"在操作层面的样子。
"

NewTactic adjoinL
