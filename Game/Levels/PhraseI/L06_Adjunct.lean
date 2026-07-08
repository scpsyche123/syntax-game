import Game.Metadata

World "PhraseI"
Level 6

Title "附加语:可有可无,层级不变"

Introduction "
目标:*my big house*,一个 DP。比 *my house* 多了一个 *big*——形容词短语,
作**附加语**(adjunct)。

附加语和补足语的区别,是 X-bar 理论的辨析核心:

- **补足语**被中心语**选择**、**改变层级**(X⁰ + 补足语 → X′)。上一关的
  *the cat*、*the house* 就是补足语——头点名要它,而且必须有。
- **附加语**不被选择、**不改变层级**(X′ + 附加语 → 还是 X′)。所以附加语
  可以堆叠(*big old red house*),也可以完全不出现(*house*)。

新规则 `adjoinL XP`:在 X′ 的左侧挂一个附加语,bar 级别不变。
注意挂上去的必须是**完整的短语**——*big* 要先自己投射成 AP。
"

set_option XSyntax.treeView.enabled false

/-- 为 *my big house* 建一个 DP。 -/
Statement : XSyntax.Utters .two .D "my big house" := by
  Hint "老三步开头:`nospec`,然后 D 选 NP —— `complement NP`。"
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
附加语只是横向挂载。这就是「附接不改变 bar 级别」在操作层面的样子。

对照上一关:*the cat* 里 `complement` 把 `V′` 收成了 `V⁰ + DP`(层级下降一格);
这一关 `adjoinL` 让 `N′` 生出一个 `AP` 却还留在 `N′`(层级不动)。同样是往树上
加东西,补足语和附加语在几何上就是不一样。

下一关不给你念稿——轮到你自己判断,哪个位置该用补足语,哪个该用附加语。
"

NewTactic adjoinL
NewDefinition «APDef»
NewHiddenTactic «AP»
