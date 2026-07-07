import Game.Metadata

World "XBar"
Level 3

Title "补足语与选择"

Introduction "
目标:*my house*,一个 DP——限定词 *my* 作中心语,带一个 NP 补足语。

新规则 `complement XP`:在 X′ 目标上,宣告中心语要选择一个什么范畴的补足语。
它会同时开出两个子目标:中心语本身,和你宣告的补足语。

但**选择不是自由的**:D 选择 NP,不选择 VP——这是词库知识,叫选择限制
(c-selection)。系统在你敲下 `complement` 的那一刻当场检查。

先做个实验:走到 `D′` 之后,故意输入 `complement VP`,读一读系统怎么说。
然后再用 `complement NP` 走正路。
"

/-- 为 *my house* 建一个 DP。 -/
Statement : XSyntax.Utters .two .D "my house" := by
  Hint "老规矩,`nospec` 开顶。"
  nospec
  Hint "现在在 `D′`。想试非法搭配就是此刻:`complement VP`。正路是 `complement NP`。"
  complement NP
  Hint "两个目标:先种中心语 `head \"my\"`,再去搭 NP。"
  head "my"
  nospec
  nocomp
  head "house"

Conclusion "
如果你做了那个实验,你已经见过这个游戏最重要的一句话:

`✗ selection violation: D does not select V`

不合语法的搭配,在这个系统里不是\"被标红的错误\",而是**根本造不出来的对象**——
它需要一张不存在的许可证。
"

NewTactic complement
NewDefinition «NP» «VP» «AP» «PP» «AdvP» «TP» «DP» «CP» «ConjP»

-- 双轨并行:NewDefinition 喂词汇/定义登记表(玩家词汇面板);
-- NewHiddenTactic 喂 tactic 门禁(complement/specifier/adjoin 的参数 token
-- 被门禁当指令盘查,单靠 NewDefinition 放不行,故此处显式放行)。
-- 全九类一次登齐,后续关卡(L04 用 AP,L05 用 TP/DP/… )自动继承。
NewHiddenTactic «NP» «VP» «AP» «PP» «AdvP» «TP» «DP» «CP» «ConjP»
