import Game.Metadata

World "PhraseI"
Level 5

Title "为什么造不出来"

Introduction "
这个游戏的核心论点,到现在你已经用过很多次,但从没被要求**证明**过:

> 不合语法 = 这样的结构根本造不出来。

上一关,*the sleep*(把限定词直接接到动词上)会被拒绝——因为 D 选 N 的许可证
存在,D 选 V 的许可证不存在。

先做个实验(不计分,随便试):去 Playground 或上一关的 `V′` 目标上,
输入 `complement VP` 试试把一个 D 接到 V 上,读一读系统怎么拒绝你。

这一关不搭树——**证明**这样的许可证根本不存在。新规则 `cannotSelect`:
在一个「¬ Selects c d」(c 不选择 d)的目标上,穷尽选择表里的每一条许可,
一条都不匹配,证明就成立。如果这对组合其实合法,`cannotSelect` 会拒绝你,
和 `complement` 拒绝非法搭配时用的是同一套语言。
"

/-- 证明 D 不选择 V——*the sleep* 这类病句背后的结构原因。 -/
Statement : ¬ XSyntax.Selects .D .V := by
  cannotSelect

Conclusion "
证明完毕:D 不选择 V。

这和上一关 `complement AP`/`complement VP` 报错的原因完全一致——只是这次
你自己把「许可证不存在」变成了一个被类型系统全程审查过的证据,而不是一句
系统吐出来的报错。**合语法性 = 存在一棵树;不合语法性 = 存在一个「这样的
许可证不存在」的证明。**两句话,同一个硬币的两面。
"

NewTactic cannotSelect
