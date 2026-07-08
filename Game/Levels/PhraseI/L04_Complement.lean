import Game.Metadata

World "PhraseI"
Level 4

Title "补足语与选择:及物动词打样"

Introduction "
目标:*sees the cat*,一个 VP。

*sees* 是**及物动词**(transitive verb)——光有 *sees* 不成句,它**需要**一个宾语。
这不是风格问题,是句法上的硬要求:*sees* 在词库里就标记着「我要选一个 D 范畴的
搭档」。这种「头对补足语范畴的强制要求」,语言学上叫**选择**或**次范畴化**
(subcategorization / c-selection)。

新规则 `complement XP`:在 X′ 目标上,宣告中心语要选择一个什么范畴的补足语。
它会同时开出两个子目标——中心语本身,和你宣告的补足语——而且**选择在这一刻
当场检查**:V 选 D 有许可,V 选 A 没有,系统立刻知道。

*the cat* 本身也是一个短语:*the* 是上一关认识的 D,它选择一个 NP(*cat*)作
补足语——同一套机制,套了两层。

先做个实验:走到 `V′` 之后,故意输入 `complement AP`,读一读系统怎么说。
然后再用 `complement DP` 走正路。
"

set_option XSyntax.treeView.enabled false

/-- 为 *sees the cat* 建一个 VP。 -/
Statement (sees : XSyntax.Lexicon .V "sees") (the : XSyntax.Lexicon .D "the")
    (cat : XSyntax.Lexicon .N "cat") :
    XSyntax.Parses .two .V "sees the cat" := by
  Hint "`nospec` 开顶:VP 拆到 V′。"
  nospec
  Hint "现在在 `V′`。想试非法搭配就是此刻:`complement AP`。正路是 `complement DP`。"
  complement DP
  Hint "两个目标:先种中心语 `head \"sees\"`,再去搭 DP。"
  head "sees"
  Hint "*the cat* 是个 DP:`nospec` 之后 `complement NP`,D 选 N 一样要检查许可。"
  nospec
  complement NP
  head "the"
  nospec
  nocomp
  head "cat"

Conclusion "
如果你做了那个实验,你已经见过这个游戏最重要的一句话:

`✗ selection violation: V does not select A`

不合语法的搭配,在这个系统里不是\"被标红的错误\",而是**根本造不出来的对象**——
它需要一张不存在的许可证。

你已经见过 D 选 N(*the cat*)。但反过来呢——D 能选 V 吗?比如把 *the* 直接接
到一个动词上?下一关不搭树,而是**证明**这样的许可证根本不存在。
"

NewTactic complement

-- 双轨并行,且刻意用两套不同的名字(教训来自 Phrase I 早期版本的一次事故,
-- 详见 CLAUDE.md 已知地雷/协作约定):
-- · NewDefinition 喂词汇/定义登记表(玩家词汇面板),登记键是 «NPDef» 等
--   (显示文本仍是 "NP",见 Metadata.lean;键名本身玩家永远看不到)。
-- · NewHiddenTactic 喂 tactic 门禁(complement/specifier/adjoin 的参数 token
--   被门禁当指令盘查,单靠 NewDefinition 放不行,故此处显式放行),登记键
--   是裸 «NP» 等(门禁按玩家敲的字面 token 匹配,不能改名)。
-- 两套键名故意不同,避免 GameServer 的隐藏名单跨类别连累词汇面板。
-- VP 一并注册(供 Phrase II 的 T 选 VP 用),此处只是登记,尚未真的当参数用。
NewDefinition «NPDef» «VPDef» «DPDef»
NewHiddenTactic «NP» «VP» «DP»
