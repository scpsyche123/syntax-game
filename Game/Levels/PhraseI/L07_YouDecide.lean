import Game.Metadata

World "Phrase I"
Level 7

Title "你来判断"

Introduction "
目标:*the strange dog*,一个 DP。

这一关**没有分步提示**。你已经有了全部需要的指令——现在轮到你自己判断
每一步该用哪个。

判断的关键就是上两关的对立:

- *the* 和 *dog* 的关系:*the* 是 D,它**选择**一个名词性补足语。→ 用哪个指令?
- *strange* 和 *dog* 的关系:形容词**不被** *dog* 选择,它只是修饰,可来可不来。→ 又该用哪个?

想清楚「这是选择还是修饰」,指令自然就定了。搭错了也不要紧——系统会用
语言学的话告诉你哪里不对,读完再来。
"

/-- 为 *the strange dog* 建一个 DP。自己判断补足语 vs 附加语。 -/
Statement : XSyntax.Utters .two .D "the strange dog" := by
  nospec
  complement NP
  head "the"
  nospec
  adjoinL AP
  nospec
  nocomp
  head "strange"
  nocomp
  head "dog"

Conclusion "
你自己走完了:*the* 是补足语关系里的头(D 选 NP),*strange* 是附加语(AP 附接在
N′ 上,不改变层级)。同一棵 DP 里,选择和修饰各就各位。

能不靠提示分清这两者,你就掌握了短语内部结构最要紧的一课。

下一关是 Phrase I 的收尾:右附接,以及一个新范畴——副词(Adv)。
"
