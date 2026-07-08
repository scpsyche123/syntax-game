import Game.Metadata

World "PhraseII"
Level 4

Title "Colorless green ideas sleep furiously"

Introduction "
终关:Chomsky 1957 年那句著名的话——语义荒谬,句法完美。
你要为整句建一棵 CP,证明它**合语法**。

好消息:**没有新指令**。你在前十一关练熟的动作,这里全都要用,但一个不多。
这句话只是更长——它把你会的零件叠了好几层:

- CP 外壳(空 C)、TP(主语 + 空 T)、VP,和上一关同一套骨架;
- 主语 *Colorless green ideas* 是一个 DP:空 D + NP,NP 上**左附接**两个 AP
  (*Colorless*、*green*)——附加语可以堆叠,还记得吗;
- 谓语 *sleep furiously* 是一个 VP:*furiously* 是**右附接**的 AdvP。

三个空头(C、T、D)都在这句里出现——正是你在 L10 认识的三种沉默。
自上而下,一层一层来。
"

/-- 为 *Colorless green ideas sleep furiously* 建一棵完整的 CP。 -/
Statement : XSyntax.Utters .two .C "Colorless green ideas sleep furiously" := by
  Hint "最外层是 CP:`nospec`,然后 C 选择什么?"
  nospec
  complement TP
  head ""
  Hint "TP 带主语:`specifier DP`。"
  specifier DP
  Hint "先搭主语 DP:空 D 选 NP,NP 里两个 AP 左附接。"
  nospec
  complement NP
  head ""
  nospec
  adjoinL AP
  nospec
  nocomp
  head "Colorless"
  adjoinL AP
  nospec
  nocomp
  head "green"
  nocomp
  head "ideas"
  Hint "主语完工。现在是 `T′`:空 T 选择 VP。"
  complement VP
  head ""
  Hint "VP 内部:*furiously* 右附接在 V′ 上,先 `adjoinR AdvP` 再种 *sleep*。"
  nospec
  adjoinR AdvP
  nocomp
  head "sleep"
  nospec
  nocomp
  head "furiously"

Conclusion "
🎉 这棵树存在——所以这句话合语法。

这就是整个游戏的论点浓缩成一关:**合语法性 = 存在一棵树**。
你刚才不是画了一张图,而是构造了一个被类型系统全程审查过的证据。

而这句话**毫无意义**——绿色的想法不会无色,想法也不会睡觉。合语法却无意义:
这正是 Chomsky 用它证明的事——**句法自成一体,不依赖语义**。反过来也成立:
*ideas green sleep* 有词、勉强能猜出意思,却**不合语法**——你在这个系统里
根本搭不出它的树。意义和合语法,是两件独立的事。

(顺带:你全程没有写一行 Lean——你用的每一条指令,都是一条 X-bar 规则本身。)
"
