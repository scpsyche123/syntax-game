import Game.Metadata

World "PhraseII"
Level 3

Title "迁移关:自己组装一整句"

Introduction "
目标:*the big dog sees the cat*,一个完整的 CP。这一关没有逐步提示——你学过的
零件这里全都要用上,由你自己拼。

先在脑子里搭骨架(这是唯一的整体提示):

- 最外层 **CP**:空 C,选一个 TP。
- **TP**:主语是 DP *the big dog*(住在 specifier);T 是现在时,空头。
- **T′** 底下的 **VP**:*sees* 是及物动词,选一个宾语 DP *the cat*。
- 两个 DP 内部:*the* 是补足语关系里的 D 头;*big* 是附加语(AP)。

一层一层往下,先搭主语、再搭谓语。搭错了,系统会用语言学的话拦住你,读完再来。
"

set_option XSyntax.treeView.enabled false

/-- 为 *the big dog sees the cat* 建一个完整的 CP。自己组装。 -/
Statement (the : XSyntax.Lexicon .D "the") (big : XSyntax.Lexicon .A "big")
    (dog : XSyntax.Lexicon .N "dog") (sees : XSyntax.Lexicon .V "sees")
    (cat : XSyntax.Lexicon .N "cat")
    (nullC : XSyntax.Lexicon .C "") (nullT : XSyntax.Lexicon .T "") :
    XSyntax.Parses .two .C "the big dog sees the cat" := by
  Hint "CP 外壳:`nospec` → `complement TP` → 空 C `head \"\"`。"
  nospec
  complement TP
  head ""
  Hint "TP 带主语:`specifier DP`。先把主语 *the big dog* 整个搭完,再回头处理 T′。"
  specifier DP
  nospec
  complement NP
  head "the"
  nospec
  adjoinL AP
  nospec
  nocomp
  head "big"
  nocomp
  head "dog"
  Hint "主语完工,现在是 `T′`:现在时空 T,`complement VP` 后 `head \"\"`。"
  complement VP
  head ""
  Hint "VP 里 *sees* 选宾语:`nospec` → `complement DP`,然后像搭主语一样搭 *the cat*。"
  nospec
  complement DP
  head "sees"
  nospec
  complement NP
  head "the"
  nospec
  nocomp
  head "cat"

Conclusion "
你独立组装了一整句——主语 DP、时态、及物动词、宾语 DP,全部到位。这是 boss 前
最后的彩排:下一关的句子更长,但用的还是这同一套动作,没有任何新指令。

准备好见识那句最著名的句子了吗?
"
