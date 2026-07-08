import Game.Metadata

World "PhraseII"
Level 1

Title "从短语到小句:认识 T"

Introduction "
到目前为止你搭的都是短语。现在要搭第一个**小句**(clause):*cats will sleep*。

一个关键问题:*cats will sleep* 里,谁是整句的头?不是动词 *sleep*。X-bar 理论
主张,英语的每个限定小句(finite clause)顶上都坐着一个专门承载**时态**的
中心语,记作 **T**(tense)。*will* 就是一个看得见的 T:它不表意义,只表
「将来」这个时态信息。整句因此是一个 **TP**(时态短语)。

T 选择一个 VP 作补足语(*will* 底下是 *sleep*)。而**主语** *cats* 站在一个
新位置:TP 的 **specifier**——短语三元结构里我们一直空着的那个角。

新规则 `specifier XP`:在 XP 目标上,宣告它带一个什么范畴的 specifier,把 XP
拆成「specifier + X′」。主语是一个 NP(*cats*),所以是 `specifier NP`。

(说明:「主语住在 Spec,TP」是生成语法的一个主流分析,不是唯一分析。这个游戏
选定了这套几何;别的理论可能把主语放在别处。你在这里学的是一种被广泛使用的
标准分析。)
"

set_option XSyntax.treeView.enabled false

/-- 为 *cats will sleep* 建一个 TP。 -/
Statement (cats : XSyntax.Lexicon .N "cats") (will : XSyntax.Lexicon .T "will")
    (sleep : XSyntax.Lexicon .V "sleep") :
    XSyntax.Parses .two .T "cats will sleep" := by
  Hint "整句是 TP,带主语:`specifier NP`。会开出主语 NP 和 T′ 两个目标。"
  specifier NP
  Hint "先搭主语 *cats*(一个 NP):`nospec` / `nocomp` / `head \"cats\"`。"
  nospec
  nocomp
  head "cats"
  Hint "现在是 `T′`:T 选择 VP。`complement VP` 会把 *will* 放到 T⁰,*sleep* 留给 VP。"
  complement VP
  head "will"
  Hint "最后把 VP *sleep* 走完全程投射。"
  nospec
  nocomp
  head "sleep"

Conclusion "
你搭出了第一个句子级的结构。回顾骨架:TP ⟶ 主语NP + T′;T′ ⟶ T⁰(*will*) + VP。

两件事值得记住:
1. **时态是一个头**。哪怕它只是一个 *will*,它统领整个句子——句子是 TP,不是 VP。
2. **主语住在 specifier**。这是你第一次填上短语三元结构(spec-head-comp)最后那个角。

下一关:如果 *will* 换成现在时的 *cats sleep*,那个 T 还在吗?还有,整句的
最外层真的就到 TP 为止了吗?认识最后一个功能中心语——C。
"

NewTactic specifier
NewDefinition «TPDef»
NewHiddenTactic «TP»
