import Game.Metadata

World "Phrase II"
Level 2

Title "整句的外壳:认识 C"

Introduction "
目标:*cats sleep*,建成一个 **CP**。

先看时态。这次没有 *will*——但句子仍然是现在时。X-bar 理论说:时态**永远**在,
哪怕它不发音。*cats sleep* 顶上仍有一个 T,只是这个现在时的 T 是**空头**
(`head \"\"`)——看不见,但结构上在,和上一关的 *will* 占同一个位置。

再看最外层。整句真的到 TP 就封顶了吗?考虑 *I think **that** cats sleep*——
那个 *that* 是**标句词**(complementizer),它引导一个小句。它也是一个中心语,
记作 **C**,撑起一个 **CP**(标句词短语)。X-bar 理论主张:哪怕是不带 *that*
的主句 *cats sleep*,最外层也有一个 C,只是这个陈述主句的 C 是**空头**。

所以整句的完整骨架是:CP ⟶ C⁰ + TP。C 选择 TP 作补足语。
"

/-- 为 *cats sleep* 建一个完整的 CP(空 C、空 T)。 -/
Statement : XSyntax.Utters .two .C "cats sleep" := by
  Hint "最外层是 CP:`nospec` 到 C′,然后 C 选 TP —— `complement TP`。"
  nospec
  complement TP
  Hint "陈述主句的 C 不发音:`head \"\"`。"
  head ""
  Hint "TP 带主语:`specifier NP`,主语 *cats*。"
  specifier NP
  nospec
  nocomp
  head "cats"
  Hint "T′:现在时的 T 也不发音。`complement VP` 之后 `head \"\"`。"
  complement VP
  head ""
  nospec
  nocomp
  head "sleep"

Conclusion "
你搭出了完整的小句外壳:CP ⟶ C⁰ + TP ⟶ C⁰ + (主语 + T′) ⟶ … 。

这一关出现了**两个空头**,它们为空的理由**各不相同**:

- **空 C**:这是个陈述主句,不需要 *that* 之类的标句词——但 C 这个位置还在。
- **空 T**:英语现在时(第三人称复数)不额外加助动词——但时态还在。

(还有第三种空头你很快会见到:**空 D**。像 *cats*、*ideas* 这样的**光杆复数**
名词,前面不带限定词,但 X-bar 分析里它们仍被包在一个空 D 的 DP 里。三种沉默,
三种不同的语言学理由——别把它们混成同一件事。)

下一关不给提示:你要独立搭一个更长的句子,把学过的零件全用上。
"

NewDefinition «CPDef»
