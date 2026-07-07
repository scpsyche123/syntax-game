import Game.Metadata

World "Phrase I"
Level 3

Title "认识虚词:D 也是一个范畴"

Introduction "
到目前为止,你搭的都是**实词**(content word):名词、动词、形容词——它们
本身就带着意义。但句法里还有一类词,意义很稀薄,主要工作是**组织结构**,
叫**虚词**或**功能词**(function word)。英语里最好认的一类就是限定词
(determiner):*the*、*a*、*my*、*this*……

X-bar 理论对虚词和实词一视同仁:限定词照样是一个范畴的头,记作 **D**
(determiner)。*this*、*mine*、*hers* 这类词,可以自己撑起一整个 **DP**
(限定词短语),不需要另外接一个名词——就像 *ideas* 自己撑起一整个 NP 一样。

动作和上一关完全一样,只是换了范畴:`nospec`、`nocomp`、`head`,这次种在 D 上。
"

/-- 为 *hers* 建一个完整的 DP。 -/
Statement : XSyntax.Utters .two .D "hers" := by
  Hint "还是老三步:`nospec` 把 DP 拆到 D′。"
  nospec
  Hint "`nocomp` 拆到中心语层 D⁰。"
  nocomp
  Hint "`D⁰` 到了,种词:`head \"hers\"`。"
  head "hers"

Conclusion "
范畴系统不止 N/V/A 这些实词——D 这样的虚词,一样是头,一样要走完整套投射。
以后你会看到,句法里几乎每一层结构,顶上坐的都可能是一个虚词。

下一关:D 不会总是孤零零站着。*my house* 里,*my* 要去**选择**一个名词短语
作为搭档——这就是补足语和选择关系,句法里最重要的机制之一。
"
