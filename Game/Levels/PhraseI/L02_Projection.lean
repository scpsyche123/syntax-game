import Game.Metadata

World "PhraseI"
Level 2

Title "空洞投射:从词到短语"

Introduction "
这一关的目标是 `NP`——一个完整的名词短语。但你手里的指令 `head` 只会在 X⁰ 上工作。

X-bar 理论的主张:词不能直接当短语用。哪怕短语里只有一个词,
它也必须走完投射的全程:X⁰ → X′ → XP。每一层都是真实的结构。

两条新规则:

- `nospec` —— XP → X′(这个短语没有 specifier)
- `nocomp` —— X′ → X⁰(这个中心语没有补足语)

自上而下拆解:先 `nospec` 把 NP 拆到 N′,再 `nocomp` 拆到 N⁰,最后 `head`。

(不信的话,可以先直接试 `head \"ideas\"`,读一读系统怎么拒绝你。)
"

/-- 为 *ideas* 建一个完整的 NP。 -/
Statement : XSyntax.Utters .two .N "ideas" := by
  Hint "从 `nospec` 开始:XP 先拆成 X′。"
  nospec
  Hint "现在目标是 `N′`。用 `nocomp` 拆到中心语层。"
  nocomp
  Hint "`N⁰` 到了,种词:`head \"ideas\"`。"
  head "ideas"

Conclusion "
三步,三层。你刚才亲手执行了教科书上写作 NP → N′ → N⁰ 的那条投射线。

学生画树时最常见的错误,就是把这两层直接跳过——在这个系统里,跳层根本无法输入。

你已经会搭 N 的三层了。下一关我们不换动作,换范畴:除了名词、动词、形容词这些
**实词**,句法里还有一类**虚词**(功能词)——比如限定词 *the*/*my*。虚词也有
自己的三层投射,规则完全一样。
"

NewTactic nospec nocomp
