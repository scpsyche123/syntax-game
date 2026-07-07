import Game.Metadata

World "XBar"
Level 5

Title "Colorless green ideas sleep furiously"

Introduction "
终关:Chomsky 1957 年那句著名的话——语义荒谬,句法完美。
你要为整句建一棵 CP,证明它**合语法**。

三样新东西:

- `specifier XP`:短语带 specifier 时用它封顶(主语住在 TP 的 specifier 里)
- `adjoinR XP`:右附接(*furiously* 挂在 V′ 右侧)
- **空头**:C、D、T 三个功能中心语在这句里都不发音,用 `head \"\"` 种下——
  看不见,但结构上在。

整句的骨架:CP ⟶ C⁰ + TP;TP ⟶ 主语DP + T′;T′ ⟶ T⁰ + VP。
自上而下,一层一层来。
"

/-- 为 *Colorless green ideas sleep furiously* 建一棵完整的 CP。 -/
Statement : CP := by
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

这就是整个项目的论点浓缩成一关:**合语法性 = 存在一棵树**。
你刚才不是画了一张图,而是构造了一个被类型系统全程审查过的证据。

(顺带:你全程没有写一行 Lean——七条指令全部是 X-bar 规则本身。)
"

NewTactic specifier adjoinR
