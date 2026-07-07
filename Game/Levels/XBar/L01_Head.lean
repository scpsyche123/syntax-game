import Game.Metadata

World "XBar"
Level 1

Title "词与中心语"

Introduction "
每棵句法树都从词开始。词从词库进入句法,站上的第一个位置叫**中心语**(head),记作 X⁰。

目标面板上显示 `N⁰`:一个等待被填充的**名词性中心语位置**。

把词种进去:输入 `head \"ideas\"`。
"

/-- 为词 *ideas* 建一个名词中心语 N⁰。 -/
Statement : XSyntax.Utters .zero .N "ideas" := by
  Hint "输入 `head \"ideas\"`(引号是指令的一部分)。"
  head "ideas"

Conclusion "
第一棵(最小的)树建成。

注意:`head` 只能在 X⁰ 位置种词。如果目标是 N′ 或 NP,它会拒绝你——下一关见。
"

NewTactic head
