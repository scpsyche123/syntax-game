# Handoff: 词库许可进构造子 + 词汇表进已知条件(方案 B)

- Agent: 小红(Claude Code 主窗口)
- Date: 2026-07-08
- Commit: `b136857`(rebase 到小绿的 `6a0b583` 之上)
- 施工单: `~/.claude/plans/cozy-stirring-kettle.md`(维护者已批)

## 做了什么

补齐 Church 三连的第三条(几何 / 选择 / **词性**):

- **`Tree.lean`**:新增 `inductive Lexicon : Pos → String → Prop`(**空**,无构造子);
  `word` 构造子改为 `(e : LexicalEntry c) → Lexicon c e.word → XTree .zero c`。
  `Lexicon` 空 = 空上下文造不出词树 = 全局纯净;词性事实由关卡当假设发。
- **`Operations.lean`**:`Head`/`yield`/`plot` 的 `.word` 分支加 `_` 丢许可。
- **`Tactics.lean`**:内部件 `lexicon!`(`license!` 的孪生)从**本关假设**取 `Lexicon`
  许可,报错语言学化(错范畴 / 不在词库)。`head` 归一 `∅`→`""`、走 `by lexicon!`。
  删全局 `checkVocab`。`Utters` → **`Parses`**(单一事实源)。**读目标处一律
  `consumeMData`**(见下「值钱的坑」)。
- **`Display.lean`**:`delabLexicon` 把 `Lexicon .N "cat"` 渲染成 `N ： "cat"`(空头 `∅`);
  `xTreeLabel?` 用真短语记法 token,去掉 `«DP»` 书名号(顺办 #13 的一半)。
- **`Vocabulary.lean`**:删除(门禁角色移到构造子 + `lexicon!`)。
- **12 关**:每关 Statement 加本关词的 `Lexicon` 假设 binder(= 玩家看到的「本关词汇表」),
  目标 `Parses`。空头关加 `Lexicon .C ""` 等。
- **`Playground.lean`**:全局纯净后闭合树造不出,加**本文件私有** `devLexicon` 公理 +
  `assumeEnglish` 战术喂词库,保住 `#eval`。游戏与理论核心都不 import 它,纯净不外泄。

## 和小绿 TreeView 的集成

施工单假设「我先落、小绿再 rebase」,但小绿的 `6a0b583`(活树标记,**关卡里默认
`set_option XSyntax.treeView.enabled false`**)已先进 main。故反过来:我把自己 rebase 到
`6a0b583` 上,手工合并 `Tactics.lean`(12 关自动合)。小绿的 tree-view 事件记录**全部保留**,
只把它引用的旧名 `Utters`/`asUtters?`/`closeUtters` 跟着改成 `Parses`/`asParses?`/`closeParses`,
`installSplitLink` 的 `Utters` 判断也改 `Parses`。TreeView 仍默认关闭。

## 值钱的坑(务必记住)

**目标类型被 `mdata` 包裹**:`have`,以及 **lean4game 自动 intro 关卡假设 binder**,会给
目标类型套一层 `Expr.mdata`,`getAppFn` 返回包裹层,`isConstOf ``XTree``/``Parses`` 全部
失配 → tactic 报「不是句法位置」。**一挂 `Lexicon` 假设 binder,不 `consumeMData` 每关开局
就崩。** 已在所有读目标处修(`goalType` 等)。这是本次最隐蔽的 bug,调了半天用探针才逮到
(probe 显示 `have` 后 headConst 从 `XTree` 变 `mdata`/`NP`)。

## 验证(静态,已过)

- `lake build` 全绿,无 `No world introducing` 门禁警告,12 关样板解全过。
- 错范畴 `head "cat"`(D 位)→「"cat" 在这一关的词库里是 N,不能作 D」。
- 表外词 → 「不在这一关的词库里」。空头 `head ""` 与 `head "∅"` 都过。
- 全局纯净:空上下文 `head "cat"` 造不出。
- 显示:`cat : N ： "cat"`、`C ： "∅"`、目标 `NP ： "cat"`(无 `«»`)。

## 未做 / 待办

- **实机试玩(地雷 8)**:假设区在网页里长什么样、词汇表排布好不好看,只有公网实机能验。
  维护者请以玩家身份走前几关确认,再定 delab 措辞。
- 显示可调:假设名=词,读作 `house : N ： "house"`(词重复一次);要更干净可改 `house : N`。
- #13 的另一半(目标改 `"my house" : DP` 字符串在前 + ASCII 冒号)没做,有解析风险,留排版任务。
- #14(L05 证伪关真实词显示)独立立项,未动。
- stage-2「玩家自己定义词性」= 后续「词库世界」;需 `define` 战术铸 `Lexicon` 假设,
  铸造口一开全局纯净就破,机制待单独定夺。
