# Syntax Game — 项目上下文

用 Lean 4 形式化 X-bar 句法理论,并做成 lean4game 教学游戏,公开部署于
https://adam.math.hhu.de/#/g/scpsyche123/syntax-game
维护者是理论句法研究者(生成语法背景),Lean 熟练度:中级、在快速学习中。

## 目录地图

- `XSyntax/` — 理论库(游戏无关,也用于 VS Code 投屏走稿)
  - `Basic.lean` — `Pos`(九范畴)、`StrAdd`、参数化 `LexicalEntry (c : Pos)`
  - `Tree.lean` — `Bar` 索引、`Selects`(选择许可表,inductive Prop)、
    `Lexicon : Pos → String → Prop`(词库许可,**空 inductive**;词性事实由关卡当
    假设发)、`XTree : Bar → Pos → Type`(双索引族;`compl` 携带 `Selects c d`、
    `word` 携带 `Lexicon c e.word` 许可证)
  - `Operations.lean` — `cat`/`bar`(O(1) 投影)、`Head`/`yield`/`plot`
  - `TypeNotation.lean` — 27 条短语类型记法(`NP`/`N′`/`N⁰`…)+ 9 条裸范畴
    显示记法(`D` = `Pos.D`)。注意:这些是**全局保留 token**,见「地雷」。
  - `Tactics.lean` — 玩家指令集(elab):`nospec nocomp head complement
    adjoinL adjoinR specifier`;内部件 `license!`(选择违规报错)、`lexicon!`
    (词性违规报错,从关卡假设取证);关卡目标类型 `Parses`(旧名 `Utters`,已改)
  - `Display.lean` — print 侧翻译层:`delabParses`/`delabXTree`(短语记法 token,
    去 `«»`)、`delabLexicon`(`Lexicon .N "cat"` → `N ： "cat"`,空头 `∅`)
  - `TreeView.lean` — 小绿的活树状态标记(`register_option
    XSyntax.treeView.enabled`,**关卡里默认 false**;需前端 fork 才渲染 SVG)
  - `Playground.lean` — VS Code 走稿;因全局纯净,用**本文件私有** dev 公理
    `devLexicon` + `assumeEnglish` 战术喂词库,保住闭合 `#eval`(游戏与理论核心都不 import)
- `Game/` — lean4game 关卡层
  - `Metadata.lean` — TacticDoc ×7 + DefinitionDoc ×9(短语类型词汇)
  - `Levels/XBar/L01–L05` — 五关:中心语→空洞投射→补足语与选择→附加语→colorless 全句
- 基建文件(lakefile、lean-toolchain、.github/workflows)来自 GameSkeleton 模板,
  **lean-toolchain 钉死 v4.23.0,不要改**(与 GameServer 依赖配套)。

## 架构不变量(改动前必读)

1. **玩家视野里只有语言学。** parse 侧(玩家输入)、print 侧(目标面板)、
   error 侧(报错)三个方向都必须说语言学,不说 Lean。任何新功能按此验收。
2. **Church 式:不合法结构不可表达(三连)。** 几何违规由 Bar/Pos 索引拦截;
   选择违规由 `Selects` 许可证拦截(无居民 = 不合语法);**词性违规由 `Lexicon`
   许可证拦截**。区别:`Selects` 是普遍语法(写死构造子),`Lexicon` 是个别语言的
   (空 inductive,词性事实由每关当**已知条件**发给玩家)。故空上下文里造不出任何
   词树 = 语法性永远相对于给定词库,`head` 用 `lexicon!` 从关卡假设取许可。
3. **选择在合并处检查**(对应理论中 subcategorization 在 Merge 时满足):
   `complement` 内嵌 `(by license!)` 当场求值,没有事后的 license 步骤。
4. **玩家词汇表固定七条**,全部对应 X-bar 规则;`tree`/`pronounce` 已废除。
5. 空头 = `head ""` 或 `head "∅"`(都归一成空串),不设独立构造子;许可来自
   关卡发的 `Lexicon .C ""`/`.T ""`/`.D ""`(显示成 `∅`)。
6. 诊断分层靠「不 catch」:外层 elab 预检层级/宣告,内层 `license!` 的
   异常原文上浮,互不吞话。
7. `Parses` 目标(旧名 `Utters`)不只核验整句 yield,也会把目标字符串分配给子目标,
   让玩家看到 `D⁰ ： "my"`、`NP ： "house"` 这类「片段 + 词性」目标。关卡把本关
   词库当 `Lexicon` 假设 binder 发下来,玩家在假设区看到 `my : D ： "my"` 这排词汇。

## 构建・验证・部署流水线

- 本地:`lake build`(裸的,default target 必须是 Game)。
  **本地神谕**:若出现 `No world introducing X, but required by XBar` warning,
  说明玩家会用到的道具 X 未注册,游戏内会被门禁拦截
  ("The tactic 'X' is not available in this game!")。
  修法:在关卡文件加 `NewDefinition «X»`(见地雷 1)+ Metadata 里配 DefinitionDoc。
  warning 清零 = 门禁放行。
- 部署:`git push` → GitHub Actions 自动构建(等绿)→ 浏览器访问
  `https://adam.math.hhu.de/import/trigger/scpsyche123/syntax-game` → 验证
  `https://adam.math.hhu.de/data/g/scpsyche123/syntax-game/game.json` 吐 JSON
  → 刷新游戏页。
- 网络注意:此机器在国内,大文件下载易断;依赖已全部就位,勿轻易
  `rm -rf .lake` 或改动依赖版本触发重新下载。

## 已知地雷

1. **记法 token 碰撞**:`NP`、`D` 等已被 notation 注册为全局保留字,
   在命令里当标识符用必须穿法式引号:`NewDefinition «NP»`、`DefinitionDoc «NP» as "NP"`。
2. **`@[default_target]` 只附着紧随其后的那一条声明**。lakefile 中
   `lean_lib XSyntax` 必须在它之前;插错位置会导致 Game 不编译、
   gamedata 不生成、云端部署 404(已发生过一次)。
3. **notation 的反美化器失效**:Group 2 记法先把 `Pos.D` 改写成 `D`,
   导致 Group 1 的语法层模式(期待原始 `Pos.D`)匹配失败,目标面板
   显示裸类型 `XSyntax.XTree XSyntax.Bar.one D`。已修复,见
   `XSyntax/Display.lean`(表达式层 `@[delab app.XSyntax.XTree]`,
   `isConstOf` 检查免疫此地雷)。
4. `.history/` 是 VS Code 插件的本地快照,已加 .gitignore,勿入库。
5. GameServer 包无独立可执行文件(文档中的 gameserver exe 描述已过时,
   由 relay 直接驱动);Windows 本地起 lean4game 前端会因 `/bin/bash` 崩溃,
   本地开发只用 VS Code + Playground,联网体验用公网部署版。
6. LF/CRLF warning 是 Windows 例行噪音,无视。
7. **World 名(`World "…"`)必须无空格**。它不是显示串,而是标识符,会进
   URL / websocket 路径 / 服务器文件路径。带空格(曾命名 `"Phrase I"`)会让
   线上交互服务器 404、目标永远 loading 转圈。显示名放 `Title`,World id 用
   无空格 CamelCase(`PhraseI`)。
8. **静态验证 ≠ 交互可玩**:`lake build`、CI、`game.json` 只证明静态数据正确;
   目标面板加载、指令执行、报错渲染这些**交互对局**行为,只有真人在公网部署版
   里玩才能验(Windows 本地起不了前端,见地雷 5)。改动关卡/tactic/delaborator
   后,务必提示维护者实机试玩,别把"CI 绿"当成"能玩"。

9. **目标类型被 `mdata` 包裹**:`have`、以及 lean4game **自动 intro 关卡假设
   binder**,都会给目标类型套一层 `Expr.mdata`,使 `getAppFn` 返回包裹层、
   `isConstOf ``XTree``/``Parses`` 认不出 → tactic 报"不是句法位置"。**读目标处一律
   `consumeMData`**(`goalType`/`asXTree?`/`asParses?`/`closeParses`/`installSplitLink`
   已修)。关卡一旦带 `Lexicon` 假设 binder,这条是必修,否则每关开局就崩。

## 当前头号任务:无(上一个已完成)

`Display.lean`(print 侧翻译层)已落地并验证:`XSyntax/Display.lean` 提供
`@[delab app.XSyntax.XTree]`,表达式层检查两个索引(`isConstOf`),
免疫地雷 3。`Tactics.lean` 的 `Utters` 目标(见下方)复用同一套映射显示。
下一项头号任务待维护者从「挂账中的债务」里挑选后在此更新。

## 挂账中的债务(未排期,动工前先与维护者讨论)

- ~~词库门禁~~ **已完成(2026-07-08,方案 B)**:`Lexicon` 进构造子,`head` 用
  `lexicon!` 从关卡假设取证。stage-2「玩家自己定义词性」(需 `define` 战术当场铸
  `Lexicon` 假设)是后续「词库世界」的事——铸造口一开全局纯净就破,机制待单独定夺。
- `Selects` 是范畴粒度:拦 *the sleeps*,不拦 *sleep the cat*(不及物性
  是词项特征)。债主:LexicalEntry 上的 feature 系统。
- X′ 出现在宣告位时的报错来自门禁("not available"),措辞不语言学;
  理想归宿是 `checkDeclaredXP` 的 "must be a full phrase"。
- **切分的"承诺驱动"重构(思想已验证,实现待重做)**:目标面板给子目标
  预分配字符串是**剧透**——玩家该自己判断"my house"里哪部分是 D⁰、哪部分
  是 NP,不该被系统提前切好告诉他。旧实现更靠一套启发式(限定词表、谓词表
  `sleep/sees`、左右附接默认一词……),既剧透又只服务五关。
  已验证的替代思想:切分处子目标**开成未定目标**,不预算边界(面板显示裸
  `D⁰`/`NP`);玩家一旦种下参照子树(如 `head "my"`),才把"整串减去该子树
  yield"的**残量**赋给兄弟目标(→ `NP ： "house"`),错误作为后果在整句
  念不对时暴露,而非当场剧透。
  **关键实现洞见**(值钱的部分,重做时照搬):减法只在 tactic 的**编译 meta
  代码**里算、结果赋给普通元变量,**绝不进类型索引**——否则内核要归约
  `String.take`/`drop`,而字符串字面量在内核里对这些操作不归约(会卡死)。
  整句 yield 证明用 `mkEqRefl` 交**内核**验,别用 elaborator 的 `isDefEq`/
  `refl`(整句会炸;逐节 `simp` 之所以行是因为它只碰小片段)。
  另有几个 Lean 元编程地雷(`?_` 被后续 binder 捕获、tag 带 hygiene 需
  `eraseMacroScopes`、`Subtype.val ⟨tree, ?prf⟩` 让 `hasExprMVar` 误判、
  需按 mvar 类型 Prop/Type 判断树是否搭完)见
  `docs/HANDOFF-2026-07-07-commitment-segmentation.md`。
  注意:该 handoff 附带的 `agent/xiaolan` 分支实现(基于旧关卡结构)**已随
  结构改动过期**,重做时以本条思想为准、勿直接合并那份代码。
- i18n 双语(.i18n/en/Game.pot 已生成)、README.md 仍是模板原文。
- 体验债账本:维护者将以玩家身份重玩记录,分诊后逐条立项。

## 协作约定

- 维护者要求**每处改动都解释**:改了什么、为什么、机制是什么。
  宁可解释多,不可静默改。风格偏好:哲学/原理框架优先于实现细节。
- 报错一律要原文;修复前先给诊断。
- 改动玩家可见文本(关卡 Introduction/Hint/错误信息)属于教学设计,
  先提案再改;纯工程改动可先做后讲。
- commit message 用英文,风格:`fix:`/`feat:`/`chore:` 前缀。
- **AI 昵称记录**:每个 AI/窗口在工作记录(`docs/HANDOFF-*.md`)里必须写
  自己的昵称和来源。当前登记在案:Codex 窗口昵称**小绿**,Claude Code
  主窗口昵称**小红**,Claude Code 侧窗口(worktree:
  `.claude/worktrees/xiaolan`,分支 `agent/xiaolan`)昵称**小蓝**。未知来源
  不要补编昵称,写"another AI window, nickname unknown"即可。
- **多 AI/多窗口并行工作**:完整流程见 `docs/WORKFLOW.md`。核心规则——
  按「文件所有权」而非「主题」划分并行单位(教学设计和技术修复常常
  碰同一批关卡文件,不能假设主题不重叠就能并行);只有一个主窗口
  负责最终 `git status`/`lake build`/commit/push/看 CI,其余窗口不
  直接 push;每个窗口收尾写 `docs/HANDOFF-*.md`,只有长期有效的事实
  才提炼进本文件。

## 会话交接记录

- `docs/HANDOFF-2026-07-07.md` 汇总了 2026-07-07 的跨窗口工作记录:
  已落地修复、教学设计诊断、部署自动化、definitions 面板事故、以及剩余债务。
