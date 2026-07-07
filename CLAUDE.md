# Syntax Game — 项目上下文

用 Lean 4 形式化 X-bar 句法理论,并做成 lean4game 教学游戏,公开部署于
https://adam.math.hhu.de/#/g/scpsyche123/syntax-game
维护者是理论句法研究者(生成语法背景),Lean 熟练度:中级、在快速学习中。

## 目录地图

- `XSyntax/` — 理论库(游戏无关,也用于 VS Code 投屏走稿)
  - `Basic.lean` — `Pos`(九范畴)、`StrAdd`、参数化 `LexicalEntry (c : Pos)`
  - `Tree.lean` — `Bar` 索引、`Selects`(许可表,inductive Prop)、
    `XTree : Bar → Pos → Type`(双索引族;`compl` 携带 `Selects c d` 许可证)
  - `Operations.lean` — `cat`/`bar`(O(1) 投影)、`Head`/`yield`/`plot`
  - `TypeNotation.lean` — 27 条短语类型记法(`NP`/`N′`/`N⁰`…)+ 9 条裸范畴
    显示记法(`D` = `Pos.D`)。注意:这些是**全局保留 token**,见「地雷」。
  - `Tactics.lean` — 玩家指令集(elab):`nospec nocomp head complement
    adjoinL adjoinR specifier`;内部件 `license!`(选择违规的语言学化报错)
  - `Playground.lean` — VS Code 走稿 + 回归钉(`#guard`)
- `Game/` — lean4game 关卡层
  - `Metadata.lean` — TacticDoc ×7 + DefinitionDoc ×9(短语类型词汇)
  - `Levels/XBar/L01–L05` — 五关:中心语→空洞投射→补足语与选择→附加语→colorless 全句
- 基建文件(lakefile、lean-toolchain、.github/workflows)来自 GameSkeleton 模板,
  **lean-toolchain 钉死 v4.23.0,不要改**(与 GameServer 依赖配套)。

## 架构不变量(改动前必读)

1. **玩家视野里只有语言学。** parse 侧(玩家输入)、print 侧(目标面板)、
   error 侧(报错)三个方向都必须说语言学,不说 Lean。任何新功能按此验收。
2. **Church 式:不合法结构不可表达。** 几何违规由 Bar/Pos 索引拦截;
   选择违规由 `Selects` 许可证拦截(无居民 = 不合语法)。
3. **选择在合并处检查**(对应理论中 subcategorization 在 Merge 时满足):
   `complement` 内嵌 `(by license!)` 当场求值,没有事后的 license 步骤。
4. **玩家词汇表固定七条**,全部对应 X-bar 规则;`tree`/`pronounce` 已废除。
5. 空头 = `head ""`(发音为空的普通词条),不设独立构造子。
6. 诊断分层靠「不 catch」:外层 elab 预检层级/宣告,内层 `license!` 的
   异常原文上浮,互不吞话。

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

## 当前头号任务:无(上一个已完成)

`Display.lean`(print 侧翻译层)已落地并验证:`XSyntax/Display.lean` 提供
`@[delab app.XSyntax.XTree]`,表达式层检查两个索引(`isConstOf`),
免疫地雷 3。`Tactics.lean` 的 `Utters` 目标(见下方)复用同一套映射显示。
下一项头号任务待维护者从「挂账中的债务」里挑选后在此更新。

## 挂账中的债务(未排期,动工前先与维护者讨论)

- 词库门禁:`head` 不查词库,任何词可在任何 X⁰ 落地("sleeps" 可当名词)。
  修复需把 `Lexicon` 引入构造侧,是设计决定,勿擅动。
- `Selects` 是范畴粒度:拦 *the sleeps*,不拦 *sleep the cat*(不及物性
  是词项特征)。债主:LexicalEntry 上的 feature 系统。
- X′ 出现在宣告位时的报错来自门禁("not available"),措辞不语言学;
  理想归宿是 `checkDeclaredXP` 的 "must be a full phrase"。
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
  窗口昵称**小红**。未知来源不要补编昵称,写"another AI window, nickname
  unknown"即可。
- **多 AI/多窗口并行工作**:完整流程见 `docs/WORKFLOW.md`。核心规则——
  按「文件所有权」而非「主题」划分并行单位(教学设计和技术修复常常
  碰同一批关卡文件,不能假设主题不重叠就能并行);只有一个主窗口
  负责最终 `git status`/`lake build`/commit/push/看 CI,其余窗口不
  直接 push;每个窗口收尾写 `docs/HANDOFF-*.md`,只有长期有效的事实
  才提炼进本文件。

## 会话交接记录

- `docs/HANDOFF-2026-07-07.md` 汇总了 2026-07-07 的跨窗口工作记录:
  已落地修复、教学设计诊断、部署自动化、definitions 面板事故、以及剩余债务。
