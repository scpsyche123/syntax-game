# Syntax Game — v1 现状总结

> 快照:`main` @ `34c8630`(线上部署版)。本文汇总当前**已上线**的 v1 全貌——
> 概念、工程架构、关卡、机制、不变量、地雷、以及诚实的短板评估——供下一步方向
> 讨论与新窗口交接使用。不含尚未合并的在途工作(见末节)。

---

## 0. 一句话与定位

用 Lean 4 形式化 X-bar 句法理论,做成 lean4game 教学关卡。核心论点:

> **合语法 = 存在一棵树;不合语法 = 造不出树(Church 式:不合法结构不可表达)。**

维护者是理论句法研究者(生成语法背景),Lean 中级。公开部署:
`https://adam.math.hhu.de/#/g/scpsyche123/syntax-game`。

**受众目前未明确定义**——这是 v1 的一个悬而未决的战略问题(见 §10)。

---

## 1. 仓库布局与技术栈

- **`XSyntax/`** — 理论库(游戏无关,也用于 VS Code 投屏走稿)。
- **`Game/`** — lean4game 关卡层(Metadata + 两个 World 的 12 关)。
- **`Game.lean`** — 游戏根:导入两个 World、Title/Introduction/Info、`MakeGame`。
- **基建**:`lakefile.lean`、`lean-toolchain`(钉死 `leanprover/lean4:v4.23.0`,与
  GameServer 依赖配套,**不要改**)、`.github/workflows/`(CI)。来自 GameSkeleton 模板。
- **依赖**:`GameServer`(hhu-adam/lean4game)、batteries、Cli、i18n、importGraph。
  `.lake/packages` ~126MB,已就位;此机器在国内,大文件下载易断,**勿轻易
  `rm -rf .lake` 或改依赖版本触发重下**。
- **lakefile 关键点**:`@[default_target]` 只附着紧随其后的声明,故 `lean_lib XSyntax`
  必须在 `@[default_target] lean_lib Game` **之前**(插错会导致 gamedata 不生成、
  云端 404)。

---

## 2. 理论库(`XSyntax/`)逐文件

### `Basic.lean`
- `Pos`:9 个句法范畴 `N V A P Adv T D C Conj`(`deriving Repr, DecidableEq`)。
- `PlotPos` / `PlotPosSpecialFont`:范畴的普通/小型大写渲染。
- `StrAdd`:空格感知拼接(空操作数不产生多余空格)——`yield` 用它。
- `LexicalEntry (c : Pos)`:范畴是**类型参数**不是字段(`LexicalEntry .D` 与
  `LexicalEntry .V` 是不同类型;范畴不匹配在词库层就死)。

### `Tree.lean`(类型层,Church 式两次)
- `Bar`:`zero | one | two`(bar 层作为索引值)。
- `Selects : Pos → Pos → Prop`——**许可表**,5 条构造子:
  `DN`(D→N)、`TV`(T→V)、`CT`(C→T)、`PD`(P→D)、`VD`(V→D)。
  表里没有的搭配(如 `Selects .D .V`)**无居民** = 不合语法。
- `XTree : Bar → Pos → Type`——双索引族,7 个构造子:
  - `word : LexicalEntry c → XTree .zero c`
  - `bareX0 : XTree .zero c → XTree .one c`(X⁰→X′,无补足语)
  - `bareX1 : XTree .one c → XTree .two c`(X′→XP,无 specifier)
  - `compl : XTree .zero c → XTree .two d → Selects c d → XTree .one c`
    (**携带 `Selects c d` 证据**——无许可 = 造不出)
  - `adjunctL : XTree .two d → XTree .one c → XTree .one c`(左附接,层级不变)
  - `adjunctR : XTree .one c → XTree .two d → XTree .one c`(右附接)
  - `Spec : XTree .two d → XTree .one c → XTree .two c`(specifier 封顶)
- **几何违规由 Bar/Pos 索引拦截;选择违规由 `Selects` 无居民拦截。**

### `Operations.lean`
- `cat` / `bar`:O(1) 投影(从类型索引读出,非递归)。
- `Head : XTree b c → LexicalEntry c`——返回类型即**内心性定理**(头的范畴=树的范畴)。
- `yield : XTree b c → String`——表层字符串(用 `StrAdd` 递归拼)。
- `plot : XTree b c → String`——带标签括号,如 `[ᴅᴘ my [ɴᴘ [ᴀᴘ big] house]]`
  (**已实现但尚未进游戏面板**——见 §10 可视化)。

### `TypeNotation.lean`
- Group 1:27 条短语记法(`NP`/`N′`/`N⁰` … 3 bar × 9 范畴 → `XTree ...`)。
- Group 2:9 条裸范畴显示(`D` = `Pos.D`,让 `Selects` 目标显示成 `Selects D N`)。
- ⚠ 这些是**全局保留 token**:命令里当标识符用要穿法式引号(`NewDefinition «NP»`)。

### `Display.lean`
- `@[delab app.XSyntax.XTree]` delaborator:表达式层查两个索引是否具体常量
  (`isConstOf`),产出 `NP`/`D′` 等语言学记法。**表达式层检查免疫**"notation 反美化器
  被 Group 2 改写干扰"的地雷。
- 已知小瑕疵:标签用 `mkIdent`,而 `DP` 是保留 token → 渲染成 `«DP»`(带书名号)。

### `Tactics.lean`(玩家指令 + 校验机制)—— 见 §3。

### `Playground.lean`
- VS Code 走稿(5 幕)+ 回归钉(`#guard`)。开发用,不进游戏。

---

## 3. 玩家机制(`Tactics.lean`)

### 目标类型 `Utters b c s`
```
def Utters (b : Bar) (c : Pos) (s : String) : Type := { t : XTree b c // yield t = s }
```
关卡目标 = "念作 `s`、范畴 `c`、bar 层 `b` 的树"。玩家全程只用搭树指令;
`yield t = s` 的证明义务被藏在可见目标之外,搭完自动核验。

### 8 条玩家指令
七条 X-bar 规则各一条 + 一条证否:
`nospec`(XP→X′)、`nocomp`(X′→X⁰)、`head "w"`(种词,空头 `head ""`)、
`complement XP`(X′→X⁰+补足语,内嵌 `by license!` **当场查选择**)、
`adjoinL XP` / `adjoinR XP`(左/右附接)、`specifier XP`(XP→Spec+X′)、
`cannotSelect`(在 `¬ Selects c d` 目标上证明许可不存在——唯一的"证明"而非"搭树"关)。
`license!` 是内部件,不是玩家词汇。

### 切分与显示(当前实现:**启发式**)
`complement`/`adjoinL`/`adjoinR`/`specifier` 会把父串按启发式(限定词表、
谓词/助动词白名单、左右附接默认切一词)**预先切好**分给子目标,面板显示
`«D⁰» ： "my"`、`«NP» ： "house"`。

### 错误反馈(当前:分层"不 catch")
- 错 bar 层、错范畴(`license!`)、错词(head 与目标不符)、多词头——**当场拒**,
  语言学化中文报错。
- 整句 yield 最后由组合证明核验。
- **局限**:结构/切分若前期就错,可能到深处才暴露(启发式预切也带**剧透**——
  见 §10)。这正是在途工作要解决的(§11)。

---

## 4. 关卡(12 关,两个 World)

> lean4game 要求每个 World 内 Level 从 1 连续编号;World id 必须**无空格**
> (曾用 `"Phrase I"` 导致线上 404,已改 `PhraseI`/`PhraseII`,显示名在 `Title`)。

### World `PhraseI` — 短语内部(8 关)
| # | 文件 | 目标句 | 新概念 | 步数 |
|---|---|---|---|---|
| 1 | L01_Head | *ideas* (N⁰) | 词=中心语 | 1 |
| 2 | L02_Projection | *ideas* (NP) | X⁰→X′→XP 三层 | 3 |
| 3 | L03_Determiner | *hers* (DP) | D 是范畴(功能词也是头) | 3 |
| 4 | L04_Complement | *sees the cat* (VP) | complement、及物动词、选择限制 | 9 |
| 5 | L05_Refutation | `¬ Selects .D .V` | 证伪(cannotSelect),必经 | 1 |
| 6 | L06_Adjunct | *my big house* (DP) | adjoinL、补足语 vs 附加语 | 10 |
| 7 | L07_YouDecide | *the strange dog* (DP) | 去提示自主判断(**与 L06 同构,是缺陷**) | 10 |
| 8 | L08_RightAdjunct | *sleep quickly* (VP) | adjoinR、副词 | 6 |

### World `PhraseII` — 小句结构(4 关)
| # | 文件 | 目标句 | 新概念 | 步数 |
|---|---|---|---|---|
| 1 | L01_Tense | *cats will sleep* (TP) | 时态头 T、specifier、主语在 Spec,TP | 9 |
| 2 | L02_Complementizer | *cats sleep* (CP) | 标句头 C、空 C + 空 T、三种沉默 | 12 |
| 3 | L03_Transfer | *the big dog sees the cat* (CP) | 无提示组装(**方法论有问题,见 §10**) | ~24 |
| 4 | L04_Colorless | *Colorless green ideas sleep furiously* (CP) | 招牌终关:合语法但无意义 | ~30 |

`Game/Metadata.lean`:7+1 条 TacticDoc、9 条 DefinitionDoc(短语类型词汇,注册键
用 `«NPDef»` 等**与门禁 token 岔开**,否则 `NewHiddenTactic «NP»` 会连累词汇面板
被隐藏——曾发生)。

---

## 5. 构建・验证・部署流水线

- 本地:`lake build`(裸,default target = Game)。
  **本地神谕**:出现 `No world introducing X` warning = 玩家会用的道具 X 没注册,
  游戏内会被门禁拦(需 `NewDefinition`/`NewHiddenTactic`)。warning 清零 = 放行。
- **CI 全自动**(`.github/workflows/build.yml`):push 到 main → GitHub Actions 构建 →
  `curl` 触发 `adam.math.hhu.de/import/trigger/...` → 轮询 `game.json` 至有效。
  **CI 绿 = 游戏已真的更新在线**(不只是编译过)。
- 游戏 Info 面板**盖部署 commit 短哈希 + UTC 时间**戳(CI 构建前 sed 注入),
  可对 `git log -1` 核实是否最新版。
- 远程走 **SSH**(`git@github.com:...`),不再弹账号选择框,也绕开 HTTPS 连接重置。

---

## 6. 架构不变量(改动前必读,源自 CLAUDE.md)

1. **玩家视野里只有语言学**:parse/print/error 三侧都说语言学,不说 Lean。
2. **Church 式:不合法结构不可表达**(几何违规靠 Bar/Pos 索引;选择违规靠 `Selects` 无居民)。
3. **选择在合并处检查**:`complement` 内嵌 `(by license!)` 当场求值,无事后 license 步。
4. **玩家词汇固定**(7 条 X-bar 规则 + `cannotSelect`);`tree`/`pronounce` 已废除。
5. **空头 = `head ""`**(发音为空的普通词条),不设独立构造子。
6. **诊断分层靠"不 catch"**:外层 elab 预检层级/宣告,内层 `license!` 异常原文上浮。
7. **`Utters` 会把目标串分配给子目标**,让玩家看到 `D⁰ ： "my"` 这类"片段+词性"目标
   (当前是启发式,见 §10/§11)。

---

## 7. 已知地雷(源自 CLAUDE.md)

1. **记法 token 碰撞**:`NP`/`D` 是保留字,命令里当标识符要穿 `«»`。
2. **`@[default_target]` 只附着下一条声明**:`lean_lib XSyntax` 必须在 Game 之前。
3. **notation 反美化器失效**:已由 `Display.lean` 表达式层 delab 修复。
4. `.history/` 是 VS Code 快照,已 gitignore。
5. **GameServer 无独立可执行文件;Windows 本地起不了 lean4game 前端**(`/bin/bash` 崩)——
   本地只能 VS Code + Playground,交互体验只能靠公网部署版。
6. LF/CRLF warning 是 Windows 例行噪音,无视。
7. **World 名必须无空格**(会进 URL/websocket/文件路径;带空格线上 404)。
8. **静态验证 ≠ 交互可玩**:`lake build`/CI/`game.json` 只证明静态数据;目标加载、
   指令执行、报错渲染只有**实机试玩**能验(Windows 起不了前端)。改关卡/tactic/delaborator
   后必须提示维护者实机试玩,别把"CI 绿"当"能玩"。

---

## 8. 什么是真·Lean 独有,什么只是皮

- **已是骨头**:①不合法结构**不可表达**(类型系统,非事后检查);②`cannotSelect` =
  证明"许可证不存在"(¬∃ 的雏形,Python 说都说不出这句话)。
- **还只是皮**:其余 11 关都是"搭树 = 执行",Python 用带类型 AST + 检查器也能做。
  歧义(`∃ t₁ t₂, t₁ ≠ t₂ ∧ yield 相同`)、否定(¬∃)、组合性语义——这些 Lean 独有的
  **定理形态**尚未出现。
- 真正的 Lean 优势是**"证明,而非测试"**:合语法=造证据,不合法=证否。NNG 那类
  好玩的定理关"不是用不上,是还没走到"。

---

## 9. 教学法与语言学短板(下一步方向的靶子)

1. **教执行,不教判断**:每关玩家都知道该搭什么,只是把已知树敲进去=抄写,不是学习。
   缺歧义关、判断关(先猜后验)、反例预测关(哪一步会死)、最小对立对
   (*proud of him* 补足 vs *proud man* 附接)。L07 本该是判断关却与 L06 同构。
2. **DP 假说被静默烘焙**:争议性分析当默认,连"这是理论选择"都没声明——违背项目
   "理论承诺要显式、可审计"的立项哲学。
3. **无移位 → 小句层不诚实**:*sees* 的 `-s` 实为 T(V-to-T / affix hopping);TP/CP
   全靠空头糊过去。**短语内部诚实,小句层不诚实**——这是范围问题,不是选词问题。
4. **无树可视化**:目标面板是文本,树靠脑补——对句法教学是硬伤(树就是这门学科的
   表征)。`plot` 的标签括号已实现但没进游戏。可选升级:文本档(括号进反馈)/
   框架档(Introduction 塞静态树图)/ 越狱档(ProofWidgets HTML widget——但
   **lean4game 前端是否放行 widget 需调研**)。
5. **受众未定**:在"教零基础"与"只有 syntax-literate 能欣赏"之间拧巴;"没人愿意主动玩"
   多半源于此。真正能赢的受众可能是**已懂些句法、想把手画树变成机器审查的精确对象**的人。
6. **小瑕疵**:`head ""` 回车键常卡在引号中间(既插换行又提交,导致这行过不了);
   目标显示 `«DP»` 有书名号、类目在前(维护者想要 `"my house" : DP`)。

---

## 10. 挂账中的技术债(源自 CLAUDE.md,未排期)

- **词库门禁**:`head` 不查词库,任何词可落在任何 X⁰("sleeps" 可当名词)。修复需把
  `Lexicon` 引到构造侧,是设计决定。
- **`Selects` 是范畴粒度**:拦 *the sleeps*,不拦 *sleep the cat*(不及物性是词项特征)。
- **X′ 出现在宣告位的报错来自门禁**("not available"),措辞不语言学。
- **切分的"承诺驱动"重构**(思想已验证,实现待定):当前启发式预切既**剧透**又只服务
  少数句型;替代思想见 `docs/HANDOFF-2026-07-07-commitment-segmentation.md`(小蓝)——
  子目标开成未定、玩家种下参照子树后用**残量减法**(编译 meta 代码,不进类型索引)
  算兄弟目标。**这是解决 §9.1"教判断"的技术前提**(玩家自己定切分才能有判断关)。
- i18n 双语(`.i18n/en/Game.pot` 已生成)、README 仍是模板原文。

---

## 11. 在途未提交工作(已暂停,等定方向)

隔离 worktree `.claude/worktrees/xiaohong-feedback-fixes`(分支
`worktree-xiaohong-feedback-fixes`,**未合并、未上线**)做了一半,针对维护者试玩反馈:
- 移植小蓝的**残量切分**(玩家自己定切分、不剧透)替换启发式;
- 加**即时反馈**(错词/错构在提交那一刻就拦,不留下游);
- `cannotSelect` → `CannotSelect` 改名;
- 显示改 `"my house" : DP`、去 `«»`;
- 证伪关目标用真实词显示。

当前卡在一个**空头 bug**(即时前缀检查误拦 `head ""`,一行可修:`r == ""` 视为合法),
按"先讨论方向"的要求停着。

---

## 12. 协作与工作流(多 AI/多窗口)

- 完整规则见 `docs/WORKFLOW.md`。核心:按**文件所有权**(非主题)划分并行;
  只有**一个主窗口**负责 `git status`/`lake build`/commit/push/看 CI,其余窗口不直接 push;
  每窗口收尾写 `docs/HANDOFF-*.md`,只有长期事实才提炼进 CLAUDE.md。
- **AI 昵称登记**:Codex 窗口 = **小绿**;Claude Code 主窗口 = **小红**;Claude Code
  侧窗口(worktree `xiaolan`,分支 `agent/xiaolan`)= **小蓝**。
- 相关 handoff:`HANDOFF-2026-07-07.md`(综述)、`-target-spans.md`(小绿,启发式显示)、
  `-commitment-segmentation.md`(小蓝,残量思想 + 元编程避坑)、`-level-redesign.md`(小红,12 关重设计)、`-xiaolan-setup.md`。

---

## 13. 一句话总判断

v1 是**能跑、能通关、已上线的骨架**:X-bar 短语结构 + 选择许可 + Church 式不可表达 +
一条证否关,工程流水线(自动部署、版本戳、SSH)成熟。但它**教执行不教判断、
把争议性理论静默烘焙、小句层因无移位而不诚实、没有树可视化、且尚未兑现任何
Lean 独有的定理乐趣**。方向未错,但离"有人愿意主动玩"隔着整个游戏设计的距离。
下一步最高杠杆的单点:**先做一个歧义关**(`∃ t₁ t₂ …`)——它同时治"教判断"、
证明 Lean 独有性、给出第一个真正好玩的关。
