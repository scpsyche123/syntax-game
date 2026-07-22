# Bare Grammar 基底 + CannotYield 垂直切片 — 报告

**分支** `bg-base-slice` · **昵称** 小蓝 · **日期** 2026-07-09
**施工单**:`claude-code-brief-bg-slice.md`(初版)+ 路线 A 重做裁决 + **v2 undergeneration spec 第一单**(`Syntax-Game-Undergeneration-Construction-Spec.md`,§2/§14.1/§17.1)
**lake build** 通过(v1 未动 63 jobs;`lake build BareSyntax` 7 jobs;无 `sorry`)

一句话结论:v2 把所有"无法生成"统一成 **expand/close/cut/reuse** 反驳演算;本单交**语义审计 + flat 层 + expand/close 首关(长度失配)**。旧的路线 A/B/C(下方 §0–§5)在 v2 里的位置:`deadYield` 退化为 `cut no_adv` 的后端,路线 B 是"裸反演"反面对照。神键禁令一脉延续到 v2:自动化只**核对**玩家申报,玩家负责**解释**。

---

## v2-A. 语义审计(spec §2 / §17.1)

**结论:当前基底是"递归槽位"语义,v2 需要"flat"。**

- 现状:`Basic.lean` 的 `Deriv.app` 输入是 `DerivList`(每个输入是**完整子推导** `Deriv`),所以 `N→D N` 的 N 槽能填**任意 N-子树**——包括另一条 `N→D N`。即 kernel 按**递归**解释,`linear₁` 生成无限语言 {D N, D D N, …}。
- spec §2.1 要 **flat**:每槽恰消耗**一个词**(lex),`N→D N` = "一个 lex D + 一个 lex N";`linear₁` = 有限模板集 `{[D,N], [D,A,N]}`,不是递归无限语言。
- 差在哪:递归语义下"模板窮舉/长度排除/逐模板 law preservation"都不可靠(N 槽可无限展开)。故 flat 必须**型别层显式分层**,否则后续 expand/close/cut 全踩空。
- 处置:递归 `Deriv` **不删**(它是 W3 的料,spec §2.2),另起 flat 层。

## v2-B. Flat 层设计(spec §2.3:方案 A vs B)

**选方案 A(拆分关系)**,代码 `BareSyntax/Flat.lean`:
- `FlatTemplate`(`result` + `slots : List Cat`,每槽一个词类)、`FlatGrammar`(Cat/词库/模板表)、`FlatLicensed`(= `words.length = slots.length ∧ ∀ 配对 ∈ 词库`)、`CanYieldFlat`(∃ 结果范畴对的模板被许可)。
- 与递归 `Deriv` **完全分开**,不共用含混 `Licensed`——正是 spec §2.3 的要求。

**为何 A 不 B**:方案 B(`Slot` 标 `lex`/`tree`)要在**同一** `Deriv` 里混两种槽语义,会把 flat 的"每槽一词"和递归的"每槽一子树"塞进一个构造子,`applyRule` 得按标签分叉——正是 spec 警告的"含混 `Licensed`"。A 把两套关系彻底隔开,flat 层的定理/tactic 不受递归拖累。**代价**:两套关系不共享引理,W2→W3 升级时 flat 结果要显式"抬"进 tree 层(spec §1.4 要的正是这种"升级不推翻"——A 下是加一层 refinement,可接受)。

**摩擦记录**:
- `List.Forall₂` 在本工具链不可用(非 Mathlib),`FlatLicensed` 改用**显式 length 合取 + `zip` 逐对**——反而更顺:`close length` 直接吃第一个合取,`close category at i` 吃 zip 的第 i 对。
- `FlatGrammar.Cat` 仍是投影,`.D` 点记法认不出(写全 `Linear1Cat.D`);`instDecEqCat` 干扰同前(§4.3)。
- **§8 词汇歧义口子已留**:词库是 `List (String × Cat)`,一个词可多次出现(多词类);`FlatLicensed` 的配对 `(w, slot) ∈ 词库` 天然量化"该词的某个词类等于槽"——即便当前每词一类,接口已对所有 readings 量化。

## v2-C. Expand/Close 首关(长度失配)+ 玩家步数

**关卡**:`¬ CanYieldFlat linear₁flat ["a","house","good","room"] N`(D N A N,长 4;模板长 2/3,每条 route 死于长度)。玩家三件工具 `suppose`/`expand`/`close length`(`Flat.lean`,elab tactic)。

**玩家动作序列(逐步标注:判断 vs 被藏的 Lean 杂活)**:

| # | 玩家打的 | 玩家面对的判断 | 类别 |
|---|---|---|---|
| 1 | `suppose` | —(假设"能生成",拆出 route + 许可) | **杂活**(intro + 拆 ∃) |
| 2 | `expand` | 这个主张能从哪些 route 来?列出 `[D,N]`、`[D,A,N]` | **判断**(认清 route 清单) |
| 3 | `close length` | route `[D,N]` 为何不成立?——**长度**(4 词 ≠ 2 槽) | **判断**(选 route + 判失配类型=长度) |
| 4 | `close length` | route `[D,A,N]` 呢?——**长度**(4 ≠ 3) | **判断** |

- **玩家判断:3 个**(枚举 route + 对每条 route 申报"长度"失配)。**红线达标**:`close length` **只核对**——玩家申报"长度",系统验 `words.length ≠ slots.length`;若长度其实相等(如 `a good good` 的 `[D,A,N]` 支,3=3),`close length` **报错拒绝**(实测:`decide proved ¬… is false`),逼玩家改用 `close category`。玩家**不碰** `rfl`/`simp`/`decide`——那些只在编译后 proof term 里。
- **被藏的 Lean 杂活**:拆 ∃、模板表投影展开、`List.length` 计算、`absurd`+`decide` 生成的行政证明——全在 tactic 内部,不泄露到玩家层(spec §15/§16)。
- **报错人话化**:目前拒绝信息还是 Lean 腔(`decide proved ¬… is false`)。spec §5/§16 要换成人话(如 `✗ 这条 route 长度并不失配,不能 close length`),数据都在(词数、槽数),属战术层包装,**本单未做**(和旧路线 A 的错误包装同性质)。

**generalize 待办(已在代码注释标)**:`expand` 现在把 `linear₁flat` 写死在 simp 集里;通用化 = 从 membership 假设读出 grammar 常量再 unfold。不影响首关,记账。

---

## 0. 路线 A 重做说明(维护者裁决)

**旧版被否**:旧路线 A 用一个 `dead_category Adv` + 整表 `decide (Adv ∉ usedCats)`,一步出结论——**神键/作弊感**:认出 Adv、扫规则表、下结论全替玩家做了。"2 步达标"是过度包装刷出来的,不算数。

**设计铁律(本次验收准绳)**:自定义 tactic **只准藏 Lean 杂活 + 报错换人话,绝不准藏语言学判断**。神键(判断也包进去)错;裸奔(Lean 杂活全暴露成 47 步管道工)也错;**正确在中间**——每步句法判断留给玩家,tactic 只吸收 Lean 机械。

**重做机制**:"死范畴"事实从引理内部**拆出来当假设**。作者只证纯结构归纳 `deadYield`(把 `hdead : ∀ r ∈ rules, Adv ∉ r.posCat` 当**参数**);玩家**逐条**建立 `hdead`——一条规则一步真判断,**不用一个 decide 扫完整表**。

---

## 1. 完成状态与代码位置

| 件 | 状态 | 位置 |
|---|---|---|
| 基底(词元/表达式/规则/`Deriv`/`CanYield`) | ✅ | `BareSyntax/Basic.lean` |
| 正向冒烟(`the ideas : N`) | ✅ | `Smoke.lean` — `smoke` |
| **plumbing** 结构归纳(通用死范畴引理) | ✅ 作者证 | `Linear.lean` — `deadYield`/`deadYieldL`(互递归),辅助 `linear₁_concat` |
| **路线 A**(玩家逐步亲历判断) | ✅ 证通,已重做 | `Linear.lean` — `route_A` |
| 路线 B(裸 cases 反演,反面对照) | ✅ 证通 | `Linear.lean` — `derivDA`/`noVery`/`route_B` |
| 路线 C(可判定性) | ⏸ 可行性判定:延后 | `Linear.lean` — Route C 注释块 |

`deadYield` 的三个假设正是玩家判断的插口:`hdead`(死范畴,逐规则填)、`hw`(该词只属该范畴)、`hbuild`(规则拼接,纯 plumbing)。引理体是对 `Deriv`/`DerivList` 的互递归结构归纳——**纯 Lean,零句法判断**。

---

## 2. 路线 A 玩家步数核算(逐步标注:句法判断 vs 被藏的 Lean 杂活)

`route_A` 的证明逐条(**判断**=玩家亲历的句法决定;**杂活**=自定义 tactic 该吸收的 Lean 机械):

| # | 证明里的动作 | 玩家面对的问句 | 类别 |
|---|---|---|---|
| 0 | `rintro ⟨d⟩` | —(假设"能生成",取出那棵推导树) | **杂活** |
| 1 | `?inTarget`(定位 "very" 在目标串) | 哪个词是问题所在? | **判断** |
| 2 | `?veryCat`(该词库里 "very" 只能是 Adv) | "very" 是什么词类?只此一种吗? | **判断** |
| 3a | `rcases hr`(规则表有两条,逐条看) | 规则表里有哪些规则? | **判断**(认清规则清单) |
| 3b | 规则 `N→D N`:各位置 D、N,无 Adv | 这条规则收 Adv 吗? | **判断** |
| 3c | 规则 `N→D A N`:各位置 D、A、N,无 Adv | 下一条呢?收 Adv 吗? | **判断** |
| 4 | `linear₁_concat`(规则都是拼接) | —(规则把输入串拼起来) | **杂活** |
| 5 | `?tgtCat`(N ≠ Adv) | —(目标范畴显然不是 Adv) | **杂活** |
| 6 | `deadYield`(结构归纳收尾) | —(死范畴的词进不了任何推导 ⇒ 矛盾) | **杂活** |

- **玩家亲历的句法判断:5 个**(定位问题词、判词类、认规则清单、逐条核 2 条规则)。**没有神键**:整表从不被一个 `decide` 一次扫完;规则一条一条过,5 条规则就是 5 步。
- **被藏的 Lean 杂活:4 处**(拆 Nonempty、拼接事实、N≠Adv、结构归纳)——全是机械,无句法内容,正是自定义 tactic 该吸收的。
- 对照:`usedCats` 仍作数据留着(供显示/工具),但**路线 A 的证明不用它做整表 decide**——那正是被否的神键形态。

### 玩家面(建议的战术层,本轮不实现)

每个"判断"配一条只藏 Lean、把报错换人话的战术:
- `offending_word "very"` — 玩家指认问题词(判断);tactic 定位、失败报 `✗ "very" 不在目标串里`。
- `word_is "very" Adv` — 玩家判词类(判断);tactic 查词库核对,错则 `✗ 词库里 "very" 的词类不是 Adv`。
- 逐规则 `rule_rejects "N→D N" Adv` — 玩家判这条规则收不收 Adv(判断);tactic 只查该条 `posCat`,错则 `✗ "N→D N" 的第 k 位就是 Adv,这条其实收 Adv`。
- `linear₁_concat` / `N≠Adv` / `deadYield` 由战术自动吸收,玩家看不见(纯 Lean)。

数据都在(`Rule.posCat`、词库),报错可读性是战术层实现,本轮只给设计。

---

## 3. 验收线达标判定(新准绳)

旧准绳"≤15 步"被否(能被过度包装刷过)。**新准绳:玩家亲历每一步句法判断 + tactic 只藏 Lean + 报错可读。**

| 路线 | 玩家是否亲历每步判断 | tactic 只藏 Lean? | 报错可读 | 判定 |
|---|---|---|---|---|
| **A(重做)** | ✅ 5 个判断全在玩家手里;规则逐条过,无整表神键 | ✅ 藏的 4 处全是纯 Lean(拆包/拼接/N≠Adv/归纳) | 设计已给(数据齐),战术层实现 | ✅ **达标** |
| **B** | ✅✅ 过度暴露:连 Lean 机械都要玩家做(~47 步管道工) | ❌ 什么都没藏 | 差(全是元级报错) | ❌ 不达标(反面) |

**结论:否定可玩,当且仅当走重做后的路线 A**——玩家逐条做真判断("这条规则不收 Adv,下一条也不收 ⇒ very 进不去 ⇒ 含 very 的串生不出"),tactic 只擦掉 Lean 机械。神键(旧 A)和裸奔(B)是两端错误,重做后的 A 落在正确中间。

---

## 4. 规则表示的摩擦记录(供终审:偏函数 vs 关系/图)

**总体倾向:定义域必须是数据。** 重做后这点更硬——玩家要**逐条核 `posCat`**,`posCat` 必须是可当场检视的显式数据字段,绝不能埋进不透明应用函数。

1. **定义域=数据,是"玩家逐规则判断"的前提。** 若规则只存不透明 `apply : List Expr → Option Expr`,玩家根本无法"看这条规则收不收 Adv"。我把 `posCat`(各位置范畴)存成显式字段、`applyRule` 由它派生。重做后这从"否定证明需要"升级为"**玩家判断需要**"——更强的一票投给"规则=数据/关系"。
2. **`build` 仍是函数字段。** 派生的死范畴论证还需要"规则拼接输入串"这条(`hbuild`/`linear₁_concat`),因为一般 `build` 可以凭空造词、破坏"输出词 ⊆ 输入词"。本切片所有规则 `build = flatten`,`hbuild` 一句 `rfl` 可证(纯 plumbing)。终审若把 `build` 也降成数据(如拼接模板枚举),这条假设可去、且规则表可 `DecidableEq`。
3. **`Cat` 可判定性是结构字段,反噬具体范畴 `decide`。** 全局转发实例 `instDecEqCat`(已降 `priority := low`)仍干扰 `decide (N ≠ Adv)` 的合成(重做里 `?tgtCat` 又踩到,改用 `Linear1Cat.noConfusion`)。终审定 Cat 载体时一并处理;换统一可枚举 Cat 可去掉该实例。
4. **`Expr G.Cat` 的 `G.Cat` 投影不归约**:`.D` 点记法认不出,得写全 `ToyCat.D`;`∈ G.lexicon` 的 `decide` 靠那个转发实例。per-grammar 的 Cat 作投影,处处要扶。

---

## 5. 其他偏离与发现

**偏离(记录在案)**:
- `applyRule` 由数据派生(非存不透明函数)——服务"定义域可检视",重做后更是玩家判断的硬前提。
- `(A)*` 展开为两条规则 `N→D N` / `N→D A N`(施工单许可;词库封闭忠实)。
- `deadYield` 加 `hbuild`(规则拼接)假设,使死范畴引理对**拼接型**语法通用;非拼接语法需另论(词能凭空产生时,"死范畴"论证本就不成立)。
- 路线 B 的 `N→D N` 支对象子推导交给 `noVery`(即 `deadYield` 特化)收尾,而非再裸反演一层——完全独立的 B 更长,只会加深"B 不达标"。互递归 `Deriv`/`DerivList` 绕开嵌套正性。

**发现**:
- **否定的可玩形态 = 作者证结构归纳 plumbing + 玩家逐条填"死范畴"假设**。玩家动作是一串真句法判断(定位词、判词类、逐规则核),`deadYield` 只把 Lean 归纳擦掉。这正是"中间态":既非神键、也非裸奔。
- **"逐条核规则"天然抗神键**:规则表多长,玩家就走多少步;整表 `decide` 那种一步扫完的写法在重做里被明确排除(仅 `usedCats` 作数据留存,不进证明)。
- 路线 C(整命题可判定)仍非本层能一行 `decide`:需"规则增长串长 ⇒ 生成有限"的枚举器(本轮出界)。有限性脚手架已就位,不挡后续。

**给集成(小红)/终审**:
- 规则表示终审:本切片(尤其重做后"玩家逐规则核 posCat")强烈倾向"定义域=数据/关系"。三处摩擦(§4)是输入。
- 采纳路线 A 做关卡的下一步:实现 §2 那三条战术层小件(`offending_word` / `word_is` / `rule_rejects`)+ 把 `deadYield` 作 NewTheorem 发放。属战术/关卡层,本轮按施工单只交基底+三路线+步数报告。
