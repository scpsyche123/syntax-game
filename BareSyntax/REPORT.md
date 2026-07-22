# Bare Grammar 基底 + CannotYield 垂直切片 — 报告

**分支** `bg-base-slice` · **昵称** 小蓝 · **日期** 2026-07-09
**执行施工单** `claude-code-brief-bg-slice.md` · **lake build** 通过(v1 未动,63 jobs;`lake build BareSyntax` 6 jobs;无 `sorry`)

一句话结论:**否定证明可玩——但只经路线 A(宣称"死范畴"+系统复核规则表),不经路线 B(裸反演)。** 路线 A ≤ 2 玩家步、1 个新动作,达标;路线 B ~40+ 步、多个新动作,不达标。这正是"否定是否可玩"的答案:**可玩,前提是给玩家路线 A 那把武器,而不是让他裸反演。**

---

## 1. 完成状态与代码位置

| 件 | 状态 | 位置 |
|---|---|---|
| 基底(词元/表达式/规则/`Deriv`/`CanYield`) | ✅ | `BareSyntax/Basic.lean` |
| 正向冒烟测试(`the ideas : N`) | ✅ | `BareSyntax/Smoke.lean` — `smoke` |
| `linear₁` 语法 + 目标命题 | ✅ | `BareSyntax/Linear.lean` |
| 路线 A(死范畴引理 + 可判定表检) | ✅ 证通 | `Linear.lean` — `usedCats` / `noVery`(互递归)/ `route_A` |
| 路线 B(裸 cases 反演) | ✅ 证通(见 §5 偏离) | `Linear.lean` — `derivDA` / `route_B` |
| 路线 C(可判定性) | ⏸ 可行性判定:延后 | `Linear.lean` — Route C 注释块 |

基底关键设计(细节见 §4 摩擦):
- 规则的**定义域是显式数据**(`posCat : List Cat`),`applyRule` 由它**派生**——不是把定义域藏进不透明函数体。否定证明因此能把规则表当数据逐行走。
- `Deriv`/`DerivList` 用**互归纳**(配对归纳)绕开 `List (Deriv …)` 的嵌套正性;递归一律 match,不用 `induction` 战术。

---

## 2. 玩家步数核算

"步" = 一次 tactic 调用或一次理由选择。W1 动作集 = word/rule 对应的构造步骤(`.lex` / `.app` / 搭 `DerivList`)。

### 路线 A(动作序列)

裸证明体只有两步:

| # | 动作 | 说明 |
|---|---|---|
| 1 | `rintro ⟨d⟩` | 拆 `Nonempty`,拿到那棵(假想的)推导树 |
| 2 | `exact noVery d ⟨N≠Adv⟩ ⟨表检⟩` | 应用死范畴引理:宣称"目标范畴非 Adv" + 系统对规则表 `decide` 复核"Adv 无位置" |

- **玩家步数:2**。
- **新动作:1**——"宣称某范畴是死范畴,系统复核规则表"(游戏里应包成一条自定义战术,如 `dead_category Adv`;`noVery` 作为 NewTheorem 战利品发给玩家,像 NNG 里 `rw [add_comm]`)。
- 表检 `Adv ∉ usedCats linear₁` 是 `by decide`,对应"系统当场复核玩家的理由"。玩家只需**说出理由**,不需证引理(引理是作者一次性证的 `noVery`)。

### 路线 B(动作序列,裸反演)

按 `route_B` 逐条数(不含它依赖的 `derivDA` 辅助引理本身的 ~12 步):

| 段 | 动作 | 步数 |
|---|---|---|
| 开局 | `rintro ⟨d⟩` → `cases d`(lex/app) | 2 |
| lex 支 | `simp` 关闭(非词库条目) | 1 |
| app 预处理 | `simp hr` → `rcases hr`(两条规则) | 2 |
| N→D N 支 | `cases dl`×3 降到正确长度(3 个错长度用 `simp` 各关) + `split` + `rename_i` + `rw` + `obtain` + `simp hcat` + `obtain` + `derivDA` 定 D 叶 + `simp hstr` + 对象 N 交给 `noVery` + `rw` + `exact` | ~15 |
| N→D A N 支 | `cases dl`×4 + 错长度 `simp` + `split`+`rename_i`+`rw`+`obtain`+`simp hcat`+`obtain`+`derivDA`×2 定 D、A 叶 + `simp` 撞 `good≠very` | ~15 |
| **合计** | | **~35(+辅助引理 ~12)** |

- **玩家步数:~35(单靠 route_B)+ ~12(derivDA)≈ 47**。
- **新动作:多个**——`cases`(对 `Deriv`/`DerivList` 反演)、`split`(拆 `applyRule` 的 `if`)、`rename_i`、`obtain`、`rw … at`、字符串 `cons.injEq` 反演……全是 W1 之外的元级操作。

---

## 3. 验收线达标判定

验收线:**≤ 15 步、超出 W1 的新动作 ≤ 1、每步失败报错可被非 Lean 用户理解**。

| 路线 | 步数 | 新动作数 | 报错可读性 | 判定 |
|---|---|---|---|---|
| **A** | 2 | 1(`dead_category`) | 见下 | ✅ **达标** |
| **B** | ~47 | 多个(cases/split/obtain/rw…) | 差(裸 Lean 反演,报错全是元级) | ❌ 不达标 |

**结论:否定证明可玩,当且仅当走路线 A。** 路线 B 是反面对照:它把"为什么不可生成"这件本该一句话("very 是死范畴")的事,摊成对每棵可能推导树的逐支反演——步数、新动作、报错三项全崩。

**报错可读性(路线 A,需后续包装,本轮只给建议)**:
- 玩家宣称一个**并非死范畴**的范畴时,表检 `by decide` 失败——建议包一条自定义战术,失败信息读作:`✗ "N" 出现在规则 "N→D N" 的第 2 个位置,不是死范畴`(从 `usedCats` 数据直接生成,天然可读)。
- 玩家宣称的死范畴对,但词/串对不上时,`noVery` 的 `C ≠ Adv` 前提或末端 membership 失败——建议错误信息:`✗ 目标串里没有范畴为 "Adv" 的词`。
- 这两条都不必本轮实现;数据都在(`usedCats`、词库、规则表),包装是关卡层/战术层的活。

---

## 4. 规则表示的摩擦记录(供终审:偏函数 vs 关系/图)

**总体倾向:数据(关系/表)胜于不透明函数。** 三处摩擦都源于"把语法信息塞进函数体":

1. **定义域必须是数据,否则否定证明做不了。** 施工单原文把规则的核心写成"应用函数 `List Expr → Option Expr`"。若真把它存成一个不透明闭包,否定证明就无法"逐行核验该范畴有无位置"——那信息被埋进函数体了。**我实际改成**:存 `posCat`(各位置范畴)+ `result` + `build`,`applyRule` 由它们**派生**。这是一票投给"规则=数据"。终审若定"规则=关系/图",会更顺:`posCat` 本就是关系的一行。

2. **`build : List (List String) → List String` 仍是函数字段,挡住 `DecidableEq (Rule)`。** 本切片的否定证明不需要规则相等判定(只用 `∈ rules` 成员 + `posCat` 内省),没被卡;但这意味着规则表不是完全一等数据(不能 `decide` 两规则是否相等)。若终审要"规则表可枚举比较/去重",`build` 得也降成数据(如"拼接模板"枚举)。

3. **`Cat` 的可判定性是结构字段而非类型类,反噬了具体范畴的 `decide`。** `BareGrammar.Cat : Type` + `decCat` 字段,导致 `DecidableEq G.Cat` 不进实例搜索。我加了全局实例 `instDecEqCat` 转发字段——但它**干扰**了具体 `Linear1Cat` 上 `decide (¬ D = A)` 的实例合成(合成失败)。只好:该实例降 `priority := low`,且范畴不等改用 `contradiction`/`Linear1Cat.noConfusion` 而非 `decide`。**这是"语法带自己的 Cat 类型"这一立场的直接代价**,终审若允许范畴用统一可枚举载体(如 `Fin n` + 标签表)会省掉这层。

4. **`Expr G.Cat` 里 `G.Cat` 是投影,不归约。** `.D` 点记法在期望类型 `G.Cat` 处认不出(报 `BareGrammar.Cat.D` 未知),得写全 `ToyCat.D`;`∈ G.lexicon` 的 `decide` 也要靠上面那个转发实例。per-grammar 的 Cat 作投影,处处要额外扶一把。

---

## 5. 其他偏离与发现

**偏离(均记录在案,施工单允许)**:
- **`applyRule` 由数据派生**,而非存不透明应用函数(见 §4.1)——服务"定义域可检查"的硬要求。
- **`(A)*` 展开为两条规则** `N→D N` / `N→D A N`(施工单许可;词库封闭下忠实)。
- **路线 B 的 `N→D N` 支**:对象 N 子推导交给路线 A 的 `noVery` 收尾,而非再裸反演一整层。完全独立的 B 会在此再降一层(又一轮 `cases dl`/`split`/串反演,~+15 步)。这只会让 B 的步数更难看,不改变"B 不达标"的结论。用互递归 `Deriv`/`DerivList`(配对归纳)绕开 `List (Deriv …)` 的嵌套正性。

**发现**:
- **否定可玩,答案是"给玩家 `noVery` 这把武器 + 一条 `dead_category` 战术"**。玩家动作 = 说出语言学理由("这个词类在任何规则里都没有位置"),系统 `decide` 复核。这正对应 Church 式否定的直觉,且步数/新动作达标。
- **可判定表检是干净的玩家可验证载体**:`Adv ∉ usedCats linear₁` 一个 `decide` 搞定,数据全现成。
- **路线 C(整命题可判定)不是本层能一行 `decide` 的**:`Deriv` 是真正的数据上归纳族,`Decidable (CanYield …)` 需要"规则严格增长串长 ⇒ 生成有限"这条(本轮显式出界)的枚举器,否则实例会循环。有限性脚手架(处处 `List`/`DecidableEq`)已就位,不挡后续。

**给集成(小红)/终审的建议**:
- 规则表示终审:本切片是"规则=函数"的实测,结论倾向"定义域必须是数据"。三处摩擦(§4)是输入。
- 若采纳路线 A 做关卡:需两个战术层小件——`dead_category <Cat>`(封 `noVery` + 表检 + 可读报错)、以及把 `noVery` 作为 NewTheorem 发给玩家。均属战术/关卡层,本轮未实现(施工单只要基底 + 三路线 + 步数报告)。
- `instDecEqCat` 的干扰(§4.3)建议终审时连同"Cat 载体"一起定;若换统一可枚举 Cat,这实例可去。
