Agent: 小蓝
Role: side window (worktree .claude/worktrees/bg-slice, branch bg-base-slice, from main ff2a3f4)
Date: 2026-07-09
For: 小姜(派单 claude-code-brief-bg-slice.md)/ 小红(集成:review + build + 并入)

# Bare Grammar 基底 + CannotYield 垂直切片 — 交接

**必交件全部完成,lake build 通过,v1 未动,无 sorry。不 push(等小红)。**

## 交付
- `BareSyntax/Basic.lean` — 基底:`Expr` / `Rule`(定义域 `posCat` 为显式数据)/ `BareGrammar` / `applyRule`(由数据派生)/ 互归纳 `Deriv`+`DerivList` / `CanYield`。
- `BareSyntax/Smoke.lean` — 正向冒烟 `smoke : CanYield toyG ⟨the ideas⟩ N`。
- `BareSyntax/Linear.lean` — `linear₁` + 三条路线:`route_A`(死范畴引理 `noVery` + 可判定表检)、`route_B`(裸反演 + `derivDA`)、Route C(可行性注释:延后到"生成可判定"里程碑)。
- `BareSyntax.lean` — 库根;`lakefile.lean` 加了 `lean_lib BareSyntax`(在 `@[default_target]` 之前,防地雷 2)。
- `BareSyntax/REPORT.md` — **主报告**:三路线状态、A/B 玩家步数表、验收判定、规则表示摩擦(供终审)、偏离与发现。

## 结论(REPORT 详述)
**否定证明可玩,当且仅当走路线 A**(玩家宣称"死范畴"+系统 `decide` 复核规则表):**2 玩家步、1 新动作,达标**。路线 B(裸反演)~47 步、多新动作,**不达标**——正是反面对照。这回答了施工单的关键路径问题。

## 验证
- `lake build`(默认 Game)→ v1 完好,63 jobs。
- `lake build BareSyntax` → 6 jobs 通过。
- `grep sorry/admit BareSyntax/` → 空。

## 集成注意(给小红)
- 新增文件全在 `BareSyntax/` + `BareSyntax.lean` + `lakefile.lean` 一行 `lean_lib BareSyntax`(附注释说明为何在 default_target 之前)。未碰 `XSyntax/` 或任何 Game 关卡。
- 一个基底摩擦要留意:全局实例 `instDecEqCat`(转发 `G.decCat`)对具体范畴的 `decide (¬ D=A)` 有干扰,已降 `priority := low` 并在证明里改用 `contradiction`/`noConfusion`。终审 Cat 载体时一并定(REPORT §4.3)。

## 未做(施工单允许/出界)
- lean4game scratch 世界集成("时间允许再做",本轮未做;基底+三路线+步数报告是必交件,已交)。
- 路线 A 的战术层包装(`dead_category <Cat>` + 把 `noVery` 作 NewTheorem 发放)——属关卡/战术层,REPORT 给了建议,本轮未实现。
- 路线 C 的完整 `Decidable` 实例——依赖"规则增长串长⇒生成有限"定理(显式出界)。

## 待小姜/终审
- 规则表示终审(偏函数 vs 关系/图):本切片实测倾向"定义域必须是数据",三处摩擦见 REPORT §4。
- 若采纳路线 A 做关卡,下一步是那两个战术层小件 + scratch 世界——可另派单。
