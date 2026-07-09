# 指令信道（小姜 → 团队）

总负责人**小姜**向员工窗口传令的机制。两条信道，按窗口类型分。

## 信道 A — Claude Code 窗口（直连）

用 CCD `send_message` 直发；消息以「From 小姜」作为一条用户 turn 落到对方会话，
附回链，维护者需确认。目标会话:

| 窗口 | 昵称 | sessionId |
|---|---|---|
| 主窗口 | 小红 | `local_cb0e80b7-6c77-44ca-a3f7-d61571b0de0b` |
| 侧窗口 | 小蓝 | `local_1340ca2f-b5ec-4cd7-a2dd-633f7da56be6` |

直连是交接/传令,不是后台遥控:发完不替小姜盯活。实质指令仍在本目录留一份存档
(`TO-xiaohong.md` / `TO-xiaolan.md`,按需建),保证跨窗口可追溯。

## 信道 B — Codex 窗口 小绿（文件收件箱）

`send_message` 到不了 Codex。改用收件箱文件 `docs/orders/TO-xiaolv.md`:

- **投递**:小姜把指令**直接写进小绿当前活跃 worktree 的工作树**
  (如 `.claude/worktrees/xiaolv-display-layer/docs/orders/TO-xiaolv.md`),
  他本地即可见,不必先合 main;同时 main 留规范母本存档。
- **格式**:追加式,每条 `### ORD-NNN [状态] 日期 · 标题`,状态 `OPEN`/`ACK`/`DONE`。
- **回执**:小绿开工先读收件箱,读完把状态改 `ACK`,完成改 `DONE`,收尾照旧写 handoff。

## 通则

- 一条指令 = 一个编号,全局递增,不复用。
- 指令须自足:含背景、要动的文件、验收标准、以及**它属于哪个 Phase / 是否关键路径**。
- 只有主窗口(小红)push;小姜起草的 docs 改动由小红并入。
- 昵称/来源规则见 `docs/WORKFLOW.md`。
