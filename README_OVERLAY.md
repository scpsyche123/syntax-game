# Syntax Game — 覆盖层安装说明

本 zip 是一个**覆盖层**(overlay),不是完整工程。基建文件(lakefile、
lean-toolchain、lake-manifest、.devcontainer、GitHub action)必须来自官方模板
GameSkeleton,因为 GameServer 依赖与 Lean 版本是配套钉死的。

## 安装步骤

1. **取模板**
   ```
   git clone https://github.com/hhu-adam/GameSkeleton.git SyntaxGame
   cd SyntaxGame
   ```
   (或在 GitHub 上 "Use this template" 建自己的仓库再 clone。)
   ⚠ 保留模板自带的 `lean-toolchain`,不要改成本地版本。

2. **盖覆盖层**:把本 zip 的内容复制进 SyntaxGame/,允许覆盖:
   - `Game.lean` 覆盖模板的同名文件
   - `Game/Metadata.lean` 覆盖模板的同名文件
   - `Game/Levels/XBar.lean`、`Game/Levels/XBar/` 为新增
   - `XSyntax.lean`、`XSyntax/` 为新增(理论库,与 VS Code 走稿版完全同源)
   然后删除模板的示例世界:
   ```
   rm -r Game/Levels/DemoWorld.lean Game/Levels/DemoWorld
   ```
   (若模板中 Game.lean 之外还有引用 DemoWorld 的地方,一并清理。)

3. **改 lakefile**:在模板的 lakefile 中、`lean_lib Game` 之前加一行库声明。
   - lakefile.lean 写法:
     ```lean
     lean_lib XSyntax
     ```
   - lakefile.toml 写法:
     ```toml
     [[lean_lib]]
     name = "XSyntax"
     ```

4. **构建游戏**
   ```
   lake update -R
   lake build
   ```
   (gameserver 可执行文件应由 post-update-hook 自动构建;若无,手动
   `lake build gameserver`。)

5. **起前端**:在 SyntaxGame 的**同级目录**:
   ```
   git clone https://github.com/leanprover-community/lean4game.git
   cd lean4game
   npm install --force
   npm start
   ```
   浏览器打开 http://localhost:3000/#/g/local/SyntaxGame
   (URL 末段 = 游戏文件夹名。)

6. **改动后**:游戏目录里 `lake build`,浏览器刷新。

## 内容清单

- `XSyntax/` — 理论库六文件,与轨道一(VS Code 版)逐字节相同,含 Playground
- `Game/Metadata.lean` — 七条指令的 TacticDoc
- `Game/Levels/XBar/` — 五关:中心语 → 空洞投射 → 补足语与选择(含沙盒反例)
  → 附加语 → colorless 全句
