# evidence/ · 验证取证

本目录存放验证过程的截图（**每件一组，两张**）：

| 文件名 | 内容 |
|:--|:--|
| `Day27-01_内核.png` | 内核通过：`All Messages (0)`（光标置于文件末尾） |
| `Day27-01_Comparator.png` | Comparator 二次验证通过：`Trusting challenge with hash <SHA256>` ＋ 结果为通过 |
| `Day27-02_内核.png` / `Day27-02_Comparator.png` | 同上 |
| `Day27-03_内核.png` / `Day27-03_Comparator.png` | 同上（⚠️ **须为第二稿**） |
| `Day27-04_内核.png` / `Day27-04_Comparator.png` | 同上 |
| `Day27-05_内核.png` / `Day27-05_Comparator.png` | 同上（★ 关口定理） |
| `Day27-06_内核.png` / `Day27-06_Comparator.png` | 同上 |
| `Day27-07_内核.png` / `Day27-07_Comparator.png` | 同上（⚠️ **须为第三稿**） |
| `Day27-08_内核.png` / `Day27-08_Comparator.png` | 同上 |

**纪律**：

1. **截图中的哈希须与最终落盘 SHA256 一致**；
2. **若中途重跑导致哈希变更，截图须重拍**（否则证据与文件不匹配）；
3. 平台：L∃∀N Comparator Live (Experimental) · Latest Mathlib with Lean v4.35.0；
4. ⚠️ **本仓两件有改稿**：`Day27-03`（第二稿，补 `noncomputable`）、`Day27-07`（第三稿，`λ`→`a` ＋ `simpa`→`simp`）——**截图必须对应终稿哈希**，旧稿截图一律作废。
