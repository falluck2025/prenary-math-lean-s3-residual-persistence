[![DOI](https://zenodo.org/badge/DOI/DOI-TBD.svg)](https://doi.org/DOI-TBD)

# 偏元数学 · Day27 · 残差为什么消不掉（层分离 · 零点自由度 · 四相安放）· Lean 4 形式化验证

## Prenary Mathematics · Day27 · Why the Residual Cannot Be Eliminated (Layer Separation · Zero-Point Freedom · Placement of the Four Phases) · Lean 4 Formal Verification

本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

> **DOI**：`DOI-TBD`（**发布后回填本行与顶部徽章**）。本仓库为偏元数学 S3（第三程）数学侧的**第二段**，上承 Day26 `prenary-math-lean-s3-direction-return`（对象层 `ℂ★` · 二态 · 偏元序）与 Day25 `prenary-math-lean-s3-sw-epsilon-eta`（ε↔η 映射）。

## 摘要

**问题**：既然 A1 规定「每次动作都留一个残差 `ε`」，那么——**把残差消掉的尝试，为什么消不掉？**

**答**：两层各拦一次，最后收一条判定。

**一、动作层拦一次（Day27-01／-02）**：归零操作 `zeroingOp ε x = x − x + ε` 的输出**恒为 `ε`**、与输入无关；`0` 不是它的不动点；一个**统一平移不能把两个不同残差同时归零**。相消的结果**既不是 `a`、也不是 `−a`、也不是 `0`，而是 `ε`** —— **"第三种结果"存在**。

**二、对象层拦一次（Day27-03／-04／-07）**：对象层与动作层**并列、互不定义**；只定义在对象层上的映射**读不到 `ε`**。在 `ℂ` 上，平移不变的实函数**只能取常值**；搬到 S-006 的底 `ℂ★` 上结论**更强**——**平移根本不是 `ℂ★` 的自同构**（有点被译出对象层、落进缺陷点），而 `ℂ★` 的自同构是**乘性缩放**且**可迁**，故**乘性不变的实函数必为常值**（连"径向"都读不出）。

**三、收口判定（Day27-05 ★）**：**存在一个统一平移把所有残差同时归零 ⟺ 残差本身是常数。** 逆否：**残差不为常数 ⟹ 零点被锚定。**

**四、方向（Day27-06／-08）**：`1 + i + (−1) + (−i) = 0` ⟹ 四重对称 `ℤ/4` ⟹ 无方向偏好；**缺一角** ⟹ 合向量非零 ⟹ **破缺才有偏好**。四相在数学侧的位置即覆叠阶梯的下一级商。

**不在范围内**：**不主张任何数值对应**；**不主张** `ε` 究竟属于哪一层已被判定；**不主张** `ℤ/4` 是由物理四相**推导**得来（本仓只给它在数学侧的**安放位置**）；不做覆叠分类与基本群。

## Abstract

**Question**: Given A1 ("every action leaves a residual `ε`"), **why cannot the residual be eliminated?**

**Answer**: two layers each block once, then one criterion.

**I. The action layer blocks once (Day27-01/-02)**: the zeroing operation `zeroingOp ε x = x − x + ε` outputs **`ε` exactly**, independent of the input; `0` is not its fixed point; a single uniform shift **cannot zero two distinct residuals simultaneously**. Cancellation yields **neither `a`, nor `−a`, nor `0`, but `ε`** — a **"third outcome" exists**.

**II. The object layer blocks once (Day27-03/-04/-07)**: the object layer and the action layer are **juxtaposed and mutually undefined**; a map defined only on the object layer **cannot see `ε`**. Over `ℂ`, a translation-invariant real function **must be constant**; lifted to S-006's base `ℂ★` the conclusion is **stronger** — **translation is not an automorphism of `ℂ★` at all** (some point is carried out of the object layer into the defect point), while the automorphisms of `ℂ★` are **multiplicative scalings**, which act **transitively**; hence a multiplicatively invariant real function **must be constant** (not even "radius" is readable).

**III. The closing criterion (Day27-05 ★)**: **a uniform shift zeroing all residuals exists ⟺ the residuals are themselves constant.** Contrapositive: **non-constant residuals ⟹ the zero point is anchored.**

**IV. Direction (Day27-06/-08)**: `1 + i + (−1) + (−i) = 0` ⟹ fourfold symmetry `ℤ/4` ⟹ no direction preference; **removing one corner** ⟹ nonzero resultant ⟹ **only broken symmetry yields preference**.

**Out of scope**: **no numerical correspondence** is claimed; we do **not** claim that "which layer `ε` belongs to" has been settled; we do **not** claim that `ℤ/4` is **derived** from the physical four phases (the repository gives only its **placement** on the mathematical side); no covering classification or fundamental group.

## 关键词

偏元数学；残差 ε；不可消除；层分离；对象层／动作层；零点自由度；统一平移；相消不完全；四相；ℤ/4；覆叠阶梯；对象层 ℂ★；自同构；退化；Lean 4；形式化验证；陈偏贞；老陈与AI的深夜实验室；PGI蛟龙；华夏思哲偏元注

## 概述

偏元数学是对经典数学的扩展尝试，`ε = 0` 时退化为经典。

本仓库回答一个**具体问题**：**残差为什么消不掉？**

三种"消掉它"的直觉都被逐条拦下：

| 直觉 | 被谁拦下 | 结论 |
|:--|:--|:--|
| "`x − x` 就归零了" | 动作层 | 归零操作输出恒为 `ε`，`0` 不是它的不动点 |
| "找一个统一平移把残差搬走" | 动作层 | 一个平移**不能同时**归零两个不同残差 |
| "让对象层的重标号把残差带走" | 对象层 | 对象层与动作层**并列**，对象层的映射**够不到** `ε` |

⟹ 收口为一条判定：**零点能否被搬走，取决于残差是否为常数。**

> **后续**：本仓上承 Day26（对象层 `ℂ★` · 二态 · 偏元序），并与 Day25（ε↔η 弱结构桥）互为参照。**发布文案不互相越读。**

## 核心定义

```lean
-- Day27-01：归零操作（A1 的一步代入）
def zeroingOp (ε x : ℝ) : ℝ := x - x + ε

-- Day27-03：对象层为静态（004 取 ℂ；S-006 细化为 ℂ★）
abbrev Obj := ℂ
structure Act where
  eps : ℝ
  hpos : 0 < eps
structure World where
  obj : Obj
  act : Act

-- Day27-03：对象层的重标号（平移）—— 注意签名里没有 act
def shiftObj (c : Obj) (w : World) : World := { w with obj := w.obj + c }

-- Day27-07：S-006 底下的对象层 ℂ★，与其自同构（乘性缩放）
abbrev ObjS : Type := { z : ℂ // z ≠ 0 }
def scaleS (a : ℂ) (ha : a ≠ 0) (z : ObjS) : ObjS :=
  ⟨a * (z : ℂ), mul_ne_zero ha z.2⟩
```

## 定理清单

> **如实说明**：全部命题均为**结构性**的（不涉及数值），**不构成**关于"哪一层拥有 `ε`"的断言。

### Day27-01 · 归零操作与统一平移（4 条）

| 定理 | 命题 |
|:--|:--|
| `zeroingOp_eq_eps` | 归零操作的输出**恒为 `ε`**，与输入 `x` 无关 |
| `zero_not_fixed` | `ε > 0` ⟹ **`0` 不是归零操作的不动点** |
| `fixed_point_eq_eps` | 若归零操作以 `x` 为不动点，则 **`x = ε`** |
| `uniform_shift_fails` | **一个统一平移不能把两个不同残差同时归零** |

### Day27-02 · 相消不完全（3 条）

| 定理 | 命题 |
|:--|:--|
| `idealCancel_eq_zero` | 经典相消 `a + (−a) = 0` |
| `actualCancel_eq_eps` | 实际相消 `idealCancel a + ε = ε` |
| `actualCancel_ne_zero` | `ε ≠ 0` ⟹ 相消结果 **既不是 `a`、也不是 `−a`、也不是 `0`** ⟹ **第三种结果存在** |

### Day27-03 · 层分离（类型骨架）（4 条）

| 定理 | 命题 |
|:--|:--|
| `padoa_same_obj` | 两世界（`w₁`／`w₂`）的**对象层相同** |
| `padoa_diff_eps` | 两世界的**残差不同** |
| `obj_map_cannot_see_eps` | **只定义在对象层类型上的映射，无法区分这两个世界** |
| `shiftObj_eps_invariant` | **对象层平移不改变动作层的残差**（`rfl` 级 —— 签名里没有 `act`） |

> ⚠️ **本条（`shiftObj_eps_invariant`）的诚实标注**：这是**签名层面的事实**，不是数学论证。

### Day27-04 · 对象层量的自同构不变性（2 条）

| 定理 | 命题 |
|:--|:--|
| `translation_invariant_implies_const` | **平移不变的实函数只能取常值** |
| `obj_layer_quantity_same_value` | 对象层可定义的量在**任意两点同值** ⟹ 读不出随动作变化的量 |

> ⚠️ **显式假设**：把「可定义 ⟹ 自同构不变」当作 `hdef` 引用，**非本仓所证**。

### Day27-05 · ★ 层归属与零点自由度（3 条）

| 定理 | 命题 |
|:--|:--|
| ⭐ **`zero_point_free_iff`** | **★ 存在统一平移把所有残差同时归零 ⟺ 残差本身是常数** |
| `const_shiftable` | 常值残差可被平移归零 |
| `nonconst_not_shiftable` | 两个不同残差 **消不掉** |

### Day27-06 · 方向与升域（4 条）

| 定理 | 命题 |
|:--|:--|
| `four_roots_sum_zero` | `1 + i + (−1) + (−i) = 0` ⟹ 四重对称 ⟹ **合向量为零（无偏好）** |
| `broken_symmetry_sum` | **缺一角** ⟹ 合向量 `= i` |
| `broken_symmetry_nonzero` | **破缺才有偏好**（合向量非零） |
| `two_directions_not_shiftable` | 方向不全同 ⟹ 两个方向**不能同时被平移归零** |

### Day27-07 · S-006 底下的层分离（4 条：3 定理 + 1 定义）

| 条 | 命题 |
|:--|:--|
| `shift_not_automorphism` | **平移不是 `ℂ★` 的自同构**（有点被译出对象层，落进缺陷点） |
| `scaleS`（定义） | `ℂ★` 的自同构：**乘性缩放** |
| `scale_transitive` | 乘性缩放的作用**可迁**（任两点可被一次缩放相连） |
| `scale_invariant_implies_const` | **乘性不变的实函数必为常值**（连"径向"都读不出） |

### Day27-08 · S-006 底下的 `ℤ/4`（四相的安放位置）（4 条）

| 定理 | 命题 |
|:--|:--|
| `four_state_nontrivial` | `ℤ/4` 非平凡（`1 ≠ 0`） |
| `half_turn_involution` | 「二分之一圈」＝元素 `2`：**`2 + 2 = 0`**（相差 `π` 的那一对自成 `ℤ/2`） |
| `half_turn_nontrivial` | `2 ≠ 0` ——「半圈」非平凡 |
| `four_states_distinct` | 四相各自可指认（`0 ≠ 1 ∧ 1 ≠ 2 ∧ 2 ≠ 3`） |

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战） | 代码 SHA256（锁解答） |
|:--|:--|:--|:--|:--|
| Day27-01 | No goals + All Messages (0) | ✅ Successfully validated | `5ad8f8f78a1f703202cc836d4c510317e65d7fe2d6d52f3f7fee6ee0de154ba7` | 同左 |
| Day27-02 | No goals + All Messages (0) | ✅ Successfully validated | `588ad8e2f15eaa494a5107cf72032252cd86de51ef81595cdcbe5cb025f5c0a4` | 同左 |
| Day27-03 | No goals + All Messages (0) | ✅ Successfully validated | `7a23ef43714b5ef2dbaf4f60a2783ba96664654c05460c3738323dd0bacf8034` | 同左 |
| Day27-04 | No goals + All Messages (0) | ✅ Successfully validated | `016fe72bdb6cc1e159bf026638390f1f16c0b0306ee8af71c02ef7cfa8691be0` | 同左 |
| Day27-05 | No goals + All Messages (0) | ✅ Successfully validated | `a2bbee07d40687537ccd25fe8aed6dfd2fe7ce3ad8462e69c9991d0849da3862` | 同左 |
| Day27-06 | No goals + All Messages (0) | ✅ Successfully validated | `02ca16cad428683b1b8dda86ed3ae1ab529b75f51ba1a1c0aa152d18c34df6a6` | 同左 |
| Day27-07 | No goals + All Messages (0) | ✅ Successfully validated | `17e65b8d9ef26e2cbb9ff7c962576b5438f64f7c60f35bd7525d7c9a838b79e0` | 同左 |
| Day27-08 | No goals + All Messages (0) | ✅ Successfully validated | `a72ab14796c47d5125a35fb1f34c7cf595d6fb649ec3c5e6c55615b59b5a227e` | 同左 |

- **平台**：L∃∀N Comparator Live (Experimental) · Latest Mathlib with Lean v4.35.0
- **验证时间**：2026-09-21 22:2x–22:52
- **双哈希说明**：本组采用**自编 challenge** 模式（Challenge 文本 ＝ 我方提交代码），故 **Challenge Hash 与代码 SHA256 取同一值**；已用本地 `sha256sum` 与 Comparator 显示值**逐字核对一致**。
- ⚠️ **改稿记录**：**Day27-03 为第二稿**（① 补 `noncomputable`）；**Day27-07 为第三稿**（① `λ` 系 Lean 保留记号，缩放参数改名 `a`；② 改用 `simp` 消 `unnecessarySimpa` 警告）。**其余六件均为第一稿一次通过。** 表中哈希**均为终稿哈希**。

## 文件说明

```
.
├── Day27-01_归零操作与统一平移_LEAN源码_20260921.lean          # 4 条
├── Day27-02_相消不完全_LEAN源码_20260921.lean                  # 3 条
├── Day27-03_层分离_对象层与动作层_LEAN源码_20260921.lean        # 4 条（第二稿）
├── Day27-04_对象层量的自同构不变性_LEAN源码_20260921.lean       # 2 条
├── Day27-05_层归属与零点自由度_LEAN源码_20260921.lean           # 3 条（★ 含关口定理）
├── Day27-06_方向与零点自由度_四相与升域_LEAN源码_20260921.lean   # 4 条
├── Day27-07_S006底下的层分离_对象层CStar与自同构_LEAN源码_20260921.lean  # 4 条（第三稿）
├── Day27-08_S006底下的Z4_四相的安放位置_LEAN源码_20260921.lean  # 4 条
├── README.md
├── LICENSE
└── evidence/                                                   # 验证截图（内核 / Comparator）
```

**合计：8 文件 · 27 条定理 ＋ 1 定义。**

## 复现方式

1. 打开 `https://comparator.live.lean-lang.org/`（Latest Mathlib with Lean v4.35.0）。
2. 将对应 `.lean` 文件**整份复制**（Ctrl+A，含 `import Mathlib` 与 `/-!` 抬头），分别贴入 **Challenge** 与 **Candidate Solution** 面板。
3. 运行内核，确认 `All Messages = 0`；再点二次验证，应显示 `Trusting challenge with hash <SHA256>` 且结果为通过。
4. 用 `sha256sum <file>.lean` 计算哈希，与上表**逐字核对**。

## 可证伪条件

1. 若存在一个统一平移 `c`，能把**两个不同残差** `ε₁ ≠ ε₂` **同时归零** ⟹ `zero_point_free_iff` 的逆否失效；
2. 若存在**只定义在对象层**上的映射能区分两世界（对象层同、残差不同）⟹ `obj_map_cannot_see_eps` 失效；
3. 若在 `ℂ★` 上存在**乘性不变**的非常值实函数 ⟹ `scale_invariant_implies_const` 失效；
4. 若 `ℤ/4` 中出现四相不互异的情形 ⟹ `four_states_distinct` 失效；
5. 若本仓任何一条在 Lean 4（Mathlib）中重跑**不通过** ⟹ 相应条目的形式化主张失效。

## 引用与许可

- 作者：**陈松（Chen Song）**｜ORCID：`0009-0002-9510-2239`
- GitHub：`github.com/falluck2025`
- License：**CC BY-NC-ND 4.0**

## 作者致谢

感谢一切偶然的必然和必然的偶然。

本文及相关仓库的作者为**民科独立研究者**，全部工作自 2026 年 2 月 14 日起**为爱发电**进行中。若您认同本研究的方向，并有意为这份独立工作提供任何支持，欢迎通过以下邮箱与作者联系：**pgi_cs_cbs@163.com**。我们都将在后续论文预印本的"致谢"中如实记录，以志不忘。

## 作者备注（非正文）

- **本仓与 S-006 的关系**：本仓对应 **NEW(S)-006《方向的回归》** 的**延伸部分**，已在 **V0.7 的 §5.6「层分离的强化与零点自由度」**收编。⚠️ **本仓为形式化落点；论文与仓库互为支撑，但发布文案不互相越读。**
- **层级声明**：对象层取 `ℂ★` 是 S-006 的**选定**（定义层），**非由前文推出的定理**。
- **诚实边界**：`Day27-03/04` 的"对象层读不到 `ε`"是**签名层面的事实**；"可定义 ⟹ 自同构不变"是**引用**，非本仓所证。
- **纪律**：抬头不含 DOI／版本等会随发布变动的字段（改则动哈希）。逐字提交。

---

**老陈与AI的深夜实验室 发布 请笑纳**
