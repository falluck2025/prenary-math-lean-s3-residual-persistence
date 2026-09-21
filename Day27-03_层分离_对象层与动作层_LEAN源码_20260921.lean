import Mathlib

/-! ================================================================
   偏元数学 · Day27 · 残差不可消除 · 层分离（对象层／动作层）· 类型骨架
   ------------------------------------------------------------------
   核心：把 004 的「对象层／动作层分离」落成**类型事实**——两层并列、互不定义；
         对象层的重标号（平移）在**签名上**就够不到动作层的残差 ε。
   本稿范围：① 两层并列的类型骨架；②「平移不改 ε」（类型事实，rfl 级）；
             ③ 层分离的 Padoa 形式（两世界：对象层相同、残差不同）。
   不做：不做「ε 在对象层不可定义」的模型论证明（需 Padoa／Beth，另立项）。
   注：上承本日 Day27-01、Day27-02。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay27C

-- ① 对象层：静态。004 取 ℂ（S-006 细化为 ℂ★＝挖去原点的复平面）
abbrev Obj := ℂ

-- ② 动作层：一次动作携带一个残差 ε（A1：动作留差，0 < ε < δ₀）
structure Act where
  eps : ℝ
  hpos : 0 < eps

-- ③ 世界：对象层的一个点 ＋ 动作层的一次动作
--    ⚠️ 两层**并列**：对象层不定义动作层，动作层不定义对象层
structure World where
  obj : Obj
  act : Act

-- ④ 两个世界：对象层相同、残差不同 —— 这是 Padoa 判据所需的「两模型」
def w₁ : World := ⟨1, ⟨1, by norm_num⟩⟩
-- ⚠️ 此处必须标 `noncomputable`：`(1 : ℝ) / 2` 依赖 `Real.instDivInvMonoid`，该实例为 noncomputable
noncomputable def w₂ : World := ⟨1, ⟨(1 : ℝ) / 2, by norm_num⟩⟩

-- 定理1：两世界的对象层相同
theorem padoa_same_obj : w₁.obj = w₂.obj := rfl

-- 定理2：两世界的残差不同
theorem padoa_diff_eps : w₁.act.eps ≠ w₂.act.eps := by
  have h₁ : w₁.act.eps = 1 := rfl
  have h₂ : w₂.act.eps = (1 : ℝ) / 2 := rfl
  rw [h₁, h₂]
  norm_num

-- 定理3（层分离 · Padoa 形式）：
--   任何只定义在**对象层类型** Obj 上的映射，无法区分这两个世界
theorem obj_map_cannot_see_eps {α : Type} (f : Obj → α) :
    f w₁.obj = f w₂.obj := by
  rw [padoa_same_obj]

-- ⑤ 对象层的重标号（平移）：只作用在 obj 上
def shiftObj (c : Obj) (w : World) : World := { w with obj := w.obj + c }

-- 定理4（平移够不着 ε）：对象层平移不改变动作层的残差
--   证明是 rfl 级 —— 因为「平移的签名里没有 act」
theorem shiftObj_eps_invariant (c : Obj) (w : World) :
    (shiftObj c w).act.eps = w.act.eps := rfl

end PrenaryDay27C
