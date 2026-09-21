import Mathlib

/-! ================================================================
   偏元数学 · Day27 · 残差不可消除 · 归零操作与统一平移
   ------------------------------------------------------------------
   核心：把「消残差」当作一次动作；由 A1（动作留差），该动作自己也留差 ⟹
         「归零操作」的输出恒为 ε（与输入无关），其唯一不动点是 ε，不是 0。
   本稿范围：① 归零操作的定义与其不动点；② 统一平移不能使两个不同残差同时归零。
   不做：不做「层分离」（为什么对象层看不见 ε）—— 该层未形式化，明标为开口。
   注：上承 Day26 prenary-math-lean-s3-direction-return。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay27

-- ① 归零操作：把 x 与其相反数相加（意图抵消），再叠加这次动作自身的残差 ε
--    这是 A1（动作留差：op(a) = op₀(a) + ε）在「抵消」这一动作上的直接实例
def zeroingOp (ε x : ℝ) : ℝ := x - x + ε

-- 定理1：归零操作的输出恒为 ε —— 与输入 x 无关
theorem zeroingOp_eq_eps (ε x : ℝ) : zeroingOp ε x = ε := by
  unfold zeroingOp
  ring

-- 定理2：0 不是归零操作的不动点（当 ε ≠ 0）
theorem zero_not_fixed (ε : ℝ) (hε : 0 < ε) : zeroingOp ε 0 ≠ 0 := by
  have h : zeroingOp ε 0 = ε := zeroingOp_eq_eps ε 0
  rw [h]
  exact ne_of_gt hε

-- 定理3：归零操作的唯一不动点是 ε（即「反复消」只会停在 ε）
theorem fixed_point_eq_eps (ε x : ℝ) (h : zeroingOp ε x = x) : x = ε := by
  rw [zeroingOp_eq_eps ε x] at h
  exact h.symm

-- 定理4：统一平移（同一常数 c 加于所有对象）不能使两个不同的残差同时归零
theorem uniform_shift_fails (ε₁ ε₂ c : ℝ) (h : ε₁ ≠ ε₂) :
    ¬ (ε₁ + c = 0 ∧ ε₂ + c = 0) := by
  rintro ⟨h1, h2⟩
  exact h (by linarith)

end PrenaryDay27
