import Mathlib

/-! ================================================================
   偏元数学 · Day27 · 残差不可消除 · 相消不完全（第三种结果的存在性）
   ------------------------------------------------------------------
   核心：理想相消 a + (−a) = 0；但相消是一次动作，由 A1 它留下 ε ⟹
         实际结果为 ε ≠ 0 ⟹「第三种结果」存在。
   本稿范围：只形式化「存在性」（相消不能完全 ⟹ 有非零余项）。
   不做：不做「频率／概率」—— p = p(ε) 的函数形式未定，且 ε 的数值未定，该半明标为开口。
   注：上承本日 Day27-01；本件与 Day27-01 同源（都只用 A1 与 A3）。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay27B

-- ① 理想相消：两份贡献互为相反数，合计为零
def idealCancel (a : ℝ) : ℝ := a + (-a)

-- 定理1：理想相消恒为零
theorem idealCancel_eq_zero (a : ℝ) : idealCancel a = 0 := by
  unfold idealCancel
  ring

-- ② 实际相消：理想相消之后，再叠加这次动作自身的残差 ε
def actualCancel (a ε : ℝ) : ℝ := idealCancel a + ε

-- 定理2：实际相消的余项恒为 ε（与 a 无关）
theorem actualCancel_eq_eps (a ε : ℝ) : actualCancel a ε = ε := by
  unfold actualCancel idealCancel
  ring

-- 定理3：ε ≠ 0 ⟹ 实际相消不为零 —— 即「第三种结果」存在
theorem actualCancel_ne_zero (a ε : ℝ) (hε : ε ≠ 0) : actualCancel a ε ≠ 0 := by
  rw [actualCancel_eq_eps]
  exact hε

end PrenaryDay27B
