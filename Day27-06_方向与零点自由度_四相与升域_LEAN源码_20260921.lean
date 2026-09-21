import Mathlib

/-! ================================================================
   偏元数学 · Day27 · 残差不可消除 · 方向：守住 ℤ₄ 与破缺（升域版）
   ------------------------------------------------------------------
   核心：残差「带不带方向」决定它在零点自由度关口站在哪一边——
         守住 ℤ₄（四个方向铺满圆）⟹ 合向量为零 ⟹ R̄ = 0（无偏好）；
         破缺 ℤ₄（缺一角）⟹ 合向量非零 ⟹ R̄ > 0（有偏好）；升域到 ℂ 之后，
         方向不全同的残差，不能被同一个统一平移同时归零。
   本稿范围：① 四相均匀合向量为零；② 破缺后合向量非零；③ 复数版「统一平移消不掉」。
   不做：不做标度律（√𝒩 与 R̄ 的定量关系，属另一件）；不主张「由物理四相导出 ℤ₄」（属候选层级）。
   注：上承本日 Day27-05；「守住 ℤ₄ 则 R̄ = 0」承 S3-D4《四相上的初心 · 破缺机制的落点》§2（严格结论）。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay27F

-- ① 四方向铺满（守住 ℤ₄）：合向量为零 ⟹ 无偏好（R̄ = 0）
theorem four_roots_sum_zero :
    (1 : ℂ) + Complex.I + (-1) + (-Complex.I) = 0 := by
  ring

-- ② 缺一角（破缺 ℤ₄）：合向量不再为零 ⟹ 有偏好（R̄ > 0）
theorem broken_symmetry_sum :
    (1 : ℂ) + Complex.I + (-1) + (0 : ℂ) = Complex.I := by
  ring

theorem broken_symmetry_nonzero :
    (1 : ℂ) + Complex.I + (-1) + (0 : ℂ) ≠ 0 := by
  rw [broken_symmetry_sum]
  exact Complex.I_ne_zero

-- ③ 升域版：方向不同（值不同）的两个残差，不能被同一个统一平移同时归零
theorem two_directions_not_shiftable (z w : ℂ) (h : z ≠ w) :
    ¬ ∃ c : ℂ, z + c = 0 ∧ w + c = 0 := by
  rintro ⟨c, h1, h2⟩
  apply h
  have hc : z + c = w + c := by rw [h1, h2]
  exact add_right_cancel hc

end PrenaryDay27F
