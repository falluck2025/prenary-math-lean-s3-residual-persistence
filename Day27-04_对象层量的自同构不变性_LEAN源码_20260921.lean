import Mathlib

/-! ================================================================
   偏元数学 · Day27 · 残差不可消除 · 对象层可定义量的自同构不变性
   ------------------------------------------------------------------
   核心：把「对象层可定义」的判据落成一条可用的形式条件——
         「在对象层自同构下不变」（Padoa／自同构不变性，标准模型论原理）。
         由此：对象层能携带的实数量只能是常数 ⟹ 随动作变化的残差读不出来。
   本稿范围：① 平移不变 ⟹ 常值（引理）；② 对象层量在任意两点同值（推论）。
   不做：不做「可定义性」的一阶逻辑形式化本身（那需模型论工具，另立项）；
         本件把「可定义 ⟹ 自同构不变」作为**显式假设**使用。
   注：上承本日 Day27-03；本件把「层分离」的判据从「我们造的签名」移向「标准原理」。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay27D

-- ① 对象层（004 取 ℂ；S-006 细化为 ℂ★）
abbrev Obj := ℂ

-- ② 引理：平移不变的实函数必为常值
theorem translation_invariant_implies_const (f : Obj → ℝ)
    (h : ∀ c z, f (z + c) = f z) : ∃ k : ℝ, ∀ z, f z = k := by
  refine ⟨f 0, fun z => ?_⟩
  have hz : f (z + -z) = f z := h (-z) z
  simp only [add_neg_cancel] at hz
  exact hz.symm

-- ③ 定理：对象层可定义的实数量，在任意两点取值相同
--    （hdef ＝「对象层可定义」的形式判据；其内容即 Padoa／自同构不变性）
theorem obj_layer_quantity_same_value (f : Obj → ℝ)
    (hdef : ∀ c z, f (z + c) = f z) (z₁ z₂ : Obj) : f z₁ = f z₂ := by
  obtain ⟨k, hk⟩ := translation_invariant_implies_const f hdef
  rw [hk z₁, hk z₂]

end PrenaryDay27D
