import Mathlib

/-! ================================================================
   偏元数学 · Day27-07 · S-006 底下的层分离：对象层 ℂ★ 与它的自同构
   ------------------------------------------------------------------
   核心：把 Day27-03/04 从 004 底（对象层 ℂ）搬到 S-006 底（对象层 ℂ★）——
         ① 平移**不是** ℂ★ 的自同构（存在点被译出对象层，落进缺陷点 0）；
         ② ℂ★ 的自同构是**乘性缩放**（a ∈ ℂˣ），且它在 ℂ★ 上可迁；
         ③ ⟹ 乘性不变的实函数必为常值 —— 层分离在 S-006 底上依然成立，
            且更强：连"径向"都读不出（旋转也在自同构群里）。
   ——对应 B1-3-02（2026-09-12）那句"单向平移会消除 ε 但在数学层不合法"，本件是它的形式化。
   本稿范围：对象层 ℂ★ 的自同构群与其不变函数（四条）。
   不做：不做覆叠／路径提升（A2′）本身 —— 归 Day26-03/04。
   注：上承本日 Day27-03、Day27-04；对象层取 NEW(S)-006 A0（定义 1）。
   日期：2026-09-21
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ⚠️ 改稿记录（2026-09-21）：① 一稿 → 二稿：`λ` 为 Lean 保留记号，缩放参数改名 `a`；
                            ② 二稿 → 三稿：第 ② 条证明改用 `simp`（消 `unnecessarySimpa` 警告）。
   ================================================================ -/

namespace PrenaryDay27G

-- ① 对象层 ℂ★（S-006 定义 1 / A0）：复平面挖去原点
abbrev ObjS : Type := { z : ℂ // z ≠ 0 }

-- ② 平移不是 ℂ★ 的自同构：存在对象层的点，平移后落进缺陷点（不可定义）
--    读法：把 Day27-04 的"平移"搬到 ℂ★ 上，它连函数都写不完整。
theorem shift_not_automorphism (c : ℂ) (hc : c ≠ 0) :
    ∃ z : ObjS, (z : ℂ) + c = 0 := by
  refine ⟨⟨-c, neg_ne_zero.mpr hc⟩, ?_⟩
  simp

-- ③ 乘性缩放是 ℂ★ 的自同构（a ≠ 0）
--    读法：ℂ★ 上真正"搬得动点"的操作是乘法，不是加法。
def scaleS (a : ℂ) (ha : a ≠ 0) (z : ObjS) : ObjS :=
  ⟨a * (z : ℂ), mul_ne_zero ha z.2⟩

-- ④ 乘性缩放的作用在 ℂ★ 上可迁：任两点可被一次缩放相连
theorem scale_transitive (z w : ObjS) : ∃ a : ℂ, a ≠ 0 ∧ a * (z : ℂ) = (w : ℂ) := by
  refine ⟨(w : ℂ) * ((z : ℂ))⁻¹, mul_ne_zero w.2 (inv_ne_zero z.2), ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ z.2, mul_one]

-- ⑤ ⟹ 乘性不变的实函数必为常值（层分离：对象层读不出任何非常值的量）
theorem scale_invariant_implies_const (f : ObjS → ℝ)
    (h : ∀ a (ha : a ≠ 0) (z : ObjS), f (scaleS a ha z) = f z) :
    ∃ k : ℝ, ∀ z : ObjS, f z = k := by
  refine ⟨f ⟨1, one_ne_zero⟩, fun z => ?_⟩
  have hz : scaleS ((z : ℂ)⁻¹) (inv_ne_zero z.2) z = ⟨1, one_ne_zero⟩ := by
    apply Subtype.ext
    simp only [scaleS, Subtype.coe_mk]
    exact inv_mul_cancel₀ z.2
  rw [← h ((z : ℂ)⁻¹) (inv_ne_zero z.2) z, hz]

end PrenaryDay27G
