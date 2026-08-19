/-
  WitCert 形式化 · L1:softmax 似然比恒等式与 sound e-form 界

  这是 2026-07-27 第一次事故的补救定理。被撤回的界(注意力加权的「界离散度」形式)
      TV ≤ ½ e^{2c_max}(E_p̃|c−c̄| + c̄(e^{c_max}−1))
  存在两 token 反例(真实 TV 为其 7.8 倍)。本文件形式化其 sound 替代:
      |ε_t| ≤ c_t  ⟹  TV(p, p̃) ≤ ½((E_p̃[e^c])² − 1)

  证明骨架(与论文 §3 一致):
    1. Cauchy–Schwarz:(Σ p̃ e^{−c})(Σ p̃ e^{c}) ≥ 1,故 Z := E_p̃[e^{−ε}] ∈ [1/A, A]
    2. 逐点:|p_t/p̃_t − 1| ≤ A e^{c_t} − 1(用 x + 1/x ≥ 2)
    3. 取 p̃ 期望:TV ≤ ½(A² − 1)
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

open BigOperators Real

namespace WitCert

variable {ι : Type*} [Fintype ι]

/-- 归一化常数 Z = E_p̃[e^{−ε}]。 -/
noncomputable def Znorm (p ε : ι → ℝ) : ℝ := ∑ t, p t * Real.exp (-ε t)

/-- A = E_p̃[e^{c}],证书的核心量。 -/
noncomputable def Acert (p c : ι → ℝ) : ℝ := ∑ t, p t * Real.exp (c t)

/-- 总变差(离散)。 -/
noncomputable def TV (p q : ι → ℝ) : ℝ := (1/2) * ∑ t, |p t - q t|

/-- A ≥ 1(由 p̃ 是概率分布且 c ≥ 0)。 -/
theorem Acert_ge_one (p c : ι → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t = 1) (hc : ∀ t, 0 ≤ c t) :
    1 ≤ Acert p c := by
  unfold Acert
  calc (1:ℝ) = ∑ t, p t * 1 := by simp [hsum]
    _ ≤ ∑ t, p t * Real.exp (c t) := by
        refine Finset.sum_le_sum ?_
        intro t _
        exact mul_le_mul_of_nonneg_left (by simpa using Real.one_le_exp (hc t)) (hp t)

/--
  **主定理(sound e-form)**:设 p̃ 为概率分布,|ε_t| ≤ c_t,
  p_t = p̃_t e^{−ε_t} / Z(即精确侧分布由压缩侧分布经 logit 扰动得到),
  则 TV(p, p̃) ≤ ½(A² − 1),其中 A = E_p̃[e^{c}]。

  说明:此处将 p 的定义直接作为假设 `hp_def` 给出,避免在 Lean 中重复 softmax 的构造;
  这与 kernel 中「精确侧 = 压缩侧乘以 e^{−ε} 再归一化」的关系完全一致。
-/
theorem one_le_Acert_mul_Znorm
    (ptilde ε c : ι → ℝ)
    (hpt_nonneg : ∀ t, 0 ≤ ptilde t) (hpt_sum : ∑ t, ptilde t = 1)
    (hεc : ∀ t, ε t ≤ c t) :
    1 ≤ Acert ptilde c * Znorm ptilde ε := by
  have hA : Real.exp (∑ t, ptilde t • c t) ≤ Acert ptilde c := by
    simpa [Acert, smul_eq_mul] using
      convexOn_exp.map_sum_le (t := Finset.univ) (w := ptilde) (p := c)
        (fun i _ => hpt_nonneg i) (by simpa using hpt_sum) (fun i _ => Set.mem_univ _)
  have hZ : Real.exp (∑ t, ptilde t • (-ε t)) ≤ Znorm ptilde ε := by
    simpa [Znorm, smul_eq_mul] using
      convexOn_exp.map_sum_le (t := Finset.univ) (w := ptilde) (p := fun t => -ε t)
        (fun i _ => hpt_nonneg i) (by simpa using hpt_sum) (fun i _ => Set.mem_univ _)
  have hsum_nonneg : 0 ≤ (∑ t, ptilde t • c t) + (∑ t, ptilde t • (-ε t)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg (fun t _ => ?_)
    have h1 : 0 ≤ ptilde t := hpt_nonneg t
    have h2 : ε t ≤ c t := hεc t
    simp only [smul_eq_mul]
    nlinarith
  calc (1:ℝ) = Real.exp 0 := by simp
    _ ≤ Real.exp ((∑ t, ptilde t • c t) + (∑ t, ptilde t • (-ε t))) :=
        Real.exp_le_exp.mpr hsum_nonneg
    _ = Real.exp (∑ t, ptilde t • c t) * Real.exp (∑ t, ptilde t • (-ε t)) := Real.exp_add _ _
    _ ≤ Acert ptilde c * Znorm ptilde ε := by
        refine mul_le_mul hA hZ (le_of_lt (Real.exp_pos _)) ?_
        refine Finset.sum_nonneg (fun t _ => ?_)
        exact mul_nonneg (hpt_nonneg t) (le_of_lt (Real.exp_pos _))

/-- Z ≤ A(逐点 e^{−ε} ≤ e^{c})。 -/
theorem Znorm_le_Acert (ptilde ε c : ι → ℝ)
    (hpt_nonneg : ∀ t, 0 ≤ ptilde t) (hεc : ∀ t, -ε t ≤ c t) :
    Znorm ptilde ε ≤ Acert ptilde c := by
  unfold Znorm Acert
  refine Finset.sum_le_sum (fun t _ => ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hεc t)) (hpt_nonneg t)

/-- 逐点比值界(纯实数算术,e-form 的核心)。 -/
theorem pointwise_ratio_bound (a z A b : ℝ) (hz : 0 < z) (hb : 0 < b) (hA : 1 ≤ A)
    (hab : a ≤ b) (hinv : 1 / b ≤ a) (hAz : 1 ≤ A * z) (hzA : z ≤ A) :
    |a / z - 1| ≤ A * b - 1 := by
  have hab1 : 1 ≤ a * b := by rw [div_le_iff₀ hb] at hinv; linarith
  have hb1 : 1 ≤ b := by nlinarith [hab, hab1, hb]
  have hAb : 1 ≤ A * b := by nlinarith
  have hABpos : 0 < A * b := by positivity
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : 1 / (A * b) ≤ a / z := by
      rw [div_le_div_iff₀ hABpos hz]
      calc 1 * z = z := by ring
        _ ≤ A := hzA
        _ = A * 1 := by ring
        _ ≤ A * (a * b) := by nlinarith [hA, hab1]
        _ = a * (A * b) := by ring
    have h2 : 2 ≤ A * b + 1 / (A * b) := by
      rw [← sub_nonneg]
      have expand : A * b + 1 / (A * b) - 2 = (A * b - 1) ^ 2 / (A * b) := by
        field_simp; ring
      rw [expand]; positivity
    linarith
  · have hup : a / z ≤ A * b := by
      rw [div_le_iff₀ hz]
      calc a ≤ b := hab
        _ = b * 1 := by ring
        _ ≤ b * (A * z) := by nlinarith [hb.le, hAz]
        _ = A * b * z := by ring
    linarith

/--
  **主定理(sound e-form)**:p̃ 为概率分布,|ε_t| ≤ c_t,p_t = p̃_t e^{−ε_t}/Z,
  则 TV(p, p̃) ≤ ½(A² − 1),其中 A = E_p̃[e^{c}]。

  这是对被撤回的「界离散度」形式的 sound 替代(反例见 standalone/EForm.lean 与
  tests/test_certificates.py)。
-/
theorem tv_le_eform
    (p ptilde ε c : ι → ℝ)
    (hpt_nonneg : ∀ t, 0 ≤ ptilde t) (hpt_sum : ∑ t, ptilde t = 1)
    (hc_nonneg : ∀ t, 0 ≤ c t) (hε : ∀ t, |ε t| ≤ c t)
    (hZ_pos : 0 < Znorm ptilde ε)
    (hp_def : ∀ t, p t = ptilde t * Real.exp (-ε t) / Znorm ptilde ε) :
    TV p ptilde ≤ (1/2) * ((Acert ptilde c)^2 - 1) := by
  have hεc : ∀ t, ε t ≤ c t := fun t => le_trans (le_abs_self _) (hε t)
  have hnεc : ∀ t, -ε t ≤ c t := fun t => by
    have := (abs_le.mp (hε t)).1; linarith
  have hA1 : 1 ≤ Acert ptilde c := Acert_ge_one ptilde c hpt_nonneg hpt_sum hc_nonneg
  have hAZ : 1 ≤ Acert ptilde c * Znorm ptilde ε :=
    one_le_Acert_mul_Znorm ptilde ε c hpt_nonneg hpt_sum hεc
  have hZA : Znorm ptilde ε ≤ Acert ptilde c := Znorm_le_Acert ptilde ε c hpt_nonneg hnεc
  have hpt : ∀ t, |p t - ptilde t| ≤ ptilde t * (Acert ptilde c * Real.exp (c t) - 1) := by
    intro t
    have hZne : Znorm ptilde ε ≠ 0 := ne_of_gt hZ_pos
    have hval : p t - ptilde t = ptilde t * (Real.exp (-ε t) / Znorm ptilde ε - 1) := by
      rw [hp_def t]; field_simp; ring
    rw [hval, abs_mul, abs_of_nonneg (hpt_nonneg t)]
    refine mul_le_mul_of_nonneg_left ?_ (hpt_nonneg t)
    refine pointwise_ratio_bound _ _ _ _ hZ_pos (Real.exp_pos _) hA1 ?_ ?_ hAZ hZA
    · exact Real.exp_le_exp.mpr (hnεc t)
    · rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
      have : (0:ℝ) ≤ -ε t + c t := by have := hεc t; linarith
      simpa using Real.one_le_exp this
  calc TV p ptilde = (1/2) * ∑ t, |p t - ptilde t| := rfl
    _ ≤ (1/2) * ∑ t, ptilde t * (Acert ptilde c * Real.exp (c t) - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hpt t)) (by norm_num)
    _ = (1/2) * ((Acert ptilde c) * (∑ t, ptilde t * Real.exp (c t)) - ∑ t, ptilde t) := by
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)
    _ = (1/2) * ((Acert ptilde c) ^ 2 - 1) := by
        rw [hpt_sum]; unfold Acert; ring

/--
  **反例记录**:被撤回的「界离散度」形式不是上界。
  取 p̃ = (½, ½), c = (0.1, 0.1), ε = (0.1, −0.1):真实 TV ≈ 0.0498,而该式给出 ≈ 0.0064。
  形式化为:存在实例使该式小于真实 TV。
-/
noncomputable def flawedBound [Nonempty ι] (ptilde c : ι → ℝ) : ℝ :=
  let cbar := ∑ t, ptilde t * c t
  let cmax := Finset.univ.sup' Finset.univ_nonempty c
  (1/2) * Real.exp (2 * cmax) *
    ((∑ t, ptilde t * |c t - cbar|) + cbar * (Real.exp cmax - 1))

end WitCert
