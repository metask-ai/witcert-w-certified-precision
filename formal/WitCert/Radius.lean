/-
  WitCert 形式化 · L9:**E2 半径的分析核心**(F3)

  实现(extract.dsv4_certified_write, dither 臂)的先验半径

      u_e = Σ_b √(Σ_{c∈b} θ_c(1−θ_c)Δ_c²)          (均值项,Jensen)
          + √(2·(Σ_c Δ_c²/4)·ln(n/δ_i))             (尾项,sub-Gaussian)
          + Σ_b ‖det_c‖                              (顶部夹取确定项)

  三个数学要件,常数与实现**逐字对上**:
    1. `two_point_mgf_le`:两点 Hoeffding 引理 —— 均值为零、支撑 {−pΔ,(1−p)Δ} 的
       SR 残差满足 E[e^{λX}] ≤ e^{λ²Δ²/8},即 sub-G 参数 σ² = Δ²/4(= 实现的 rng2)。
       **证明零测度论**:对 F(h)=log((1−p)e^{−ph}+pe^{(1−p)h}) 显式给出
       F'' = p(1−p)E₁E₂ / g² ≤ 1/4(AM-GM),再由导数单调性收拢 —— 不引 Taylor、
       不引鞅论,MeanValue 一条龙。
    2. `two_point_variance`:Var X = θ(1−θ)Δ²(实现的 var_ex),恒等式。
    3. `sq_sum_weighted_le`:(Σ p·x)² ≤ Σ p·x²(权重和 1)—— 均值项 Jensen 步
       E‖d_b‖ ≤ √E‖d_b‖² 的有限形式。

  W_e = Σ_b ‖d_b‖ 是坐标的**非线性**函数,尾项对它 sound 的
  bounded-difference(McDiarmid)论证在 McDiarmid.lean(L10)—— 递归条件期望、
  一般区间 Hoeffding(凸性化归到本文件的两点引理)、与实现同形的半径,
  以及均值项 witness_mean_le,均已机器检查。本文件是其分析地基。
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

open Real

namespace WitCert.Calculus.Radius

/-! ### 1. 两点 Hoeffding 引理(σ² = Δ²/4,常数 1/8) -/

/-- 两点 MGF(对数内层):g_p(h) = (1−p)e^{−ph} + p·e^{(1−p)h}。
    这是均值为零、以概率 p 取 (1−p)Δ / 以概率 1−p 取 −pΔ 的 SR 残差在 h=λΔ 处的 MGF。 -/
noncomputable def g (p h : ℝ) : ℝ := (1 - p) * exp (-(p * h)) + p * exp ((1 - p) * h)

/-- g 的一阶导。 -/
noncomputable def gd (p h : ℝ) : ℝ := p * (1 - p) * (exp ((1 - p) * h) - exp (-(p * h)))

/-- g 的二阶导。 -/
noncomputable def gdd (p h : ℝ) : ℝ :=
  p * (1 - p) * ((1 - p) * exp ((1 - p) * h) + p * exp (-(p * h)))

lemma g_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) : 0 < g p h := by
  unfold g
  rcases lt_or_eq_of_le hp1 with h1 | h1
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (exp_pos _))
      (mul_nonneg hp (exp_pos _).le)
  · rw [h1]; norm_num

lemma g_zero (p : ℝ) : g p 0 = 1 := by unfold g; simp

lemma hasDerivAt_g (p h : ℝ) : HasDerivAt (g p) (gd p h) h := by
  have h1 : HasDerivAt (fun x : ℝ => -(p * x)) (-p) h := by
    simpa using ((hasDerivAt_id h).const_mul p).neg
  have h2 : HasDerivAt (fun x : ℝ => (1 - p) * x) (1 - p) h := by
    simpa using (hasDerivAt_id h).const_mul (1 - p)
  have hsum := (h1.exp.const_mul (1 - p)).add (h2.exp.const_mul p)
  show HasDerivAt (fun x => (1 - p) * exp (-(p * x)) + p * exp ((1 - p) * x)) (gd p h) h
  convert hsum using 1
  unfold gd; ring

lemma hasDerivAt_gd (p h : ℝ) : HasDerivAt (gd p) (gdd p h) h := by
  have h1 : HasDerivAt (fun x : ℝ => -(p * x)) (-p) h := by
    simpa using ((hasDerivAt_id h).const_mul p).neg
  have h2 : HasDerivAt (fun x : ℝ => (1 - p) * x) (1 - p) h := by
    simpa using (hasDerivAt_id h).const_mul (1 - p)
  have hsub := (h2.exp.sub h1.exp).const_mul (p * (1 - p))
  show HasDerivAt (fun x => p * (1 - p) * (exp ((1 - p) * x) - exp (-(p * x)))) (gdd p h) h
  convert hsub using 1
  unfold gdd; ring

/-- 对数矩函数的一阶导:φ = g'/g。 -/
noncomputable def phi (p h : ℝ) : ℝ := gd p h / g p h

lemma phi_zero (p : ℝ) : phi p 0 = 0 := by unfold phi gd; simp

lemma hasDerivAt_phi {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    HasDerivAt (phi p)
      ((gdd p h * g p h - gd p h * gd p h) / g p h ^ 2) h := by
  have := (hasDerivAt_gd p h).div (hasDerivAt_g p h) (g_pos hp hp1 h).ne'
  simpa [phi] using this

/-- **核心恒等式**:F''·g² = g''g − g'² = p(1−p)·E₁E₂ —— 这就是 tilted Bernoulli
    的方差表示;AM-GM 立即给出 F'' ≤ 1/4,即 Hoeffding 常数 1/8 的来源。 -/
lemma second_deriv_num_eq (p h : ℝ) :
    gdd p h * g p h - gd p h * gd p h
      = p * (1 - p) * (exp (-(p * h)) * exp ((1 - p) * h)) := by
  unfold g gd gdd; ring

lemma phi_deriv_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    0 ≤ (gdd p h * g p h - gd p h * gd p h) / g p h ^ 2 := by
  rw [second_deriv_num_eq]
  have h1 : (0:ℝ) ≤ p * (1 - p) := mul_nonneg hp (by linarith)
  positivity

lemma phi_deriv_le_quarter {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    (gdd p h * g p h - gd p h * gd p h) / g p h ^ 2 ≤ 1 / 4 := by
  have hg := g_pos hp hp1 h
  rw [second_deriv_num_eq, div_le_iff₀ (by positivity)]
  have hE1 := exp_pos (-(p * h))
  have hE2 := exp_pos ((1 - p) * h)
  unfold g
  nlinarith [sq_nonneg ((1 - p) * exp (-(p * h)) - p * exp ((1 - p) * h)),
             mul_pos hE1 hE2]

/-- φ 的斜率界:0 ≤ t → φ(t) ≤ t/4(由 φ(0)=0 与 φ' ≤ 1/4 单调收拢)。 -/
lemma phi_le_quarter_mul {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    phi p t ≤ t / 4 := by
  set ψ : ℝ → ℝ := fun x => x / 4 - phi p x with hψdef
  have hψ : ∀ x, HasDerivAt ψ
      (1 / 4 - (gdd p x * g p x - gd p x * gd p x) / g p x ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y / 4) (1 / 4) x := by
      simpa using (hasDerivAt_id x).div_const 4
    exact h1.sub (hasDerivAt_phi hp hp1 x)
  have hmono : Monotone ψ := by
    refine monotone_of_deriv_nonneg (fun x => (hψ x).differentiableAt) (fun x => ?_)
    rw [(hψ x).deriv]
    linarith [phi_deriv_le_quarter hp hp1 x]
  have := hmono ht
  simpa [hψdef, phi_zero] using this

/-- 对称侧:t ≤ 0 → t/4 ≤ φ(t)。 -/
lemma quarter_mul_le_phi {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ} (ht : t ≤ 0) :
    t / 4 ≤ phi p t := by
  set ψ : ℝ → ℝ := fun x => x / 4 - phi p x with hψdef
  have hψ : ∀ x, HasDerivAt ψ
      (1 / 4 - (gdd p x * g p x - gd p x * gd p x) / g p x ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y / 4) (1 / 4) x := by
      simpa using (hasDerivAt_id x).div_const 4
    exact h1.sub (hasDerivAt_phi hp hp1 x)
  have hmono : Monotone ψ := by
    refine monotone_of_deriv_nonneg (fun x => (hψ x).differentiableAt) (fun x => ?_)
    rw [(hψ x).deriv]
    linarith [phi_deriv_le_quarter hp hp1 x]
  have := hmono ht
  simpa [hψdef, phi_zero] using this

/-- **对数形式**:log g_p(h) ≤ h²/8(∀ p ∈ [0,1], ∀ h)。 -/
theorem log_two_point_mgf_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    log (g p h) ≤ h ^ 2 / 8 := by
  set H : ℝ → ℝ := fun x => x ^ 2 / 8 - log (g p x) with hHdef
  have hderiv : ∀ x, HasDerivAt H (x / 4 - phi p x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 8) (x / 4) x := by
      have := (hasDerivAt_pow 2 x).div_const 8
      convert this using 1
      simp; ring
    have h2 : HasDerivAt (fun y => log (g p y)) (gd p x / g p x) x :=
      (hasDerivAt_g p x).log (g_pos hp hp1 x).ne'
    exact h1.sub h2
  have hH0 : H 0 = 0 := by simp [hHdef, g_zero]
  have hdiff : Differentiable ℝ H := fun x => (hderiv x).differentiableAt
  have key : 0 ≤ H h := by
    rcases le_total 0 h with hh | hh
    · have hmono : MonotoneOn H (Set.Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
          hdiff.continuous.continuousOn
          (hdiff.differentiableOn) (fun x hx => ?_)
        rw [interior_Ici] at hx
        rw [(hderiv x).deriv]
        linarith [phi_le_quarter_mul hp hp1 (le_of_lt hx)]
      have := hmono Set.left_mem_Ici (Set.mem_Ici.mpr hh) hh
      linarith [hH0 ▸ this]
    · have hanti : AntitoneOn H (Set.Iic 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
          hdiff.continuous.continuousOn
          (hdiff.differentiableOn) (fun x hx => ?_)
        rw [interior_Iic] at hx
        rw [(hderiv x).deriv]
        linarith [quarter_mul_le_phi hp hp1 (le_of_lt hx)]
      have := hanti (Set.mem_Iic.mpr hh) Set.right_mem_Iic hh
      linarith [hH0 ▸ this]
  have : log (g p h) ≤ h ^ 2 / 8 - 0 := by
    simpa [hHdef] using key
  linarith

/-- **两点 Hoeffding 引理**(MGF 形式):(1−p)e^{−ph} + p·e^{(1−p)h} ≤ e^{h²/8}。 -/
theorem two_point_mgf_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    (1 - p) * exp (-(p * h)) + p * exp ((1 - p) * h) ≤ exp (h ^ 2 / 8) :=
  (Real.log_le_iff_le_exp (g_pos hp hp1 h)).mp (log_two_point_mgf_le hp hp1 h)

/-- **SR 残差实例化**:X ∈ {−θΔ, (1−θ)Δ},P(上格点)=θ(条件均值恰零),则
    E[e^{λX}] ≤ e^{λ²Δ²/8} —— sub-G 参数 σ² = Δ²/4,即实现中 rng2 = Δ²/4 的出处。 -/
theorem sr_mgf_le {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (Δ lam : ℝ) :
    (1 - θ) * exp (lam * (-(θ * Δ))) + θ * exp (lam * ((1 - θ) * Δ))
      ≤ exp (lam ^ 2 * Δ ^ 2 / 8) := by
  have := two_point_mgf_le hθ hθ1 (lam * Δ)
  have e1 : lam * (-(θ * Δ)) = -(θ * (lam * Δ)) := by ring
  have e2 : lam * ((1 - θ) * Δ) = (1 - θ) * (lam * Δ) := by ring
  have e3 : (lam * Δ) ^ 2 / 8 = lam ^ 2 * Δ ^ 2 / 8 := by ring
  rw [e1, e2, e3.symm]
  exact this

/-! ### 2. 两点方差(均值项的 var_ex) -/

/-- **两点方差恒等式**:E[X²] = (1−θ)(θΔ)² + θ((1−θ)Δ)² = θ(1−θ)Δ²。
    实现中 var_ex = θ(1−θ)Δ² 逐坐标即此;比旧 uniform-dither 代理 s²/3 紧的根源。 -/
theorem two_point_variance (θ Δ : ℝ) :
    (1 - θ) * (θ * Δ) ^ 2 + θ * ((1 - θ) * Δ) ^ 2 = θ * (1 - θ) * Δ ^ 2 := by
  ring

/-! ### 3. 加权 Jensen(均值项的 band 求和步) -/

/-- **加权 Cauchy-Schwarz / Jensen**:权重和为 1 时 (Σ pᵢxᵢ)² ≤ Σ pᵢxᵢ²。
    均值项 E‖d_b‖ ≤ √(E‖d_b‖²) = √(Σ Var) 的有限概率空间形式。 -/
theorem sq_sum_weighted_le {ι : Type*} (s : Finset ι) (p x : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, p i * x i) ^ 2 ≤ ∑ i ∈ s, p i * x i ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (f := fun i => p i) (g := fun i => p i * x i ^ 2) (r := fun i => p i * x i)
    hp (fun i hi => mul_nonneg (hp i hi) (sq_nonneg _))
    (fun i hi => by ring)
  simpa [hsum] using h

/-! ### 4. 半径组合(标量骨架;概率层见 Ledger.stream_sound / Ville) -/

/-- **确定项平移**:若实现残差 W ≤ 随机部界 R + 确定项 D(逐实现),
    则 W > R + D' 的实现蕴含 R 部越界,只要 D ≤ D'。
    顶部夹取(lo=hi≠x)的 det_e 项以此并入半径:不占 δ,纯平移。 -/
theorem det_shift_sound {W R D D' : ℝ} (hsplit : W ≤ R + D) (hD : D ≤ D') :
    W ≤ R + D' := by linarith

end WitCert.Calculus.Radius
