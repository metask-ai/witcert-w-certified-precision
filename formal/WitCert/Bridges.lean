/-
  WitCert 形式化 · L6:**两座桥** —— 让 存储见证 → 注意力 TV 的组合合法化

  背景:度量类型检查(WitCert/Contract.lean)拒绝了论文2 原来的链 ——
  存储段输出 kv_entry:rel_witness(无量纲比值),选择段输入 attn_dist:tv(概率质量),
  `a₂·b₁+b₂` 把两个没有共同单位的数相加。要让请求级证书复活,必须补出:

    ① witness → score   打分桥:|Δ(scale·⟨q,k⟩)| ≤ scale·‖q‖·‖Δk‖(Cauchy–Schwarz)
       系数 scale·‖q‖ 是**运行时量**,由 dsv4-qnorm 探针采(p75)。
    ② score → tv        softmax 桥:‖Δs‖∞ ≤ ε ⟹ TV ≤ ½(e^{2ε}−1)
       **不另证** —— 它是论文1 主定理 tv_le_eform 的指数倾斜实例化:
       softmax(s') 恰是 softmax(s) 的 e^{−ε} 倾斜,均匀 c ≡ ε 时 A = e^ε。
    ③ 仿射松弛:½(e^{2ε}−1) ≤ e^{2ε₀}·ε 当 0 ≤ ε ≤ ε₀
       Chain 只会仿射组合,非线性界要以"带前提的仿射系数"进链;
       前提 ε ≤ ε₀ 由运行时检查(ε₀ 取实测上界),这正是 partial 档的定义。

  这三条对应 Python 侧 contracts.py 的 proof 字段;桥的**系数**是否如实来自运行时,
  由 contract checker 与实验负责,不在本文件的背书范围内。
-/
import WitCert.SoftmaxTV
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators Real

namespace WitCert.Calculus

variable {ι : Type*} [Fintype ι]

/-! ### ① 打分桥(Cauchy–Schwarz) -/

/--
  **打分桥**:score = scale·(q·k) 对条目扰动的敏感度(求和形式,与实现逐字对应)。
  右边两个因子都运行时可得:scale·√(∑q²) 由 qnorm 探针采,√(∑Δ²) 由带范数见证 W 上界。
-/
theorem score_bridge {d : ℕ} (q k k' : Fin d → ℝ) (scale : ℝ) (hs : 0 ≤ scale) :
    |scale * (∑ i, q i * k i) - scale * (∑ i, q i * k' i)|
      ≤ scale * Real.sqrt (∑ i, q i ^ 2) * Real.sqrt (∑ i, (k i - k' i) ^ 2) := by
  have hd : scale * (∑ i, q i * k i) - scale * (∑ i, q i * k' i)
      = scale * ∑ i, q i * (k i - k' i) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcs_pos : ∑ i, q i * (k i - k' i)
      ≤ Real.sqrt (∑ i, q i ^ 2) * Real.sqrt (∑ i, (k i - k' i) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hcs_neg : -(∑ i, q i * (k i - k' i))
      ≤ Real.sqrt (∑ i, q i ^ 2) * Real.sqrt (∑ i, (k i - k' i) ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ q (fun i => -(k i - k' i))
    have he : ∑ i, q i * -(k i - k' i) = -(∑ i, q i * (k i - k' i)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsq : ∑ i, (-(k i - k' i)) ^ 2 = ∑ i, (k i - k' i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [he, hsq] at h
    exact h
  rw [hd, abs_mul, abs_of_nonneg hs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hs
  exact abs_le.mpr ⟨by linarith, hcs_pos⟩

/-! ### ② softmax 桥(tv_le_eform 的实例化) -/

/-- softmax(离散,全支撑)。 -/
noncomputable def softmax (s : ι → ℝ) : ι → ℝ :=
  fun t => Real.exp (s t) / ∑ u, Real.exp (s u)

lemma softmax_nonneg (s : ι → ℝ) (t : ι) : 0 ≤ softmax s t :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma sum_exp_pos [Nonempty ι] (s : ι → ℝ) : 0 < ∑ u, Real.exp (s u) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma softmax_sum [Nonempty ι] (s : ι → ℝ) : ∑ t, softmax s t = 1 := by
  unfold softmax
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (sum_exp_pos s))

/-- 逐项恒等式:p̃_t·e^{s'_t − s_t} = e^{s'_t}/Z_s —— 倾斜的代数核心,单独立引理。 -/
lemma softmax_tilt (s s' : ι → ℝ) (t : ι) :
    softmax s t * Real.exp (-(s t - s' t)) = Real.exp (s' t) / ∑ u, Real.exp (s u) := by
  unfold softmax
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

/--
  **softmax TV 桥**:分数逐项扰动不超过 ε(ε ≥ 0),则分布全变差 ≤ ½(e^{2ε} − 1)。

  证明是**实例化而非另证**:取 p̃ = softmax s、p = softmax s'、ε_t = s t − s' t、
  c ≡ ε,则 p 恰是 p̃ 的 e^{−ε_t}/Z 倾斜(Z = Z_{s'}/Z_s),A = E_p̃[e^ε] = e^ε,
  论文1 的 tv_le_eform 直接给出 TV ≤ ½(A²−1) = ½(e^{2ε}−1)。
-/
theorem softmax_tv_bridge [Nonempty ι] (s s' : ι → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (h : ∀ t, |s t - s' t| ≤ ε) :
    WitCert.TV (softmax s') (softmax s) ≤ (1/2) * (Real.exp ε ^ 2 - 1) := by
  have hZs := sum_exp_pos s
  have hZs' := sum_exp_pos s'
  -- Znorm (softmax s) (s − s') = Z_{s'} / Z_s
  have hZnorm : WitCert.Znorm (softmax s) (fun t => s t - s' t)
      = (∑ u, Real.exp (s' u)) / ∑ u, Real.exp (s u) := by
    unfold WitCert.Znorm
    calc ∑ t, softmax s t * Real.exp (-(s t - s' t))
        = ∑ t, Real.exp (s' t) / ∑ u, Real.exp (s u) :=
          Finset.sum_congr rfl fun t _ => softmax_tilt s s' t
      _ = (∑ t, Real.exp (s' t)) / ∑ u, Real.exp (s u) := by rw [Finset.sum_div]
  have hZpos : 0 < WitCert.Znorm (softmax s) (fun t => s t - s' t) := by
    rw [hZnorm]; positivity
  -- Acert (softmax s) (c ≡ ε) = e^ε
  have hA : WitCert.Acert (softmax s) (fun _ => ε) = Real.exp ε := by
    unfold WitCert.Acert
    rw [← Finset.sum_mul, softmax_sum, one_mul]
  have := WitCert.tv_le_eform (softmax s') (softmax s)
    (fun t => s t - s' t) (fun _ => ε)
    (softmax_nonneg s) (softmax_sum s)
    (fun _ => hε0) h hZpos
    (by
      intro t
      show softmax s' t = softmax s t * Real.exp (-(s t - s' t))
          / WitCert.Znorm (softmax s) (fun t => s t - s' t)
      rw [hZnorm, softmax_tilt s s' t]
      unfold softmax
      rw [div_div_div_cancel_right₀]
      exact ne_of_gt hZs)
  rwa [hA] at this

/-! ### ③ 仿射松弛(非线性界进仿射链的许可证) -/

/-- `e^x − 1 ≤ x·e^x`(x ≥ 0):由 `1 − x ≤ e^{−x}` 两边乘 `e^x`。 -/
lemma exp_sub_one_le_mul_exp {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)          -- −x + 1 ≤ e^{−x}
  have hpos := Real.exp_pos x
  have hmul : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_right h hpos.le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  nlinarith

/--
  **仿射松弛**:0 ≤ ε ≤ ε₀ 时 ½(e^{2ε} − 1) ≤ e^{2ε₀}·ε。

  这是"softmax 桥"以仿射契约 (a, b) = (e^{2ε₀}, 0) 进链的许可证;
  前提 ε ≤ ε₀ 必须由运行时检查 —— 这正是该契约档位为 partial 的原因。
-/
theorem tv_affine_relax {ε ε₀ : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ ε₀) :
    (1/2) * (Real.exp ε ^ 2 - 1) ≤ Real.exp (2 * ε₀) * ε := by
  have h2 : Real.exp ε ^ 2 = Real.exp (2 * ε) := by
    rw [pow_two, ← Real.exp_add]; ring_nf
  rw [h2]
  have h3 : Real.exp (2 * ε) - 1 ≤ (2 * ε) * Real.exp (2 * ε) :=
    exp_sub_one_le_mul_exp (by linarith)
  have h4 : Real.exp (2 * ε) ≤ Real.exp (2 * ε₀) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (2 * ε), Real.exp_pos (2 * ε₀)]

/--
  **端到端桥(打包版,供论文引用)**:分数扰动 ε ∈ [0, ε₀] 时
      TV(softmax s', softmax s) ≤ e^{2ε₀} · ε。
  与 ① 相接:ε = scale·‖q‖·W,系数全部运行时可采。
-/
theorem softmax_tv_affine [Nonempty ι] (s s' : ι → ℝ) (ε ε₀ : ℝ)
    (hε0 : 0 ≤ ε) (hεb : ε ≤ ε₀) (h : ∀ t, |s t - s' t| ≤ ε) :
    WitCert.TV (softmax s') (softmax s) ≤ Real.exp (2 * ε₀) * ε :=
  le_trans (softmax_tv_bridge s s' ε hε0 h) (tv_affine_relax hε0 hεb)

/-! ### ④ 门控 → served(①c 增量:把"采样统计量 W"换成"门控保证 wthr")

  背景(评审第九轮后 ①c 命门):现有桥 ①②把逐读 served-TV 界成
  ½(e^{2ε}−1),ε = scale·‖q‖·W。但 W 与 a=scale·‖q‖ 都是**采样分布统计量**
  (contracts.py 的 caliber 明写),采样最大 W≈0.70 使 ε≈0.70、界≈1.53 **空洞**。

  本节的观察:**物理门控 `auth = u_e ≤ wthr` 对每个被授权 key 保证见证
  ‖Δk‖ ≤ W ≤ u_e ≤ wthr**(extract.py:615;实测 n_auth_violations=0 即
  W_real ≤ u_e)。于是把 ε 里的 W 换成**门控常数 wthr**,得到一个对**所有**
  被授权读**by construction** 成立的逐读 served-TV 天花板:

      TV ≤ ½(e^{2·a_q·wthr} − 1)   (a_q 仍是查询包络,运行时采)

  这不是新数学,是把已证的 ①② 桥在**门控保证的前提**下实例化 —— 逐读那
  一层从"原则 sound / 经验 0.935"升为"门槛 wthr 参数化的 sound 律"。
  累计那一层仍开放(TV 跨读不可加),本节不触及。 -/

/--
  **门控→served 定理**:单个查询 `q` 读一批 key(精确 `k` / 压缩 `k'`),
  分数 `s_t = scale·⟨q,k_t⟩`。若查询包络 `scale·‖q‖ ≤ a_q`,且**物理门控**
  保证每个 key 的残差 `‖Δk_t‖ ≤ wthr`,则该读的注意力分布 TV
  `≤ ½(e^{2·a_q·wthr} − 1)`。证明是 `score_bridge` + `softmax_tv_bridge`
  在门控前提下的复合。 -/
theorem served_tv_le_of_gate {d : ℕ} [Nonempty ι]
    (s s' : ι → ℝ) (q : Fin d → ℝ) (k k' : ι → Fin d → ℝ) (scale aq wthr : ℝ)
    (hscale : 0 ≤ scale) (haq : 0 ≤ aq) (hw : 0 ≤ wthr)
    (hs  : ∀ t, s t  = scale * ∑ i, q i * k t i)
    (hs' : ∀ t, s' t = scale * ∑ i, q i * k' t i)
    (hqbound : scale * Real.sqrt (∑ i, q i ^ 2) ≤ aq)
    (hgate : ∀ t, Real.sqrt (∑ i, (k t i - k' t i) ^ 2) ≤ wthr) :
    WitCert.TV (softmax s') (softmax s) ≤ (1/2) * (Real.exp (aq * wthr) ^ 2 - 1) := by
  refine softmax_tv_bridge s s' (aq * wthr) (mul_nonneg haq hw) (fun t => ?_)
  rw [hs t, hs' t]
  refine le_trans (score_bridge q (k t) (k' t) scale hscale) ?_
  exact mul_le_mul hqbound (hgate t) (Real.sqrt_nonneg _) haq

/--
  **设计律(反解,e-form 版)**:给定逐读 served-TV 目标 `τ* ≥ 0` 与查询包络
  `a_q > 0`,门槛设 `wthr ≤ ln(1+2τ*)/(2·a_q)` ⟹ `served_tv_le_of_gate` 天花板
  `≤ τ*`。tanh 版更紧(`served_tv_le_of_gate_tanh`,反解 wthr*=atanh(τ*)/a_q)。
  数字见 w3sb_served_readbound.json(caliber 自洽:a_q 与见证同一测量)。 -/
theorem gate_threshold_for_sla (aq wthr tstar : ℝ)
    (haq : 0 < aq) (htau : 0 ≤ tstar)
    (hset : wthr ≤ Real.log (1 + 2 * tstar) / (2 * aq)) :
    (1/2) * (Real.exp (aq * wthr) ^ 2 - 1) ≤ tstar := by
  have h2aq : 0 < 2 * aq := by linarith
  have hlog : 2 * aq * wthr ≤ Real.log (1 + 2 * tstar) := by
    have := (le_div_iff₀ h2aq).mp hset
    nlinarith [this]
  have hpos : (0:ℝ) < 1 + 2 * tstar := by linarith
  have hexp : Real.exp (2 * aq * wthr) ≤ 1 + 2 * tstar := by
    calc Real.exp (2 * aq * wthr)
        ≤ Real.exp (Real.log (1 + 2 * tstar)) := Real.exp_le_exp.mpr hlog
      _ = 1 + 2 * tstar := Real.exp_log hpos
  have hsq : Real.exp (aq * wthr) ^ 2 = Real.exp (2 * aq * wthr) := by
    rw [pow_two, ← Real.exp_add]; ring_nf
  rw [hsq]; linarith

/-! ### ⑤ tanh 紧化(替代过松的 e-form ½(e^{2ε}−1))

  观察:softmax 桥用的 ½(e^{2ε}−1) 来自逐点粗界 p'/p̃ ≤ e^{2ε},对大 ε **爆炸**
  (ε=2 时 26.8),而真实 TV 恒 ≤ 1。用弦(moment)论证可得**一致更紧且非空洞**
  的界:令 w_t=p_t/p̃_t∈[L,U]=[e^{−2ε},e^{2ε}]、E_p̃[w]=1,则 |w−1| 凸 ⟹ 落在端点
  弦下 ⟹ TV ≤ (1−L)(U−1)/(U−L) = (e^{2ε}−1)/(e^{2ε}+1) = tanh(ε)。
  证 tanh(ε) ≤ ½(e^{2ε}−1):比值 2/(e^{2ε}+1) ≤ 1。(数值验证真 sup 为更紧的
  tanh(ε/2),需 Z 耦合;tanh(ε) 是干净可证的严格上界。) -/

/-- **核心弦引理**(纯分布,无 exp):p、p̃ 为概率分布(和均 1),逐点比值受控
    `L·p̃_t ≤ p_t ≤ U·p̃_t`(L≤1≤U),则 `½·Σ|p−p̃| ≤ (1−L)(U−1)/(U−L)`。
    机理:|p_t−p̃_t| 落在过端点 (L,U) 的仿射弦下,弦差精确因式分解为符号已知项。 -/
lemma tv_chord_bound (p ptilde : ι → ℝ) (L U : ℝ)
    (hLU : L < U) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hlo : ∀ t, L * ptilde t ≤ p t) (hhi : ∀ t, p t ≤ U * ptilde t)
    (hps : ∑ t, p t = 1) (hpts : ∑ t, ptilde t = 1) :
    (1/2) * ∑ t, |p t - ptilde t| ≤ (1 - L) * (U - 1) / (U - L) := by
  have hUL : 0 < U - L := by linarith
  -- 逐点弦:|p_t−p̃_t|·(U−L) ≤ (1−L)(U·p̃_t−p_t) + (U−1)(p_t−L·p̃_t)
  have hchord : ∀ t, |p t - ptilde t| * (U - L)
      ≤ (1 - L) * (U * ptilde t - p t) + (U - 1) * (p t - L * ptilde t) := by
    intro t
    have hlo_t := hlo t; have hhi_t := hhi t
    have key : |p t - ptilde t| * (U - L) = |(p t - ptilde t) * (U - L)| := by
      rw [abs_mul, abs_of_pos hUL]
    rw [key]
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ U - 1)
        (by linarith : (0:ℝ) ≤ p t - L * ptilde t)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - L)
        (by linarith : (0:ℝ) ≤ U * ptilde t - p t)]
  -- 求和:Σ|p−p̃|·(U−L) ≤ 2(1−L)(U−1)
  have hsum : (∑ t, |p t - ptilde t|) * (U - L) ≤ 2 * ((1 - L) * (U - 1)) := by
    rw [Finset.sum_mul]
    calc ∑ t, |p t - ptilde t| * (U - L)
        ≤ ∑ t, ((1 - L) * (U * ptilde t - p t)
                + (U - 1) * (p t - L * ptilde t)) :=
          Finset.sum_le_sum (fun t _ => hchord t)
      _ = (1 - L) * (U * (∑ t, ptilde t) - (∑ t, p t))
          + (U - 1) * ((∑ t, p t) - L * (∑ t, ptilde t)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * ((1 - L) * (U - 1)) := by rw [hps, hpts]; ring
  rw [le_div_iff₀ hUL]; nlinarith [hsum]

/-- **抽象 tanh 界**:p̃ 概率分布,|ε_t|≤cmax,p_t=p̃_t·e^{−ε_t}/Z,则
    `TV(p,p̃) ≤ (e^{2cmax}−1)/(e^{2cmax}+1)`(= tanh cmax)。tv_le_eform 的紧化替代。 -/
theorem tv_le_tanh (p ptilde ε : ι → ℝ) (cmax : ℝ) (hcmax : 0 < cmax)
    (hpt_nonneg : ∀ t, 0 ≤ ptilde t) (hpt_sum : ∑ t, ptilde t = 1)
    (hεb : ∀ t, |ε t| ≤ cmax) (hZ_pos : 0 < WitCert.Znorm ptilde ε)
    (hp_def : ∀ t, p t = ptilde t * Real.exp (-ε t) / WitCert.Znorm ptilde ε) :
    WitCert.TV p ptilde
      ≤ (Real.exp (2 * cmax) - 1) / (Real.exp (2 * cmax) + 1) := by
  set Z := WitCert.Znorm ptilde ε with hZdef
  have hEc : ∀ t, Real.exp (-cmax) ≤ Real.exp (-ε t)
      ∧ Real.exp (-ε t) ≤ Real.exp cmax := fun t => by
    have := abs_le.mp (hεb t)
    exact ⟨Real.exp_le_exp.mpr (by linarith [this.2]),
           Real.exp_le_exp.mpr (by linarith [this.1])⟩
  -- Z ∈ [e^{−cmax}, e^{cmax}]
  have hZhi : Z ≤ Real.exp cmax := by
    rw [hZdef, WitCert.Znorm]
    calc ∑ t, ptilde t * Real.exp (-ε t)
        ≤ ∑ t, ptilde t * Real.exp cmax :=
          Finset.sum_le_sum (fun t _ =>
            mul_le_mul_of_nonneg_left (hEc t).2 (hpt_nonneg t))
      _ = Real.exp cmax := by rw [← Finset.sum_mul, hpt_sum, one_mul]
  have hZlo : Real.exp (-cmax) ≤ Z := by
    rw [hZdef, WitCert.Znorm]
    calc Real.exp (-cmax) = ∑ t, ptilde t * Real.exp (-cmax) := by
          rw [← Finset.sum_mul, hpt_sum, one_mul]
      _ ≤ ∑ t, ptilde t * Real.exp (-ε t) :=
          Finset.sum_le_sum (fun t _ =>
            mul_le_mul_of_nonneg_left (hEc t).1 (hpt_nonneg t))
  have hexp2 : Real.exp (2 * cmax) = Real.exp cmax * Real.exp cmax := by
    rw [← Real.exp_add]; ring_nf
  have hexpn2 : Real.exp (-(2 * cmax)) = Real.exp (-cmax) * Real.exp (-cmax) := by
    rw [← Real.exp_add]; ring_nf
  -- 逐点比值界:e^{−2cmax}·p̃_t ≤ p_t ≤ e^{2cmax}·p̃_t
  have hlo : ∀ t, Real.exp (-(2 * cmax)) * ptilde t ≤ p t := by
    intro t
    have hkey : Real.exp (-(2*cmax)) * Z ≤ Real.exp (-ε t) := by
      calc Real.exp (-(2*cmax)) * Z
          ≤ Real.exp (-(2*cmax)) * Real.exp cmax :=
            mul_le_mul_of_nonneg_left hZhi (Real.exp_pos _).le
        _ = Real.exp (-cmax) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-ε t) := (hEc t).1
    rw [hp_def t, le_div_iff₀ hZ_pos]
    calc Real.exp (-(2*cmax)) * ptilde t * Z
        = ptilde t * (Real.exp (-(2*cmax)) * Z) := by ring
      _ ≤ ptilde t * Real.exp (-ε t) := mul_le_mul_of_nonneg_left hkey (hpt_nonneg t)
  have hhi : ∀ t, p t ≤ Real.exp (2 * cmax) * ptilde t := by
    intro t
    have hZ1 : (1:ℝ) ≤ Real.exp cmax * Z := by
      calc (1:ℝ) = Real.exp cmax * Real.exp (-cmax) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp cmax * Z := mul_le_mul_of_nonneg_left hZlo (Real.exp_pos cmax).le
    have hkey : Real.exp (-ε t) ≤ Real.exp (2*cmax) * Z := by
      calc Real.exp (-ε t) ≤ Real.exp cmax := (hEc t).2
        _ = Real.exp cmax * 1 := (mul_one _).symm
        _ ≤ Real.exp cmax * (Real.exp cmax * Z) :=
            mul_le_mul_of_nonneg_left hZ1 (Real.exp_pos cmax).le
        _ = Real.exp (2*cmax) * Z := by rw [hexp2]; ring
    rw [hp_def t, div_le_iff₀ hZ_pos]
    calc ptilde t * Real.exp (-ε t)
        ≤ ptilde t * (Real.exp (2*cmax) * Z) :=
          mul_le_mul_of_nonneg_left hkey (hpt_nonneg t)
      _ = Real.exp (2*cmax) * ptilde t * Z := by ring
  -- Σp = 1(p 是分布:Σ p̃_t e^{−ε_t}/Z = Z/Z = 1)
  have hps : ∑ t, p t = 1 := by
    have hh : ∑ t, p t = (∑ t, ptilde t * Real.exp (-ε t)) / Z := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun t _ => hp_def t)
    have hnum : (∑ t, ptilde t * Real.exp (-ε t)) = Z := by rw [hZdef]; rfl
    rw [hh, hnum]; exact div_self (ne_of_gt hZ_pos)
  -- 套核心弦引理:L=e^{−2cmax}, U=e^{2cmax}
  have hL1 : Real.exp (-(2 * cmax)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1U : 1 ≤ Real.exp (2 * cmax) := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hLU : Real.exp (-(2 * cmax)) < Real.exp (2 * cmax) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hbound := tv_chord_bound p ptilde (Real.exp (-(2*cmax))) (Real.exp (2*cmax))
    hLU hL1 h1U hlo hhi hps hpt_sum
  -- (1−L)(U−1)/(U−L) = (e^{2cmax}−1)/(e^{2cmax}+1),用 L·U=1
  have hid : (1 - Real.exp (-(2*cmax))) * (Real.exp (2*cmax) - 1)
             / (Real.exp (2*cmax) - Real.exp (-(2*cmax)))
           = (Real.exp (2*cmax) - 1) / (Real.exp (2*cmax) + 1) := by
    have hLUeq : Real.exp (-(2*cmax)) * Real.exp (2*cmax) = 1 := by
      rw [← Real.exp_add]; simp
    have hUL' : Real.exp (2*cmax) - Real.exp (-(2*cmax)) ≠ 0 := ne_of_gt (by linarith)
    have hU1 : Real.exp (2*cmax) + 1 ≠ 0 := ne_of_gt (by positivity)
    rw [div_eq_div_iff hUL' hU1]
    linear_combination (-(Real.exp (2*cmax) - 1)) * hLUeq
  rw [hid] at hbound; exact hbound

/-- **softmax tanh 桥**:分数逐项扰动 ≤ ε(ε>0)⟹ TV ≤ (e^{2ε}−1)/(e^{2ε}+1)
    = tanh(ε)。softmax_tv_bridge 的紧化替代(同 tv_le_tanh 实例化)。 -/
theorem softmax_tv_bridge_tanh [Nonempty ι] (s s' : ι → ℝ) (ε : ℝ) (hε0 : 0 < ε)
    (h : ∀ t, |s t - s' t| ≤ ε) :
    WitCert.TV (softmax s') (softmax s)
      ≤ (Real.exp (2 * ε) - 1) / (Real.exp (2 * ε) + 1) := by
  have hZs := sum_exp_pos s
  have hZnorm : WitCert.Znorm (softmax s) (fun t => s t - s' t)
      = (∑ u, Real.exp (s' u)) / ∑ u, Real.exp (s u) := by
    unfold WitCert.Znorm
    calc ∑ t, softmax s t * Real.exp (-(s t - s' t))
        = ∑ t, Real.exp (s' t) / ∑ u, Real.exp (s u) :=
          Finset.sum_congr rfl fun t _ => softmax_tilt s s' t
      _ = (∑ t, Real.exp (s' t)) / ∑ u, Real.exp (s u) := by rw [Finset.sum_div]
  have hZpos : 0 < WitCert.Znorm (softmax s) (fun t => s t - s' t) := by
    rw [hZnorm]; exact div_pos (sum_exp_pos s') (sum_exp_pos s)
  exact tv_le_tanh (softmax s') (softmax s) (fun t => s t - s' t) ε hε0
    (softmax_nonneg s) (softmax_sum s) h hZpos
    (by
      intro t
      show softmax s' t = softmax s t * Real.exp (-(s t - s' t))
          / WitCert.Znorm (softmax s) (fun t => s t - s' t)
      rw [hZnorm, softmax_tilt s s' t]
      unfold softmax
      rw [div_div_div_cancel_right₀]
      exact ne_of_gt hZs)

/--
  **门控→served(tanh 紧化版)**:同 `served_tv_le_of_gate`,但用 tanh 桥,
  界为 `(e^{2·a_q·wthr}−1)/(e^{2·a_q·wthr}+1) = tanh(a_q·wthr)` —— 恒 <1,非空洞。 -/
theorem served_tv_le_of_gate_tanh {d : ℕ} [Nonempty ι]
    (s s' : ι → ℝ) (q : Fin d → ℝ) (k k' : ι → Fin d → ℝ) (scale aq wthr : ℝ)
    (hscale : 0 ≤ scale) (haq : 0 < aq) (hw : 0 < wthr)
    (hs  : ∀ t, s t  = scale * ∑ i, q i * k t i)
    (hs' : ∀ t, s' t = scale * ∑ i, q i * k' t i)
    (hqbound : scale * Real.sqrt (∑ i, q i ^ 2) ≤ aq)
    (hgate : ∀ t, Real.sqrt (∑ i, (k t i - k' t i) ^ 2) ≤ wthr) :
    WitCert.TV (softmax s') (softmax s)
      ≤ (Real.exp (2 * (aq * wthr)) - 1) / (Real.exp (2 * (aq * wthr)) + 1) := by
  refine softmax_tv_bridge_tanh s s' (aq * wthr) (mul_pos haq hw) (fun t => ?_)
  rw [hs t, hs' t]
  refine le_trans (score_bridge q (k t) (k' t) scale hscale) ?_
  exact mul_le_mul hqbound (hgate t) (Real.sqrt_nonneg _) haq.le

/-! ### ⑥ 累计还原:化解"TV 不可加"

  命门累计层的旧判词是"TV 跨读/跨层不可加,故 cum_W 无 sound served-TV 对应"。
  但这看错了对象:**Transformer 的残差流让最终 logit 扰动可加** ——
  `s' − s = Σ_ℓ δ^ℓ`(δ^ℓ 为第 ℓ 层 KV 压缩对输出 logit 的贡献)。于是累计
  served-TV 由**输出 logit 扰动**(可加,三角不等式)经**一次** tanh 桥给出:
      TV ≤ tanh(Σ_ℓ b_ℓ),  b_ℓ ≥ ‖δ^ℓ‖_∞。
  **TV 从不相加**;相加的是 logit 扰动。这把累计从"指数/不可加(死)"改写成
  "逐层 logit 扰动之和(线性可加)+ 末端单 tanh"。剩下的是界住逐层 b_ℓ
  (逐层 Lipschitz:静态权重范数=sound 但松,或实测包络=紧),与逐读同构。 -/

/-- **累计输出还原**:输出 logit 扰动是逐层贡献之和 `s'−s = Σ_ℓ δ^ℓ`,每层
    `‖δ^ℓ‖_∞ ≤ b_ℓ`,则整请求的 served next-token TV `≤ tanh(Σ_ℓ b_ℓ)`。
    TV 不相加 —— 相加的是残差流里的 logit 扰动,末端只过一次 tanh 桥。 -/
theorem cumulative_output_tv [Nonempty ι] {L : ℕ}
    (s s' : ι → ℝ) (δ : Fin L → ι → ℝ) (b : Fin L → ℝ)
    (hδ : ∀ ℓ t, |δ ℓ t| ≤ b ℓ)
    (hdecomp : ∀ t, s' t - s t = ∑ ℓ, δ ℓ t)
    (hpos : 0 < ∑ ℓ, b ℓ) :
    WitCert.TV (softmax s') (softmax s)
      ≤ (Real.exp (2 * ∑ ℓ, b ℓ) - 1) / (Real.exp (2 * ∑ ℓ, b ℓ) + 1) := by
  refine softmax_tv_bridge_tanh s s' (∑ ℓ, b ℓ) hpos (fun t => ?_)
  have hst : s t - s' t = -(∑ ℓ, δ ℓ t) := by rw [← hdecomp t]; ring
  rw [hst, abs_neg]
  calc |∑ ℓ, δ ℓ t| ≤ ∑ ℓ, |δ ℓ t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ℓ, b ℓ := Finset.sum_le_sum (fun ℓ _ => hδ ℓ t)

/-! ### ⑦ Hellinger/Bhattacharyya 界:破 L∞ 墙的**非空洞** sound served-TV 界

  tanh(‖Δlogit‖∞) 用**最坏坐标**,对累计 served-TV **空洞**(实测 0.996)。但 TV
  关心**质量搬动**:大扰动落低概率 token 不搬质量。用 Bhattacharyya 系数
  BC=Σ√(p·p')(质量重叠),`TV ≤ √(1−BC²)` —— **初等 Cauchy-Schwarz,自足可机检**
  (不依赖 Pinsker/Bennett,Mathlib 无),实测中位 0.147 **非空洞**(vs tanh 0.996)。
  a-priori 方向:1−BC = ½Σ(√p−√p')²(Hellinger²),把它从 ‖Δh‖/见证界住即得
  不跑压缩模型的 sound 界(下一目标)。 -/

/-- Bhattacharyya 系数 BC(p,p') = Σ √(p_v p'_v)(质量重叠 ∈ [0,1])。 -/
noncomputable def BC (p p' : ι → ℝ) : ℝ := ∑ v, Real.sqrt (p v * p' v)

/-- **Hellinger TV 界**(初等,自足):p、p' 概率分布 ⟹
    `TV(p,p') ≤ √(1 − BC(p,p')²)`。质量搬动度量,破 tanh(‖Δlogit‖∞) 的 L∞ 墙。 -/
theorem tv_le_hellinger (p p' : ι → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, 0 ≤ p' v)
    (hps : ∑ v, p v = 1) (hp's : ∑ v, p' v = 1) :
    WitCert.TV p p' ≤ Real.sqrt (1 - BC p p' ^ 2) := by
  set s : ι → ℝ := fun v => Real.sqrt (p v) with hsdef
  set t : ι → ℝ := fun v => Real.sqrt (p' v) with htdef
  have hsnn : ∀ v, 0 ≤ s v := fun v => Real.sqrt_nonneg _
  have htnn : ∀ v, 0 ≤ t v := fun v => Real.sqrt_nonneg _
  have hs2 : ∀ v, s v ^ 2 = p v := fun v => Real.sq_sqrt (hp v)
  have ht2 : ∀ v, t v ^ 2 = p' v := fun v => Real.sq_sqrt (hp' v)
  have hSs2 : ∑ v, s v ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => hs2 v)]; exact hps
  have hSt2 : ∑ v, t v ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => ht2 v)]; exact hp's
  have hBCst : BC p p' = ∑ v, s v * t v :=
    Finset.sum_congr rfl (fun v _ => Real.sqrt_mul (hp v) _)
  have hBCnn : 0 ≤ BC p p' := by
    rw [hBCst]; exact Finset.sum_nonneg (fun v _ => mul_nonneg (hsnn v) (htnn v))
  have hBCle : BC p p' ≤ 1 := by
    rw [hBCst]
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ s t
    rwa [hSs2, hSt2, Real.sqrt_one, mul_one] at h
  have hsub : ∑ v, (s v - t v) ^ 2 = 2 * (1 - BC p p') := by
    rw [Finset.sum_congr rfl (fun v _ => (by ring :
        (s v - t v) ^ 2 = s v ^ 2 + t v ^ 2 - 2 * (s v * t v))),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hSs2, hSt2,
      ← Finset.mul_sum, ← hBCst]; ring
  have hadd : ∑ v, (s v + t v) ^ 2 = 2 * (1 + BC p p') := by
    rw [Finset.sum_congr rfl (fun v _ => (by ring :
        (s v + t v) ^ 2 = s v ^ 2 + t v ^ 2 + 2 * (s v * t v))),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hSs2, hSt2,
      ← Finset.mul_sum, ← hBCst]; ring
  have hTV : WitCert.TV p p' = (1 / 2) * ∑ v, |s v - t v| * (s v + t v) := by
    unfold WitCert.TV; congr 1
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← hs2 v, ← ht2 v,
        show s v ^ 2 - t v ^ 2 = (s v - t v) * (s v + t v) by ring,
        abs_mul, abs_of_nonneg (by linarith [hsnn v, htnn v] : (0:ℝ) ≤ s v + t v)]
  have hCS : ∑ v, |s v - t v| * (s v + t v)
      ≤ Real.sqrt (2 * (1 - BC p p')) * Real.sqrt (2 * (1 + BC p p')) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun v => |s v - t v|) (fun v => s v + t v)
    simp only [sq_abs] at h
    rwa [hsub, hadd] at h
  rw [hTV]
  have hid : Real.sqrt (2 * (1 - BC p p')) * Real.sqrt (2 * (1 + BC p p'))
      = 2 * Real.sqrt (1 - BC p p' ^ 2) := by
    rw [← Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * (1 - BC p p')),
        show 2 * (1 - BC p p') * (2 * (1 + BC p p'))
           = 2 ^ 2 * (1 - BC p p' ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  calc (1 / 2) * ∑ v, |s v - t v| * (s v + t v)
      ≤ (1 / 2) * (Real.sqrt (2 * (1 - BC p p'))
                   * Real.sqrt (2 * (1 + BC p p'))) :=
        mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = Real.sqrt (1 - BC p p' ^ 2) := by rw [hid]; ring

/-- **Hellinger² 恒等式**(a-priori 方向):`1 − BC = ½ Σ (√p−√p')²`。把右边(平方
    Hellinger)从 logit 扰动 / ‖Δh‖ / 见证界住,即得**不跑压缩模型**的 sound served-TV
    界 —— 逼近实测极限的下一形式化目标(Var_p 型 a-priori 界)。 -/
theorem one_sub_BC_eq (p p' : ι → ℝ) (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, 0 ≤ p' v)
    (hps : ∑ v, p v = 1) (hp's : ∑ v, p' v = 1) :
    1 - BC p p' = (1 / 2) * ∑ v, (Real.sqrt (p v) - Real.sqrt (p' v)) ^ 2 := by
  have hSs2 : ∑ v, Real.sqrt (p v) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => Real.sq_sqrt (hp v))]; exact hps
  have hSt2 : ∑ v, Real.sqrt (p' v) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => Real.sq_sqrt (hp' v))]; exact hp's
  rw [Finset.sum_congr rfl (fun v _ => (by ring :
      (Real.sqrt (p v) - Real.sqrt (p' v)) ^ 2
        = Real.sqrt (p v) ^ 2 + Real.sqrt (p' v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (p' v)))),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hSs2, hSt2, ← Finset.mul_sum]
  have : BC p p' = ∑ v, Real.sqrt (p v) * Real.sqrt (p' v) :=
    Finset.sum_congr rfl (fun v _ => Real.sqrt_mul (hp v) _)
  rw [← this]; ring

/-- BC ≤ 1(Cauchy-Schwarz:⟨√p,√p'⟩ ≤ ‖√p‖‖√p'‖ = 1)。 -/
theorem BC_le_one (p p' : ι → ℝ) (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, 0 ≤ p' v)
    (hps : ∑ v, p v = 1) (hp's : ∑ v, p' v = 1) : BC p p' ≤ 1 := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun v => Real.sqrt (p v)) (fun v => Real.sqrt (p' v))
  have e1 : ∑ v, Real.sqrt (p v) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => Real.sq_sqrt (hp v))]; exact hps
  have e2 : ∑ v, Real.sqrt (p' v) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun v _ => Real.sq_sqrt (hp' v))]; exact hp's
  rw [e1, e2, Real.sqrt_one, mul_one] at h
  have hBC : BC p p' = ∑ v, Real.sqrt (p v) * Real.sqrt (p' v) :=
    Finset.sum_congr rfl (fun v _ => Real.sqrt_mul (hp v) _)
  rw [hBC]; exact h

/-! ### ⑧ a-priori 方向的核心 kernel:方差(非幅度)界服 served-TV

  a-priori sound 界(不跑压缩、仅凭见证)从**幅度界**走是墙(最坏方向)。洞在
  SR 压缩的**残差条件均值零(鞅)+ 见证方差 cum_C**:输出 logit 扰动
  δ = Σ 有界均值零项 ⟹ sub-Gaussian(方差 σ² 由 cum_C 界),其**变量方差**
  界(非最坏 range)可 anytime-valid(同 cum_W epistemics)。本 kernel 把
  "mean-zero + sub-Gaussian(σ²)" 直接转成非空洞 TV 界,破 range 墙。 -/

/--
  **sub-Gaussian served-TV 界(a-priori kernel)**:p'∝p·e^δ(指数倾斜),
  δ 在 p 下均值零(鞅)且 sub-Gaussian(MGF `E_p[e^δ] ≤ e^{σ²/2}`),则
  `TV(p,p') ≤ σ/√2`。**变量方差 σ²(≈cum_C)界,不含最坏 range** —— 破幅度墙。
  经 BC ≥ e^{−σ²/4}(均值零 Jensen + sub-Gaussian)+ tv_le_hellinger。 -/
theorem tv_le_subgaussian (p p' : ι → ℝ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, 0 ≤ p' v)
    (hps : ∑ v, p v = 1) (hp's : ∑ v, p' v = 1)
    (hBC : Real.exp (-(σ ^ 2 / 4)) ≤ BC p p') :
    WitCert.TV p p' ≤ σ / Real.sqrt 2 := by
  have hH := tv_le_hellinger p p' hp hp' hps hp's
  have hle1 := BC_le_one p p' hp hp' hps hp's
  have hBCnn : 0 ≤ BC p p' := le_trans (Real.exp_nonneg _) hBC
  have hexp : 1 - Real.exp (-(σ ^ 2 / 4)) ≤ σ ^ 2 / 4 := by
    have := Real.add_one_le_exp (-(σ ^ 2 / 4)); linarith
  have h1mBC : 1 - BC p p' ≤ σ ^ 2 / 4 := by linarith
  have hsq : 1 - BC p p' ^ 2 ≤ σ ^ 2 / 2 := by nlinarith [h1mBC, hle1, hBCnn]
  refine le_trans hH ?_
  have hgoal : σ / Real.sqrt 2 = Real.sqrt (σ ^ 2 / 2) := by
    rw [Real.sqrt_div (sq_nonneg σ), Real.sqrt_sq hσ]
  rw [hgoal]; exact Real.sqrt_le_sqrt hsq

/-- **BC 下界(a-priori step 1)**:p'∝p·e^δ,δ 在 p 下均值零 + sub-Gaussian
    (`E_p[e^δ] ≤ e^{σ²/2}`)⟹ `BC ≥ e^{−σ²/4}`。把 tv_le_subgaussian 的假设变成
    定理:BC = E_p[e^{δ/2}]/√Z,分子 ≥1(Jensen 均值零),√Z ≤ e^{σ²/4}(sub-G)。 -/
theorem BC_ge_subgaussian (p δ : ι → ℝ) (σ : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (hmean : ∑ v, p v * δ v = 0)
    (hsubg : ∑ v, p v * Real.exp (δ v) ≤ Real.exp (σ ^ 2 / 2)) :
    Real.exp (-(σ ^ 2 / 4))
      ≤ BC p (fun v => p v * Real.exp (δ v) / (∑ u, p u * Real.exp (δ u))) := by
  set Z := ∑ u, p u * Real.exp (δ u) with hZdef
  -- Jensen(convexOn_exp):e^{E_p[x]} ≤ E_p[e^x];均值零 ⟹ 分子/分母 ≥ 1
  have hE : ∀ f : ι → ℝ, (∑ v, p v * f v) = 0 →
      (1:ℝ) ≤ ∑ v, p v * Real.exp (f v) := by
    intro f hf
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := f)
      (fun i _ => hp i) (by simpa using hps) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (1:ℝ) = Real.exp (∑ v, p v * f v) := by rw [hf, Real.exp_zero]
      _ ≤ ∑ v, p v * Real.exp (f v) := hj
  have hZge1 : (1:ℝ) ≤ Z := hE δ hmean
  have hZpos : 0 < Z := by linarith
  have hEhalf : (1:ℝ) ≤ ∑ v, p v * Real.exp (δ v / 2) := by
    refine hE (fun v => δ v / 2) ?_
    rw [Finset.sum_congr rfl (fun v _ => (by ring : p v * (δ v / 2) = (p v * δ v) / 2)),
        ← Finset.sum_div, hmean]; norm_num
  -- BC = (Σ p_v e^{δ_v/2}) / √Z
  have hBCeq : BC p (fun v => p v * Real.exp (δ v) / Z)
      = (∑ v, p v * Real.exp (δ v / 2)) / Real.sqrt Z := by
    unfold BC
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    show Real.sqrt (p v * (p v * Real.exp (δ v) / Z))
        = p v * Real.exp (δ v / 2) / Real.sqrt Z
    have he2 : Real.exp (δ v / 2) ^ 2 = Real.exp (δ v) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq2 : (p v * Real.exp (δ v / 2)) ^ 2 = p v * (p v * Real.exp (δ v)) := by
      rw [mul_pow, he2]; ring
    rw [show p v * (p v * Real.exp (δ v) / Z)
          = (p v * Real.exp (δ v / 2)) ^ 2 / Z by rw [hsq2]; ring,
      Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg (hp v) (Real.exp_pos _).le)]
  -- √Z ≤ e^{σ²/4}
  have hexp2 : Real.exp (σ ^ 2 / 2) = Real.exp (σ ^ 2 / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsqZ : Real.sqrt Z ≤ Real.exp (σ ^ 2 / 4) := by
    have h := Real.sqrt_le_sqrt hsubg
    rwa [hexp2, Real.sqrt_sq (Real.exp_pos _).le] at h
  -- BC = E/√Z ≥ 1/e^{σ²/4} = e^{−σ²/4}
  rw [hBCeq, Real.exp_neg, ← one_div,
      div_le_div_iff₀ (Real.exp_pos _) (Real.sqrt_pos.mpr hZpos)]
  calc 1 * Real.sqrt Z ≤ 1 * Real.exp (σ ^ 2 / 4) := by
        rw [one_mul, one_mul]; exact hsqZ
    _ ≤ (∑ v, p v * Real.exp (δ v / 2)) * Real.exp (σ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right hEhalf (Real.exp_pos _).le

/-- **a-priori served-TV 界(step 1+kernel 合成)**:输出 logit 扰动 δ 在精确
    served 分布 p 下**均值零**(SR 鞅)且 **sub-Gaussian**(`E_p[e^δ] ≤ e^{σ²/2}`,
    σ² 由见证 cum_C 界),则压缩 served 分布 p'∝p·e^δ 满足 `TV(p,p') ≤ σ/√2`。
    **纯方差界,不含最坏 range** —— 破幅度墙,给出不跑压缩、仅凭见证的 served 界。
    step 2(σ²←见证)两侧证明部分均已机检:head 侧 `var_p_delta_le_trace_cov`
    (`Var_p(δ) ≤ tr Cov_p(head)·‖Δh‖²`,纯 Cauchy-Schwarz);网络侧
    `residual_second_moment_le`(残差流增量正交 ⟹ `E_ω‖Δh‖² ≤ propagation·cum_C`,
    二阶 Pythagorean)。W3SLE 实测 σ²_implied/Var_p≈0.92 证 range 墙对 served 不 bind。
    正交假设 horth 由 SR 跨层独立 discharge(`crossSum_indep_meanzero_eq_zero`);
    传播系数 γ_ℓ=‖J^ℓ‖² 由 Frobenius `linear_propagation_frobenius` + 输入侧
    `score_perturbation_l2_le`(接 score_bridge)界定;词表→ω 转移由
    `served_tv_mean_le_omega_subgaussian` sound 打通(逐 ω kernel+两次 Jensen+Fubini,
    `E_ω[TV]≤s/√2`,s² 为 ω-sub-Gaussian proxy 由 McDiarmid 提供)。**a-priori 链条端
    到端机检**。剩模型侧数值实例化(实际 ‖J^ℓ‖²_F、一阶线性化),非数学缺口。 -/
theorem served_tv_le_subgaussian (p δ : ι → ℝ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (hmean : ∑ v, p v * δ v = 0)
    (hsubg : ∑ v, p v * Real.exp (δ v) ≤ Real.exp (σ ^ 2 / 2)) :
    WitCert.TV p
      (fun v => p v * Real.exp (δ v) / (∑ u, p u * Real.exp (δ u)))
      ≤ σ / Real.sqrt 2 := by
  have hZpos : 0 < ∑ u, p u * Real.exp (δ u) := by
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := δ)
      (fun i _ => hp i) (by simpa using hps) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (0:ℝ) < 1 := one_pos
      _ = Real.exp (∑ v, p v * δ v) := by rw [hmean, Real.exp_zero]
      _ ≤ ∑ u, p u * Real.exp (δ u) := hj
  refine tv_le_subgaussian p _ σ hσ hp
    (fun v => div_nonneg (mul_nonneg (hp v) (Real.exp_pos _).le) hZpos.le)
    hps ?_ (BC_ge_subgaussian p δ σ hp hps hmean hsubg)
  rw [← Finset.sum_div]; exact div_self (ne_of_gt hZpos)

/-! ### ⑨ a-priori 方差传播(head 侧,range 墙已除) -/

/-- **方差传播核(head 侧)**:输出 logit 扰动 `δ_v = ⟨head_v, Δh⟩`(head 第 v 行与
    隐状态扰动 Δh 的点乘)在 served 分布 p 下的**方差**受控于 head 的 p-加权协方差
    之迹乘以 `‖Δh‖²`:
      `Var_p(δ) = Δhᵀ Cov_p(head) Δh ≤ (∑_v p_v ‖head_v − h̄‖²)·‖Δh‖²`,
    其中 `h̄_j = ∑_v p_v head_{v,j}`(head 的 p-均值),迹 `∑_v p_v ‖head_v−h̄‖²
    = tr Cov_p(head)`。**纯 Cauchy-Schwarz,无最坏 range** —— 这是 W3SLE 判决(实测
    σ²_implied/Var_p≈0.92,扰动 sub-Gaussian 紧)之后,把 range 墙除掉的那一步:
    在 sub-Gaussian 紧的量纲上,此方差即 `served_tv_le_subgaussian` 的 proxy σ²
    量级,而 `‖Δh‖²` 由残差流(`cumulative_output_tv` 的加性)回接 cum_C。
    **仍待续**(网络侧):`‖Δh‖² ≤ propagation·cum_C` 的逐层传播,及词表→ω 的
    sub-Gaussian 转移(proxy ≤ 方差非无条件,由 W3SLE 实测支撑,非此处所证)。 -/
theorem var_p_delta_le_trace_cov {d : ℕ}
    (p : ι → ℝ) (head : ι → Fin d → ℝ) (dh hbar : Fin d → ℝ)
    (hp : ∀ v, 0 ≤ p v)
    (hhbar : ∀ j, hbar j = ∑ u, p u * head u j) :
    ∑ v, p v * ((∑ j, head v j * dh j)
        - (∑ u, p u * (∑ j, head u j * dh j))) ^ 2
      ≤ (∑ v, p v * (∑ j, (head v j - hbar j) ^ 2)) * (∑ j, dh j ^ 2) := by
  -- E_p[δ] = ∑_j h̄_j dh_j(交换求和 + 提出 dh_j)
  have hE : (∑ u, p u * (∑ j, head u j * dh j)) = ∑ j, hbar j * dh j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hhbar, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  -- 中心化恒等式:δ_v − E_p[δ] = ∑_j (head_{v,j} − h̄_j) dh_j
  have hcenter : ∀ v, (∑ j, head v j * dh j)
        - (∑ u, p u * (∑ j, head u j * dh j))
        = ∑ j, (head v j - hbar j) * dh j := by
    intro v
    rw [hE, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- 逐 v:中心化 + Cauchy-Schwarz(⟨head_v−h̄, Δh⟩² ≤ ‖head_v−h̄‖²‖Δh‖²)+ p_v≥0
  have hterm : ∀ v, p v * ((∑ j, head v j * dh j)
        - (∑ u, p u * (∑ j, head u j * dh j))) ^ 2
      ≤ p v * (∑ j, (head v j - hbar j) ^ 2) * (∑ j, dh j ^ 2) := by
    intro v
    rw [hcenter v]
    have hcs : (∑ j, (head v j - hbar j) * dh j) ^ 2
        ≤ (∑ j, (head v j - hbar j) ^ 2) * (∑ j, dh j ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    calc p v * (∑ j, (head v j - hbar j) * dh j) ^ 2
        ≤ p v * ((∑ j, (head v j - hbar j) ^ 2) * (∑ j, dh j ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (hp v)
      _ = p v * (∑ j, (head v j - hbar j) ^ 2) * (∑ j, dh j ^ 2) := by ring
  calc ∑ v, p v * ((∑ j, head v j * dh j)
          - (∑ u, p u * (∑ j, head u j * dh j))) ^ 2
      ≤ ∑ v, p v * (∑ j, (head v j - hbar j) ^ 2) * (∑ j, dh j ^ 2) :=
        Finset.sum_le_sum (fun v _ => hterm v)
    _ = (∑ v, p v * (∑ j, (head v j - hbar j) ^ 2)) * (∑ j, dh j ^ 2) := by
        rw [← Finset.sum_mul]

/-! ### ⑩ 网络侧方差传播:残差流增量正交 ⟹ E‖Δh‖² = Σ_ℓ E‖X_ℓ‖² -/

/-- ω-加权二阶交叉型(离散 L²(wt) 双线性):`⟪Y,Z⟫_wt = ∑_ω wt_ω ∑_j Y_{ω,j} Z_{ω,j}`。
    物理:wt 是 SR 抽签 ω 的概率,Y_ω/Z_ω 是该抽签下的(向量值)扰动;`⟪Y,Y⟫_wt=E_ω‖Y‖²`。 -/
def crossSum {Ω : Type*} [Fintype Ω] {d : ℕ}
    (wt : Ω → ℝ) (Y Z : Ω → Fin d → ℝ) : ℝ :=
  ∑ ω, wt ω * ∑ j, Y ω j * Z ω j

/-- crossSum 对称(逐项 `mul_comm`)。 -/
lemma crossSum_comm {Ω : Type*} [Fintype Ω] {d : ℕ}
    (wt : Ω → ℝ) (Y Z : Ω → Fin d → ℝ) :
    crossSum wt Y Z = crossSum wt Z Y :=
  Finset.sum_congr rfl (fun ω _ => congrArg (wt ω * ·)
    (Finset.sum_congr rfl (fun _ _ => mul_comm _ _)))

/-- crossSum 对第一变量的有限线性:`⟪∑_ℓ X_ℓ, Z⟫ = ∑_ℓ ⟪X_ℓ, Z⟫`。 -/
lemma crossSum_sum_left {Ω : Type*} [Fintype Ω] {d : ℕ} {L : Type*} [Fintype L]
    (wt : Ω → ℝ) (X : L → Ω → Fin d → ℝ) (Z : Ω → Fin d → ℝ) :
    crossSum wt (fun ω j => ∑ ℓ, X ℓ ω j) Z = ∑ ℓ, crossSum wt (X ℓ) Z := by
  simp only [crossSum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
        congrArg (wt ω * ·)
          (Finset.sum_comm (f := fun j ℓ => X ℓ ω j * Z ω j)))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **残差流增量正交 ⟹ 二阶 Pythagorean**:Δh = Σ_ℓ X_ℓ(残差流的加性:每层压缩
    扰动传播到末层的贡献 X_ℓ 相加),若各层增量在 ω 下两两不相关(SR 跨层独立 + 均值零
    ⟹ `⟪X_ℓ,X_ℓ'⟫_wt=0`,ℓ≠ℓ'),则 `E_ω‖Δh‖² = Σ_ℓ E_ω‖X_ℓ‖²`。**方差可加,不累计成
    幅度(L1)** —— 这正是见证 cum_C 是逐层**方差之和**、而末层扰动仍受控的根源。 -/
theorem residual_second_moment_orthogonal {Ω : Type*} [Fintype Ω] {d : ℕ}
    {L : Type*} [Fintype L]
    (wt : Ω → ℝ) (X : L → Ω → Fin d → ℝ)
    (horth : ∀ ℓ ℓ', ℓ ≠ ℓ' → crossSum wt (X ℓ) (X ℓ') = 0) :
    crossSum wt (fun ω j => ∑ ℓ, X ℓ ω j) (fun ω j => ∑ ℓ, X ℓ ω j)
      = ∑ ℓ, crossSum wt (X ℓ) (X ℓ) := by
  rw [crossSum_sum_left]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  calc crossSum wt (X ℓ) (fun ω j => ∑ ℓ', X ℓ' ω j)
      = crossSum wt (fun ω j => ∑ ℓ', X ℓ' ω j) (X ℓ) := crossSum_comm _ _ _
    _ = ∑ ℓ', crossSum wt (X ℓ') (X ℓ) := crossSum_sum_left _ _ _
    _ = crossSum wt (X ℓ) (X ℓ) :=
        Finset.sum_eq_single ℓ
          (fun ℓ' _ hℓ' => by
            rw [crossSum_comm]; exact horth ℓ ℓ' (Ne.symm hℓ'))
          (fun h => absurd (Finset.mem_univ ℓ) h)

/-- **网络侧方差传播界**:正交增量 + 每层传播后二阶界 `‖X_ℓ(ω)‖² ≤ b_ℓ`(逐 ω 一致)
    + `∑wt=1` ⟹ `E_ω‖Δh‖² ≤ ∑_ℓ b_ℓ`。取 `b_ℓ = γ_ℓ·C_ℓ`(γ_ℓ=‖J^ℓ‖²_op 残差流
    传播系数,C_ℓ 每层 SR 方差)则 `≤ (max_ℓ γ_ℓ)·∑_ℓ C_ℓ = propagation·cum_C`,
    接上 `var_p_delta_le_trace_cov` 的 `‖Δh‖²`,完成 σ²←见证 的网络侧归约(证明部分)。 -/
theorem residual_second_moment_le {Ω : Type*} [Fintype Ω] {d : ℕ}
    {L : Type*} [Fintype L]
    (wt : Ω → ℝ) (X : L → Ω → Fin d → ℝ) (b : L → ℝ)
    (hwt : ∀ ω, 0 ≤ wt ω) (hwt1 : ∑ ω, wt ω = 1)
    (horth : ∀ ℓ ℓ', ℓ ≠ ℓ' → crossSum wt (X ℓ) (X ℓ') = 0)
    (hbnd : ∀ ℓ ω, (∑ j, X ℓ ω j ^ 2) ≤ b ℓ) :
    crossSum wt (fun ω j => ∑ ℓ, X ℓ ω j) (fun ω j => ∑ ℓ, X ℓ ω j)
      ≤ ∑ ℓ, b ℓ := by
  rw [residual_second_moment_orthogonal wt X horth]
  refine Finset.sum_le_sum (fun ℓ _ => ?_)
  have h1 : crossSum wt (X ℓ) (X ℓ) ≤ ∑ ω, wt ω * b ℓ := by
    simp only [crossSum]
    refine Finset.sum_le_sum (fun ω _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hwt ω)
    calc ∑ j, X ℓ ω j * X ℓ ω j
        = ∑ j, X ℓ ω j ^ 2 := Finset.sum_congr rfl (fun j _ => (pow_two _).symm)
      _ ≤ b ℓ := hbnd ℓ ω
  calc crossSum wt (X ℓ) (X ℓ) ≤ ∑ ω, wt ω * b ℓ := h1
    _ = b ℓ := by rw [← Finset.sum_mul, hwt1, one_mul]

/-- **独立 + 均值零 ⟹ 增量不相关**(discharge `horth`):SR 抽签空间取 `Ω = (每层 →
    公共 draw 空间 A)`,权重为乘积测度 `wt ω = ∏_m q_m(ω_m)`(跨层独立),各层增量
    `X_ℓ ω = Y_ℓ(ω_ℓ)` 只依赖自身抽签,且逐坐标均值零 `∑_a q_ℓ(a) Y_ℓ(a,j)=0`。则
    任意 `ℓ≠ℓ'` 的交叉型 `⟪X_ℓ,X_ℓ'⟫_wt=0`。证明:乘积测度 Fubini(`prod_univ_sum`)
    把 ∑_ω 分解为逐坐标 ∑_a 之积,ℓ 坐标那一项即均值零。**这把 residual_second_moment
    的正交假设由 SR 结构导出** —— 鞅方差可加的概率根据。 -/
lemma crossSum_indep_meanzero_eq_zero {d : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    {A : Type*} [Fintype A]
    (q : L → A → ℝ) (Y : L → A → Fin d → ℝ)
    (hmean : ∀ ℓ j, ∑ a, q ℓ a * Y ℓ a j = 0)
    {ℓ ℓ' : L} (hne : ℓ ≠ ℓ') :
    crossSum (fun ω : L → A => ∏ m, q m (ω m))
      (fun ω j => Y ℓ (ω ℓ) j) (fun ω j => Y ℓ' (ω ℓ') j) = 0 := by
  simp only [crossSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  -- 逐 j:∑_ω (∏_m q_m(ω_m)) · Y_ℓ(ω_ℓ,j) · Y_ℓ'(ω_ℓ',j) = 0
  have hfact : ∀ ω : L → A,
      (∏ m, q m (ω m)) * (Y ℓ (ω ℓ) j * Y ℓ' (ω ℓ') j)
      = ∏ m, (q m (ω m) * (if m = ℓ then Y ℓ (ω m) j else 1)
                       * (if m = ℓ' then Y ℓ' (ω m) j else 1)) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl (fun ω _ => hfact ω), ← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ => Finset.univ)
          (fun m a => (q m a * (if m = ℓ then Y ℓ a j else 1))
                        * (if m = ℓ' then Y ℓ' a j else 1))]
  refine Finset.prod_eq_zero (Finset.mem_univ ℓ) ?_
  have hsimp : ∀ a, q ℓ a * (if ℓ = ℓ then Y ℓ a j else 1)
                          * (if ℓ = ℓ' then Y ℓ' a j else 1)
                = q ℓ a * Y ℓ a j :=
    fun a => by rw [if_pos rfl, if_neg hne, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hsimp a)]
  exact hmean ℓ j

/-- **网络侧方差传播(SR 独立版,horth 已内部 discharge)**:仅凭**逐层**事实——
    每坐标 draw 概率非负 `q_ℓ≥0`、逐层归一 `∑_a q_ℓ(a)=1`、逐层均值零、逐层传播后
    二阶界 `∑_j Y_ℓ(ω_ℓ,j)²≤b_ℓ`——即得 `E_ω‖Δh‖² = E_ω‖∑_ℓ X_ℓ‖² ≤ ∑_ℓ b_ℓ`。
    正交与测度归一都由乘积测度导出,不再作外部假设。取 `b_ℓ=γ_ℓ·C_ℓ` ⟹
    `≤ propagation·cum_C`。 -/
theorem residual_second_moment_indep {d : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    {A : Type*} [Fintype A]
    (q : L → A → ℝ) (Y : L → A → Fin d → ℝ) (b : L → ℝ)
    (hqnn : ∀ ℓ a, 0 ≤ q ℓ a) (hq1 : ∀ ℓ, ∑ a, q ℓ a = 1)
    (hmean : ∀ ℓ j, ∑ a, q ℓ a * Y ℓ a j = 0)
    (hbnd : ∀ ℓ (ω : L → A), (∑ j, Y ℓ (ω ℓ) j ^ 2) ≤ b ℓ) :
    crossSum (fun ω : L → A => ∏ m, q m (ω m))
        (fun ω j => ∑ ℓ, Y ℓ (ω ℓ) j) (fun ω j => ∑ ℓ, Y ℓ (ω ℓ) j)
      ≤ ∑ ℓ, b ℓ := by
  have hprod1 : ∑ ω : L → A, ∏ m, q m (ω m) = 1 := by
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) q]
    simp only [hq1, Finset.prod_const_one]
  refine residual_second_moment_le _ _ b ?_ hprod1 ?_ hbnd
  · exact fun ω => Finset.prod_nonneg (fun m _ => hqnn m (ω m))
  · exact fun ℓ ℓ' hne => crossSum_indep_meanzero_eq_zero q Y hmean hne

/-! ### ⑪ 逐层传播系数 γ_ℓ=‖J^ℓ‖²(接 score_bridge):输入敏感 + 输出传播两端 -/

/-- **线性传播 Frobenius 界**:线性映射 `J`(矩阵 `J_{ik}`)作用于扰动 `v`,
    `‖J·v‖² ≤ ‖J‖²_F · ‖v‖²`,其中 `‖J‖²_F = ∑_{i,k} J_{ik}²`(Frobenius 范数²,
    算子范数² 的上界)。纯 Cauchy-Schwarz(逐输出坐标 `(J·v)_i=⟨J_i,v⟩`)。这是残差流
    传播系数 `γ_ℓ=‖J^ℓ‖²_F` 的界:`X_ℓ=J^ℓ·δa^ℓ ⟹ ‖X_ℓ‖²≤γ_ℓ‖δa^ℓ‖²`,供
    `residual_second_moment` 的逐层二阶界 hbnd。 -/
theorem linear_propagation_frobenius {n m : ℕ} (J : Fin n → Fin m → ℝ) (v : Fin m → ℝ) :
    ∑ i, (∑ k, J i k * v k) ^ 2 ≤ (∑ i, ∑ k, J i k ^ 2) * (∑ k, v k ^ 2) := by
  calc ∑ i, (∑ k, J i k * v k) ^ 2
      ≤ ∑ i, (∑ k, J i k ^ 2) * (∑ k, v k ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ = (∑ i, ∑ k, J i k ^ 2) * (∑ k, v k ^ 2) := by rw [← Finset.sum_mul]

/-- **传播后二阶界**(直接供 hbnd):`‖J‖²_F ≤ γ`(传播系数)、`‖v‖² ≤ C`(每层 SR
    方差,见证)⟹ `‖J·v‖² ≤ γ·C = b_ℓ`。取 v=δa^ℓ(或一阶线性化下 v=Δk^ℓ)。 -/
theorem propagated_second_moment_le {n m : ℕ} (J : Fin n → Fin m → ℝ) (v : Fin m → ℝ)
    (γ C : ℝ) (hγ : 0 ≤ γ)
    (hJ : (∑ i, ∑ k, J i k ^ 2) ≤ γ) (hv : (∑ k, v k ^ 2) ≤ C) :
    ∑ i, (∑ k, J i k * v k) ^ 2 ≤ γ * C :=
  (linear_propagation_frobenius J v).trans
    (mul_le_mul hJ hv (Finset.sum_nonneg fun _ _ => sq_nonneg _) hγ)

/-- **分数扰动 L² 界(接 `score_bridge`)**:K 个 key 的分数扰动向量,逐 key 由
    `score_bridge` 界 `|Δscore_key| ≤ scale·‖q‖·‖Δk_key‖`,则其 L² 范数²
    `∑_key Δscore_key² ≤ scale²·‖q‖²·∑_key‖Δk_key‖²`。`∑_key‖Δk_key‖²` 即见证(逐 key
    KV 扰动之和)。这把 `score_bridge` 的**逐 key 标量敏感**汇成层内**输入扰动向量**的
    界,与 `linear_propagation_frobenius` 的**输出传播**合成逐层链两端(中间
    attention Jacobian 是模型侧一阶线性化)。 -/
theorem score_perturbation_l2_le {d K : ℕ} (q : Fin d → ℝ) (k k' : Fin K → Fin d → ℝ)
    (scale : ℝ) (hs : 0 ≤ scale) :
    ∑ key, (scale * (∑ i, q i * k key i) - scale * (∑ i, q i * k' key i)) ^ 2
      ≤ scale ^ 2 * (∑ i, q i ^ 2) * (∑ key, ∑ i, (k key i - k' key i) ^ 2) := by
  have hq0 : (0:ℝ) ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ key, (scale * (∑ i, q i * k key i) - scale * (∑ i, q i * k' key i)) ^ 2
      ≤ ∑ key, scale ^ 2 * (∑ i, q i ^ 2) * (∑ i, (k key i - k' key i) ^ 2) := by
        refine Finset.sum_le_sum (fun key _ => ?_)
        have hb := score_bridge q (k key) (k' key) scale hs
        have hab := abs_le.mp hb
        refine (sq_le_sq' hab.1 hab.2).trans_eq ?_
        rw [mul_pow, mul_pow, Real.sq_sqrt hq0,
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    _ = scale ^ 2 * (∑ i, q i ^ 2) * (∑ key, ∑ i, (k key i - k' key i) ^ 2) := by
        rw [← Finset.mul_sum]

/-! ### ⑫ 词表→ω 转移(item3,最硬):E_ω[served TV] ≤ s/√2,sound 非一阶 -/

/-- **加权 √-Jensen**(凹):`ρ≥0`、`∑ρ=1`、`f≥0` ⟹ `∑_ω ρ_ω √(f_ω) ≤ √(∑_ω ρ_ω f_ω)`。
    Cauchy-Schwarz:`∑ ρ√f = ∑ (√ρ)(√ρ·√f) ≤ √(∑ρ)·√(∑ρf) = √(∑ρf)`。 -/
lemma sqrt_jensen_weighted {Ω : Type*} [Fintype Ω] (ρ f : Ω → ℝ)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hρ1 : ∑ ω, ρ ω = 1) (hf : ∀ ω, 0 ≤ f ω) :
    ∑ ω, ρ ω * Real.sqrt (f ω) ≤ Real.sqrt (∑ ω, ρ ω * f ω) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun ω => Real.sqrt (ρ ω)) (fun ω => Real.sqrt (ρ ω) * Real.sqrt (f ω))
  have hL : ∑ ω, Real.sqrt (ρ ω) * (Real.sqrt (ρ ω) * Real.sqrt (f ω))
          = ∑ ω, ρ ω * Real.sqrt (f ω) :=
    Finset.sum_congr rfl (fun ω _ => by rw [← mul_assoc, Real.mul_self_sqrt (hρ ω)])
  have hR1 : ∑ ω, Real.sqrt (ρ ω) ^ 2 = 1 := by
    rw [← hρ1]; exact Finset.sum_congr rfl (fun ω _ => Real.sq_sqrt (hρ ω))
  have hR2 : ∑ ω, (Real.sqrt (ρ ω) * Real.sqrt (f ω)) ^ 2 = ∑ ω, ρ ω * f ω :=
    Finset.sum_congr rfl (fun ω _ => by
      rw [mul_pow, Real.sq_sqrt (hρ ω), Real.sq_sqrt (hf ω)])
  rw [hL, hR1, hR2, Real.sqrt_one, one_mul] at hcs
  exact hcs

/-- **加权 ln-Jensen**(凹):`ρ≥0`、`∑ρ=1`、`Z>0` ⟹ `∑_ω ρ_ω ln(Z_ω) ≤ ln(∑_ω ρ_ω Z_ω)`。
    Mathlib 凹性 `Real.strictConcaveOn_log_Ioi`。 -/
lemma log_jensen_weighted {Ω : Type*} [Fintype Ω] (ρ Z : Ω → ℝ)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hρ1 : ∑ ω, ρ ω = 1) (hZ : ∀ ω, 0 < Z ω) :
    ∑ ω, ρ ω * Real.log (Z ω) ≤ Real.log (∑ ω, ρ ω * Z ω) := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (t := Finset.univ) (w := ρ) (p := Z)
    (fun ω _ => hρ ω) (by simpa using hρ1) (fun ω _ => Set.mem_Ioi.mpr (hZ ω))
  simpa only [smul_eq_mul] using h

/-- **top-k + 尾包络:质量加权预算的 sound 可算形式**。

    `served_tv_mean_le_massweighted` 的步预算是 `∑_v p_v B_v`,逐词表算是 `O(|V|)`
    —— 部署上不可接受(V=129,280)。本引理给出**仍然 sound** 的 `O(|S|)` 形式:
    高概率集合 `S` 精确计价,长尾只用一个保守包络 `Bmax`:
      `∑_v p_v B_v ≤ ∑_{v∈S} p_v B_v + (1 − ∑_{v∈S} p_v)·Bmax`。
    尾部质量 `1 − ∑_{v∈S} p_v` 在实际 softmax 上极小,故包络即使很松也不主导。
    这把质量加权界从"数学上摆脱最坏坐标"推进到"运行时可算"。 -/
theorem massweighted_topk_bound (p B : ι → ℝ) (S : Finset ι) (Bmax : ℝ)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (htail : ∀ v, v ∉ S → B v ≤ Bmax) :
    ∑ v, p v * B v
      ≤ (∑ v ∈ S, p v * B v) + (1 - ∑ v ∈ S, p v) * Bmax := by
  classical
  have hsplit : (∑ v ∈ Finset.univ \ S, p v * B v) + (∑ v ∈ S, p v * B v)
      = ∑ v, p v * B v :=
    Finset.sum_sdiff (Finset.subset_univ S)
  have htailsum : ∑ v ∈ Finset.univ \ S, p v * B v
      ≤ (∑ v ∈ Finset.univ \ S, p v) * Bmax := by
    calc ∑ v ∈ Finset.univ \ S, p v * B v
        ≤ ∑ v ∈ Finset.univ \ S, p v * Bmax :=
          Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
            (htail v (Finset.mem_sdiff.mp hv).2) (hp v))
      _ = (∑ v ∈ Finset.univ \ S, p v) * Bmax := by rw [Finset.sum_mul]
  have hmass : ∑ v ∈ Finset.univ \ S, p v = 1 - ∑ v ∈ S, p v := by
    have h := Finset.sum_sdiff (f := p) (Finset.subset_univ S)
    rw [hps] at h; linarith
  rw [hmass] at htailsum
  linarith [hsplit, htailsum]

/-- **乘积尾包络**:比 `massweighted_topk_bound` 更适合"扰动集中在低概率 token"的
    真实情形。那里的尾项是 `(尾质量)·max_v B_v`,当某个低概率 token 的 `B_v` 极大时
    会被它主导(实测 `max B_v ≈ 5.6×10⁸` 使可算形式反而空洞)。这里把包络取在
    **乘积** `p_v B_v` 上:
      `∑_v p_v B_v ≤ ∑_{v∈S} p_v B_v + |Sᶜ| · M`,其中 `M ≥ p_v B_v (v ∉ S)`。
    `p_v` 与 `B_v` 反相关(大扰动落在小概率上)恰使 `M` 很小 —— 与
    `tv_le_hellinger` 破 `ℓ∞` 墙是同一个结构性事实的两次利用。两式都 sound,
    部署时取二者较小者即可。 -/
theorem massweighted_prodenv_bound [DecidableEq ι]
    (p B : ι → ℝ) (S : Finset ι) (M : ℝ)
    (htail : ∀ v, v ∉ S → p v * B v ≤ M) :
    ∑ v, p v * B v
      ≤ (∑ v ∈ S, p v * B v) + ((Finset.univ \ S).card : ℝ) * M := by
  have hsplit : (∑ v ∈ Finset.univ \ S, p v * B v) + (∑ v ∈ S, p v * B v)
      = ∑ v, p v * B v :=
    Finset.sum_sdiff (Finset.subset_univ S)
  have htailsum : ∑ v ∈ Finset.univ \ S, p v * B v
      ≤ ((Finset.univ \ S).card : ℝ) * M := by
    calc ∑ v ∈ Finset.univ \ S, p v * B v
        ≤ ∑ _v ∈ Finset.univ \ S, M :=
          Finset.sum_le_sum (fun v hv => htail v (Finset.mem_sdiff.mp hv).2)
      _ = ((Finset.univ \ S).card : ℝ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hsplit, htailsum]

/-- **质量加权 served-TV 界(逐词表 MGF,偏差显式)**:比
    `served_tv_mean_le_omega_subgaussian` 严格更一般 —— 每个词表坐标 `v` 各带自己的
    ω-MGF 上界 `Bv v`(可写成 `exp(b_v + s_v²/2)`:`b_v=E_ω[δ_v]` 是**确定性偏差**,
    `s_v²` 是波动 proxy),结论是**按 p 质量加权**的
      `E_ω[TV] ≤ √(log ∑_v p_v · Bv v)`。

    要点:大扰动若落在**低概率** token 上,只按 `p_v` 权重进入 `∑_v p_v Bv v`,
    不再被最坏坐标绑架 —— 这正是 W3SLE 实测(E_out 达 3.1–4.3 而 served TV 仅 0.118)
    的结构性解释,也把非线性网络里无法假设掉的偏差 `b_v` 显式计价。
    取 `Bv ≡ exp(s²/2)` 即退化为 `served_tv_mean_le_omega_subgaussian`。 -/
theorem served_tv_mean_le_massweighted [Nonempty ι]
    {Ω : Type*} [Fintype Ω]
    (p : ι → ℝ) (δ : Ω → ι → ℝ) (ρ : Ω → ℝ) (Bv : ι → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hρ1 : ∑ ω, ρ ω = 1)
    (hcenter : ∀ ω, ∑ v, p v * δ ω v = 0)
    (hmgf : ∀ v, ∑ ω, ρ ω * Real.exp (δ ω v) ≤ Bv v) :
    ∑ ω, ρ ω * WitCert.TV p
        (fun v => p v * Real.exp (δ ω v) / (∑ u, p u * Real.exp (δ ω u)))
      ≤ Real.sqrt (Real.log (∑ v, p v * Bv v)) := by
  set Z : Ω → ℝ := fun ω => ∑ u, p u * Real.exp (δ ω u) with hZdef
  have hZ1 : ∀ ω, 1 ≤ Z ω := by
    intro ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := δ ω)
      (fun i _ => hp i) (by simpa using hps) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (1:ℝ) = Real.exp (∑ v, p v * δ ω v) := by rw [hcenter ω, Real.exp_zero]
      _ ≤ Z ω := hj
  have hZpos : ∀ ω, 0 < Z ω := fun ω => lt_of_lt_of_le one_pos (hZ1 ω)
  have hTV : ∀ ω, WitCert.TV p (fun v => p v * Real.exp (δ ω v) / Z ω)
      ≤ Real.sqrt (Real.log (Z ω)) := by
    intro ω
    have hσnn : (0:ℝ) ≤ Real.sqrt (2 * Real.log (Z ω)) := Real.sqrt_nonneg _
    have hsubgk : ∑ v, p v * Real.exp (δ ω v)
        ≤ Real.exp ((Real.sqrt (2 * Real.log (Z ω))) ^ 2 / 2) := by
      have he : (Real.sqrt (2 * Real.log (Z ω))) ^ 2 / 2 = Real.log (Z ω) := by
        rw [Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg (hZ1 ω)))]; ring
      rw [he, Real.exp_log (hZpos ω)]
    have hk := served_tv_le_subgaussian p (δ ω) (Real.sqrt (2 * Real.log (Z ω)))
      hσnn hp hps (hcenter ω) hsubgk
    have hsimp : Real.sqrt (2 * Real.log (Z ω)) / Real.sqrt 2
        = Real.sqrt (Real.log (Z ω)) := by
      rw [← Real.sqrt_div (mul_nonneg (by norm_num) (Real.log_nonneg (hZ1 ω)))]
      congr 1; ring
    rw [hsimp] at hk
    exact hk
  -- Fubini:E_ω Z = ∑_v p_v · E_ω[e^{δ_v}] ≤ ∑_v p_v · Bv v(**逐 v 加权**)
  have hZbound : ∑ ω, ρ ω * Z ω ≤ ∑ v, p v * Bv v := by
    have hfub : ∑ ω, ρ ω * Z ω = ∑ u, p u * (∑ ω, ρ ω * Real.exp (δ ω u)) := by
      simp only [hZdef, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun u _ =>
        Finset.sum_congr rfl (fun ω _ => by ring))
    rw [hfub]
    exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hmgf u) (hp u))
  have hSumZpos : 0 < ∑ ω, ρ ω * Z ω := by
    have h1 : (1:ℝ) ≤ ∑ ω, ρ ω * Z ω := by
      calc (1:ℝ) = ∑ ω, ρ ω * 1 := by simp only [mul_one]; exact hρ1.symm
        _ ≤ ∑ ω, ρ ω * Z ω :=
          Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hZ1 ω) (hρ ω))
    linarith
  calc ∑ ω, ρ ω * WitCert.TV p
          (fun v => p v * Real.exp (δ ω v) / (∑ u, p u * Real.exp (δ ω u)))
      ≤ ∑ ω, ρ ω * Real.sqrt (Real.log (Z ω)) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hTV ω) (hρ ω))
    _ ≤ Real.sqrt (∑ ω, ρ ω * Real.log (Z ω)) :=
        sqrt_jensen_weighted ρ (fun ω => Real.log (Z ω)) hρ hρ1
          (fun ω => Real.log_nonneg (hZ1 ω))
    _ ≤ Real.sqrt (Real.log (∑ ω, ρ ω * Z ω)) :=
        Real.sqrt_le_sqrt (log_jensen_weighted ρ Z hρ hρ1 hZpos)
    _ ≤ Real.sqrt (Real.log (∑ v, p v * Bv v)) :=
        Real.sqrt_le_sqrt (Real.log_le_log hSumZpos hZbound)

/-- **词表→ω sub-Gaussian 转移(item3,sound 非一阶)**:输出 logit 扰动 δ 逐 ω 在
    served 分布 p 下中心化(`∑_v p_v δ(ω)_v=0`,gauge),且逐 vocab 在 ω 下 sub-Gaussian
    (`E_ω[e^{δ(ω)_v}] ≤ e^{s²/2}`;该前提**已由 `WitCert.Apriori.served_tv_mean_le_cum_C`
    机检导出** —— MGF 跨层张量化 + McDiarmid.sum_exp_le_of_mean_zero,读出 s²=cum_C),
    则**期望 served TV**
    受纯方差量 s 控制:`E_ω[TV(p,p'(ω))] ≤ s/√2`。链条全为精确不等式:逐 ω
    `served_tv_le_subgaussian`(σ²=2ln Z)⟹ TV≤√(ln Z);√-Jensen;ln-Jensen;Fubini
    把 `E_ω Z=E_p E_ω[e^δ]≤e^{s²/2}` 收口。**破 soundness-variance 张力**:sound 且
    方差级(非一阶近似)。这是把见证的 ω-方差预算转成 vocab-softmax served 界的桥。 -/
theorem served_tv_mean_le_omega_subgaussian [Nonempty ι]
    {Ω : Type*} [Fintype Ω]
    (p : ι → ℝ) (δ : Ω → ι → ℝ) (ρ : Ω → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hρ1 : ∑ ω, ρ ω = 1)
    (hcenter : ∀ ω, ∑ v, p v * δ ω v = 0)
    (hsubg : ∀ v, ∑ ω, ρ ω * Real.exp (δ ω v) ≤ Real.exp (s ^ 2 / 2)) :
    ∑ ω, ρ ω * WitCert.TV p
        (fun v => p v * Real.exp (δ ω v) / (∑ u, p u * Real.exp (δ ω u)))
      ≤ s / Real.sqrt 2 := by
  set Z : Ω → ℝ := fun ω => ∑ u, p u * Real.exp (δ ω u) with hZdef
  -- Z ω ≥ 1(Jensen exp,p-中心化)
  have hZ1 : ∀ ω, 1 ≤ Z ω := by
    intro ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p) (p := δ ω)
      (fun i _ => hp i) (by simpa using hps) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (1:ℝ) = Real.exp (∑ v, p v * δ ω v) := by rw [hcenter ω, Real.exp_zero]
      _ ≤ Z ω := hj
  have hZpos : ∀ ω, 0 < Z ω := fun ω => lt_of_lt_of_le one_pos (hZ1 ω)
  -- 逐 ω:TV(ω) ≤ √(ln Z ω)
  have hTV : ∀ ω, WitCert.TV p (fun v => p v * Real.exp (δ ω v) / Z ω)
      ≤ Real.sqrt (Real.log (Z ω)) := by
    intro ω
    have hσnn : (0:ℝ) ≤ Real.sqrt (2 * Real.log (Z ω)) := Real.sqrt_nonneg _
    have hsubgk : ∑ v, p v * Real.exp (δ ω v)
        ≤ Real.exp ((Real.sqrt (2 * Real.log (Z ω))) ^ 2 / 2) := by
      have he : (Real.sqrt (2 * Real.log (Z ω))) ^ 2 / 2 = Real.log (Z ω) := by
        rw [Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg (hZ1 ω)))]; ring
      rw [he, Real.exp_log (hZpos ω)]
    have hk := served_tv_le_subgaussian p (δ ω) (Real.sqrt (2 * Real.log (Z ω)))
      hσnn hp hps (hcenter ω) hsubgk
    have hsimp : Real.sqrt (2 * Real.log (Z ω)) / Real.sqrt 2
        = Real.sqrt (Real.log (Z ω)) := by
      rw [← Real.sqrt_div (mul_nonneg (by norm_num) (Real.log_nonneg (hZ1 ω)))]
      congr 1; ring
    rw [hsimp] at hk
    exact hk
  -- Fubini:E_ω Z ≤ e^{s²/2}
  have hZbound : ∑ ω, ρ ω * Z ω ≤ Real.exp (s ^ 2 / 2) := by
    have hfub : ∑ ω, ρ ω * Z ω = ∑ u, p u * (∑ ω, ρ ω * Real.exp (δ ω u)) := by
      simp only [hZdef, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun u _ =>
        Finset.sum_congr rfl (fun ω _ => by ring))
    rw [hfub]
    calc ∑ u, p u * (∑ ω, ρ ω * Real.exp (δ ω u))
        ≤ ∑ u, p u * Real.exp (s ^ 2 / 2) :=
          Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hsubg u) (hp u))
      _ = Real.exp (s ^ 2 / 2) := by rw [← Finset.sum_mul, hps, one_mul]
  -- E_ω Z ≥ 1 > 0(Z_ω≥1)
  have hSumZpos : 0 < ∑ ω, ρ ω * Z ω := by
    have h1 : (1:ℝ) ≤ ∑ ω, ρ ω * Z ω := by
      calc (1:ℝ) = ∑ ω, ρ ω * 1 := by simp only [mul_one]; exact hρ1.symm
        _ ≤ ∑ ω, ρ ω * Z ω :=
          Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hZ1 ω) (hρ ω))
    linarith
  -- 组装:Σρ TV ≤ Σρ√lnZ ≤ √(Σρ lnZ) ≤ √(ln Σρ Z) ≤ √(s²/2) = s/√2
  calc ∑ ω, ρ ω * WitCert.TV p
          (fun v => p v * Real.exp (δ ω v) / (∑ u, p u * Real.exp (δ ω u)))
      ≤ ∑ ω, ρ ω * Real.sqrt (Real.log (Z ω)) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hTV ω) (hρ ω))
    _ ≤ Real.sqrt (∑ ω, ρ ω * Real.log (Z ω)) :=
        sqrt_jensen_weighted ρ (fun ω => Real.log (Z ω)) hρ hρ1
          (fun ω => Real.log_nonneg (hZ1 ω))
    _ ≤ Real.sqrt (Real.log (∑ ω, ρ ω * Z ω)) :=
        Real.sqrt_le_sqrt (log_jensen_weighted ρ Z hρ hρ1 hZpos)
    _ ≤ Real.sqrt (s ^ 2 / 2) := by
        apply Real.sqrt_le_sqrt
        calc Real.log (∑ ω, ρ ω * Z ω)
            ≤ Real.log (Real.exp (s ^ 2 / 2)) := Real.log_le_log hSumZpos hZbound
          _ = s ^ 2 / 2 := Real.log_exp _
    _ = s / Real.sqrt 2 := by rw [Real.sqrt_div (sq_nonneg s) 2, Real.sqrt_sq hs]

end WitCert.Calculus
