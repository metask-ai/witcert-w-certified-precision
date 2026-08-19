/-
  **L12:a-priori served 界的见证实例化** —— 把 `Bridges.served_tv_mean_le_omega_subgaussian`
  悬空的 `hsubg`(逐 vocab 在 ω 下的 sub-Gaussian MGF)由 McDiarmid 的 Hoeffding 引理
  在**乘积测度上张量化**得到,并读出 `s² = cum_C`(逐层见证方差之和)。

  这是 ①c a-priori 链条的最后一段:此前 `hsubg` 是"由 McDiarmid 提供"的口头承诺,
  本文件把它变成机器检查的推导。关键一步是**张量化**(`mgf_tensorize`):跨层独立
  ⟹ 和的 MGF = 各层 MGF 之积 ⟹ 指数上**方差相加**。这正是 cum_C 作为逐层方差
  之和的来历(与 `Bridges.residual_second_moment_orthogonal` 的二阶 Pythagorean 同源,
  一个在二阶矩层面、一个在 MGF 层面)。

  分层:本文件是 L12,import Bridges(L6)与 McDiarmid(L10);反向依赖不存在。
-/
import WitCert.Bridges
import WitCert.McDiarmid
import WitCert.CumLoss

open BigOperators Real
open WitCert.Calculus.Ville
open WitCert.Calculus.CumLoss

namespace WitCert.Calculus.Apriori

variable {A : Type*} [Fintype A]
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- 乘积测度归一:`∑_ω ∏_m q_m(ω_m) = 1`(逐坐标归一的 Fubini)。 -/
lemma prod_measure_total (D : L → Draw A) :
    ∑ ω : L → A, (∏ m, (D m).p (ω m)) = 1 := by
  rw [← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun m a => (D m).p a)]
  simp only [Draw.total, Finset.prod_const_one]

/-! ### ① 张量化:乘积测度下和的 MGF = 各层 MGF 之积 -/

/-- **MGF 张量化**:跨层独立(乘积测度 `wt ω = ∏_m q_m(ω_m)`)+ 各层贡献只依赖自身
    抽签(`f_ℓ(ω_ℓ)`)⟹ `E_ω[e^{∑_ℓ f_ℓ}] = ∏_ℓ E_{ω_ℓ}[e^{f_ℓ}]`。
    `Real.exp_sum` 把和的指数拆成积,再由乘积测度 Fubini(`Finset.prod_univ_sum`)
    把 ∑_ω ∏_m 换成 ∏_m ∑_a。**指数上方差相加的代数根源**。 -/
theorem mgf_tensorize (D : L → Draw A) (f : L → A → ℝ) :
    ∑ ω : L → A, (∏ m, (D m).p (ω m)) * Real.exp (∑ ℓ, f ℓ (ω ℓ))
      = ∏ ℓ, (∑ a, (D ℓ).p a * Real.exp (f ℓ a)) := by
  have hstep : ∀ ω : L → A, (∏ m, (D m).p (ω m)) * Real.exp (∑ ℓ, f ℓ (ω ℓ))
      = ∏ m, ((D m).p (ω m) * Real.exp (f m (ω m))) := by
    intro ω
    rw [Real.exp_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), ← Fintype.piFinset_univ,
      ← Finset.prod_univ_sum (fun _ => Finset.univ)
          (fun m a => (D m).p a * Real.exp (f m a))]

/-- **张量化 + 逐层 sub-Gaussian ⟹ 累计 sub-Gaussian**:每层 MGF `≤ e^{C_ℓ/2}` ⟹
    总 MGF `≤ e^{(∑_ℓ C_ℓ)/2}`。**proxy 相加**:`s² = ∑_ℓ C_ℓ = cum_C`。 -/
theorem mgf_tensorize_le (D : L → Draw A) (f : L → A → ℝ) (C : L → ℝ)
    (hC : ∀ ℓ, (∑ a, (D ℓ).p a * Real.exp (f ℓ a)) ≤ Real.exp (C ℓ / 2)) :
    ∑ ω : L → A, (∏ m, (D m).p (ω m)) * Real.exp (∑ ℓ, f ℓ (ω ℓ))
      ≤ Real.exp ((∑ ℓ, C ℓ) / 2) := by
  rw [mgf_tensorize]
  calc ∏ ℓ, (∑ a, (D ℓ).p a * Real.exp (f ℓ a))
      ≤ ∏ ℓ, Real.exp (C ℓ / 2) := by
        refine Finset.prod_le_prod (fun ℓ _ => ?_) (fun ℓ _ => hC ℓ)
        exact Finset.sum_nonneg
          (fun a _ => mul_nonneg ((D ℓ).nonneg a) (Real.exp_pos _).le)
    _ = Real.exp ((∑ ℓ, C ℓ) / 2) := by
        rw [← Real.exp_sum, ← Finset.sum_div]

/-! ### ② 逐层 Hoeffding(McDiarmid 的实例化,λ=1) -/

/-- **逐层 MGF 界**(McDiarmid `sum_exp_le_of_mean_zero` 在 λ=1 的实例化):SR 增量
    均值零(鞅)且取值于 `[lo,hi]` ⟹ `E[e^{g}] ≤ e^{C/2}`,其中
    **`C = (hi−lo)²/4`** 恰是 Hoeffding 方差 proxy —— 每层见证 `C_ℓ` 的来历。 -/
lemma coord_mgf_le [Nonempty A] (D : Draw A) (g : A → ℝ) {lo hi : ℝ}
    (hbdd : ∀ x, lo ≤ g x ∧ g x ≤ hi)
    (hmean : ∑ x, D.p x * g x = 0) :
    ∑ x, D.p x * Real.exp (g x) ≤ Real.exp ((hi - lo) ^ 2 / 4 / 2) := by
  have h := WitCert.Calculus.McDiarmid.sum_exp_le_of_mean_zero D g 1 hbdd hmean
  simp only [one_mul, one_pow] at h
  calc ∑ x, D.p x * Real.exp (g x) ≤ Real.exp ((hi - lo) ^ 2 / 8) := h
    _ = Real.exp ((hi - lo) ^ 2 / 4 / 2) := by ring_nf

/-! ### ③ 合成:a-priori served-TV 界,proxy 即 cum_C -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **a-priori served-TV 界(端到端,proxy = cum_C)**:输出 logit 扰动逐 vocab 分解为
    逐层贡献之和 `δ(ω)_v = ∑_ℓ g_{v,ℓ}(ω_ℓ)`(残差流加性 + 一阶线性化,增量 ω-local),
    每层 SR 抽签独立(乘积测度)、增量均值零(鞅)且有界(见证 `(hi−lo)²/4 ≤ C_ℓ`),
    则**期望 served TV 受累计见证方差控制**:
      `E_ω[TV(p, p'(ω))] ≤ √(cum_C)/√2`,`cum_C = ∑_ℓ C_ℓ`。

    这把 `Bridges.served_tv_mean_le_omega_subgaussian` 的 `hsubg` 由 McDiarmid 的
    Hoeffding MGF 张量化**导出**,不再是外部假设。链条:逐层 Hoeffding(`coord_mgf_le`)
    → 跨层张量化(`mgf_tensorize_le`,proxy 相加)→ 词表→ω sound 转移
    (`served_tv_mean_le_omega_subgaussian`:逐 ω kernel + 两次 Jensen + Fubini)。

    **口径(引用必带)**:此处 `C_ℓ` 是**传播到 logit 后**的逐层方差 proxy
    (`(hi−lo)²/4`,其中 `hi−lo` 是 `g_{v,ℓ}` 即"该层 SR 增量经 J^ℓ 与 head 行"到达
    logit 的幅度),故 `cum_C = ∑_ℓ C_ℓ` 是**传播后**累计方差;与原始见证的
    KV 侧 cum_C 之间差 item2 的传播常数(`Bridges.linear_propagation_frobenius` /
    `score_perturbation_l2_le` 给出该常数的 sound 界,数值实例化仍待模型侧测量)。

    `hcenter`(vocab 侧 p-中心化)是 gauge:softmax 对逐 ω 加常数不变,且该常数
    `c(ω)=∑_v p_v δ(ω)_v` 本身仍是逐层贡献之和、仍逐层均值零,故重规范不破坏其余前提
    (范围至多加倍)—— 此处作前提列出,不另证。
    `g_{v,ℓ}` 只依赖 `ω_ℓ` 即一阶线性化(增量 ω-local),与 item1 同一模型假设。 -/
theorem served_tv_mean_le_cum_C [Nonempty A]
    (p : ι → ℝ) (D : L → Draw A) (g : ι → L → A → ℝ)
    (C : L → ℝ) (lo hi : ι → L → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (hcenter : ∀ ω : L → A, ∑ v, p v * (∑ ℓ, g v ℓ (ω ℓ)) = 0)
    (hbdd : ∀ v ℓ x, lo v ℓ ≤ g v ℓ x ∧ g v ℓ x ≤ hi v ℓ)
    (hmean : ∀ v ℓ, ∑ x, (D ℓ).p x * g v ℓ x = 0)
    (hrange : ∀ v ℓ, (hi v ℓ - lo v ℓ) ^ 2 / 4 ≤ C ℓ) :
    ∑ ω : L → A, (∏ m, (D m).p (ω m)) *
        WitCert.TV p (fun v => p v * Real.exp (∑ ℓ, g v ℓ (ω ℓ)) /
                        (∑ u, p u * Real.exp (∑ ℓ, g u ℓ (ω ℓ))))
      ≤ Real.sqrt (∑ ℓ, C ℓ) / Real.sqrt 2 := by
  -- cum_C ≥ 0(每层 C_ℓ ≥ (hi−lo)²/4 ≥ 0;ι 非空提供见证 v)
  have hCnn : ∀ ℓ, 0 ≤ C ℓ := by
    intro ℓ
    obtain ⟨v⟩ := ‹Nonempty ι›
    exact le_trans (by positivity) (hrange v ℓ)
  have hcum : (0:ℝ) ≤ ∑ ℓ, C ℓ := Finset.sum_nonneg (fun ℓ _ => hCnn ℓ)
  refine served_tv_mean_le_omega_subgaussian (Ω := L → A) p
    (fun ω v => ∑ ℓ, g v ℓ (ω ℓ))
    (fun ω => ∏ m, (D m).p (ω m)) (Real.sqrt (∑ ℓ, C ℓ)) (Real.sqrt_nonneg _)
    hp hps (fun ω => Finset.prod_nonneg (fun m _ => (D m).nonneg (ω m)))
    (prod_measure_total D) hcenter ?_
  -- hsubg:逐 vocab 的 ω-MGF ≤ e^{cum_C/2},由张量化 + 逐层 Hoeffding
  intro v
  have hs2 : (Real.sqrt (∑ ℓ, C ℓ)) ^ 2 / 2 = (∑ ℓ, C ℓ) / 2 := by
    rw [Real.sq_sqrt hcum]
  rw [hs2]
  refine mgf_tensorize_le D (g v) C (fun ℓ => ?_)
  calc ∑ a, (D ℓ).p a * Real.exp (g v ℓ a)
      ≤ Real.exp ((hi v ℓ - lo v ℓ) ^ 2 / 4 / 2) :=
        coord_mgf_le (D ℓ) (g v ℓ) (fun x => hbdd v ℓ x) (hmean v ℓ)
    _ ≤ Real.exp (C ℓ / 2) := by
        exact Real.exp_le_exp.mpr (by linarith [hrange v ℓ])

/-! ### ④ 承重梁:expected-loss → 条件 MGF → 累计账本(请求级尾概率) -/

/-- **Bernoulli-MGF 支配**:`0≤L≤1` 且 `E[L] ≤ μ`(λ≥0)⟹
    `E[e^{λL}] ≤ 1 + μ(e^λ−1)`。凭 `t ↦ e^{λt}` 在 [0,1] 上的凸性取弦
    (端点 0 与 λ),再用 `e^λ−1 ≥ 0` 把 `E[L]` 换成上界 μ。
    **只要期望界,不要范围界** —— 这正是把 expected-TV 结果接进账本的入口。 -/
theorem bernoulli_mgf_le (D : Draw A) (L : A → ℝ) (mu lam : ℝ)
    (hlam : 0 ≤ lam) (hL0 : ∀ x, 0 ≤ L x) (hL1 : ∀ x, L x ≤ 1)
    (hmean : ∑ x, D.p x * L x ≤ mu) :
    ∑ x, D.p x * Real.exp (lam * L x) ≤ 1 + mu * (Real.exp lam - 1) := by
  have hE1 : (0:ℝ) ≤ Real.exp lam - 1 := by
    have : Real.exp 0 ≤ Real.exp lam := Real.exp_le_exp.mpr hlam
    rw [Real.exp_zero] at this; linarith
  -- 弦引理:∀ t∈[0,1], e^{λt} ≤ 1 + t(e^λ−1)
  have chord : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Real.exp (lam * t) ≤ 1 + t * (Real.exp lam - 1) := by
    intro t ht0 ht1
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ lam)
      (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have hcm : Real.exp (lam * t) = Real.exp (t * lam) := by rw [mul_comm]
    rw [hcm]; linarith [hc]
  calc ∑ x, D.p x * Real.exp (lam * L x)
      ≤ ∑ x, D.p x * (1 + L x * (Real.exp lam - 1)) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          (chord (L x) (hL0 x) (hL1 x)) (D.nonneg x))
    _ = 1 + (∑ x, D.p x * L x) * (Real.exp lam - 1) := by
        rw [Finset.sum_congr rfl (fun x _ => by ring :
              ∀ x ∈ Finset.univ, D.p x * (1 + L x * (Real.exp lam - 1))
                = D.p x + (D.p x * L x) * (Real.exp lam - 1)),
            Finset.sum_add_distrib, D.total, ← Finset.sum_mul]
    _ ≤ 1 + mu * (Real.exp lam - 1) := by
        have := mul_le_mul_of_nonneg_right hmean hE1; linarith

/-- **e-process 因子 ≤ 1**(承重梁的账本接口形态):取 `ψ = log(1+μ(e^λ−1))`,
    则 `E[e^{λL − ψ}] ≤ 1` —— 恰是 `cumloss_admission` 的 `hmean` 前提(m≡0)。 -/
theorem eprocess_factor_le_one_of_expected (D : Draw A) (L : A → ℝ) (mu lam : ℝ)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hL0 : ∀ x, 0 ≤ L x) (hL1 : ∀ x, L x ≤ 1)
    (hmean : ∑ x, D.p x * L x ≤ mu) :
    ∑ x, D.p x *
        Real.exp (lam * L x - Real.log (1 + mu * (Real.exp lam - 1))) ≤ 1 := by
  have hE1 : (0:ℝ) ≤ Real.exp lam - 1 := by
    have : Real.exp 0 ≤ Real.exp lam := Real.exp_le_exp.mpr hlam
    rw [Real.exp_zero] at this; linarith
  have hZ : (0:ℝ) < 1 + mu * (Real.exp lam - 1) := by nlinarith
  have hsplit : ∀ x, D.p x *
      Real.exp (lam * L x - Real.log (1 + mu * (Real.exp lam - 1)))
      = (D.p x * Real.exp (lam * L x)) / (1 + mu * (Real.exp lam - 1)) := by
    intro x
    rw [Real.exp_sub, Real.exp_log hZ, mul_div_assoc]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), ← Finset.sum_div]
  rw [div_le_one hZ]
  exact bernoulli_mgf_le D L mu lam hlam hL0 hL1 hmean

/-- **承重梁(合成):逐步期望界 ⟹ 请求级 anytime 尾概率**。
    若每一步的条件期望损失受 `μ`(同一常数上界)控制且 `0≤L≤1`,取
    `ψ ≡ log(1+μ(e^λ−1))`、`m ≡ 0`,并且 admission 一直维持账面,则
      `Pr(∃t ≤ T: 累计损失 > B_t) ≤ δ`。
    **这就是把 a-priori expected-TV 结果接进请求级风险预算的那根梁**:
    `served_tv_mean_le_cum_C` 给的是 `E_ω[TV] ≤ √(cum_C/2)`(单一固定输出、
    无时间索引);本定理说明——**只要**该期望界能升级为逐步**条件**期望界
    `E[L_t | F_{t−1}] ≤ μ`,凸性即免费给出条件 MGF,账本随即闭合。
    仍待续(诚实):把 `E_ω[TV]` 升级成条件版需 Doob 分解(见下一节)。 -/
theorem request_tail_of_expected_loss
    {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (L : List sigma → sigma → ℝ) (B : ℕ → ℝ) {lam delta mu : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hmu : 0 ≤ mu)
    (hL0 : ∀ h x, 0 ≤ L h x) (hL1 : ∀ h x, L h x ≤ 1)
    (hcond : ∀ h, ∑ x, D.p x * L h x ≤ mu)
    (hadm : ∀ h : List sigma,
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred
                 (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP D
        (fun h => B h.length < cumStep L h) T [] ≤ delta := by
  refine cumloss_admission D L (fun _ => (0:ℝ))
    (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) B hlam hdelta hdelta1 ?_ hadm
  intro h
  simpa using eprocess_factor_le_one_of_expected D (L h) mu lam hlam.le hmu
    (hL0 h) (hL1 h) (hcond h)

/-! ### ⑤ Doob 版:去掉「层贡献只依赖自身抽签」假设 -/

/-- **Doob 版 sub-Gaussian proxy(带显式偏差项)**(替代 `mgf_tensorize_le` 的
    ω-local 前提)。

    `mgf_tensorize_le` 要求 `F(ω)=∑_ℓ f_ℓ(ω_ℓ)`(每层贡献只依赖自己的抽签)。真实
    Transformer 里第 ℓ 层的输入已受前面舍入影响,后层贡献一般依赖 `ω_1..ω_ℓ` ——
    该前提等价于**一阶线性化**,而 W3GAM 真机测量(线性比 14.1≈16,饱和)**证伪**了
    它在本模型可注入量程上的成立性。

    本定理走 Doob 分解 `D_ℓ = E[F|F_ℓ] − E[F|F_{ℓ−1}]`(由 `condE` 逐层实现),只要
    **有界差分** `BddDiffAt F c` 即得
      `E[e^F] ≤ exp(E[F] + s²/2)`,`s² = ∑_ℓ c_ℓ²/4`。
    **F 可以任意非线性、自适应地依赖整条抽签序列**,且**不要求 F 无偏** ——
    逐层舍入无偏(SR 鞅)在非线性网络中**不传递**到最终 logit(路由翻转、激活、
    后续层都会引入偏差),所以偏差 `E[F]` 必须显式出现在界里,不能假设掉。
    这正是评审要求的"确定性偏差 + 零均值波动"分解:`s²` 只承担波动,`E[F]` 独立计价。 -/
theorem doob_mgf_le_biased {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (F : List sigma → ℝ) (c : ℕ → ℝ) (T : ℕ)
    (hF : WitCert.Calculus.McDiarmid.BddDiffAt F c) :
    WitCert.Calculus.McDiarmid.condE D (fun ω => Real.exp (F ω)) T []
      ≤ Real.exp (WitCert.Calculus.McDiarmid.condE D F T []
                  + (∑ i ∈ Finset.range T, c i ^ 2 / 4) / 2) := by
  have h := WitCert.Calculus.McDiarmid.condE_exp_le D hF 1 T ([] : List sigma)
  simp only [one_mul, one_pow, List.length_nil, Nat.zero_add] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have he : (∑ i ∈ Finset.range T, c i ^ 2 / 4) / 2
      = (∑ i ∈ Finset.range T, c i ^ 2) / 8 := by
    rw [← Finset.sum_div]; ring
  rw [he]

/-- 无偏特例(`E[F]=0`):`E[e^F] ≤ e^{s²/2}`。**仅在偏差可独立论证为零时可用** ——
    非线性网络里这需要论证,不是逐层无偏的自动推论。 -/
theorem doob_mgf_le {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (F : List sigma → ℝ) (c : ℕ → ℝ) (T : ℕ)
    (hF : WitCert.Calculus.McDiarmid.BddDiffAt F c)
    (hmean : WitCert.Calculus.McDiarmid.condE D F T [] = 0) :
    WitCert.Calculus.McDiarmid.condE D (fun ω => Real.exp (F ω)) T []
      ≤ Real.exp ((∑ i ∈ Finset.range T, c i ^ 2 / 4) / 2) := by
  have h := doob_mgf_le_biased D F c T hF
  rwa [hmean, zero_add] at h

/-! ### ⑥ 左端:固定输出的期望界 ⟹ 逐步条件界 ⟹ 账本闭合 -/

lemma TV_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) : 0 ≤ WitCert.TV p q := by
  unfold WitCert.TV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- 两个概率分布之间 `TV ≤ 1`(`|p−q| ≤ p+q`,两边和为 2)。 -/
lemma TV_le_one {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v)
    (hps : ∑ v, p v = 1) (hqs : ∑ v, q v = 1) : WitCert.TV p q ≤ 1 := by
  unfold WitCert.TV
  have hb : ∑ t, |p t - q t| ≤ ∑ t, (p t + q t) :=
    Finset.sum_le_sum (fun t _ => abs_le.mpr
      ⟨by linarith [hp t, hq t], by linarith [hp t, hq t]⟩)
  rw [Finset.sum_add_distrib, hps, hqs] at hb
  linarith

/-- **一个 token 的全部逐层舍入抽签**打包成账本的**一步**:乘积抽签测度。
    这是左端的关键建模选择 —— 账本的 σ 不是"一次舍入",而是"一个解码步的抽签向量",
    于是 `cumloss_admission` 要的一步条件期望 `∑_x D.p x · L h x` **恰好就是**
    `served_tv_mean_le_cum_C` 的结论形状。 -/
noncomputable def prodDraw (D : L → Draw A) : Draw (L → A) where
  p := fun ω => ∏ m, (D m).p (ω m)
  nonneg := fun ω => Finset.prod_nonneg (fun m _ => (D m).nonneg (ω m))
  total := prod_measure_total D

/-- 该步的 served 损失:压缩 served 分布与精确 served 分布的 TV。 -/
noncomputable def servedLoss (p : List (L → A) → ι → ℝ)
    (g : List (L → A) → ι → L → A → ℝ) : List (L → A) → (L → A) → ℝ :=
  fun h ω => WitCert.TV (p h)
    (fun v => p h v * Real.exp (∑ ℓ, g h v ℓ (ω ℓ)) /
              (∑ u, p h u * Real.exp (∑ ℓ, g h u ℓ (ω ℓ))))

/-- **左端合成:a-priori served-TV ⟹ 请求级 anytime 尾概率**。

    对**每个历史 h** 应用 `served_tv_mean_le_cum_C`,即得逐步**条件**期望界
    `E[L_t | F_{t−1}=h] ≤ √(cum_C/2) ≤ μ`;再由承重梁
    (`request_tail_of_expected_loss`:Bernoulli-MGF 支配 → e-process 因子 → 账本)
    得 `Pr(∃t≤T: ∑_{s≤t} L_s > B_t) ≤ δ`。

    **这就是把 a-priori served-TV 结果真正接进请求级风险预算**:此前账本闭合在
    "假设有条件期望界"上,现在它闭合在本文的 served-TV 定理上。

    口径(仍然诚实):`C_ℓ` 是**传播到 logit 后**的逐层方差 proxy;`g` 逐层 ω-local
    是一阶线性化(W3GAM 实测证伪其在本模型可注入量程上的成立性,正解见
    `doob_mgf_le` 的有界差分形态,其 proxy 形状与常数一致)。 -/
theorem request_tail_of_served_tv [Nonempty A]
    (D : L → Draw A)
    (p : List (L → A) → ι → ℝ) (g : List (L → A) → ι → L → A → ℝ)
    (C : L → ℝ) (lo hi : List (L → A) → ι → L → ℝ) (B : ℕ → ℝ)
    {lam delta mu : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hmu0 : 0 ≤ mu)
    (hp : ∀ h v, 0 ≤ p h v) (hps : ∀ h, ∑ v, p h v = 1)
    (hcenter : ∀ h (ω : L → A), ∑ v, p h v * (∑ ℓ, g h v ℓ (ω ℓ)) = 0)
    (hbdd : ∀ h v ℓ x, lo h v ℓ ≤ g h v ℓ x ∧ g h v ℓ x ≤ hi h v ℓ)
    (hmean : ∀ h v ℓ, ∑ x, (D ℓ).p x * g h v ℓ x = 0)
    (hrange : ∀ h v ℓ, (hi h v ℓ - lo h v ℓ) ^ 2 / 4 ≤ C ℓ)
    (hmubnd : Real.sqrt (∑ ℓ, C ℓ) / Real.sqrt 2 ≤ mu)
    (hadm : ∀ h : List (L → A),
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP (prodDraw D)
        (fun h => B h.length < cumStep (servedLoss p g) h) T [] ≤ delta := by
  -- 倾斜分布是概率分布(Z ≥ 1 > 0,由 p-中心化 + exp 的 Jensen)
  have hZ : ∀ h (ω : L → A),
      0 < ∑ u, p h u * Real.exp (∑ ℓ, g h u ℓ (ω ℓ)) := by
    intro h ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p h)
      (p := fun v => ∑ ℓ, g h v ℓ (ω ℓ))
      (fun i _ => hp h i) (by simpa using hps h) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (0:ℝ) < 1 := one_pos
      _ = Real.exp (∑ v, p h v * (∑ ℓ, g h v ℓ (ω ℓ))) := by
          rw [hcenter h ω, Real.exp_zero]
      _ ≤ _ := hj
  refine request_tail_of_expected_loss (prodDraw D) (servedLoss p g) B
    hlam hdelta hdelta1 hmu0 (fun h ω => TV_nonneg _ _) ?_ ?_ hadm
  · intro h ω
    refine TV_le_one _ _ (hp h)
      (fun v => div_nonneg (mul_nonneg (hp h v) (Real.exp_pos _).le) (hZ h ω).le)
      (hps h) ?_
    rw [← Finset.sum_div]; exact div_self (ne_of_gt (hZ h ω))
  · intro h
    exact le_trans (served_tv_mean_le_cum_C (p h) D (g h) C (lo h) (hi h)
      (hp h) (hps h) (hcenter h) (hbdd h) (hmean h) (hrange h)) hmubnd

/-! ### ⑦ 顶层合成的**无结构**形态:不假设逐层 ω-local -/

/-- 该步 served 损失,`δ` **任意**(不设逐层结构)。 -/
noncomputable def servedLossG {Om : Type*} [Fintype Om]
    (p : List Om → ι → ℝ) (dlt : List Om → Om → ι → ℝ) :
    List Om → Om → ℝ :=
  fun h ω => WitCert.TV (p h)
    (fun v => p h v * Real.exp (dlt h ω v) /
              (∑ u, p h u * Real.exp (dlt h ω u)))

/-- **无结构顶层合成**:`a-priori served-TV ⟹ 请求级 anytime 尾概率`,
    **不假设**扰动逐层 ω-local。

    与 `request_tail_of_served_tv` 的唯一差别:那里把该步扰动写成
    `δ(ω)_v=∑_ℓ g_{v,ℓ}(ω_ℓ)`(每层贡献只依赖自己的抽签,即一阶线性化 —— W3GAM
    真机测量已证伪其在本模型可注入量程的成立性);这里 `δ` 完全任意,只要求它在该步
    抽签下的 **sub-Gaussian MGF 界** `E_ω[e^{δ_v}] ≤ e^{s²/2}`。

    该前提正是 Doob 路线的产物:`doob_mgf_le` 由**有界差分**(改一次抽签至多改 δ 的量
    `c_ℓ`)给出同样形状、同样常数 `s²=∑_ℓ c_ℓ²/4` 的界,且允许 δ 非线性、自适应地
    依赖整条抽签序列。把 `doob_mgf_le` 的结论(`condE` 形态)转写成本定理要的
    加权和形态,是一步机械的期望泛函等价 —— **尚未做**,故本定理把该 MGF 界列为前提
    而不是内部导出。这一层分割是刻意的:顶层链条自此**不含** ω-local 假设。 -/
theorem request_tail_of_served_tv_general
    {Om : Type*} [Fintype Om] [Nonempty Om]
    (Dstep : Draw Om) (p : List Om → ι → ℝ) (dlt : List Om → Om → ι → ℝ)
    (B : ℕ → ℝ) {lam delta mu s : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmu0 : 0 ≤ mu) (hs : 0 ≤ s)
    (hp : ∀ h v, 0 ≤ p h v) (hps : ∀ h, ∑ v, p h v = 1)
    (hcenter : ∀ h (ω : Om), ∑ v, p h v * dlt h ω v = 0)
    (hsubg : ∀ h v, ∑ ω, Dstep.p ω * Real.exp (dlt h ω v)
        ≤ Real.exp (s ^ 2 / 2))
    (hmubnd : s / Real.sqrt 2 ≤ mu)
    (hadm : ∀ h : List Om,
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP Dstep
        (fun h => B h.length < cumStep (servedLossG p dlt) h) T [] ≤ delta := by
  have hZ : ∀ h (ω : Om), 0 < ∑ u, p h u * Real.exp (dlt h ω u) := by
    intro h ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p h)
      (p := fun v => dlt h ω v)
      (fun i _ => hp h i) (by simpa using hps h) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (0:ℝ) < 1 := one_pos
      _ = Real.exp (∑ v, p h v * dlt h ω v) := by rw [hcenter h ω, Real.exp_zero]
      _ ≤ _ := hj
  refine request_tail_of_expected_loss Dstep (servedLossG p dlt) B
    hlam hdelta hdelta1 hmu0 (fun h ω => TV_nonneg _ _) ?_ ?_ hadm
  · intro h ω
    refine TV_le_one _ _ (hp h)
      (fun v => div_nonneg (mul_nonneg (hp h v) (Real.exp_pos _).le) (hZ h ω).le)
      (hps h) ?_
    rw [← Finset.sum_div]; exact div_self (ne_of_gt (hZ h ω))
  · intro h
    exact le_trans (served_tv_mean_le_omega_subgaussian (Ω := Om) (p h) (dlt h)
      Dstep.p s hs (hp h) (hps h) Dstep.nonneg Dstep.total
      (hcenter h) (hsubg h)) hmubnd

/-- **顶层合成的质量加权形态**:逐词表 MGF 界(含偏差)⟹ 请求级 anytime 尾概率。
    与 `request_tail_of_served_tv_general` 的差别:那里对所有 v 共用一个
    `exp(s²/2)`;这里每个 v 各带 `Bv v`(可写 `exp(b_v+s_v²/2)`,偏差显式),
    步界为按质量加权的 `√(log ∑_v p_v Bv v)` —— 大扰动落在低概率 token 上不再
    被最坏坐标绑架。仍**不含**任何 ω-local 假设。 -/
theorem request_tail_of_served_tv_massweighted
    {Om : Type*} [Fintype Om] [Nonempty Om]
    (Dstep : Draw Om) (p : List Om → ι → ℝ) (dlt : List Om → Om → ι → ℝ)
    (Bv : List Om → ι → ℝ) (B : ℕ → ℝ) {lam delta mu : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hmu0 : 0 ≤ mu)
    (hp : ∀ h v, 0 ≤ p h v) (hps : ∀ h, ∑ v, p h v = 1)
    (hcenter : ∀ h (ω : Om), ∑ v, p h v * dlt h ω v = 0)
    (hmgf : ∀ h v, ∑ ω, Dstep.p ω * Real.exp (dlt h ω v) ≤ Bv h v)
    (hmubnd : ∀ h, Real.sqrt (Real.log (∑ v, p h v * Bv h v)) ≤ mu)
    (hadm : ∀ h : List Om,
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP Dstep
        (fun h => B h.length < cumStep (servedLossG p dlt) h) T [] ≤ delta := by
  have hZ : ∀ h (ω : Om), 0 < ∑ u, p h u * Real.exp (dlt h ω u) := by
    intro h ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p h)
      (p := fun v => dlt h ω v)
      (fun i _ => hp h i) (by simpa using hps h) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (0:ℝ) < 1 := one_pos
      _ = Real.exp (∑ v, p h v * dlt h ω v) := by rw [hcenter h ω, Real.exp_zero]
      _ ≤ _ := hj
  refine request_tail_of_expected_loss Dstep (servedLossG p dlt) B
    hlam hdelta hdelta1 hmu0 (fun h ω => TV_nonneg _ _) ?_ ?_ hadm
  · intro h ω
    refine TV_le_one _ _ (hp h)
      (fun v => div_nonneg (mul_nonneg (hp h v) (Real.exp_pos _).le) (hZ h ω).le)
      (hps h) ?_
    rw [← Finset.sum_div]; exact div_self (ne_of_gt (hZ h ω))
  · intro h
    exact le_trans (served_tv_mean_le_massweighted (Ω := Om) (p h) (dlt h)
      Dstep.p (Bv h) (hp h) (hps h) Dstep.nonneg Dstep.total
      (hcenter h) (hmgf h)) (hmubnd h)

/-! ### ⑧ 期望泛函等价:condE(List 历史)⟷ 乘积测度加权和 -/

/-- 把抽签向量 `ω : Fin k → σ` 按 `condE` 的约定 cons 到历史 `h` 上:
    `ω 0` 先 cons(最深),`ω (k−1)` 最后 cons(在表头)。 -/
def toHist {sigma : Type*} : ∀ {k : ℕ}, (Fin k → sigma) → List sigma → List sigma
  | 0, _, h => h
  | _ + 1, ω, h => toHist (fun i => ω i.succ) (ω 0 :: h)

/-- **期望泛函等价**(接头引理):`condE` 的嵌套形态 = 乘积测度下的加权和形态。

    这一步把 McDiarmid 侧的结论(`condE`,按历史递归)转写成 served-TV 侧消费的
    形态(`∑ ω, (∏ D.p) · f`,Fintype 上的加权和)。**对任意历史 `h` 一般化是必须的**
    —— k+1 步的归纳假设要用在历史 `x :: h` 上,只对 `h = []` 陈述则归纳不闭合。 -/
theorem condE_eq_prod_sum {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (f : List sigma → ℝ) :
    ∀ (k : ℕ) (h : List sigma),
      WitCert.Calculus.McDiarmid.condE D f k h
        = ∑ ω : Fin k → sigma, (∏ i, D.p (ω i)) * f (toHist ω h) := by
  intro k
  induction k with
  | zero =>
    intro h
    simp [WitCert.Calculus.McDiarmid.condE, toHist]
  | succ k ih =>
    intro h
    show (∑ x, D.p x * WitCert.Calculus.McDiarmid.condE D f k (x :: h))
      = ∑ ω : Fin (k + 1) → sigma, (∏ i, D.p (ω i)) * f (toHist ω h)
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => sigma)).sum_comp
          (fun ω => (∏ i, D.p (ω i)) * f (toHist ω h))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [ih (x :: h), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have hz : (Fin.consEquiv (fun _ : Fin (k + 1) => sigma)) (x, ω) = Fin.cons x ω := rfl
    rw [hz, Fin.prod_univ_succ, Fin.cons_zero]
    have ht : toHist (Fin.cons x ω : Fin (k + 1) → sigma) h
        = toHist ω (x :: h) := by
      show toHist (fun i => (Fin.cons x ω : Fin (k + 1) → sigma) i.succ)
             ((Fin.cons x ω : Fin (k + 1) → sigma) 0 :: h) = _
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [ht]
    have hp : (∏ i : Fin k, D.p ((Fin.cons x ω : Fin (k + 1) → sigma) i.succ))
        = ∏ i, D.p (ω i) := by
      exact Finset.prod_congr rfl (fun i _ => by rw [Fin.cons_succ])
    rw [hp]; ring

/-- **Doob 有界差分 ⟹ 加权和形态的 MGF 界**(接头合成)。

    `doob_mgf_le_biased` 的结论在 `condE` 形态;`request_tail_of_served_tv_massweighted`
    的假设在**加权和**形态。`condE_eq_prod_sum` 把两者对上,于是:
    对任意 `F : List σ → ℝ`,只要**有界差分** `BddDiffAt F c`,即得
      `∑_{ω : Fin k → σ} (∏ D.p (ω i)) · e^{F(toHist ω [])} ≤ exp(E[F] + ∑ c²/8)`。
    **无 ω-local 假设,偏差显式** —— 这就是顶层 `hmgf` 前提的合法供给方。 -/
theorem doob_mgf_prod_sum {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (F : List sigma → ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hF : WitCert.Calculus.McDiarmid.BddDiffAt F c) :
    ∑ ω : Fin k → sigma, (∏ i, D.p (ω i)) * Real.exp (F (toHist ω []))
      ≤ Real.exp ((∑ ω : Fin k → sigma, (∏ i, D.p (ω i)) * F (toHist ω []))
                  + (∑ i ∈ Finset.range k, c i ^ 2 / 4) / 2) := by
  have h1 := condE_eq_prod_sum D (fun ω => Real.exp (F ω)) k ([] : List sigma)
  have h2 := condE_eq_prod_sum D F k ([] : List sigma)
  have hb := doob_mgf_le_biased D F c k hF
  rw [h1, h2] at hb
  exact hb

/-- **可部署形态**:请求级尾界,步预算只需 `O(|S|)` 而非 `O(|V|)`。

    与 `request_tail_of_served_tv_massweighted` 的差别:那里的步预算是全词表和
    `∑_v p_v B_v`(V=129,280,线上不可算);这里只要求
      `√(log( ∑_{v∈S_h} p_h(v)B_h(v) + (1−∑_{v∈S_h} p_h(v))·Bmax_h )) ≤ μ`,
    其中 `S_h` 是高概率集合(top-k),`Bmax_h` 是尾部包络(`v ∉ S_h` 时 `B_h v ≤ Bmax_h`)。
    由 `massweighted_topk_bound` 该式**上界**全词表和,故结论仍 sound。
    尾质量在真实 softmax 上极小 ⟹ 包络即使很松也不主导 —— 这把质量加权数学
    从"摆脱最坏坐标"推进到"运行时可算"。仍不含任何 ω-local 假设。 -/
theorem request_tail_of_served_tv_topk
    {Om : Type*} [Fintype Om] [Nonempty Om]
    (Dstep : Draw Om) (p : List Om → ι → ℝ) (dlt : List Om → Om → ι → ℝ)
    (Bv : List Om → ι → ℝ) (S : List Om → Finset ι) (Bmax : List Om → ℝ)
    (B : ℕ → ℝ) {lam delta mu : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hmu0 : 0 ≤ mu)
    (hp : ∀ h v, 0 ≤ p h v) (hps : ∀ h, ∑ v, p h v = 1)
    (hcenter : ∀ h (ω : Om), ∑ v, p h v * dlt h ω v = 0)
    (hmgf : ∀ h v, ∑ ω, Dstep.p ω * Real.exp (dlt h ω v) ≤ Bv h v)
    (htail : ∀ h v, v ∉ S h → Bv h v ≤ Bmax h)
    (hmubnd : ∀ h, Real.sqrt (Real.log
        ((∑ v ∈ S h, p h v * Bv h v)
          + (1 - ∑ v ∈ S h, p h v) * Bmax h)) ≤ mu)
    (hadm : ∀ h : List Om,
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP Dstep
        (fun h => B h.length < cumStep (servedLossG p dlt) h) T [] ≤ delta := by
  refine request_tail_of_served_tv_massweighted Dstep p dlt Bv B
    hlam hdelta hdelta1 hmu0 hp hps hcenter hmgf ?_ hadm
  intro h
  -- 全词表预算 ≤ top-k+尾包络预算 ≤ μ(单调性经 log 与 √)
  have hle : ∑ v, p h v * Bv h v
      ≤ (∑ v ∈ S h, p h v * Bv h v) + (1 - ∑ v ∈ S h, p h v) * Bmax h :=
    massweighted_topk_bound (p h) (Bv h) (S h) (Bmax h) (hp h) (hps h) (htail h)
  -- 1 ≤ ∑_v p_v B_v:Z_ω≥1(gauge+Jensen)→ Fubini → hmgf 逐 v 放大
  have hZ1 : ∀ ω : Om, (1:ℝ) ≤ ∑ u, p h u * Real.exp (dlt h ω u) := by
    intro ω
    have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p h)
      (p := fun v => dlt h ω v)
      (fun i _ => hp h i) (by simpa using hps h) (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    calc (1:ℝ) = Real.exp (∑ v, p h v * dlt h ω v) := by
          rw [hcenter h ω, Real.exp_zero]
      _ ≤ _ := hj
  have hone : (1:ℝ) ≤ ∑ v, p h v * Bv h v := by
    have hfub : ∑ ω, Dstep.p ω * (∑ u, p h u * Real.exp (dlt h ω u))
        = ∑ u, p h u * (∑ ω, Dstep.p ω * Real.exp (dlt h ω u)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun u _ =>
        Finset.sum_congr rfl (fun ω _ => by ring))
    calc (1:ℝ) = ∑ ω, Dstep.p ω * 1 := by
          simp only [mul_one]; exact Dstep.total.symm
      _ ≤ ∑ ω, Dstep.p ω * (∑ u, p h u * Real.exp (dlt h ω u)) :=
          Finset.sum_le_sum (fun ω _ =>
            mul_le_mul_of_nonneg_left (hZ1 ω) (Dstep.nonneg ω))
      _ = ∑ u, p h u * (∑ ω, Dstep.p ω * Real.exp (dlt h ω u)) := hfub
      _ ≤ ∑ u, p h u * Bv h u :=
          Finset.sum_le_sum (fun u _ =>
            mul_le_mul_of_nonneg_left (hmgf h u) (hp h u))
  have hpos : 0 < ∑ v, p h v * Bv h v := lt_of_lt_of_le one_pos hone
  exact le_trans (Real.sqrt_le_sqrt (Real.log_le_log hpos hle)) (hmubnd h)

/-! ### ⑨ 一站式根定理:有界差分 ⟹ 请求级尾界(单条可 #check) -/

/-- **根定理**:从**逐历史、逐词元的有界差分**直接到**请求级 anytime 尾界**,
    中间不留接口。

    输入只有模型侧可陈述的东西:
    * `F h v` —— 历史 `h` 下、词元 `v` 的 served-logit 扰动,作为该步**整条抽签序列**
      的函数(任意非线性、自适应);
    * `hbdd` —— 有界差分 `BddDiffAt (F h v) (c v)`:改动第 ℓ 次抽签,`F_{h,v}` 至多
      变 `c_{v,ℓ}`。**常数逐词元**(不在词表间共享)—— 与实测的 `c_{ℓ,v}` 同型;
    * `hcenter` —— gauge(softmax 对逐 ω 加常数不变);
    * `hmubnd` —— 质量加权步预算 `√(log ∑_v p_v·exp(E[F_{h,v}] + ∑_ℓ c_ℓ²/8)) ≤ μ`,
      其中 `E[F]` 是**显式偏差项**(非线性网络中逐层无偏不传递到最终 logit);
    * `hadm` —— 账本 admission invariant。

    输出:`Pr(∃t≤T: ∑_{s≤t} TV_s > B_t) ≤ δ`。

    内部把 `doob_mgf_le_biased`(Doob 条件 MGF)→ `condE_eq_prod_sum`(期望泛函
    等价)→ `served_tv_mean_le_massweighted`(质量加权 served-TV)→
    `bernoulli_mgf_le`(只需期望的支配)→ `cumloss_admission`(anytime 账本)
    串成一条。**无 ω-local 假设、无一阶线性化、偏差显式计价。**

    仍未闭合的是**模型实例化**:从线上 KV 见证 sound 地给出 `c` 与 `E[F]`(见论文
    Limitations)—— 那是测量与建模问题,不再是证明问题。 -/
theorem request_tail_of_served_tv_doob_massweighted
    {sigma : Type*} [Fintype sigma] [Nonempty sigma] (k : ℕ)
    (D : Draw sigma)
    (p : List (Fin k → sigma) → ι → ℝ)
    (F : List (Fin k → sigma) → ι → List sigma → ℝ)
    (c : ι → ℕ → ℝ) (B : ℕ → ℝ) {lam delta mu : ℝ}
    (hlam : 0 < lam) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hmu0 : 0 ≤ mu)
    (hp : ∀ h v, 0 ≤ p h v) (hps : ∀ h, ∑ v, p h v = 1)
    (hcenter : ∀ h (ω : Fin k → sigma),
        ∑ v, p h v * F h v (toHist ω []) = 0)
    (hbdd : ∀ h v, WitCert.Calculus.McDiarmid.BddDiffAt (F h v) (c v))
    (hmubnd : ∀ h, Real.sqrt (Real.log (∑ v, p h v *
        Real.exp (WitCert.Calculus.McDiarmid.condE D (F h v) k []
                  + (∑ i ∈ Finset.range k, c v i ^ 2 / 4) / 2))) ≤ mu)
    (hadm : ∀ h : List (Fin k → sigma),
        cumPred (fun _ => (0:ℝ)) h
          + (Real.log (1 / delta)
             + cumPred (fun _ => Real.log (1 + mu * (Real.exp lam - 1))) h) / lam
        ≤ B h.length) :
    ∀ T, hitProbP (prodDraw (fun _ : Fin k => D))
        (fun h => B h.length <
          cumStep (servedLossG p (fun h ω v => F h v (toHist ω []))) h) T []
      ≤ delta := by
  refine request_tail_of_served_tv_massweighted
    (prodDraw (fun _ : Fin k => D)) p (fun h ω v => F h v (toHist ω []))
    (fun h v => Real.exp (WitCert.Calculus.McDiarmid.condE D (F h v) k []
                + (∑ i ∈ Finset.range k, c v i ^ 2 / 4) / 2))
    B hlam hdelta hdelta1 hmu0 hp hps hcenter ?_ hmubnd hadm
  intro h v
  have hd := doob_mgf_prod_sum D (F h v) (c v) k (hbdd h v)
  -- 把 doob_mgf_prod_sum 右端的加权和均值换回 condE(即 condE_eq_prod_sum 本身)
  rw [← condE_eq_prod_sum D (F h v) k ([] : List sigma)] at hd
  simpa only [prodDraw] using hd

/-! ### ⑩ sound 包络:Lipschitz 复合 ⟹ 有界差分(把 c 从经验 max 换成结构量) -/

/-- 映射 `g` 在两点差的意义下 `L`-Lipschitz(用逐点距离 `dist`,不假设线性)。 -/
def LipAt {α : Type*} (g : α → ℝ) (dist : α → α → ℝ) (L : ℝ) : Prop :=
  ∀ x y, |g x - g y| ≤ L * dist x y

/-- **Lipschitz 复合的有界差分**:若 served-logit 坐标 `v` 是"层 ℓ 之后的网络"
    `G_v` 作用在层 ℓ 输出上的结果,`G_v` 是 `L_v`-Lipschitz(逐点意义,允许非线性),
    且改动第 ℓ 次抽签只把层 ℓ 输出移动 `≤ r_ℓ`(SR 量化步长的直接后果),则
      `|F_v(ω) − F_v(ω')| ≤ L_v · r_ℓ`,
    即 `c_{ℓ,v} = L_v · r_ℓ` 是**sound**的有界差分常数。

    这把根定理的 `c` 从"经验 max(sup 的下界,非 sound)"换成**结构量**:剩下的义务
    是给出 `L_v`(下游网络的 Lipschitz 常数,由权重可算/可界)与 `r_ℓ`(量化步长,
    由压缩器构造已知)。**不需要一阶线性化** —— Lipschitz 是全局的,不受 W3GAM
    实测的饱和/离散跳变影响(路由翻转仍在 Lipschitz 包络之内)。 -/
theorem bdd_diff_of_lipschitz {Om A : Type*}
    (act : Om → A) (G : A → ℝ) (dist : A → A → ℝ)
    (Lv r : ℝ) (hL : 0 ≤ Lv)
    (hlip : LipAt G dist Lv)
    (hstep : ∀ ω ω' : Om, dist (act ω) (act ω') ≤ r) :
    ∀ ω ω' : Om, |G (act ω) - G (act ω')| ≤ Lv * r := by
  intro ω ω'
  exact (hlip _ _).trans (mul_le_mul_of_nonneg_left (hstep ω ω') hL)

/-- **逐层 Lipschitz 相乘**:下游若干层各自 `L_i`-Lipschitz(同一距离),复合后
    `∏ L_i`-Lipschitz。给出 `L_v = ∏_{i>ℓ} L_i` 的合法来源。 -/
theorem lip_comp {α : Type*} (g₁ g₂ : α → α) (φ : α → ℝ)
    (dist : α → α → ℝ) (L₁ L₂ Lφ : ℝ)
    (hL2 : 0 ≤ L₂) (hLφ : 0 ≤ Lφ)
    (h1 : ∀ x y, dist (g₁ x) (g₁ y) ≤ L₁ * dist x y)
    (h2 : ∀ x y, dist (g₂ x) (g₂ y) ≤ L₂ * dist x y)
    (hφ : LipAt φ dist Lφ) :
    LipAt (fun x => φ (g₂ (g₁ x))) dist (Lφ * (L₂ * L₁)) := by
  intro x y
  calc |φ (g₂ (g₁ x)) - φ (g₂ (g₁ y))|
      ≤ Lφ * dist (g₂ (g₁ x)) (g₂ (g₁ y)) := hφ _ _
    _ ≤ Lφ * (L₂ * dist (g₁ x) (g₁ y)) :=
        mul_le_mul_of_nonneg_left (h2 _ _) hLφ
    _ ≤ Lφ * (L₂ * (L₁ * dist x y)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (h1 x y) hL2) hLφ
    _ = Lφ * (L₂ * L₁) * dist x y := by ring

/-- **残差层的 Lipschitz 常数**:`x ↦ x + f(x)`,若 `f` 是 `L`-Lipschitz,则该层是
    `(1+L)`-Lipschitz。`hsub` 是范数诱导距离的次可加性(`dist(x+u, y+v) ≤
    dist(x,y)+dist(u,v)`),Transformer 的残差流恰是此形。 -/
theorem lip_residual {α : Type*} (f : α → α) (dist : α → α → ℝ) (add : α → α → α)
    (L : ℝ)
    (hsub : ∀ x y u v, dist (add x u) (add y v) ≤ dist x y + dist u v)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    ∀ x y, dist (add x (f x)) (add y (f y)) ≤ (1 + L) * dist x y := by
  intro x y
  calc dist (add x (f x)) (add y (f y))
      ≤ dist x y + dist (f x) (f y) := hsub x y (f x) (f y)
    _ ≤ dist x y + L * dist x y := by linarith [hf x y]
    _ = (1 + L) * dist x y := by ring

/-- `n` 层复合(第 `i` 层是 `g i`)。 -/
def iterComp {α : Type*} (g : ℕ → α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => g n (iterComp g n x)

/-- **逐层 Lipschitz 的乘积律**:每层 `L i`-Lipschitz ⟹ `n` 层复合是
    `(∏_{i<n} L i)`-Lipschitz。配 `lip_residual` 即得 Transformer 栈的
    `∏_ℓ (1+L_ℓ)`,再配 `bdd_diff_of_lipschitz` 得 **sound** 的 `c_ℓ`
    (= 上游包络 × 量化步长)。**全程无线性化** —— 这是包络路线优于 Jacobian 的根据:
    路由翻转、激活、归一化都在 Lipschitz 常数之内。 -/
theorem lip_iterComp {α : Type*} (g : ℕ → α → α) (dist : α → α → ℝ) (L : ℕ → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hg : ∀ i x y, dist (g i x) (g i y) ≤ L i * dist x y) :
    ∀ (n : ℕ) (x y : α),
      dist (iterComp g n x) (iterComp g n y)
        ≤ (∏ i ∈ Finset.range n, L i) * dist x y := by
  intro n
  induction n with
  | zero => intro x y; simp [iterComp]
  | succ n ih =>
    intro x y
    calc dist (iterComp g (n + 1) x) (iterComp g (n + 1) y)
        = dist (g n (iterComp g n x)) (g n (iterComp g n y)) := rfl
      _ ≤ L n * dist (iterComp g n x) (iterComp g n y) := hg n _ _
      _ ≤ L n * ((∏ i ∈ Finset.range n, L i) * dist x y) :=
          mul_le_mul_of_nonneg_left (ih x y) (hL n)
      _ = (∏ i ∈ Finset.range (n + 1), L i) * dist x y := by
          rw [Finset.prod_range_succ]; ring

/-! ### ⑪ 局部 Lipschitz:把全局常数换成「局部常数 + 运行时可查的轨迹包含」 -/

/-- 在集合 `S` 上的 Lipschitz(**局部**,不要求全空间)。 -/
def LipOn {α : Type*} (g : α → ℝ) (dist : α → α → ℝ) (S : Set α) (L : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ L * dist x y

/-- **局部 Lipschitz ⟹ sound 有界差分**,代价是多一个前提:两条抽签轨迹都落在 `S` 内。

    这正是全局包络(实测 `10^221`,空洞)与局部行为(实测沿真实轨迹**收缩**)之间
    落差的形式化出口:把"对 `ℝ^d` 上一切点成立的常数"换成"在请求激活实际占据的
    区域上成立的常数 + 一个**包含谓词**"。关键在于包含谓词
    `hstay` **是运行时可查的** —— 激活本来就被观测,校准椭球判定是 `O(d)`。
    于是证书变成:"若在线观测到激活留在校准区域内(可查),则 `c_{ℓ,v}=L·r` sound"。 -/
theorem bdd_diff_of_lipschitz_on {Om α : Type*}
    (act : Om → α) (G : α → ℝ) (dist : α → α → ℝ) (S : Set α)
    (L r : ℝ) (hL : 0 ≤ L)
    (hlip : LipOn G dist S L)
    (hstay : ∀ ω, act ω ∈ S)
    (hstep : ∀ ω ω' : Om, dist (act ω) (act ω') ≤ r) :
    ∀ ω ω' : Om, |G (act ω) - G (act ω')| ≤ L * r := by
  intro ω ω'
  exact (hlip _ (hstay ω) _ (hstay ω')).trans
    (mul_le_mul_of_nonneg_left (hstep ω ω') hL)

/-- 前向不变性:从 `S 0` 出发,第 `n` 层后仍在 `S n` 内。 -/
theorem iterComp_mem {α : Type*} (g : ℕ → α → α) (S : ℕ → Set α)
    (hmap : ∀ i x, x ∈ S i → g i x ∈ S (i + 1)) :
    ∀ (n : ℕ) (x : α), x ∈ S 0 → iterComp g n x ∈ S n := by
  intro n
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih => intro x hx; exact hmap n _ (ih x hx)

/-- **逐层局部 Lipschitz 的复合律**:每层只需在自己的区域 `S i` 上 `L i`-Lipschitz,
    外加**前向不变性** `g i : S i → S (i+1)`(校准时可验、运行时可查),
    即得整栈 `∏_{i<n} L i`。与全局版 `lip_iterComp` 同形,但常数取自局部 —— 实测
    沿真实轨迹的局部比值远小于权重谱范数给出的全局值,这是唯一可能同时
    **sound 且非空洞**的路线。 -/
theorem lip_iterComp_on {α : Type*} (g : ℕ → α → α) (dist : α → α → ℝ)
    (S : ℕ → Set α) (L : ℕ → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hmap : ∀ i x, x ∈ S i → g i x ∈ S (i + 1))
    (hg : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, dist (g i x) (g i y) ≤ L i * dist x y) :
    ∀ (n : ℕ) (x y : α), x ∈ S 0 → y ∈ S 0 →
      dist (iterComp g n x) (iterComp g n y)
        ≤ (∏ i ∈ Finset.range n, L i) * dist x y := by
  intro n
  induction n with
  | zero => intro x y _ _; simp [iterComp]
  | succ n ih =>
    intro x y hx hy
    calc dist (iterComp g (n + 1) x) (iterComp g (n + 1) y)
        = dist (g n (iterComp g n x)) (g n (iterComp g n y)) := rfl
      _ ≤ L n * dist (iterComp g n x) (iterComp g n y) :=
          hg n _ (iterComp_mem g S hmap n x hx) _ (iterComp_mem g S hmap n y hy)
      _ ≤ L n * ((∏ i ∈ Finset.range n, L i) * dist x y) :=
          mul_le_mul_of_nonneg_left (ih x y hx hy) (hL n)
      _ = (∏ i ∈ Finset.range (n + 1), L i) * dist x y := by
          rw [Finset.prod_range_succ]; ring

/-! ### ⑫ betting 置信序列接入既有 Ville 链(UCB 的 anytime 覆盖) -/

/-- **betting 因子是合法的 e-process 因子**。检验 `H_0 : m ≤ E[X]`,取
    `g h x = 1 + λ_h·(m − x)`,`λ_h ≥ 0` 且逐点非负(实现里由 `λ < c/(1−m)` 保证)。
    则 (i) `g ≥ 0`;(ii) `H_0` 下 `∑_x p_x g_h x ≤ 1`。

    配 `Ville.eprocess_ville` 即得 `∀T, hitProb D (prodProcess g) (1/δ) T [] ≤ δ`
    —— **任意时刻**资本越 `1/δ` 的概率 ≤ δ。UCB 由"反演该检验族"定义
    (`UCB = inf{m : 资本越线}`),其覆盖正是这条:若真值 μ 满足 `m ≤ μ`(即 H_0 真),
    越线概率 ≤ δ,故 `μ > UCB` 的概率 ≤ δ。这把 `wsr_ucb` 的 anytime 有效性
    落到本文既有的 Ville 形式化链上,不再只由数值冒烟担保。 -/
theorem betting_factor_eprocess {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (X : sigma → ℝ) (m : ℝ) (lam : List sigma → ℝ)
    (hlam : ∀ h, 0 ≤ lam h)
    (hpos : ∀ h x, 0 ≤ 1 + lam h * (m - X x))
    (hnull : m ≤ ∑ x, D.p x * X x) :
    (∀ h x, 0 ≤ 1 + lam h * (m - X x)) ∧
    (∀ h, ∑ x, D.p x * (1 + lam h * (m - X x)) ≤ 1) := by
  refine ⟨hpos, fun h => ?_⟩
  have hexp : ∑ x, D.p x * (1 + lam h * (m - X x))
      = 1 + lam h * (m - ∑ x, D.p x * X x) := by
    have hsplit : ∀ x, D.p x * (1 + lam h * (m - X x))
        = D.p x + lam h * m * D.p x - lam h * (D.p x * X x) :=
      fun x => by ring
    calc ∑ x, D.p x * (1 + lam h * (m - X x))
        = ∑ x, (D.p x + lam h * m * D.p x - lam h * (D.p x * X x)) :=
          Finset.sum_congr rfl (fun x _ => hsplit x)
      _ = (∑ x, D.p x) + lam h * m * (∑ x, D.p x)
            - lam h * (∑ x, D.p x * X x) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 + lam h * (m - ∑ x, D.p x * X x) := by rw [D.total]; ring
  rw [hexp]
  have : lam h * (m - ∑ x, D.p x * X x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hlam h) (by linarith)
  linarith

/-- **UCB 的 anytime 覆盖**(合成):在 `H_0 : m ≤ E[X]` 下,betting 资本过程
    任意时刻越 `1/δ` 的概率 ≤ δ。反演该检验族给出的上置信界因此是
    anytime-valid —— 与账本共用同一条 Ville 不等式。 -/
theorem betting_ucb_anytime {sigma : Type*} [Fintype sigma] [Nonempty sigma]
    (D : Draw sigma) (X : sigma → ℝ) (m : ℝ) (lam : List sigma → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hlam : ∀ h, 0 ≤ lam h)
    (hpos : ∀ h x, 0 ≤ 1 + lam h * (m - X x))
    (hnull : m ≤ ∑ x, D.p x * X x) :
    ∀ T, WitCert.Calculus.Ville.hitProb D
        (WitCert.Calculus.Ville.prodProcess (fun h x => 1 + lam h * (m - X x)))
        (1 / delta) T [] ≤ delta := by
  obtain ⟨hg, hm⟩ := betting_factor_eprocess D X m lam hlam hpos hnull
  exact WitCert.Calculus.Ville.eprocess_ville D _ hdelta hdelta1 hg hm

end WitCert.Calculus.Apriori