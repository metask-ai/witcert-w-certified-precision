/-
  WitCert 形式化 · L7:**请求级风险账本**

  第一档请求级保证(与账本实现 contracts.RequestLedger 一致):

      P(请求内任一入账事件越界) ≤ Σ_i δ_i ≤ δ_req

  三个要件,各一条定理:
    1. `telescope_sum`:预算权重 w_i = 1/((i+1)(i+2))(0 起)的前 n 项和 = 1 − 1/(n+1)。
       **未知长度也 sound 的根据**:无论请求生成多长,Σ w_i < 1 恒成立。
       与 6/(π²i²) 同为 1/i² 衰减,但和恰为 1 且只需一条望远镜引理,不需要 Basel。
    2. `ledger_sound`:条件式(首次失败形)union bound + 任意满足 Σ ≤ δ_req 的
       预算序列 ⟹ 对**每个** n,前 n 个事件的并集概率 ≤ δ_req。
    3. `coverage_confidence`:(1−p)^n ≤ e^{−np} —— 覆盖率报告的置信根据:
       n 次采样全部通过证书检查时,"单事件失败率 ≥ ln(1/δ)/n"以概率 ≤ δ 被排除。
       这是"0 次违约"必须附带的统计口径(不能写成"违约率 0%")。

  账本的**语义边界**(定理不背书的部分,由实现与论文措辞负责):
  账本只保证"入账的局部操作不越界";经验对象绝不入账(回退或降级);
  它不保证最终输出相同 —— 那需要层间传播或重置点,是显式的下一阶段。
-/
import WitCert.RequestBudget
import WitCert.Contract

open BigOperators MeasureTheory

namespace WitCert.Calculus.Ledger

/-! ### 1. 望远镜预算权重 -/

/-- 预算权重(0 起):w i = 1/((i+1)(i+2))。 -/
noncomputable def w (i : ℕ) : ℝ := 1 / ((i + 1) * (i + 2))

lemma w_nonneg (i : ℕ) : 0 ≤ w i := by unfold w; positivity

/-- **望远镜和**:∑_{i<n} w i = 1 − 1/(n+1)。 -/
theorem telescope_sum (n : ℕ) :
    ∑ i ∈ Finset.range n, w i = 1 - 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold w
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- 权重和恒 < 1 —— 请求生成多长都不超预算。 -/
theorem telescope_sum_le_one (n : ℕ) : ∑ i ∈ Finset.range n, w i ≤ 1 := by
  rw [telescope_sum]
  have : (0:ℝ) < 1 / (n + 1) := by positivity
  linarith

/-! ### 2. 账本 soundness(未知长度) -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/--
  **账本定理**:事件按首次失败形入账,第 i 个事件的预算为 δseq i,
  预算序列的每个前缀和 ≤ δ_req ⟹ **对每个 n**,前 n 个事件的并集概率 ≤ δ_req。

  "对每个 n"就是未知长度 soundness:请求随时可以停,也随时可以继续。
-/
theorem ledger_sound (E : ℕ → Set Ω) (δseq : ℕ → ENNReal) (δreq : ENNReal)
    (h : ∀ i, μ (E i \ ⋃ j ∈ Finset.range i, E j) ≤ δseq i)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, δseq i ≤ δreq) (n : ℕ) :
    μ (⋃ i ∈ Finset.range n, E i) ≤ δreq :=
  le_trans (WitCert.Calculus.Budget.conditional_union_le μ E δseq h n) (hsum n)

/-- 望远镜权重的实例化:δseq i = ofReal (δ · w i),前缀和 ≤ ofReal δ。 -/
theorem telescope_budget_le (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ENNReal.ofReal (δ * w i) ≤ ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hδ (w_nonneg i))]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  calc δ * ∑ i ∈ Finset.range n, w i ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left (telescope_sum_le_one n) hδ
    _ = δ := mul_one δ

/-! ### 3. 覆盖率置信(“0 次违约”的统计口径) -/

/--
  **覆盖率置信引理**:单事件失败率为 p 时,n 次独立采样全部通过的概率 (1−p)^n ≤ e^{−np}。
  倒读:观察到 n 次全过,则「p ≥ ln(1/δ)/n」这一假设成立的概率 ≤ δ ——
  报告覆盖率必须带这条,**“0 次违约”不等于“违约率 0%”**。
-/
theorem coverage_confidence {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(n * p)) := by
  have h1 : 1 - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  have h0 : 0 ≤ 1 - p := by linarith
  calc (1 - p) ^ n ≤ Real.exp (-p) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-(n * p)) := by
        rw [← Real.exp_nat_mul]; ring_nf

/-! ### 4. 未知长度的代价定理(√2 一致界) -/

/--
  **未知长度的代价 ≤ √2**(对 δ ≤ ½,一致于所有事件序号):

  已知长度 N 时的均分预算给第 i 个事件 δ/N;未知长度的望远镜预算给 δ/(i(i+1))。
  sub-Gaussian 半径按 √log(1/δᵢ) 走,故代价是对数比的平方根。本定理给出

      log(i(i+1)/δ) ≤ 2·log(N/δ)      (1 ≤ i ≤ N, δ ≤ ½)

  即**半径至多贵 √2 —— 与 N 无关的一致常数**。评审口算的"约 33%"由此变成定理:
  未知长度不是渐近惩罚,是一个 √2。
-/
theorem unknown_length_price {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/2)
    {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    Real.log (i * (i + 1) / δ) ≤ 2 * Real.log (N / δ) := by
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hiN' : (i:ℝ) ≤ N := by exact_mod_cast hiN
  have hN1 : (1:ℝ) ≤ N := le_trans hi1 hiN'
  have h2 : (i:ℝ) * (i + 1) ≤ 2 * N ^ 2 := by nlinarith
  have h3 : (i:ℝ) * (i + 1) * δ ≤ N ^ 2 := by nlinarith
  have key : (i:ℝ) * (i + 1) / δ ≤ (N / δ) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hδ0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h3 hδ0.le]
  have hpos : (0:ℝ) < i * (i + 1) / δ := by positivity
  calc Real.log ((i:ℝ) * (i + 1) / δ)
      ≤ Real.log ((N / δ) ^ 2) := Real.log_le_log hpos key
    _ = 2 * Real.log (N / δ) := by
        rw [Real.log_pow]; push_cast; ring

/-! ### 5. 两层预算结构(条目级 δ=0 + 概率级望远镜) -/

/-- 前 n 个事件里概率性事件的个数(账本的概率计数器)。 -/
def probCount (f : ℕ → Option ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => (f j).isSome)).card

/--
  **两层预算**:确定性证书(margin 类,条件失败不可能)以 δ=0 入账,
  概率性证书按**自己的计数器**取望远镜权重(`f i = some k` 且 k 恰为此前概率
  事件数 —— 与 RequestLedger.certify_probabilistic 的实现语义逐字一致)。
  任意长度前缀的预算和 ≤ δ_req。

  这正是评审建议的降本结构:千万级条目事件不消费风险预算,
  预算只在 query/head/block 级的概率证书上按 1/k(k+1) 衰减。
-/
theorem two_layer_budget_le (δ : ℝ) (hδ : 0 ≤ δ) (f : ℕ → Option ℕ)
    (hctr : ∀ i k, f i = some k → k = probCount f i) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      (match f i with
       | none => 0
       | some k => ENNReal.ofReal (δ * w k)) ≤ ENNReal.ofReal δ := by
  classical
  -- 等式:前缀和 = 前 probCount n 个望远镜项之和(计数器语义逐事件对齐)
  have heq : ∀ m, ∑ i ∈ Finset.range m,
      (match f i with
       | none => 0
       | some k => ENNReal.ofReal (δ * w k))
      = ∑ k ∈ Finset.range (probCount f m), ENNReal.ofReal (δ * w k) := by
    intro m
    induction m with
    | zero => simp [probCount]
    | succ m ih =>
      have hrange : Finset.range (m + 1) = insert m (Finset.range m) := by
        rw [Finset.range_succ]
      cases h : f m with
      | none =>
        have hc : probCount f (m + 1) = probCount f m := by
          unfold probCount
          rw [hrange, Finset.filter_insert]
          simp [h]
        rw [Finset.sum_range_succ, ih, h, hc]
        simp
      | some k =>
        have hk : k = probCount f m := hctr m k h
        have hc : probCount f (m + 1) = probCount f m + 1 := by
          unfold probCount
          rw [hrange, Finset.filter_insert]
          simp only [h, Option.isSome_some, if_true]
          rw [Finset.card_insert_of_not_mem (by simp)]
        rw [Finset.sum_range_succ, ih, h, hc, Finset.sum_range_succ, hk]
  rw [heq n]
  exact telescope_budget_le δ hδ (probCount f n)

/-! ### 6. Refinement 接口:定理假设的显式化 -/

/--
  **已认证事件流**:把 `ledger_sound` 的全部数学前提捆成一个具名接口。

  Lean 只能保证"若 δseq 真是首次失败形的条件界,则总账不超";**runtime 交来的
  δ 是否真有这个含义,是 refinement 义务**,由以下三条(无法内化为类型的)
  运行时义务承担,Python 账本逐事件以 assumption 字段留痕:
    (R1) 事件与真实读取一一对应 —— 所有使用压缩结果的读取都被检查;
    (R2) 回退不改变事件语义 —— 回退后的读取是精确的,不产生新的失败模式;
    (R3) 概率证书的随机源相对历史条件独立(如 dither 之于已生成的 token)。
-/
structure CertifiedEventStream (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  E : ℕ → Set Ω
  δseq : ℕ → ENNReal
  /-- 首次失败形的条件界 —— ledger_sound 的数学前提 -/
  cond_bound : ∀ i, μ (E i \ ⋃ j ∈ Finset.range i, E j) ≤ δseq i
  /-- 预算前缀和不超 δ_req -/
  budget : ENNReal
  budget_ok : ∀ n, ∑ i ∈ Finset.range n, δseq i ≤ budget

/-- 接口版账本定理:任何满足接口的事件流,任意长度下总失败概率 ≤ 预算。 -/
theorem stream_sound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : CertifiedEventStream Ω μ) (n : ℕ) :
    μ (⋃ i ∈ Finset.range n, s.E i) ≤ s.budget :=
  ledger_sound μ s.E s.δseq s.budget s.cond_bound s.budget_ok n

end WitCert.Calculus.Ledger