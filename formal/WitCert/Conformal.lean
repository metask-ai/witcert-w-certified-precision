/-
  WitCert 形式化 · L14:**共形(顺序统计量)历史外推界**。

  ①c 的最后一道量词缺口是"界在**每个**历史上成立"。此前用的工具是:把留出历史
  逐个判"通过/未通过",再对这串**二值指示器**做 Clopper–Pearson。6 个留出历史、
  2 个未通过 ⟹ 0.8269 —— 一个没有任何用处的数。

  **诊断与本篇其它四次失败同族**:用了一件按"最坏情形值域"定价的仪器去界一个
  并非被值域限制住的量。二值计数扔掉了分数之间的**顺序结构**,而顺序恰恰是
  可交换性唯一需要的东西。换成顺序统计量:

      P(新历史的分数 > 校准分数的最大值) ≤ 1/(N+1)

  同样 12 个历史,从 0.8269 变成 1/13 = 0.0769。且**校准分数不需要覆盖各自的
  真值** —— 它们只是"符合性分数",于是逐历史 Bonferroni 也一并消失:未覆盖
  预算只对**新**历史付一次。

  本文件的数学内容是两条,都不许是伪装的算术:
    * `strictMax_pairwiseDisjoint` —— 严格最大值至多在一个位置取到(**推导**出来的
      两两不交,不是假设);
    * `sum_prob_strictMax_le_one` —— 不交事件的概率和 ≤ 1。
  可交换性以假设 `hex`(各位置成为严格最大的概率相等)显式进入,不藏在证明里;
  它正是"历史是目标总体的可交换抽样"这一实验侧前提的形式化对应物 —— 而我们的
  12 个历史按**递增长度**人为选取,**不**满足它。故本文件给出的是仪器的效率上限,
  实验侧仍须诚实标注前提未被满足(见 w3mh 裁决的 caliber)。
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical

namespace WitCert.Calculus.Conformal

variable {Ω : Type*} [Fintype Ω]

/-- 有限概率空间:权重非负、总和为 1。 -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  total : ∑ ω, p ω = 1

/-- 事件概率。 -/
noncomputable def prob (μ : FinProb Ω) (A : Finset Ω) : ℝ := ∑ ω ∈ A, μ.p ω

lemma prob_nonneg (μ : FinProb Ω) (A : Finset Ω) : 0 ≤ prob μ A :=
  Finset.sum_nonneg fun ω _ => μ.nonneg ω

lemma prob_mono (μ : FinProb Ω) {A B : Finset Ω} (h : A ⊆ B) : prob μ A ≤ prob μ B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => μ.nonneg ω

lemma prob_le_one (μ : FinProb Ω) (A : Finset Ω) : prob μ A ≤ 1 := by
  have := prob_mono μ (Finset.subset_univ A)
  simpa [prob, μ.total] using this

/-- 次可加性(union bound):由 `∑_{A∪B} + ∑_{A∩B} = ∑_A + ∑_B` 与交的非负性得。 -/
lemma prob_union_le (μ : FinProb Ω) (A B : Finset Ω) :
    prob μ (A ∪ B) ≤ prob μ A + prob μ B := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := μ.p)
  have hi : 0 ≤ prob μ (A ∩ B) := prob_nonneg μ _
  simp only [prob] at *
  linarith

/-! ### 严格最大值事件 -/

/-- `strictMax S i` = 第 `i` 个分数**严格**大于其余全部分数的那些样本点。 -/
noncomputable def strictMax {n : ℕ} (S : Fin n → Ω → ℝ) (i : Fin n) : Finset Ω :=
  Finset.univ.filter fun ω => ∀ j, j ≠ i → S j ω < S i ω

lemma mem_strictMax {n : ℕ} (S : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) :
    ω ∈ strictMax S i ↔ ∀ j, j ≠ i → S j ω < S i ω := by
  simp [strictMax]

/-- **数学内容其一**:严格最大值至多在一个位置取到,故这 `n` 个事件两两不交。
    (若 `ω` 同时属于 `i` 与 `j`(`i ≠ j`),则 `S j ω < S i ω` 与 `S i ω < S j ω`。) -/
lemma strictMax_pairwiseDisjoint {n : ℕ} (S : Fin n → Ω → ℝ) :
    (Finset.univ : Finset (Fin n)).toSet.PairwiseDisjoint (strictMax S) := by
  intro i _ j _ hij
  simp only [Function.onFun, Finset.disjoint_left]
  intro ω hi hj
  rw [mem_strictMax] at hi hj
  exact absurd (hi j (Ne.symm hij)) (not_lt.mpr (le_of_lt (hj i hij)))

/-- **数学内容其二**:不交事件的概率和不超过 1。 -/
lemma sum_prob_strictMax_le_one {n : ℕ} (μ : FinProb Ω) (S : Fin n → Ω → ℝ) :
    ∑ i, prob μ (strictMax S i) ≤ 1 := by
  have hb : ∑ ω ∈ Finset.univ.biUnion (strictMax S), μ.p ω
      = ∑ i ∈ (Finset.univ : Finset (Fin n)), ∑ ω ∈ strictMax S i, μ.p ω :=
    Finset.sum_biUnion (strictMax_pairwiseDisjoint S)
  calc ∑ i, prob μ (strictMax S i)
      = prob μ (Finset.univ.biUnion (strictMax S)) := by
        simp only [prob]; exact hb.symm
    _ ≤ 1 := prob_le_one μ _

/-- **共形界**:在可交换性(`hex`:每个位置成为严格最大的概率相同)下,任一位置
    成为严格最大的概率 ≤ `1/n`。取 `i = 最后一个`(新历史)即得
    `P(新分数 > 校准分数最大值) ≤ 1/(N+1)`。 -/
theorem conformal_exceedance_le {n : ℕ} (hn : 0 < n) (μ : FinProb Ω) (S : Fin n → Ω → ℝ)
    (hex : ∀ i j, prob μ (strictMax S i) = prob μ (strictMax S j)) (i : Fin n) :
    prob μ (strictMax S i) ≤ 1 / n := by
  have hs := sum_prob_strictMax_le_one μ S
  have heq : ∑ j, prob μ (strictMax S j) = (n : ℝ) * prob μ (strictMax S i) := by
    rw [Finset.sum_congr rfl fun j _ => hex j i]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [heq] at hs
  rw [le_div_iff₀ hnpos]
  linarith [hs]

/-! ### 从"分数不超阈值"到"真值不超阈值":未覆盖预算只付一次 -/

/-- 若 `ω` 不在最后一个位置的严格最大事件里,则最后一个分数被某个校准分数支配,
    从而被任何支配全部校准分数的阈值 `thr` 支配。 -/
lemma le_thr_of_not_strictMax {N : ℕ} (S : Fin (N + 1) → Ω → ℝ) (thr : Ω → ℝ)
    (hthr : ∀ ω, ∀ j : Fin (N + 1), j ≠ Fin.last N → S j ω ≤ thr ω)
    (ω : Ω) (h : ω ∉ strictMax S (Fin.last N)) :
    S (Fin.last N) ω ≤ thr ω := by
  rw [mem_strictMax] at h
  push_neg at h
  obtain ⟨j, hj, hle⟩ := h
  exact le_trans hle (hthr ω j hj)

/-- **完整的历史外推风险账**。设 `trueMean` 是新历史的真实条件均值,`S last` 是
    为它算的置信上界,`cover` 是"该上界确实覆盖"的事件。则

        P(真值 > 阈值) ≤ 1/(N+1) + α,

    其中 `1/(N+1)` 来自可交换性(顺序统计量),`α` 是**新历史那一个**上界的未覆盖
    预算。**校准侧的上界不必覆盖**,它们只作符合性分数 —— 于是逐历史 Bonferroni
    在这条路线上不存在。 -/
theorem conformal_risk_union {N : ℕ} (μ : FinProb Ω) (S : Fin (N + 1) → Ω → ℝ)
    (trueMean thr : Ω → ℝ) (α : ℝ) (cover : Finset Ω)
    (hcov : ∀ ω ∈ cover, trueMean ω ≤ S (Fin.last N) ω)
    (hthr : ∀ ω, ∀ j : Fin (N + 1), j ≠ Fin.last N → S j ω ≤ thr ω)
    (halpha : prob μ coverᶜ ≤ α)
    (hex : ∀ i j, prob μ (strictMax S i) = prob μ (strictMax S j)) :
    prob μ (Finset.univ.filter fun ω => thr ω < trueMean ω)
      ≤ 1 / (N + 1) + α := by
  have hsub : (Finset.univ.filter fun ω => thr ω < trueMean ω)
      ⊆ strictMax S (Fin.last N) ∪ coverᶜ := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_contra hc
    simp only [Finset.mem_union, not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    have hcv : ω ∈ cover := by simpa using h2
    exact absurd (le_trans (hcov ω hcv)
      (le_thr_of_not_strictMax S thr hthr ω h1)) (not_le.mpr hω)
  have hmono := prob_mono μ hsub
  have hu := prob_union_le μ (strictMax S (Fin.last N)) coverᶜ
  have hcf : prob μ (strictMax S (Fin.last N)) ≤ 1 / (N + 1) := by
    have := conformal_exceedance_le (n := N + 1) (Nat.succ_pos N) μ S hex (Fin.last N)
    simpa using this
  linarith


/-! ### 组合:把"逐历史的界"与"历史外推的界"合成**随机历史上的总风险**

  论文的端到端主张不是两条界之一,而是它们的**合成**:请求落在一个随机抽到的
  历史上,per-history 的账本风险 δ 只在"该历史被 μ_conf 覆盖"时可用,而覆盖失败
  的概率由共形界付。此前这一步只写在散文里(风险公式 δ_ledger+α_draw+…),
  而散文里的风险公式已经被评审抓到过一次是**旧的**。故在此机器检查。

  数学内容是**按历史分纤维求和**(全概率),不是重排的算术。 -/

/-- **随机历史上的总风险**。`hlab` 把样本点标记到它所属的历史;`exceed` 是
    "该历史的真值超出 μ_conf"的事件(由 `conformal_risk_union` 付 `p`);
    `hδ` 是逐历史的条件账本风险(在未超出的历史上,坏事件占该历史质量的 ≤ δ)。
    则总风险 ≤ δ + p —— 论文风险公式的机器检查版本。 -/
theorem total_risk_over_random_history {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FinProb Ω) (hlab : Ω → ι) (bad exceed : Finset Ω) (δ p : ℝ)
    (hδ : ∀ i : ι, prob μ ((bad \ exceed).filter fun ω => hlab ω = i)
            ≤ δ * prob μ (Finset.univ.filter fun ω => hlab ω = i))
    (hp : prob μ exceed ≤ p) :
    prob μ bad ≤ δ + p := by
  -- ① 按历史分纤维:坏且未超出的质量 = 各历史上该质量之和
  have hfib : ∀ (A : Finset Ω),
      ∑ i : ι, prob μ (A.filter fun ω => hlab ω = i) = prob μ A := by
    intro A
    simp only [prob]
    exact Finset.sum_fiberwise A hlab μ.p
  -- ② 逐历史用条件界,再用"各历史质量之和 = 1"
  have hsum : prob μ (bad \ exceed) ≤ δ := by
    have h1 : prob μ (bad \ exceed)
        = ∑ i : ι, prob μ ((bad \ exceed).filter fun ω => hlab ω = i) := (hfib _).symm
    have h2 : ∑ i : ι, prob μ ((bad \ exceed).filter fun ω => hlab ω = i)
        ≤ ∑ i : ι, δ * prob μ (Finset.univ.filter fun ω => hlab ω = i) :=
      Finset.sum_le_sum fun i _ => hδ i
    have h3 : ∑ i : ι, δ * prob μ (Finset.univ.filter fun ω => hlab ω = i)
        = δ * prob μ (Finset.univ : Finset Ω) := by
      rw [← Finset.mul_sum, hfib]
    have h4 : prob μ (Finset.univ : Finset Ω) = 1 := by simp [prob, μ.total]
    rw [h1]; rw [h3, h4] at h2; linarith
  -- ③ bad ⊆ (bad \ exceed) ∪ exceed
  have hsub : bad ⊆ (bad \ exceed) ∪ exceed := by
    intro ω hω
    by_cases hx : ω ∈ exceed
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hω, hx⟩)
  have := prob_mono μ hsub
  have hu := prob_union_le μ (bad \ exceed) exceed
  linarith

/-- 反例:**条件界不能省掉"未超出"这一限制**。若把 `hδ` 换成"在**全部**历史上
    坏事件占比 ≤ δ",结论当然成立但那是更强的前提;反过来,只知道"平均意义上"
    坏事件占比 ≤ δ 不足以推出逐历史成立 —— 一个历史可以独占全部坏质量。 -/
theorem average_does_not_give_per_history :
    ∃ (q : Fin 2 → ℝ) (δ : ℝ), (∀ i, 0 ≤ q i) ∧ (q 0 + q 1) / 2 ≤ δ ∧ δ < q 0 := by
  refine ⟨![0.4, 0.0], 0.2, ?_, ?_, ?_⟩ <;> norm_num [Fin.forall_fin_two]

/-! ### 反例:为什么必须是**严格**最大,以及可交换性不可省 -/

/-- 并列会破坏不交性:两个位置可以同时是(非严格)最大。故定义里的 `<` 不可换成 `≤`。 -/
theorem ties_break_disjointness :
    ∃ (f : Fin 2 → ℝ), (∀ j, j ≠ (0 : Fin 2) → f j ≤ f 0) ∧
      (∀ j, j ≠ (1 : Fin 2) → f j ≤ f 1) := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j _ <;> simp

/-- 可交换性不可省:不交事件的概率和 ≤ 1 只给出"**某个**位置 ≤ 1/n",
    而一个位置可以独占几乎全部概率。 -/
theorem exchangeability_needed :
    ∃ q : Fin 2 → ℝ, (∀ i, 0 ≤ q i) ∧ q 0 + q 1 ≤ 1 ∧ 1 / 2 < q 0 := by
  refine ⟨![0.9, 0.05], ?_, ?_, ?_⟩ <;> norm_num [Fin.forall_fin_two]

end WitCert.Calculus.Conformal
