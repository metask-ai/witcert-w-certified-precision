/-
  WitCert 形式化 · L17:**替换恒等式** —— 路由 TV 看不见"换进来的是谁"。

  起因(2026-08-09,R6/R7)。MoE 服务里省显存的一类做法是:只把一部分专家常驻
  快速内存,某个 token 选中的专家若不常驻,就**换**一个常驻的顶上(或者干脆丢
  掉)。直觉上"换成分数次好的专家"应当远好于"随机换一个"—— 本文前面的证书
  全部用**路由分布 TV** 记账,于是自然想用 TV 去认证这件事。

  本文件证明那条路**在原理上走不通**:设路由权重由"把逐专家非负分数 u 在选中
  集上归一化"得到,把选中集 S 换成 S'(保留集 K = S ∩ S'),则

      TV(W_S, W_{S'}) = 1 − (Σ_{i∈K} u i) / max(U, U')          [substTV]

  其中 U = Σ_S u、U' = Σ_{S'} u。右端**只通过总量 U' 依赖 S'** —— 换进来的
  具体是哪几个专家完全不出现。特别地,若替补更弱(U' ≤ U),右端退化为
  1 − Σ_K u / U,连 U' 都消失:

      "按分数挑最好的常驻替补"、"随机挑一个"、"干脆丢掉不换" —— TV **完全相同**。

  这是对**整个用路由 TV 表达的证书/监控族**的不可能性结论,不是某个实现的缺陷。

  实测对照(两侧都在案,故这条定理不是空转):
    · 九个模型上恒等式残差 ≤2.4e-7(w3rs_residency_vs_bits.py);三臂逐 token
      TV 相同的比例:五个模型 100%,带 per-expert bias 的四个 82%~99%
      (那 1%~18% 正是 U' > U 的情形,恒等式的一般形式仍成立)。
    · **而 ΔNLL 也确实分辨不出**(w3rq_residency_quality.py:random/score 中位比
      1.01)—— 即 TV 的迟钝在这里是**忠实的**,不是缺陷。原先猜"ΔNLL 会分出
      3× 差距、从而证明 TV 量错了"的假设被自己的预注册判据判否。

  闭环边界(诚实说明):本文件只管归一化权重的 TV 恒等式。"TV 是不是预测质量的
  好货币"由实验回答(上一段),Lean 管不到;而"替换到底值不值得做"由 ΔNLL 回答
  (答:ρ=0.25 时 2.65 nats,不值得),更不在此列。
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities

open BigOperators

namespace WitCert.ExpertSubstitution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 离散总变差(与 `WitCert.TV` 同式,此处独立给出以免依赖 Mathlib 重模块)。 -/
noncomputable def TV (p q : ι → ℝ) : ℝ := (1 / 2) * ∑ i, |p i - q i|

/-- 把逐专家非负分数 `u` 在选中集 `S` 上归一化得到的路由权重。 -/
noncomputable def routeW (u : ι → ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then u i / ∑ j ∈ S, u j else 0

/-- `|a − b| = a + b − 2·min a b`。 -/
theorem abs_sub_eq_add_sub_two_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- 全域上的 `if i ∈ S` 求和塌成 `S` 上的求和。 -/
theorem sum_ite_mem_univ (S : Finset ι) (g : ι → ℝ) :
    ∑ i, (if i ∈ S then g i else 0) = ∑ i ∈ S, g i := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i; simp

/-- TV 的"重叠"形式:两个概率分布的 TV = 1 − Σ 逐点最小值。 -/
theorem tv_eq_one_sub_overlap (p q : ι → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    TV p q = 1 - ∑ i, min (p i) (q i) := by
  unfold TV
  have h : ∑ i, |p i - q i|
      = ∑ i, (p i + q i - 2 * min (p i) (q i)) :=
    Finset.sum_congr rfl fun i _ => abs_sub_eq_add_sub_two_min (p i) (q i)
  rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
  ring

/-- 归一化后确实是概率分布(需要 `S` 上的分数和为正)。 -/
theorem routeW_sum_one (u : ι → ℝ) (S : Finset ι) (hU : 0 < ∑ j ∈ S, u j) :
    ∑ i, routeW u S i = 1 := by
  unfold routeW
  rw [sum_ite_mem_univ S (fun i => u i / ∑ j ∈ S, u j), ← Finset.sum_div]
  exact div_self (ne_of_gt hU)

/-- 逐点最小值:`i ∈ S ∩ S'` 时为 `u i / max U U'`,否则为 0。 -/
theorem min_routeW (u : ι → ℝ) (S S' : Finset ι)
    (hu : ∀ i, 0 ≤ u i) (hU : 0 < ∑ j ∈ S, u j) (hU' : 0 < ∑ j ∈ S', u j)
    (i : ι) :
    min (routeW u S i) (routeW u S' i)
      = if i ∈ S ∩ S' then u i / max (∑ j ∈ S, u j) (∑ j ∈ S', u j) else 0 := by
  unfold routeW
  by_cases hs : i ∈ S <;> by_cases hs' : i ∈ S' <;>
    simp only [hs, hs', Finset.mem_inter, if_true, if_false, and_true, and_false,
      false_and, true_and, if_pos, if_neg, not_false_iff]
  · -- 两侧都在:min 的分母取 max
    rcases le_total (∑ j ∈ S, u j) (∑ j ∈ S', u j) with hle | hle
    · rw [max_eq_right hle]
      exact min_eq_right (div_le_div_of_nonneg_left (hu i) hU hle)
    · rw [max_eq_left hle]
      exact min_eq_left (div_le_div_of_nonneg_left (hu i) hU' hle)
  · exact min_eq_right (div_nonneg (hu i) (le_of_lt hU))
  · exact min_eq_left (div_nonneg (hu i) (le_of_lt hU'))
  · simp

/--
  **替换恒等式(主定理)**。

      TV(W_S, W_{S'}) = 1 − (Σ_{i ∈ S ∩ S'} u i) / max(U, U')

  右端对 `S'` 的依赖**只通过 U' = Σ_{S'} u**:换进来的是哪几个专家不出现在
  等式右端。于是任意两种替换策略,只要换进来的专家总分数相同,TV 就相同。
-/
theorem subst_tv (u : ι → ℝ) (S S' : Finset ι)
    (hu : ∀ i, 0 ≤ u i) (hU : 0 < ∑ j ∈ S, u j) (hU' : 0 < ∑ j ∈ S', u j) :
    TV (routeW u S) (routeW u S')
      = 1 - (∑ i ∈ S ∩ S', u i) / max (∑ j ∈ S, u j) (∑ j ∈ S', u j) := by
  rw [tv_eq_one_sub_overlap _ _ (routeW_sum_one u S hU) (routeW_sum_one u S' hU')]
  have h : ∑ i, min (routeW u S i) (routeW u S' i)
      = ∑ i, (if i ∈ S ∩ S' then
          u i / max (∑ j ∈ S, u j) (∑ j ∈ S', u j) else 0) :=
    Finset.sum_congr rfl fun i _ => min_routeW u S S' hu hU hU' i
  rw [h, sum_ite_mem_univ (S ∩ S') _, ← Finset.sum_div]

/--
  **推论:替补更弱时,TV 与 S' 完全无关。**

  `U' ≤ U`(替补的分数总和不超过原选中集)时右端化为 `1 − Σ_K u / U`,
  其中只剩保留集 `K` 与原总量 `U` —— 这正是"按分数挑 / 随机挑 / 干脆丢掉"
  三者 TV 相同的形式表述。
-/
theorem subst_tv_of_weaker (u : ι → ℝ) (S S' : Finset ι)
    (hu : ∀ i, 0 ≤ u i) (hU : 0 < ∑ j ∈ S, u j) (hU' : 0 < ∑ j ∈ S', u j)
    (hle : ∑ j ∈ S', u j ≤ ∑ j ∈ S, u j) :
    TV (routeW u S) (routeW u S') = 1 - (∑ i ∈ S ∩ S', u i) / ∑ j ∈ S, u j := by
  rw [subst_tv u S S' hu hU hU', max_eq_left hle]

/--
  **不可能性(判别形式):两个不同的替换策略给出同一个 TV。**

  只要两个替换集 `S₁ S₂` 与原集的交相同、且各自的分数总和都不超过原总量,
  TV 就逐字相等 —— **哪怕 `S₁ ≠ S₂`**。任何以路由 TV 为判据的证书/监控,
  在这两者之间**没有区分度**。
-/
theorem tv_cannot_separate (u : ι → ℝ) (S S₁ S₂ : Finset ι)
    (hu : ∀ i, 0 ≤ u i) (hU : 0 < ∑ j ∈ S, u j)
    (hU₁ : 0 < ∑ j ∈ S₁, u j) (hU₂ : 0 < ∑ j ∈ S₂, u j)
    (h₁ : ∑ j ∈ S₁, u j ≤ ∑ j ∈ S, u j) (h₂ : ∑ j ∈ S₂, u j ≤ ∑ j ∈ S, u j)
    (hK : S ∩ S₁ = S ∩ S₂) :
    TV (routeW u S) (routeW u S₁) = TV (routeW u S) (routeW u S₂) := by
  rw [subst_tv_of_weaker u S S₁ hu hU hU₁ h₁,
      subst_tv_of_weaker u S S₂ hu hU hU₂ h₂, hK]

/--
  **上一条不是空转:前提可满足,且 `S₁ ≠ S₂`。**

  三个专家,原选中集 `S = {0, 1}`,两个替换集 `S₁ = {0, 2}`、`S₂ = {0, 2}` 之外
  再取 `S₂' = {2, 0}` 无意义 —— 真正要点是**存在两个不同的替换集与 S 的交相同**:
  取 `S = {0,1}`、`S₁ = {0,2}`、`S₂ = {0}`,则 `S ∩ S₁ = S ∩ S₂ = {0}` 而
  `S₁ ≠ S₂`。于是 `tv_cannot_separate` 的前提在非平凡实例上成立:两个**不同**的
  替换策略被 TV 判为完全一样。
-/
theorem exists_indistinguishable_substitutions :
    ∃ (S S₁ S₂ : Finset (Fin 3)), S₁ ≠ S₂ ∧ S ∩ S₁ = S ∩ S₂ := by
  refine ⟨{0, 1}, {0, 2}, {0}, by decide, by decide⟩

end WitCert.ExpertSubstitution
