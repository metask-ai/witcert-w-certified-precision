/-
  WitCert 形式化 · L8:**有限 Ω 上的 Ville 不等式与 e-process**(E3)

  动机:请求级预算的望远镜分账把 δ_req 切成几万份,后期事件的授权半径被
  log(1/δ_i) 机械放大。e-process 用一个随请求增长的乘积过程一次性认证任意时刻:

      P(∃ t ≤ T, M_t ≥ 1/δ) ≤ δ·M_0

  **为什么能绕开 Mathlib 鞅论**(缓存里没有那棵树):我们的随机源是有限离散的
  抽签(SR 的逐坐标伯努利),概率空间是有限乘积 —— 条件期望就是逐支加权和,
  "命中概率"可以对剩余时域**递归定义**,Ville 由一个三行归纳给出。
  没有测度论、没有停时理论、没有条件期望算子:全部是 Finset.sum。

  范围纪律(评估时已定):e-process 认证**累计过程**(如对数似然和/风险账户),
  不替代逐条目确定性检查 —— 两层结构不变,它接管的是概率层的分账。
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

open BigOperators

namespace WitCert.Calculus.Ville

variable {σ : Type*} [Fintype σ]

/-- 单步抽签的分布:非负、总和 1。 -/
structure Draw (σ : Type*) [Fintype σ] where
  p : σ → ℝ
  nonneg : ∀ x, 0 ≤ p x
  total : ∑ x, p x = 1

/--
  **命中概率**(对剩余时域递归):从历史 h 出发再走 T 步,过程 M(按历史索引,
  适应性由此内建)在途中(含当下)达到 ≥ c 的概率。

  这就是有限乘积测度下 sup 事件的概率 —— 逐支展开的加权和,定义即计算。
-/
noncomputable def hitProb (D : Draw σ) (M : List σ → ℝ) (c : ℝ) :
    ℕ → List σ → ℝ
  | 0, h => if c ≤ M h then 1 else 0
  | T + 1, h => if c ≤ M h then 1 else ∑ x, D.p x * hitProb D M c T (x :: h)

/- 历史约定:新抽签 cons 在头部(适应性不受编码影响,M 只看历史)。 -/

lemma hitProb_nonneg (D : Draw σ) (M : List σ → ℝ) (c : ℝ) :
    ∀ T h, 0 ≤ hitProb D M c T h := by
  intro T
  induction T with
  | zero => intro h; unfold hitProb; split <;> norm_num
  | succ T ih =>
    intro h
    unfold hitProb
    split
    · norm_num
    · exact Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (ih _)

/--
  **有限 Ville 不等式**:M 非负、单步条件均值不增(逐历史的加权和形式),则

      P(∃ t ≤ T, M_t ≥ c) = hitProb ≤ M(h)/c        (c > 0)

  证明:对剩余时域归纳。已达标 → 1 ≤ M/c;未达标 → 逐支用归纳假设,
  再用超鞅性质收拢。三行数学,零测度论。
-/
theorem ville (D : Draw σ) (M : List σ → ℝ) {c : ℝ} (hc : 0 < c)
    (hM : ∀ h, 0 ≤ M h)
    (hsuper : ∀ h, ∑ x, D.p x * M (x :: h) ≤ M h) :
    ∀ T h, hitProb D M c T h ≤ M h / c := by
  intro T
  induction T with
  | zero =>
    intro h
    unfold hitProb
    split
    · rename_i hle
      rw [le_div_iff₀ hc]; linarith
    · rename_i hlt
      push_neg at hlt
      exact div_nonneg (hM h) hc.le
  | succ T ih =>
    intro h
    unfold hitProb
    split
    · rename_i hle
      rw [le_div_iff₀ hc]; linarith
    · calc ∑ x, D.p x * hitProb D M c T (x :: h)
          ≤ ∑ x, D.p x * (M (x :: h) / c) :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (ih (x :: h)) (D.nonneg x)
        _ = (∑ x, D.p x * M (x :: h)) / c := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ M h / c := div_le_div_of_nonneg_right (hsuper h) hc.le

/--
  **e-process 构造**:单步因子 g(h, x) ≥ 0 且逐历史条件均值 ≤ 1,
  则乘积过程 M(h) = Π 因子 是非负超鞅 —— Ville 直接适用。

  实例化(概率层分账的替代):g = e^{λX − ψ(λ)},条件 MGF 界 E[e^{λX}|h] ≤ e^{ψ}
  即给出 Σ p·g ≤ 1;于是 P(∃t: ΣλX − Σψ ≥ ln(1/δ)) ≤ δ,**不切 δ、不知长度、随时停**。
-/
noncomputable def prodProcess (g : List σ → σ → ℝ) : List σ → ℝ
  | [] => 1
  | x :: h => prodProcess g h * g h x

theorem prodProcess_supermartingale (D : Draw σ) (g : List σ → σ → ℝ)
    (hg : ∀ h x, 0 ≤ g h x) (hmean : ∀ h, ∑ x, D.p x * g h x ≤ 1) :
    (∀ h, 0 ≤ prodProcess g h) ∧
    (∀ h, ∑ x, D.p x * prodProcess g (x :: h) ≤ prodProcess g h) := by
  have hnn : ∀ h, 0 ≤ prodProcess g h := by
    intro h
    induction h with
    | nil => simp [prodProcess]
    | cons x h ih => exact mul_nonneg ih (hg h x)
  refine ⟨hnn, ?_⟩
  · intro h
    have hM : 0 ≤ prodProcess g h := hnn h
    calc ∑ x, D.p x * prodProcess g (x :: h)
        = ∑ x, D.p x * (prodProcess g h * g h x) := rfl
      _ = prodProcess g h * ∑ x, D.p x * g h x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ prodProcess g h * 1 := mul_le_mul_of_nonneg_left (hmean h) hM
      _ = prodProcess g h := mul_one _

/-- 打包版:e-process 的任意时刻风险界(供论文与账本引用)。 -/
theorem eprocess_ville (D : Draw σ) (g : List σ → σ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hg : ∀ h x, 0 ≤ g h x) (hmean : ∀ h, ∑ x, D.p x * g h x ≤ 1) :
    ∀ T, hitProb D (prodProcess g) (1 / δ) T [] ≤ δ := by
  intro T
  obtain ⟨hnn, hsm⟩ := prodProcess_supermartingale D g hg hmean
  have h := ville D (prodProcess g) (c := 1 / δ) (by positivity) hnn hsm T []
  -- M₀ = 1,故界为 1/(1/δ) = δ
  have heq : prodProcess g ([] : List σ) / (1 / δ) = δ := by
    simp [prodProcess]
  rwa [heq] at h

end WitCert.Calculus.Ville
