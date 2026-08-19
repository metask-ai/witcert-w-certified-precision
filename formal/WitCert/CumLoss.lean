/-
  WitCert 形式化 · L9:**累计损失的 anytime-valid admission 定理**(E12 路线 b)

  P0 纠偏(TinyKG 11244)后的正确保证对象:不再对"逐事件失败"下注
  (那需要 union 累积),而是直接上界**累计实现损失**:

      P( ∃ t ≤ T,  Σ_{s≤t} L_s  >  B_t ) ≤ δ,   任意 T、随时停,

  其中 admission 规则保证每一步的**可预测**账面
      cumM_t + (ln(1/δ) + cumΨ_t)/λ ≤ B_t
  (m_s、ψ_s 均 F_{s-1} 可测:m 为预抽均值项,ψ 为条件 MGF 上界 ——
  正是 McDiarmid/两点 MGF 机器已提供的量;fallback 事件 L=m=ψ=0 自然吸收)。

  证明结构:指数积恒等(prodProcess = exp(λΣ(L−m) − Σψ))+ 事件包含
  (超预算 ⟹ 财富 ≥ 1/δ)+ 谓词版命中概率单调 + 复用 eprocess_ville。
  与被纠偏的错误设计的差别:财富越线在这里**就是**损失超预算的充分表征,
  不是"模型不诚实"的检验统计量 —— 保证对象与 SLA 对齐。
-/
import WitCert.Ville
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators

namespace WitCert.Calculus.CumLoss

open WitCert.Calculus.Ville

variable {σ : Type*} [Fintype σ]

open Classical

/-- 谓词版命中概率:从历史 h 再走 T 步,途中(含当下)满足 Q 的概率。 -/
noncomputable def hitProbP (D : Draw σ) (Q : List σ → Prop) :
    ℕ → List σ → ℝ
  | 0, h => if Q h then 1 else 0
  | T + 1, h => if Q h then 1 else ∑ x, D.p x * hitProbP D Q T (x :: h)

/-- 上界 1。 -/
lemma hitProbP_le_one (D : Draw σ) (Q : List σ → Prop) :
    ∀ T h, hitProbP D Q T h ≤ 1 := by
  intro T
  induction T with
  | zero =>
    intro h; unfold hitProbP; split <;> norm_num
  | succ T ih =>
    intro h
    unfold hitProbP
    split
    · norm_num
    · calc ∑ x, D.p x * hitProbP D Q T (x :: h)
          ≤ ∑ x, D.p x * 1 :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (ih (x :: h)) (D.nonneg x)
        _ = 1 := by simpa [mul_one] using D.total

/-- 单调:逐历史蕴含 ⟹ 命中概率不减。 -/
lemma hitProbP_mono (D : Draw σ) {Q₁ Q₂ : List σ → Prop}
    (himp : ∀ h, Q₁ h → Q₂ h) :
    ∀ T h, hitProbP D Q₁ T h ≤ hitProbP D Q₂ T h := by
  intro T
  induction T with
  | zero =>
    intro h
    unfold hitProbP
    by_cases h1 : Q₁ h
    · simp [h1, himp h h1]
    · by_cases h2 : Q₂ h <;> simp [h1, h2]
  | succ T ih =>
    intro h
    unfold hitProbP
    by_cases h1 : Q₁ h
    · simp [h1, himp h h1]
    · by_cases h2 : Q₂ h
      · simp only [h1, h2, if_false, if_true]
        calc ∑ x, D.p x * hitProbP D Q₁ T (x :: h)
            ≤ ∑ x, D.p x * 1 :=
              Finset.sum_le_sum fun x _ =>
                mul_le_mul_of_nonneg_left
                  (hitProbP_le_one D Q₁ T (x :: h)) (D.nonneg x)
          _ = 1 := by simpa [mul_one] using D.total
      · simp only [h1, h2, if_false]
        exact Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (ih (x :: h)) (D.nonneg x)

/-- 谓词版与阈值版一致(取 Q = "过程 ≥ c")。 -/
lemma hitProbP_eq_hitProb (D : Draw σ) (M : List σ → ℝ) (c : ℝ) :
    ∀ T h, hitProbP D (fun h => c ≤ M h) T h = hitProb D M c T h := by
  intro T
  induction T with
  | zero => intro h; unfold hitProbP hitProb; rfl
  | succ T ih =>
    intro h
    unfold hitProbP hitProb
    by_cases hc : c ≤ M h
    · simp [hc]
    · simp only [hc, if_false]
      exact Finset.sum_congr rfl fun x _ => by rw [ih]

/-- 沿历史的逐步累计(步函数依赖历史与当步抽签)。 -/
def cumStep (f : List σ → σ → ℝ) : List σ → ℝ
  | [] => 0
  | x :: h => cumStep f h + f h x

/-- 沿历史的可预测累计(只依赖历史)。 -/
def cumPred (f : List σ → ℝ) : List σ → ℝ
  | [] => 0
  | _ :: h => cumPred f h + f h

omit [Fintype σ] in
/-- 指数积恒等:指数因子的乘积过程 = 累计和的指数。 -/
lemma prodProcess_exp (L : List σ → σ → ℝ) (m ψ : List σ → ℝ) (lam : ℝ) :
    ∀ h, prodProcess (fun h x => Real.exp (lam * (L h x - m h) - ψ h)) h
      = Real.exp (lam * (cumStep L h - cumPred m h) - cumPred ψ h) := by
  intro h
  induction h with
  | nil => simp [prodProcess, cumStep, cumPred]
  | cons _ h ih =>
    simp only [prodProcess, cumStep, cumPred, ih, ← Real.exp_add]
    ring_nf

/--
  **主定理(E12 路线 b)**:admission 规则下,累计实现损失任意时刻超预算的
  概率 ≤ δ。

  假设:
  · `hmean`:逐历史条件 MGF 条件(由 McDiarmid/两点 MGF 在别处 discharge);
  · `hadm`:admission 账面不变量 —— 每个可达历史满足
        cumM + (ln(1/δ) + cumΨ)/λ ≤ B(len);
    (真实系统只对**已 admit** 的动作收此账;fallback 的 L=m=ψ=0 使
    该步因子为 1、账面不动,故对全历史陈述即保守成立。)
-/
theorem cumloss_admission (D : Draw σ) (L : List σ → σ → ℝ)
    (m ψ : List σ → ℝ) (B : ℕ → ℝ) {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmean : ∀ h, ∑ x, D.p x *
        Real.exp (lam * (L h x - m h) - ψ h) ≤ 1)
    (hadm : ∀ h : List σ,
        cumPred m h + (Real.log (1 / δ) + cumPred ψ h) / lam ≤ B h.length) :
    ∀ T, hitProbP D (fun h => B h.length < cumStep L h) T [] ≤ δ := by
  intro T
  set g : List σ → σ → ℝ :=
    fun h x => Real.exp (lam * (L h x - m h) - ψ h) with hg_def
  -- 事件包含:超预算 ⟹ 财富 ≥ 1/δ
  have himp : ∀ h, (B h.length < cumStep L h) →
      (1 / δ ≤ prodProcess g h) := by
    intro h hover
    have h1 : cumPred m h + (Real.log (1 / δ) + cumPred ψ h) / lam
        < cumStep L h := lt_of_le_of_lt (hadm h) hover
    have h2 : Real.log (1 / δ) + cumPred ψ h
        < lam * (cumStep L h - cumPred m h) := by
      have := (div_lt_iff₀ hlam).mp (by linarith : (Real.log (1 / δ)
          + cumPred ψ h) / lam < cumStep L h - cumPred m h)
      linarith [this]
    have h3 : Real.log (1 / δ)
        < lam * (cumStep L h - cumPred m h) - cumPred ψ h := by linarith
    have h4 : (1 : ℝ) / δ
        ≤ Real.exp (lam * (cumStep L h - cumPred m h) - cumPred ψ h) := by
      have := Real.exp_lt_exp.mpr h3
      rw [Real.exp_log (by positivity : (0:ℝ) < 1 / δ)] at this
      exact this.le
    rw [prodProcess_exp]
    exact h4
  calc hitProbP D (fun h => B h.length < cumStep L h) T []
      ≤ hitProbP D (fun h => 1 / δ ≤ prodProcess g h) T [] :=
        hitProbP_mono D himp T []
    _ = hitProb D (prodProcess g) (1 / δ) T [] :=
        hitProbP_eq_hitProb D (prodProcess g) (1 / δ) T []
    _ ≤ δ := eprocess_ville D g hδ hδ1
        (fun h x => Real.exp_nonneg _) hmean T

/-! ## 控制面:prospective 物理门控实现的 soundness(①b,extract phys 模式)

    cumloss_admission 保证"admission 维持账面 ⟹ 累计损失不越预算"(概率层)。
    但 ①b 的门控**实现**用了一个工程近似:授权前不知哪些条目通过量级门,故
    用**全批** m/C 上界(_m_batch/_C_batch)算 charged,而 settle 只累加**实际
    通过**(passed⊆全批)的 m/C。这个"用全批代替 passed"的正确性是新的义务,
    不在概率定理里 —— 它属于控制面(admission control):**prospective 保守
    门控 admit ⟹ realized(passed 子集)必然也满足预算**。本段钉死它。 -/

/-- tail 项 (ln(1/δ)+λ²C/8)/λ:对累计 C 单调不减(λ>0)。 -/
noncomputable def tailTerm (lam logInvδ C : ℝ) : ℝ :=
  (logInvδ + lam ^ 2 * C / 8) / lam

lemma tailTerm_mono {lam logInvδ : ℝ} (hlam : 0 < lam) {C₁ C₂ : ℝ}
    (h : C₁ ≤ C₂) : tailTerm lam logInvδ C₁ ≤ tailTerm lam logInvδ C₂ := by
  unfold tailTerm
  gcongr

/-- 物理门控账面:charged = cum_m + m_batch + tail(cum_C + C_batch)。 -/
noncomputable def phCharged (cum_m cum_C m_batch C_batch lam logInvδ : ℝ) : ℝ :=
  cum_m + m_batch + tailTerm lam logInvδ (cum_C + C_batch)

/-- **保守门控**:passed 子集的 m/C 不超过全批(m_pass≤m_all, C_pass≤C_all),
    则 realized charged ≤ prospective charged。 -/
theorem gating_conservative {cum_m cum_C lam logInvδ : ℝ} (hlam : 0 < lam)
    {m_all m_pass C_all C_pass : ℝ}
    (hm : m_pass ≤ m_all) (hC : C_pass ≤ C_all) :
    phCharged cum_m cum_C m_pass C_pass lam logInvδ
      ≤ phCharged cum_m cum_C m_all C_all lam logInvδ := by
  unfold phCharged
  have ht : tailTerm lam logInvδ (cum_C + C_pass)
      ≤ tailTerm lam logInvδ (cum_C + C_all) :=
    tailTerm_mono hlam (by linarith)
  linarith

/-- **控制面 soundness**(①b 核心):prospective 门控用全批上界判 admit,
    则实际通过(passed)子集必然满足同一预算 —— "用全批代替 passed" sound。
    这把 extract phys 门控的工程近似的正确性钉死:admit 不会放行一个
    realized 越预算的调用。 -/
theorem admit_implies_realized_within {cum_m cum_C lam logInvδ B : ℝ}
    (hlam : 0 < lam) {m_all m_pass C_all C_pass : ℝ}
    (hm : m_pass ≤ m_all) (hC : C_pass ≤ C_all)
    (hadmit : phCharged cum_m cum_C m_all C_all lam logInvδ ≤ B) :
    phCharged cum_m cum_C m_pass C_pass lam logInvδ ≤ B :=
  le_trans (gating_conservative hlam hm hC) hadmit

/-- **违规实例(闭环:带违规实例的规则)**:若门控错误地用 passed 子集的 m/C
    (而非全批上界)判 admit,则存在配置 —— admit 通过(passed 账面 ≤ B)但
    全批 realized 越预算(> B)。这正是 extract phys 门控**必须**用
    _m_batch/_C_batch(全批,授权前)而非 passed 的原因:用 passed 判会放行
    一个整批越预算的写调用。extract 的保守取用由 test_phys_gate_math 的
    "wide 全 admit/tight 中段触发"实证,越权取用由本定理证否。 -/
theorem nonconservative_admit_can_exceed :
    ∃ cum_m cum_C m_all m_pass C_all C_pass lam logInvδ B : ℝ,
      0 < lam ∧ m_pass ≤ m_all ∧ C_pass ≤ C_all ∧
      phCharged cum_m cum_C m_pass C_pass lam logInvδ ≤ B ∧
      B < phCharged cum_m cum_C m_all C_all lam logInvδ :=
  ⟨0, 0, 100, 1, 0, 0, 1, 0, 50, by norm_num,
   by norm_num [phCharged, tailTerm], by norm_num [phCharged, tailTerm]⟩

/-- **预算下限**(量纲义务):tail 基线 = ln(1/δ)/λ(C=0 时)。B 低于它则
    连空批都超账 —— 门控无 admit 空间。extract 的 B_phys 必须 > 此基线
    (离线 test_phys_gate_math 验:预注册 wide/tight 均 » 1151)。 -/
theorem budget_floor {lam logInvδ B : ℝ}
    (hB : B < logInvδ / lam) :
    B < phCharged 0 0 0 0 lam logInvδ := by
  have h : phCharged 0 0 0 0 lam logInvδ = logInvδ / lam := by
    simp [phCharged, tailTerm]
  rw [h]; exact hB

end WitCert.Calculus.CumLoss
