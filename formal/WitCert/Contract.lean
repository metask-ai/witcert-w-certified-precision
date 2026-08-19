/-
  WitCert 形式化 · L5:**带度量类型的误差契约**(论文2 的中心定理)

  动机:论文2 的核心主张不是某一条复杂不等式,而是"不同类型的误差契约能否**合法组合**"。
  Python 侧 `contracts.py` 的 `Contract` 只有 (a, b, δ) 三个浮点数,`compose()` 直接算
  `a₂·b₁ + b₂` —— 它无法察觉 b₁ 的单位是「KV 条目的相对残差」而 b₂ 的单位是
  「注意力分布的全变差」。**这两个数相加没有意义**,而三档 registry 也拦不住:
  它检查的是"这个指标属于哪一档",不是"这两段的度量能不能对接"。

  本文件把**度量做成类型参数**,于是:
    · 串联只在「前段输出度量 = 后段输入度量」时才通过类型检查;
    · 跨度量组合必须显式插入一个**已证的桥接契约**,否则这个值根本构造不出来;
    · "缺 selector→attention 的桥"不再是论文里的一句自述,而是**编译期错误**。

  与 Python 侧的分工(三层证据,缺一不可):
      Lean 定理        保证「公式组合合法」          —— 本文件
      contract checker 保证「运行时用了正确的契约」  —— src/witcert/probe/contracts.py
      测试与实验       保证「实现符合模型假设」      —— tests/ + experiments/
  形式化**不能**替以下事实背书,它们只能靠实验:各层真实传播系数、算子 Lipschitz 常数、
  用样本中位数代替逐请求上界的合理性、Triton/CUDA 实现与本模型的对应、浮点与并发行为。
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace WitCert.Calculus

/-! ### 1. 带类型的误差契约 -/

/--
  载体 `α` 上的一个**误差度量**。

  关键在于:同一个载体上可以有多个不同的 `ErrMetric`(如 KV 向量上的「相对残差」与
  「绝对 ℓ2 残差」),**它们是不同的对象**,契约不能跨着组合。这正是要靠类型
  而不是靠命名约定来保证的事。
-/
structure ErrMetric (α : Type) where
  d : α → α → ℝ
  d_nonneg : ∀ x y, 0 ≤ d x y

/--
  从 `(α, mα)` 到 `(β, mβ)` 的**仿射误差契约**:

      d_β (exact x, approx x̂) ≤ a · d_α (x, x̂) + b

  `exact` 是理想实现,`approx` 是真实实现。契约携带的不只是两个系数,还有
  **它所断言的那个不等式的证明**(`sound`)—— 所以"有一个 Contract 值"本身就是
  "这段的界已被证明"的机器证据,而不是一条标签。
-/
structure Contract {α β : Type} (mα : ErrMetric α) (mβ : ErrMetric β) where
  a : ℝ
  b : ℝ
  ha : 0 ≤ a
  hb : 0 ≤ b
  exact : α → β
  approx : α → β
  sound : ∀ x x', mβ.d (exact x) (approx x') ≤ a * mα.d x x' + b

/-! ### 2. 串联组合定理(论文2 的基础组合定理) -/

/--
  **契约串联**。类型签名本身就是那条纪律:`C₂` 的输入度量必须**恰好是** `C₁` 的
  输出度量 `mβ`,否则这个应用式无法通过类型检查 —— 这就是"数学类型检查器"。

  系数为 `(a₂a₁, a₂b₁+b₂)`,与 Python 侧 `Chain.compose()` 一致;
  区别在于这里的等式带着证明,而那边只是浮点算术。
-/
def comp {α β γ : Type} {mα : ErrMetric α} {mβ : ErrMetric β} {mγ : ErrMetric γ}
    (C₂ : Contract mβ mγ) (C₁ : Contract mα mβ) : Contract mα mγ where
  a := C₂.a * C₁.a
  b := C₂.a * C₁.b + C₂.b
  ha := mul_nonneg C₂.ha C₁.ha
  hb := add_nonneg (mul_nonneg C₂.ha C₁.hb) C₂.hb
  exact := C₂.exact ∘ C₁.exact
  approx := C₂.approx ∘ C₁.approx
  sound := by
    intro x x'
    have h1 : mβ.d (C₁.exact x) (C₁.approx x') ≤ C₁.a * mα.d x x' + C₁.b := C₁.sound x x'
    have h2 : mγ.d (C₂.exact (C₁.exact x)) (C₂.approx (C₁.approx x'))
        ≤ C₂.a * mβ.d (C₁.exact x) (C₁.approx x') + C₂.b := C₂.sound _ _
    have h3 : C₂.a * mβ.d (C₁.exact x) (C₁.approx x')
        ≤ C₂.a * (C₁.a * mα.d x x' + C₁.b) := by
      exact mul_le_mul_of_nonneg_left h1 C₂.ha
    calc mγ.d (C₂.exact (C₁.exact x)) (C₂.approx (C₁.approx x'))
        ≤ C₂.a * mβ.d (C₁.exact x) (C₁.approx x') + C₂.b := h2
      _ ≤ C₂.a * (C₁.a * mα.d x x' + C₁.b) + C₂.b := by linarith
      _ = C₂.a * C₁.a * mα.d x x' + (C₂.a * C₁.b + C₂.b) := by ring

/--
  **串联组合定理**(显式陈述版,供论文引用):两段契约复合后的界恰为 `(a₂a₁, a₂b₁+b₂)`,
  且第一段的输出度量与第二段的输入度量由类型系统保证完全一致。
-/
theorem comp_sound {α β γ : Type} {mα : ErrMetric α} {mβ : ErrMetric β} {mγ : ErrMetric γ}
    (C₂ : Contract mβ mγ) (C₁ : Contract mα mβ) (x x' : α) :
    mγ.d (C₂.exact (C₁.exact x)) (C₂.approx (C₁.approx x'))
      ≤ (C₂.a * C₁.a) * mα.d x x' + (C₂.a * C₁.b + C₂.b) :=
  (comp C₂ C₁).sound x x'

/-- 恒等契约:`(a, b) = (1, 0)`。串联的单位元。 -/
def idContract {α : Type} (mα : ErrMetric α) : Contract mα mα where
  a := 1; b := 0
  ha := zero_le_one; hb := le_refl 0
  exact := id; approx := id
  sound := by intro x x'; simp

/--
  **桥接契约**:同一载体上两个不同度量之间的换算。它就是一个 `exact = approx = id`
  的契约,所以"必须先有已证的桥接定理才能跨度量组合"在类型层面自动成立 ——
  没有这个值,`comp` 就没有可插入的一段。
-/
structure Bridge {α : Type} (m m' : ErrMetric α) where
  toContract : Contract m m'
  /-- 桥接不改变对象本身,只换度量 —— 这两条把它钉死为"换算",而不是又一段计算。 -/
  exact_id : toContract.exact = id
  approx_id : toContract.approx = id

/-- 桥接的语义:同一对对象在新度量下的距离被旧度量仿射控制。 -/
theorem bridge_sound {α : Type} {m m' : ErrMetric α} (B : Bridge m m') (x x' : α) :
    m'.d x x' ≤ B.toContract.a * m.d x x' + B.toContract.b := by
  have h := B.toContract.sound x x'
  rw [B.exact_id, B.approx_id] at h
  simpa using h

/-! ### 3. 自适应请求级风险预算(条件式 union bound) -/

namespace Budget

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/--
  **条件式 union bound**。假设写成「首次失败」形式:

      μ (E i \ ⋃_{j<i} E j) ≤ δ i

  它由 `P(E i ∣ 前 i 段都没失败) ≤ δ i` 直接推出(两边乘以 ≤ 1 的历史概率)。
  这比"对所有层做无条件 union bound"更贴近真实运行时:探针档位、回退、量化选择
  都可能**依赖前面的执行结果**,此时 `μ (E i) ≤ δ i` 本身未必成立,而条件版仍然成立。

  注意本证明**不需要可测性假设** —— 用的是测度的次可加性。
-/
theorem conditional_union_le (E : ℕ → Set Ω) (δ : ℕ → ENNReal)
    (h : ∀ i, μ (E i \ ⋃ j ∈ Finset.range i, E j) ≤ δ i) (n : ℕ) :
    μ (⋃ i ∈ Finset.range n, E i) ≤ ∑ i ∈ Finset.range n, δ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (⋃ i ∈ Finset.range (n + 1), E i)
        = (⋃ i ∈ Finset.range n, E i) ∪ (E n \ ⋃ j ∈ Finset.range n, E j) := by
      ext ω
      simp only [Finset.mem_range, Set.mem_iUnion, Set.mem_union, Set.mem_diff,
                 Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨i, hi, hω⟩
        by_cases hlt : ∃ j, j < n ∧ ω ∈ E j
        · exact Or.inl hlt
        · have : i = n := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
            · exact absurd ⟨i, h', hω⟩ hlt
            · exact h'
          exact Or.inr ⟨this ▸ hω, hlt⟩
      · rintro (⟨i, hi, hω⟩ | ⟨hω, _⟩)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hω⟩
        · exact ⟨n, Nat.lt_succ_self n, hω⟩
    rw [hsplit, Finset.sum_range_succ]
    exact le_trans (measure_union_le _ _) (add_le_add ih (h n))

/--
  无条件版是条件版的推论:若各段**边缘**概率就已 ≤ δ i,则条件形式的假设自然满足
  (差集只会变小)。保留它是为了说明条件版**严格更强**,不是换了个写法。
-/
theorem conditional_union_le_of_marginal (E : ℕ → Set Ω) (δ : ℕ → ENNReal)
    (h : ∀ i, μ (E i) ≤ δ i) (n : ℕ) :
    μ (⋃ i ∈ Finset.range n, E i) ≤ ∑ i ∈ Finset.range n, δ i :=
  conditional_union_le μ E δ (fun i => le_trans (measure_mono Set.diff_subset) (h i)) n

end Budget

/-! ### 4. 三个代表性局部定理 -/

/--
  **Lemma P1(池化,ℓ∞ 口径)**:凸组合不放大逐槽误差上界,即 `a = 1, b = 0`,
  且**不需要任何额外假设**(只要权重非负且和为 1)。

  这是池化段两个口径中"无假设"的那个;ℓ2 口径给 `a = ‖w‖₂ ≤ 1`,更紧但要求
  入口误差按 ℓ2 聚合。选哪个口径决定了 `e_in` 的定义,**不能混用**。
-/
theorem pool_linf {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (Δ : Fin n → E) (e : ℝ) (hΔ : ∀ j, ‖Δ j‖ ≤ e) :
    ‖∑ j, w j • Δ j‖ ≤ e := by
  calc ‖∑ j, w j • Δ j‖ ≤ ∑ j, ‖w j • Δ j‖ := norm_sum_le _ _
    _ = ∑ j, w j * ‖Δ j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, w j * e := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hΔ j) (hw j)
    _ = e := by rw [← Finset.sum_mul, hsum, one_mul]

/--
  **rank-prefix 稳定性**:若逐项扰动不超过 ε,且集合 `S` 与其补集之间的分数间隙
  严格大于 `2ε`,则扰动后 `S` 仍然整体高于补集 —— top-k 前缀不变。

  `2ε` 不能减半:i 可能被压低 ε 而 j 可能被抬高 ε,两边各让一半。
  这条**只在可判定子集上成立**(margin > 2ε 的那些行),故对应档位是 partial 而非
  certified —— 档位不是修辞,它就是"这条定理的前提能否被运行时判定"。
-/
theorem rank_prefix_stable {ι : Type*} (s s' : ι → ℝ) (ε : ℝ)
    (hε : ∀ i, |s i - s' i| ≤ ε) (S : Set ι)
    (hgap : ∀ i ∈ S, ∀ j ∉ S, s j + 2 * ε < s i) :
    ∀ i ∈ S, ∀ j ∉ S, s' j < s' i := by
  intro i hi j hj
  have hi' := abs_le.mp (hε i)
  have hj' := abs_le.mp (hε j)
  have := hgap i hi j hj
  linarith [hi'.1, hi'.2, hj'.1, hj'.2]

/--
  **哨兵检测延迟**:若单轮漏检概率为 `q ∈ (0,1)` 且各轮独立,则 `n` 轮全漏的概率是
  `q^n`;要把它压到 `δ` 以下,取 `n ≥ log δ / log q` 即可。

  这里形式化的是**预算算术**那一半(由 q 与 δ 定 n),概率那一半(单轮漏检恰为超几何
  `C(M-B,r)/C(M,r)`、各轮独立)是模型假设,由实验对拍,不由本定理背书。
-/
theorem sentinel_rounds {q δ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ)
    {n : ℕ} (hn : Real.log δ / Real.log q ≤ n) : q ^ n ≤ δ := by
  have hlq : Real.log q < 0 := Real.log_neg hq0 hq1
  have h1 : (n : ℝ) * Real.log q ≤ Real.log δ := (div_le_iff_of_neg hlq).mp hn
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq0 n
  have h2 : Real.log (q ^ n) ≤ Real.log δ := by rw [Real.log_pow]; exact h1
  exact (Real.log_le_log_iff hqn hδ).mp h2

/-! ### 5. 非法组合:类型检查器当场拒绝 -/

namespace Illegal

/--
  存储侧的输出度量:**相对残差**(无量纲比值)。
-/
noncomputable def relResidual : ErrMetric ℝ where
  d x y := |x - y| / (1 + |x|)
  d_nonneg _x _y := div_nonneg (abs_nonneg _) (by positivity)

/--
  选择侧的输入度量:**全变差**(概率质量)。

  **载体故意取成与 `relResidual` 相同的 `ℝ`** —— 这样反例才说明问题:
  即使两段的载体完全一致,只要**度量不同**,组合就通不过类型检查。
  换句话说,拦住非法组合的不是"类型对不上",而是"单位对不上"。
-/
noncomputable def attnTV : ErrMetric ℝ where
  d x y := |x - y| / 2
  d_nonneg _x _y := by positivity

/-- 入口与出口的占位度量(内容无关,只为把两段契约的两端补齐)。 -/
noncomputable def anyMetric : ErrMetric ℝ where
  d x y := |x - y|
  d_nonneg _x _y := abs_nonneg _

/-- 存储段:输出的是**相对残差**。 -/
noncomputable def storeC : Contract anyMetric relResidual where
  a := 1; b := 1
  ha := zero_le_one; hb := zero_le_one
  exact := id; approx := id
  sound := by
    intro x x'
    have h0 : (0:ℝ) < 1 + |x| := by positivity
    have h1 : |x - x'| / (1 + |x|) ≤ |x - x'| := by
      rw [div_le_iff₀ h0]; nlinarith [abs_nonneg (x - x'), abs_nonneg x]
    simpa [relResidual, anyMetric] using by linarith

/-- 选择段:输入的是**全变差**。 -/
noncomputable def selectC : Contract attnTV anyMetric where
  -- **a=2 不是随手填的**:第一版写 a=1,b=1,Lean 当场拒绝 —— `|x-x'| ≤ |x-x'|/2 + 1`
  -- 在大误差下为假。同一个错误在 Python 侧只是两个浮点数,没人会发现。
  a := 2; b := 0
  ha := by norm_num
  hb := le_refl 0
  exact := id; approx := id
  sound := by
    intro x x'
    simp only [attnTV, anyMetric, id_eq]
    ring_nf
    exact le_refl _

/-
  **机器检查的反例**:把存储段接到选择段上 —— 这正是 Python 侧 `Chain.compose()`
  照做不误的那次组合(`a₂·b₁ + b₂`,b₁ 是相对残差、b₂ 是全变差)。

  `comp` 要求前段的输出度量与后段的输入度量是**同一个值**,而
  `relResidual ≠ attnTV`,故下式**无法通过类型检查**。`#guard_msgs` 把这条错误
  钉成编译期断言:哪天有人"顺手"让它能编译了,或者错误信息变了,构建就会失败。
-/
#check_failure comp selectC storeC

/--
  合法的做法:先给出一个**已证的桥接**,再组合。这里不构造它 —— 因为
  selector 分数到真实注意力质量的稳定性桥**目前并不存在**,这正是论文2 该补的洞。
  类型签名把这件事写死:没有 `Bridge relResidual attnTV` 这个值,就拼不出请求级证书。
-/
noncomputable def legalWithBridge (B : Bridge relResidual attnTV) :
    Contract anyMetric anyMetric :=
  comp selectC (comp B.toContract storeC)

end Illegal

end WitCert.Calculus
