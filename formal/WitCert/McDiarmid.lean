/-
  WitCert 形式化 · L10:**有限 Ω McDiarmid**(F3 Stage 2 —— E2 尾项的概率核心)

  实现中(dsv4_certified_write, dither 臂)的尾项

      tail = √(2·(Σ_c Δ_c²/4)·ln(n/δ_i))

  依赖的数学事实:W_e = Σ_b ‖d_b‖ 是各坐标 SR 抽签的**非线性**函数,但逐坐标
  bounded difference ≤ Δ_c;McDiarmid 给出 P(W ≥ E[W] + tail) ≤ δ_i/n。

  本文件在**有限乘积空间**上完整证明(延续 Ville.lean 的递归风格,零测度论):
    · `condE`:对剩余时域递归的条件期望 —— 定义即计算;
    · `condE_bdd_diff`:f 的逐坐标 bounded difference 传递到条件期望(pre 泛化归纳);
    · `sum_exp_le_of_mean_zero`:一般区间 Hoeffding 引理 —— 经 exp 凸性化归到
      Radius.two_point_mgf_le(常数 1/8 不放松);
    · `condE_exp_le`:Doob 结构的 MGF 归纳(Azuma–Hoeffding);
    · `mcdiarmid` / `mcdiarmid_radius`:尾界与**与实现同形**的半径表述。

  均值项 E[W] ≤ Σ_b √(Σ Var) 亦已形式化(§6:band_mean_le / witness_mean_le)——
  ‖d_b‖² 逐坐标可加**没有交叉项**,只需线性 + 递归 Jensen;§7 的
  eprocess_factor_mean_le_one 把 MGF 界接到 Ville 的 e-process 单步条件(F4)。
-/
import WitCert.Radius
import WitCert.Ville
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real WitCert.Calculus.Ville
open scoped Classical

namespace WitCert.Calculus.McDiarmid

variable {σ : Type*} [Fintype σ] [Nonempty σ]

/-! ### 1. 递归条件期望(定义即计算) -/

/-- 从历史 h 出发、再走 k 步的 f 期望(与 Ville.hitProb 同一约定:新抽签 cons 头部)。 -/
noncomputable def condE (D : Draw σ) (f : List σ → ℝ) : ℕ → List σ → ℝ
  | 0, h => f h
  | k + 1, h => ∑ x, D.p x * condE D f k (x :: h)

lemma condE_mono (D : Draw σ) {f g : List σ → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    ∀ k h, condE D f k h ≤ condE D g k h := by
  intro k
  induction k with
  | zero => intro h; exact hfg h
  | succ k ih =>
    intro h
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (ih (x :: h)) (D.nonneg x)

lemma condE_const_mul (D : Draw σ) (r : ℝ) (f : List σ → ℝ) :
    ∀ k h, condE D (fun ω => r * f ω) k h = r * condE D f k h := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih =>
    intro h
    show ∑ x, D.p x * condE D (fun ω => r * f ω) k (x :: h)
        = r * ∑ x, D.p x * condE D f k (x :: h)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [ih (x :: h)]; ring

/-! ### 2. bounded difference 及其向条件期望的传递 -/

/-- **逐坐标 bounded difference**(深度 = 该坐标之下的历史长度):
    换掉一个坐标,f 的改变 ≤ c(深度)。SR 见证 W = Σ_b ‖d_b‖ 对坐标 c 满足
    该性质且 c = Δ_c(范数的 1-Lipschitz)。 -/
def BddDiffAt (f : List σ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ (pre : List σ) (x y : σ) (h : List σ),
    |f (pre ++ x :: h) - f (pre ++ y :: h)| ≤ c h.length

lemma BddDiffAt.c_nonneg {f : List σ → ℝ} {c : ℕ → ℝ} (hf : BddDiffAt f c)
    (d : ℕ) : 0 ≤ c d := by
  obtain ⟨x⟩ := ‹Nonempty σ›
  have := hf [] x x (List.replicate d x)
  simpa using this

/-- bounded difference 传递到条件期望(对 pre 泛化的归纳 —— 关键技术步)。 -/
lemma condE_bdd_diff (D : Draw σ) {f : List σ → ℝ} {c : ℕ → ℝ}
    (hf : BddDiffAt f c) :
    ∀ k (pre : List σ) (x y : σ) (h : List σ),
      |condE D f k (pre ++ x :: h) - condE D f k (pre ++ y :: h)| ≤ c h.length := by
  intro k
  induction k with
  | zero => intro pre x y h; exact hf pre x y h
  | succ k ih =>
    intro pre x y h
    show |∑ z, D.p z * condE D f k (z :: (pre ++ x :: h))
          - ∑ z, D.p z * condE D f k (z :: (pre ++ y :: h))| ≤ c h.length
    rw [← Finset.sum_sub_distrib]
    calc |∑ z, (D.p z * condE D f k (z :: (pre ++ x :: h))
               - D.p z * condE D f k (z :: (pre ++ y :: h)))|
        ≤ ∑ z, |D.p z * condE D f k (z :: (pre ++ x :: h))
               - D.p z * condE D f k (z :: (pre ++ y :: h))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, D.p z * c h.length := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg (D.nonneg z)]
          exact mul_le_mul_of_nonneg_left (ih (z :: pre) x y h) (D.nonneg z)
      _ = c h.length := by rw [← Finset.sum_mul, D.total, one_mul]

/-! ### 3. 一般区间 Hoeffding(凸性化归到两点引理,常数 1/8) -/

/-- **有限 Hoeffding 引理**:均值为零、取值于 [a,b] 的有限随机变量,
    E[e^{λA}] ≤ e^{λ²(b−a)²/8}。经 exp 凸性把一般分布压到两点端点分布,
    再调用 `Radius.two_point_mgf_le` —— 常数不放松。 -/
lemma sum_exp_le_of_mean_zero (D : Draw σ) (A : σ → ℝ) {a b : ℝ} (lam : ℝ)
    (hab : ∀ x, a ≤ A x ∧ A x ≤ b)
    (hmean : ∑ x, D.p x * A x = 0) :
    ∑ x, D.p x * exp (lam * A x) ≤ exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
  -- a ≤ 0 ≤ b(均值为零挤出符号)
  have ha0 : a ≤ 0 := by
    have h1 : a = ∑ x, D.p x * a := by rw [← Finset.sum_mul, D.total, one_mul]
    have h2 : ∑ x, D.p x * a ≤ ∑ x, D.p x * A x :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hab x).1 (D.nonneg x)
    linarith [hmean ▸ h2, h1]
  have hb0 : 0 ≤ b := by
    have h1 : b = ∑ x, D.p x * b := by rw [← Finset.sum_mul, D.total, one_mul]
    have h2 : ∑ x, D.p x * A x ≤ ∑ x, D.p x * b :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hab x).2 (D.nonneg x)
    linarith [hmean ▸ h2, h1]
  rcases eq_or_lt_of_le (le_trans ha0 hb0 : a ≤ b) with hab' | hab'
  · -- 退化:a = b(与 a ≤ 0 ≤ b 一并给出 a = b = 0,A ≡ 0,两边都是 1)
    have ha : a = 0 := le_antisymm ha0 (hab' ▸ hb0)
    have hb : b = 0 := by rw [← hab', ha]
    have hLHS : ∑ x, D.p x * exp (lam * A x) = 1 := by
      have hA0 : ∀ x, A x = 0 := fun x =>
        le_antisymm (hb ▸ (hab x).2) (ha ▸ (hab x).1)
      calc ∑ x, D.p x * exp (lam * A x) = ∑ x, D.p x := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hA0 x, mul_zero, exp_zero, mul_one]
        _ = 1 := D.total
    rw [hLHS, hb, ha]
    simp
  · -- a < b:凸性 + 两点引理
    have hba : (0:ℝ) < b - a := by linarith
    -- 逐点凸性:e^{λA} ≤ (1−t)e^{λa} + t e^{λb},t = (A−a)/(b−a)
    have hconv : ∀ x, exp (lam * A x)
        ≤ (b - A x) / (b - a) * exp (lam * a) + (A x - a) / (b - a) * exp (lam * b) := by
      intro x
      have hne : b - a ≠ 0 := hba.ne'
      have ht0 : 0 ≤ (A x - a) / (b - a) := div_nonneg (by linarith [(hab x).1]) hba.le
      have ht1 : 0 ≤ (b - A x) / (b - a) := div_nonneg (by linarith [(hab x).2]) hba.le
      have htsum : (b - A x) / (b - a) + (A x - a) / (b - a) = 1 := by
        rw [div_add_div_same, div_eq_one_iff_eq hne]; ring
      have hcx := convexOn_exp.2 (Set.mem_univ (lam * a)) (Set.mem_univ (lam * b))
        ht1 ht0 htsum
      simp only [smul_eq_mul] at hcx
      have harg : (b - A x) / (b - a) * (lam * a) + (A x - a) / (b - a) * (lam * b)
          = lam * A x := by field_simp; ring
      rwa [harg] at hcx
    -- 求和:落到两点分布 (1−q)e^{λa} + q e^{λb},q = −a/(b−a)
    set q : ℝ := -a / (b - a) with hq
    have hsum : ∑ x, D.p x * exp (lam * A x)
        ≤ (1 - q) * exp (lam * a) + q * exp (lam * b) := by
      calc ∑ x, D.p x * exp (lam * A x)
          ≤ ∑ x, D.p x * ((b - A x) / (b - a) * exp (lam * a)
              + (A x - a) / (b - a) * exp (lam * b)) :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (hconv x) (D.nonneg x)
        _ = (∑ x, D.p x * (b - A x)) / (b - a) * exp (lam * a)
              + (∑ x, D.p x * (A x - a)) / (b - a) * exp (lam * b) := by
            rw [Finset.sum_div, Finset.sum_div, Finset.sum_mul, Finset.sum_mul,
                ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = (1 - q) * exp (lam * a) + q * exp (lam * b) := by
            have e1 : ∑ x, D.p x * (b - A x) = b := by
              have : ∑ x, D.p x * (b - A x)
                  = (∑ x, D.p x * b) - ∑ x, D.p x * A x := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun x _ => by ring
              rw [this, hmean, ← Finset.sum_mul, D.total]; ring
            have e2 : ∑ x, D.p x * (A x - a) = -a := by
              have : ∑ x, D.p x * (A x - a)
                  = (∑ x, D.p x * A x) - ∑ x, D.p x * a := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun x _ => by ring
              rw [this, hmean, ← Finset.sum_mul, D.total]; ring
            rw [e1, e2, hq]
            have : 1 - -a / (b - a) = b / (b - a) := by field_simp
            rw [this]
    -- 两点引理(p := q, h := λ(b−a))
    have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (by linarith) hba.le
    have hq1 : q ≤ 1 := by
      rw [hq, div_le_one hba]; linarith
    have h2p := WitCert.Calculus.Radius.two_point_mgf_le hq0 hq1 (lam * (b - a))
    have ea : -(q * (lam * (b - a))) = lam * a := by
      rw [hq]; field_simp; ring
    have eb : (1 - q) * (lam * (b - a)) = lam * b := by
      rw [hq]; field_simp; ring
    have eexp : (lam * (b - a)) ^ 2 / 8 = lam ^ 2 * (b - a) ^ 2 / 8 := by ring
    rw [ea, eb, eexp] at h2p
    linarith [hsum, h2p]

/-! ### 4. Doob 结构的 MGF 归纳(Azuma–Hoeffding) -/

/-- **MGF 主归纳**:f 逐坐标 bounded difference ⟹
    E[e^{λf} | h] ≤ exp(λ·E[f|h] + λ²·Σ 剩余坐标 c²/8)。 -/
lemma condE_exp_le (D : Draw σ) {f : List σ → ℝ} {c : ℕ → ℝ}
    (hf : BddDiffAt f c) (lam : ℝ) :
    ∀ k (h : List σ),
      condE D (fun ω => exp (lam * f ω)) k h
        ≤ exp (lam * condE D f k h
            + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + i) ^ 2) / 8) := by
  intro k
  induction k with
  | zero =>
    intro h
    simp [condE]
  | succ k ih =>
    intro h
    -- 每支先用 IH,再对本步增量 A_x 用区间 Hoeffding
    set m : ℝ := condE D f (k + 1) h with hm
    set A : σ → ℝ := fun x => condE D f k (x :: h) - m with hA
    have hAmean : ∑ x, D.p x * A x = 0 := by
      have : ∑ x, D.p x * A x = (∑ x, D.p x * condE D f k (x :: h)) - m := by
        rw [hA]
        have : ∑ x, D.p x * (condE D f k (x :: h) - m)
            = (∑ x, D.p x * condE D f k (x :: h)) - ∑ x, D.p x * m := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
        rw [this, ← Finset.sum_mul, D.total, one_mul]
      rw [this, hm]
      show (condE D f (k + 1) h) - condE D f (k + 1) h = 0
      ring
    -- A 的区间:以任一参考点 x₀ 为中心,宽 ≤ c h.length
    obtain ⟨x0⟩ := ‹Nonempty σ›
    set aA : ℝ := Finset.univ.inf' Finset.univ_nonempty A with haA
    set bA : ℝ := Finset.univ.sup' Finset.univ_nonempty A with hbA
    have hbounds : ∀ x, aA ≤ A x ∧ A x ≤ bA := fun x =>
      ⟨Finset.inf'_le _ (Finset.mem_univ x), Finset.le_sup' _ (Finset.mem_univ x)⟩
    have hwidth : bA - aA ≤ c h.length := by
      obtain ⟨xm, _, hxm⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty A
      obtain ⟨xn, _, hxn⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty A
      have hd := condE_bdd_diff D hf k [] xm xn h
      simp only [List.nil_append] at hd
      have hdiff : A xm - A xn = condE D f k (xm :: h) - condE D f k (xn :: h) := by
        simp only [hA]; ring
      have habs : A xm - A xn ≤ c h.length := by
        rw [hdiff]
        exact le_trans (le_abs_self _) hd
      have e1 : bA = A xm := by rw [hbA, hxm]
      have e2 : aA = A xn := by rw [haA, hxn]
      rw [e1, e2]
      exact habs
    have hstep : ∑ x, D.p x * exp (lam * A x)
        ≤ exp (lam ^ 2 * c h.length ^ 2 / 8) := by
      have h1 := sum_exp_le_of_mean_zero D A lam hbounds hAmean
      have h2 : lam ^ 2 * (bA - aA) ^ 2 / 8 ≤ lam ^ 2 * c h.length ^ 2 / 8 := by
        have hw0 : 0 ≤ bA - aA := by
          have := hbounds x0; linarith [this.1, this.2]
        have : (bA - aA) ^ 2 ≤ c h.length ^ 2 := by
          have hc0 := hf.c_nonneg h.length
          nlinarith
        nlinarith [sq_nonneg lam]
      exact le_trans h1 (exp_le_exp.mpr h2)
    -- 组装
    show ∑ x, D.p x * condE D (fun ω => exp (lam * f ω)) k (x :: h) ≤ _
    have hlen : ∀ x : σ, (x :: h : List σ).length = h.length + 1 := fun x => rfl
    calc ∑ x, D.p x * condE D (fun ω => exp (lam * f ω)) k (x :: h)
        ≤ ∑ x, D.p x * exp (lam * condE D f k (x :: h)
            + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8) := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (D.nonneg x)
          have := ih (x :: h)
          simpa [hlen x] using this
      _ = ∑ x, D.p x * (exp (lam * m
            + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8)
            * exp (lam * A x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← exp_add]
          have harg : lam * condE D f k (x :: h)
              + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8
              = lam * m + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8
              + lam * A x := by
            simp only [hA]; ring
          rw [harg]
      _ = exp (lam * m + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8)
            * ∑ x, D.p x * exp (lam * A x) := by
          conv_rhs => rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ exp (lam * m + lam ^ 2 * (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) / 8)
            * exp (lam ^ 2 * c h.length ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hstep (exp_pos _).le
      _ = exp (lam * m
            + lam ^ 2 * (∑ i ∈ Finset.range (k + 1), c (h.length + i) ^ 2) / 8) := by
          rw [← exp_add]
          congr 1
          have hsplit : ∑ i ∈ Finset.range (k + 1), c (h.length + i) ^ 2
              = (∑ i ∈ Finset.range k, c (h.length + 1 + i) ^ 2) + c h.length ^ 2 := by
            rw [Finset.sum_range_succ' (fun i => c (h.length + i) ^ 2) k]
            simp only [Nat.add_zero]
            have hcong : ∀ i ∈ Finset.range k,
                c (h.length + (i + 1)) ^ 2 = c (h.length + 1 + i) ^ 2 := fun i _ => by
              have hi : h.length + (i + 1) = h.length + 1 + i := by omega
              rw [hi]
            rw [Finset.sum_congr rfl hcong]
          rw [hsplit]; ring

/-! ### 5. Chernoff 收口:McDiarmid 尾界与实现同形的半径 -/

/-- 事件概率 = 指示函数的条件期望(有限乘积空间;定义即计算)。 -/
noncomputable def probE (D : Draw σ) (E : List σ → Prop) (k : ℕ) (h : List σ) : ℝ :=
  condE D (fun ω => if E ω then (1:ℝ) else 0) k h

/-- **有限 Ω McDiarmid**:逐坐标 bounded difference c,则
    P(f ≥ E[f] + t) ≤ exp(−2t²/Σc²)。 -/
theorem mcdiarmid (D : Draw σ) {f : List σ → ℝ} {c : ℕ → ℝ}
    (hf : BddDiffAt f c) (T : ℕ) {t : ℝ} (ht : 0 < t)
    (hC : 0 < ∑ i ∈ Finset.range T, c i ^ 2) :
    probE D (fun ω => condE D f T [] + t ≤ f ω) T []
      ≤ exp (-2 * t ^ 2 / ∑ i ∈ Finset.range T, c i ^ 2) := by
  set C : ℝ := ∑ i ∈ Finset.range T, c i ^ 2 with hCdef
  set lam : ℝ := 4 * t / C with hlam
  have hlam0 : 0 ≤ lam := by
    rw [hlam]; positivity
  set m : ℝ := condE D f T [] with hm
  -- Markov:指示 ≤ e^{λ(f − (m+t))}
  have hpt : ∀ ω, (if m + t ≤ f ω then (1:ℝ) else 0)
      ≤ exp (-(lam * (m + t))) * exp (lam * f ω) := by
    intro ω
    rw [← exp_add]
    by_cases hω : m + t ≤ f ω
    · simp only [hω, if_true]
      have : 0 ≤ -(lam * (m + t)) + lam * f ω := by nlinarith
      exact Real.one_le_exp this
    · simp only [hω, if_false]
      exact (exp_pos _).le
  have h1 : probE D (fun ω => m + t ≤ f ω) T []
      ≤ exp (-(lam * (m + t))) * condE D (fun ω => exp (lam * f ω)) T [] := by
    have := condE_mono D hpt T []
    calc probE D (fun ω => m + t ≤ f ω) T []
        ≤ condE D (fun ω => exp (-(lam * (m + t))) * exp (lam * f ω)) T [] := this
      _ = exp (-(lam * (m + t))) * condE D (fun ω => exp (lam * f ω)) T [] :=
          condE_const_mul D _ _ T []
  have h2 : condE D (fun ω => exp (lam * f ω)) T []
      ≤ exp (lam * m + lam ^ 2 * C / 8) := by
    have := condE_exp_le D hf lam T []
    simpa [hCdef, hm] using this
  have h3 : probE D (fun ω => m + t ≤ f ω) T []
      ≤ exp (-(lam * (m + t)) + (lam * m + lam ^ 2 * C / 8)) := by
    rw [exp_add]
    calc probE D (fun ω => m + t ≤ f ω) T []
        ≤ exp (-(lam * (m + t))) * condE D (fun ω => exp (lam * f ω)) T [] := h1
      _ ≤ exp (-(lam * (m + t))) * exp (lam * m + lam ^ 2 * C / 8) :=
          mul_le_mul_of_nonneg_left h2 (exp_pos _).le
  have hexp : -(lam * (m + t)) + (lam * m + lam ^ 2 * C / 8) = -2 * t ^ 2 / C := by
    rw [hlam]
    field_simp
    ring
  rw [hexp] at h3
  exact h3

/-- **与实现同形的半径**:tail = √(2·(Σc²/4)·ln(1/δ)),则
    P(f ≥ E[f] + tail) ≤ δ —— 即 dsv4_certified_write 尾项的形式对应
    (实现取 δ := δ_i/n 完成 n 条目 union)。 -/
theorem mcdiarmid_radius (D : Draw σ) {f : List σ → ℝ} {c : ℕ → ℝ}
    (hf : BddDiffAt f c) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hC : 0 < ∑ i ∈ Finset.range T, c i ^ 2) :
    probE D (fun ω => condE D f T []
        + Real.sqrt (2 * ((∑ i ∈ Finset.range T, c i ^ 2) / 4) * Real.log (1 / δ))
      ≤ f ω) T [] ≤ δ := by
  set C : ℝ := ∑ i ∈ Finset.range T, c i ^ 2 with hCdef
  set t : ℝ := Real.sqrt (2 * (C / 4) * Real.log (1 / δ)) with htdef
  have hlog : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]; linarith
  have ht : 0 < t := by
    rw [htdef]
    apply Real.sqrt_pos.mpr
    positivity
  have hmc := mcdiarmid D hf T ht hC
  have ht2 : t ^ 2 = C * Real.log (1 / δ) / 2 := by
    rw [htdef, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (C / 4) * Real.log (1 / δ))]
    ring
  have hexp : -2 * t ^ 2 / C = -Real.log (1 / δ) := by
    rw [ht2]; field_simp; ring
  have : exp (-2 * t ^ 2 / C) = δ := by
    rw [hexp, Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 1 / δ)]
    field_simp
  exact this ▸ hmc

/-! ### 6. 均值项:可加坐标函数 + 递归 Jensen —— E[W] ≤ Σ_b √(Σ Var) 全链闭合 -/

lemma condE_add (D : Draw σ) (f g : List σ → ℝ) :
    ∀ k h, condE D (fun ω => f ω + g ω) k h = condE D f k h + condE D g k h := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih =>
    intro h
    show ∑ x, D.p x * condE D (fun ω => f ω + g ω) k (x :: h)
        = (∑ x, D.p x * condE D f k (x :: h)) + ∑ x, D.p x * condE D g k (x :: h)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [ih (x :: h)]; ring

lemma condE_nonneg (D : Draw σ) {f : List σ → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    ∀ k h, 0 ≤ condE D f k h := by
  intro k
  induction k with
  | zero => intro h; exact hf h
  | succ k ih =>
    intro h
    exact Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (ih (x :: h))

lemma condE_congr (D : Draw σ) {f g : List σ → ℝ} (hfg : ∀ ω, f ω = g ω) :
    ∀ k h, condE D f k h = condE D g k h := by
  have : f = g := funext hfg
  intro k h; rw [this]

/-- 有限带集上的线性:E[Σ_b F_b] = Σ_b E[F_b]。 -/
lemma condE_finset_sum {β : Type*} (D : Draw σ) (s : Finset β)
    (F : β → List σ → ℝ) (k : ℕ) (h : List σ) :
    condE D (fun ω => ∑ b ∈ s, F b ω) k h = ∑ b ∈ s, condE D (F b) k h := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    have : condE D (fun _ => (0:ℝ)) k h = 0 := by
      have h0 : ∀ ω : List σ, (0:ℝ) ≤ 0 := fun _ => le_rfl
      have hle : condE D (fun _ => (0:ℝ)) k h ≤ condE D (fun _ => (0:ℝ)) k h := le_rfl
      -- 0 = 0·condE 0:由 const_mul 以 r = 0 直接给出
      have := condE_const_mul D 0 (fun _ => (0:ℝ)) k h
      simpa using this
    exact this
  | cons b s hb ih =>
    have hpt : ∀ ω : List σ, ∑ b' ∈ Finset.cons b s hb, F b' ω
        = F b ω + ∑ b' ∈ s, F b' ω := fun ω => Finset.sum_cons hb
    calc condE D (fun ω => ∑ b' ∈ Finset.cons b s hb, F b' ω) k h
        = condE D (fun ω => F b ω + ∑ b' ∈ s, F b' ω) k h := condE_congr D hpt k h
      _ = condE D (F b) k h + condE D (fun ω => ∑ b' ∈ s, F b' ω) k h :=
          condE_add D _ _ k h
      _ = condE D (F b) k h + ∑ b' ∈ s, condE D (F b') k h := by rw [ih]
      _ = ∑ b' ∈ Finset.cons b s hb, condE D (F b') k h := by rw [Finset.sum_cons]

/-- **可加坐标函数**(深度索引):addF v (x :: h) = v h.length x + addF v h。
    band 内平方残差和 ‖d_b‖² = Σ_c X_c² 即此形(逐坐标平方的和,**无交叉项**)。 -/
def addF (v : ℕ → σ → ℝ) : List σ → ℝ
  | [] => 0
  | x :: h => v h.length x + addF v h

lemma addF_nonneg {v : ℕ → σ → ℝ} (hv : ∀ j x, 0 ≤ v j x) :
    ∀ ω, 0 ≤ addF v ω := by
  intro ω
  induction ω with
  | nil => exact le_rfl
  | cons x h ih => exact add_nonneg (hv h.length x) ih

/-- **线性**:E[addF | h] = addF h + Σ 未来坐标的单步均值(与历史无关 —— 独立性
    在乘积结构里的化身)。 -/
lemma condE_addF (D : Draw σ) (v : ℕ → σ → ℝ) :
    ∀ k h, condE D (addF v) k h
      = addF v h + ∑ i ∈ Finset.range k, ∑ x, D.p x * v (h.length + i) x := by
  intro k
  induction k with
  | zero => intro h; simp [condE]
  | succ k ih =>
    intro h
    show ∑ x, D.p x * condE D (addF v) k (x :: h) = _
    have hstep : ∀ x : σ, condE D (addF v) k (x :: h)
        = v h.length x + addF v h
          + ∑ i ∈ Finset.range k, ∑ z, D.p z * v (h.length + 1 + i) z := by
      intro x
      have := ih (x :: h)
      have hlen : (x :: h : List σ).length = h.length + 1 := rfl
      rw [this]
      show addF v (x :: h) + _ = _
      have haddF : addF v (x :: h) = v h.length x + addF v h := rfl
      rw [haddF, hlen]
    calc ∑ x, D.p x * condE D (addF v) k (x :: h)
        = ∑ x, (D.p x * v h.length x
            + D.p x * (addF v h
              + ∑ i ∈ Finset.range k, ∑ z, D.p z * v (h.length + 1 + i) z)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hstep x]; ring
      _ = (∑ x, D.p x * v h.length x)
            + (addF v h + ∑ i ∈ Finset.range k, ∑ z, D.p z * v (h.length + 1 + i) z) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, D.total, one_mul]
      _ = addF v h + ∑ i ∈ Finset.range (k + 1), ∑ x, D.p x * v (h.length + i) x := by
          have hsplit : ∑ i ∈ Finset.range (k + 1), ∑ x, D.p x * v (h.length + i) x
              = (∑ i ∈ Finset.range k, ∑ x, D.p x * v (h.length + 1 + i) x)
                + ∑ x, D.p x * v h.length x := by
            rw [Finset.sum_range_succ' (fun i => ∑ x, D.p x * v (h.length + i) x) k]
            simp only [Nat.add_zero]
            have hcong : ∀ i ∈ Finset.range k,
                (∑ x, D.p x * v (h.length + (i + 1)) x)
                  = ∑ x, D.p x * v (h.length + 1 + i) x := fun i _ => by
              have hi : h.length + (i + 1) = h.length + 1 + i := by omega
              rw [hi]
            rw [Finset.sum_congr rfl hcong]
          rw [hsplit]; ring

/-- **递归 Jensen**:(E[f|h])² ≤ E[f²|h](逐步用加权 Cauchy–Schwarz)。 -/
lemma condE_sq_le (D : Draw σ) (f : List σ → ℝ) :
    ∀ k h, (condE D f k h) ^ 2 ≤ condE D (fun ω => f ω ^ 2) k h := by
  intro k
  induction k with
  | zero => intro h; exact le_rfl
  | succ k ih =>
    intro h
    show (∑ x, D.p x * condE D f k (x :: h)) ^ 2
        ≤ ∑ x, D.p x * condE D (fun ω => f ω ^ 2) k (x :: h)
    calc (∑ x, D.p x * condE D f k (x :: h)) ^ 2
        ≤ ∑ x, D.p x * (condE D f k (x :: h)) ^ 2 :=
          WitCert.Calculus.Radius.sq_sum_weighted_le Finset.univ D.p _
            (fun x _ => D.nonneg x) D.total
      _ ≤ ∑ x, D.p x * condE D (fun ω => f ω ^ 2) k (x :: h) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (ih (x :: h)) (D.nonneg x)

/-- **单带均值项**:E[√(Σ_c X_c²)] ≤ √(Σ_c E[X_c²]) —— 实现中
    mean_bound 的 band 内形式(v j x = 该坐标残差平方;两点情形
    E[X²] = θ(1−θ)Δ²,见 Radius.two_point_variance)。 -/
theorem band_mean_le (D : Draw σ) (v : ℕ → σ → ℝ) (hv : ∀ j x, 0 ≤ v j x) (T : ℕ) :
    condE D (fun ω => Real.sqrt (addF v ω)) T []
      ≤ Real.sqrt (∑ i ∈ Finset.range T, ∑ x, D.p x * v i x) := by
  have hY : ∀ ω, Real.sqrt (addF v ω) ^ 2 = addF v ω := fun ω =>
    Real.sq_sqrt (addF_nonneg hv ω)
  have h1 : (condE D (fun ω => Real.sqrt (addF v ω)) T []) ^ 2
      ≤ condE D (addF v) T [] := by
    have := condE_sq_le D (fun ω => Real.sqrt (addF v ω)) T []
    have heq := condE_congr D (f := fun ω => Real.sqrt (addF v ω) ^ 2)
      (g := addF v) hY T []
    linarith [heq ▸ this]
  have h2 : condE D (addF v) T []
      = ∑ i ∈ Finset.range T, ∑ x, D.p x * v i x := by
    have h := condE_addF D v T []
    rw [show addF v [] = (0:ℝ) from rfl, zero_add] at h
    simpa using h
  have h3 : 0 ≤ condE D (fun ω => Real.sqrt (addF v ω)) T [] :=
    condE_nonneg D (fun ω => Real.sqrt_nonneg _) T []
  have hS : 0 ≤ ∑ i ∈ Finset.range T, ∑ x, D.p x * v i x := by
    rw [← h2]
    exact condE_nonneg D (addF_nonneg hv) T []
  rw [Real.le_sqrt h3 hS]
  rw [← h2]
  exact h1

/-- **多带均值项**(与实现同形):E[Σ_b √(Σ_{c∈b} X_c²)] ≤ Σ_b √(Σ_{c∈b} E X_c²)
    —— dsv4_certified_write 的 mean_bound = Σ_b √(Σ θ(1−θ)Δ²) 的形式对应。 -/
theorem witness_mean_le {β : Type*} (D : Draw σ) (s : Finset β)
    (V : β → ℕ → σ → ℝ) (hV : ∀ b j x, 0 ≤ V b j x) (T : ℕ) :
    condE D (fun ω => ∑ b ∈ s, Real.sqrt (addF (V b) ω)) T []
      ≤ ∑ b ∈ s, Real.sqrt (∑ i ∈ Finset.range T, ∑ x, D.p x * V b i x) := by
  rw [condE_finset_sum]
  exact Finset.sum_le_sum fun b _ => band_mean_le D (V b) (hV b) T

/-! ### 7. e-process 因子(F4:接通 Ville —— 同对象任意时刻模型校验) -/

/-- **e-process 因子的合法性**:λ ≥ 0、先验均值项 m ≥ E[f|h] 时,
    g = exp(λ(f − m) − λ²·Σc²/8) 满足 E[g|h] ≤ 1 —— 恰为
    `Ville.eprocess_ville` 要求的单步条件;因子乘积对**同一对象**
    (实现残差见证 W 对其先验均值项)给出任意时刻有效的模型校验:
    P(∃t: Π g ≥ 1/δ) ≤ δ,越阈即半径假设(R3-SR)被数据否证。 -/
theorem eprocess_factor_mean_le_one (D : Draw σ) {f : List σ → ℝ} {c : ℕ → ℝ}
    (hf : BddDiffAt f c) {lam m : ℝ} (hlam : 0 ≤ lam) (T : ℕ) (h : List σ)
    (hm : condE D f T h ≤ m) :
    condE D (fun ω => exp (lam * f ω - (lam * m
        + lam ^ 2 * (∑ i ∈ Finset.range T, c (h.length + i) ^ 2) / 8))) T h ≤ 1 := by
  set K : ℝ := lam * m + lam ^ 2 * (∑ i ∈ Finset.range T, c (h.length + i) ^ 2) / 8
    with hK
  have hpt : ∀ ω : List σ, exp (lam * f ω - K) = exp (-K) * exp (lam * f ω) := fun ω => by
    rw [← exp_add]; congr 1; ring
  have h1 : condE D (fun ω => exp (lam * f ω - K)) T h
      = exp (-K) * condE D (fun ω => exp (lam * f ω)) T h := by
    rw [condE_congr D hpt T h]
    exact condE_const_mul D _ _ T h
  have h2 := condE_exp_le D hf lam T h
  have h3 : condE D (fun ω => exp (lam * f ω)) T h ≤ exp K := by
    refine le_trans h2 (exp_le_exp.mpr ?_)
    rw [hK]
    have := mul_le_mul_of_nonneg_left hm hlam
    linarith
  rw [h1]
  calc exp (-K) * condE D (fun ω => exp (lam * f ω)) T h
      ≤ exp (-K) * exp K := mul_le_mul_of_nonneg_left h3 (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp

end WitCert.Calculus.McDiarmid
