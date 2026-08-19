/-
  WitCert 形式化 · L11:**共享条目读取的风险语义**(H3,八审)

  场景:前缀缓存/并发下,同一个写入事件产出的条目会被**多个请求**读取。
  问题:风险预算会不会随读者数放大?

  答案由 fail-closed refinement 的四条运行时义务钉死(extract 已实现):
    W1 写后审计在同一 hook 调用内完成,先于任何共享读取;
    W2 违约条目当场**恢复原字节**(槽位状态 3 = restored-exact),
       served 误差 ≤ 声明界因此是确定性恒成立,不再是概率命题;
    W3 任何读取的失败都可归因到其**来源写事件**的 BAD(W_e 超预授半径);
    W4 同一写事件不可变:多个读者读到同一份字节。

  本文件给出与之对应的定理:读者集合**任意大**时,
      P(任一读取 served 值越界) ≤ Σ_{写事件} δ_e
  —— union bound 落在写事件上,与读者数无关。δ 每写事件记一次的实现
  (cwrite_by_rid 按 owner 记账)即此语义。
-/
import WitCert.McDiarmid

open scoped Classical

namespace WitCert.Calculus.SharedRead

open WitCert.Calculus.Ville WitCert.Calculus.McDiarmid

variable {σ : Type*} [Fintype σ] [Nonempty σ]

/-- 事件的指示函数逐点被并集成员的指示函数和控制。
    (ite 的 Decidable 实例显式取 Classical —— 与 probE 定义处一致,
    避免 Finset 派生实例导致的 defeq 失配。) -/
private lemma indicator_exists_le_sum {ι : Type*} (s : Finset ι)
    (B : ι → List σ → Prop) (ω : List σ) :
    (@ite ℝ (∃ e ∈ s, B e ω) (Classical.propDecidable _) 1 0)
      ≤ ∑ e ∈ s, (@ite ℝ (B e ω) (Classical.propDecidable _) 1 0) := by
  by_cases hex : ∃ e ∈ s, B e ω
  · obtain ⟨e0, he0, hB0⟩ := hex
    have hsum := Finset.single_le_sum
      (f := fun e => @ite ℝ (B e ω) (Classical.propDecidable _) 1 0)
      (fun e _ => by by_cases hbe : B e ω <;> simp [hbe]) he0
    simp only [hB0, if_true] at hsum
    have hx : ∃ e ∈ s, B e ω := ⟨e0, he0, hB0⟩
    simpa [hx] using hsum
  · simp only [hex, if_false]
    exact Finset.sum_nonneg fun e _ => by by_cases hbe : B e ω <;> simp [hbe]

/-- **有限 union bound**(递归概率 probE 的次可加性)。 -/
theorem probE_union_le {ι : Type*} (D : Draw σ) (T : ℕ) (h : List σ)
    (s : Finset ι) (B : ι → List σ → Prop) (δ : ι → ℝ)
    (hB : ∀ e ∈ s, probE D (B e) T h ≤ δ e) :
    probE D (fun ω => ∃ e ∈ s, B e ω) T h ≤ ∑ e ∈ s, δ e := by
  unfold probE at hB ⊢
  have h1 := condE_mono D (indicator_exists_le_sum s B) T h
  have h2 := condE_finset_sum D s
    (fun e ω => @ite ℝ (B e ω) (Classical.propDecidable _) 1 0) T h
  exact le_trans (h2 ▸ h1) (Finset.sum_le_sum hB)

/-- probE 对事件蕴含单调。 -/
theorem probE_mono_event (D : Draw σ) (T : ℕ) (h : List σ)
    {E F : List σ → Prop} (himp : ∀ ω, E ω → F ω) :
    probE D E T h ≤ probE D F T h := by
  unfold probE
  refine condE_mono D (fun ω => ?_) T h
  by_cases hE : E ω
  · simp [hE, himp ω hE]
  · by_cases hF : F ω <;> simp [hE, hF]

/--
  **共享读 soundness**:读者集合任意大,风险只按**写事件**计。

  前提对应运行时义务:
    · `hsrc`:每次读取有唯一来源写事件(W4 不可变);
    · `hlink`:读取失败 ⟹ 来源写事件 BAD(W1+W2 的 fail-closed 归因);
    · `hδ`:每个写事件的 BAD 概率 ≤ δ_e(McDiarmid 半径 + 预授权语义)。

  结论中的和只跑写事件 —— 与 |reads| 无关:同一条目被多少请求共享读取,
  δ 都不重复消费。这就是"写侧 δ 由 owner 承担,读侧检查确定性"的形式面。
-/
theorem shared_read_sound {ι ρ : Type*} (D : Draw σ) (T : ℕ) (h : List σ)
    (writes : Finset ι) (reads : Finset ρ) (src : ρ → ι)
    (RFail : ρ → List σ → Prop) (BAD : ι → List σ → Prop) (δ : ι → ℝ)
    (hsrc : ∀ r ∈ reads, src r ∈ writes)
    (hlink : ∀ r ∈ reads, ∀ ω, RFail r ω → BAD (src r) ω)
    (hδ : ∀ e ∈ writes, probE D (BAD e) T h ≤ δ e) :
    probE D (fun ω => ∃ r ∈ reads, RFail r ω) T h ≤ ∑ e ∈ writes, δ e := by
  have himp : ∀ ω, (∃ r ∈ reads, RFail r ω) → (∃ e ∈ writes, BAD e ω) := by
    intro ω ⟨r, hr, hf⟩
    exact ⟨src r, hsrc r hr, hlink r hr ω hf⟩
  calc probE D (fun ω => ∃ r ∈ reads, RFail r ω) T h
      ≤ probE D (fun ω => ∃ e ∈ writes, BAD e ω) T h :=
        probE_mono_event D T h himp
    _ ≤ ∑ e ∈ writes, δ e := probE_union_le D T h writes BAD δ hδ

end WitCert.Calculus.SharedRead
