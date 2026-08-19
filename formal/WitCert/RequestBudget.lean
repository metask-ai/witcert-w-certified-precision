/-
  WitCert 形式化 · L3:逐 token 联合 + 请求级 union budget

  证书的失败概率预算按 (层 × 头 × 解码步) 均分:δ_loc = δ_req / (L·H·T),
  每个 (层,头,步) 内再对 S 个历史 token 做联合(体现在 log(2S/δ_loc) 中)。
  本文件形式化该预算分配的 soundness:所有局部事件的并集概率不超过 δ_req。
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic

open MeasureTheory ENNReal

namespace WitCert

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/--
  **请求级预算定理**:若 n 个局部违约事件各自概率 ≤ δ_loc,且 n · δ_loc ≤ δ_req,
  则「至少一个局部事件发生」的概率 ≤ δ_req。

  工程含义:L·H·T 个 (层,头,步) 的证书各自以 1−δ_loc 成立 ⟹ 整个请求以 1−δ_req 成立。
-/
theorem request_budget_sound
    {n : ℕ} (E : Fin n → Set Ω)
    (δloc δreq : ℝ≥0∞) (hδ : ∀ i, μ (E i) ≤ δloc)
    (hbudget : (n : ℕ) * δloc ≤ δreq) :
    μ (⋃ i, E i) ≤ δreq := by
  -- 联合界(测度论)+ 预算算术(见 standalone/Budget.lean 的零依赖版本)
  refine le_trans (measure_iUnion_fintype_le μ E) (le_trans ?_ hbudget)
  calc ∑ i, μ (E i) ≤ ∑ _i : Fin n, δloc := Finset.sum_le_sum (fun i _ => hδ i)
    _ = (n : ℕ) * δloc := by simp [Finset.sum_const, nsmul_eq_mul]

/-- 局部预算的具体分配:δ_loc = δ_req / (L·H·T)。 -/
noncomputable def deltaLocal (δreq : ℝ) (L H T : ℕ) : ℝ := δreq / (L * H * T)

theorem deltaLocal_budget (δreq : ℝ) (L H T : ℕ) (h : 0 < L * H * T) :
    ((L * H * T : ℕ) : ℝ) * deltaLocal δreq L H T = δreq := by
  unfold deltaLocal
  have hne : ((L : ℝ) * H * T) ≠ 0 := by
    have : (0 : ℝ) < (L : ℝ) * H * T := by
      exact_mod_cast (by exact_mod_cast h : (0 : ℕ) < L * H * T)
    exact ne_of_gt this
  push_cast
  field_simp
