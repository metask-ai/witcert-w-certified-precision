/-
  WitCert 形式化 · L4:proof–kernel refinement 定理

  这是防止「M3 事故」再次发生的核心定理。2026-07-27 的事故是:kernel 为了省一次矩阵乘,
  把逐 token 的 A = Σ_t p̃_t · e^{u_t} 替换成了「先平均方差再开根」的 ½(e^{2u(V̄)}−1),
  两者在方差异质时并不相等,且后者不 sound(反例见 tests/test_certificates.py::T6)。

  本文件证明:**当 u 在块内为常数时**(WitCert 的 scale 逐块 + tile 整除块保证了这一点),
  分块累加器与逐 token 求和**恒等**。于是 kernel 的优化是 refinement 而非替换。

  这个定理只需有限和的代数,不依赖概率论,故可先于其余部分机器检查。
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open BigOperators

namespace WitCert

variable {ι β : Type*} [Fintype ι] [DecidableEq β]

/-- 逐 token 形式:A = Σ_t p̃ t * e^{u t}(此处 `e` 抽象为任意函数 `w`,避免依赖 Real.exp)。 -/
def A_perToken (p w : ι → ℝ) : ℝ := ∑ t, p t * w t

/-- 分块形式:A = Σ_b w_b * (Σ_{t ∈ b} p̃ t),即 kernel 实际计算的累加器。 -/
noncomputable def A_blockwise (p : ι → ℝ) (blk : ι → β) (wB : β → ℝ) (B : Finset β) : ℝ :=
  ∑ b ∈ B, wB b * (∑ t ∈ Finset.univ.filter (fun t => blk t = b), p t)

/--
  **Refinement 定理**:若权重在块内恒定(`w t = wB (blk t)`),且块集合 `B` 覆盖全部 token,
  则分块累加器与逐 token 求和恒等。

  对应工程含义:kernel 里 `a_num += e^{u_b} * rowsum(p)` 与规格里 `A = Σ_t p̃_t e^{u_t}`
  计算的是同一个数——优化不改变被证明的数学对象。
-/
theorem A_blockwise_eq_perToken
    (p : ι → ℝ) (blk : ι → β) (wB : β → ℝ) (B : Finset β)
    (hcover : ∀ t : ι, blk t ∈ B) :
    A_blockwise p blk wB B = A_perToken p (fun t => wB (blk t)) := by
  unfold A_blockwise A_perToken
  have key : ∀ b ∈ B, wB b * (∑ t ∈ Finset.univ.filter (fun t => blk t = b), p t)
      = ∑ t ∈ Finset.univ.filter (fun t => blk t = b), p t * wB (blk t) := by
    intro b _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hb : blk t = b := (Finset.mem_filter.mp ht).2
    rw [hb, mul_comm]
  rw [Finset.sum_congr rfl key]
  exact Finset.sum_fiberwise_of_maps_to (fun t _ => hcover t) (fun t => p t * wB (blk t))

-- 反面命题(块内权重变化时恒等式失效)的离散骨架见 standalone/Refinement.lean,
-- 该文件零依赖且已机器检查,此处不重复。

end WitCert
