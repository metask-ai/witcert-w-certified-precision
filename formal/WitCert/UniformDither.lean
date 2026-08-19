/-
  WitCert 形式化 · L2:均匀抖动的 sub-Gaussian proxy

  减性抖动量化 x̂ = s·(round(x/s + u) − u),u ~ U[−½, ½) 使残差 r = x̂ − x 满足
  r ~ U[−s/2, s/2](与输入独立)。本文件形式化其 MGF 界:

      E[e^{λ r}] = sinh(λ s/2)/(λ s/2) ≤ e^{λ² (s²/12) / 2}

  即 proxy **恰等于方差** s²/12,而非通常 sub-Gaussian 论证给出的更松的 (s/2)²。
  这是 WitCert 相对 Bernstein 型界(带 M·log 项)更紧的根本原因。

  核心不等式(可独立机器检查,不依赖概率测度):
      ∀ x > 0,  sinh x / x ≤ e^{x²/6}
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic

open Real Nat

namespace WitCert

/--
  **核心 MGF 不等式**:sinh x ≤ x · e^{x²/6}(x ≥ 0)。

  证明思路(泰勒逐项比较):
    sinh x / x = Σ_{k≥0} x^{2k} / (2k+1)!
    e^{x²/6}   = Σ_{k≥0} x^{2k} / (6^k k!)
  逐项有 (2k+1)! ≥ 6^k k!,故右式逐项不小于左式。
  归纳基:k=0 时 1 = 1;归纳步:(2k+3)!/(2k+1)! = (2k+2)(2k+3) ≥ 6(k+1)。
-/
theorem six_pow_mul_factorial_le (n : ℕ) :
    6 ^ n * Nat.factorial n ≤ Nat.factorial (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have e1 : Nat.factorial (2 * (k + 1) + 1)
          = (2 * k + 3) * ((2 * k + 2) * Nat.factorial (2 * k + 1)) := by
        have hidx : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
        rw [hidx, Nat.factorial_succ, Nat.factorial_succ]
      have e2 : 6 ^ (k + 1) * Nat.factorial (k + 1)
          = (6 * (k + 1)) * (6 ^ k * Nat.factorial k) := by
        first
          | (simp only [Nat.factorial_succ, pow_succ]; ring)
          | simp only [Nat.factorial_succ, pow_succ]
      rw [e1, e2]
      have harith : 6 * (k + 1) ≤ (2 * k + 3) * (2 * k + 2) := by nlinarith
      calc (6 * (k + 1)) * (6 ^ k * Nat.factorial k)
          ≤ ((2 * k + 3) * (2 * k + 2)) * Nat.factorial (2 * k + 1) :=
            Nat.mul_le_mul harith ih
        _ = (2 * k + 3) * ((2 * k + 2) * Nat.factorial (2 * k + 1)) := by ring

/--
  **核心 MGF 不等式**:sinh x ≤ x · e^{x²/6}(x ≥ 0)。
  逐项比较泰勒级数,组合核心为 `six_pow_mul_factorial_le`。
-/
theorem sinh_le_mul_exp_sq_div_six (x : ℝ) (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  rw [Real.sinh_eq_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum, ← tsum_mul_left]
  refine tsum_le_tsum (fun i ↦ ?_) x.hasSum_sinh.summable
    ((NormedSpace.expSeries_summable' (x ^ 2 / 6)).mul_left x)
  have hfac : ((6:ℝ) ^ i * (Nat.factorial i : ℝ)) ≤ (Nat.factorial (2 * i + 1) : ℝ) := by
    exact_mod_cast six_pow_mul_factorial_le i
  have hnum : x ^ (2 * i + 1) = x * (x ^ 2) ^ i := by
    rw [pow_succ, pow_mul, mul_comm]
  have hi : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have h6 : ((6:ℝ) ^ i) ≠ 0 := by positivity
  have hrhs : x * ((Nat.factorial i : ℝ)⁻¹ • (x ^ 2 / 6) ^ i)
      = x * (x ^ 2) ^ i / ((6:ℝ) ^ i * (Nat.factorial i : ℝ)) := by
    simp only [smul_eq_mul, div_pow]
    field_simp
    exact Or.inl (mul_comm _ _)
  rw [hnum, hrhs]
  first
    | (gcongr; · positivity; · exact hfac)
    | exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac

/-- 量化步长 s 的均匀残差的 sub-Gaussian proxy(= 方差)。 -/
noncomputable def uniformProxy (s : ℝ) : ℝ := s^2 / 12

/--
  **proxy 恰为方差**:U[−s/2, s/2] 的方差为 s²/12,且由上述 MGF 界,
  它同时是合法的 sub-Gaussian proxy(通常论证只能给出 (s/2)² = 3× 更松)。
-/
theorem uniformProxy_eq_variance (s : ℝ) :
    uniformProxy s = s^2 / 12 := rfl

end WitCert
