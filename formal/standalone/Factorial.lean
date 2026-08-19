/-
  WitCert · L2 的组合核心(**自包含,零依赖**)

  目标(sub-Gaussian proxy = 方差 的算术根源):逐项比较
      sinh x / x = Σ_k x^{2k}/(2k+1)!   ≤   Σ_k x^{2k}/(6^k k!) = e^{x²/6}
  需要:6^k · k! ≤ (2k+1)!。本文件机器检查该引理(纯 Nat,不用 Mathlib 的 factorial/ring)。
-/
namespace WitCert

/-- 自定义阶乘(Lean 核心无 Nat.factorial)。 -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- 归纳步算术核心:6·(k+1) ≤ (2k+2)(2k+3)。 -/
theorem six_mul_succ_le (k : Nat) : 6 * (k + 1) ≤ (2 * k + 2) * (2 * k + 3) := by
  -- 避开非线性:用 (2k+3) ≥ 3 把乘法降为线性
  have h3 : 3 ≤ 2 * k + 3 := by omega
  have hmul : (2 * k + 2) * 3 ≤ (2 * k + 2) * (2 * k + 3) :=
    Nat.mul_le_mul (Nat.le_refl (2 * k + 2)) h3
  have heq : (2 * k + 2) * 3 = 6 * (k + 1) := by omega
  omega

/-- 阶乘的两步展开:(2k+3)! = (2k+2)(2k+3)·(2k+1)!。 -/
theorem fact_two_step (k : Nat) :
    fact (2 * k + 3) = (2 * k + 2) * (2 * k + 3) * fact (2 * k + 1) := by
  show ((2 * k + 2) + 1) * fact (2 * k + 2) = _
  show ((2 * k + 2) + 1) * (((2 * k + 1) + 1) * fact (2 * k + 1)) = _
  have : (2 * k + 2) + 1 = 2 * k + 3 := by omega
  have h2 : (2 * k + 1) + 1 = 2 * k + 2 := by omega
  rw [this, h2]
  rw [← Nat.mul_assoc]
  have : (2 * k + 3) * (2 * k + 2) = (2 * k + 2) * (2 * k + 3) := Nat.mul_comm _ _
  rw [this]

/--
  **L2 组合引理**:6^k · k! ≤ (2k+1)!

  这是"均匀抖动的 sub-Gaussian proxy 恰等于方差 s²/12"(而非通常论证给出的更松的 (s/2)²)
  的算术根源,也是 WitCert 的界比 Bernstein 型(带 M·log 项)更紧的来源。
-/
theorem six_pow_mul_fact_le (k : Nat) : 6 ^ k * fact k ≤ fact (2 * k + 1) := by
  induction k with
  | zero => decide
  | succ n ih =>
      have hidx : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      rw [hidx, fact_two_step n]
      have hlhs : 6 ^ (n + 1) * fact (n + 1) = (6 * (n + 1)) * (6 ^ n * fact n) := by
        show 6 ^ (n + 1) * ((n + 1) * fact n) = _
        rw [Nat.pow_succ]
        rw [Nat.mul_comm (6 ^ n) 6]
        rw [Nat.mul_assoc, Nat.mul_assoc]
        rw [← Nat.mul_assoc (n + 1) (6 ^ n) (fact n)]
        rw [Nat.mul_comm (n + 1) (6 ^ n)]
        rw [Nat.mul_assoc]
      rw [hlhs]
      exact Nat.mul_le_mul (six_mul_succ_le n) ih

end WitCert

#print axioms WitCert.six_mul_succ_le
#print axioms WitCert.fact_two_step
#print axioms WitCert.six_pow_mul_fact_le
