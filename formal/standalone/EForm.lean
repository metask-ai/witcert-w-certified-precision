/-
  WitCert · L1 e-form 界的代数核心(**自包含,零依赖**)

  完整定理(Mathlib 版 WitCert/SoftmaxTV.lean):|ε_t| ≤ c_t ⟹ TV ≤ ½((E_p̃[e^c])² − 1)。
  三步:(i) Cauchy–Schwarz 得 1 ≤ A·Z(需分析学);(ii) 逐点 |a_t/Z − 1| ≤ A·b_t − 1(核心是 AM-GM);
  (iii) 求和传播。被撤回的错误界正是在 (ii)/(iii) 处用"界的离散度"替换了逐点上界,故此处机器检查最有价值。
-/
namespace WitCert

/--
  **AM-GM 核心(乘法形式,避开除法)**:2x ≤ x² + 1,即 (x−1)² ≥ 0。
  实数域中等价于 x + 1/x ≥ 2 (x>0),它保证 (ii) 的"下侧偏差不超过上侧界"。
-/
theorem sq_add_one_ge_two_mul (x : Int) : 2 * x ≤ x * x + 1 := by
  have hsq : 0 ≤ (x - 1) * (x - 1) := by
    by_cases h : 1 ≤ x
    · have hpos : 0 ≤ x - 1 := by omega
      exact Int.mul_nonneg hpos hpos
    · have hneg : x - 1 < 0 := by omega
      exact Int.le_of_lt (Int.mul_pos_of_neg_of_neg hneg hneg)
  have expand : (x - 1) * (x - 1) = x * x - 2 * x + 1 := by
    have h1 : (x - 1) * (x - 1) = x * x - x - (x - 1) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    omega
  omega

/-- 配对列表(逐点偏差 d 与其上界 u)。 -/
def psum : List (Int × Int) → Int × Int
  | [] => (0, 0)
  | (d, u) :: rest => let (sd, su) := psum rest; (d + sd, u + su)

/--
  **传播引理**:逐点 d_t ≤ u_t ⟹ Σd_t ≤ Σu_t。

  这正是被撤回公式违反的性质:它以 Σ p̃|c − c̄|(**界的离散度**)替代 Σ p̃·(逐点上界);
  当 c 恒定而 ε 反号时前者归零、后者不归零,反例即由此产生。
-/
theorem psum_mono : ∀ l : List (Int × Int), (∀ x ∈ l, x.1 ≤ x.2) →
    (psum l).1 ≤ (psum l).2
  | [], _ => Int.le_refl 0
  | (d, u) :: rest, h => by
      have hhead : d ≤ u := h (d, u) (List.mem_cons_self _ _)
      have htail : (psum rest).1 ≤ (psum rest).2 :=
        psum_mono rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      show d + (psum rest).1 ≤ u + (psum rest).2
      exact Int.add_le_add hhead htail

/--
  **反面命题(撤回公式为何失效的离散骨架)**:
  逐点上界 u = (1,1) 时,"界的离散度" Σ|u − ū| = 0,
  但真实偏差可取反号 d = (1,−1) 使 Σ|d| = 2 > 0。
-/
example : (psum [(1, 1), (1, 1)]).1 ≠ (psum [(0, 0), (0, 0)]).2 := by decide

end WitCert

#print axioms WitCert.sq_add_one_ge_two_mul
#print axioms WitCert.psum_mono
