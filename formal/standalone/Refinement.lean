/-
  WitCert · L4 proof–kernel refinement 定理(**自包含版,不依赖 Mathlib**)

  这是防止 M3 事故重演的核心定理,刻意做成零依赖以便在 CI 中秒级检查。

  事故回顾(2026-07-27):kernel 为省一次矩阵乘,把逐 token 的
      A = Σ_t p̃_t · w_t          (w_t = e^{u_t})
  替换为对方差先平均再开根的形式。两者在 w 逐 token 变化时**不等**且不 sound。
  本定理证明:**当 w 在块内恒定时**(WitCert 的 scale 逐块 + tile 整除块保证),
  分块累加器与逐 token 求和**恒等** —— 于是该优化是 refinement 而非替换。

  代数结构:只需加法交换幺半群 + 左分配律,这里用最小自定义类型类,
  并对 Int 给出实例(实数情形的同一恒等式在 Mathlib 版 WitCert/Refinement.lean 中)。
-/
namespace WitCert

/-- 最小代数结构:满足左分配律的交换半环骨架(够证明本定理)。 -/
class DistribSum (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  mul_zero : ∀ a, mul a zero = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

instance : DistribSum Int where
  add := Int.add
  mul := Int.mul
  zero := 0
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add

variable {α β : Type} [D : DistribSum α]

open DistribSum

/-- 列表求和。 -/
def lsum : List α → α
  | [] => zero
  | x :: xs => add x (lsum xs)

/-- 逐 token 形式:Σ_t (p_t * w),w 为该块的常数权重。 -/
def perToken (w : α) : List α → α
  | [] => zero
  | p :: ps => add (mul w p) (perToken w ps)

/--
  **块内提取引理**(refinement 的核心):w 在块内恒定时,
      Σ_t (w * p_t) = w * (Σ_t p_t)
  即 kernel 的 `a_num += e^{u_b} * rowsum(p)` 与规格的逐 token 求和一致。
-/
theorem perToken_eq_mul_lsum (w : α) : ∀ ps : List α, perToken w ps = mul w (lsum ps)
  | [] => by simp [perToken, lsum, mul_zero]
  | p :: ps => by
      simp only [perToken, lsum]
      rw [perToken_eq_mul_lsum w ps, left_distrib]

/-- 分块形式:Σ_b w_b * (Σ_{t∈b} p_t) —— kernel 实际计算的累加器。 -/
def blockwise : List (α × List α) → α
  | [] => zero
  | (w, ps) :: rest => add (mul w (lsum ps)) (blockwise rest)

/-- 逐 token 形式的分组展开:Σ_b Σ_{t∈b} (w_b * p_t)。 -/
def perTokenGrouped : List (α × List α) → α
  | [] => zero
  | (w, ps) :: rest => add (perToken w ps) (perTokenGrouped rest)

/--
  **Refinement 主定理**:分块累加器 ≡ 逐 token 求和(块内权重恒定的前提下)。

  工程含义:kernel 中「每 query 一标量 × softmax 行和」的累加,与论文/规格中
  A = Σ_t p̃_t e^{u_t} 计算同一个数。任何声称"等价"的化简都必须在此处补出证明。
-/
theorem blockwise_eq_perTokenGrouped :
    ∀ groups : List (α × List α), blockwise groups = perTokenGrouped groups
  | [] => rfl
  | (w, ps) :: rest => by
      simp only [blockwise, perTokenGrouped]
      rw [perToken_eq_mul_lsum w ps, blockwise_eq_perTokenGrouped rest]

/--
  **反面命题**:若权重在块内变化,恒等式一般不成立。
  取块内两 token 权重 1 与 3、p 均为 1:逐 token 得 4,而按常数 w=1 的分块式得 2。
-/
example : (perToken (α := Int) 1 [1, 1]) ≠ Int.add (Int.mul 1 1) (Int.mul 3 1) := by
  decide

end WitCert

-- 黄金验证:确认证明不依赖 sorryAx(在 namespace 外用全名)
#print axioms WitCert.perToken_eq_mul_lsum
#print axioms WitCert.blockwise_eq_perTokenGrouped
