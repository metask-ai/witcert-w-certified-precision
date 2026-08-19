/-
  WitCert · L3 请求级预算的算术核心(**自包含,零依赖**)

  证书按 (层 × 头 × 解码步) 分配失败概率:δ_loc = δ_req / (L·H·T)。
  soundness 论证 = 联合界(测度论,见 Mathlib 版)+ **预算算术**(本文件)。

  本文件证明:n 个事件各自概率 ≤ δ_loc ⟹ 概率之和 ≤ n·δ_loc。
  与联合界 P(∪Eᵢ) ≤ Σ P(Eᵢ) 合成,即得 P(∪Eᵢ) ≤ n·δ_loc ≤ δ_req。
-/
namespace WitCert

/-- 有序加法结构(够证明本定理的最小假设)。 -/
class OrdAdd (α : Type) where
  add : α → α → α
  zero : α
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  add_le_add : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)
  zero_le_zero : le zero zero
  add_zero : ∀ a, add a zero = a

instance : OrdAdd Int where
  add := Int.add
  zero := 0
  le := (· ≤ ·)
  le_refl := Int.le_refl
  le_trans := Int.le_trans
  add_le_add := fun h1 h2 => Int.add_le_add h1 h2
  zero_le_zero := Int.le_refl 0
  add_zero := Int.add_zero

variable {α : Type} [O : OrdAdd α]

open OrdAdd

/-- 列表求和。 -/
def lsum : List α → α
  | [] => zero
  | x :: xs => add x (lsum xs)

/-- n 份 δ 相加(n·δ 的构造性写法)。 -/
def nsmul (n : Nat) (d : α) : α :=
  match n with
  | 0 => zero
  | k + 1 => add d (nsmul k d)

/--
  **预算算术定理**:若列表每个元素 ≤ δ,则其和 ≤ (列表长度)·δ。

  工程含义:L·H·T 个 (层,头,步) 的局部违约概率各自 ≤ δ_loc ⟹ 总和 ≤ (L·H·T)·δ_loc = δ_req。
  与测度论的联合界(Mathlib 版 RequestBudget.lean)合成即得请求级 soundness。
-/
theorem lsum_le_nsmul (d : α) :
    ∀ (xs : List α), (∀ x ∈ xs, le x d) → le (lsum xs) (nsmul xs.length d)
  | [], _ => by
      show le zero zero
      exact zero_le_zero
  | x :: xs, h => by
      show le (add x (lsum xs)) (add d (nsmul xs.length d))
      refine add_le_add (h x (List.mem_cons_self x xs)) ?_
      exact lsum_le_nsmul d xs (fun y hy => h y (List.mem_cons_of_mem x hy))

/--
  **预算合成**:给定联合界(作为假设 `hsub`,其证明属测度论)与上述算术,
  得到请求级违约概率 ≤ δ_req。这里显式把"测度论部分"与"预算算术部分"分离,
  使得后者可零依赖机器检查,前者在 Mathlib 版中补齐。
-/
theorem request_budget_compose
    (Punion : α) (probs : List α) (δloc δreq : α)
    (hsub : le Punion (lsum probs))                       -- 联合界(测度论)
    (hloc : ∀ p ∈ probs, le p δloc)                       -- 每个局部事件的预算
    (hbudget : le (nsmul probs.length δloc) δreq) :       -- 预算分配
    le Punion δreq :=
  le_trans hsub (le_trans (lsum_le_nsmul δloc probs hloc) hbudget)

end WitCert

#print axioms WitCert.lsum_le_nsmul
#print axioms WitCert.request_budget_compose
