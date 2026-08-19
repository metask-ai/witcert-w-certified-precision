/-
  WitCert · 代际一致性定理(**自包含版,不依赖 Mathlib**)

  事故回顾(2026-08-02):packed 池的 `written` 标志把「曾经打包过」与「仍属
  当前代际」混为一谈。分配器复用槽位(源换代)时全仓无人调用 invalidate,
  读路径的 ¬written 门永不刷新 —— 消费者吃到上一代的 payload。长上下文检索
  从 1.000 崩到 0.050;写站点无条件失效(布尔散射 + 代际递增)修复后恢复
  1.000,两臂仅差失效开关的对照返回 INVALIDATION_CONFIRMED(p118→p124c)。

  本文件把这次「缺陷 → 修复」钉成两个机器检查的命题:

  · `stale_consume_reachable`:无失效纪律的事件模型里,存在事件迹使消费者
    在 written=true 下读到与当前源**不同**的值 —— 缺陷不是偶然,是可达状态;
  · `run_fresh`:把「写站点失效」建模为复合事件(源写与失效原子成对,
    对应 extract.py 在任何采样门之前的无条件失效),则新鲜性不变量沿任意
    事件迹保持,消费值恒等于当前源值 —— 修复是充分的,且不依赖
    「首见即终态」之类的经验假设。

  与工程的对应:Slot.gen_src = FP8 源的代际(分配器复用即换代);
  Slot.packed_gen/written = PackedInt*Pool 的 slot_gen/written_map;
  consume 的 fail-closed 分支 = 消费者按 written 掩码回退 FP8。
-/
namespace WitCert

/-- 双存储槽:src 为真理源(FP8 页),packed 为压缩副本。 -/
structure Slot (α : Type) where
  src        : α
  gen_src    : Nat
  packed     : α
  packed_gen : Nat
  written    : Bool

/-- 缺陷模型的事件:源写(槽位复用)**不**通知 packed —— 2026-08-02 之前的系统。 -/
inductive Ev (α : Type) where
  | srcWrite (v : α)   -- 上游写入/槽位复用:源换代,packed 状态原样保留
  | pack               -- 打包:packed := src,记录打包时代际
  | invalidate         -- 显式失效(缺陷系统中存在此 API 但零调用)

def step {α} (s : Slot α) : Ev α → Slot α
  | .srcWrite v  => { s with src := v, gen_src := s.gen_src + 1 }
  | .pack        => { s with packed := s.src, packed_gen := s.gen_src, written := true }
  | .invalidate  => { s with written := false }

def run {α} (s : Slot α) : List (Ev α) → Slot α
  | []      => s
  | e :: t  => run (step s e) t

/-- 消费语义(fail-closed):written 时读 packed,否则回退源。 -/
def consume {α} (s : Slot α) : α :=
  if s.written then s.packed else s.src

/-- **缺陷可达**:存在初始槽与事件迹,消费者在 written=true 下读到非当前源值。
    迹即最小复现:pack(终态入 packed)→ srcWrite(槽位复用换代,无人失效)。 -/
theorem stale_consume_reachable :
    ∃ (s₀ : Slot Bool) (tr : List (Ev Bool)),
      (run s₀ tr).written = true ∧ consume (run s₀ tr) ≠ (run s₀ tr).src := by
  refine ⟨⟨false, 0, false, 0, false⟩, [.pack, .srcWrite true], ?_, ?_⟩
  · rfl
  · simp [run, step, consume]

/-- 合规模型的事件:**写站点失效纪律** —— 源写与失效是一个原子复合事件
    (工程实现:dsv4_certified_write_compress 在任何采样门之前无条件
    invalidate,槽位被写 = 定义上换代)。 -/
inductive EvD (α : Type) where
  | srcWriteInv (v : α)   -- 源写 + 同步失效(原子)
  | pack
  | invalidate

def stepD {α} (s : Slot α) : EvD α → Slot α
  | .srcWriteInv v => { s with src := v, gen_src := s.gen_src + 1, written := false }
  | .pack          => { s with packed := s.src, packed_gen := s.gen_src, written := true }
  | .invalidate    => { s with written := false }

def runD {α} (s : Slot α) : List (EvD α) → Slot α
  | []      => s
  | e :: t  => runD (stepD s e) t

/-- 新鲜性不变量:written 蕴含 packed 与源同代同值。 -/
def Inv {α} (s : Slot α) : Prop :=
  s.written = true → s.packed_gen = s.gen_src ∧ s.packed = s.src

theorem inv_step {α} (s : Slot α) (e : EvD α) (_h : Inv s) : Inv (stepD s e) := by
  cases e with
  | srcWriteInv v => intro hw; cases hw
  | pack          => intro _; exact ⟨rfl, rfl⟩
  | invalidate    => intro hw; cases hw

theorem inv_run {α} (s : Slot α) (tr : List (EvD α)) (h : Inv s) :
    Inv (runD s tr) := by
  induction tr generalizing s with
  | nil => exact h
  | cons e t ih => exact ih (stepD s e) (inv_step s e h)

/-- **修复充分性**:失效纪律下,任意事件迹后的消费值恒等于当前源值。
    不依赖「首见即终态」等经验假设 —— 正确性由不变量承担。 -/
theorem run_fresh {α} (s : Slot α) (tr : List (EvD α)) (h : Inv s) :
    consume (runD s tr) = (runD s tr).src := by
  have hinv := inv_run s tr h
  unfold consume
  by_cases hw : (runD s tr).written = true
  · rw [if_pos hw]; exact (hinv hw).2
  · rw [if_neg hw]

#print axioms stale_consume_reachable
#print axioms run_fresh

end WitCert
