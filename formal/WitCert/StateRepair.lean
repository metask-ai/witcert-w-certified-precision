/-
  WitCert 形式化 · L16:**修复只约束未来** —— 合规的未来不蕴含干净的现场。

  2026-08-09 的直接起因(同一天两次):

    * `runx` 的 `--pull` 失败后不 kill 子进程,四轮失败留下四对僵尸
      (`rsync` + `ssh -W <目标> <跳板>`),最久从 16:30 挂到 21:24、累计 54 分钟
      CPU,一直占着到**生产**跳板的连接。我给失败路径加了清理 —— 但**已经在跑
      的那四对不会因此消失**,仍要手工 kill。
    * 作废轮的 `r2a_packed.invalid.json`:我删了本地那份,下一次 `--pull` 又把它
      从远端拉了回来 —— 它带着**原始 mtime**,看起来像"一个新出现的未跟踪产物"。

  以及更早的同形状:"撤回要撤干净 —— 作废的产物 JSON 必须删除或显式标注
  superseded,留在 `experiments/out/` 就是给未来的自己埋引用陷阱"。

  三个实例共享一条逻辑事实:**策略约束的是轨迹,不是初始状态**。
  "从此以后每次获取都配对释放"与"此刻仍持有若干资源"完全相容 —— 正因如此,
  修复动作本身必须显式包含一次**清场**,否则修好的是未来、留下的是现场。

  本文件把它写成可机器检查的形式,并给出反例(否则规则是装饰品):

    * `compliant_future_keeps_dirty_site` —— **反例**:未来轨迹完全平衡,
      现场仍非空。这是"加了清理却仍有四对僵尸在跑"的形式版本。
    * `sweep_then_balanced_is_clean` —— 充分条件:先清场再走平衡轨迹,终态为空。
      修复动作必须**同时**包含这两半。
    * `delete_one_side_then_sync_restores` —— **反例**:双副本下只删一侧,
      随后一次同步就把它恢复。这是"删了本地、`--pull` 又拉回来"的形式版本;
      它说明"撤回"的作用域必须与"同步"的作用域一致。

  闭环边界(诚实说明):Lean 管不到 bash 有没有真写那句 `kill`。那一半由
  `tests/test_shell_gating.py` 的规则四承担(脚本若 `--pull` 且失败时 `exit`
  却从不 `kill` 残留 ⟹ 判红,变异检验在案)。本文件只负责说清**为什么"以后
  会清理"不等于"现在是干净的"** —— 那是判据设计时最容易跳过的一步。
-/

namespace WitCert.StateRepair

/-- 现场:当前持有的资源(子进程 / 未撤回的产物)。用 `List` 而非 `Finset`,
    因为同一资源可被重复获取(四对僵尸是四次独立 spawn)。 -/
abbrev Site := List Nat

/-- 可执行的操作。`sweep` 是**显式清场**,是修复动作里最容易被漏掉的那一半。 -/
inductive Op
  | acq (r : Nat)   -- 获取:spawn 一个子进程 / 落一份产物
  | rel (r : Nat)   -- 释放:kill / 删除
  | sweep           -- 清场:释放当前持有的全部
  deriving DecidableEq

def step (s : Site) : Op → Site
  | .acq r => r :: s
  | .rel r => s.erase r
  | .sweep => []

def run (s : Site) : List Op → Site
  | []      => s
  | o :: t  => run (step s o) t

/-- **平衡轨迹** = 修复后的策略:每次 `acq` 都紧跟配对的 `rel`。
    这正是"给失败路径加上 kill"之后,新产生的每一次拉取所满足的形状。 -/
inductive Balanced : List Op → Prop
  | nil  : Balanced []
  | pair (r : Nat) (t : List Op) : Balanced t → Balanced (.acq r :: .rel r :: t)

/-- 平衡轨迹从空现场出发,终态仍为空。 -/
theorem balanced_from_empty (t : List Op) (h : Balanced t) : run [] t = [] := by
  induction h with
  | nil => rfl
  | pair r t' _ ih =>
      -- run [] (acq r :: rel r :: t') = run ((r :: []).erase r) t' = run [] t'
      simp [run, step, List.erase_cons_head, ih]

/-- **反例①:合规的未来不蕴含干净的现场。**

    取现场 `[7]`(一个还在跑的僵尸)与空轨迹(此后不再获取任何资源,
    平凡地满足平衡)。策略被完美遵守,而现场依然非空。

    对应实况:我给 `runx` 的失败路径加了 `kill`,此后每一轮都会清理 ——
    但那四对已经在跑的僵尸不会因此消失,仍要手工 kill。 -/
theorem compliant_future_keeps_dirty_site :
    ∃ (s₀ : Site) (t : List Op), s₀ ≠ [] ∧ Balanced t ∧ run s₀ t ≠ [] := by
  refine ⟨[7], [], by simp, Balanced.nil, by simp [run]⟩

/-- **充分条件:清场 + 平衡未来 ⟹ 终态干净。**

    修复动作必须**同时**包含这两半:一次针对现场的 `sweep`,以及此后
    每次获取都配对释放。只做后者是 `compliant_future_keeps_dirty_site`。 -/
theorem sweep_then_balanced_is_clean (s₀ : Site) (t : List Op) (h : Balanced t) :
    run s₀ (.sweep :: t) = [] := by
  simpa [run, step] using balanced_from_empty t h

/-- 双副本(本地 / 远端)。`--pull` 的语义是**远端覆盖本地**。 -/
structure Replicas where
  local_ : Site
  remote : Site

/-- 只删本地(我当时做的)。 -/
def delLocal (p : Replicas) (r : Nat) : Replicas :=
  ⟨p.local_.erase r, p.remote⟩

/-- 两侧都删(应当做的)。 -/
def delBoth (p : Replicas) (r : Nat) : Replicas :=
  ⟨p.local_.erase r, p.remote.erase r⟩

/-- 一次 `--pull`:远端覆盖本地。 -/
def pull (p : Replicas) : Replicas := ⟨p.remote, p.remote⟩

/-- **反例②:只删一侧,一次同步就恢复。**

    对应实况:作废轮的 `r2a_packed.invalid.json` 我只删了本地,
    下一次 `--pull` 把它带着**原始 mtime** 拉了回来 —— 于是它看起来像
    "一个新出现的未跟踪产物",归因成本远高于当场删干净。

    要害:**撤回的作用域必须与同步的作用域一致**。 -/
theorem delete_one_side_then_sync_restores (r : Nat) (p : Replicas)
    (h : r ∈ p.remote) : r ∈ (pull (delLocal p r)).local_ := by
  simpa [pull, delLocal] using h

/-- 两侧都删则同步后确实消失(前提:远端 `erase` 后不再含 `r`,
    即该资源在远端只有一份)。这是 `delete_one_side_then_sync_restores`
    的对照组:修法不是"再删一次",而是**扩大撤回的作用域**。 -/
theorem delete_both_survives_sync (r : Nat) (p : Replicas)
    (h : r ∉ p.remote.erase r) : r ∉ (pull (delBoth p r)).local_ := by
  simpa [pull, delBoth] using h

end WitCert.StateRepair
