/- 观测充分性与门禁非空洞性(仪器/判据层形式化)。

  盘点本项目全部真实事故后的发现:多数"易踩坑"是**同一个逻辑形状**——
  观测函数在结论所依赖的区分上**不单射**,于是"读数一致"被误当作
  "状态一致"。四次不同现场,同一形状:

  · 铁律 7(2026-08-02):"两臂结果相同"区分不了"生效且无害"与
    "根本没生效"(p112a 假阴性)—— 只看输出的门禁对 installed 不单射;
  · Limitations(graph 采样事故):全程覆盖 ≠ 运行期存活 —— 启动期样本
    让 28 层全覆盖,replay 期贡献为 0,而门禁只看总量;
  · 等待循环出口(记忆 wait-loop-must-distinguish-exits,今日第三变体):
    "轮询耗尽"与"找到结果"退出码同为 0;
  · 根因纪律 1:/health 通 ≠ 服务就绪、env 已设 ≠ 代码执行 —— 间接信号
    对目标状态不单射。

  另有两类**非**此形状、单独形式化的:
  · 门禁非空洞性(test_gate_falsifiable 的原则):恒真判据是装饰品,
    必须存在能让它 FAIL 的输入;
  · 分派 fallthrough(L0 编码偏差):主判别式不在最外层时,某些输入被
    路由到错误分支。

  聚合键的身份充分性是本形状的另一族实例,单列于 KeyIdentity.lean
  (三次事故:代际/行级/请求身份)。

  零外部依赖,`by decide` 全机械判定。-/

namespace WitCert.Adequacy

/-- 观测充分性:若两状态在**结论所量化的性质** `P` 上不同,观测必须不同。
    不充分 ⇔ 存在一对"P 不同而观测相同"的状态(混淆对)。 -/
def Adequate {S O K : Type} [DecidableEq O] [DecidableEq K]
    (obs : S → O) (P : S → K) : Prop :=
  ∀ a b : S, P a ≠ P b → obs a ≠ obs b

/-- 混淆对的存在即不充分(定义展开,给实例用的便利形式)。 -/
theorem inadequate_of_confusion {S O K : Type} [DecidableEq O] [DecidableEq K]
    {obs : S → O} {P : S → K} {a b : S}
    (hP : P a ≠ P b) (hO : obs a = obs b) : ¬ Adequate obs P :=
  fun h => (h a b hP) hO

/-! ## 实例一:门禁只看输出(铁律 7,p112a 假阴性) -/

/-- 一臂的可观测面:是否装配、逐题输出。 -/
structure Arm where
  installed : Nat        -- 存在证据(计数器)
  output    : Nat        -- 无害证据(质量读数)
  deriving DecidableEq, Repr

/-- 只看 output 的门禁,对"装没装"零区分度 —— 装了无害与根本没装
    产生同一读数。这正是 p112a 险些通过的假阴性。 -/
theorem output_only_gate_inadequate :
    ¬ Adequate (fun a : Arm => a.output) (fun a : Arm => a.installed) :=
  inadequate_of_confusion (a := ⟨1, 100⟩) (b := ⟨0, 100⟩)
    (by decide) (by decide)

/-- 修复:观测同时携带存在证据,即充分(验收判据必须含"处理独有的
    正向信号")。 -/
theorem existence_plus_output_adequate :
    Adequate (fun a : Arm => (a.installed, a.output))
             (fun a : Arm => a.installed) := by
  intro a b h hEq
  exact h (congrArg Prod.fst hEq)

/-! ## 实例二:全程覆盖 ≠ 运行期存活(CUDA graph 采样事故) -/

structure Run where
  warmupHits : Nat       -- 启动期样本
  liveHits   : Nat       -- 运行期(replay)真实贡献
  deriving DecidableEq, Repr

/-- 只看总量的覆盖门对"运行期是否存活"不单射:启动期样本可以把
    全部层数刷满,而 replay 贡献为 0。 -/
theorem lifetime_coverage_inadequate :
    ¬ Adequate (fun r : Run => r.warmupHits + r.liveHits)
               (fun r : Run => r.liveHits) :=
  inadequate_of_confusion (a := ⟨28, 0⟩) (b := ⟨0, 28⟩)
    (by decide) (by decide)

/-- 修复:设备侧执行计数单列(观测直接含 liveHits)。 -/
theorem live_counter_adequate :
    Adequate (fun r : Run => (r.liveHits, r.warmupHits))
             (fun r : Run => r.liveHits) := by
  intro a b h hEq
  exact h (congrArg Prod.fst hEq)

/-! ## 实例三:等待循环出口(耗尽 vs 找到) -/

inductive Exit | found | exhausted
  deriving DecidableEq, Repr

/-- 只看退出码(两者皆 0)对出口类型零区分度 —— 通知长得一模一样。 -/
theorem exit_code_inadequate :
    ¬ Adequate (fun _ : Exit => (0 : Nat)) (fun e : Exit => e) :=
  inadequate_of_confusion (a := Exit.found) (b := Exit.exhausted)
    (by decide) (by decide)

/-! ## 实例四:间接信号(/health 通 ≠ 就绪;env 已设 ≠ 代码执行) -/

structure Service where
  healthOk : Nat         -- 间接信号(端口应答,旧进程亦可满足)
  ready    : Nat         -- 目标状态(本进程真正就绪)
  deriving DecidableEq, Repr

theorem indirect_signal_inadequate :
    ¬ Adequate (fun s : Service => s.healthOk) (fun s : Service => s.ready) :=
  inadequate_of_confusion (a := ⟨1, 0⟩) (b := ⟨1, 1⟩)
    (by decide) (by decide)

/-- **带充分性证明的仪器**(与 KeyedClaim / CausalFinding 同律):
    仪器要支撑关于 `P` 的结论,必须携带 `Adequate obs P` 的证明 ——
    只看输出的门禁想声明"装配生效"?`sound` 字段无从提供。 -/
structure AdequateInstrument (S O K : Type) [DecidableEq O] [DecidableEq K] where
  obs   : S → O
  P     : S → K
  sound : Adequate obs P

/-- 修复后的验收门可构造(观测携带存在证据)。 -/
def armGateFixed : AdequateInstrument Arm (Nat × Nat) Nat :=
  ⟨fun a => (a.installed, a.output), fun a => a.installed,
   existence_plus_output_adequate⟩

/-- 修复后的图内覆盖门可构造(观测携带设备侧执行计数)。 -/
def graphCoverageFixed : AdequateInstrument Run (Nat × Nat) Nat :=
  ⟨fun r => (r.liveHits, r.warmupHits), fun r => r.liveHits,
   live_counter_adequate⟩

/-! ## 实例五:无噪声底的差异量(2026-08-05 q11n/q11o 事故)

    两轮读数之差被当作"是否腐坏"的信号,而同配置重复对本身就差同样
    量级 —— 差异量对"腐坏与否"不单射。修复:观测须携带同配置重复对
    的底噪(差异 + 底噪 ⇒ 可判)。 -/

structure DiffObs where
  crossDiff : Nat        -- 跨臂差异(×1000)
  noiseFloor : Nat       -- 同配置重复对底噪(×1000)
  corrupt   : Nat        -- 目标状态:是否真腐坏
  deriving DecidableEq, Repr

/-- 只看跨臂差异:腐坏与"底噪同样大的健康对"读数相同 —— 零区分度。 -/
theorem bare_diff_inadequate :
    ¬ Adequate (fun d : DiffObs => d.crossDiff) (fun d : DiffObs => d.corrupt) :=
  inadequate_of_confusion (a := ⟨595, 66, 1⟩) (b := ⟨595, 595, 0⟩)
    (by decide) (by decide)

/-- 修复:差异与底噪成对观测即充分(此即"噪声底必须逐设定计算")。 -/
theorem diff_with_floor_adequate :
    Adequate (fun d : DiffObs => (d.crossDiff, d.noiseFloor, d.corrupt))
             (fun d : DiffObs => d.corrupt) := by
  intro a b h hEq
  exact h (congrArg (fun t => t.2.2) hEq)

/-! ## 稳定性(Adequate 的对偶;2026-08-05 q11o 复审的两个度量错)

    Adequate 管"P 不同 ⇒ 读数必须不同"(漏报方向);这里管
    "P 相同 ⇒ 读数不许乱跳"(误报方向)。两个真实度量错各归一类:
    ①带符号求和后取相对差 —— 对逐元素微扰**不稳定**(近零分母放大);
    ②聚合无序集合却取"迭代序最后一个" —— 对**置换不不变**。 -/

/-- 稳定:目标性质相同的两状态,观测必须一致(误报方向的守门)。 -/
def Stable {S O K : Type} [DecidableEq O] [DecidableEq K]
    (obs : S → O) (P : S → K) : Prop :=
  ∀ a b : S, P a = P b → obs a = obs b

theorem unstable_of_spurious {S O K : Type} [DecidableEq O] [DecidableEq K]
    {obs : S → O} {P : S → K} {a b : S}
    (hP : P a = P b) (hO : obs a ≠ obs b) : ¬ Stable obs P :=
  fun h => hO (h a b hP)

/-- 玩具行:两个带符号分量;P = 粗量化(等价类);obs = 和的符号级
    读数。微扰不改 P,却把和从 0 拉到非 0 —— 带符号求和不稳定。
    (Int 版本;真实场景即 512 维行近零代数和的相对差爆炸。) -/
def rowP (r : Int × Int) : Int × Int := (r.1 / 10, r.2 / 10)   -- 粗量化
def rowSum (r : Int × Int) : Int := r.1 + r.2

theorem signed_sum_unstable :
    ¬ Stable (fun r => rowSum r) (fun r => rowP r) :=
  unstable_of_spurious (a := ((10 : Int), (-10 : Int)))
    (b := ((11 : Int), (-10 : Int))) (by decide) (by decide)

/-- 修复:L1(绝对值和)在同一对上稳定读数接近 —— 玩具中取粗量化后
    相等,机器可判。 -/
theorem l1_stable_on_witness :
    (fun r : Int × Int => (Int.natAbs r.1 + Int.natAbs r.2) / 10)
        ((10 : Int), (-10 : Int))
      = (fun r : Int × Int => (Int.natAbs r.1 + Int.natAbs r.2) / 10)
        ((11 : Int), (-10 : Int)) := by decide

/-- 置换不变:聚合无序集合的读数不得依赖迭代序。 -/
def PermInvariant {O : Type} [DecidableEq O] (f : List Nat → O) : Prop :=
  ∀ l l' : List Nat, l.Perm l' → f l = f l'

/-- "记最后一个"不置换不变:[a,b] 与 [b,a] 读数不同 —— 相位并集使
    同槽同调用双行,行序即随机,q11o 写次数越多差越大即此。 -/
def lastOr0 : List Nat → Nat
  | [] => 0
  | [x] => x
  | _ :: xs => lastOr0 xs

theorem last_not_perm_invariant : ¬ PermInvariant lastOr0 := by
  intro h
  have hp : ([1, 2] : List Nat).Perm [2, 1] := by
    exact List.Perm.swap 2 1 []
  have := h [1, 2] [2, 1] hp
  simp [lastOr0] at this

/-- 修复:插入排序读数置换不变 —— 见证对上机器可判。 -/
def insSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert1 x (insSort xs)
where
  insert1 (x : Nat) : List Nat → List Nat
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert1 x ys

theorem sorted_multiset_invariant_witness :
    insSort [1, 2] = insSort [2, 1] := by decide

/-! ## 实例六:陈旧完成标记(2026-08-06 runx 等待循环事故)

    等待谓词 = "远端日志里 grep 到 DONE"。日志跨轮未截断时,上一轮残留
    的 DONE 与本轮真完成产生同一读数 —— 观测对"本轮是否完成"不单射:
    runx 在 3 分钟处宣布 8 分钟采集"完成"并拉回上一轮产物。
    机械修复:发射前截断远端日志(runx 步骤 2.5),使"旧标记存在"退出
    可达状态 —— 该不变量下同一观测即充分。 -/

structure LaunchLog where
  staleMarker : Nat      -- 日志残留的上一轮标记(0/1)
  thisDone    : Nat      -- 目标状态:本轮真正完成(0/1)
  deriving DecidableEq, Repr

/-- 只 grep 标记:『旧标记残留+本轮未完成』与『本轮完成且无残留』读数
    相同 —— 零区分度。 -/
theorem stale_marker_inadequate :
    ¬ Adequate (fun l : LaunchLog => max l.staleMarker l.thisDone)
               (fun l : LaunchLog => l.thisDone) :=
  inadequate_of_confusion (a := ⟨1, 0⟩) (b := ⟨0, 1⟩)
    (by decide) (by decide)

/-- 修复:截断不变量(staleMarker = 0)下,标记读数就是完成状态本身 ——
    充分性在可达状态上恢复。 -/
theorem truncated_marker_adequate :
    ∀ a b : LaunchLog, a.staleMarker = 0 → b.staleMarker = 0 →
      a.thisDone ≠ b.thisDone →
      max a.staleMarker a.thisDone ≠ max b.staleMarker b.thisDone := by
  intro a b ha hb h
  simpa [ha, hb, Nat.zero_max] using h

/-! ## 实例七:冻结的记账键(2026-08-06 w1 池采集 run-2/4 事故)

    产物声明按请求 uid 分组,但身份状态机在 radix-off+tp4 配置下从未
    执行,uid 恒 0 —— 键通道对请求身份零区分,"真实池"实为合成池。
    KeyIdentity 家族的退化变体:键不是缺声明,是**声明了但常值**。
    符合性层影子 = 非退化义务(观测键基数 ≥ 2 才许承载逐请求结论,
    tests/test_key_conformance.py key_card 检查)。 -/

structure KeyedRecord where
  uidField : Nat         -- 记录携带的 uid 字段
  request  : Nat         -- 真实请求身份
  deriving DecidableEq, Repr

/-- 冻结键(恒 0)对请求身份零区分 —— 不充分。 -/
theorem frozen_key_inadequate :
    ¬ Adequate (fun _ : KeyedRecord => (0 : Nat))
               (fun r : KeyedRecord => r.request) :=
  inadequate_of_confusion (a := ⟨0, 0⟩) (b := ⟨0, 1⟩)
    (by decide) (by decide)

/-- 修复:忠实键(uidField = request 不变量)下键读数即身份 —— 充分。
    恒值键在任何含两个请求的产物上必然违反忠实性,故基数检查可判。 -/
theorem faithful_key_adequate :
    ∀ a b : KeyedRecord, a.uidField = a.request → b.uidField = b.request →
      a.request ≠ b.request → a.uidField ≠ b.uidField := by
  intro a b ha hb h
  rw [ha, hb]; exact h

/-! ## 实例八:死窗口冒充测量(2026-08-07 E13 run-1 事故)

    压测客户端在服务器已死时"每档照常结束",launcher 只看进程退出 ——
    观测对"是否真的测了活服务器"不单射:死窗口(0 完成+海量错误)与
    活窗口产生同一个 ARM_OK。修复:级别有效性必须携带正向完成信号
    (completed > 0),Python 同构 = w3cc_verdict.py V3。 -/

structure Window where
  completed : Nat        -- 窗口内真实完成的请求数
  exited    : Nat        -- 客户端进程正常退出(0/1)—— 死活皆 1
  deriving DecidableEq, Repr

/-- 只看退出:死窗口(0 完成)与活窗口读数相同 —— 零区分度。 -/
theorem dead_window_inadequate :
    ¬ Adequate (fun w : Window => w.exited)
               (fun w : Window => w.completed) :=
  inadequate_of_confusion (a := ⟨0, 1⟩) (b := ⟨9, 1⟩)
    (by decide) (by decide)

/-- 修复:观测携带完成计数即充分(正向信号纪律,铁律 7 同族)。 -/
theorem completion_signal_adequate :
    Adequate (fun w : Window => (w.completed, w.exited))
             (fun w : Window => w.completed) := by
  intro a b h hEq
  exact h (congrArg Prod.fst hEq)

/-! ## 实例九:链条返回冒充尾步执行(2026-08-07 interactive-chain 事故)

    `commit && truncate && launch` 在中段(pre-commit 拒绝)断裂,链条
    "结束"了而发射从未发生 —— 观测(链条返回)对"尾步执行了吗"不单射,
    操作者据此报了"在途"。机械修复:尾步自发正向标记(runx 步骤 3.6
    LAUNCH_CONFIRMED:远端进程存活 ∧ 日志非空),报告以其为前提;
    结构性修复:树清洁前台化(步骤 2.7),链条失去存在理由。 -/

structure Chain where
  tailRan  : Nat         -- 尾步(发射)真的执行了(0/1)
  returned : Nat         -- 链条命令返回了(断裂与成功皆 1)
  deriving DecidableEq, Repr

/-- 只看链条返回:中段断裂(尾步未跑)与全链成功读数相同。 -/
theorem chain_return_inadequate :
    ¬ Adequate (fun c : Chain => c.returned)
               (fun c : Chain => c.tailRan) :=
  inadequate_of_confusion (a := ⟨0, 1⟩) (b := ⟨1, 1⟩)
    (by decide) (by decide)

/-- 修复:观测携带尾步自发标记即充分(LAUNCH_CONFIRMED 语义)。 -/
theorem tail_marker_adequate :
    Adequate (fun c : Chain => (c.tailRan, c.returned))
             (fun c : Chain => c.tailRan) := by
  intro a b h hEq
  exact h (congrArg Prod.fst hEq)

/-! ## 实例十:静默即挂起(2026-08-07 runx STALL 假报事故)

    等待器判"实验是否 hang"用的观测 = launcher 日志 mtime 静默时长。
    但长 decode 下 launcher 日志本就静默(每请求间才打点),而 srv 日志
    在滚、进程活着、GPU 出力 —— "静默"对"真 hang"不单射:健康长跑与
    真死锁产生同一个"日志静默"读数,三臂被误判 hang 直至墙钟超时。
    真 hang 的定义就是 srv 也静默且进程已死(isHung 由这两者判定),故
    只看 launcher 静默必不充分;观测带 (srv 静默, 进程活性) 即充分。
    命名根因另记:srv glob 前缀漂移使 srv mtime 从未被采到。 -/

structure Wait where
  launcherIdle : Nat     -- launcher 日志静默时长(长 decode 下健康态也大)
  srvIdle      : Nat     -- srv 日志静默时长(decode 期持续滚动 ⇒ 小)
  procAlive    : Nat     -- launcher 进程活性(0/1)
  deriving DecidableEq, Repr

/-- 真 hang 的判定:srv 也静默(≥30)且进程已死。目标状态由 (srv, proc)
    决定 —— launcher 静默不在其中。 -/
def isHung (w : Wait) : Nat :=
  if w.procAlive = 0 ∧ 30 ≤ w.srvIdle then 1 else 0

/-- 只看 launcher 静默:健康长跑(⟨99,0,1⟩:srv 在滚+进程活,isHung=0)与
    真 hang(⟨99,30,0⟩:srv 静默+进程死,isHung=1)读数相同 —— 零区分度。 -/
theorem silence_inadequate :
    ¬ Adequate (fun w : Wait => w.launcherIdle) isHung :=
  inadequate_of_confusion (a := ⟨99, 0, 1⟩) (b := ⟨99, 30, 0⟩)
    (by decide) (by decide)

/-- 修复:观测携带 (srv 静默, 进程活性) 即充分 —— isHung 是这两者的函数,
    故观测相同 ⟹ 目标相同,充分性平凡成立。 -/
theorem liveness_signals_adequate :
    Adequate (fun w : Wait => (w.srvIdle, w.procAlive)) isHung := by
  intro a b h hEq
  apply h
  have hs : a.srvIdle = b.srvIdle := congrArg Prod.fst hEq
  have hp : a.procAlive = b.procAlive := congrArg Prod.snd hEq
  simp only [isHung, hs, hp]

/-! ## 门禁非空洞性(test_gate_falsifiable 的原则) -/

/-- 可证伪:存在能让判据 FAIL 的输入。恒真判据 = 装饰品。 -/
def Falsifiable {S : Type} (g : S → Bool) : Prop := ∃ s : S, g s = false

/-- **带证据的门禁**:构造时必须提供反例见证,装饰品构造不出。 -/
structure Gate (S : Type) where
  decide     : S → Bool
  falsifiable : Falsifiable decide

/-- 恒真门不可构造(其可证伪性不成立)。 -/
theorem const_true_not_falsifiable {S : Type} :
    ¬ Falsifiable (fun _ : S => true) := by
  rintro ⟨s, hs⟩; exact Bool.noConfusion hs

/-- 真判据的例子:要求存在证据非零(p112a 修复后的门)。 -/
def installedGate : Gate Arm :=
  ⟨fun a => decide (a.installed ≠ 0), ⟨⟨0, 100⟩, by decide⟩⟩

/-! ## 分派 fallthrough(L0 编码偏差:AND 条件落入后续 else-if) -/

/-- 三元判别:主类型 `kind`,次要标志 `flag`。 -/
structure Item where
  kind : Nat             -- 0=A,1=B
  flag : Nat             -- 0/1
  deriving DecidableEq, Repr

/-- 错误分派:`flag=1 ∧ kind=0` 才走 A,否则落 else-if 判 kind ——
    于是 `flag=0` 的 A 类被路由成 B(真实事故形状)。 -/
def dispatchBad (i : Item) : Nat :=
  if i.flag = 1 ∧ i.kind = 0 then 0 else 1

/-- 正确分派:主类型在最外层,标志只影响处理细节。 -/
def dispatchGood (i : Item) : Nat := i.kind

/-- 误路由存在性:flag=0 的 A 类被 dispatchBad 判成 B。 -/
theorem dispatch_fallthrough :
    dispatchBad ⟨0, 0⟩ ≠ dispatchGood ⟨0, 0⟩ := by decide

/-- 且错误只在 flag=0 的 A 类上发作 —— "主判别式必须在最外层"的
    机器形态:两分派在 kind=1 与 (kind=0,flag=1) 上一致。 -/
theorem dispatch_agrees_elsewhere :
    dispatchBad ⟨0, 1⟩ = dispatchGood ⟨0, 1⟩
  ∧ dispatchBad ⟨1, 0⟩ = dispatchGood ⟨1, 0⟩
  ∧ dispatchBad ⟨1, 1⟩ = dispatchGood ⟨1, 1⟩ := by decide

end WitCert.Adequacy
