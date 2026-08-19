/- 发布不变量演算(工程管理的形式化层,续裁决演算谱系)。

  动机(2026-08-06 发布链评审,四事故全部实锤,详见 tools/incidents.py):
  发布链的每个守卫都盖住"声明↔事实"的一段,而失效全部发生在**接缝**:
  判定口径与执行口径分家(集群账号名上网)、脚本发了传递依赖没发
  (check_all.sh 在公开仓必死)、附录行号静默落 0 却声称 resolve、
  仓名字面量与清单无绑定(p1 附录印成 p2 仓名)。

  本文件把四条接缝做成可判定命题:
  · 数据由 tools/release_export.py 从清单/论文/脚本机械导出
    (WitCert/ReleaseData.lean,不许手写);
  · 正门在 ReleaseGate.lean:`publishable snapshot = true := by decide`,
    编译失败 = 不许出包(挂进 make_release 出包关);
  · 本文件的负例定理把历史事故编成"该状态被演算拒绝"——事故不再是
    散文教训,是构造不出的反例。

  零外部依赖(core Lean),全部 `by decide`。
  不得 import 进 WitCert 根 —— 工程层,不计入论文定理数。-/

namespace WitCert.Release

/-- 论文/README 对读者承诺的一次调用:路径 + 是否真的在发布清单内。 -/
structure Ref where
  path    : String
  shipped : Bool
  deriving Repr, DecidableEq

/-- 发布快照:四条接缝各一读数,由导出器对**将要公开的内容**实算。 -/
structure Snapshot where
  /-- 模拟真实落盘变换(该扩展名会被脱敏则脱敏,否则原样)后,
      对输出内容与目标路径名复扫 LEAK_PATTERNS 的**残余**命中数。
      端态判据:不管判定/执行在代码里怎么绕,出包内容命中必须为 0。 -/
  residualLeaks : Nat
  /-- 随包脚本与 README 的裸调用路径(`[ -f` 守卫下的显式 SKIP 不计)。 -/
  refs : List Ref
  /-- 附录定理清单的源行号;0 = 解析失败(却对读者声称 resolve)。 -/
  thmLines : List Nat
  /-- 论文 tex 中每次出现的 github 仓名 × 清单 [repo] name。 -/
  repoNames : List (String × String)
  /-- collect() 的 dest 映射冲突数:两个源文件映射到同一目标路径 =
      后者静默覆盖前者(p124b 产物覆盖事故的清单版)。 -/
  destCollisions : Nat := 0
  /-- dist 终验执行期间,monorepo 内、发布包外的文件读取数(audit hook 实测)。
      非零 = 发布包对私有仓有隐性依赖:本机能跑,读者 clone 必挂。 -/
  dynOutsideReads : Nat := 0
  deriving Repr

def leakFree (s : Snapshot) : Bool := s.residualLeaks == 0

def promisesClosed (s : Snapshot) : Bool := s.refs.all (·.shipped)

def locatable (s : Snapshot) : Bool := s.thmLines.all (0 < ·)

def repoNamesBound (s : Snapshot) : Bool :=
  s.repoNames.all fun p => p.1 == p.2

def destsUnique (s : Snapshot) : Bool := s.destCollisions == 0

def selfContained (s : Snapshot) : Bool := s.dynOutsideReads == 0

/-- 出包总判据:六条接缝全部闭合。 -/
def publishable (s : Snapshot) : Bool :=
  leakFree s && promisesClosed s && locatable s && repoNamesBound s
    && destsUnique s && selfContained s

/-! ## 负例:2026-08-06 的四个实锤事故,在本演算下构造不出 -/

/-- 事故一(泄露双口径):`.list` 按 `.json` 口径判"可改写"放行,落盘按
    源扩展名走 copy 分支 —— 集群账号名 7 处上公网。端态复扫残余 = 7 ≠ 0。 -/
theorem dual_caliber_leak_rejected :
    publishable { residualLeaks := 7, refs := [], thmLines := [], repoNames := [] }
      = false := by decide

/-- 事故二(承诺未闭包):论文附录让读者跑 check_all.sh,它调用的
    ../tests/test_incident_coverage.py 不在清单 —— p1 前科(漏 check_all.sh
    本体)的同型复发:上次补了脚本,没补脚本的传递依赖。 -/
theorem missing_transitive_dep_rejected :
    publishable { residualLeaks := 0,
                  refs := [⟨"tests/test_incident_coverage.py", false⟩],
                  thmLines := [], repoNames := [] } = false := by decide

/-- 事故三(行号落 0):locate() 兜底 `(?, 0)` 静默照印,p1 附录 10 处
    `standalone/*.lean:0`,同页写着 "the file:line references below resolve"。 -/
theorem line_zero_rejected :
    publishable { residualLeaks := 0, refs := [], thmLines := [72, 0],
                  repoNames := [] } = false := by decide

/-- 事故四(仓名漂移):p1 附录仓名硬编码成 p2 的 `witprobe-attention-memory`,
    三处字面量与 RELEASE.toml [repo] name 之间无任何机器绑定。 -/
theorem repo_name_drift_rejected :
    publishable { residualLeaks := 0, refs := [], thmLines := [],
                  repoNames := [("witprobe-attention-memory",
                                 "witcert-kv-certificates")] } = false := by decide

/-- 事故五(2026-08-06 CI 首跑双红的结构化):随包 Python 的传递依赖
    (figprint import / baseline json)不在清单 —— 本机 dist 终验能"读到
    monorepo 的文件"这一事实,恰是 selfContained 要判红的形态。 -/
theorem outside_dependence_rejected :
    publishable { residualLeaks := 0, refs := [], thmLines := [],
                  repoNames := [], dynOutsideReads := 2 } = false := by decide

/-- 事故六(前瞻负例,p124b 产物覆盖的清单版):两个源文件经前缀剥离
    映射到同一 dest,copy 静默 last-wins。 -/
theorem dest_collision_rejected :
    publishable { residualLeaks := 0, refs := [], thmLines := [],
                  repoNames := [], destCollisions := 1 } = false := by decide

/-- 正向样例:全部接缝闭合才可出包(演算自身的可满足性见证)。 -/
theorem publishable_example :
    publishable { residualLeaks := 0, refs := [⟨"formal/check_all.sh", true⟩],
                  thmLines := [72, 173], repoNames :=
                  [("witcert-kv-certificates", "witcert-kv-certificates")] }
      = true := by decide

end WitCert.Release
