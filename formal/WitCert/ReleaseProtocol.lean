/- 发布协议迹演算:push 必须被"同摘要的 verify_ok"先行支配。

  动机(2026-08-06 事故 release-push-despite-failed-verify):dist 终验失败,
  但编排命令的管道吞掉退出码,带 .FAILED 的包被推上公开仓 —— "验证过什么"
  与"推送了什么"之间此前没有任何机器绑定。缺席型判据(.FAILED 不存在)
  还违反纪律 7(正向信号):make_release 在终验前崩溃同样留不下 .FAILED。

  本演算把发布史当作事件迹:
  · verify_ok slug digest —— make_release 全关通过后记入(digest 为包内容摘要);
  · verify_fail slug     —— 任一关失败时记入,清除该 slug 的已验证摘要;
  · push_ok slug digest  —— 推送完成后记入。
  合法性:每个 push_ok 时点,该 slug 当前已验证摘要恰等于所推摘要;
  attemptLegal 供 push_release 在推送**前**裁决本次尝试。
  数据(journal/pending)由 tools/release_export.py 从 dist/release_events.jsonl
  机械导出到 ReleaseProtocolData.lean;正门定理在 ReleaseProtocolGate.lean。

  零外部依赖,全部 `by decide`。不得 import 进 WitCert 根(工程层)。-/

namespace WitCert.Release

inductive Ev
  | verifyOk   (slug digest : String)
  | verifyFail (slug : String)
  | pushOk     (slug digest : String)
  deriving Repr, DecidableEq

/-- 各 slug 的"当前已验证摘要"表。 -/
abbrev VState := List (String × String)

def vset (st : VState) (k v : String) : VState :=
  (k, v) :: st.filter (fun p => p.1 != k)

def vdel (st : VState) (k : String) : VState :=
  st.filter (fun p => p.1 != k)

def vget (st : VState) (k : String) : Option String :=
  (st.find? (fun p => p.1 == k)).map (·.2)

def okFrom : VState → List Ev → Bool
  | _,  [] => true
  | st, .verifyOk s d :: rest => okFrom (vset st s d) rest
  | st, .verifyFail s :: rest => okFrom (vdel st s) rest
  | st, .pushOk s d :: rest => (vget st s == some d) && okFrom st rest

/-- 整条迹合法:每次推送都被同摘要验证先行支配。 -/
def protocolOk (j : List Ev) : Bool := okFrom [] j

/-- 迹结束时的已验证状态(与合法性无关地折叠)。 -/
def stateAfter (j : List Ev) : VState :=
  j.foldl (fun st e => match e with
    | .verifyOk s d => vset st s d
    | .verifyFail s => vdel st s
    | .pushOk _ _   => st) []

/-- 本次推送尝试合法:历史合法,且该 slug 当前已验证摘要 = 待推摘要。 -/
def attemptLegal (j : List Ev) (slug digest : String) : Bool :=
  protocolOk j && (vget (stateAfter j) slug == some digest)

/-! ## 负例:2026-08-06 的事故迹在本演算下构造不出 -/

/-- 事故本尊:终验失败后照推(管道吞码)。 -/
theorem push_after_failed_verify_rejected :
    protocolOk [.verifyFail "p2", .pushOk "p2" "d0"] = false := by decide

/-- 同族:验证的是 d1,推的是 d2(验证后内容又被改动)。 -/
theorem push_stale_digest_rejected :
    protocolOk [.verifyOk "p1" "d1", .pushOk "p1" "d2"] = false := by decide

/-- 同族:从未验证过的 slug 直接推。 -/
theorem push_unverified_rejected :
    attemptLegal [] "p1" "d1" = false := by decide

/-- 正向样例:验证-推送-再验证-再推送,同摘要支配即合法。 -/
theorem happy_path :
    protocolOk [.verifyOk "p1" "d1", .pushOk "p1" "d1",
                .verifyOk "p1" "d2", .pushOk "p1" "d2"] = true := by decide

end WitCert.Release
