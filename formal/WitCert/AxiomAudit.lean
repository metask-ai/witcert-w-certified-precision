/- 公理审计:环境内全量自审 —— 编译本文件即审计通过。

  动机(2026-08-06 发布链评审,三处实锤):
  1. check_all.sh 的主闸 `lake build | grep sorry && fail` 管道退出码不门控
     (`set -e` 豁免 `&&` 左侧),**编译错误静默放行**;
  2. `#print axioms` 清单手抄 9 条,与两篇论文主定理集(MAIN ∪ MAIN2)
     交集不完整 —— 论文2 的 14 条主定理无一显式审计;
  3. tools/lean_extract.py 的 sorryAx 断言只作用于论文1 的 items。

  本文件把闸门搬进内核:遍历环境内全部 `WitCert.*` 定理(两篇论文的
  Mathlib 层全量,不是抽样),`collectAxioms` 必须 ⊆ 三条标准公理,
  违者 `throwError` → 编译失败 → `lake build WitCert.AxiomAudit` 红。
  shell 只需判这一条 build 的退出码,不再依赖 grep 文本。

  覆盖边界(诚实说明):只审 `import WitCert` 可见的模块(= 论文定理的
  全量真理源);零依赖层由 check_standalone.sh 单独审;Adequacy/KeyIdentity/
  Adjudication 工程层由 check_all.sh 单独 build。
  本文件不得 import 进 WitCert 根 —— 工程层,不计入论文定理数。-/
import Lean
import WitCert

open Lean Elab Command

namespace WitCert.AxiomAudit

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def audit : CommandElabM Unit := do
  let env ← getEnv
  let mut audited := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    if (`WitCert).isPrefixOf n && !n.isInternal then
      match ci with
      | .thmInfo _ =>
          let axs ← liftCoreM (collectAxioms n)
          let extra := axs.toList.filter (fun a => !stdAxioms.contains a)
          if !extra.isEmpty then
            bad := bad.push (n, extra)
          audited := audited + 1
      | _ => pure ()
  if !bad.isEmpty then
    throwError "公理审计失败:{bad.size} 条定理依赖非标准公理(sorryAx 亦在此列):{bad.toList}"
  logInfo m!"AxiomAudit PASS:{audited} 条 WitCert.* 定理,公理依赖全部 ⊆ {stdAxioms}"

run_cmd audit

end WitCert.AxiomAudit
