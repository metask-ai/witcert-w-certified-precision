/- 发布协议正门:整条事件迹合法 + 本次推送尝试合法,`by decide` 编译失败
   即拒绝。数据由 tools/release_export.py 生成(ReleaseProtocolData.lean);
   挂载点:tools/push_release.sh 推送前。
   不得 import 进 WitCert 根 —— 工程层,不计入论文定理数。-/
import WitCert.ReleaseProtocolData

namespace WitCert.Release

theorem journal_conforms : protocolOk journal = true := by decide

theorem pending_attempt_legal : pendingOk = true := by decide

end WitCert.Release
