/- 发布正门:每篇快照的四条接缝不变量,`by decide` 编译失败 = 不许出包。
   数据由 tools/release_export.py 机械导出(ReleaseData.lean);
   挂载点:make_release.py 出包关(--check 与落盘前各一次)。
   不得 import 进 WitCert 根 —— 工程层,不计入论文定理数。-/
import WitCert.ReleaseData

namespace WitCert.Release

theorem p1_release_publishable : publishable snapshot_p1 = true := by decide

theorem p2_release_publishable : publishable snapshot_p2 = true := by decide

-- 2026-08-14:此前只有 p1/p2 两条,而 release_export 的 SLUGS 也只硬编码这两篇 ——
-- `make_release.py p4 --check` 跑的正门里根本没有 p4:检查跑了、判词也给了,
-- 判的是别人。SLUGS 改为按 papers/*/RELEASE.toml 通配后,这里必须同步补齐,
-- 否则新快照导出了却无人裁决(装饰品的另一种形态)。
theorem p3_release_publishable : publishable snapshot_p3 = true := by decide

theorem p4_release_publishable : publishable snapshot_p4 = true := by decide

end WitCert.Release
