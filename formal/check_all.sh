#!/bin/bash
# WitCert 形式化完整闸门:标准公理外无 sorryAx。
#
# 2026-08-06 重写(发布链评审三实锤):
# 1. 旧版 `lake build | grep sorry && fail` 管道退出码不门控(set -e 豁免
#    && 左侧)—— 编译错误静默放行。现全部改为 returncode 直判,杜绝
#    "grep 文本当判据"。
# 2. 公理审计不再手抄定理清单:WitCert/AxiomAudit.lean 在**内核里**遍历
#    环境全部 WitCert.* 定理逐条 collectAxioms(两篇论文全量),编译通过
#    即审计通过 —— 本脚本只判那一条 build 的退出码。
# 3. monorepo 工程层步骤(裁决数据重导出/事故归宿/键符合性)按存在性
#    显式 SKIP:公开仓 clone 里没有这些文件,读者跑到的是"证明+审计"
#    全量闸,而不是半路硬死。
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"

echo "=== 零依赖层(秒级) ==="
./check_standalone.sh

echo ""
echo "=== Mathlib 层(ℝ / 测度论):编译 ==="
lake build || { echo "FAIL: Lean 编译未通过"; exit 1; }

echo ""
echo "=== 公理审计(内核内全量,含 sorryAx 检查) ==="
lake build WitCert.AxiomAudit || { echo "FAIL: 存在非标准公理依赖(或审计模块编译失败)"; exit 1; }

echo ""
echo "=== 裁决演算(工程管理层,不计入论文定理数) ==="
if [ -f ../tools/adjudication_export.py ]; then
  # 数据由 tools/adjudication_export.py 从产物 JSON 机械导出;先重导出保证同步
  python3 ../tools/adjudication_export.py
else
  echo "SKIP: 裁决数据重导出(monorepo only;随包 AdjudicationData.lean 为发布时快照)"
fi
lake build WitCert.AdjudicationChain || { echo "FAIL: 裁决演算未通过"; exit 1; }
echo "裁决演算:premisesHold 全见证编译通过,负例拒绝定理成立"

lake build WitCert.Adequacy WitCert.KeyIdentity || { echo "FAIL: 仪器层演算未通过"; exit 1; }
echo "仪器层:观测充分性/键身份/非空洞/分派 全部机械判定通过"

lake build WitCert.ReleaseCalculus || { echo "FAIL: 发布演算未通过"; exit 1; }
echo "发布演算:四条接缝不变量 + 事故拒绝定理编译通过(正门在 make_release 出包关)"

# 事故归宿:每条方法性事故必须有归宿且归宿真实存在(规则库不许与目录分家)
if [ -f ../tests/test_incident_coverage.py ]; then
  python3 ../tests/test_incident_coverage.py || { echo "FAIL: 事故归宿"; exit 1; }
else
  echo "SKIP: 事故归宿守卫(monorepo only)"
fi
if [ -f ../tests/test_key_conformance.py ]; then
  python3 ../tests/test_key_conformance.py || { echo "FAIL: 键身份符合性"; exit 1; }
else
  echo "SKIP: 键身份符合性守卫(monorepo only)"
fi

echo ""
echo "=== 全部通过:L1/L2/L3/L4 主定理均已机器检查,无 sorryAx ==="
