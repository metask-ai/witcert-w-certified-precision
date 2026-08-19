#!/bin/bash
# WitCert 形式化 CI 闸门:零依赖检查四个核心定理(秒级,无需 Mathlib)。
# 任何"更便宜的等价形式"提案必须先让本脚本通过。
set -e
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
FILES="standalone/Refinement.lean standalone/Factorial.lean standalone/Budget.lean standalone/EForm.lean standalone/Generation.lean"
FAIL=0
for f in $FILES; do
  OUT=$(lean "$f" 2>&1) || { echo "[$f] 编译失败"; echo "$OUT"; FAIL=1; continue; }
  if echo "$OUT" | grep -q "error"; then echo "[$f] FAIL 编译错误"; echo "$OUT"; FAIL=1; continue; fi
  if echo "$OUT" | grep -q "sorryAx"; then echo "[$f] FAIL 证明依赖 sorryAx"; echo "$OUT"; FAIL=1; continue; fi
  N=$(echo "$OUT" | grep -c "depends on axioms\|does not depend on any axioms" || true)
  echo "[$f] PASS ($N 个定理已机器检查)"
done
[ $FAIL -eq 0 ] && echo "=== 全部通过:L1核心/L2核心/L3核心/L4 refinement 均无 sorryAx ===" || exit 1
