#!/bin/bash
# 编论文并**真的**判红。
# 2026-08-08 事故:main.tex 引了本机未装的 hyphenat,pdflatex 每次都以
# "Fatal error occurred, no output PDF file produced!" 结束,而
# `grep -c Overfull main.log` 返回 0(日志里根本走不到排版阶段)被读成
# "0 overfull";`pdfinfo main.pdf | grep Pages` 读的是十小时前的旧 PDF。
# 于是"20 页 0 overfull"连报四次,全是假的。
# 判据一律用**直接信号**:PDF 的 mtime 必须前进,日志不得含 Fatal/未定义引用。
set -o pipefail
D=${1:?用法: build_paper.sh <papers/xxx 目录>}
cd "$D" || exit 2
BEFORE=$(stat -f %m main.pdf 2>/dev/null || echo 0)
# 参考文献(2026-08-13):正文挂了 \bibliography 就必须真的跑 bibtex,否则
# 每条 \cite 都会留下 "undefined citation" —— 而下面的 UND 判据正是查这个,
# 所以漏跑 bibtex 会**判红**而不是静默放行。bibtex 自身的失败也要判红:
# 它退出码非 0 时 .bbl 可能是空的或半截的,而 pdflatex 照样出 PDF。
fail=0
pdflatex -interaction=nonstopmode main.tex >/dev/null 2>&1
if grep -q '\\bibliography{' main.tex 2>/dev/null; then
  if ! bibtex main >/tmp/bibtex_$$.log 2>&1; then
    echo "FAILED: bibtex 失败:"; tail -8 /tmp/bibtex_$$.log; fail=1
  fi
  # bibtex 对"引了但 .bib 里没有"只报 warning、退出码仍是 0 —— 间接信号,
  # 必须显式查(否则参考文献表里悄悄少一条,正文显示 [?])。
  if grep -qi "didn't find a database entry\|I couldn't open database" /tmp/bibtex_$$.log 2>/dev/null; then
    echo "FAILED: bibtex 有找不到的条目:"; grep -i "didn't find\|couldn't open" /tmp/bibtex_$$.log | head -5; fail=1
  fi
  rm -f /tmp/bibtex_$$.log
fi
for i in 1 2 3; do pdflatex -interaction=nonstopmode main.tex >/dev/null 2>&1; done
AFTER=$(stat -f %m main.pdf 2>/dev/null || echo 0)
if [ "$AFTER" -le "$BEFORE" ]; then
  echo "FAILED: main.pdf 未更新(mtime $BEFORE -> $AFTER)—— 编译没真的产出"; fail=1
fi
if grep -q "Fatal error occurred" main.log 2>/dev/null; then
  echo "FAILED: 日志含 Fatal error:"; grep -B2 "Fatal error occurred" main.log | head -6; fail=1
fi
if grep -qE "^! " main.log 2>/dev/null; then
  echo "FAILED: 日志含 LaTeX 错误:"; grep -E "^! " main.log | head -5; fail=1
fi
# grep -c 无匹配时返回码 1;`|| echo 0` 会把 "0" 追加到已打印的 "0" 后面 ——
# 变成 "0\n0" 再喂给 [ -gt ] 就报 integer expression expected(本脚本首跑即中)。
UND=$(grep -c "undefined" main.log 2>/dev/null; true)
OVF=$(grep -c "Overfull" main.log 2>/dev/null; true)
UND=${UND:-0}; OVF=${OVF:-0}
PGS=$(pdfinfo main.pdf 2>/dev/null | awk '/^Pages/{print $2}')
[ "$fail" = 1 ] && exit 1
echo "OK: $D -> ${PGS} 页, Overfull ${OVF}, undefined ${UND}"
[ "$UND" -gt 0 ] && { echo "FAILED: 有未定义引用"; exit 1; }
# Overfull 此前只**打印**不门控 —— p1 就这样带着 7 处过了一个多月,直到用户问起
# (2026-08-16)。只报不判的数必然漂移,这是本项目反复吃过的亏。六份正文现已全部
# 归零,故上闸:任何一处溢出即判红。改稿中途想暂时放行用 WC_ALLOW_OVERFULL=1。
if [ "$OVF" -gt 0 ] && [ "${WC_ALLOW_OVERFULL:-0}" != 1 ]; then
  echo "FAILED: ${OVF} 处 Overfull(文字探出版心)。定位:"
  grep -n "Overfull" main.log | head -5
  echo "  常见修法:长 \\texttt/URL 给 \\allowbreak;标题设 \\raggedright;"
  echo "  宽表用 \\resizebox 或改 p{} 列;宽公式在 \\qquad 处拆行。"
  echo "  确需暂时放行:WC_ALLOW_OVERFULL=1 bash \"$0\" $D"
  exit 1
fi
exit 0
