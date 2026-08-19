# -*- coding: utf-8 -*-
"""批量文本编辑:**逐条**校验命中数,不给"整批变了没有"这种判据留位置。

为什么存在(2026-08-08):一次论文批改写成"三处 `s.replace(...)` + 一句
`assert s != o`"。其中一处因换行不同没命中,另外两处命中了,于是 `s != o`
成立、断言通过、提交信息宣称三处都改了 —— 实际漏一处,下一轮评审才发现。

逻辑内核不是手滑,是**量词降级**:做出的断言是 `∃ 处改变`,而需要的是
`∀ 处命中`。一个存在性观测对全称义务零信息 —— 观测到"有变化"与"某条没
命中"完全相容,正因如此它做不了判据。同族在本项目还有三例(聚合 odds
ratio vs 逐深度组、端点累计 vs 逐步、"批量改了 canon" vs 每条都重生成)。
形式化在 `formal/WitCert/BatchEdit.lean`:
  * `applyAll_isSome_iff_allHit` —— 正确判据的形式;
  * `changed_but_not_all_applied` —— 反例:`结果 ≠ 原文` 推不出全称;
  * `one_hit_masks_many_misses` —— 批量越大该判据越无力;
  * `overlap_makes_order_matter` —— "每条至少命中一次"仍不够,还要恰好一次。

闭环边界(诚实说明):Lean 看不见 Python,已提交代码里该反模式实例数为 0
(它只活在用完即弃的临时脚本里),所以**没有**可扫描的产物、也就不该加
扫描守卫 —— 那会是装饰品。真正让规则生效的是本文件:把逐条校验做成唯一
可用的形态,再用 `tests/test_textedit.py` 守住本文件自己的行为。

    from textedit import apply_edits
    apply_edits("papers/x/main.tex", [
        ("旧句一", "新句一"),
        ("旧句二", "新句二", 2),      # 第三项 = 期望命中数,默认 1
    ])

任何一条命中数与期望不符 → 抛 `EditMissError`,**且不落盘**(避免半改状态)。
"""
from __future__ import annotations

import io
import os


class EditMissError(AssertionError):
    """某条编辑的命中数与期望不符。带上全部条目的实际命中数,便于一次修完。"""


def plan_edits(text, edits):
    """只算不改:返回 [(序号, 期望, 实际)],供调用方在落盘前自查。"""
    out = []
    for i, e in enumerate(edits):
        pat, _rep = e[0], e[1]
        want = e[2] if len(e) > 2 else 1
        out.append((i, want, text.count(pat)))
    return out


def apply_edits(path, edits, encoding="utf-8", dry_run=False):
    """对 `path` 施加 `edits`;**每一条**都必须恰好命中期望次数。

    `edits`:`(pattern, replacement)` 或 `(pattern, replacement, expected_count)`。
    先整批校验、全部通过才写盘 —— 中途抛异常留下半改文件是另一条踩过的坑
    (CLAUDE.md 铁律 8:批量修改先全部断言再统一写盘)。
    返回实际写入的文本。
    """
    with io.open(path, encoding=encoding) as fh:
        text = orig = fh.read()

    plan = plan_edits(text, edits)
    bad = [(i, w, g) for (i, w, g) in plan if w != g]
    if bad:
        lines = [
            f"  #{i}: 期望命中 {w} 次,实际 {g} 次 —— {edits[i][0][:60]!r}"
            for (i, w, g) in bad
        ]
        raise EditMissError(
            f"{path}: {len(bad)}/{len(edits)} 条编辑命中数不符,**未写盘**。\n"
            + "\n".join(lines)
            + "\n(为什么逐条查:`assert 文本变了` 是存在性观测,一条命中就能"
              "让它通过 —— 见 formal/WitCert/BatchEdit.lean 的 "
              "changed_but_not_all_applied)"
        )

    for e in edits:
        pat, rep = e[0], e[1]
        cnt = e[2] if len(e) > 2 else 1
        text = text.replace(pat, rep, cnt)

    # 重叠检查:逐条命中数对了,但前一条的替换文本可能制造/吃掉后一条的模式
    # (BatchEdit.overlap_makes_order_matter)。这里给一个**可判**的必要条件:
    # 依次应用之后,每条模式不应仍以原命中数存在(否则它其实没被替换掉)。
    # **追加型编辑是合法的**:替换文本里含有原模式(在原行后面接一段)时,
    # 应用后模式当然还在 —— 那不是残留。只在替换**不含**原模式时才查。
    # (2026-08-08 首次真实使用即命中:三条追加型编辑被误判为重叠。)
    residue = [(i, e[0]) for i, e in enumerate(edits)
               if e[0] and e[0] not in (e[1] if len(e) > 1 else "")
               and text.count(e[0]) >= (e[2] if len(e) > 2 else 1)]
    if residue:
        raise EditMissError(
            f"{path}: 应用后仍有模式残留(编辑之间可能重叠/相互制造),**未写盘**:"
            + "; ".join(f"#{i} {p[:40]!r}" for i, p in residue)
        )

    if text == orig:
        raise EditMissError(f"{path}: 全部编辑命中但文本未变 —— 替换与原文相同?")
    if not dry_run:
        tmp = path + ".textedit.tmp"
        # **保留原文件权限**(2026-08-09 事故 textedit-drops-exec-bit):os.replace
        # 换上的是新建的临时文件,其模式来自 umask —— 于是任何被本工具编辑过的
        # .sh 都会**静默**丢掉 +x。tools/runx.sh 与 ruler_ab.sh 就是这样在两次
        # 提交里从 100755 变成 100644 并被推上去,几小时后才以 "Permission
        # denied" 现形。原子性不该以丢元数据为代价。
        try:
            _mode = os.stat(path).st_mode
        except OSError:
            _mode = None
        with io.open(tmp, "w", encoding=encoding) as fh:
            fh.write(text)
        if _mode is not None:
            os.chmod(tmp, _mode & 0o7777)
        os.replace(tmp, path)          # 原子替换,不留半改状态
    return text
