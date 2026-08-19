# -*- coding: utf-8 -*-
"""每页版面密度检查:正文每一页至少有一个图、表或块状公式。

为什么要有(2026-08-09):这条是用户提的硬排版要求,我手工调完当时是满足的,
但**任何一次正文增删都会移动分页**——加了第九个模型的三段话之后,又有 8 个
正文页退化成纯文字,而没有任何信号。排版属性和数字一样,靠人眼复查必然漂移。

判据(直接信号,读**编译产物** main.pdf 而不是 .tex):
  逐页取 pdftotext -layout,页内命中以下任一即算合格 ——
    · 图/表标题        "Figure N" / "Table N"
    · 带号公式          右边距上孤立的 "(N)"
    · 块状公式          缩进起行且含数学符号的行
豁免只有两类,且必须写明理由:标题/摘要页(无版心可放浮动体)、参考文献页。

python3 tools/check_page_density.py papers/p3-witcert-v
"""
import os
import re
import subprocess
import sys

# 豁免:页码 -> 理由。**只允许这两类**,新增豁免要在此写清为什么。
EXEMPT_KINDS = {
    "title": "标题/摘要页:版心被标题占据,浮动体会挤掉摘要",
    "refs": "参考文献页:按条目排版,不放浮动体",
}


def _extract(pdf, layout):
    cmd = ["pdftotext"] + (["-layout"] if layout else []) + [pdf, "-"]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        print("pdftotext 失败:", out.stderr.strip()[:200])
        sys.exit(2)
    return out.stdout.split("\f")


def page_texts(pdf):
    """返回 [(layout 文本, 阅读序文本)] —— **两种抽取都要**。

    2026-08-14:检查器此前只用 `-layout`,那是按单栏标定的。双栏文档下
    `-layout` 把两栏并排铺开,图注前面顶着另一栏的正文,`^\\s*(Figure|Table)`
    永远匹配不上 —— p3 的 MLSys 版因此被报 11 个"裸页",而实测那些页里
    有 "Table 2. Five routes..."。不加 -layout 的阅读序抽取里图注恰好在行首。
    反过来,带号公式的判据依赖列位置(编号 `(N)` 贴右边距、多行公式收尾行缩进
    很深),只有 -layout 保得住。所以两种各管一段,取并集 —— 而不是二选一。

    页数必须对齐才敢按下标配对;不对齐就退回只用 layout(宁可误红不误绿)。
    """
    lay = _extract(pdf, True)
    plain = _extract(pdf, False)
    if len(plain) != len(lay):
        plain = lay
    return list(zip(lay, plain))


_REL = "=≤≥≈≪≫∈→"   # **关系**符号,散文极少出现


#: 图注:`Figure 3: The k-law…`(article)或 `Table 2. Five routes…`(MLSys)。
#: 必须是**图注**而不是正文里的引用 —— `Table~\ref{}` 渲染出来也是 "Table 1",
#: 只按名字匹配会把"某页提到了表 1"当成"某页有表 1"(2026-08-09 自查:p4 就是
#: 靠一句引用判绿的)。约束三条:行首起、编号后接 `:` 或 `.`、其后首字母大写且
#: 同行还有 ≥15 个字符(真图注的首行是长的;"…in Table 5. The next…" 这类断行
#: 引用即使碰巧落在行首,也很少能同时满足大写+长尾)。
CAPTION = re.compile(r"^[ \t]*(Figure|Table)[ ]+\d+[.:][ ]+[A-Z][^\n]{15,}", re.M)


def classify(layout, plain=None):
    """返回该页命中的版面元素集合。

    检测口径按本文实际排版**标定过**,不靠想当然:块公式一律 equation 环境
    (故必带编号),pdftotext -layout 下编号 `(N)` 与公式**同行**、缩进只有 4 个
    空格 —— 早先那版要求"编号独占一行 + 缩进 ≥40"两条都不成立,于是把明明
    有块公式的页判成裸页(2026-08-09 自查抓出:检查器自己的假信号)。

    图注在**阅读序**文本里找(双栏下 -layout 会让图注前面顶着另一栏的正文),
    公式在 **layout** 文本里找(它依赖列位置)。见 page_texts 的说明。
    """
    hits = set()
    texts = [layout] + ([plain] if plain is not None else [])
    for t in texts:
        if CAPTION.search(t):
            hits.add("float")
        for ln in t.split("\n"):
            if not re.search(r"\(\d{1,2}\)\s*$", ln):
                continue
            # **整行只有一个编号** = 块公式的编号行。散文不会有这样的行,所以这
            # 是最强的一档信号,且不依赖缩进。必须先剥掉抽取带来的控制字符
            # (\x02/\x03 之类):它们不是空白,`lstrip()` 不认,于是缩进判据在
            # 双栏 PDF 上恒为 0 —— 前一版加了"两种抽取都看"却仍全灭,就是被这个
            # 吃掉的。debug 到字节级才看见。
            core = re.sub(r"[\s\x00-\x1f ]", "", ln)
            if re.fullmatch(r"\(\d{1,2}\)", core):
                hits.add("eqnum")
                break
            # 同行含关系符(公式本体与编号同行),或编号缩进很深(多行公式的
            # 收尾行)。**两种抽取都要看**:双栏的 -layout 下编号后面顶着另一栏
            # 的正文,行尾判据永远不成立 —— p3 的 MLSys 版 p2/p10/p16 明明各有
            # 一个带号公式((2)/(16)(17)/(23)),却被判成裸页。阅读序抽取里
            # 编号回到行尾;缩进在那里没有意义,靠关系符兜住。
            if any(c in ln for c in _REL) or (len(ln) - len(ln.lstrip())) >= 20:
                hits.add("eqnum")
                break
    return hits


def is_refs(text):
    """参考文献页。**两处判据必须共用它** —— 2026-08-13 挂了 bibliography 之后,
    裸页判据豁免了 refs、而文末堆积判据没有,于是参考文献页(自然没有正文段落、
    自然在正文之后)被判成"被推到文末的浮动体"。一个概念两处实现,迟早分叉。"""
    return bool(re.search(r"^\s*References\s*$", text, re.M)) or \
        len(re.findall(r"^\[\d+\]", text, re.M)) >= 3


def refs_from(pages):
    """参考文献**首页**的页号(1-based),没有则返回 None。

    2026-08-14:p3 改完引言后条目多溢出一页,最后一页只剩 1 条 `[16]` ——
    逐页判据要求 heading 或 ≥3 条,于是这一页被判成裸页。文献表在
    \\end{document} 前、是全文最后一块,所以正确判据是**从它开始到结尾全部豁免**,
    而不是逐页猜。边界:若将来有附录排在 bibliography 之后,这条会连带豁免它 ——
    本仓库三篇都不是这个顺序,真出现时这里要改。"""
    for i, t in enumerate(pages, 1):
        if re.search(r"^\s*References\s*$", t, re.M):
            return i
    # 作者-年份体例(mlsys2026.bst)既没有 `[N]` 也不打印 "References" 标题 ——
    # p3 的 MLSys 版最后一页因此被判成裸页。回退判据:**从末页往前**数,只要
    # 该页像文献条目(≥3 处 arXiv 号或 "作者. 标题. 年." 的年份结尾)就继续。
    # 只允许从尾部生长,所以正文中间一页恰好引了三个 arXiv 号也不会被误豁免 ——
    # 豁免是"判绿",这个方向的误判比误红危险得多,判据必须只能从尾部长出来。
    shaped = re.compile(r"arXiv:\d{4}\.\d{4,5}|,\s*(?:19|20)\d\d\.\s*$", re.M)
    idx = [i for i, t in enumerate(pages, 1) if t.strip()]
    start = None
    for i in reversed(idx):
        if len(shaped.findall(pages[i - 1])) >= 3:
            start = i
        else:
            break
    return start


def has_body_text(text):
    """该页是否有正文段落(而非只有浮动体)。

    正文行的特征是**顶格且长**;图注是缩进的,表格单元格是短的。阈值按本文
    版心标定:正文行宽约 72-78 字符,取 55 做下限,要求至少 6 行。
    """
    return sum(1 for ln in text.split("\n")
               if len(ln) >= 55 and not ln.startswith(" ")) >= 6


def _selftest():
    """判据变异检验:今天为了适配双栏放宽了四条判据(图注标点、双抽取取并集、
    整行编号、作者-年份文献表),**放宽的方向就是误绿的方向**。所以每条都要有
    一个能让它判红的输入,并且必须验证反例不被吞掉。"""
    fails = []

    def ck(cond, why):
        if not cond:
            fails.append(why)

    # ① 纯散文页必须判裸(否则检查器恒绿)
    prose = ("This paragraph mentions Table 5 and Figure 2 in passing, and even\n"
             "says see Table 7. the range there is wide, but contains no float.\n")
    ck(classify(prose, prose) == set(), "纯散文页未判裸 —— 检查器恒绿")
    # ② 引用不等于图注:必须首字母大写 + 同行长尾
    ck(classify("in Table 5. The next section\n") == set(),
       "把正文里的表引用当成了图注")
    # ③ 两种图注标点都要认(article `:` / MLSys `.`)
    ck("float" in classify("Table 2: Five routes to the same number here\n"),
       "冒号式图注漏认")
    ck("float" in classify("Table 2. Five routes to the same number here\n"),
       "句点式图注漏认(MLSys 体例)")
    # ④ 整行只有编号 = 块公式;控制字符不得吃掉它
    ck("eqnum" in classify("\x02      \x03            (16)\n"),
       "整行编号漏认(控制字符吃掉了判据)")
    ck(classify("are not covered by (27)\n") == set(),
       "把正文里对公式的引用当成了块公式")
    # ⑤ 文献表只能从尾部生长 —— 中间一页引三个 arXiv 号不许被豁免
    mid = "see arXiv:2506.13329, arXiv:2505.03804 and arXiv:2603.02217 here\n"
    ck(refs_from([mid, "body\n", "body\n"]) is None,
       "文献表判据从中间页生长 —— 会把正文页误豁免(误绿)")
    ck(refs_from(["body\n", mid, mid]) == 2, "尾部文献表未被识别")
    if fails:
        print("PAGE DENSITY SELFTEST FAILED:")
        for f in fails:
            print("   " + f)
        sys.exit(1)
    print("PAGE DENSITY SELFTEST PASSED(8 项:裸页可判红、引用不冒充图注、"
          "两种标点均认、整行编号认、文献表只从尾部生长)")


def main():
    if "--selftest" in sys.argv:
        return _selftest()
    paper = sys.argv[1] if len(sys.argv) > 1 else "papers/p3-witcert-v"
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    pdf = os.path.join(root, paper, "main.pdf")
    tex = os.path.join(root, paper, "main.tex")
    if not os.path.exists(pdf):
        print(f"PAGE DENSITY: {paper} 未编译,跳过")
        return
    # **读产物就必须先证明产物是新的**:否则改完 tex 不重编,这里读的是旧 PDF,
    # 判绿说明的是上一版的版面(pdflatex 静默失败那次事故的同一形状)。
    if os.path.getmtime(pdf) < os.path.getmtime(tex):
        print(f"PAGE DENSITY FAILED({paper}):main.pdf 比 main.tex 旧 —— "
              f"读的是上一版版面。先跑 tools/build_paper.sh {paper}")
        sys.exit(1)
    pairs = page_texts(pdf)
    pages = [lay for lay, _ in pairs]
    # 文献表首页同样要两种抽取都找 —— 双栏下 `References` 标题前面顶着另一栏
    # 的正文,`^\\s*References\\s*$` 在 -layout 里匹配不上。取两者的较早者。
    _r = [x for x in (refs_from(pages), refs_from([pl for _, pl in pairs]))
          if x]
    rf = min(_r) if _r else None
    bare = []
    n = 0
    for i, (lay, plain) in enumerate(pairs, 1):
        if not lay.strip():
            continue
        n += 1
        if i == 1:
            continue                      # title:见 EXEMPT_KINDS
        if is_refs(lay) or is_refs(plain) or (rf and i >= rf):
            continue                      # refs:见 EXEMPT_KINDS
        if not classify(lay, plain):
            bare.append(i)
    if bare:
        print(f"PAGE DENSITY FAILED({paper}):{len(bare)}/{n} 页无图/表/块公式")
        print("   页码:" + ", ".join(str(b) for b in bare))
        print("   修法:把该页附近最复杂的行内公式提成块状,或把成组数字提成表")
        sys.exit(1)
    # **反向失效**:每页都有浮动体,却是因为 LaTeX 把排不下的 float 全堆到文末。
    # 2026-08-09 实测:20 个 float 在默认参数下有 10 页被推到正文之后 —— 上面那条
    # 判据对此完全无感(那些页当然"有图"),所以必须单独查。
    tail = [i for i in range(1, len(pages) + 1)
            if pages[i - 1].strip() and not has_body_text(pages[i - 1])
            and not is_refs(pages[i - 1]) and not (rf and i >= rf)]
    last_body = max((i for i in range(1, len(pages) + 1)
                     if pages[i - 1].strip() and has_body_text(pages[i - 1])),
                    default=0)
    deferred = [i for i in tail if i > last_body]
    if deferred:
        print(f"PAGE DENSITY FAILED({paper}):{len(deferred)} 页浮动体被推到正文"
              f"之后(正文止于 p{last_body})")
        print("   页码:" + ", ".join(str(d) for d in deferred))
        print("   修法:放宽 topfraction/textfraction/totalnumber,或改用 [!htbp]")
        sys.exit(1)
    print(f"PAGE DENSITY PASSED({paper}):{n} 页,正文每页均有图/表/块公式"
          f"(豁免 标题页、参考文献页);无浮动体堆积在文末")


if __name__ == "__main__":
    main()
