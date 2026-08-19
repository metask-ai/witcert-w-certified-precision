"""论文3 图:由 experiments/out/*.json 程序化生成(不手画、不转录 —— 同 make_figs 原则)。

    python3 tools/p3_figs.py   -> papers/p3-witcert-v/figs/*.pdf + *.png

F1 界的紧度阶梯:①c 累计 served-TV 的三条 sound 界与实测值。讲的是"破 L∞ 墙" ——
   tanh(‖Δlogit‖∞) 空洞(0.996),而质量重叠度量(Hellinger)与纯方差度量
   (sub-Gaussian kernel)都非空洞,把实测 TV 夹在下面。
F2 γ_ℓ 饱和:传播常数真机探测的**负结果**。ρ=‖Δh‖²/‖δ‖² 若线性则与 eps 无关;
   实测两档 eps 的 ρ 相差 14.1 倍(≈能量比 16)⟹ 响应饱和,一阶线性化失效。
   这张图解释了主定理为何取 Doob 有界差分形态。
"""
import json
import math
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "experiments", "out")
P3, P4 = "p3-witcert-v", "p4-moe-protect"
FIG = os.path.join(ROOT, "papers", P3, "figs")
#: 图名 -> 归属论文。**save() 落盘与 figdata 路由共用它** —— 2026-08-14 之前
#: 只有 figdata 按篇分,PDF 一律写进 p3 的 figs/ 再手工拷到 p4,于是 p4/figs
#: 停在 8-10 而 p3 的已是 8-13(同一图两份、其中一份过期)。
OWNER = {}
for _p in (P3, P4):
    os.makedirs(os.path.join(ROOT, "papers", _p, "figs"), exist_ok=True)
plt.rcParams.update({"font.size": 9, "axes.spines.top": False,
                     "axes.spines.right": False,
                     "font.family": "STIXGeneral", "mathtext.fontset": "stix"})

FIGDATA = {}


def J(n):
    return json.load(open(os.path.join(OUT, n), encoding="utf-8"))


def save(fig, name, paper=None):
    paper = paper or P3
    OWNER[name] = paper
    d = os.path.join(ROOT, "papers", paper, "figs")
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(d, f"{name}.{ext}"), bbox_inches="tight", dpi=200)
    plt.close(fig)
    print(f"  {paper}/{name}.pdf/.png")


def f1_bound_ladder():
    """三条 sound 界 vs 实测(末位 served)。"""
    s = J("w3sle_eout_verdict.json")["summary"]
    items = [
        ("measured\n(realized TV)", s["TV_served_median"], "#333333"),
        (r"Bhattacharyya" + "\n" + r"$\sqrt{1-\mathrm{BC}^2}$",
         s["hellinger_served_median"], "#1b6ca8"),
        (r"sub-Gaussian" + "\n" + r"$\sigma/\sqrt{2}$",
         s["subg_kernel_tv_served_median"], "#2e8b57"),
        (r"$\tanh(\|\Delta\mathrm{logit}\|_\infty)$" + "\n(inherited)",
         s["cum_bound_tanh_served_median"], "#b03030"),
    ]
    # **按正文呈现精度落盘**:figdata 是"图⊆正文"的契约,存全精度会与正文的
    # 舍入值脱钩(守卫恒红)。图上标注也用同一精度 ⟹ 三者(图/figdata/正文)同源。
    FIGDATA["f1_bound_ladder"] = {
        "measured_TV": round(s["TV_served_median"], 3),
        "hellinger": round(s["hellinger_served_median"], 3),
        "subgaussian": round(s["subg_kernel_tv_served_median"], 3),
        "tanh_vacuous": round(s["cum_bound_tanh_served_median"], 3),
        "source": "experiments/out/w3sle_eout_verdict.json:summary",
    }
    fig, ax = plt.subplots(figsize=(4.6, 2.5))
    ys = range(len(items))
    ax.barh(list(ys), [v for _, v, _ in items],
            color=[c for _, _, c in items], height=0.62)
    for y, (_, v, _) in zip(ys, items):
        ax.text(v + 0.015, y, f"{v:.3f}", va="center", fontsize=8.5)
    ax.axvline(1.0, ls=":", lw=0.9, color="#999999")
    ax.text(1.0, len(items) - 0.35, " vacuous", fontsize=8, color="#999999",
            va="center")
    ax.set_yticks(list(ys)); ax.set_yticklabels([k for k, _, _ in items], fontsize=8)
    ax.set_xlim(0, 1.18); ax.set_xlabel("served total variation (per-request median)")
    ax.invert_yaxis()
    save(fig, "f1_bound_ladder")


def f2_gamma_saturation():
    """γ 探测的负结果:ρ 与 eps 强相关 ⟹ 饱和,非线性。"""
    g = J("w3gam_gamma_verdict.json")
    s, c = g["summary"], g["criteria"]
    FIGDATA["f2_gamma_saturation"] = {
        # 只登记**正文以同一写法出现**的量。ρ 的 min/max 在正文用科学记数
        # (4.07e-3 / 7.2e-5 / 4.9e-2),与 figdata 的十进制字符串比对必然错开 ——
        # 契约是"图上标注的数字正文都有",不是"逼正文迁就 json 的记数法"。
        # 图上标注与轴刻度不含这两个端点值,故不登记。
        "linearity_ratio_median": round(s["linearity_ratio_median"], 1),
        "n_nonlinear_pairs": c["n_nonlinear_pairs"],
        "noise_floor": c["noise_floor_dh2"],
        "source": "experiments/out/w3gam_gamma_verdict.json:summary",
    }
    # **两档 eps 各画一条**:线性区内两条应重合(ρ 与幅度无关),分离即饱和 ——
    # 图要呈现证据本身,不是把结论写成标注。
    be = g.get("rho_by_layer_by_eps") or {}
    eps_lv = [x.strip() for x in str(g.get("eps_levels", "")).split(",") if x.strip()]
    fig, ax = plt.subplots(figsize=(4.6, 2.4))
    cols = ["#1b6ca8", "#b03030"]
    for i, e in enumerate(sorted(be, key=int)):
        d = {int(k): v for k, v in be[e].items()}
        ks = sorted(d)
        lab = (r"$\varepsilon=%s$" % eps_lv[int(e)]) if int(e) < len(eps_lv) else f"eps {e}"
        ax.plot(ks, [d[k] for k in ks], marker="o", ms=2.4, lw=1.0,
                color=cols[i % 2], label=lab)
    ax.set_yscale("log")
    ax.set_xlabel("layer $\\ell$")
    ax.set_ylabel(r"$\rho_\ell=\|\Delta h\|^2/\|\delta\|^2$")
    ax.legend(fontsize=7.5, frameon=False, loc="upper right", ncol=2,
              handlelength=1.4, columnspacing=1.0)
    ax.text(0.02, 0.04,
            "linear response would superpose these curves",
            transform=ax.transAxes, fontsize=7.5, color="#555555")
    save(fig, "f2_gamma_saturation")


def f3_conformal_curve():
    """F3 换仪器:历史外推的**阈值—风险**前沿。

    留出 Clopper-Pearson 只给平面上**一个点**(而且是被支配的那个);顺序统计量
    给一条前沿:第 k 大分数当阈值 ⟹ 保证 k/(N+1)+α。同一批历史数据,不加任何
    新测量。图上把 CP 那个点画出来,是为了让"仪器错配"的代价可见,而不是修辞。
    """
    src = ("w3cf_multihist_verdict.json"
           if os.path.exists(os.path.join(OUT, "w3cf_multihist_verdict.json"))
           else "w3mh_multihist_verdict.json")
    d = J(src)["summary"]
    cur = d["conformal_curve"]
    xs = [c["risk_bound"] for c in cur]
    ys = [c["threshold"] for c in cur]
    fig, ax = plt.subplots(figsize=(3.3, 2.35))
    ax.plot(xs, ys, "o-", color="#1f4e79", ms=3.6, lw=1.4,
            label=r"order statistic ($k$-th largest)")
    ax.annotate("order statistic\n($k$-th largest score)", (xs[2], ys[2]),
                textcoords="offset points", xytext=(10, 10), fontsize=7.5,
                color="#1f4e79")
    ax.annotate(r"$k{=}1$", (xs[0], ys[0]), textcoords="offset points",
                xytext=(4, -12), fontsize=7.5, color="#1f4e79")
    cpx, cpy = d["p_history_notcertified_cp_upper"], d["mu_cal"]
    ax.plot([cpx], [cpy], "X", color="#b03030", ms=8)
    ax.annotate("held-out Clopper\u2013Pearson\n(one point, dominated\non both axes)",
                (cpx, cpy), textcoords="offset points", xytext=(-8, -12),
                fontsize=7.5, color="#b03030", ha="right", va="top")
    ax.set_xscale("log")
    import matplotlib.ticker as mt
    ax.xaxis.set_major_formatter(mt.FuncFormatter(
        lambda v, _: ("%g" % v) if v >= 0.01 else ""))
    ax.xaxis.set_minor_formatter(mt.FuncFormatter(
        lambda v, _: ("%g" % v) if v in (0.02, 0.05, 0.2, 0.5) else ""))
    ax.set_xlabel("bound on next-history failure probability")
    ax.set_ylabel(r"certified budget on $\mathbb{E}_\omega[\mathrm{TV}]$")
    ax.margins(x=0.12, y=0.12)
    # 只登记**正文确实引用**的两个点(k=1 的前沿端点与被支配的 CP 点)。曲线其余
    # 各点是图的几何,既没在图上标数字、正文也不逐点引用 —— 全部登记会把
    # "figdata ⊆ 正文"的契约变成"逼正文抄下 16 个数",那是把守卫用坏了。
    FIGDATA["f3_conformal"] = {
        "conformal_threshold_k1": round(cur[0]["threshold"], 4),
        "conformal_risk_k1": round(cur[0]["risk_bound"], 4),
        "cp_risk": round(cpx, 4),
        "cp_threshold": round(cpy, 4),
        "n_curve_points": len(cur),
        "source": src}
    save(fig, "f3_conformal_frontier")


def f4_history_certificates():
    """F4 双面板:左=跨历史跨度(五个数量级),右=逐历史证书与两条阈值。

    两件事不该压在同一条轴上。左panel 讲**选择偏差**:实测均值排序后横跨
    2e-6..2.6e-1,单历史认证落在哪一端完全是运气。右panel 讲**认证**:每个
    历史的置信上界都在 μ_cal 之下(16/16 留出通过),而共形阈值 μ_conf 只由
    校准集算出、更紧,留出点无一越过 —— 留出从未参与阈值计算,故这是**真检验**。
    """
    d = J("w3cf_multihist_verdict.json")
    s_, per = d["summary"], d["per_history"]
    role = {}
    for sh in (0, 1):
        for p in J(f"w3cf_s{sh}_exact_client.json")["plan"]:
            role[int(p["n_tok"])] = p["role"]
    rows = sorted(per, key=lambda r: r["TV_mean"])
    CAL, VAL = "#1f4e79", "#c8791a"
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.9, 2.5),
                                 gridspec_kw={"width_ratios": [1.05, 1]})

    # --- 左:跨度
    for r_, col in (("cal", CAL), ("val", VAL)):
        ix = [i for i, r in enumerate(rows) if role.get(r["n_tok"]) == r_]
        a1.plot(ix, [rows[i]["TV_mean"] for i in ix], "o", ms=2.6, color=col)
    a1.set_yscale("log")
    a1.annotate("", xy=(2, rows[0]["TV_mean"]), xytext=(2, rows[-1]["TV_mean"]),
                arrowprops=dict(arrowstyle="<->", lw=0.9, color="#555555"))
    a1.text(4.5, 3e-4, r"$1.3\times10^{5}$" + "\nspread", fontsize=7.5,
            color="#555555", va="center")
    a1.set_xlabel("history, sorted")
    a1.set_ylabel(r"realized $\mathbb{E}_\omega[\mathrm{TV}]$")
    a1.set_title("(a) one history is not representative", fontsize=8, pad=4)

    # --- 右:**每条阈值只能和它自己口径的分数比**。
    # ucb 走 Bonferroni(α'=α/H),配 μ_cal;score_conf 走 α(符合性分数不必覆盖
    # 真值,故无需 Bonferroni),配 μ_conf。把 ucb 画在 μ_conf 旁边就是混口径 ——
    # 本文正在批判的那个错误,画图时我自己先犯了一次。
    ub = sorted(per, key=lambda r: r["ucb"])
    sc = sorted(per, key=lambda r: r["score_conf"])
    for r_, col, lab in (("cal", CAL, "calibration ($64$)"),
                         ("val", VAL, "held out ($16$)")):
        ix = [i for i, r in enumerate(ub) if role.get(r["n_tok"]) == r_]
        a2.plot(ix, [ub[i]["ucb"] for i in ix], "o", ms=2.6, color=col, label=lab)
        jx = [i for i, r in enumerate(sc) if role.get(r["n_tok"]) == r_]
        a2.plot(jx, [sc[i]["score_conf"] for i in jx], "^", ms=2.6, color=col,
                alpha=.75)
    a2.axhline(s_["mu_cal"], ls="--", lw=1.1, color="#b03030")
    a2.axhline(s_["mu_conformal"], ls="-.", lw=1.1, color="#2e8b57")
    a2.text(78, s_["mu_cal"] + 0.005,
            r"$\mu_{\mathrm{cal}}$ vs. Bonferroni UCB ($\bullet$)",
            fontsize=7, color="#b03030", ha="right")
    a2.text(78, s_["mu_conformal"] - 0.007,
            r"$\mu_{\mathrm{conf}}$ vs. conformity score ($\blacktriangle$)",
            fontsize=7, color="#2e8b57", ha="right", va="top")
    a2.set_xlabel("history, sorted within each series")
    a2.set_ylabel(r"bound on $\mathbb{E}_\omega[\mathrm{TV}]$")
    a2.set_title("(b) each threshold meets its own caliber", fontsize=8, pad=4)
    a2.legend(fontsize=7.2, frameon=False, loc="lower right", handlelength=1.0)
    fig.subplots_adjust(wspace=0.34)
    FIGDATA["f4_history_certificates"] = {
        "n_hist": len(rows), "mu_cal": round(s_["mu_cal"], 4),
        "mu_conformal": round(s_["mu_conformal"], 4),
        "source": "experiments/out/w3cf_multihist_verdict.json"}
    save(fig, "f4_history_certificates")


def f6_proof_chain():
    """F6 机检链路:见证方差 → 请求级尾概率 → 跨历史外推。

    这张图不是装饰:它在同一张图里区分"哪一步是**证明**、哪一步只是**测量**、
    哪一步仍**开放**" —— 论文反复强调的正是这三者不可混同。每条边标 Lean
    定理名,读者可按名字去 formal/WitCert 核对;点线框是本文明写的开放项。
    """
    from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
    fig, ax = plt.subplots(figsize=(6.9, 2.6))
    ax.set_xlim(0, 100); ax.set_ylim(0, 48); ax.axis("off")
    PROVED, MEASURED, OPEN = "#1f4e79", "#2e8b57", "#8a8a8a"

    def box(x, y, w, h, txt, col, dashed=False, fs=7.0):
        ax.add_patch(FancyBboxPatch((x, y), w, h,
                     boxstyle="round,pad=0.5,rounding_size=1.0",
                     linewidth=1.0, edgecolor=col, facecolor="white",
                     linestyle=((0, (1.4, 1.4)) if dashed else "solid"), zorder=2))
        ax.text(x + w / 2, y + h / 2, txt, ha="center", va="center",
                fontsize=fs, color=col, linespacing=1.5, zorder=3)

    def arrow(x1, y1, x2, y2, lab, col=PROVED, dy=1.8, fs=6.0, ha="center",
              labxy=None):
        ax.add_patch(FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-|>",
                     mutation_scale=8, lw=0.9, color=col, zorder=1))
        lx, ly = labxy if labxy else ((x1 + x2) / 2, (y1 + y2) / 2 + dy)
        ax.text(lx, ly, lab, ha=ha, va="bottom", fontsize=fs, color=col,
                family="monospace", zorder=3)

    Y, H = 25, 11
    box(0, Y, 20, H, "per-step draw $\\omega$\nmass-weighted\nmoment bound", PROVED)
    box(27, Y, 19, H, "expected served\ntotal variation\n$\\leq\\mu$", PROVED)
    box(53, Y, 19, H, "anytime ledger\n(Ville)", PROVED)
    box(79, Y, 21, H, "request-level tail\n$\\leq\\delta$", PROVED)
    TOP = Y + H + 1.5
    arrow(20, Y + H / 2, 27, Y + H / 2, "served_tv_mean_le_massweighted",
          labxy=(23.5, TOP))
    arrow(46, Y + H / 2, 53, Y + H / 2, "bernoulli_mgf_le", labxy=(49.5, TOP))
    arrow(72, Y + H / 2, 79, Y + H / 2, "cumloss_admission", labxy=(75.5, TOP))

    box(30, 6, 40, 10, "exchangeable history sample\n"
                       "$\\Rightarrow$ unseen history exceeds "
                       "$\\mu_{\\mathrm{conf}}$ w.p. $\\leq 1/(N{+}1)+\\alpha$",
        PROVED, fs=6.8)
    arrow(85, Y, 62, 16, "conformal_risk_union", dy=-2.4, fs=6.0)
    box(78, 6, 22, 10, "runtime traffic\nnot our population", OPEN, dashed=True)
    arrow(70, 11, 78, 11, "open", col=OPEN, dy=1.5)
    box(0, 6, 24, 10, "propagation constants\nmeasured, not bounded", MEASURED,
        dashed=True, fs=6.8)
    arrow(12, 16, 12, Y, "probe falsifies\nfirst-order surrogate", col=MEASURED,
          fs=5.8, labxy=(14.5, 18.5), ha="left")

    ax.text(50, 1.0, "solid = machine-checked in Lean          "
                     "dotted = measured or open", ha="center",
            fontsize=6.6, color="#555555")
    FIGDATA["f6_proof_chain"] = {"source": "formal/WitCert/*.lean(仅定理名,无数值)"}
    save(fig, "f6_proof_chain")


def f7_read_bound_vacuity():
    """F7 逐读界的**有效 ≠ 有用**:e-form 随掩位数迅速空洞,tanh 律不空洞。

    论文正文只给了 6.7%/41.8% 两个点;把 m=2/3/4 三档画出来,"哪一档还能用"
    一眼可见,而这正是把 e-form 换成 tanh 律的**动机**而非事后修辞。
    """
    r = J("w3sl_readtv_offline.json")["per_m"]
    ms = sorted(r, key=int)
    ef = [r[m]["vac_frac_eform"] for m in ms]
    tv = [r[m]["vac_frac_tanh"] for m in ms]
    fig, ax = plt.subplots(figsize=(3.2, 2.25))
    w = 0.36
    xs = range(len(ms))
    ax.bar([x - w / 2 for x in xs], ef, w, color="#b03030")
    ax.text(0.0, 0.28, "inherited e-form", ha="center", fontsize=7.5,
            color="#b03030")
    ax.bar([x + w / 2 for x in xs], tv, w, color="#2e8b57")
    for x, v in zip(xs, ef):
        ax.text(x - w / 2, v + 0.02, "%.1f%%" % (100 * v), ha="center", fontsize=7)
    ax.text(1.0, 0.58, "gate $\tanh$ law: $0\%$ vacuous" + "\nat every $m$",
            ha="center", fontsize=7.5, color="#2e8b57")
    ax.set_xticks(list(xs)); ax.set_xticklabels(["$m=%s$" % m for m in ms])
    ax.set_ylim(0, 1.08)
    ax.set_ylabel("fraction of reads with\nvacuous bound ($\\geq 1$)")
    ax.set_xlabel("masked mantissa bits")
    FIGDATA["f7_read_bound_vacuity"] = {
        "vac_eform_m2_pct": round(100 * ef[0], 1),
        "vac_eform_m3_pct": round(100 * ef[1], 1),
        "vac_eform_m4_pct": round(100 * ef[2], 1),
        "source": "experiments/out/w3sl_readtv_offline.json:per_m"}
    save(fig, "f7_read_bound_vacuity")


def f8_history_cost():
    """F8 设计曲线:达到目标风险需要多少个可交换历史?

    纯解析(无新测量):顺序统计量 1/(N+1)+α vs 零事件 Clopper-Pearson。
    部署侧真正要问的就是这条 —— "我要 1% 的历史失败率,得采多少个历史"。
    两条线在对数轴上是两种**不同的标度律**,这才是换仪器的长期收益。
    """
    import math
    targets = [0.20, 0.10, 0.05, 0.02, 0.01, 0.005]
    conf, cp = [], []
    for t in targets:
        a = t / 2.0                     # 两项等分:α = 1/(N+1) = t/2
        conf.append(max(1, math.ceil(1.0 / a) - 1))
        cp.append(math.ceil(math.log(0.01) / math.log(1 - t)))   # 零事件 99% 置信
    fig, ax = plt.subplots(figsize=(3.3, 2.3))
    ax.plot(targets, conf, "o-", ms=3.6, lw=1.4, color="#1f4e79",
            label="order statistic")
    ax.plot(targets, cp, "s--", ms=3.4, lw=1.4, color="#b03030",
            label="held-out Clopper\u2013Pearson")
    ax.set_xscale("log"); ax.set_yscale("log"); ax.invert_xaxis()
    ax.set_xlabel("target bound on next-history failure")
    ax.set_ylabel("exchangeable histories needed")
    ax.legend(fontsize=7.2, frameon=False, loc="upper left")
    ax.annotate("$80$ measured here", (0.0254, 80), textcoords="offset points",
                xytext=(6, -14), fontsize=7, color="#555555")
    ax.plot([0.0254], [80], "*", ms=9, color="#c8791a", zorder=5)
    FIGDATA["f8_history_cost"] = {
        "n_hist": 80, "achieved": 0.0254,
        "source": "解析曲线(无新测量);实测点取自 w3cf"}
    save(fig, "f8_history_cost")


def f9_router_margins():
    """F9 路由 margin 证书在真实位宽下的表现:binding 率与 flip 率随位宽。

    支柱 B 的核心事实不是"证书不成立"(零违约),而是"作为门它会拒掉几乎所有
    流量" —— 那要靠 binding 率随位宽逼近 1 才看得出来。左:路由权重自身量化;
    右:专家量化而**路由保持精确**,margin 仍然普遍 binding。
    数据源与 canon 同一处(per_bits_class / results),不另取分相聚合 ——
    否则论文里会冒出第二个没有解释的数(62.3 vs 63.2 就是这么来的)。
    """
    g = J("rrd_w2c_router_margin.json")["per_bits_class"]
    u = J("w2cp_upstream_router.json")["results"]

    def merged(d):                       # prefill/decode 按 n 加权合并,与左图同口径
        tot = d["prefill"]["n"] + d["decode"]["n"]
        return {k: (d["prefill"][k] * d["prefill"]["n"]
                    + d["decode"][k] * d["decode"]["n"]) / tot
                for k in ("binding", "flip")}

    left = {int(k[3:]): g[k] for k in g}
    right = {int(k[-1]): merged(u[k]) for k in u if k.startswith("armA_int")}
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.6, 2.25), sharey=True)
    for ax, src, title in ((a1, left, "(a) router weights quantized"),
                           (a2, right, "(b) experts quantized, router exact")):
        xs = sorted(src)
        for key, col, mk, lab in (("binding", "#1f4e79", "o", "margin binding"),
                                  ("flip", "#b03030", "s", "selection flipped")):
            ax.plot(xs, [src[b][key] for b in xs], mk + "-", ms=4.4, lw=1.4,
                    color=col, label=lab)
            for b in xs:
                ax.annotate("%.1f%%" % (100 * src[b][key]), (b, src[b][key]),
                            textcoords="offset points", xytext=(0, 6),
                            ha="center", fontsize=6.4, color=col)
        ax.set_xticks(xs); ax.set_xticklabels([f"INT{b}" for b in xs])
        ax.invert_xaxis()                # 左→右 = 精度递减
        ax.set_title(title, fontsize=8, pad=4)
        ax.set_ylim(0.42, 1.10)
    a1.set_ylabel("fraction of tokens")
    a1.legend(fontsize=7, frameon=False, loc="lower left", handlelength=1.4)
    a1.text(0.5, 0.03, "zero certificate violations throughout",
            transform=a1.transAxes, ha="center", fontsize=6.8, color="#555555")
    fig.subplots_adjust(wspace=0.08)
    FIGDATA["f9_router_margins"] = {
        "gate_int4_flip_pct": round(100 * left[4]["flip"], 1),
        "gate_int4_binding_pct": round(100 * left[4]["binding"], 1),
        "source": "experiments/out/rrd_w2c_router_margin.json:per_bits_class "
                  "+ w2cp_upstream_router.json:results"}
    save(fig, "f9_router_margins", P4)


def f10_crossfamily_margin():
    """F10 跨家族路由 margin:binding 随 top-k 单调,与厂商/专家数/scoring 无关。

    表格给的是九个数;这张图给的是**结构** —— headroom 在对数纵轴上沿 k 落成
    一条直线,而与专家数(8..384)、scoring(softmax/sigmoid/sqrtsoftplus)、
    选择结构(greedy/bias 校正/分组)、厂商都无关。这比"九个都接近 1"信息量大
    得多:证书被绑定的根源是**选中集合的边界数量**,不是模型规模或路由花样。

    回归线与 canon 的 k 规律条目**同式同源**(都是对 (k, log(1-binding)) 的
    无加权最小二乘),不许在这里另算一套 —— 图与正文数字脱钩由
    test_paper_claims 的 figdata⊆prose 关卡挡住。
    """
    import glob as _g
    rows = []
    for p in sorted(_g.glob(os.path.join(OUT, "w2cv_*_router_margin.json"))):
        d = J(os.path.basename(p))
        rows.append((d["topk"], d["per_bits"]["int4"]["binding"],
                     d["n_routed_experts"], d["model"],
                     d.get("routing_mode", "flat"),
                     d.get("has_per_expert_bias", False)))
    # 展示名:截断到 15 字符会得到 "DeepSeek-V4-Fla" 这种半截词,显式给短名
    SHORT = {"DeepSeek-V4-Flash": "DSV4-Flash", "DeepSeek-V3.2": "DSV3.2",
             "GLM-5.2-FP8": "GLM-5.2", "Qwen3-30B-A3B-Instruct-2507":
             "Qwen3-30B-A3B", "Llama-4-Scout-17B-16E-Instruct": "Llama-4-Scout",
             "Mixtral-8x7B-Instruct-v0.1": "Mixtral-8x7B"}
    fig, ax = plt.subplots(figsize=(5.0, 2.8))
    # 同 k 的点挤在一起:k 最大的那侧已贴右边界,标签必须朝**左**排,否则出血
    rows.sort(key=lambda r: (r[0], -r[1]))
    from collections import defaultdict
    seen = defaultdict(int)
    kmax = max(r[0] for r in rows)
    # k=kmax 那一档挤了五个模型,逐点标注必然叠字 —— 图的职责是呈现**结构**,
    # 逐个点名交给表 tab:crossfamily。这里只点名承担论证的四个,余下的画成一族。
    top = [r for r in rows if r[0] < kmax]
    for k, bd, E, m, mode, hb in rows:
        col = "#b03030" if hb else "#1f4e79"
        mk = "s" if mode == "grouped" else "o"
        ax.plot([k], [1 - bd], mk, ms=5 + 2.2 * (E / 256) ** .5, color=col,
                alpha=.85)
        if k == kmax:
            continue
        # k=1 与 k=2 的 headroom 几乎同高,同向偏移会让两个标签叠字 —— 交错上下
        i = seen[k]; seen[k] += 1
        dy = (8, -12)[len([r for r in top if r[0] < k]) % 2] - 8.5 * i
        ax.annotate(SHORT.get(m, m), (k, 1 - bd), textcoords="offset points",
                    xytext=(9, dy), ha="left", fontsize=6.4, color="#444444")
    grp = [r for r in rows if r[0] == kmax]
    if grp:
        Es = sorted({r[2] for r in grp})
        ax.annotate("%d models, $E\\in\\{%s\\}$\n(within $0.002$ of "
                    "each other)" % (len(grp), ",".join(str(e) for e in Es)),
                    (kmax, max(1 - r[1] for r in grp)),
                    textcoords="data", xytext=(5.3, 0.035), ha="center",
                    va="center", fontsize=6.4, color="#444444",
                    arrowprops=dict(arrowstyle="-", lw=0.5, color="#bbbbbb",
                                    ls=":", shrinkA=2, shrinkB=4))
    # 预注册的 alive/too-small 分界(binding=0.5 ⟺ headroom=0.5),以及实测分界带
    # alive 线用**黑点线**而非绿虚线:绿色已被 oracle 拟合线占用,同色会被读成
    # 同一族。它的说明并进左下角图例 —— 内联标注无论放哪一档都会压到某条线上。
    ax.axhline(0.5, ls=":", lw=1.2, color="#333333")
    ax.axvspan(2.15, 3.85, color="#cccccc", alpha=.35, lw=0)
    # 带的标注放在 T0 线**之下**、图例**之上**的空当(原位置 3e-3 与图例叠字)
    ax.text(3.0, 3e-2, "boundary", fontsize=6.4, color="#666666", ha="center")
    # **三条线**:同一批 token、同一量化口径,只换判据的松紧。
    # 论文此前把 T0 的斜率读成"MoE 的性质",而 T2/oracle 说其中约九成是仪器 ——
    # 图必须把这三条并置,否则读者只能看到最松的那条(2026-08-09 更正)。
    xs = [r[0] for r in rows]

    def _fit(ys):
        n = len(xs); mx, my = sum(xs) / n, sum(ys) / n
        sl = (sum((x - mx) * (y - my) for x, y in zip(xs, ys))
              / sum((x - mx) ** 2 for x in xs))
        ic = my - sl * mx
        sst = sum((y - my) ** 2 for y in ys)
        ssr = sum((y - (sl * x + ic)) ** 2 for x, y in zip(xs, ys))
        return ic, sl, 1 - ssr / sst

    lad = {}
    for p in _g.glob(os.path.join(OUT, "w2cw_*_ladder.json")):
        d = J(os.path.basename(p))
        lad[d["model"]] = d["per_bits"]["int4"]
    gx = [min(xs) - 0.3, max(xs) + 0.3]
    ic, sl, r2 = _fit([math.log(1 - r[1]) for r in rows])
    ax.plot(gx, [math.exp(ic + sl * x) for x in gx], "-", lw=1.1,
            color="#888888", zorder=0)
    _leg = [(plt.Line2D([], [], color="#888888", lw=1.1),
             "T0 as published:  $%.3f\\,k$" % sl)]
    KEY = [("T2_local_lipschitz", "#c8791a", "T2 tightened"),
           ("T3_oracle", "#2e8b57", "oracle (physical)")]
    if len(lad) == len(rows):
        for key, col, lab in KEY:
            ys2 = [math.log(max(lad[r[3]][key]["admit"], 1e-9)) for r in rows]
            i2, s2, q2 = _fit(ys2)
            ax.plot(gx, [math.exp(i2 + s2 * x) for x in gx], "--", lw=1.0,
                    color=col, zorder=0, alpha=.85)
            ax.plot([r[0] for r in rows], [math.exp(y) for y in ys2], "_",
                    ms=5, color=col, alpha=.8)
            _leg.append((plt.Line2D([], [], color=col, lw=1.0, ls="--"),
                         "%s:  $%.3f\\,k$" % (lab, s2)))
    # 三条斜率放**左下角图例**:此前各自贴在线的右端,与"alive bar"及彼此叠字
    _leg.append((plt.Line2D([], [], color="#333333", lw=1.2, ls=":"),
                 "pre-registered ``alive\'\' bar"))
    ax.legend([h for h, _ in _leg], [t for _, t in _leg], loc="lower left",
              fontsize=6.0, frameon=False, handlelength=1.8,
              labelspacing=0.35, borderaxespad=0.4)
    ax.set_yscale("log")
    ax.set_xticks(sorted({r[0] for r in rows}))
    ax.set_xlabel("experts selected per token ($k$)")
    ax.set_ylabel("headroom $1-$binding\n(fraction the certificate admits)")
    # 记号含义写在图注里,不在图内重复占位(左下角让给斜率图例)
    FIGDATA["f10_crossfamily_margin"] = {
        "n_models": len(rows),
        "klaw_intercept": round(ic, 2),
        "klaw_slope": round(sl, 3),
        "klaw_r2": round(r2, 3),
        "source": "experiments/out/w2cv_*_router_margin.json:per_bits.int4"
                  " + w2cw_*_ladder.json:per_bits.int4"}
    save(fig, "f10_crossfamily_margin", P4)


def f11_replay_gain_vs_damage():
    """F11(p4)本篇最该有图的一条曲线:replay 收益随损伤下降并**变号**。

    正文把它写成一串行内数字("+0.030 at 0.26 nats, +0.039 at 0.73, -0.007 at
    1.19, -0.078 at 1.82, -0.211 at 2.81"),读者要在脑子里把曲线重建出来 ——
    而这正是 p4 的第二个头条结果。三件事一张图说清:
      ① 同一模型内 replay 收益随损伤单调下降,在 ~1.2 nats 处穿过零;
      ② GPTQ-2bit 落在曲线**远下方**(-1.284 对外推的 ~-0.25)⟹ 量化器留下的
         指纹超出"损伤深度"能解释的范围,所以横轴不是唯一变量;
      ③ Qwen3-30B 在 2.04 nats 仍**为正** ⟹ 阈值是模型局部的,
         "每个模型都有反号点"已被预注册判死。

    数值按**正文呈现精度**落盘(图/figdata/正文三者同源;全精度会让
    figdata⊆prose 恒红)。行级混合四点来自 R17c 扫描,p=1.00 端点即 R10 深度
    曲线的 int2 —— 两者的 p=0 端点在 crossrun 控制里对齐过(+0.02992)。
    """
    g = J("w3rl_reversal_threshold.json")["grid"]
    dep = J("w3rc_routing_curve.json")["curve"]["int2"]
    qw = J("w3rk_qwen32b.json")["per_domain"]["ours"]["self"]["dnll_mean"]
    pts = [(round(g[k]["self_dnll_mean"], 2), round(g[k]["gain_nll_mean"], 3))
           for k in ("mix_p0.00", "mix_p0.25", "mix_p0.50", "mix_p0.75")]
    pts.append((round(dep["self"]["dnll_mean"], 2),
                round(dep["gain_nll_mean"], 3)))
    gx = round(g["gptq2"]["self_dnll_mean"], 3)
    gy = round(g["gptq2"]["gain_nll_mean"], 3)
    qx = round(qw, 2)

    fig, (hi, lo) = plt.subplots(
        2, 1, figsize=(5.4, 3.4), sharex=True,
        gridspec_kw={"height_ratios": [2.6, 1], "hspace": 0.10})
    for ax in (hi, lo):
        ax.axhline(0, color="0.75", lw=0.8, zorder=0)
        ax.axvline(qx, color="#7a5195", ls=":", lw=1.0, zorder=0)
        ax.plot(*zip(*pts), "-o", color="#1f4e79", ms=4.2, lw=1.4,
                label="DeepSeek-V2-Lite, row-mix 3$\\to$2 bit")
        ax.plot([gx], [gy], "X", color="#c1272d", ms=8, zorder=3,
                label="same model, GPTQ at 2 bits")
    # 断轴:上格只放曲线,下格放掉队的 GPTQ 点
    hi.set_ylim(-0.295, 0.085)
    lo.set_ylim(-1.35, -1.22)
    lo.set_yticks([-1.28])
    hi.spines["bottom"].set_visible(False)
    lo.spines["top"].set_visible(False)
    hi.tick_params(bottom=False)
    # 断轴记号:不画的话 -0.2 到 -1.22 的跳会被读成连续轴
    kw = dict(transform=hi.transAxes, clip_on=False, color="k", lw=0.9)
    hi.plot([-0.013, 0.013], [-0.03, 0.03], **kw)
    kw["transform"] = lo.transAxes
    lo.plot([-0.013, 0.013], [1 - 0.078, 1 + 0.078], **kw)
    hi.annotate("replay stops paying\n(sign change $\\approx1.2$ nats)",
                xy=(1.19, -0.007), xytext=(1.24, 0.048), fontsize=7.4,
                arrowprops=dict(arrowstyle="->", lw=0.7, color="0.35"))
    hi.annotate("Qwen3-30B still positive at\nthis damage: the reversal\n"
                "point is model-local", xy=(qx, -0.155),
                xytext=(qx + 0.05, -0.29), fontsize=7.2, color="#7a5195",
                va="bottom")
    lo.annotate("far below the curve \u2014 the quantizer leaves\n"
                "a fingerprint beyond damage depth",
                xy=(gx, gy), xytext=(0.42, -1.335), fontsize=7.2,
                color="#c1272d",
                arrowprops=dict(arrowstyle="->", lw=0.7, color="#c1272d"))
    lo.set_xlabel("quantization damage, self-routed $\\Delta$NLL (nats)")
    hi.set_ylabel("replay gain (nats)", y=0.34)
    hi.legend(frameon=False, fontsize=7.6, loc="lower left",
              borderaxespad=0.2, handletextpad=0.5)
    FIGDATA["f11_replay_gain_vs_damage"] = {
        "damage_nats": [p[0] for p in pts],
        "gain_nats": [p[1] for p in pts],
        "gptq2_damage": gx, "gptq2_gain": gy,
        "qwen3_damage_still_positive": qx,
        "source": "experiments/out/w3rl_reversal_threshold.json:grid + "
                  "w3rc_routing_curve.json:curve.int2 + "
                  "w3rk_qwen32b.json:per_domain.ours"}
    save(fig, "f11_replay_gain_vs_damage", P4)


def f5_coverage_budget():
    """F5 覆盖-预算单调曲线:回退率随累计损失预算的变化,对照 union 基线。

    Table 2 按预算分列已经把'不是免费午餐'说清了;这张图让**单调性**本身可见:
    在 union 自己的工作点附近 cumloss 并不占优,收益要更宽的预算去换。
    """
    c = J("w3av5_coverage.json")
    mc = (c.get("summary") or c).get("monotone_curve")
    order = [("cumtight_5e3", 5e3), ("cumopen_2e4", 2e4), ("cumwide_5e4", 5e4)]
    xs = [b for _, b in order]
    ys = [mc[k] for k, _ in order]
    fig, ax = plt.subplots(figsize=(3.3, 2.35))
    ax.plot(xs, ys, "o-", color="#1f4e79", ms=4, lw=1.4)
    ax.axhline(mc["union"], ls="--", lw=1.1, color="#b03030")
    ax.text(5.2e3, mc["union"] * 1.12, "per-event union baseline",
            fontsize=7.5, color="#b03030")
    for xv, yv in zip(xs, ys):
        ax.annotate("%.3g" % yv, (xv, yv), textcoords="offset points",
                    xytext=(4, 6), fontsize=7)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel(r"cumulative-loss budget $\tilde B$")
    ax.set_ylabel("fallback-to-exact rate")
    FIGDATA["f5_coverage_budget"] = {
        "union": round(mc["union"], 3),
        "cumtight": round(mc["cumtight_5e3"], 3),
        "cumopen": round(mc["cumopen_2e4"], 3),
        "cumwide": round(mc["cumwide_5e4"], 4),
        "source": "experiments/out/w3av5_coverage.json"}
    save(fig, "f5_coverage_budget")


#: 图 -> 归属论文。**发布仓只画本篇的图** —— 2026-08-19 以外人身份验证
#: p3 的公开仓时,生成器跑到 f9 就 FileNotFoundError:那是 p4 的图,而 p4 的
#: 产物(正确地)不在 p3 仓里。让读者看到一个必然失败的命令,比不给命令更糟。
FIG_PAPER = [("f1_bound_ladder", P3), ("f2_gamma_saturation", P3),
             ("f3_conformal_curve", P3), ("f4_history_certificates", P3),
             ("f5_coverage_budget", P3), ("f6_proof_chain", P3),
             ("f7_read_bound_vacuity", P3), ("f8_history_cost", P3),
             ("f9_router_margins", P4), ("f10_crossfamily_margin", P4),
             ("f11_replay_gain_vs_damage", P4)]


def _only():
    """发布仓 ⟹ 本篇 slug;monorepo ⟹ None(全画)。"""
    rj = os.path.join(ROOT, "RELEASE.json")
    if not os.path.exists(rj):
        return None
    return json.load(open(rj, encoding="utf-8")).get("release")


def main():
    only = _only()
    print("论文图:" + (" 仅 %s(发布仓)" % only if only else " 全部"))
    for name, paper in FIG_PAPER:
        if only and paper != only:
            continue
        globals()[name]()
    # 论文拆分收尾(2026-08-13):路由两图的**正文已经在 p4**,figdata 必须跟着走 ——
    # 留在 p3 会让 "figdata ⊆ 正文" 守卫判红 4 个数(99.5 / 0.95 / 0.943 / 0.962),
    # 那不是数字错了,是归属没跟上拆分。键→论文的映射在此显式声明,不靠目录猜。
    # 归属由 save() 记的 OWNER 决定 —— 图文件落哪篇、figdata 进哪篇,同一个来源。
    for slug in (P3, P4):
        if only and slug != only:
            continue
        keys = {k for k in FIGDATA if OWNER.get(k, P3) == slug}
        p = os.path.join(ROOT, "papers", slug, "figdata.json")
        json.dump({k: FIGDATA[k] for k in sorted(keys)},
                  open(p, "w"), ensure_ascii=False, indent=1)
        print("  %s/figdata.json(%d 张)" % (slug, len(keys)))


if __name__ == "__main__":
    main()
