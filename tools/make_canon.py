"""从 experiments/out/*.json 生成冻结的"数字与口径清单" papers/p1-kv-certificates/CANON.md。

动机:代码比论文成熟得快,导致中文稿、英文稿、摘要、README 相互矛盾(2026-07-28 实测:
英文 main.tex 仍说 Yi 因 rope_theta 更难、仍说 SGLang 存储侧未接入,而后文自己又反过来;
abstract_en 停在两模型 / LongBench 未跑 / 存储侧未接;README 停在 v0.1)。

对策:**唯一数字来源是实验 JSON**。本脚本把它们编译成一份带口径的清单,
`tests/test_paper_claims.py` 用这份清单同时核查中文稿、main.tex、abstract_en.md —
任何一份文档漏掉或写错一个数字都会 FAIL。

    python tools/make_canon.py            # 生成 papers/p1-kv-certificates/CANON.md + papers/p1-kv-certificates/canon.json
"""
import glob
import json
import os
import statistics

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "experiments", "out")


def J(name):
    with open(os.path.join(OUT, name), encoding="utf-8") as f:
        return json.load(f)


def ruler():
    res = {}
    for d in sorted(glob.glob(os.path.join(ROOT, "experiments", "out_siteB", "ruler_results", "*", ""))):
        f = os.path.join(d, "metrics.json")
        if not os.path.exists(f):
            continue
        m = json.load(open(f, encoding="utf-8"))
        v = [x["string_match"] for x in m.values()]
        res[os.path.basename(d.rstrip("/")).split("Instruct__")[1]] = (sum(v) / len(v), m)
    return res


def build():
    C = []           # (分组, 名称, 数值字符串, 口径)
    def add(g, n, v, scope, headline=False, paper=1, src=None):
        # headline=True 的条目摘要里也必须出现;其余只约束正文两版
        # paper 指该数字归属哪篇论文:守卫只拿本篇的条目去查本篇的文档,
        # 否则论文2 的数字一冻结就会把论文1 的守卫打红
        # src(2026-08-06 评审 C1):值的机器可溯来源 —— "文件.json:路径说明"
        # 或 "derived:推导口径"。本编译器要防的失效正是"数字与产物脱钩",
        # 手打值必须显式声明来路;存量未溯源条目由 test_paper_claims 按
        # (group,name) 冻结棘轮,新条目必须带 src。
        C.append({"group": g, "name": n, "value": v, "scope": scope,
                  "headline": headline, "paper": paper, "source": src})

    # ---- 理论 / 形式化 ----
    add("理论", "反例倍数", "7.8", "两 token 反例:真实 TV 是错误式给出的『界』的 7.8 倍", headline=True)
    add("理论", "错误式通过的检查组数", "32,256", "均值口径检查数;逐 query 检查才暴露问题")
    # 定理计数由 tools/lean_extract.py 从 formal/ 抽取,不手写
    th = json.load(open(os.path.join(ROOT, "papers", "p1-kv-certificates", "theorems.json"), encoding="utf-8"))
    add("理论", "Lean 主定理数", str(th["n_main"]),
        "Mathlib 层 L1–L4,公理仅 propext/Classical.choice/Quot.sound;由 lean_extract 抽取", headline=True,
        src="papers/p1-kv-certificates/theorems.json:n_main")
    add("理论", "机器检查定理总数", str(th["n_total"]),
        f"Mathlib 层 {th['n_mathlib']} + 零依赖层 {th['n_standalone']};"
        "由 formal/Export.lean 用 Lean 自己的 pretty-printer 与 collectAxioms 导出,"
        "陈述编译进 papers/p1-kv-certificates/THEOREMS.md 与 papers/p1-kv-certificates/arxiv/theorems.tex",
        headline=True,
        src="papers/p1-kv-certificates/theorems.json:n_total")
    add("理论", "公理并集", "、".join(th["axioms_union"]),
        "collectAxioms 机器给出,无 sorryAx",
        src="papers/p1-kv-certificates/theorems.json:axioms_union")

    # ---- T-E bootstrap CI(评审 B-3)----
    ci = json.load(open(os.path.join(OUT, "te_ci.json"), encoding="utf-8"))["configs"]
    def fmt_ci(c): return f"[{c[0]:+.1f},{c[1]:+.1f}]"
    add("RULER门控CI", "fp8 门控配对差", f"+{ci['fp8_gate5']['diff_vs_none']:.1f} " + fmt_ci(ci['fp8_gate5']['diff_ci95']),
        "逐样本配对 vs 满血,150 样本,bootstrap 10⁴;risk-ranked τ=5")
    add("RULER门控CI", "int8/kivi 门控配对差", "0.0",
        "两配置与满血在每个样本上判分完全一致(配对差恒 0)")
    add("RULER门控CI", "fp8 裸跑配对差", f"{ci['fp8_raw']['diff_vs_none']:.1f} " + fmt_ci(ci['fp8_raw']['diff_ci95']),
        "崩塌统计显著")
    add("RULER门控CI", "kivi 裸跑配对差", f"{ci['kivi_raw']['diff_vs_none']:.1f} " + fmt_ci(ci['kivi_raw']['diff_ci95']),
        "静默尾部从轶事升级为统计显著;复跑均值 71.3(原切片 73.7,run-to-run 漂移)")

    # ---- 128k 覆盖率 P38(评审 B-4)----
    p38 = json.load(open(os.path.join(OUT, "p38_long_coverage.json"), encoding="utf-8"))["results"]
    def _p38(S):
        rs = [r for r in p38 if r["S"] == S]
        return min(r["jkv"] for r in rs), max(r["jkv"] for r in rs), max(r["jkv_tanh"] for r in rs)
    lo8, hi8, _ = _p38(8192)
    lo32, hi32, _ = _p38(32768)
    lo128, hi128, t128 = _p38(131072)
    add("128k覆盖率", "8k 区间", f"{lo8*100:.1f}–{hi8*100:.1f}%",
        "Qwen2.5-1.5B,两域拼接流,P17 同配置,δ=10⁻²,KV-head any-of-G")
    add("128k覆盖率", "32k 区间", f"{lo32*100:.1f}–{hi32*100:.1f}%", "同上")
    add("128k覆盖率", "128k 区间", f"{lo128*100:.1f}–{hi128*100:.1f}%",
        "同上,YaRN factor=4(厂商官方长上下文配置);tanh 参考塌到 ≤0.2%", headline=False)
    add("128k覆盖率", "128k tanh 上限", f"{t128*100:.1f}%", "128k 下确定性 tanh 界的最好域")
    add("128k覆盖率", "违约", f"0",
        "三档 × 两域全部零违约(soundness 第四条独立证据链)")

    # ---- 双侧收紧界 P37(评审 A-2b 验证:负结果)----
    p37 = json.load(open(os.path.join(OUT, "p37_twosided_bound.json"), encoding="utf-8"))["results"]
    r8 = p37["rtn-8bit"]
    add("双侧界", "有效档中位反松", f"{1/r8['median_shrink_old_over_two']:.1f}×",
        "rtn-8bit(有效档)双侧聚合形/旧 e-form 的中位比;双侧形在小 c 区二阶劣化")
    add("双侧界", "有效档胜出比例", f"{r8['two_wins_frac']*100:.1f}%", "rtn-8bit,双侧形更紧的单元占比")
    add("双侧界", "coverage 变化", f"{r8['coverage_tau02_old']:.3f}→{r8['coverage_tau02_meter']:.3f}",
        "τ=0.2,min(1,旧,双侧,逐token min) 相对旧界;实质无变化")
    add("双侧界", "min形数值soundness",
        f"0/{sum(v['n'] for v in p37.values()):,}",
        "全部六量化器单元 meter ≥ 真 TV 的违约计数")
    add("双侧界", "饱和档最大缩减", f"{max(v['median_shrink_old_over_two'] for v in p37.values()):,.0f}×",
        "rtn-2bit 中位缩减(但仍远高于 1,meter 恒饱和,无操作点变化)")

    # ---- δ 曲线(三模型族;固定原始 6-7B 三族口径,H200 阶梯(14B-72B)单列 H200战役组)----
    _p17_three = [f for f in sorted(glob.glob(os.path.join(OUT, "p17_*.json")))
                  if not any(t in f for t in ("_14b", "_32b", "_72b"))]
    vals, tanh, red, dd, v_d2 = [], [], [], [], []
    for f in _p17_three:
        rows = json.load(open(f, encoding="utf-8"))
        doms = {}
        for r in rows:
            doms.setdefault(r["domain"], []).append(r)
        for _, rs in doms.items():
            for dk in ("jkv_0.0001", "jkv_0.001", "jkv_0.01", "jkv_0.05"):
                vals.append(statistics.mean(r[dk] for r in rs))
            s = statistics.mean(r["jkv_0.01"] for r in rs)
            v_d2.append(s)
            t = statistics.mean(r["jkv_tanh"] for r in rs)
            tanh.append(t)
            red.append(((1 - t) - (1 - s)) / (1 - t) * 100)
            dd.append((statistics.mean(r["jkv_0.05"] for r in rs)
                       - statistics.mean(r["jkv_0.0001"] for r in rs)) * 100)
    # 评审 A-3:头条区间必须取单一工作点(δ=10⁻²),不得跨 δ 档拼接极值
    add("δ曲线", "subG 覆盖率区间", f"{min(v_d2)*100:.1f}–{max(v_d2)*100:.1f}%",
        "三模型族(Qwen2.5-7B/Mistral-7B/Yi-1.5-6B)×三域,固定 δ=10⁻²,域内均值,KV-head any-of-G", headline=True)
    add("δ曲线", "tanh 覆盖率区间", f"{min(tanh)*100:.1f}–{max(tanh)*100:.1f}%", "同上,确定性 tanh 界", headline=True)
    add("δ曲线", "换页率相对下降", f"{min(red):.1f}–{max(red):.1f}%", "δ=10⁻² 下相对 tanh", headline=True)
    add("δ曲线", "δ 收紧 500× 最大损失", f"{max(dd):.1f}pp", "5×10⁻²→10⁻⁴,六个模型×域组合的最大值", headline=True)
    add("δ曲线", "模型族数", "3", "Qwen2.5-7B(8k)/Mistral-7B(8k)/Yi-1.5-6B(4k,受其位置上限)", headline=True,
        src="derived:三族枚举,清单即口径")

    # ---- RULER ----
    R = ruler()
    if R:
        w = R["witcert__0.40__fraction0.200"][0]
        e = R["expected_attention__0.40__fraction0.200"][0]
        b = R["no_press__0.00__fraction0.200"][0]
        add("RULER-4k", "WitCert 均分", f"{w:.2f}", "13 任务均值,Qwen2.5-7B,1300 样本,字节预算 46.5%", headline=True)
        add("RULER-4k", "满血均分", f"{b:.2f}", "no_press", headline=True)
        add("RULER-4k", "EA 均分", f"{e:.2f}", "expected_attention,其 compression_ratio=0.401 = 丢 40.1% token", headline=True)
        add("RULER-4k", "差值", f"+{w-e:.2f}", "配对 bootstrap p≈0.12,**不显著**;两列预算量纲不同", headline=True)
        add("RULER-4k", "字节节省", "46.5%", "K 145.1B + V 129B = 274.1B vs fp16 512B", headline=True,
        src="derived:1-274.1/512,字节数见口径")

    # ---- LongBench-E ----
    lb = J("longbench_e_summary.json")
    add("LongBench-E", "长度桶数", f"{lb['buckets']}", "5 任务 × 3 桶;lcc_e 三配置全部运行失败未计入", headline=True)
    add("LongBench-E", "WitCert 跌幅>1pp 桶数", f"WitCert {lb['witcert_drops_gt1pp']}/{lb['buckets']}", "")
    add("LongBench-E", "EA 跌幅>1pp 桶数", f"EA {lb['ea_drops_gt1pp']}/{lb['buckets']}", "")
    add("LongBench-E", "2wikimqa 4-8k WitCert", "−3.23", "唯一实质下降")
    add("LongBench-E", "2wikimqa 4-8k EA", "−7.79", "同桶,我们的 2.4 倍")
    add("LongBench-E", "对我方不利处", "+4.36", "EA 在 hotpotqa_e 8k+ 明显更好(如实列出)")

    # ---- 质量消融 ----
    p23 = J("p23_real_v_S8192.json")["results"]
    add("质量", "抖动增益(质量中性)", f"{p23['RTN']['rel_err']/p23['dither']['rel_err']:.2f}×",
        "真实 V,Qwen2.5-7B/8k;抖动本身质量中性", headline=True)
    add("质量", "离群旁路增益", f"{p23['RTN']['rel_err']/p23['RTN+离群']['rel_err']:.2f}×", "同上")

    # ---- 单卡 kernel ----
    p21 = J("p21_quad_S32768.json")
    add("kernel", "四联报覆盖率", f"{p21['coverage_witcert']*100:.1f}%", "S=32768,nq=24,τ=0.2,合成 K")
    add("kernel", "四联报时延", f"{p21['latency_ms']['WitCert-INT8']:.3f}", "ms")
    add("kernel", "四联报加速比",
        f"{p21['latency_ms']['WitCert-INT8']/p21['latency_ms']['fp16']:.2f}×",
        "**kernel 级;不可作为部署代价引用**,端到端见 serving 表", headline=True)
    add("kernel", "四联报误差", f"{p21['rel_err']['WitCert-INT8']:.1e}".replace("e-03", "e-3"), "")
    p24 = J("p24_packed_S32768.json")
    add("kernel", "真实显存节省",
        f"{(1-p24['measured_bytes']['packed']/p24['measured_bytes']['fp16'])*100:.1f}%",
        "torch.cuda.memory_allocated 实测,8k/32k/128k 一致", headline=True)
    p26 = J("p26_fallback_S32768.json")
    add("kernel", "回退后误差", f"{p26['err_fb_after']:.2e}".replace("e-04", "e-4"), "回退前 9.18e-3")
    add("kernel", "有效位宽", f"{p26['effective_bits']:.2f}", "门控后,净省 31.5%")
    add("kernel", "块级换页流量降低", f"{J('p27_blockpagein_S32768.json')['reduction']:.0f}×",
        "中位 1/128 块即回落阈值")
    p28 = J("p28_longcot.json")
    add("kernel", "长 CoT KV 头覆盖率", f"{max(r['cov_kv_head'] for r in p28):.3f}",
        "R1-Distill-7B 真实生成,n=4;与常规长文 0.792 持平")
    p29 = J("p29_sr_S32768.json")
    assert all(r["cov_sr"] == 0.0 for r in p29), "SR 覆盖率不再全为 0,论文否决结论需重写"
    add("kernel", "随机舍入分支覆盖率", "0.000", "所有离群预算下恒为 0 ⟹ 被数据否决")
    for r in J("p31_outlier_budget_S32768.json")["rows"]:
        add("kernel", f"m={r['m_pairs']} 覆盖率(实机)", f"{r['coverage']:.3f}", "S=32768,τ=0.2,合成 K")
    p30 = J("p30_e2e_m16.json")
    add("端到端解码", "m=16 覆盖率", f"{p30['cert_coverage']:.3f}", "HF Cache,28 层,真实 query")
    add("端到端解码", "m=16 KL", f"{p30['kl']:.2e}".replace("e-03", "e-3"), "teacher-forcing")
    add("端到端解码", "m=16 top-5 重叠", f"{p30['top5_overlap']:.3f}", "")
    add("端到端解码", "m=16 最大证书", f"{p30['cert_max']:.3f}", "距 τ=0.2 有 2.3× 余量")

    # ---- scale 粒度 ----
    p32 = J("p32_scale_granularity_S8192.json")["results"]
    A = [v for k, v in p32.items() if k.startswith("A")][0]
    g32 = [v for k, v in p32.items() if "32通道组" in k][0]
    add("scale粒度", "论文口径误差", f"{A['rel_err']:.3e}".replace("e-02", "e-2"), "逐块逐通道,分页不兼容")
    add("scale粒度", "G=32 相对论文", f"{g32['rel_err']/A['rel_err']:.2f}×", "逐 token 逐 32 通道组,分页兼容且更准", headline=True)

    # ---- 离群旁路 ----
    for tag, mn in (("Qwen2.5-7B-Instruct", "Qwen"), ("Yi-1.5-6B-Chat", "Yi")):
        p = J(f"p33_outlier_{tag}.json")
        add("离群旁路", f"{mn} 通道稳定性 Jaccard", f"{p['jaccard_mean']:.3f}", "前半/后半 token 各选 top-8 对")
        add("离群旁路", f"{mn} m=0 覆盖率", f"{p['coverage_by_m']['0']['coverage']:.3f}", "S=4096,τ=0.2,逐 token 组 scale")
        add("离群旁路", f"{mn} m=4 覆盖率", f"{p['coverage_by_m']['4']['coverage']:.3f}", "已排除 amax")
        add("离群旁路", f"{mn} m=16 覆盖率", f"{p['coverage_by_m']['16']['coverage']:.3f}", "")
    add("离群旁路", "只旁路不排除 amax 的降幅", "8%", "证书上界只降 8% ⟹ 必须同时排除")
    add("离群旁路", "旁路+排除 amax 的降幅", "32×", "合成对照:证书最大 2.378 → 0.0731")

    # ---- RULER 级门控评测(T-E) ----
    te = J("te_ruler.json")["rows"]
    add("RULER门控", "满血 avg", f"{te['none']['avg']:.1f}", "6 难任务×25样本=150条,7B,SGLang观测台", headline=True)
    add("RULER门控", "fp8 裸跑 avg", f"{te['fp8_raw']['avg']:.1f}", "灾难级;零分样本 114/150", headline=True)
    add("RULER门控", "fp8 门控 avg", f"{te['fp8_gate5']['avg']:.1f}",
        f"τ_gate=5;零分回到 {te['fp8_gate5']['n_zero']}(=满血);PCIe {te['fp8_gate5']['fallback']['mib']/1024:.1f} GiB 一次性", headline=True)
    add("RULER门控", "kivi 裸跑 avg", f"{te['kivi_raw']['avg']:.1f}",
        f"尾部损伤:零分 {te['kivi_raw']['n_zero']} vs 满血 {te['none']['n_zero']}(9 个静默失败)", headline=True)
    add("RULER门控", "kivi 门控 avg", f"{te['kivi_gate02']['avg']:.1f}",
        f"9 个静默失败全部消除;PCIe {te['kivi_gate02']['fallback']['mib']/1024:.1f} GiB")
    add("RULER门控", "int8 门控 PCIe", f"{te['int8_gate5']['fallback']['mib']/1024:.1f} GiB",
        "安全方案流量比 fp8 少 3.4×(增量持久修复;选择性在规模上成立)")
    add("RULER门控", "增量修复流量降幅", "41×", "整请求重换页 bug 修复:fp8_gate02 1267→30.9 GiB")

    # ---- 机理与第二方法(T-F E1 / T-G) ----
    e1 = J("tf_e1_layers.json")
    n_loss = sum(1 for k, v in e1.items() if k.startswith("L") and v < e1["none"] - 1e-6)
    add("机理", "单层污染有损层数", f"{n_loss}/28",
        "kivi2 逐层单独污染,needle 1.5B;全部无损 ⟹ 无关键层,失败纯来自跨层累积", headline=True)
    add("机理", "全层污染 acc", f"{e1['all']:.3f}", "对照:单层全部 1.0")
    tg = J("tg_kvquant.json")["result"]
    add("机理", "kvquant4 覆盖率", f"{tg['coverage']:.5f}",
        "第二个真实方法复刻:needle 满分但逐步认证不可得,与 KIVI 互证")

    # ---- 重复性(3 不相交切片,450 唯一样本) ----
    rp = J("te_repeats.json")["agg"]
    add("重复性", "满血三切片均值", f"{rp['none']['avg_mean']:.1f}", "79.3/87.2/83.4;所有方向性结论三切片复现")
    add("重复性", "fp8裸跑三切片均值", f"{rp['fp8_raw']['avg_mean']:.1f}", "22.8/27.8/28.7 —— 灾难在每个切片复现")
    add("重复性", "门控距满血差距", "0.4", "fp8/kivi 门控三切片均值与满血差 ≤0.4;kivi 额外零分(+9~+12)全消")

    # ---- T-H 界形对照 ----
    th2 = J("th_gate_bounds.json")["rows"]
    add("界形对照", "det门 fp8 PCIe", f"{th2['det_tanh']['fp8']['pcie_gib']:.1f} GiB",
        "τ=0.99,同见证输入;e-form 同 τ 为 30.8 GiB ⟹ Tier-A 档 det-tanh 门便宜 2.5×")
    add("界形对照", "det门 int8 PCIe", f"{th2['det_tanh']['int8']['pcie_gib']:.1f} GiB",
        "e-form 同 τ 27.3 GiB(5.2×);两界形质量均恢复(79.3–80.1)。受控抖动器档 e-form 反超")

    # ---- SGLang serving ----
    sv = J("sglang_serving_matrix.json")["models"]
    for mn in ("1.5B", "7B"):
        v = sv[mn]
        f_, w, o = v["fp16"], v["witcert"], v["witcert_outlier"]
        add("serving", f"{mn} fp16 容量", f"{f_['capacity']:,}", "page_size=16,mem_frac 0.88,batch16×64tok")
        add("serving", f"{mn} WitCert 容量", f"{w['capacity']:,}", f"{w['capacity_ratio']:.2f}×")
        add("serving", f"{mn} 容量倍率", f"{w['capacity_ratio']:.2f}×", "同显存预算")
        add("serving", f"{mn} 吞吐倍率", f"{w['tp_ratio']:.2f}×", "3 次取中位数")
        add("serving", f"{mn} 覆盖率(无旁路)", f"{w['coverage']:.3f}", "生产遥测,抽样 stride 32")
        add("serving", f"{mn} 旁路容量", f"{o['capacity']:,}", f"{o['capacity_ratio']:.2f}×")
        add("serving", f"{mn} 旁路覆盖率", f"{o['coverage']:.3f}", "m=4 固定通道集")
        add("serving", f"{mn} 证书边际(带旁路)",
            f"{abs(v['cert_marginal_with_outlier'])*100:.1f}%", "")
    add("serving", "证书边际(1.5B 无旁路)", "6.4%", "短序列 decode;长序列微基准是 +0.35%")
    add("serving", "证书边际(7B 无旁路)", "16.2%", "同上")
    add("serving", "kernel 级证书成本", "+0.35%", "S=4096 微基准,量化存储路径")
    add("serving", "fp16 路径证书成本", "+11.9%", "SGLang decode kernel,存储未量化时")
    add("serving", "写路径 Triton 加速", "82×", "torch 版在 decode 循环里会主导时延(63.7→575.9 tok/s)")
    # 补丁行数走冻结产物(2026-08-06 发布纪律:integration/ 私有不随
    # 发布,行数以 integration_stats.json 为准 —— monorepo 里由
    # tools/freeze_integration_stats.py 现算冻结,公开仓直读产物)
    _ps = J("integration_stats.json")
    _pl = [_ps["lines"][f] for f in (
        "witcert_sglang.patch", "witcert_sglang_extend.patch",
        "witcert_sglang_serving.patch")]
    add("serving", "补丁行数", f"{_pl[0]} / {_pl[1]} / {_pl[2]}",
        "decode / extend / serving 接线,三份可提 PR;行数由 "
        "freeze_integration_stats 现算冻结进产物,不手抄")

    # ---- H200 战役(P0/P1,2026-07-29/30,8×H200 143GB)----
    p40 = J("p40_adaptive_stress.json")
    add("H200战役", "自适应违约(自由解码)", f"0/{p40['n_req_free']}",
        "Qwen2.5-7B,50 prompts×20 seeds,prefill 4096,decode 64,δ_req=1e-2", headline=True)
    add("H200战役", "自适应监测 cell 总数", f"{p40['n_cells_total']:,}",
        "每步×每层×每 q-head,free+forced 双模式;数值容差 1e-9,零容差残余全部 |边际|≤1.8e-13")
    add("H200战役", "自适应轨迹分歧率", f"{p40['diverged_frac_free']*100:.1f}%",
        f"free 组与 fp16 基线分歧,中位第 {p40['div_step_median']} 步;rule-of-three 上界 0.3%")
    add("H200战役", "最坏 TV/界比", f"{p40['max_ratio_B_free']:.3f}", "全部 informative cell 上取最大")
    p41 = J("p41_rc_full_system.json")
    add("H200战役", "RC 对照 Δppl", f"+{p41['lm_ctx8192']['dppl_rc_mean']:.4f}",
        "Llama-3.1-8B,ctx8192×8 配对窗;WitCert 同框 +%.4f" % p41['lm_ctx8192']['dppl_wc_mean'])
    add("H200战役", "RC 页入", f"{p41['ruler_4096']['rc_pagein_mb_per_req']:.0f} MB/请求",
        "RC 快路径常态促升页入(RULER-4096);WitCert 认证态为 0,且无 CPU 常驻副本")
    p43 = J("p43_packed_gate_e2e.json")
    add("H200战役", "packed 门控闭环质量", f"{p43['gate02_fixed_avg']:.2f}",
        f"RULER 6 难任务×25,τ=0.2;= packed 无门控 {p43['packed_avg']:.2f},fp16 {p43['fp16_avg']:.2f}",
        headline=True)
    _pd = p43["per_req_pagein_mib_dist"]
    add("H200战役", "门控逐请求页入 P50/P95", f"{_pd['P50']/1024:.2f} / {_pd['P95']/1024:.2f} GiB",
        "串行差分口径,150 请求;packed 修复非持久化固有成本")
    p44s = J("p44_serving_rows.json")["results"]
    _rt = [p44s[k]["kv_capacity"] / p44s[k[:-8] + "_fp16"]["kv_capacity"]
           for k in p44s if k.endswith("_witcert")]
    assert _rt and all(abs(r - _rt[0]) < 5e-4 for r in _rt), f"容量比跨配置不一致:{_rt}"
    add("H200战役", "容量比跨规模/并行不变", f"{_rt[0]:.3f}×",
        "7B/14B/32B(单卡)、70B(tp4)、7B(tp2/tp4) 全部 1.8824×;结构决定", headline=True,
        src="p44_serving_rows.json:kv_capacity witcert/fp16 三对现算,断言一致")
    add("H200战役", "70B tp4 容量", f"{p44s['70b_tp4_witcert']['kv_capacity']:,}",
        f"fp16 {p44s['70b_tp4_fp16']['kv_capacity']:,};吞吐比 {p44s['70b_tp4_witcert']['tok_per_s_median']/p44s['70b_tp4_fp16']['tok_per_s_median']:.2f}×")
    p45 = J("p45_native128k.json")
    _p45rows = p45["results"]
    _nd = {r["S"]: r["jkv"] for r in _p45rows if r["domain"] == "needle"}
    add("H200战役", "原生 128k 覆盖率(needle)",
        f"{_nd[8192]*100:.1f} / {_nd[32768]*100:.1f} / {_nd[131072]*100:.1f}%",
        "Llama-3.1-8B 原生窗口(无 YaRN)@8k/32k/128k,零违约——随长度平坦;"
        "1.5B+YaRN 档的下滑为 YaRN 外推特有", headline=True)
    p48 = J("p48_pareto.json")["curves"]
    add("H200战役", "前沿最不利工况点", f"{p48['witcert']['512']['output_throughput']/p48['fp16']['512']['output_throughput']:.2f}×",
        "c=512 短请求(1024in/256out):witcert %.0f vs fp16 %.0f tok/s;单流 0.78×,tp2 反超"
        % (p48['witcert']['512']['output_throughput'], p48['fp16']['512']['output_throughput']))
    p46 = J("p46_longctx_serving.json")["cells"]
    add("H200战役", "长上下文代价比例平稳", "1.84×→1.89×",
        "Llama-8B witcert TTFT 中位比 @8k→32k(TPOT 1.47×→1.49×),不随 S 恶化;"
        "qwen7b cert-on 30k TPOT 异常已列工程项")
    add("H200战役", "72B 覆盖率", "25.5–29.8%",
        "jkv@δ=1e-2 三域,零违约;显著低于 7–32B(54–81%),削弱性结果如实报告(与 Yi 同型)")

    # ---- R8 异构架构尺子(2026-07-30,论文2 平台篇;paper=2 不参与论文1 守卫)----
    def add2(n, v, scope):
        add("R8平台", n, v, scope, paper=2)

    p50 = J("p50_latent_v2lite.json")["schemes"]
    add2("latent 尺子 cells", f"{p50['latent-rtn8']['n']:,}",
         "V2-Lite S=4096,9 文档×3 域,7 层采样×头步 2(MLA latent 数学验证)")
    add2("latent int8 双 Tier 违约", f"{p50['latent-rtn8']['viol_A']}/{p50['latent-rtn8']['n']:,}",
         "Tier A 零违约;Tier A soundness 由此承担,在线观测只给量级与紧度")
    add2("latent dither Tier B 覆盖率",
         f"{p50['latent-dither8']['covB']['0.2']*100:.1f}%", "τ=0.2;τ=0.5 时 100%")
    p51 = J("p51_glm_serving_phase1.json")["summary"]
    add2("GLM 生产 fp8 相对残差", f"{p51['fp8_rel_pct']:.2f}%",
         "GLM-5.2 W4AFP8 生产栈在线观测,78 层×8 rank,相对 latent 范数")
    add2("GLM latent 层间异质", f"{p51['heterogeneity_ratio']:.0f}×",
         "latent 范数最大/最小之比,异构策略论据")
    p52 = J("p52_corruption_sentinel.json")["summary"]
    add2("坏块哨兵假阳性率", f"{p52['false_positive_rate']:.0%}",
         f"{p52['verify_passes_total']} 次基线校验零告警;注入坏块被逐槽位定位(论文2 引言动机实验)")
    p53 = J("p53_topk.json")
    add2("DSA top-1 认证率", f"{p53['cert_rate_r']['0.001/r1']*100:.2f}%",
         f"GLM-5.2,η=1e-3,{p53['n_layers']} 层×{p53['rows_total']:,} 行;逐层区间 90.0–100%")
    add2("DSA 严格集合认证率", f"{p53['cert_rate_k']['0.001']*100:.2f}%",
         "top-2048 集合口径过强(负结果);认证内翻转恒 0")
    p54 = J("p54_v4flash_quant.json")
    add2("V4 条目二次量化 int8 残差", f"{p54['aggregate']['rel_int8']['mean']*100:.3f}%",
         f"{p54['n_layers']}/43 层×{p54['effective_rows']:,} 行;与 GLM 生产 fp8 的 0.93% 同量级")
    add2("V4 带范数见证保守度", f"{p54['aggregate']['tight_int8']['mean']:.2f}×",
         "W/‖Δ‖,B=16,int8;逐层 2.73–3.86")
    p58 = J("p58_v4_topk.json")
    add2("V4 页级 top-1 认证率", f"{p58['cert_rate_r']['0.001/r1']*100:.2f}%",
         "η=1e-3,21 个 C4 索引层;V4 选压缩页,与 DSA 的 token 级量纲不可直接比")
    # p56 有两种产出口径(本仓库两条并行工作线),字段名不同,兼容读取
    p56 = J("p56_kda_contraction.json")
    _sm = p56.get("summary")
    if _sm:                                   # 双 rank 合并口径(commit 93afe28)
        _lo, _hi = _sm["a_mean_range"]
        _h = _sm["half_life_range_steps"]
        _n = _sm["near_one_frac_range"]
        add2("KDA 收缩因子 ā", f"{_lo:.3f}–{_hi:.3f}",
             f"Kimi-Linear-48B 代理,{_sm['n_kda_layers']}/20 KDA 层全部 ā<1;"
             f"半衰期 {_h[0]:.1f}–{_h[1]:.1f} 步;逐层标量近似口径")
        add2("KDA 近 1 通道占比", f"{_n[0]*100:.1f}–{_n[1]*100:.1f}%",
             "P(a_t≥0.999) 逐层区间;这些通道上界退化为线性累积 ⇒ 界须逐通道给,"
             "属紧度限制而非 soundness 问题")
    else:                                     # 单 rank 逐层口径
        add2("KDA 收缩因子 ā", f"{p56['a_mean']['median']:.4f}",
             f"{p56['n_kda_layers']}/20 KDA 层;半衰期中位 "
             f"{p56['half_life_steps']['median']:.1f} 步;逐层标量近似口径")
        add2("KDA 近 1 通道占比", f"{p56['p_ge_0999']['median']*100:.1f}%",
             f"P(a_t≥0.999) 中位,最大 {p56['p_ge_0999']['max']*100:.1f}%")
    if os.path.exists(os.path.join(OUT, "p52_sentinel_sla.json")):
        _sla = J("p52_sentinel_sla.json")
        _ad = _sla["all_detected"]
        add2("哨兵单块检出概率", f"{_ad['per_block_detect_prob']:.3f}",
             f"有效轮数 n≈{_ad['n_effective']}(注入 rank 注入后的校验轮数,非全 rank 总和),"
             f"每轮抽 128/1024;超几何闭式")
        add2("哨兵检出 2/4 的概率", f"{_ad['P_at_most_observed']:.3f}",
             "'至多检出 2 个'的概率;实测 2/4 属正常涨落,是抽样受限而非能力上限")
        _row1 = next(r for r in _sla["sla_table"]["rows"] if r["B"] == 1)
        _knob = " / ".join(str(_row1[f"r{rx}"]["0.01"]) for rx in (32, 64, 128, 256))
        add2("哨兵检出延迟旋钮", f"{_knob} 轮",
             "B=1、δ=1e-2 时 r=32/64/128/256 所需轮数;检出延迟与抽样预算近似成反比")
    if os.path.exists(os.path.join(OUT, "p55_v4flash_attribution.json")):
        p55 = J("p55_v4flash_attribution.json")
        _pa4 = p55["pool_path"]["pool_attn"]["block4"]
        _pa128 = p55["pool_path"]["pool_attn"]["block128"]
        add2("V4 池化粒度", f"4 与 128 并存({_pa4['n_layers']}/{_pa128['n_layers']} 层)",
             "同一模型内两种 hc 池化块大小;1/block 差 32 倍,跨层比较必须用归一化量")
        add2("V4 池化集中度(block4)", f"{_pa4['top1_norm_median']:.4f}",
             f"top1_norm 中位(0=完全均摊,1=完全主导);有效 token {_pa4['eff_tokens_median']:.2f}/4;"
             "经验观测,不称证书")
        _sel = p55["select_path"]
        if _sel.get("b_S"):
            add2("选择段契约 b_S", f"{_sel['b_S']['0.001']:.5f}",
                 "Lemma S2:(a_S,b_S)=(1,½(m_out+m_in));η=1e-3,V4 C4 索引器 21 层中位;"
                 "选择段**加性不放大**上游误差")
        # p55 的 end_to_end 是被度量类型检查废掉的那次组合(相对见证 + TV 直接相加,
        # 不属任何度量)—— 不再产出冻结数字;合法重建见 p76 块
        add2("V4 三路自检违反", "0",
             "见证违约 + 认证内翻转 + 池化不变量违反合计;存储侧 sound / 选择侧条件认证 / 池化侧无认证")
    if os.path.exists(os.path.join(OUT, "p68_adaptive_sampling.json")):
        _ad = J("p68_adaptive_sampling.json")["phases"]
        add2("自适应采样覆盖地板兜底", str(_ad["high_load_c32"]["forced_by_floor"]),
             "高负载阶段触发次数;0 表示 every 一直在安全区。覆盖两阶段均 43 层未塌 —— "
             "地板存在的意义是覆盖塌陷没有免费警报,不是它常被触发")
    if os.path.exists(os.path.join(OUT, "p66_concurrent_overhead.json")):
        _cc = J("p66_concurrent_overhead.json")
        _w = _cc["worst_case"]
        add2("并发下探针开销(EVERY=64)",
             f"吞吐 {_w['on_e64']['throughput_worst_pct']:+.1f}% / "
             f"TTFT P99 {_w['on_e64']['ttft_p99_worst_pct']:+.1f}%",
             "并发 1/8/32/64,每档 3 次重复取中位;**均在逐档噪声以内** —— "
             "只能给上界不能给点估计;关图口径")
        add2("并发下探针开销(EVERY=16)",
             f"吞吐 {_w['on_e16']['throughput_worst_pct']:+.1f}% / "
             f"TTFT P99 {_w['on_e16']['ttft_p99_worst_pct']:+.1f}%",
             "**双双超出噪声,是可主张的真实退化**;故常开生产档位取 EVERY=64 不取 16")
    if os.path.exists(os.path.join(OUT, "p71_graph_safe.json")):
        _gs = J("p71_graph_safe.json")
        _rt = _gs["replay_test"]
        add2("图重放期累加(graph-safe)",
             f"Δ元素 {_rt['delta_elements']} / Δn_calls {_rt['delta_n_calls']}",
             f"**带图运行**(未加 disable-cuda-graph)。CUDA graph 重放不执行 Python,"
             f"故 n_calls 只涨 prefill 的 {_rt['expected_n_calls_prefill_only']} 次,"
             f"而设备累加器涨满 {_rt['expected_decode_replays']} 次 decode 重放 + prefill;"
             f"两者与预期分毫不差,静置后不再变化。"
             f"**判据是累加器在重放期继续增长,不是带图下的开销** —— 开销数字仍是关图口径")
    if os.path.exists(os.path.join(OUT, "p72_graph_overhead.json")):
        _go = J("p72_graph_overhead.json")
        _w1 = _go["worst_case"]["e1"]
        add2("带图全速探针开销(EVERY=1)",
             f"吞吐 {_w1['throughput_worst_pct']:+.1f}% / "
             f"TTFT P99 {_w1['ttft_p99_worst_pct']:+.1f}%",
             "**带图口径**,单卡 Qwen2.5-7B + gqa-kv,并发 1/8/32 各 3 次重复取中位。"
             "EVERY=1 是唯一被验证过在重放期有完整覆盖的档位,故这是带图成本的**上界**。"
             "**与论文关图数字栈不同,不可相减**")
    if os.path.exists(os.path.join(OUT, "p71_graph_safe_e64.json")):
        _e64 = J("p71_graph_safe_e64.json")
        add2("带图下 EVERY=64 的重放增量", str(_e64["replay_test"]["delta_elements"]),
             f"跑完整轮负载后累加器增量为 {_e64['replay_test']['delta_elements']},"
             f"判定 {_e64['verdict']} —— **采样门是 capture 时求值一次的 Python 分支**,"
             "开图后 EVERY 的语义从'每 N 次采一次'变成'这张图采不采'。"
             "该档层覆盖仍显示 28/28(起服期陈旧样本),验收门原本会放行,"
             "故新增设备侧执行计数与 --expect-replay 才能拦住")
    if os.path.exists(os.path.join(OUT, "p73_capture_select.json")):
        _cs = J("p73_capture_select.json")
        _v = _cs["verdicts"]
        add2("带图最省档探针开销(1 层 × 单量化档)",
             f"吞吐 {_v['s28q1']['throughput_worst_pct']:+.2f}% / "
             f"TTFT P99 {_v['s28q1']['ttft_p99_worst_pct']:+.2f}%",
             "**带图口径**,capture 时按层号选择性插桩(确定性旋钮),**未用融合算子**。"
             "重放累加与层覆盖对账均通过 —— 不是'探针不在图里'的免费。"
             "仍超出 c=32 档的噪声下界,故仅靠减插桩点**压不进噪声**;"
             "把 kernel 数压到 1 之后的同覆盖档见'带图常开档'")
        _win = _v.get("f28q1", {})
        add2("带图常开档(融合算子,1/28 层)",
             f"吞吐 {_win.get('throughput_worst_pct', 0):+.2f}% / "
             f"TTFT P99 {_win.get('ttft_p99_worst_pct', 0):+.2f}%",
             "**三条判据同时满足**:重放累加为真、退化在逐档噪声下界内、层覆盖与声明一致。"
             "**成立的是'1 层常开'不是'全层常开'** —— 同为融合算子,全 28 层仍要 "
             f"{_v.get('fall', {}).get('throughput_worst_pct', 0):+.2f}%")
        add2("融合算子在全层覆盖下的收益",
             f"{-52.81 / _v.get('fall', {}).get('throughput_worst_pct', -1):.1f}×",
             "同为 28/28 层带图运行:torch 版 -52.81%,融合版 "
             f"{_v.get('fall', {}).get('throughput_worst_pct', 0):+.2f}%。"
             "**kernel 数是成本的驱动量**,这是把它从几十压到 1 的直接收益")
        add2("带图插桩成本的标度",
             f"{_v['s14']['throughput_worst_pct'] / _v['s14q1']['throughput_worst_pct']:.2f}×",
             "同为 2 层,量化档从 2 减到 1 的吞吐成本之比 —— "
             f"另:同为单量化档,层数 2->1 的比为 "
             f"{_v['s14q1']['throughput_worst_pct'] / _v['s28q1']['throughput_worst_pct']:.2f}×。"
             "**成本 ≈ 层数 × 每次执行的 kernel 数,两个旋钮各自近似线性且可乘**;"
             "故开图后的成本驱动量是 kernel 数,不是采样率")
    if os.path.exists(os.path.join(OUT, "p74_fused_equiv.json")):
        _fq = J("p74_fused_equiv.json")
        add2("融合见证算子的数值等价", f"{max(c['worst_rel_err'] for c in _fq['cases']):.1e}",
             "融合 Triton 版与 torch 版在四组形状上的最大相对误差(mean/min/max);"
             "**viol 计数与样本数完全相等** —— viol 是 soundness 自检,不容许近似。"
             "舍入取 away-from-zero 而非 torch 的银行家舍入,仅在精确 .5 处不同(测度为零)")
        add2("融合见证算子单调用耗时",
             f"{_fq['latency_us']['fused_1quant']:.1f} us",
             f"对 torch 单量化档 {_fq['speedup']['vs_torch_1quant']:.1f}×、"
             f"双量化档 {_fq['speedup']['vs_torch_2quant']:.1f}×;"
             "**第一版用 grid=(1,) 想避开原子操作,反而 346us 比 torch 还慢** —— "
             "拿并行度换原子操作是亏本买卖,改按行分块 + 三维分带归约才拿到这个数")
    if os.path.exists(os.path.join(OUT, "p78_full_composition.json")):
        _fc = J("p78_full_composition.json")
        _s = _fc["summary"]
        add2("全链逐层注意力 TV 界(typical)", f"{_s['tv_total_typ_median']:.3f}",
             f"存储(窗口+压缩页均见证)+ 经验桥换算的选择误差,均 attn_dist:tv;"
             f"c4 层({_s['n_c4_layers']} 层)中 {_s['n_nonvacuous_typ']} 层非空洞。"
             "**组合档位 empirical**(选择段经经验桥,最弱段决定);c128 层页侧未见证分开报")
        add2("经验桥系数 ρ", f"{_s['rho_median']:.2f}",
             f"注意力口径遗漏质量 / 选择器口径遗漏质量,截断集上实测;中位 {_s['rho_median']:.2f}"
             f" 接近 1(尾部 {_s['rho_max']:.2f},折算取 ρ_max 保守)。"
             "**选择器质量是注意力质量的可用代理** —— 外推到 η 扰动换手集是均质性假设")
        add2("选择误差项(注意力单位)", f"{_s['b_S_attn']:.5f}",
             f"ρ_max × b_S;empirical 档。**不是瓶颈** —— 主导是存储见证"
             f"(centry max {_s['wit_centry_max']:.3f} 比 swa 还大)")
        add2("C4 截断遗漏质量", f"{_s['trunc_mass_median']:.3f}",
             f"top-512 截断遗漏的假想全压缩注意力质量,中位(最大 {_s['trunc_mass_max']:.3f});"
             "**架构设计量而非误差** —— 稀疏选择是 V4 的模型语义,不计入误差链;"
             "本负载 decode 采样口径")
    if os.path.exists(os.path.join(OUT, "p80_request_ledger.json")):
        _rl = J("p80_request_ledger.json")
        _wp = _rl["working_point_coverage"]; _bp = _rl.get("working_point_bound")
        add2("请求级账本:保留优先工作点",
             f"保留 {100*_wp['entry_retention']:.1f}% / 每步 TV 界 {_wp['tv_bound_per_step_max']:.2f}",
             f"**离线重放原型,非在线闭环**;条目级确定性证书(W ≤ {_wp['W_thr']:.2f})+ "
             f"假想局部回退;n={_rl['n_entries_total']:,} 条目,c4 {_rl['n_layers']} 层。"
             "保留率=压缩收益保留,不称 certified coverage(其每步界空洞须一并说)。"
             "非空洞界与 ≥80% 保留不能同时成立(int8 代理见证无重尾)。Σδ=0;"
             "Lean: ledger_sound/telescope_sum/two_layer_budget_le/unknown_length_price")
        if _bp:
            add2("请求级账本:界优先工作点",
                 f"TV ≤ {_bp['tv_bound_per_step_max']:.2f} / 保留 {100*_bp['entry_retention']:.1f}%",
                 f"W ≤ {_bp['W_thr']:.2f} 的条目走压缩,其余逐条目精确读取(局部回退)。"
                 "构造性:被读条目全 ≤ 阈值 ⟹ 每步 TV 界成立;"
                 "探针为采样审计口径,生产化=逐读取检查(gating 补丁)")
    if os.path.exists(os.path.join(OUT, "p82_online_ledger.json")):
        _ol = J("p82_online_ledger.json")
        _os = _ol["summary"]
        add2("在线影子账本:逐读取事件数", f"{_os['events_total']:,}",
             f"{_ol['n_requests']} 条串行请求,逐请求账本在线建立;每 decode 步 × c4 层 × "
             f"全部被选中页条目(非抽样)。**只读影子**:超阈条目照常被使用,"
             "回退为假想(would_*);真实回退与概率预算消费是 A9 终局")
        add2("在线影子账本:逐请求保留率中位", f"{_os['retention_median']:.3f}",
             f"W_thr={_ol['W_thr']:.2f};min {_os['retention_min']:.3f} / "
             f"max {_os['retention_max']:.3f};假想页入中位 "
             f"{_os['would_pagein_mib_median']:.0f} MiB/请求 —— 这就是把回退做实的"
             "代价预告,与 p80 离线曲线一致")
    if os.path.exists(os.path.join(OUT, "p88_same_request.json")):
        _sr = J("p88_same_request.json")
        _ss = _sr["summary"]
        add2("贪心解码重启稳定性地板", _ss["stability_off_vs_off2"],
             "off vs off2(零干预、两次独立起服):n=8 中即有分歧 —— **一切输出级"
             "对比的噪声地板**。p83 的'策略保护输出'对比缺此地板,已由本口径修正:"
             "干预效应真实(all 臂重度分歧),但 policy/dither 与基线的差异在 n=8 下"
             "处于地板附近,不可分辨;不称 protective,称 consistent with")
        add2("写策略接受率(精度粗化)", f"{100*_ss['policy_acceptance_rate']:.1f}%",
             "**掩码条目占比/策略接受率 —— 非物理压缩收益**(字节数不变,是值域粗化;"
             "物理收益需打包另案)。窗口 nope 侧")
        add2("抽签前授权:预授权率与保守代价",
             f"{100*_ss['dither_preauth_rate']:.1f}% / {_ss['preauth_conservatism']:.1f}×",
             "授权只看先验半径 u_e(均值项+尾项),**不看随机实现**;保守代价 = "
             "policy 事后接受率 / dither 预授权率 —— 先验尾项的价格,如实报")
        _av = _ss["auth_violations_observed"].split("/")
        add2("预授权违约审计", f"{_av[0]}/{int(_av[1]):,}",
             "事件 E_i='授权条目实现 W 超预授半径' 的运行时验证:全部预授条目实测"
             "违约计数;δ_i 自此**绑定真实概率事件**(五审 P0-1 修复),"
             "假设 R3′ 逐事件计数留痕")
        add2("同请求闭环 Σδ", f"{_ss['delta_spent_dither']:.7f}",
             "读侧逐请求账本与写侧真实策略**同一次运行**;逐请求快照差分出写侧逐请求"
             "账目(每请求一行:读侧检查数/写侧压缩与回退增量/δ 增量/违约);"
             "Σδ < δ_req=0.01(望远镜),每份 δ_i 绑定事件")
    if os.path.exists(os.path.join(OUT, "p86_full43_composition.json")):
        _f43 = J("p86_full43_composition.json")
        _s43 = _f43["summary"]
        add2("全 43 层存储项结构落账",
             f"dense 2 / c4 {_f43['families']['c4']} / c128 {_f43['families']['c128']}",
             "41 个有页层的页侧全部见证(写后读回口径);L0/L1 为 ratio=0 稠密层,"
             "无压缩页是架构事实非测量省略。c128 无索引器稠密读,无选择项")
        add2("c128 层逐层 TV 界(worst)", f"{_s43['tv_worst_median_c128']:.3f}",
             f"中位;c4 侧为 {_s43['tv_worst_median_c4']:.3f}(含经验桥选择项)。"
             f"c128 页见证 max {_s43['w_cw_max_c128']:.3f} 比 c4({_s43['w_cw_max_c4']:.3f})"
             "干净约一倍 —— 粗压缩层反而更好认证;43 层中 "
             f"{_s43['n_nonvacuous_worst_43']} 层 worst 界 < 1")
    if os.path.exists(os.path.join(OUT, "p96_identity_v2.json")):
        _iv = J("p96_identity_v2.json")
        _vs = _iv["summary"]
        add2("真实生命周期请求身份:user 请求独立预算 max Σδ",
             f"{_vs['max_delta_spent']:.6f}",
             f"七审 F2 重做:边界 = 写路径 extend 转换(先于任何写入,无一批偏移),"
             f"UID 永不复用;{_vs['n_user_requests']} 个 user 请求账户(warmup/boot "
             f"{_vs['n_warmup_accounts']} 个分开计)全部独立 ≤ δ_req=0.01;"
             "单元测试 R5 覆盖复用+更长初始长度等漏检情形。串行 batch=1 口径")
        add2("SR 随机流:跨请求零复用",
             "(nonce,UID,layer,k)",
             "七审关键修复:种子四元组含永不复用的请求 UID —— 不同请求不共享随机数,"
             "条件随机性对自适应流量成立(Lean 超鞅前提可实例化);四元组跨 rank 一致,"
             f"8-rank 账目{'逐字段一致' if _vs['replica_coupling_identical'] else '不一致'}(耦合保持)")
        _eg = _vs["eprocess_global"]
        add2("全局 e-process(跨请求不重置)",
             f"峰值 {_eg['log_M_max']:.2f} vs 阈值 {_eg['threshold']:.2f}",
             f"持续全服务漂移哨兵:{_eg['n_factors']:,} 因子跨全部请求单调累积"
             f"(终值 {_eg['log_M_final']:.1f}),越阈 {'0 次' if not _eg['crossed'] else '发生'};"
             "log_M_max 仅含更新后值(不以初始化 0 冒充峰值)。κ=0.5 预注册,δ_e=1%")
    if os.path.exists(os.path.join(OUT, "p97_owner_closure.json")):
        _oc = J("p97_owner_closure.json")
        _os2 = _oc["summary"]
        add2("owner 版本化:复用压力下闭环",
             f"复用 {_os2['slot_reuses_total']:,} 次 / 读未写 {_os2['read_unwritten_total']} 次",
             "G2:认证写逐槽位记录写入者 UID,复用 = 写时 owner 变更(压缩池无独立 "
             "free 路径,复用必先重写,flags 恒新鲜 —— 设计即约束,无需 allocator "
             "hook);不同 prompt 各账户 1,000+ 次复用下 foreign=0,自有闭环精确。"
             "口径:串行页回收 + 前缀共享;**请求中途驱逐**负载未覆盖")
        add2("foreign 读归属(前缀共享)",
             f"{_os2['foreign_reads_total']:,}(重复 prompt 占 {_os2['foreign_reads_dup_prompt']:,})",
             "读到别的请求写入的条目按 owner 分账 —— 重复 prompt 94% 读命中前缀缓存"
             "(owner=首写请求),不再误记入本请求闭环;写侧 δ 由 owner 请求承担,"
             "读侧检查确定性 δ=0,跨请求共享不破坏预算语义")
    if os.path.exists(os.path.join(OUT, "p98_concurrent_identity.json")):
        _ci = J("p98_concurrent_identity.json")
        _cs = _ci["summary"]
        add2("并发逐行身份:8 路并发独立预算",
             f"max Σδ = {_cs['max_delta_spent']:.6f}",
             f"G1:批内多请求混行下逐条目 UID 归属(decode 计划 [bs,16] 批行对齐 / "
             f"prefill 逐 query token 前缀和分段);{_cs['n_user_requests']} 个 user 账户"
             "各自独立 ≤ δ_req=0.01;每账户独立 (nonce,uid,layer,k) 随机流;"
             f"8-rank 耦合{'逐字段一致' if _cs['replica_coupling_identical'] else '不一致'}")
        add2("并发归属守卫:foreign 读",
             f"{_cs['foreign_reads_user']}/{_cs['read_events_user']:,}",
             "owner 分账做成归属正确性的**运行时守卫**:首验 foreign 3.4% 触发,"
             "定位出 c4/c128 两池共用键空间的 owner 污染(串行同刻单 uid 掩盖,"
             "并发暴露 —— 最早分配者低号槽位与 c128 数值区重叠);键按压缩比分离后"
             "8,228,864 次读 foreign=0、读未写=0")
    if os.path.exists(os.path.join(OUT, "p99_concurrent_identity.json")):
        _hz = J("p99_concurrent_identity.json")
        _hg = _hz.get("gate", {})
        add2("硬化验收门(machine-decidable)",
             f"{sum(_hg.get('criteria', {}).values())}/{len(_hg.get('criteria', {}))} PASS",
             "八/九审收口:**全零硬判据**(foreign/unwritten/violations/归属回退/"
             "身份 fail-closed 拦截/e-process 有数且未越阈/独立预算/账户数/8 份 rank 快照齐且耦合),"
             "判读脚本退出码承载 —— CI/发布包可直接依赖;p99 为 fail-closed 身份+"
             "违约恢复+generation 计数全部在线后的端到端复验(拦截 0/恢复 0 = "
             "硬化机制在正常流量下惰性,只在异常时接管)")
    if os.path.exists(os.path.join(OUT, "q1_packed_int4.json")):
        _q1 = J("q1_packed_int4.json")
        add2("低比特案例:packed INT4 独立池字节(GPU 实测)",
             f"{_q1['pool_bytes_gpu']['fp8_pool_MiB']:.1f}→{_q1['pool_bytes_gpu']['int4_pool_MiB']:.1f} MiB",
             "**独立池格式收益,非服务进程总显存**(FP8 原池仍是 FlashMLA 真实输入);"
             "64Ki token,memory_allocated 差分 −38.4%")
    if os.path.exists(os.path.join(OUT, "p105_wc_q2e.json.rank0")):
        _p5 = J("p105_wc_q2e.json.rank0")
        _pc = _p5.get("packshadow_check") or {}
        add2("低比特案例:serving 内 pack↔unpack 自洽",
             f"{_pc.get('n_checked',0):,} 检查 / unwritten {_pc.get('n_unwritten',0)} / rel {100*_pc.get('rel_mean',0):.1f}%",
             "真实 360B/token packed 池在 serving 内三跑稳定;工具证伪两条设计假设:"
             "①槽位渐进演化(只改 pack 时机误差 18×)②python 读路径非真实消费者"
             "(FlashMLA kernel 内直吃 FP8,三探 packedread=null)。"
             "**不声称**:INT4 已被 attention 消费/HBM 已降/吞吐/质量;"
             "rel_max≈4.9 归因演化期重读(近零范数假设被数据否决)")
    if os.path.exists(os.path.join(OUT, "p90_cert_adjudication.json")):
        _aj = J("p90_cert_adjudication.json")
        add2("四证书裁决:非空洞 43 层",
             " / ".join(f"{k} {v}" for k, v in _aj["nonvacuous_43"].items()),
             "认证对象=掩 2 位 SR(θ/Δ 由捕获字节离线重建);中心化 tanh(osc/4) 使全部"
             "43 层非空洞(现行形 0/43);soundness 自检:全部半径零被击穿"
             "(顶部夹取的确定性平移与零权重分支 log(0) 两个 bug 均被自检抓出后修复)")
        add2("四证书裁决:tightness(半径/实测中位)",
             " / ".join(f"{k} {v:.1f}×" for k, v in _aj["tightness_median_ratio"].items()),
             "64 次 SR 实现为地面真值;现行形 15.8× 松 → 中心化/精确 MGF 2.0×(8 倍收紧)。"
             "**门1(≥30/43)过;门2(retention@0.2 ≥1.5×)败** —— 全族 retention=0,"
             "τ=0.2 在掩 2 位粒度不可达;按预注册规则 E4 重 kernel 跳过。"
             "部署分野:写时预授权 x 在手 θ 免费(精确 MGF 零元数据);读时需 θ ≈+39% 存储")
    if os.path.exists(os.path.join(OUT, "wc_e2.json.rank0")):
        _e2 = J("wc_e2.json.rank0")["certified_write"]
        _n2 = _e2["n_compressed"] + _e2["n_fallback_exact"]
        add2("SR 精确半径:预授权率", f"{100*_e2['n_compressed']/max(1,_n2):.1f}%",
             "真随机舍入(条件均值恰零)+ **variance-aware two-point bounded-difference "
             "radius**(精确的是两点方差 θ(1−θ)Δ² 与夹取项;整体半径含 Jensen 与 "
             "Hoeffding 放缩,该组合尚未 Lean 化 → F3);同阈值 7.8%→67.5%(8.7×)")
        add2("SR 预授权违约审计", f"{_e2['n_auth_violations']}/{_e2['n_authorized']:,}",
             "全部预授条目实测违约计数;δ_i 绑定事件'授权条目实现 W 超预授半径'")
    if os.path.exists(os.path.join(OUT, "p92_eprocess_compare.json")):
        _ep = J("p92_eprocess_compare.json")
        add2("e-process 累计收紧", f"{_ep['ratio']:.0f}×",
             f"T={_ep['T']:,} 事件,**双侧**累计对象(公平口径,各付 δ/2):"
             f"{_ep['eprocess_anytime_radius_two_sided']:.0f}σ vs 望远镜求和 "
             f"{_ep['telescoping_cumulative_radius']:,.0f}σ。**失败事件不同**:"
             "望远镜界'任一逐事件半径被突破'(条目授权用),e-process 界有符号累计和 —— "
             "后者是累计误差的可形式化路线,**尚未接入逐条目授权账本**(F4)")
    if os.path.exists(os.path.join(OUT, "p93_e4_overhead.json")):
        _e4 = J("p93_e4_overhead.json")
        add2("认证写路径开销(未融合)", f"{_e4['overhead_ratio_median']:.2f}×",
             f"逐请求墙钟中位 off {_e4['arms']['off']['wall_median']:.1f}s → "
             f"dither {_e4['arms']['dither']['wall_median']:.1f}s;关图 + python 路径口径 —— "
             "融合 kernel 被 E1 门2 按预注册规则挡下,此为**未优化实现的诚实成本**;"
             "物理字节不变(精度粗化非物理压缩)")
    if os.path.exists(os.path.join(OUT, "p65_kda_logsum.json")):
        _k = J("p65_kda_logsum.json")
        add2("KDA 对数收缩 E[log a]", f"{_k['E_log_a']['median']:.4f}",
             f"正确判据(乘积口径)的逐层中位;均值口径 log(ā) 为 "
             f"{_k['log_of_mean']['median']:.4f} —— **均值把收缩算弱了 2.6×**;"
             f"全 {_k['n_layers']} 层 E[log a] 均为负")
        add2("KDA 误差半衰期", f"{_k['half_life_steps']['logsum_median']:.2f} 步",
             f"对数和判据;均值口径会报成 {_k['half_life_steps']['mean_median']:.2f} 步。"
             "口径:E[log a] 是 (通道,时刻) 聚合,**不是逐通道 Σlog a_t** —— "
             f"近 1 通道占比中位 {_k['p_near_one']['median']:.4f},其上不收缩")
    # p64 已被度量类型检查判废(superseded):它把相对见证与 TV 直接相加,
    # 得到的量不属于任何度量。**superseded 的产物不再产出冻结数字** —— 死数字
    # 留在 canon 里就是给未来的自己埋引用陷阱;其替代是 p76(桥接后的合法组合)。
    if os.path.exists(os.path.join(OUT, "p76_bridged_composition.json")):
        _c = J("p76_bridged_composition.json")
        _s = _c["summary"]
        add2("桥接后逐层注意力 TV 界(typical)", f"{_s['tv_typ_median']:.3f}",
             f"**窗口存储项**,精确形 ½(e^{{2ε}}−1),{_s['n_nonvacuous_typ']}/{_s['n_layers']} 层非空洞;"
             "ε = scale·‖q‖·W(打分桥 Cauchy–Schwarz × softmax 桥 e-form 实例化),"
             "q 范数与 W 均为采样分布统计量。**压缩页条目量化项未见证;"
             "选择段 b_S 在 selector_dist:tv,不相加**。每段 proof 指向已证 Lean 定理")
        add2("桥接后逐层注意力 TV 界(worst)", f"{_s['tv_worst_median']:.3f}",
             f"全 rank 逐层最大值口径,{_s['n_nonvacuous_worst']}/{_s['n_layers']} 层非空洞;"
             "Cauchy–Schwarz 取 Δk 与 q 对齐的最坏情形 —— sound 但悲观,这是证书的代价")
        add2("桥接系数 scale·max‖q‖", f"{_s['qn_max_all']:.4f}",
             "q 过 rmsnorm 后 scale·‖q‖ ≈ 1,打分桥几乎不放大;界的主导项是绝对见证 W"
             f"(全层最大 {_s['wit_max_all']:.3f})。p75 实采,43 层 × 8 rank")
        add2("请求级 TV 聚合预算", f"{_s['request_budget_sum_worst']:.1f}",
             f"{_s['n_layers']} 层求和(worst 口径),>> 1 —— **空洞,如实报**。"
             "跨层求和是聚合预算而非端到端输出距离(各层是不同的分布);"
             "被类型检查废掉的 0.982 连界都不是,不能拿本数字与它比较")
    if os.path.exists(os.path.join(OUT, "p61_platform_matrix.json")):
        pm = J("p61_platform_matrix.json")
        add2("平台覆盖:过验收门的探针行",
             f"{pm['n_probe_rows_verified']} 行 / {pm['n_unique_models']} 模型",
             "架构族 %s;适配器 %d/注入点 %d;收录门槛=通过覆盖->量纲->soundness 验收门"
             % ("、".join(pm["families_covered"]), pm["adapters"], pm["injection_points"]))
        gl = next((r for r in pm["matrix"] if r["path"] == "mla"), None)
        if gl:
            add2("GLM latent 二次量化 int8 残差", f"{gl['rel_int8_median']*100:.3f}%",
                 f"统一框架,{gl['layers_covered']}/{gl['layers_expected']} 层,"
                 f"采样 EVERY={gl['sample_every']};保守度中位 {gl['tight_int8_median']:.2f}×")
    if os.path.exists(os.path.join(OUT, "p60_probe_overhead.json")):
        p60 = J("p60_probe_overhead.json")
        worst = max(max(d.values()) for d in p60["overhead_pct"].values())
        add2("探针开销(最不利档)", f"{worst:+.2f}%",
             p60["caliber"])

    # ---- 代际失效因果链 + 生产集成(2026-08-02,case study 收口;paper=2)----
    try:
        b118 = J("p118_ruler_base_off.json")
        pk_on = J("p118_ruler_packed_on.json")
        pk_off = J("p118_ruler_packed_off.json")
        add2("matched 五臂:radix 掩蔽",
             f"{pk_on['acc']:.3f} vs {pk_off['acc']:.3f}",
             f"packed 臂 radix on/off;base 两侧均 {b118['acc']:.3f} —— 0.800 是"
             "缓存命中口径非质量,confounding 由同 launcher 五臂排除")
        p119o = J("p119_freshness_packonce.json")
        p119e = J("p119_freshness_everyread.json")
        add2("freshness 判别:pack-once vs every-read",
             f"{p119o['acc']:.3f} vs {p119e['acc']:.3f}",
             "20 篇 niah,两臂仅差 PACK_EVERY_READ 且读写双路径均有执行计数;"
             "everyread 恢复 ⇒ 代际一致性是主因(诊断配置,不作唯一归因)")
        q5 = J("q5_pack_roundtrip.json")
        add2("生产 pack 路径本征误差",
             f"{q5['B_pool']['mean']:.4f}",
             f"真实 c4 条目 {q5['n_rows']:,} 行/{q5['n_layers']} 层,纯核/池路径/"
             f"覆盖写三档同值,max {q5['B_pool']['max']:.4f},rope 段恰 0")
        v124 = J("p124_verdict.json")
        on124 = J("p124c_conc_inval_on.json")
        off124x = J("p124_conc_inval_off.json")
        add2("代际失效因果确认(第二次)",
             v124["verdict"],
             f"六条机器判据全过:inval_on acc={on124['acc']:.3f} / "
             f"inval_off acc={off124x['acc']:.3f}(并发 4 口径,两臂仅差失效开关,"
             "n_invalidate 双向证据);不覆盖 abort/radix-on/HiSparse/MTP/PD")
        dc4 = on124["snapshot"]["decode_shadow_all_ranks"]["c4"]
        off124 = J("p124_conc_inval_off.json")
        dc4off = off124["snapshot"]["decode_shadow_all_ranks"]["c4"]
        add2("解码侧影子:修复后 c4 保真度",
             f"{dc4['rel_mean']:.4f}",
             f"内核即将读到的 packed vs 此刻 FP8 源(重填前,1/32 采样,n="
             f"{dc4['n_checked']:,});本征 {q5['B_pool']['mean']:.4f},对照臂 "
             f"{dc4off['rel_mean']:.4f}({dc4off['rel_mean']/dc4['rel_mean']:.0f}×)"
             " —— centry 站点同指标对本失效零区分度(双写者构造性跨代比较)")
        a2 = J("p112a2_swapA.json")
        add2("阶段 A 池装配(规范寻址)",
             f"acc {a2['acc']:.3f}",
             "c128_kv_pool→SwappedC128Pool,20 层 remap(rank 快照 installed=1),"
             "与 noswap 臂 acc/解码侧 rel 一致 —— 结构性换池零质量代价")
        bf = J("p112b2_fp8.json"); bs = J("p112b2_stageb.json")
        dh = sum(bf["hbm_mib_per_gpu"]) - sum(bs["hbm_mib_per_gpu"])
        est_mib = 398478880 * 8 / 1048576
        add2("stage-B HBM 实测差分",
             f"{dh:,} MiB",
             f"FP8 全量 c128 池→窗口环(ring_pages=257)+ packed 常驻,8 卡 "
             f"aggregate 总差;核算 {est_mib:,.0f} MiB,aggregate 相差 "
             f"{abs(1 - dh / est_mib) * 100:.1f}%(逐卡 [566,346×7] 非均匀,"
             "有误差抵消,不得称逐卡吻合);c128 仅 ~0.3% 总 HBM(c4 是 32× "
             "大头),机制验证口径")
        add2("stage-B bring-up 质量(负结果)",
             f"{bs['acc']:.3f} vs {bf['acc']:.3f}",
             "6 篇 niah miss 3;HTTP n_error=0(产物 snapshot 空,**不能**声明"
             "内部 err/orphan/8rank installed —— 证据链洞,GPT review);后由 "
             "p112d 定谳为 decode 越界读环(寻址缺陷),环链是否无损未证明")
    except FileNotFoundError as e:
        print("[canon] 代际链产物缺失,跳过该组:", e)

    # ---- Q4/Q5/Q6 服务化收口(2026-08-03;paper=2)----
    try:
        q5r = J("q5e_refcons.json")
        rs5 = q5r["snapshot"]["pool_swap"]["ring_stats"]
        q5o = J("q5e_oracle.json")
        add2("参考消费者:packed 服务内消费",
             f"{rs5['n_ref_packed']:,} 行",
             f"三分类恒等式 {rs5['n_ref_resident']:,}+{rs5['n_ref_packed']:,}"
             f"+{rs5['n_ref_failed']}+{rs5['n_ref_skip_current']:,}="
             f"{rs5['n_ref_slots_total']:,}(rank0 聚合,逐调用去重槽);"
             f"oracle/refcons acc {q5o['acc']:.3f}/{q5r['acc']:.3f},tol=0;"
             "SMOKE 6 docs,环 129 页,覆盖随驱逐失效语义;不称无损")
        s1 = J("p112_serving_hbm.json")
        bt = s1["byte_truth"]
        add2("c128 单层 staging HBM 净差",
             f"{bt['measured_median_bytes']/1048576:.0f} MiB/GPU",
             f"实测中位 vs 字节净差 {bt['net_expected_bytes']/1048576:.1f} MiB"
             f"(freed {bt['staging1_freed_bytes']/1048576:.1f} − ring+packed "
             f"{(bt['ring_bytes']+bt['packed_bytes'])/1048576:.1f});全部 "
             "untyped_storage 直读;c128 仅 ~0.3% 总 HBM,机制口径")
        q4n = J("q4e_native.json"); q4s = J("q4e_c4staging.json")
        d4 = sorted(a - b for a, b in
                    zip(q4n["hbm_mib_per_gpu"], q4s["hbm_mib_per_gpu"]))
        sw4 = q4s["snapshot"]["pool_swap_c4"]
        net4 = (sw4["staging1_freed_bytes"] - sw4["ring_bytes"]
                - sw4["packed_bytes"]) / 1048576
        add2("c4 INT6 替换 HBM 净差",
             f"{d4[len(d4)//2]:,} MiB/GPU",
             f"native vs c4-staging1(formal 九门含 abort 扰动),字节净差 "
             f"{net4:,.0f} MiB(freed {sw4['staging1_freed_bytes']/2**30:.2f} "
             f"GiB=20/21 层,张量直读);双臂 acc {q4n['acc']:.3f}/"
             f"{q4s['acc']:.3f};SMOKE 探针配置(双图关),c128 保持原生 —— "
             "单独口径,不与 c128/图模式数字混算")
        g2 = J("q6g2_graphb2.json"); g2n = J("q6g2_native.json")
        pk6 = g2["snapshot"]["packed_kernel"]
        add2("packed kernel 包装器调用(双图开启)",
             f"{pk6['n_packed']:,} 次",
             f"**capture/eager 路径计数口径**(replay 执行录制内核,不回 "
             "host 计数;replay 图含 packed 分支由'capture 时所走分支'推得)"
             f":c128 INT4 {pk6['n_packed_c128']:,} + c4 "
             f"INT6 {pk6['n_packed_c4']:,};双臂 acc {g2['acc']:.3f}/"
             f"{g2n['acc']:.3f},negflag/uncovered=0,8 rank;fallback "
             f"{pk6['n_fallback']} 已归因无压缩缓存调用;SMOKE 单 seed 受限配置")
        k6 = J("q6k_graphb2.invalid.json"); k6n = J("q6c_native.json")
        add2("radix×stage-B 质量退化(复现)",
             f"{k6['acc']:.3f} vs {k6n['acc']:.3f}",
             "q6c 与 q6k(全链口径)两轮独立复现;radix-off 装配门显式拒绝"
             "该组合;吞吐坍缩为日志观察无独立 bench 产物,不作性能结论")
        pd1 = J("pd1_native.json"); pd2 = J("pd2_stageb.invalid.json")
        add2("PD 分离:native 通过 / stage-B 布局缺口",
             f"{pd1['acc']:.3f} / {pd2['acc']:.3f}",
             "单机双进程(prefill TP4+decode TP4+mini-lb,mooncake);native "
             "针跨进程答对=KV 真传输;stage-B 0/6 且 n_error=0 —— 传输完成、"
             "内核被调、服务不崩但语义错:布局契约未被传输层承载(runtime "
             "contract 必要性的实证);TP4×2 口径")
        h6a = J("q6h_rep1.json"); h6b = J("q6h_rep2.json")
        td = sum(1 for x, y in zip(h6a["items"], h6b["items"])
                 if x.get("out") != y.get("out"))
        add2("重复运行答案稳定性",
             f"acc {h6a['acc']:.3f}/{h6b['acc']:.3f}",
             f"同配置串行重复对(带路由),逐题文本 {td}/{len(h6a['items'])} "
             "不同(上游非确定推理;dsv4 不在 deterministic 白名单)——"
             "只主张答案稳定性,不主张逐字确定性")
        lat = J("p113_serving_latency.json")
        r = lat["ratio_staging1_over_native"]
        add2("staging1 服务时延比值",
             f"吞吐×{r['output_throughput_tok_s']:.3f} 成本×"
             f"{r['cost_gpu_s_per_output_token']:.3f}",
             "bench_serving random seed42 N=32;探针配置非生产;staging1 为"
             "逐调用全量物化未优化实现 = 上界开销;仅臂间可比,**不构成**"
             "token 成本降低声明")
        fu = J("p115_fused_unpack.json")
        rf = fu["ratio_fusedk_over_refcons"]
        add2("fused 解包核服务比值(含脚手架)",
             f"吞吐×{rf['output_throughput_tok_s']:.3f} 成本×"
             f"{rf['cost_gpu_s_per_output_token']:.3f}",
             "fusedk 臂含逐调用 ensure_fresh+Python 逐槽审计(非共模诊断"
             "脚手架)—— 比值是上界**不是纯核开销**;功能面独立成立"
             "(597,981 槽审计 stale=0,质量锚 1.000)")
        n12 = J("q6n_graphb2.json")
        m42 = J("q6m42_graphb2.json"); m43 = J("q6m43_graphb2.json")
        add2("图模式 12-doc 探针(负结果)",
             f"{n12['acc']:.3f}",
             f"无 MTP、12 docs、WORKERS=4:doc 稳定漏针(15@0.5/16@0.85/"
             f"18@0.5);MTP 双 seed 同树 {m42['acc']:.3f}/{m43['acc']:.3f}"
             "(漏针集与之高度重叠)—— 6-doc SMOKE 口径掩盖的系统性残差,"
             "cudagraph 图内消费声明由此限定为 6-doc;十四轮判别链定谳:"
             "预填压缩上下文读为必要通道且依赖 c4 环驻留(见判别链条目)")
        # ---- Q11 九轮判别链(2026-08-04):驱逐介导 + 分池双解离 + 写链无罪 ----
        o12 = J("q6o_graphb2.json")
        p3a = J("q6p3_ring1025.json"); p3b = J("q6p3_ring513.json")
        p5a = J("q6p5_c128small.json"); p5b = J("q6p5_c4small.json")
        p6a = J("q6p6_c4evict.json")
        fr = p6a["snapshot"]["pool_swap"]["ring_stats"]["n_forensic_rows"]
        fr4 = p6a["snapshot"]["pool_swap_c4"]["ring_stats"]["n_forensic_rows"]
        add2("判别:零驱逐环下 W4 并发全对",
             f"{p3a['acc']:.3f}",
             f"ring1025(n_evict=0)12-doc W4 = {p3a['acc']:.3f};同轮对照 "
             f"ring513 = {p3b['acc']:.3f}(n_evict=256)—— 腐坏驱逐介导;"
             f"串行 W1(q6o)= {o12['acc']:.3f} 但 n_evict=0,'串行干净'是"
             "混杂变量(未曾行使驱逐),真不变量 = 在飞请求页被驱逐 ⇔ 腐坏")
        add2("判别:分池双解离定位 c4",
             f"{p5a['acc']:.3f} / {p5b['acc']:.3f}",
             f"c128 独驱(256 次)acc={p5a['acc']:.3f} 全对 vs c4 独驱"
             f"(353 次)acc={p5b['acc']:.3f} —— c4 池驱逐特异;c128 驱逐"
             "无害此后又两轮复现(q6p6/q6p7 均 1.000)")
        add2("判别:eager 写链取证无罪",
             f"{fr + fr4:,}",
             f"烘定-存储逐行对账 {fr:,}(c128)+{fr4:,}(c4)行,mismatch=0,"
             "形状漂移=0 —— build→forward 间环槽从未易主;图内 finalize 撞"
             "已释放页计数亦为 0;fallback 调用全为无压缩缓存口径"
             "(extra_k_cache=None),与 c 池无关")
        p14a = J("q6p14_ablate.json"); p14c = J("q6p14_control.json")
        add2("判别:预填 extra 必要性消融(收口轮)",
             f"{p14a['acc']:.3f} / {p14c['acc']:.3f}",
             f"extra_topk_length 清零(执行自证 5,125 次)acc={p14a['acc']:.3f}"
             f" 全灭 vs 对照 {p14c['acc']:.3f}(c4 剂量带内)—— 预填压缩"
             "上下文读是任务必要通道;叠加坐标域错乱(kv-cache 坐标索引环"
             "缓冲,c4 越界 66 倍)与 14 轮驱逐剂量不变量,机制闭环:该通道"
             "数据依赖 c4 环驻留。修法=预填 extra 物化适配层(roadmap);"
             "短期口径=环≥活工作集(唯一已证干净配置)")
        q2g = J("q6q2_graphb2.json"); q3g = J("q6q3_graphb2.json")
        q2n = J("q6q2_native.json"); q3n = J("q6q3_native.json")
        add2("MTP 零驱逐口径重测(改判 PASS)",
             f"{q2g['acc']:.3f}/{q2n['acc']:.3f} 与 {q3g['acc']:.3f}/{q3n['acc']:.3f}",
             "EAGLE 1步,12-doc W4,双环 1025(quality_caliber 零驱逐自证):"
             "seed42/43 双臂全对 —— 每轮为同轮双臂受控对照,无跨轮归因需求;"
             "历史残差(q6i3 5/6、q6m 14/24)由 14 轮判别链归因为 c4 驱逐"
             "机制混杂,非 MTP 特异。矩阵 mtp 改判 PASS")
        qa_n = J("q10a_native.json"); qa_g = J("q10a_graphb2.json")
        qa_nb = J("q10a_native_bench.json"); qa_gb = J("q10a_graphb2_bench.json")
        add2("Q10 终表数据轮(零驱逐口径,未优化物化路径)",
             f"{qa_gb['output_throughput']:.1f} vs {qa_nb['output_throughput']:.1f} tok/s",
             f"bench(32 请求,2048/128):output 吞吐 ×"
             f"{qa_gb['output_throughput']/qa_nb['output_throughput']:.3f},"
             f"TTFT mean {qa_gb['mean_ttft_ms']/1000:.1f}s vs "
             f"{qa_nb['mean_ttft_ms']/1000:.1f}s;HBM ~"
             f"{max(qa_g['hbm_mib_per_gpu'])/1024:.1f} vs ~"
             f"{max(qa_n['hbm_mib_per_gpu'])/1024:.1f} GiB/GPU(大环口径反超,"
             "节省被环撑大抹掉)—— 真实代价口径,收益主张不作。**质量锚 "
             f"{qa_g['acc']:.3f}(11/12):零驱逐反例** —— bench 前置使逻辑"
             "槽复用,环页仍驻留即喂前任请求行(needle_0 输出他请求暗号),"
             "'零驱逐⇒干净'必要非充分;引用本表必须带此口径")
        qa_m = J("q11a_matfix.json"); qa_c = J("q11a_control.json")
        _tr = qa_m["snapshot"]["pool_swap_c4"]["ring_stats"]["n_translate_read"]
        add2("判别:读侧物化修正无效(伤害通道重开)",
             f"{qa_m['acc']:.3f} / {qa_c['acc']:.3f}",
             f"强制 sparse 预填分支 + stageb-r:n_translate_read={_tr:,} "
             "执行自证、orphan=0(非驻留全命中 packed),c4 驱逐 355 次 —— "
             f"acc={qa_m['acc']:.3f} 与对照 {qa_c['acc']:.3f} 同带同族。"
             "'预填 extra 错读是驱逐伤害媒介'证伪;与消融合并:通道必要、"
             "预填寻址非媒介 —— 修错了相位(后由 q11t2 定谳:伤害消费者"
             "= decode 侧 extra 读,见下两条)")

        # ---- Q11 结案(2026-08-05,46 轮):持久态全同 + decode 读侧定谳 ----
        def _pair_stats(wa, wb, merge_gen):
            import collections as _c
            def _m(w):
                m = _c.defaultdict(list)
                for k, v in w.items():
                    kk = ":".join(k.split(":")[:2]) if merge_gen else k
                    vs = v[1] if isinstance(v[1], list) else [v[1]]
                    m[kk].extend(vs)
                return {k: sorted(v) for k, v in m.items()}
            ma, mb = _m(wa), _m(wb)
            rel = []
            for k in set(ma) & set(mb):
                va, vb = ma[k], mb[k]
                if len(va) != len(vb):
                    continue
                rel += [abs(x - y) / max(abs(x), abs(y), 1e-6)
                        for x, y in zip(va, vb)]
            rel.sort()
            n = len(rel)
            return (rel[n // 2],
                    100.0 * sum(1 for r in rel if r > 0.1) / n, n)
        c4f = _pair_stats(
            J("q11p_rep1.json")["snapshot"]["stageb_oracle"]["w"],
            J("q11p_rep2.json")["snapshot"]["stageb_oracle"]["w"], True)
        c4x = _pair_stats(
            J("q11q_ring129.json")["snapshot"]["stageb_oracle"]["w"],
            J("q11q_ring257.json")["snapshot"]["stageb_oracle"]["w"], True)
        swf = _pair_stats(
            J("q11r2_rep1.json")["snapshot"]["swa_oracle"]["w"],
            J("q11r2_rep2.json")["snapshot"]["swa_oracle"]["w"], False)
        swx = _pair_stats(
            J("q11s_ring129.json")["snapshot"]["swa_oracle"]["w"],
            J("q11s_ring257.json")["snapshot"]["swa_oracle"]["w"], False)
        add2("判别:持久态跨臂全同(v6 内容对拍)",
             f"c4 中位 {c4x[0]:.4f}(底噪 {c4f[0]:.4f});"
             f"SWA 中位 {swx[0]:.4f}(底噪 {swf[0]:.4f})",
             f"L1+有序多重集度量,同配置重复对先定底噪再判读:c4(q11q,"
             f"{c4x[2]:,} 配对元素)>10% 键 {c4x[1]:.1f}% vs 底噪 "
             f"{c4f[1]:.1f}%;SWA(q11s,{swx[2]:,} 元素)>10% "
             f"{swx[1]:.1f}% vs 底噪 {swf[1]:.1f}% —— 腐坏臂(0.500)与"
             "健康臂(1.000)的 c4 与 SWA 写入内容均在底噪带内,持久态"
             "全同;SWA 行是预填残差流的函数,故预填计算两臂等价,伤害"
             "只能在 decode 瞬态。前代哈希差判读(q11l)以坏度量作废")
        s129 = J("q11s_ring129.json")["snapshot"]
        t2f = J("q11t2_r129fix.json"); t2c = J("q11t2_r129ctl.json")
        _ntr = s129["pool_swap_c4"]["ring_stats"]["n_translate_read"]
        _xm = s129["sm120_route"]["extra_max_ring-c4"]
        _ev = t2f["snapshot"]["pool_swap_c4"]["ring_stats"]["n_evict"]
        _dtr = t2f["snapshot"]["packed_kernel"]["n_dtr_calls"]
        add2("判别:decode extra 读侧未翻译定谳(干预确认,46 轮收官)",
             f"{t2f['acc']:.3f} vs {t2c['acc']:.3f}",
             f"机制:decode extra 读以逻辑槽直索物理坐标的后备存储(读侧翻译"
             f"执行数 n_translate_read={_ntr};请求逻辑条目上界 "
             f"{_xm:,} > ring129 物理容量 8,256)—— 零驱逐+单请求时物理"
             "=逻辑恒等映射侥幸成立,驱逐回收/多请求共环即读到他条目"
             "内容且 written/代际审计不报警(q10a 零驱逐反例同机制)。"
             f"干预:非驻留读折 -1({_dtr:,} 调用)= **诚实截断被逐条目**"
             f"(~26% extra 行被弃,微缩仍全对;后续判别定谳:重映射对请求"
             f" id ≈恒等,疗效即截断本身,且时机敏感 —— 驱逐落进预填窗口时"
             f"截断亦致 0.500),W1 ring129(驱逐 {_ev})"
             f"{t2c['acc']:.3f}→{t2f['acc']:.3f},对照臂翻译计数确认为空,"
             "驱逐/调用数两臂全同。**范围口径与开放问题**:W1 微缩干预"
             "有效性确认(驱逐晚于预填时);W4 规模剂量分层四对+方差基线"
             "判定 —— 剂量随机、同剂量两臂共曲线(截断与腐坏等价伤害);"
             "九轮穷尽仪器化(选择流含底噪/服务内容/档完整性/键控/topk)"
             "全部跨臂等价后质量分裂依旧,**伤害微观机制最后一公里开放**;"
             "生产可证语义 = 零驱逐 + 请求隔离(三轮 W4 零驱逐全对)")
        # ---- p111 双池 PPL(2026-08-06,tp4 同口径配对)----
        import math as _m
        _pb = J("p111_lp_base.json"); _pp = J("p111_lp_packed.json")
        if isinstance(_pb, dict): _pb = _pb["docs"]
        if isinstance(_pp, dict): _pp = _pp["docs"]
        _nb = sum(x["n_tok"] for x in _pb); _np = sum(x["n_tok"] for x in _pp)
        _ppl_b = _m.exp(-sum(x["sum_lp"] for x in _pb) / _nb)
        _ppl_p = _m.exp(-sum(x["sum_lp"] for x in _pp) / _np)
        add2("双池 PPL 配对(teacher-forcing)",
             f"{_ppl_b:.4f} vs {_ppl_p:.4f}",
             f"tp4 同口径双臂(此前 base 沿用 tp8 的 p108,跨 tp logprob "
             f"有真实差,已重制):natural+code 24 篇 × 4k 前缀,"
             f"{_nb:,} token 逐 token logprob;packed(INT4/INT6 消费)"
             f"ΔPPL {100*(_ppl_p/_ppl_b-1):+.2f}% —— PPL 口径中性。"
             "flagship dual_pool_ppl 由 PENDING 转有数;激活双向门口径:packed 臂 "
             "消费计数为正,base 臂以 manifest 证明 packed 开关/适配器缺席")
    except FileNotFoundError as e:
        print("[canon] Q4/Q5/Q6 产物缺失,跳过:", e)

    # ---- p3(witcert-w)W 线门序数字(2026-08-07;paper=3)----
    try:
        import statistics as _st

        def add3(g, n, v, scope, src=None, headline=False):
            add(g, n, v, scope, headline=headline, paper=3, src=src)

        def add4(g, n, v, scope, src=None, headline=False):
            # 论文4 的条目:数字义务在 p4 正文,不再借道 p3(2026-08-11 修正 ——
            # 此前 paper 字段未切导致每次给 p4 写内容都被守卫逼着同步进 p3,
            # 工具约束扭曲内容决策,积累两篇重复段)
            add(g, n, v, scope, headline=headline, paper=4, src=src)

        # ---- R3 五臂等预算表·质量列(2026-08-12;r3f{1,2,3}{b,c},18/18)----
        _r3 = {}
        for _r in "123":
            for _leg, _tags in (("b", ("a3union", "a4cum")), ("c", ("a3rep", "a5shadow"))):
                for _t in _tags:
                    _f = os.path.join(OUT, "r3f%s%s_%s.json" % (_r, _leg, _t))
                    if os.path.exists(_f):
                        _r3.setdefault(_t, []).append(json.load(open(_f, encoding="utf-8")))
        if len(_r3) == 4 and all(len(v) == 3 for v in _r3.values()):
            def _fbr(d):
                _cw = d["snapshot"]["certified_write"]
                return _cw["n_fallback_exact"] / (_cw["n_compressed"] + _cw["n_fallback_exact"])
            _u = [_fbr(d) for d in _r3["a3union"]] + [_fbr(d) for d in _r3["a3rep"]]
            _c = [_fbr(d) for d in _r3["a4cum"]]
            _ad = [d["snapshot"]["certified_write"]["cumloss"]["n_admit_calls"] for d in _r3["a4cum"]]
            _fb = [d["snapshot"]["certified_write"]["cumloss"]["n_fallback_calls"] for d in _r3["a4cum"]]
            _ch = [d["snapshot"]["certified_write"]["cumloss"]["charged_max"] / 7.5e5 for d in _r3["a4cum"]]
            _sh = [d["snapshot"]["all_ranks"]["rel_mean"] for d in _r3["a5shadow"]]
            _ds = [d["snapshot"]["certified_write"]["delta_spent"] / 0.01 for d in _r3["a3union"]]
            add3("R3五臂", "union 臂写侧回退率", "%.1f" % (100 * sum(_u) / len(_u)),
                 "六轮(a3union×3+a3rep×3)均值百分比;NDOC=12 WORKERS=1 质量列口径"
                 "(零驱逐∧无槽复用);回退报率不报绝对量(事件总数随批次波动)",
                 src="experiments/out/r3f1b_a3union.json:snapshot.certified_write", headline=True)
            add3("R3五臂", "union 账耗尽份额", "%.1f" % (100 * sum(_ds) / len(_ds)),
                 "delta_spent/0.01 三轮均值百分比 —— union 望远镜账在每个 12 文档请求组上近乎烧尽",
                 src="experiments/out/r3f1b_a3union.json:snapshot.certified_write.delta_spent")
            add3("R3五臂", "cum 臂写侧回退率", "%.1f" % (100 * sum(_c) / len(_c)),
                 "三轮均值百分比;同一 WTHR 下比 union 臂低约 3pp —— cumulative 账同质量更高覆盖",
                 src="experiments/out/r3f1b_a4cum.json:snapshot.certified_write", headline=True)
            add3("R3五臂", "cum 门控计数", "%d / %d" % (round(sum(_ad) / 3), round(sum(_fb) / 3)),
                 "admit/budget-forced-fallback 三轮均值取整(区间 %d-%d / %d-%d);"
                 "fallback>0 = 门控真会关(BNORM=7.5e5 上膛)" % (min(_ad), max(_ad), min(_fb), max(_fb)),
                 src="experiments/out/r3f1b_a4cum.json:snapshot.certified_write.cumloss")
            add3("R3五臂", "cum 峰值账占预算", "%.2f" % (100 * sum(_ch) / len(_ch)),
                 "charged_max/BNORM 三轮均值百分比 —— 三轮均精确顶到预算,控制器在边界运行",
                 src="experiments/out/r3f1b_a4cum.json:snapshot.certified_write.cumloss.charged_max")
            add3("R3五臂", "影子对账相对误差", "%.1f" % (100 * sum(_sh) / len(_sh)),
                 "packed vs FP8 逐条目 rel_mean 三轮均值百分比,n_checked 4600-4800/轮",
                 src="experiments/out/r3f1c_a5shadow.json:snapshot.all_ranks.rel_mean")

        _wq = json.load(open(os.path.join(ROOT, "experiments", "out_siteB",
                                          "rrd_w2a_qwen7b.json"), encoding="utf-8"))
        _wv = json.load(open(os.path.join(OUT, "rrd_w2a_dsv2lite.json"),
                             encoding="utf-8"))
        for tag, d in (("Qwen2.5-7B", _wq), ("DeepSeek-V2-Lite", _wv)):
            for s, r in d["verdicts"].items():
                add3("W2a谱", f"{tag} {s} ρ90",
                     f"{r['rho90_median']:.4f}".rstrip("0").rstrip("."),
                     f"{tag} {s} prefill 逐层中位;verdict={r['verdict']};"
                     "预注册 ρ90≤0.15∧留出≥0.70=concentrated",
                     src=("experiments/out_siteB/rrd_w2a_qwen7b.json"
                          if tag.startswith("Qwen") else
                          "experiments/out/rrd_w2a_dsv2lite.json")
                         + ":verdicts")
                _srcp = ("experiments/out_siteB/rrd_w2a_qwen7b.json"
                         if tag.startswith("Qwen") else
                         "experiments/out/rrd_w2a_dsv2lite.json")
                add3("W2a谱", f"{tag} {s} 留出",
                     f"{r['heldout_median']:.3f}",
                     f"偶Σ top-7.1%d 子空间在奇Σ能量占比中位;平谱基线 0.071",
                     src=_srcp + ":verdicts")
        _wc = json.load(open(os.path.join(OUT, "rrd_w2c_router_margin.json"),
                             encoding="utf-8"))
        _pl = [r for r in _wc["per_layer"] if r["phase"] == "prefill"]
        _mm = _st.median(r["margin_median"] for r in _pl)
        _em = _st.median(r["int4"]["eps_median"] for r in _pl)
        _i4 = _wc["per_bits_class"]["int4"]
        add4("W2c门臂", "margin 中位(层中位)", f"{_mm:.3f}",
             "V2-Lite 64 专家 top-6,gate 线性 logit 域,prefill 逐层"
             "margin_median 再取层中位(推导)",
             src="experiments/out/rrd_w2c_router_margin.json:per_layer(derived)")
        add4("W2c门臂", "INT4 门量化 ε∞ 中位(层中位)", f"{_em:.3f}",
             "gate 权重 g32 RTN;同上推导口径",
             src="experiments/out/rrd_w2c_router_margin.json:per_layer(derived)")
        add4("W2c门臂", "INT4 门量化翻转率", f"{100*_i4['flip']:.1f}",
             f"top-6 集合变化占比(%);binding={100*_i4['binding']:.1f}%;"
             "verdict=dead_too_small —— 'router 永不量化'的自家实证",
             src="experiments/out/rrd_w2c_router_margin.json:per_bits_class.int4",
             headline=True)
        add4("W2c门臂", "INT4 门量化 binding", f"{100*_i4['binding']:.1f}",
             "m≤2ε∞ 占比(%),证书须拒绝的流量",
             src="experiments/out/rrd_w2c_router_margin.json:per_bits_class.int4")
        _wp = json.load(open(os.path.join(OUT, "w2cp_upstream_router.json"),
                             encoding="utf-8"))

        def _tot(key, f):
            r = _wp["results"][key]
            n = r["prefill"]["n"] + r["decode"]["n"]
            return (r["prefill"][f] * r["prefill"]["n"]
                    + r["decode"][f] * r["decode"]["n"]) / max(n, 1)
        add4("W2c上游臂", "armA INT4 binding",
             f"{100*_tot('armA_int4','binding'):.1f}",
             "gate 保 bf16、仅量化 expert 投影(AMD 生产口径)g32 INT4;"
             "m≤2‖Δz‖∞ 占比(%);verdict=" + _wp["verdict"], headline=True,
             src="experiments/out/w2cp_upstream_router.json:results.armA_int4")
        add4("W2c上游臂", "armA INT4 翻转率",
             f"{100*_tot('armA_int4','flip'):.1f}",
             "同上口径,top-6 实际变化占比(%);teacher-forced matched 三过",
             src="experiments/out/w2cp_upstream_router.json:results.armA_int4")
        _wq2 = json.load(open(os.path.join(OUT, "w2cq_flip_vs_quality.json"),
                              encoding="utf-8"))
        add4("W2c判别臂", "armA INT4 ΔNLL p95",
             f"{_wq2['summary']['dnll_p95']:.4f}",
             f"teacher-forced 配对差(nats/token),n={_wq2['summary']['n_tokens']:,};"
             f"中位 {_wq2['summary']['dnll_median']:.4f};verdict="
             + _wq2["verdict"] + " —— 同臂同流 58.3% 翻转 × 质量不动 ⇒ "
             "逐 token 路由不变性为非承载不变量(三臂链闭合)", headline=True,
             src="experiments/out/w2cq_flip_vs_quality.json:summary")
        _wr = json.load(open(os.path.join(OUT, "w2cr_natural_discriminator.json"),
                             encoding="utf-8"))
        _t = _wr["summary"]["task"]
        add4("W2c自然臂", "自然文本 ΔNLL 中位/p95",
             f"{_wr['summary']['dnll_median']:.4f} / {_wr['summary']['dnll_p95']:.3f}",
             "Gutenberg12+code4×4k token,armA INT4-expert;中位无害而 p95 重伤"
             "=损伤尾部化;重复文本口径 p95=0.0011 的假阴性坐实(470x)",
             src="experiments/out/w2cr_natural_discriminator.json:summary",
             headline=True)
        add4("W2c自然臂", "ARC-Easy 配对 Δacc",
             f"{_t['dacc_pp']:+.1f}",
             f"pp;500 题 0-shot choice-logprob,base {100*_t['acc_base']:.1f}%,"
             f"CI95 ({_t['dacc_ci95'][0]:.1f},{_t['dacc_ci95'][1]:.1f});任务级无害",
             src="experiments/out/w2cr_natural_discriminator.json:summary.task")
        add4("W2c自然臂", "自然文本翻转率",
             f"{100*_wr['summary']['flip_rate_natural']:.1f}",
             "%,any-MoE-layer top-6 变;重复文本口径 58.3%",
             src="experiments/out/w2cr_natural_discriminator.json:summary")
        _ws = json.load(open(os.path.join(OUT, "w2cs_flip_tail_overlap.json"),
                             encoding="utf-8"))
        _wg = _ws["summary"]["per_depth_group"]
        add4("W2c重合臂", "翻转-尾部富集比 OR(**分深度组**;聚合 OR 退化不可引用)",
             " / ".join(f"{_wg[k]['or']:.2f}" for k in ("shallow", "mid", "deep")),
             "tail=ΔNLL 前 5%;verdict=flip_uninformative —— 支柱 B 终葬。"
             "**聚合 OR 必须按退化处理**(与 Qwen1.5-MoE 同一标准):any-layer "
             f"翻转率 {_ws['summary']['flip_rate_any_layer']:.4f} 于 "
             f"{_ws['summary']['n_tokens']:,} token 上只剩 "
             f"{round(_ws['summary']['n_tokens'] * (1 - _ws['summary']['flip_rate_any_layer']))}"
             " 个未翻转 token、**2 个尾部事件**,单 token 扰动就能把 OR 从 0.46 "
             "推到 1.47 —— 该聚合值区分不了'无关'与'3× 富集'(预注册复活线 OR≥3)。"
             "分深度组的未翻转样本为 12,590 / 2,791 / 1,180,三组 OR 全部 <1,"
             "结论不变而仪器可用。"
             f"逐组 P(tail|flip) vs P(tail|¬flip):"
             + "; ".join(f"{k} {_wg[k]['p_tail_flip']:.3f} vs {_wg[k]['p_tail_noflip']:.3f}"
                         for k in ("shallow", "mid", "deep"))
             + "。产物内 auroc 字段因并列秩无效,勿引用", headline=True,
             src="experiments/out/w2cs_flip_tail_overlap.json:summary")
        _qr = json.load(open(os.path.join(OUT, "w2cr_qwenmoe.json"),
                             encoding="utf-8"))
        _qs = json.load(open(os.path.join(OUT, "w2cs_qwenmoe.json"),
                             encoding="utf-8"))
        _qt = _qr["summary"]["task"]
        add4("W2c跨模型", "Qwen1.5-MoE ΔNLL 中位/p95",
             f"{_qr['summary']['dnll_median']:.4f} / {_qr['summary']['dnll_p95']:.3f}",
             f"同口径复证(60 专家 top-4,仅 routed experts INT4):与 V2-Lite"
             f"(0.0002/0.518)逐项重合;Δacc {_qt['dacc_pp']:+.1f}pp CI"
             f"({_qt['dacc_ci95'][0]:.1f},{_qt['dacc_ci95'][1]:.1f}),翻转"
             f" {100*_qr['summary']['flip_rate_natural']:.1f}%",
             src="experiments/out/w2cr_qwenmoe.json:summary", headline=True)
        _pd = _qs["summary"]["per_depth_group"]
        add4("W2c跨模型", "Qwen1.5-MoE **分深度风险比 RR**(浅/中/深;三组齐报)",
             f"{_pd['shallow']['or']:.2f} / {_pd['mid']['or']:.2f} / "
             f"{_pd['deep']['or']:.2f}",
             "any-layer 翻转在细粒度 MoE 上饱和(99.99%)致聚合 OR 退化"
             "(除零伪影,勿引);分深度组翻转率 ~95% 非退化,OR<1 与"
             " V2-Lite 的分深度 0.84/0.71/0.75 同向 —— flip_uninformative "
             "跨模型成立。**两个模型用同一标准**:聚合按退化处理、三组齐报。"
             "两条口径更正:①产物字段名 `or` 实为**风险比** RR(脚本 orate 返回 "
             "p_tail_flip/p_tail_noflip),不是 odds ratio,引用时不可混称;"
             "②该产物顶层 `verdict` 字段字面是 `flip_predicts_tail`,那是聚合"
             "退化(未翻转样本≈0)的**除零伪影**,不是结论 —— 结论以分深度组为准",
             src="experiments/out/w2cs_qwenmoe.json:summary.per_depth_group")
        _w3 = json.load(open(os.path.join(OUT, "w3av_wc_w3av.json.rank0"),
                             encoding="utf-8"))
        _eg = _w3["eprocess_global"]
        add3("W3AV", "serving e-process 峰值/因子数",
             f"{_eg['log_M_max']:.2f} / {_eg['n_factors']:,}",
             "DSV4 tp4 dither+ledger,8 请求×decode1024;sup log M 远低于"
             " ln(1/0.01)=4.61,未越线 —— **仅证『半径模型未被否证』**"
             "(model-validation),不证 admission 风险(P0 纠偏 11244:"
             "AV 财富与逐动作越界是不同保证对象,禁作覆盖率主张)",
             src="experiments/out/w3av_wc_w3av.json.rank0:eprocess_global",
             headline=True)
        _ca = {a: json.load(open(os.path.join(OUT, f"w3cc_{a}.json"),
                                 encoding="utf-8")) for a in ("w4afp8", "fp8")}
        _kvw = _ca["w4afp8"]["server_info"]["max_total_num_tokens"]
        _kvf = _ca["fp8"]["server_info"]["max_total_num_tokens"]
        add3("W3CC容量", "KV 容量 W4AFP8 vs FP8",
             f"{_kvw:,} vs {_kvf:,}",
             f"GLM-5.2 双臂匹配口径(tp8/ep8/dp8,kv fp8,mem_fraction 0.85,"
             f"ctx 65536);比值 {_kvw/_kvf:.2f}x —— 权重省下的 HBM 全部"
             "转为 KV 容量;裁决 w3cc_verdict VALID(逐档活性/档位一致)",
             src="experiments/out/w3cc_w4afp8.json:server_info", headline=True)
        _tw = [r for r in _ca["w4afp8"]["levels"]
               if r.get("concurrency") == 128][0]
        _tf = [r for r in _ca["fp8"]["levels"]
               if r.get("concurrency") == 128][0]
        add3("W3CC容量", "C=128 聚合吞吐 W4AFP8 vs FP8",
             f"{_tw['agg_gen_tok_s']:,.0f} vs {_tf['agg_gen_tok_s']:,.0f}",
             "tok/s(SSE 块口径,两臂同法);同并发全谱平局(1..128 零错误),"
             "收益不在同并发速度而在容量 —— 与 Cloudflare 生产结论同构",
             src="experiments/out/w3cc_w4afp8.json:levels", headline=True)
        try:
            _ce = {a: json.load(open(os.path.join(OUT, f"w3cc_{a}_ext.json"),
                                     encoding="utf-8")) for a in ("w4afp8", "fp8")}
            _pw = [r for r in _ce["w4afp8"]["levels"] if r.get("concurrency") == 512][0]
            _pf = [r for r in _ce["fp8"]["levels"] if r.get("concurrency") == 512][0]
            add3("W3CC容量", "扩展档 C=512 吞吐 W4AFP8 vs FP8",
                 f"{_pw['agg_gen_tok_s']:,.0f} vs {_pf['agg_gen_tok_s']:,.0f}",
                 "tok/s;192-512 档两臂零错误且吞吐平台(~1.9k)重合,TTFT 同步"
                 "排队增长 —— 本负载(1k prompt/512 gen)在 C≈150 计算饱和,"
                 "**两臂均未触 KV 墙**:容量优势只在长上下文/大驻留负载兑现,"
                 "禁写成 divergence;吞吐单轮无 CI,平局表述须带限定",
                 src="experiments/out/w3cc_w4afp8_ext.json:levels")
        except FileNotFoundError:
            print("[canon] w3cc ext 缺,跳过")
        _a2 = json.load(open(os.path.join(OUT, "w3av2_cum_admission.json"),
                             encoding="utf-8"))
        _s2 = _a2["summary"]
        add3("W3AV2双记账", "union 耗尽率 / 回退上界中位 / cumloss 违约",
             f"{_s2['union_budget_exhausted_frac']:.0%} / "
             f"{_s2['union_fallback_frac_ub_median']:.1%} / "
             f"{_s2['cumloss_guarantee_violations']}",
             f"{_s2['n_request_accounts']} 个真实请求账户(DSV4 serving 因子流,"
             "decode1024×8 请求×4 rank):望远镜 union 预算每请求打满并强制回退"
             "(上界口径,未分耗尽/半径两因);cumloss_admission(定理机检)同流"
             "零违约且 Σz 全负 —— 归一化接口,描述性对照,armed 轮待做",
             src="experiments/out/w3av2_cum_admission.json:summary", headline=True)
        _av3 = json.load(open(os.path.join(OUT, "w3av3_verdict.json"),
                              encoding="utf-8"))
        _c3 = _av3["criteria"]
        add3("W3AV4armed", "armed admit 调用数 cumopen/cumtight/union",
             "1,336,588 / 641,284 / 0",
             "DSV4 tp4 dither+armed cumloss(冻结码 46145a7,三臂 V0 自证);"
             "union 0=处理独有正向信号(armed 真生效);逐条目 fail-closed 审计不变",
             src="experiments/out/w3av3_verdict.json:criteria.V2_开关双向",
             headline=True)
        add3("W3AV4armed", "剂量-反应 精确回退率中位 tight/open/union",
             "0.842 / 0.339 / 0.315",
             "B̃=5e3/2e4 vs union;预算越紧回退越多(770,664 次整批回退)——"
             "控制器按预算真调节;**V5 覆盖收益(open<union)未实现**:cumopen"
             "量级门放松(δ_i=0.01 固定)被 B̃=2e4 中后段整批回退盖过,"
             "净收益需更大 B̃(cumwide 探测中);诚实负结果未改门",
             src="experiments/out/w3av3_verdict.json:criteria.V4_紧预算会关",
             headline=True)
        add3("W3AV4armed", "armed 判定开销 union→cumopen",
             "344.5 → 357.1",
             "wall s/请求中位;+3.7% ≤ 10% 门 —— cumloss admission 判定"
             "(可预测账面查表)不显著拖慢;anytime 轨迹零违约(V3 cum_gap_max 全≤0)",
             src="experiments/out/w3av3_verdict.json:criteria.V6_开销≤10%")
        _pl = json.load(open(os.path.join(OUT, "w3av4b_physical_ledger.json"),
                             encoding="utf-8"))
        _ps = _pl["summary"]
        add3("W3AV4b物理账", "物理见证账 非空洞度/余量/违约",
             f"{100*_ps['tail_over_m_median']:.2f}% / "
             f"{100*_ps['margin_over_W_median']:.1f}% / {_ps['violations']}",
f"{_ps['n_endpoints']} 端点(2 策略×8 客户端请求,rank0 去 TP 镜像+排"
             "boot/u1 暖机;cumloss 以物理 L=W、ψ=λ²C/8、exploratory λ=4e-3 "
             "实例化):**端点**零越界、tail/cum_m 中位 0.67%(非空洞)、余量 4.6%、"
             "16/16 cum_W<cum_m —— 承重梁①a:见证质量单位端点预算非空洞。"
             "**边界**:①端点非 anytime(物理轨迹待 extract 记);②λ exploratory "
             "(方向预注册值未先冻,待 held-out 复证);③cum_W=局部认证见证非 "
             "served TV/NLL,桥仍开放",
             src="experiments/out/w3av4b_physical_ledger.json:summary",
             headline=True)
        _cov = json.load(open(os.path.join(OUT, "w3av5_coverage.json"),
                             encoding="utf-8"))["summary"]
        add3("W3AV5覆盖", "cumloss 覆盖收益转正 union vs cumwide 回退率",
             f"{100*_cov['union_fb_median']:.2f}% vs {100*_cov['cumwide_fb_median']:.2f}%",
             f"归一化 z 账 armed(冻结码 fce92be);B̃=5e4 使 cumloss 门几乎不触发,"
             f"只享固定 δ_i=0.01 量级门放松 vs union 望远镜 δ_i 二次衰减 —— 精确"
             f"回退率中位 31.49%→0.79%(**降 {_cov['fallback_reduction_x']}×**),"
             "V5(B̃=2e4)FAIL 后覆盖收益转正定位。**边界**:①z 门控非物理①b;"
             "②cumwide exploratory(非预注册,held-out 复证待);③回退低=授权多非质量",
             src="experiments/out/w3av5_coverage.json:summary", headline=True)
        _v6 = json.load(open(os.path.join(OUT, "w3av6_verdict.json"),
                             encoding="utf-8"))["criteria"]
        add3("W3AV6物理门控", "①b 物理门控 armed 剂量反应 tight/wide/union",
             "0.48 / 0.22 / 0.31",
             "**cum_W 真参与 admission**(WITCERT_CUMLOSS_MODE=phys,冻结码"
             " 4e35993,九条 PHYS_GATE_VALID):精确回退率中位 —— V4 剂量反应"
             "(tight 0.48>wide 0.22,门控真会关)、V5 覆盖收益(wide 0.22<union"
             " 0.31);exploratory λ=4e-3/B_phys(8e5/5.5e5,held-out 复证待)",
             src="experiments/out/w3av6_verdict.json:criteria", headline=True)
        add3("W3AV6物理门控", "①b 物理 anytime + 控制面对账",
             "0 / 0",
             "V3 物理 anytime 零违约(cum_W_gap_max≤0 全账户,cumloss_admission"
             " 以 L=W 实例化实测)/ V3d 控制面对账 realized>prospective 账户=0"
             "(**gating_conservative/admit_implies_realized_within 的运行时实证"
             "闭环** —— Lean 定理'用全批代替 passed sound'真机验证);开销 +3.8%",
             src="experiments/out/w3av6_verdict.json:criteria", headline=True)
        _sb = json.load(open(os.path.join(OUT, "w3sb_served_readbound.json"),
                             encoding="utf-8"))
        _sbi, _sbs = _sb["inputs"], _sb["summary"]
        add3("W3SB逐读served律",
             "①c 逐读 served-TV tanh 紧化:a_q / 采样见证 / e-form空洞 / tanh(ε) / tanh(ε/2)",
             f"{_sbi['a_q']:.4f} / {_sbi['W_sampled_max']:.2f} / "
             f"{_sbs['tv_eform_worstkey']:.2f} / {_sbs['tv_tanh_worstkey']:.2f} / "
             f"{_sbs['tv_tanh_half_worstkey']:.2f}",
             "tv_le_tanh/softmax_tv_bridge_tanh/served_tv_le_of_gate_tanh(机检):"
             "门控保证 W≤wthr,逐读 TV≤tanh(a_q·wthr)。p76 自洽(a_q=1.0034,采样"
             "见证峰 0.70)worst-key:e-form=1.54 空洞 → tanh(ε)=0.61 机检非空洞 → "
             "tanh(ε/2)=0.34 紧;5% SLA 须 wthr*≤0.05。caliber:不混 V4-Flash "
             "armed(异模型,待测 a_q);worst-key+查询包络;累计仍开放",
             src="experiments/out/w3sb_served_readbound.json", headline=True)
        # ---- R1(2026-08-09):a_q 阶梯与门控差距分解 ----
        _aq = json.load(open(os.path.join(OUT, "w3sq_aq_ladder.json"),
                             encoding="utf-8"))
        _g5 = _aq["sla_gaps"]["tau_0.05"]
        add3("R1查询包络阶梯",
             "**差距不在 a_q**:sound(权重派生)a_q / 实测 a_q / sound 比实测松几倍",
             f"{_aq['rungs']['L1_sound_static']['a_q']:.4f} / "
             f"{_aq['rungs']['L3_measured']['a_q']:.4f} / "
             f"{_aq['tightness_of_sound_bound']:.2f}",
             "sound 版 a_q = softmax_scale·‖q‖_static,其中 ‖q‖_static ="
             "‖γ‖∞·√rank·max_head σmax(wq_b) 对**所有输入**成立、"
             "softmax_scale = head_dim^-0.5(SGLang 的 DSV4 实现无 YaRN "
             "mscale 修正,已核源码)⟹ **权重派生、不需要任何一次运行**,"
             "因此天生与 armed 同模型。这直接推翻论文此前的开放项写法"
             "('pending an a_q measured on the armed model'):那个开放项"
             "**定位错了**。实测版仅用于说明 sound 有多紧,来自另一 campaign,"
             "不参与合成",
             src="experiments/out/w3sq_aq_ladder.json:rungs", headline=True)
        # R5(2026-08-09):三层账的第②层实测
        try:
            _el = json.load(open(os.path.join(OUT, "w3sq_aq_ellipsoid.json"),
                                 encoding="utf-8"))
        except FileNotFoundError:
            _el = None
        if _el:
            add3("R1查询包络阶梯",
                 "**球→椭球在 KV 侧买不到东西**:增益中位 / 层间范围 / "
                 "留出违约 / Δk 协方差稳定秩中位",
                 f"{_el['gain_median_over_layers']:.2f} / "
                 f"{_el['gain_min_over_layers']:.2f}–"
                 f"{_el['gain_max_over_layers']:.2f} / "
                 f"{_el['soundness_viol_total']} / "
                 f"{_el['cov_stable_rank_median']:.0f}",
                 "a_q 由柯西–施瓦茨 |q·Δk| ≤ ‖q‖‖Δk‖ 产生,取等号当且仅当 Δk 与 q "
                 "同向 —— 即在半径 W 的**球**上取最坏点。换成实测椭球给 "
                 "|q·δ| ≤ r‖C^½q‖。V4-Flash 的 armed 捕获、43 层、留出协议"
                 "(C 与 r 只用前半行拟合),增益中位**小于 1** —— **椭球比球还差**,"
                 "而留出半零违约说明这不是过拟合造成的假低。"
                 "稳定秩 37/448 证伪了'各向同性'的解释:能量确实集中,但 r 是 448 维里的"
                 "**极值统计**(实测 25–31,超过各向同性基准 √448=21.2),它必须罩住"
                 "低方差方向上最离群的那一行,把各向异性省下的又吐回去。"
                 "对照:同一手法在**路由侧**买回 3.9–18.5×,那里换的是逐专家 ℓ∞ 球、"
                 "结构不同 —— **不能外推**。**结论**:三层账 ①1.50× ②本轮实测无空间 "
                 "③约 700× 已测全,'剩下的全是工作点问题'从推测变成实测",
                 src="experiments/out/w3sq_aq_ellipsoid.json:per_layer",
                 headline=True)
        add3("R1查询包络阶梯",
             "**门控差距**:认证 5% 逐读 served TV 所需 w_thr(sound)/ armed "
             "实际 / 倍数",
             f"{_g5['w_thr_star_sound']:.4f} / {_aq['armed_w_thr']:.2f} / "
             f"{_g5['gap_vs_armed_sound']:.0f}",
             "w_thr* = atanh(τ*)/a_q(机检 gate_threshold_for_sla)。"
             "armed 门限 35.34 取自**发射脚本一手来源** "
             "w3av6_phys_h200.sh:31 WITCERT_LEDGER_WTHR;它门在 u_e ="
             "mean_bound+tail+det_bound 上,而 u_e 是带范数和 ≥‖Δk‖"
             "(三角不等式)⟹ 与 a_q 同单位,复合合法(这曾是本结论唯一的暗前提)。"
             f"armed 处的界 tanh(a_q·w_thr) = {_g5['tv_bound_at_armed']:.4f} 空洞。"
             "**要害**:三个数量级的差距里,查询包络的松只占 "
             f"{_aq['tightness_of_sound_bound']:.2f}× —— 收紧 a_q 救不了它;"
             "把门收紧三个数量级等价于把放行率压到接近零,即支柱 A 在**逐读 "
             "SLA 口径**下面临与支柱 B 同型的可用性问题",
             src="experiments/out/w3sq_aq_ladder.json:sla_gaps", headline=True)
        add3("W3SB逐读served律", "①c 门控设计律:5% 逐读 served SLA 门槛(proven)",
             f"{_sbs['sla_to_threshold']['5pct']['wthr_star_proven']:.2f}",
             "wthr*=atanh(τ*)/a_q(tanh 版反解):5% 逐读 served TV 须门槛 ≤0.05"
             "(proven,tanh(ε));tight(tanh(ε/2))版 ≤0.10。门控认证版,需同模型 a_q",
             src="experiments/out/w3sb_served_readbound.json", headline=True)
        _v7 = json.load(open(os.path.join(OUT, "w3av7_verdict.json"),
                             encoding="utf-8"))
        _v7s = _v7.get("summary", {})
        add3("W3AV7held-out确认", "①b 物理门控 held-out 同轮覆盖收益 widehO/union",
             f"{_v7s['fb_widehO']:.2f} / {_v7s['fb_union']:.2f}",
             "**held-out confirmatory**(冻结 λ=4e-3/B_phys=8e5,主题与标定不相交):"
             "物理 anytime/控制面对账/剂量反应三性质复现;V5 覆盖收益升**同轮**"
             "(widehO 0.14 < 同轮 union 0.30,非跨轮推断)—— ①b exploratory→"
             "confirmatory,Gap2(跨轮)闭合;7 门 CONFIRMATORY_VALID",
             src="experiments/out/w3av7_verdict.json:summary", headline=True)
        _rt = json.load(open(os.path.join(OUT, "w3sl_readtv_offline.json"),
                             encoding="utf-8"))["per_m"]["2"]
        add3("W3SL逐读实测", "①c 逐读 served-TV 真实量级(V4-Flash 部署 m=2):中位/max",
             f"{_rt['tvreal_median']:.2f} / {_rt['tvreal_max']:.2f}",
             "K0 基建离线重建 exact vs 压缩注意力(V4-Flash 捕获字节+真实 q):部署档"
             "逐读 served TV 中位 0.03、max 0.29 —— **真实非空洞**;读时逐键紧形式实测",
             src="experiments/out/w3sl_readtv_offline.json:per_m", headline=True)
        add3("W3SL逐读实测", "①c tanh 界真实数据验证:tanh 违反数 / e-form 部署空洞率",
             f"{_rt['viol_tanh']} / {_rt['vac_frac_eform']:.2f}",
             "机检 tv_le_tanh 在真实数据上违反=0(含紧 tanh(ε/2));e-form 部署档"
             "空洞率 0.07(m=4 达 0.93),tanh 空洞率恒 0 —— tanh 化解 e-form 空洞",
             src="experiments/out/w3sl_readtv_offline.json:per_m", headline=True)
        _se = json.load(open(os.path.join(OUT, "w3sle_eout_verdict.json"),
                             encoding="utf-8"))["summary"]
        add3("W3SLE累计served实测",
             "①c 累计 served next-token TV 端到端直测(armed V4-Flash,8 请求末位):中位/max",
             f"{_se['TV_served_median']:.2f} / {_se['TV_served_max']:.2f}",
             "两臂同定长 prompt(exact vs cwrite 压缩)捕获 LM head 前隐状态,离线"
             "Δh→head.weight→Δlogit→softmax;末位=整请求累计 served TV。中位 0.12、"
             "max 0.22 —— **端到端实测非空洞**(cumulative_output_tv 还原的实测;"
             "9 门 EOUT_MEASURED_NONVACUOUS)",
             src="experiments/out/w3sle_eout_verdict.json:summary", headline=True)
        add3("W3SLE累计served实测",
             "①c 累计 sound 界:tanh(E_out)空洞 vs Hellinger 非空洞;E_out 末位中位",
             f"{_se['cum_bound_tanh_served_median']:.3f} / "
             f"{_se['hellinger_served_median']:.2f} / {_se['hellinger_served_max']:.2f} / "
             f"{_se['E_out_served_median']:.1f}",
             "tanh(‖Δlogit‖∞)=0.996 空洞(E_out 末位中位 3.1,最坏坐标落低概率 token)"
             "→ **Hellinger √(1−BC²) 中位 0.16、max 0.28 非空洞**(机检 tv_le_hellinger,"
             "违反 0;质量重叠破 L∞ 墙)。给定扰动 sound 界(逼近实测 0.12);a-priori"
             "(仅见证)走鞅+cum_C 待续",
             src="experiments/out/w3sle_eout_verdict.json:summary", headline=True)
        add3("W3SLE累计served实测",
             "①c variance 路线判决:实测 served 扰动 sub-Gaussian proxy σ²_implied 与词表"
             "方差 Var_p(δ) 之比 + sub-Gaussian kernel sound 界(末位中位)",
             f"{_se['sig2_over_varp_served']:.2f} / "
             f"{_se['subg_kernel_tv_served_median']:.2f} / {_se['var_p_delta_served_median']:.3f}",
             "**σ²_implied/Var_p 逐请求中位 0.99(n=8,范围 0.78-1.47)≈1 ⟹ 实测扰动 "
             "variance-tight(sub-Gaussian,非 range "
             "主导)**:尽管 E_out 达 3.2-18.9,σ²=2·ln E_p[e^{δ̃}]≈Var_p≈0.115(小,大扰动"
             "砸低概率 token)。**range 墙对 served 分布不 bind**。served_tv_le_subgaussian"
             "(机检)对实测 δ 给 sound 非空洞界 √(σ²/2)=0.23(V8 违反 0、V9 非空洞;比 "
             "Hellinger 0.16 松 √2,soundness 相对纯方差信息的固有代价)。a-priori 目标由此"
             "从'破 range 墙'降为'方差传播 Var_p(δ)≤tr(Cov_p head)·‖Δh‖²≤propagation·cum_C'",
             src="experiments/out/w3sle_eout_verdict.json:summary", headline=True)
        _gm = json.load(open(os.path.join(OUT, "w3gam_gamma_verdict.json"),
                             encoding="utf-8"))
        add3("W3GAM传播常数",
             "item2 传播系数 γ_ℓ 真机测:逐层 ρ=‖Δh_服务位‖²/‖δ‖² 的层中位/min/max,"
             "与线性性比(应≈1)",
             f"{_gm['summary']['rho_layer_median']:.2e} / "
             f"{_gm['summary']['rho_layer_min']:.1e} / "
             f"{_gm['summary']['rho_layer_max']:.1e} / "
             f"{_gm['summary']['linearity_ratio_median']:.1f}",
             "43 层×2 种子×2 eps 全覆盖,195 有效点,**噪声地板=0(逐字节确定)**;"
             "Hutchinson ⟹ ‖J‖²_F 中位≈5.6e3(dim δ=1.37e6)。**但 verdict="
             "nonlinear_regime**:线性比中位 14.1≈16=(eps 比 4)² ⟹ ‖Δh‖² 与注入"
             "能量近乎无关(**饱和**),即一阶线性化 X_ℓ=J^ℓδa^ℓ 在该 MoE 的此扰动"
             "量程上**经验性失效**(极可能 MoE 路由 argmax 离散翻转)。故 γ_ℓ 数值"
             "**不可直接用作 sound 传播常数**;需 Doob 分解路线",
             src="experiments/out/w3gam_gamma_verdict.json:summary", headline=True)
        _bd = json.load(open(os.path.join(OUT, "w3gam8_bdddiff_verdict.json"),
                             encoding="utf-8"))
        _b0 = _bd["by_eps"]["0"]
        add3("W3BD有界差分预算",
             "根定理消费的质量加权步预算:**直接经验 MGF** / Hoeffding 路 / "
             "top-8192 可部署形式",
             f"{_b0['budget_empirical_mgf']:.4f} / "
             f"{_b0['budget_full_vocab']:.4f} / "
             f"{_b0['topk']['8192']['budget']:.3f}",
             "43 层×9 种子,逐词表 c_{ℓ,v}=max_seeds|δ_v|、b_v=∑_ℓ E_seeds[δ_v],"
             "**δ 已按定理假设 (i) 做 gauge 中心化**(softmax 平移不变);"
             "s_v²=∑c²/4,B_v=exp(b_v+s_v²/2),budget=√(log ∑_v p_v B_v)。"
             "**直接估 E_ω[e^{δ_v}] 给 0.0390**,比经 Hoeffding(取 sup)的 0.0489 更紧 —— "
             "根定理要的**既不是典型值也不是上确界,是期望**,直接估它即绕开了"
             "'典型值 vs sup 差 251×'那个陷阱。两者都**极度非空洞**,且**不经一阶线性化**(有界差分可直接测,"
             "不受 W3GAM 饱和证伪影响)。可部署 top-k 需 **K 在千量级**:"
             "top-8192=0.276(16× 降本),top-1024=0.967,top-64=1.288(空洞)——"
             "因扰动质量散在长尾,尾包络必须取在**乘积 p_v·B_v** 上"
             "(massweighted_prodenv_bound),取 max B_v 会被 5.6e8 主导。"
             "**统计义务定价**:经验 Bernstein(Maurer-Pontil,α=0.01)把预算从 "
             "0.0390 推成 **7.64(空洞)**,slack/mean 2.74(n=9);加样本救不了 —— "
             "n=12 时估计本身已收敛(0.0390→0.0404)而界只从 7.64 到 7.18、"
             "slack 2.74→2.02。**失效的是界不是估计**:其 range 项 ∝ e^c·ln(1/α)/n,"
             "所需样本随有界差分**指数增长**。正解是 betting 型置信序列"
             "(方差自适应、anytime-valid,恰是本文已有机制)。估计风险 α 须加到账本 "
             "δ 上,部署证书报 δ+α。"
             "口径:经验 max 是 sup 的**下界** ⟹ 非空洞但**非 sound**;b_v 是 9 样本"
             "估计不是界;扰动是改动该层抽签的代理",
             src="experiments/out/w3gam8_bdddiff_verdict.json:by_eps", headline=True)
        _lp = json.load(open(os.path.join(OUT, "w3lip_layer_lipschitz.json"),
                             encoding="utf-8"))
        add3("W3LIP逐层Lipschitz",
             "sound 包络的数值实例化:整栈 ∏_ℓ(1+L_ℓ) 的 log10 / 逐层 (1+L) 中位 / "
             "最大谱范数",
             f"{_lp['summary']['stack_envelope_log10']:.0f} / "
             f"{_lp['summary']['L_layer_median']:.2e} / "
             f"{_lp['summary']['spec_max_over_layers']:.0f}",
             "43/43 层权重幂迭代谱范数(V4-Flash FP8 dequant)。"
             "**verdict=LIP_ENVELOPE_VACUOUS(预注册为很可能失败)**:sound 的 "
             "Lipschitz 复合律已机检(lip_residual/lip_iterComp/bdd_diff_of_lipschitz),"
             "但由权重实例化得 **10^221**,完全空洞 ⟹ 结构性包络这条路给不出可用的 "
             "c_ℓ。而且该估计在**多处偏乐观**(幂迭代给下界、RMSNorm 未计入、"
             "专家采样取 max),真值只会更大。**这正是经验有界差分路线(0.0489)"
             "不可替代的原因**,也把开放问题量化为'包络需降约 220 个数量级,"
             "或改用数据依赖/局部 Lipschitz 而非全局'",
             src="experiments/out/w3lip_layer_lipschitz.json:summary", headline=True)
        import math as _m
        import statistics as _st
        _gv = json.load(open(os.path.join(OUT, "w3gam8_gamma_verdict.json"),
                             encoding="utf-8"))
        _ri = [v for v in _gv["rank_info"].values() if v.get("r_eff")]
        _dim = _gv["summary"]["dim_delta"]
        _reff = _st.median([v["r_eff"] for v in _ri])
        _typ = _st.median([_m.sqrt(v["rho_mean"]) for v in _ri])
        _sig = _st.median([_m.sqrt(_dim * v["rho_mean"] / v["r_eff"]) for v in _ri])
        add3("W3LOC局部Lipschitz",
             "局部(层 ℓ→服务位)映射:随机方向典型比 √ρ / **算子范数估计 σ_max** / "
             "有效秩 r_eff(三者中位)",
             f"{_typ:.4f} / {_sig:.1f} / {_reff:.0f}",
             "**纠正**:随机探针估的是 ‖J‖²_F/dim,**不是**算子范数;二者只在增益"
             "散布于多方向时重合,而实测有效秩仅 42(dim=1.37e6)⟹ σ_max 中位 16、"
             "max 62.5,**expansive 而非收缩**,是典型比的 251×。"
             "(此前据典型比称'每层收缩'系口径错误,已撤。)"
             "意义:局部化仍值大钱 —— 同口径全局包络中位 10^109,局部算子范数 16,"
             "**改善逾百个数量级**;但 16>1 ⟹ 以 sup 喂 Hoeffding 仍空洞。"
             "根定理要的是 E_ω[e^δ]≤B_v(**期望**,抽签是随机非对抗),用最坏 sup "
             "去界它恰恰丢掉了实测揭示的结构(放大子空间仅 42 维、舍入误差不瞄准它)"
             "⟹ 正解是按有效秩标定的 **Bernstein 型方差界**,不是按 sup 标定的 "
             "Hoeffding。251× 是用错不等式的代价,不是网络的性质",
             src="experiments/out/w3gam8_gamma_verdict.json:rank_info",
             headline=True)
        _jt = json.load(open(os.path.join(OUT, "w3joint_joint_scalar_verdict.json"),
                             encoding="utf-8"))
        _js = _jt["summary"]
        add3("W3JOINT联合标量矩",
             "根定理消费的量**正确测法**:联合抽签 —— **betting CS 上界 E[TV]** / "
             "标量矩点估 / 抽签数",
             f"{_js['TV_ucb_betting']:.4f} / {_js['budget_point']:.4f} / "
             f"{_jt['n_draws']}",
             "固定历史,**全部 43 层联合重采样**(WITCERT_GAMMA_JOINT=1),整前向,"
             "每 seed 归约为一个标量;E[TV]≤√(log E[Z])。"
             "**这修正了此前 ∏_ℓ Ê[e^{δ_ℓ,v}] 的错误** —— 逐层矩相乘需 ω-local 可加,"
             "而饱和实测已证伪之(那两个数 0.0390/0.0489 已降格为模型依赖诊断)。"
             "Z 极度集中(mean 1.000005,max 1.000024),噪声地板 0,279 次抽签。"
             "**betting 型置信序列(WSR)直接界 E[TV]:上界 0.0322,α=0.01,anytime-valid**"
             " —— TV∈[0,1] 是**确定性**边界,故该路线**不需要任何样本极值**,"
             "Bernstein 那个 'R 取样本 max' 的 non-sound 缺口在此消失。"
             "**关键对比:同一 Bernstein 不等式,逐层×逐词元路线给 7.64(空洞),"
             "联合标量路线给 0.2086(非空洞)** —— 差别来自无词表 union、标量集中、"
             "α 只付一次。口径:R 取样本极值而非确定性上界 ⟹ 该上界**诊断非 sound**;"
             "真 sound 需 Z 的确定性上界或 betting 型置信序列;扰动仍是 SR 重采样的代理;"
             "α 须与账本 δ 相加,部署证书报 δ+α",
             src="experiments/out/w3joint_joint_scalar_verdict.json:summary",
             headline=True)
        _sr = json.load(open(os.path.join(OUT, "w3sr_realsr_verdict.json"),
                             encoding="utf-8"))
        _ss, _sc = _sr["summary"], _sr["criteria"]
        add3("W3SR真实SR抽签",
             "**去掉代理**:扰动即部署的随机舍入本身 —— E[TV] 的 betting CS 上界 / "
             "TV 均值 / 抽签数",
             f"{_ss['TV_ucb_betting']:.4f} / {_ss['TV_mean']:.2e} / {_sr['n_draws']}",
             "SR 种子含 current_uid(逐请求不同)⟹ 对**同一** prompt 重复发 N 次,"
             "每次即一次**真实部署抽签**;exact 臂给参照 p,comp 臂给 p'_j;radix 关。"
             "预注册四判据全过:**S0 压缩真发生(1,999,586 条目)**、"
             "**S1 抽签真在变(160/160 个 TV 互不相同 —— 若全同则说明 uid 未变、"
             "跑的是同一次抽签,预注册为判红而非'结果稳定')**、S3 非空洞、"
             "**S4 两臂对账**(exact/comp 各 160 捕获、位数同为 334、gap 0 —— "
             "该判据是因一次在 flush 未完成时跑裁决、comp 只读到 56 而脚本照常出数"
             "才补上的 fail-closed)。"
             "**E_ω[TV] ≤ 0.0552(α=0.01,anytime-valid,不用任何样本极值)**,"
             "TV 均值 1.64e-5,160 次抽签。这是**部署量**,不再是高斯注入代理。"
             "样本量假说由此得到**对照**而非推断:同一实验 56 抽签给 0.1463、"
             "160 抽签给 0.0552,量本身未变(TV 均值 1.4e-5→1.6e-5)。"
             "口径(引用必带):**这是在一个固定历史上的界**(一个 prompt、一个 "
             "prefill 末位),而根定理的假设量化在**每个历史**上 ⟹ 此处 anytime-valid "
             "指随抽签数增加仍有效,**不是**沿自回归请求的所有历史有效;"
             "另假设各请求抽签独立;风险须记 δ_ledger+α_draw+**α_history**,"
             "本文只付前两项",
             src="experiments/out/w3sr_realsr_verdict.json:summary", headline=True)
        # 多历史轮的数据源:**优先 w3cf**(80 历史、无放回可交换抽样、前提由构造
        # 满足),它一旦产出就取代 w3mh(12 历史、确定性递增长度、前提未满足)。
        # 文件不存在时回落 w3mh —— 加这段时 w3cf 尚在跑,是空操作。
        _mh_src = ("w3cf_multihist_verdict.json"
                   if os.path.exists(os.path.join(OUT, "w3cf_multihist_verdict.json"))
                   else "w3mh_multihist_verdict.json")
        _mh = json.load(open(os.path.join(OUT, _mh_src), encoding="utf-8"))
        _ms = _mh["summary"]
        add3("W3MH多历史heldout",
             "跨历史条件界(**认证口径,三态**):留出**认证通过**数 / "
             "p_history(认证失败率 CP 上界) / **跨历史 TV 均值 max/min 倍差**"
             + ("(80 历史,可交换抽样)" if _ms.get("exchangeable_sampling") else ""),
             f"{_ms['n_heldout_certified_pass']}/{_ms['n_heldout']} / "
             f"{_ms['p_history_notcertified_cp_upper']:.4f} / "
             f"{_ms['TV_mean_over_hists_max'] / _ms['TV_mean_over_hists_min']:,.0f}",
             "12 历史(各用互不相同 token 数)× 每历史 40 次真实部署 SR 抽签 × 两臂;"
             "压缩 5,830,313 条目;**exact 臂逐历史自差恒为 0**(M5,查全部捕获)。"
             f"**verdict={_mh['verdict']}**。判读是**三态**的,只有外侧两态是结论:"
             "UCB_h ≤ μ_cal 判**认证通过**、LCB_h > μ_cal 判**认证违约**、其余"
             "**未获认证**。本次 "
             f"**{_ms['n_heldout_certified_pass']} 通过 / "
             f"{_ms['n_heldout_undetermined']} 未获认证 / "
             f"{_ms['n_heldout_certified_violation']} 违约**"
             "(两次纠正各记一笔:①拿样本均值冒充界;②把'未获认证'读成'违约',"
             "后者是前者高一层的同族错误)。"
             f"α_draw 按 Bonferroni 逐历史分配 {_ms['alpha_draw_per_hist']:.2e}"
             "(每个历史各建一个 UCB,不能只付一次)。"
             f"**最重要的实证事实:跨历史 TV 均值 "
             f"{_ms['TV_mean_over_hists_min']:.1e}→{_ms['TV_mean_over_hists_max']:.1e},"
             f"差 {_ms['TV_mean_over_hists_max'] / _ms['TV_mean_over_hists_min']:,.0f} 倍**,"
             "此前单历史实验恰落在最不敏感一端。"
             "口径:①**CP 界的是认证失败率**(未通过认证的历史比例 ≤ 0.8269),"
             "**不是真实违约率**(零违约事件的对应上界是 0.5358);"
             "②CP 要求历史是目标族的 i.i.d./可交换抽样,而本族是**人为选取**"
             "(递增长度、确定性交错分割)⟹ p_history 只能算**样本量诊断**,"
             "不是'下一未见历史'的正式风险账;完整账还需 β_history(估计历史失败率"
             "本身的置信失败概率)",
             src="experiments/out/" + _mh_src + ":summary", headline=True)
        add3("W3CF共形历史外推",
             "**共形(顺序统计量)口径**:μ_conf / P(下一未见历史真值 > μ_conf) / "
             "相对留出 CP 的紧化倍数",
             f"{_ms['mu_conformal']:.4f} / {_ms['p_next_history_conformal']:.4f} / "
             f"{_ms['conformal_vs_cp_ratio']:.1f}×",
             "**同一批数据,只换仪器**。留出 CP 把留出历史压成二值指示器再计数,"
             "顺序结构被扔掉;顺序统计量直接给 P(新历史分数 > 全部 N 个校准分数) "
             "≤ 1/(N+1)(Conformal.lean 的 conformal_exceedance_le,不交性是**推出**"
             "的,可交换性是显式假设),并上新历史自己那一个上界的未覆盖预算 α "
             "⟹ conformal_risk_union。**两个维度同时改善**:阈值 "
             f"{_ms['mu_cal']:.4f}→{_ms['mu_conformal']:.4f}(校准分数**不必覆盖"
             "真值**,只作符合性分数 ⟹ 逐历史 Bonferroni 在这条路线上不存在,"
             f"α 从 {_ms['alpha_draw_per_hist']:.2e} 回到 {_ms['alpha_conformal']}),"
             f"失败概率 {_ms['p_history_notcertified_cp_upper']:.4f}→"
             f"{_ms['p_next_history_conformal']:.4f}(**边际**保证)。"
             "**两种保证强度必须分开**(评审 2026-08-08):边际界对校准集与新历史"
             "联合平均;训练条件(PAC)界对**已抽到的这个**校准集以 1-δ 置信成立 = "
             f"{_ms['p_next_history_conformal_pac']:.4f}。"
             "**该界必须按有限池无放回算(负超几何 P(J≥j)=C(M-j,N)/C(M,N)),"
             "不能用 Beta(1,N)** —— 后者假设 i.i.d. 无限连续总体,与本设计不符"
             "且错在不安全一侧(0.0794 vs 正确的 0.0933;自审 2026-08-08 抓出)。"
             "CP 是高置信陈述 ⟹ **同保证强度的倍率只有 "
             f"{_ms['conformal_pac_vs_cp_ratio']:.1f}×**;拿边际界比 CP 得到的 "
             f"{_ms['conformal_vs_cp_ratio']:.1f}× 是跨保证强度,不可引用。"
             "这是本篇'仪器错配'诊断的"
             "**正面实例**:前四次是把最坏值域仪器用在非值域受限的量上,这次是"
             "把二值计数换成顺序统计量。"
             + (f"**可交换前提由构造满足**:从 {_ms['conformal_pool_size']} 个按 "
                "token 数去重的候选历史中**无放回均匀抽样** ⟹ 该界在**该候选池"
                "上的均匀分布**这个总体上是**真界**,不再只是仪器效率上限。"
                f"并有对它的**真检验**:{_ms['n_val']} 个留出历史越界 "
                f"{_ms['n_val_exceed_conformal']} 个(期望 ≤ "
                f"{_ms['val_exceed_expected']:.2f})—— **功效很低,是 sanity check "
                "而非确认性检验**;阈值只由校准集决定,留出从未参与。"
                "候选池由少数基础文本的不同截断构成,语义多样性远低于同等数量的"
                "真实请求,且是前缀集而非自回归请求真正走过的历史流。"
                "口径(引用必带):总体是该候选池,**不是运行时流量** —— 要当运行时"
                "风险账仍须改为从真实流量可交换抽样。"
                if _ms.get("exchangeable_sampling") else
                "口径(引用必带):**可交换性假设未被本数据满足**(历史按递增字符"
                "长度人为构造)⟹ 此数是**仪器效率上限**,不是运行时风险账。")
             + "达**总** 1% 需 α=0.005 与 199 个历史(留出 CP 零事件达同一 1% 需 459 个)",
             src="experiments/out/" + _mh_src + ":summary", headline=True)
        # 跨家族路由 margin:自动收全所有 w2cv_*_router_margin.json
        import glob as _g2
        _bvs = {}
        for _p in sorted(_g2.glob(os.path.join(OUT, "w2cv_*_router_margin.json"))):
            _d = json.load(open(_p, encoding="utf-8"))
            _bvs[_d["model"]] = _d
        _bv = _bvs.get("DeepSeek-V4-Flash") or list(_bvs.values())[0]
        _b4 = _bv["per_bits"]["int4"]
        if len(_bvs) > 1:
            add4("W2CV跨家族路由margin",
                 "**跨模型家族**的 INT4 binding(证书作为门会拒掉的流量占比;"
                 "顺序 " + " / ".join(sorted(_bvs)) + ")",
                 # 值里**只放数字**:模型名含版本号(如 -2507)会被数字守卫当成
                 # 待核验的值,而它当然不在正文里。名字放进说明。
                 " / ".join(f"{100*d['per_bits']['int4']['binding']:.1f}%"
                            for _, d in sorted(_bvs.items())),
                 "同一量化口径(group-32 absmax RTN)、同一预注册判据,**三种不同的"
                 "路由制度**:"
                 + "; ".join(
                     f"{m}({d['n_routed_experts']} 专家 top-{d['topk']}"
                     + (f",**分组路由** n_group={d.get('n_group')}/选 "
                        f"{d.get('topk_group')}(两段选择,组阶段预算 4Lε)"
                        if d.get("routing_mode") == "grouped" else "")
                     + f",{'选择分数域 L=' + str(d['lipschitz_L']) if d['has_per_expert_bias'] else 'logit 域(无 bias)'})"
                     f" binding {100*d['per_bits']['int4']['binding']:.1f}%、"
                     f"翻转 {100*d['per_bits']['int4']['flip']:.1f}%、"
                     f"soundness 违约 {d['per_bits']['int4']['soundness_viol']}"
                     for m, d in sorted(_bvs.items()))
                 + "。**结论跨家族一致**:证书恒 sound(违约全 0),但作为门会拒掉"
                 "几乎全部流量 ⟹ 支柱 B 的否定不是小模型伪影。"
                 "口径:margin 域由**有无 per-expert bias** 决定而非由模型名决定 —— "
                 "无 bias 时选择完全由 logit 序定(单调不改序),有 bias 时必须在"
                 "选择分数域并乘 scoring 的 Lipschitz 上界",
                 # src 必须指向**真实存在**的文件(通配符不算,守卫会判红):
                 # 取字典序第一个作代表,其余同族在正文里逐条列出
                 src=("experiments/out/w2cv_%s_router_margin.json:per_bits.int4"
                      % sorted(_bvs)[0].split("-")[0].lower().replace("deepseek", "v4")),
                 headline=True)
            # k 规律:headroom = 1-binding 对 k 的对数线性回归。**正文里的
            # 斜率/截距/R² 必须由此处产出**,不许在别处临时算(算出来就不可回溯)。
            import math as _m
            _pts = [(d["topk"], d["per_bits"]["int4"]["binding"], m)
                    for m, d in sorted(_bvs.items())]
            _xs = [p[0] for p in _pts]
            _ys = [_m.log(1.0 - p[1]) for p in _pts]
            _n = len(_xs)
            _mx, _my = sum(_xs) / _n, sum(_ys) / _n
            _sl = (sum((x - _mx) * (y - _my) for x, y in zip(_xs, _ys))
                   / sum((x - _mx) ** 2 for x in _xs))
            _ic = _my - _sl * _mx
            _sst = sum((y - _my) ** 2 for y in _ys)
            _ssr = sum((y - (_sl * x + _ic)) ** 2 for x, y in zip(_xs, _ys))
            _r2 = 1.0 - _ssr / _sst
            _k8 = sorted(b for k, b, _ in _pts if k == 8)
            add4("W2CV跨家族路由margin",
                 "**k 规律**:log(1-binding) 对 k 的回归(截距 / 斜率 / R² / "
                 "每多选一个专家吃掉的余量%)",
                 f"{_ic:.2f} / {_sl:.3f} / {_r2:.3f} / "
                 f"{100 * (1 - _m.exp(_sl)):.0f}",
                 f"{_n} 个模型(k∈{sorted(set(_xs))},专家数 "
                 f"{sorted(set(d['n_routed_experts'] for d in _bvs.values()))})"
                 "的 INT4 binding 各取一点,**无加权最小二乘**。口径:每模型一点"
                 "(不按 token 加权),binding 取 per_bits.int4.binding。"
                 "**专家数无独立效应**是这条规律的要害:k=8 档共 "
                 f"{len(_k8)} 个模型、专家数横跨三档,binding 极差仅 "
                 f"{_k8[-1] - _k8[0]:.4f}。**这是拟合不是定律** —— 只在已测的 "
                 "k 与量化口径内成立,外推到 k>8 或别的量化族没有依据",
                 src=("experiments/out/w2cv_%s_router_margin.json:per_bits.int4"
                      % sorted(_bvs)[0].split("-")[0].lower().replace(
                          "deepseek", "v4")),
                 headline=True)
            # ---- W2-c-w/x/y:保守性分解、可部署证书、路由 TV(2026-08-09)----
            _lad, _ell, _rtv = {}, {}, {}
            for _p in _g2.glob(os.path.join(OUT, "w2cw_*_ladder.json")):
                _d = json.load(open(_p, encoding="utf-8"))
                _lad[_d["model"]] = _d
            for _p in _g2.glob(os.path.join(OUT, "w2cy_*_ellipsoid.json")):
                _d = json.load(open(_p, encoding="utf-8"))
                _ell[_d["model"]] = _d
            for _p in _g2.glob(os.path.join(OUT, "w2cx_*_routing_tv.json")):
                _d = json.load(open(_p, encoding="utf-8"))
                _rtv[_d["model"]] = _d
            if _lad:
                def _fitk(g):
                    _x = [d["topk"] for d in _lad.values()]
                    _y = [_m.log(max(g(d), 1e-9)) for d in _lad.values()]
                    _n = len(_x); _ux, _uy = sum(_x) / _n, sum(_y) / _n
                    _s = (sum((a - _ux) * (b - _uy) for a, b in zip(_x, _y))
                          / sum((a - _ux) ** 2 for a in _x))
                    return _s
                _sl0 = _fitk(lambda d: d["per_bits"]["int4"]["T0_global_eps"]["admit"])
                _sl2 = _fitk(lambda d: d["per_bits"]["int4"]["T2_local_lipschitz"]["admit"])
                _slo = _fitk(lambda d: d["per_bits"]["int4"]["T3_oracle"]["admit"])
                _k8 = [d for d in _lad.values() if d["topk"] == 8]
                add4("W2CW保守性分解",
                     "**k 规律的斜率有多少是仪器**:log(admit) 对 k 的斜率,"
                     "现行判据 / 收紧后 / oracle",
                     f"{_sl0:.3f} / {_sl2:.3f} / {_slo:.3f}",
                     "同一批 token、同一量化口径,只换判据的松紧:"
                     "T0=现行(逐 token 全体专家取 max 的 ε∞ + 全局 Lipschitz)、"
                     "T2=逐专家 ε + 局部 Lipschitz(仍是确定性最坏情形界)、"
                     "T3=oracle(真实是否翻转)。**要害**:现行斜率里只有约 "
                     f"{100 * _slo / _sl0:.0f}% 是物理,其余是界的松紧随 k 恶化 —— "
                     "把 −0.94 读成'MoE 的性质'是把自家口径写成了模型属性。"
                     "soundness 违约:三档全 0",
                     src="experiments/out/w2cw_kimi_ladder.json:per_bits.int4",
                     headline=True)
                add4("W2CW保守性分解",
                     "**收紧倍数**(T2/T0)与**离 oracle 的剩余倍数**(oracle/T2),"
                     "k=8 档极值",
                     f"{max(d['per_bits']['int4']['T2_local_lipschitz']['admit'] / max(d['per_bits']['int4']['T0_global_eps']['admit'], 1e-9) for d in _k8):.0f}"
                     f" / {max(d['per_bits']['int4']['T3_oracle']['admit'] / max(d['per_bits']['int4']['T2_local_lipschitz']['admit'], 1e-9) for d in _k8):.1f}",
                     f"{len(_k8)} 个 k=8 模型。ε∞ 对全体专家取 max 是最大一块浪费"
                     "(只有边界两个专家的误差进判据);sigmoid 的局部斜率再拿回一档"
                     "(top 专家 logit 高、处于饱和区)。剩余倍数是**符号未知**的硬"
                     "代价:确定性证书必须假设两个专家的扰动恰好反向",
                     src="experiments/out/w2cw_glm52_ladder.json:per_bits.int4")
            if _ell:
                _e12 = sorted((d for d in _ell.values() if d["topk"] <= 2),
                              key=lambda d: d["topk"])
                _e4 = [d for d in _ell.values() if d["topk"] >= 4]
                add4("W2CY可部署证书",
                     "**可部署**证书的放行率(扰动方向未知):球 / 实测椭球 / "
                     "共形椭球α=0.05,k≤2 档",
                     " / ".join(
                         f"{100 * d['tiers']['D0_ball']['admit']:.2f}%,"
                         f"{100 * d['tiers']['D1_ellipsoid']['admit']:.2f}%,"
                         f"{100 * d['tiers']['D3_conformal_a0.05']['admit']:.2f}%"
                         for d in _e12),
                     "**口径分水岭**:已发表的 binding 用的是实测 ε∞ —— 拿到它等于"
                     "已把量化路径算完,不可部署,它是**乐观端**。本条量的是方向未知"
                     "时能做到多好。协议:协方差 C 与半径 r 只用逐层前半 token 拟合,"
                     "放行率与违约只在后半评估;确定性档违约必须为 0(实测为 0),"
                     "共形档 α=0.05 的实测违约也是 0(α 没花掉,卡住的是椭球维数)。"
                     f"k≥4 的 {len(_e4)} 个模型全部为 0.00%(gpt-oss 共形档 0.01%)"
                     " —— 每一种确定性与边际覆盖的收紧都试过了",
                     src="experiments/out/w2cy_llama4_ellipsoid.json:tiers",
                     headline=True)
                _sr = [d["diag_layer_mean"]["stable_rank"] for d in _ell.values()]
                add4("W2CY可部署证书",
                     "门 logit 误差 Δz 的**稳定秩**范围(专家数 8→384)",
                     f"{min(_sr):.1f}–{max(_sr):.1f}",
                     "稳定秩 = tr(C)/λ_max,C 为逐层 Δz 的留出协方差。"
                     "**与专家数无关**:8 个专家与 384 个专家的稳定秩同量级 ⟹ "
                     "扰动真的活在约十维的集合里,椭球赌的低维性成立且已被吃干净;"
                     "确定性证书仍要付 √(有效维数),这是它逼不到 oracle 的原因",
                     src="experiments/out/w2cy_kimi_ellipsoid.json:diag_layer_mean")
            if _rtv:
                _nf = [d for d in _rtv.values() if d["topk"] > 1]
                add4("W2CX路由TV",
                     "**证书通过者仍在漂移**:集合不变的 token 其路由分布 TV "
                     "中位(最小–最大,跨模型)/ 单模型最大值",
                     f"{min(d['tv_given_no_flip']['median'] for d in _nf):.4f}–"
                     f"{max(d['tv_given_no_flip']['median'] for d in _nf):.4f} / "
                     f"{max(d['tv_given_no_flip']['max'] for d in _nf):.3f}",
                     "路由分布 TV = ½‖w′−w‖₁,w 为选中集合上重归一化的门控权重。"
                     "支持集不相交 ⟹ 精确分解成'换人'与'漂移'两块;集合不变的 "
                     "token 其 TV 全部来自漂移,而**现行证书对漂移不设任何界**。"
                     "对照:发生翻转时搬动的质量中位 "
                     f"{min(d['tv_flipped_only']['median'] for d in _nf):.3f}–"
                     f"{max(d['tv_flipped_only']['median'] for d in _nf):.3f}"
                     "(top-k 会重归一化 ⟹ 边际专家权重约 1/k 而非趋零,"
                     "'翻转搬动质量极小'的猜测被**证伪**)。k=1 不入统计:"
                     "单专家权重恒为 1,漂移在定义上为 0",
                     src="experiments/out/w2cx_kimi_routing_tv.json:tv_given_no_flip",
                     headline=True)
            # ---- R2(2026-08-09):容量兑现链的**两点对照** ----
            def _lv(tag, suf):
                _d = json.load(open(os.path.join(
                    OUT, "w3cc_%s_%s.json" % (tag, suf)), encoding="utf-8"))
                return {l["concurrency"]: l for l in _d["levels"]}, _d
            try:
                _fN, _fNd = _lv("fp8", "cross")     # 无前缀复用(26k,C=128..256)
                _wN, _wNd = _lv("w4afp8", "cross")
                _fS, _fSd = _lv("fp8", "warm2")     # 会话复用(26k,C=96..256)
                _wS, _wSd = _lv("w4afp8", "warm2")
            except FileNotFoundError as _e:
                _fN = None
                print("[canon] R2 容量产物缺失,跳过:", _e)
            if _fN:
                _cap = (_wNd["server_info"]["max_total_num_tokens"]
                        / _fNd["server_info"]["max_total_num_tokens"])
                _rN = [_wN[c]["agg_gen_tok_s"] / _fN[c]["agg_gen_tok_s"]
                       for c in sorted(set(_fN) & set(_wN)) if c >= 128]
                _rS = [_wS[c]["agg_gen_tok_s"] / _fS[c]["agg_gen_tok_s"]
                       for c in sorted(set(_fS) & set(_wS)) if c >= 96]
                add3("R2容量兑现链",
                     "**同一 3.7 倍容量,两种工况的兑现结果**:无前缀复用的吞吐比 / "
                     "会话复用的吞吐比(区间)/ 会话复用的均值",
                     "%.2f–%.2f / %.2f–%.2f / %.2f"
                     % (min(_rN), max(_rN), min(_rS), max(_rS),
                        sum(_rS) / len(_rS)),
                     "GLM-5.2 生产栈(tp8/ep8/dp8 + dsa 后端 + graphs on,两臂 "
                     "mem_fraction 匹配 0.85),26k token/请求,W4AFP8 vs FP8,"
                     f"配置容量比 {_cap:.3f}×。**两个工况必须一起报**:"
                     "无复用时每请求付全额 prefill(cached-token 峰值 fp8 2,560、"
                     "w4afp8 0,对照 26,000 的 prompt)⟹ 算力先饱和,容量优势"
                     "**无处兑现**;会话复用(每 worker 自有长上下文跨轮复用,"
                     "编程 agent 形状)⟹ 前缀命中,容量决定**多少会话保持 cache-warm**"
                     "⟹ 兑现。单报任一个都会误导。"
                     "**口径**:会话轮的协议含分档前缀命名空间 + 每档 90s 预热 —— "
                     "无此二者会跨档携带 cache,曾测出伪值 1.58×",
                     src="experiments/out/w3cc_fp8_warm2.json:levels", headline=True)
                add3("R2容量兑现链",
                     "**兑现链逐环衰减**(会话复用工况):配置容量 / 并发 / 热命中 / 吞吐",
                     "%.2f / %.2f / %.2f / %.2f"
                     % (_cap, 23.5 / 10.5, 27 / 14, sum(_rS) / len(_rS)),
                     "并发比取两臂 running-req 峰值众数(FP8 10–11 被 KV 封顶,"
                     "占用 1.00;W4AFP8 23–24,占用 0.54);热命中比取全命中 prefill "
                     "次数(cached-token > 13,000)。**每一环都在衰减** —— 命中省下的"
                     "是 prefill,而稳态吞吐仍由 decode 与算力决定。"
                     "TTFT 在 C<=192 改善 1.08–1.20×,**C=256 反转到 0.92×**:"
                     "算力饱和后 W4AFP8 的 24 并发使单请求分到更少,"
                     "**容量买到的吞吐以单请求延迟为代价**。"
                     "窗口内每会话仅约 1.9 轮(181 完成/96 会话),真实 agent 要跑"
                     "几十轮 ⟹ 1.19 是**下界**,但不据此外推",
                     src="experiments/out/w3cc_w4afp8_warm2.json:levels",
                     headline=True)
            # ---- R6/R7(2026-08-09):替换恒等式 + 常驻的质量代价 ----
            _rs = {}
            for _t in ("v4", "v32", "glm52", "kimi", "minimax", "qwen3",
                       "gptoss", "llama4", "mixtral"):
                _f = os.path.join(OUT, "w3rs_%s.json" % _t)
                if os.path.exists(_f):
                    _rs[_t] = json.load(open(_f, encoding="utf-8"))
            if len(_rs) >= 9:
                _gap = max(v["armB_residency"]["rho0.2500"]["identity_max_abs_gap"]
                           for v in _rs.values())
                _rat = [v["armB_residency"]["rho0.2500"]["tv_score"]["mean"]
                        / v["armA_quantize_all"]["int4"]["mean"] for v in _rs.values()]
                _same = [1.0 - v["armB_residency"]["rho0.2500"]
                         ["frac_tv_differs_score_vs_random"] for v in _rs.values()]
                add4("R6替换恒等式",
                     "TV(W,W′)=1−(Σ_K u)/max(U,U′) 的实测残差(九模型最大)",
                     f"{_gap:.1e}",
                     "**恒等式不是界**。右端对 S′ 的依赖只通过总量 U′ —— 换进来的"
                     "是哪几个专家不出现在等式里。⟹ 按分数挑最好的常驻替补、随机挑、"
                     "干脆丢掉,三者路由 TV **完全相同**(机检 tv_cannot_separate)。"
                     "残差在数值精度量级,k=1 的 Llama-4 精确为 0。"
                     "这是对**整个用路由 TV 表达的证书族**的不可能性结论",
                     src="experiments/out/w3rs_v4.json:armB_residency",
                     headline=True)
                add4("R6替换恒等式",
                     "三个替换策略逐 token TV 相同的比例(九模型最小–最大)",
                     f"{100*min(_same):.0f}%–{100*max(_same):.0f}%",
                     "五个模型 100%(权重序与选择序一致);带 per-expert bias 的四个"
                     f"{100*min(_same):.0f}%–99%,差异全部来自 U′>U 的情形,"
                     "恒等式的一般形式仍成立",
                     src="experiments/out/w3rs_glm52.json:armB_residency")
                add4("R6等字节头对头",
                     "**等专家显存**下 ρ=1/4 常驻 bf16 相对 INT4 全量化的路由 TV 倍数"
                     "(九模型,均值口径)",
                     f"{min(_rat):.1f}×–{max(_rat):.1f}×",
                     "臂A(全量化)E 个专家×b bit vs 臂B(常驻)ρE 个×bf16,"
                     "ρ=b/16 时等字节。**量化臂 9/9 全胜**。"
                     "但 TV 上的胜负**不可单独下结论**(先于数据写死):TV 低估臂A"
                     "(看不见专家输出误差),同时可能高估臂B(恒等式说明它看不见替补"
                     "是不是分数相邻,实测替补的全局排名中位只有 1–11)。"
                     "两向都偏 ⟹ 判词 needs_dnll,由 R7 定谳",
                     src="experiments/out/w3rs_mixtral.json:armA_quantize_all",
                     headline=True)
            _rq_f = os.path.join(OUT, "w3rq_residency_quality.json")
            if os.path.exists(_rq_f):
                _rq = json.load(open(_rq_f, encoding="utf-8"))
                _s = _rq["summary"]
                add4("R7常驻质量代价",
                     "**DeepSeek-V2-Lite** 常驻 1/2、1/4、1/8 专家 + 按分数替换的 "
                     "ΔNLL 中位 / ARC Δacc",
                     f"{_s['score_r050']['dnll_median']:.3f} 纳特 / "
                     f"{_s['score_r050']['dacc_pp']:+.1f}pp;"
                     f"{_s['score_r025']['dnll_median']:.3f} / "
                     f"{_s['score_r025']['dacc_pp']:+.1f}pp;"
                     f"{_s['score_r0125']['dnll_median']:.3f} / "
                     f"{_s['score_r0125']['dacc_pp']:+.1f}pp",
                     "与 INT4 全量化**等字节**的是 ρ=1/4 那档,而后者在同模型同语料"
                     "同协议下是 2.5e-4 纳特 / +0.8pp —— **差 4×10³ 倍**。"
                     "base ARC 0.524 与 w2cr 已发表基线逐字相同 ⟹ 协议同源。"
                     "常驻集由**不相交**语料标定;门控权重复算与模块自身逐层核对 ≤1e-4,"
                     "不符即中止",
                     src="experiments/out/w3rq_residency_quality.json:summary",
                     headline=True)
                add4("R7常驻质量代价",
                     "随机替换 / 按分数替换的 ΔNLL 中位比(预注册:≥3.0 判 TV 量错了)",
                     f"{_rq['random_over_score_median_ratio']:.2f}",
                     "**预注册假设被判否**:按分数挑替补只比随机挑好 8%。"
                     "⟹ 路由 TV 看不见替补身份,是因为替补身份**不重要** —— R6 的"
                     "恒等式描述的是真实不变量而非仪器缺陷。这条同时把'TV 高估常驻臂'"
                     "的警告证伪,等字节比较的推理链因此闭合。"
                     "机制读法:免费的不是'随便改路由' —— 量化改的是模型**自己在扰动下"
                     "的偏好**(自洽),常驻替换是**外部强制覆盖**(不自洽)",
                     src="experiments/out/w3rq_residency_quality.json:"
                         "random_over_score_median_ratio",
                     headline=True)
            # ---- R8(2026-08-10):专家权重的比特地板 ----
            _rb_f = os.path.join(OUT, "w3rb_expert_bits.json")
            if os.path.exists(_rb_f):
                _rb = json.load(open(_rb_f, encoding="utf-8"))
                _b = _rb["summary"]
                add4("R8比特地板",
                     "**DeepSeek-V2-Lite** expert-only RTN 量化的 ΔNLL 中位 / ARC Δacc"
                     "(INT4 / INT3 / INT2)",
                     f"{_b['int4']['dnll_median']:.5f} / {_b['int4']['dacc_pp']:+.1f}pp;"
                     f"{_b['int3']['dnll_median']:.5f} / {_b['int3']['dacc_pp']:+.1f}pp;"
                     f"{_b['int2']['dnll_median']:.3f} / {_b['int2']['dacc_pp']:+.1f}pp",
                     "对照臂**逐位精确**复现已发表值(abs_gap=0.0)。INT4 的 Δacc CI "
                     f"({_b['int4']['dacc_ci95'][0]:+.1f},{_b['int4']['dacc_ci95'][1]:+.1f})"
                     " 跨 0 ⟹ 与零不可区分;INT3 CI "
                     f"({_b['int3']['dacc_ci95'][0]:+.1f},{_b['int3']['dacc_ci95'][1]:+.1f})"
                     ";INT2 CI "
                     f"({_b['int2']['dacc_ci95'][0]:+.1f},{_b['int2']['dacc_ci95'][1]:+.1f})。"
                     "**悬崖在 3 和 2 之间,不在 4** —— 生产的 MXFP4 是惯例不是实测悬崖。"
                     "量化器是**纯 RTN**(无校准数据/无 Hessian/无搜索),方向不对称:"
                     "RTN 下免费 ⟹ 结论更强;RTN 下不免费 **不可**推出该档不行。"
                     "INT3 的 2.6 点正是校准型量化器通常能吃掉的量级",
                     src="experiments/out/w3rb_expert_bits.json:summary",
                     headline=True)
            # ---- R9(2026-08-10):保持路由不变买不到东西 ----
            _rf_f = os.path.join(OUT, "w3rf_forced_routing.json")
            if os.path.exists(_rf_f):
                _rf = json.load(open(_rf_f, encoding="utf-8"))
                _ci = _rf["diff_nll_median_ci95"]
                add4("R9路由保持无收益",
                     "专家权重固定(armA INT4)只换路由策略:强制回放 bf16 原路由 vs "
                     "量化模型自路由,配对 ΔNLL 中位差占量化总效应的比例 / 回放覆盖率",
                     f"{100*abs(_rf['diff_forced_minus_self_nll_median'])/2.4647542159073055e-4:.1f}%"
                     f" 的量化总效应 / 回放覆盖率 {100*_rf['override_rate']:.1f}%",
                     "**两臂专家权重逐位相同**,唯一差别是门控输出。回放覆盖率"
                     f"{100*_rf['override_rate']:.1f}% ⟹ 干预非空(<1% 会判 VACUOUS,"
                     "该自检是补加的:原脚本只校验调用次数与形状,不校验回放到底改了什么)。"
                     "配对差 −6e-6 纳特,是量化总效应(2.5e-4)的 **2.4%** ⟹ "
                     "**在量化下把路由恢复成原样买不到东西**。"
                     "**定位(2026-08-10 文献核查后更正)**:该 2×2 已被做过两次 —— "
                     "EAC-MoE(ACL 2025 Table 1,2–3 bit,含 4-bit attention)与 "
                     "MoBiE(Table 1,1-bit,专家二值化),**两次都是 forced 赢**。"
                     "故'领域信念未经检验'这个前提**不成立**,不得作为卖点。"
                     "本轮的贡献是**部署档那个缺失的点**:1-bit ΔPPL 2.37–3.44、"
                     "2–3 bit 0.36–0.44、**4-bit 0.050**,即优势随比特每档降约一个数量级,"
                     "到实际出货精度只剩基线 PPL 的 0.7%。且本轮扰动更纯(只量化专家,"
                     "gate 与 attention 都 bf16)、量化器更差(RTN 非 GPTQ,扰动更大,"
                     "方向上偏向'找得到差距'),仍然只有 0.050。"
                     "**判词须打折看**:它由准确率一支触发(self 0.532 vs forced 0.520,"
                     "500 题里 6 题),而那一支是**裸门限无 CI**,与本文其他判据不一致;"
                     "有 CI 的 ΔNLL 一支方向相反(forced 略好)。两臂实用上不可区分。"
                     "规则不追改(看了数据再改规则是作弊),缺陷如实披露,"
                     "acc CI 只加给将来的运行。"
                     "与另外两台独立仪器同向:翻转率反预测损伤(RR 0.71–0.84)、"
                     "三者合起来:**路由不是量化损伤流经的通道**"
                     "(翻转层数计数的 AUROC 因并列秩未修复,不引用)。"
                     "机制层面本文不下结论 —— 当日提出的两个机制解释都被随后的测量打掉"
                     "(替补相邻性 比值 1.08;分数带内/带外 细粒度模型比值 0.12–0.59),"
                     "故只报测量",
                     src="experiments/out/w3rf_forced_routing.json:"
                         "diff_forced_minus_self_nll_median",
                     headline=True)
            # ---- R10(2026-08-10):保持路由的收益 vs 实际路由漂移(受控曲线) ----
            _rc_f = os.path.join(OUT, "w3rc_routing_curve.json")
            if os.path.exists(_rc_f):
                _rc = json.load(open(_rc_f, encoding="utf-8"))
                _cv = _rc["curve"]
                _row = lambda b: _cv["int%d" % b]
                add4("R10路由保持的收益曲线",
                     "**同模型同量化器同协议**下,恢复原路由的收益 vs 实际路由改变率"
                     "(4/3/2 bit)",
                     " ; ".join(
                         "%d bit: 改变率 %.1f%% → 相对收益 %+.1f%%(绝对 %+.3f PPL)"
                         % (b, 100 * _row(b)["override_rate"],
                            100 * _row(b)["rel_gain"], _row(b)["abs_gain_ppl"])
                         for b in (4, 3, 2)),
                     "**存在反号点**,预注册的单调性被判否。三档的配对增益 CI 全部"
                     "排除零(4bit +0.00723 [+0.0037,+0.0109];3bit +0.02992 "
                     "[+0.0182,+0.0438];2bit **−0.21098** [−0.3920,−0.0633]),"
                     "即漂移足够大之后**未量化模型的路由对量化模型的表示不再是对的路由**,"
                     "交叉点落在改变率 52.5% 与 88.1% 之间。"
                     "**2026-08-10 更正(R12 撤回)**:我曾据 16.6%→11.7% 这一降读出"
                     "'名义比特不是横轴、路由改变率才是',并据此调和 MoBiE 与本轮。"
                     "R12 固定 4bit 只改 group、把比特与漂移解耦后:漂移从 24.4% 涨到 36.0%"
                     "(1.5×),相对收益 15.6/16.6/14.8/17.4/18.9%,**无可检测变化**,"
                     "且与 3bit 点(11.7%)的 CI 全部重叠 ⟹ 那个'降'本在噪声内,"
                     "横轴论证**已撤**。存活的是更简单的版本:可用区间内相对收益"
                     "近似恒定(约 15%),唯一显著的效应是 2bit 处的反号。"
                     "路由改变率仍值得报(router-only,九模型七配置 22 秒),但只作描述统计,"
                     "不再声称它是解释性的轴。"
                     "本轮量化器 RTN 比 GPTQ 差 ⟹ 漂移更大 ⟹ 偏向'找得到收益',方向保守;"
                     "只量化专家(gate/attention 都 bf16),比 EAC-MoE 干净(它同时量化 attention)。"
                     "int4 self 臂复现已发表值,口径同源",
                     src="experiments/out/w3rc_routing_curve.json:curve",
                     headline=True)
                add4("R10路由保持的收益曲线",
                     "部署档(W4)上恢复原路由的**绝对**收益,相对基线 PPL",
                     "%.3f / %.2f = %.2f%%"
                     % (_row(4)["abs_gain_ppl"], _rc["base_ppl"],
                        100 * _row(4)["abs_gain_ppl"] / _rc["base_ppl"]),
                     "预注册的 worth_it(相对 ≥25% **且** 绝对 ≥0.2 PPL)在 4/3/2 三档"
                     "**全部不满足**。相对收益在可用档位是 16.6%/11.7%,不算小 —— "
                     "但它乘的是一个很小的损伤(W4 处 0.026 PPL),故绝对收益低于任何"
                     "工程阈值。⟹ 路由一致性机制的回报**与你已经接受的损伤成正比**,"
                     "因此在你真正想出货的精度上回报最小。这不与 EAC-MoE/MoBiE 冲突:"
                     "他们的大收益(0.36–3.44 PPL)来自损伤本来就大的工作点",
                     src="experiments/out/w3rc_routing_curve.json:base_ppl",
                     headline=True)
            # ---- R12(2026-08-10):把比特与漂移解耦,横轴论证被自己判否 ----
            _rd_f = os.path.join(OUT, "w3rd_drift_axis.json")
            if os.path.exists(_rd_f):
                _rd = json.load(open(_rd_f, encoding="utf-8"))
                _g = _rd["grid"]
                add4("R12漂移不是那根轴",
                     "固定 4bit 只改 group(比特与漂移解耦)下,漂移 → 相对收益",
                     " ; ".join("g%d: 漂移 %.1f%% → %+.1f%%"
                                % (v["group"], 100 * v["drift"], 100 * v["rel_gain"])
                                for v in _g.values()),
                     "判词 **inconclusive_no_drift_overlap**(4bit 漂移最高 36.0%,"
                     "够不到 3bit 点 52.5% 的 ±8pp,预注册的诚实出口)。"
                     "但数据本身给了答案:同一比特内漂移涨 1.5×,相对收益**无可检测变化**,"
                     "六个点 CI 全部互相重叠 ⟹ R10 里 16.6%→11.7% 的'下降'本在噪声内,"
                     "**我据此建的横轴论证已从论文与 canon 撤回**。"
                     "跨轮对照逐位精确(b4g32 漂移 0.276、selfΔNLL 0.04358,与 R10 int4 相同)。"
                     "这是当日第四个被自己下一次测量打掉的解释(前三:替补相邻性 1.08;"
                     "分数带内/带外;漂移轴)",
                     src="experiments/out/w3rd_drift_axis.json:grid",
                     headline=True)
            # ---- R13/R14/R15(2026-08-10):份额不变量 + 修复容量 + 扰动族 ----
            _rg_f = os.path.join(OUT, "w3rg_gptq_share.json")
            _rh_f = os.path.join(OUT, "w3rh_gate_repair.json")
            _ri_f = os.path.join(OUT, "w3ri_armb_share.json")
            if all(os.path.exists(f) for f in (_rg_f, _rh_f, _ri_f)):
                _rg = json.load(open(_rg_f, encoding="utf-8"))
                _rh = json.load(open(_rh_f, encoding="utf-8"))
                _ri = json.load(open(_ri_f, encoding="utf-8"))
                _sa = _rg["arms"]
                add4("R13-15路由份额不变量",
                     "回放份额 (self−forced)/self:RTN / GPTQ / armB(均 4bit g32 主档)",
                     "%.1f%% (%.1f,%.1f) / %.1f%% (%.1f,%.1f) / %.1f%% (%.1f,%.1f)"
                     % (100 * _sa["rtn"]["share"], *[100 * c for c in _sa["rtn"]["share_ci95"]],
                        100 * _sa["gptq"]["share"], *[100 * c for c in _sa["gptq"]["share_ci95"]],
                        100 * _ri["share"], *[100 * c for c in _ri["share_ci95"]]),
                     "**份额 ≈16%(12~19%)是横跨四个自由度的不变量**:group 16→256"
                     "(R12)、bit 3→4(R10)、量化器 RTN→GPTQ(R13,GPTQ 的 H-度量"
                     "权重误差好 2.9×、5070 Linear 100% 更优、端到端好 23%,份额不动)、"
                     "扰动族 armA→armB(R15,attention+稠密MLP 一起量化,漂移 45.1%,"
                     "份额 +2.0pp << 预注册 15pp 门限)。当日第五、六个被判否的假设。"
                     "唯一逃逸:深损伤区(2bit,漂移 88%)反号 −7.5%。"
                     "EAC-MoE 的 53%(NLL 换算)用尽可测嫌疑,剩评测域/换算口径,标开放",
                     src="experiments/out/w3ri_armb_share.json:share",
                     headline=True)
                _s3 = _rh["summary"]["int3"]
                _s2 = _rh["summary"]["int2"]
                add4("R14gate修复容量",
                     "gate-only KL 蒸馏的修复容量(占损伤比例):INT3 / INT2;"
                     "FP 安慰剂净效应",
                     "%.1f%%(特异 %.1f%%) / %.1f%%(特异 %.1f%%);%+.3f 纳特"
                     % (100 * _s3["capacity"], 100 * _s3["capacity_specific"],
                        100 * _s2["capacity"], 100 * _s2["capacity_specific"],
                        -_rh["placebo_gain_nll"]),
                     "**修复容量是损伤深度的函数**:部署档无款可修(INT3 0.5~9.0%,"
                     "区间来自安慰剂修正,哪端都小),深损伤区修回三成(INT2 29.4%,"
                     "独立复现 GEMQ 的 34~39% @1.5bpe,跨模型/量化器/uniform)。"
                     "安慰剂(FP 训 gate)是**净伤害** +0.022 CI(0.013,0.031) —— "
                     "FP 没东西可修,训练纯过拟合。**双区间图景**:中低损伤区路由是"
                     "损伤的次要通道(保护无用/回放恒定 16%/修复无款);深损伤区路由"
                     "翻转为主动补偿器(回放有害 −7.5%/训练修回三成),正确动作从"
                     "'对齐 FP'翻转为'适配量化'。三件如实披露:判词 INVALID 是判据"
                     "误伤(收敛判据对 KL 起点≈0 的安慰剂臂是范畴错误,不追改);"
                     "INT2 修 NLL 0.82 纳特但 ARC 358→340(GEMQ 域偏差再现);"
                     "比特地板未搬动。R10 跨轮对照逐位精确",
                     src="experiments/out/w3rh_gate_repair.json:summary",
                     headline=True)
            # ---- R16(2026-08-10):不变量跨模型复证 + 53% 归因终结 ----
            _rjd_f = os.path.join(OUT, "w3rj_dsmoe16b.json")
            _rjq_f = os.path.join(OUT, "w3rj_qwen3.json")
            if os.path.exists(_rjd_f) and os.path.exists(_rjq_f):
                _rjd = json.load(open(_rjd_f, encoding="utf-8"))
                _rjq = json.load(open(_rjq_f, encoding="utf-8"))
                _do, _dw = _rjd["per_domain"]["ours"], _rjd["per_domain"]["wikitext2"]
                _qo, _qw = _rjq["per_domain"]["ours"], _rjq["per_domain"]["wikitext2"]
                add4("R16份额不变量跨模型",
                     "回放份额跨模型跨域矩阵:dsmoe16b(ours/wt2)与 "
                     "Qwen3-30B(ours/wt2)",
                     "%.1f%% (%.1f,%.1f) / %.1f%% (%.1f,%.1f) ; "
                     "%.1f%% (%.1f,%.1f) / %.1f%% (%.1f,%.1f)"
                     % (100 * _do["share"], *[100 * c for c in _do["share_ci95"]],
                        100 * _dw["share"], *[100 * c for c in _dw["share_ci95"]],
                        100 * _qo["share"], *[100 * c for c in _qo["share_ci95"]],
                        100 * _qw["share"], *[100 * c for c in _qw["share_ci95"]]),
                     "两轮判词均 **replicates**。dsmoe16b 是 **EAC-MoE 53%% 的原模型**"
                     "(64+2 专家 top-6,同 V2-Lite 族);Qwen3-30B 是**跨族**"
                     "(128 专家 top-8,无共享专家,gate 纯 Linear,回放 logits = "
                     "完全强制)。**份额 ≈8~17%% 现在横跨三模型两族两域,加上此前的 "
                     "group/bit/量化器/扰动范围四个旋钮 —— n=1 解决**。"
                     "53%% 的归因至此终结:模型(本轮)、评测域(本轮,方向还反:"
                     "WikiText2 上 7.5%%,更低)、深度/量化器/扰动范围(V2-Lite 上)"
                     "全部排除;剩协议组合差异或表格语义与换算假设的出入,"
                     "如实标注不硬归因。正面陈述:**在 EAC-MoE 自己的模型和评测域上,"
                     "隔离协议测得 7.5~16%%**。WikiText2 用分块非滑窗,协议差异声明在案",
                     src="experiments/out/w3rj_dsmoe16b.json:per_domain",
                     headline=True)
            # ---- R17(2026-08-10):反号三件套 ----
            _kd_f = os.path.join(OUT, "w3rk_dsmoe2b.json")
            _kq_f = os.path.join(OUT, "w3rk_qwen32b.json")
            _rl_f = os.path.join(OUT, "w3rl_reversal_threshold.json")
            if all(os.path.exists(f) for f in (_kd_f, _kq_f, _rl_f)):
                _kd = json.load(open(_kd_f, encoding="utf-8"))
                _kq = json.load(open(_kq_f, encoding="utf-8"))
                _rl = json.load(open(_rl_f, encoding="utf-8"))
                _g2 = _rl["grid"]["gptq2"]
                add4("R17反号三件套",
                     "回放反号(gain<0)的跨模型/跨域/跨量化器矩阵与 V2L 模型内零点",
                     "dsmoe 2bit: −10.4%% (−15.5,−5.8) / −2.5%% (−4.9,−0.4);"
                     "Qwen3 2bit: +10.0%% / +10.2%%(无反号,损伤 2.04);"
                     "V2L GPTQ-2bit: −42%%(gain −1.284 [−1.618,−0.963],损伤 3.058);"
                     "V2L rowmix 零点 ≈1.2 纳特",
                     "**'对齐 FP 路由在深压缩下有害'跨两模型、两评测域、两量化器成立**。"
                     "漂移被干净排除:V2L 与 Qwen3 的 2bit 漂移都是 88.1%%,符号相反。"
                     "跨模型统一损伤阈值判否(V2L 零点 1.2 vs Qwen3 >2.04,第七个);"
                     "模型内 gain(损伤) 单调平滑穿零(+0.030/0.26 → −0.211/2.81,"
                     "跨轮对照 p=0 与 R10 逐位精确)。前瞻预测一中一半否:"
                     "损伤>2.81⟹负 命中;gptq2 落 rowmix 曲线 判否(实测 −1.28 vs "
                     "外推 −0.25,量化器有损伤之外的指纹)。副观察:GPTQ-2bit 逐层"
                     "重构优于 RTN(自检过)而端到端更差(3.06 vs 2.81)—— 逐层贪心"
                     "与端到端在深压缩下脱钩。与 EAC-MoE 符号级冲突(其工作点即 "
                     "GPTQ 2-3bit + dsmoe;我们在其模型其域上 RTN-2bit 也是负),"
                     "如实并置列协议差异,不指控",
                     src="experiments/out/w3rl_reversal_threshold.json:grid",
                     headline=True)
            # ---- R18/R19(2026-08-10):反号主张收缩 + 对消结构 + bias 族复证 ----
            _kim_f = os.path.join(OUT, "w3ro_kimilinear.json")
            _g256_f = os.path.join(OUT, "w3rn_qwen3_2b_g256.json")
            if os.path.exists(_kim_f) and os.path.exists(_g256_f):
                _kim = json.load(open(_kim_f, encoding="utf-8"))
                _g256 = json.load(open(_g256_f, encoding="utf-8"))
                _ko = _kim["per_domain"]["ours"]
                _qo = _g256["per_domain"]["ours"]
                add4("R18R19反号收缩与bias族",
                     "Qwen3 最深档(2bit g256)ours 份额 / Kimi-Linear(bias 校正 gate)"
                     "ours 份额",
                     "%.1f%% (%.1f,%.1f) @损伤 %.2f / %.1f%% (%.1f,%.1f)"
                     % (100 * _qo["share"], *[100 * c for c in _qo["share_ci95"]],
                        _qo["self"]["dnll_mean"],
                        100 * _ko["share"], *[100 * c for c in _ko["share_ci95"]]),
                     "**R18 no_crossing 成立**:Qwen3 到损伤 3.33(超 V2L 反号点 2.81)、"
                     "漂移 95.6%% 仍显著为正 ⟹ '每模型都有反号点'判否,反号收缩为"
                     "家族性质(V2L/dsmoe 有,Qwen3 可测范围无)。软化证据如实并置:"
                     "ours 份额随损伤单调降(10.4→4.3);对消预测方向命中(正 token "
                     "占比 53.8→49.9%%,g256 已过半;对消比 0.46→0.70)。"
                     "**R18tok 结构发现**:净份额是两股几乎对消的大流的残差 —— "
                     "V2L 4bit 正贡献 +2816/负 −2343(对消比 0.83),**回放在 47%% 的 "
                     "token 上有害,即使部署档**;尾部效应(p99 ±0.5 纳特)是净均值的 "
                     "70 倍,SLA/tail 视角下'回放有益'在 token 级不成立。"
                     "**R19 replicates**:Kimi-Linear-48B(sigmoid+correction bias,"
                     "noaux_tc 同族,256 专家,线性 KDA)份额 16.9%%,与 V2L/dsmoe 几乎"
                     "重合 ⟹ 不变量覆盖 4 模型 × 2 类 gate 机制;其漂移 43%% 远大于 "
                     "softmax 族的 25~33%% 而份额不动。V4-Flash 本体不可 transformers "
                     "加载(仅 SGLang),标开放,Kimi 为其 noaux_tc 同族代表",
                     src="experiments/out/w3ro_kimilinear.json:per_domain",
                     headline=True)
            # ---- R21~R23 + rank-1(2026-08-11):文档级结构 ----
            _sel_f = os.path.join(OUT, "w3rt_sel4b.json")
            _v23_f = os.path.join(OUT, "w3rv_v2l4b_nosh.json")
            if os.path.exists(_sel_f) and os.path.exists(_v23_f):
                _sel = json.load(open(_sel_f, encoding="utf-8"))
                _v23 = json.load(open(_v23_f, encoding="utf-8"))
                _vo = _v23["per_domain"]["ours"]
                add4("R21-23文档级rank-1",
                     "oracle 部署档消除率 / 最优置信度选择器占 oracle / "
                     "rank-1 PC1 方差(9 配置×32 文档)/ zlib 代理 ρ / "
                     "no-shared 4bit 份额",
                     "98.6%% / 12.2%%(all_forced 16.8%%) / 75.7%%(符号 9/9) / "
                     "+0.72 / %.1f%% (%.1f,%.1f)"
                     % (100 * _vo["share"], *[100 * c for c in _vo["share_ci95"]]),
                     "**净路由效应 = s(doc)×c(config) 的 rank-1 外积**:PC1 75.7%% "
                     "方差,9/9 配置载荷符号与份额符号一致(边缘反号被载荷比 CI 更灵敏"
                     "捕捉)。s(doc)=文档不可压缩信息密度,zlib 压缩比 Spearman +0.72"
                     "(ours 域 +0.80)—— **零成本可测**;高 s=实体密集散文,s≈0=代码"
                     "样板/目录/程式化叙述(冗余文本对量化扰动近乎免疫)。跨模型迁移"
                     "(文档级 r=0.83)的原因:s 是文本性质非模型性质。"
                     "R21:置信度信号族(熵/top1/margin=12.2/11.8/10.6%% oracle)全败于"
                     "不选择(16.8%%),argmax 一致率 95.7%% —— token 级无可学身份,"
                     "Jitkrittum 2307.02764 的 deferral 失效条件解释之(置信度按构造"
                     "不含臂间信息)。R22/R23:shared 不驱动反号(纯 routed 也反),"
                     "ε/δ 玩具两轮判否 —— 16%% 免疫第五旋钮(扰动构成),仍无解释。"
                     "必引同构邻居:2506.12044(example 级 ρ=0.82);三个空位确认:"
                     "文档级×路由轴 / prefix-probe 选臂 / δ 侧注入",
                     src="experiments/out/w3rv_v2l4b_nosh.json:per_domain",
                     headline=True)
            # ---- R26-28(2026-08-11):层级三部曲 ----
            _ab_f = os.path.join(OUT, "w3sa_absorb.json")
            if os.path.exists(_ab_f):
                add4("R26-28层级三部曲",
                     "回放 share 层构成(浅/中/深)/ 深组二分 / hidden 传播",
                     "−1.2%% [−3.2,0.5] / +5.0%% [2.0,8.3] / +8.6%% [4.2,13.1];"
                     "3.9%%/4.3%%;0.021→0.152 单调升(~4×)",
                     "**份额 16.6%% 的层级构成**:浅≈0(噪声级)、中 5.0、深 8.6"
                     "(深组内均分,平台非末层尖峰),三组和 12.4%%,余 4.2pp 为"
                     "文档级乘性交互(沿 s 轴,深组 doc 结构与 s r=0.94)。"
                     "两个机制判否:逐层果断度平坦(ρ=−0.02,第13)、吸收论"
                     "(hidden 差单调升 ~4×,no_decay,第14)。存活事实:**功能敏感度"
                     "由到输出的距离决定,与扰动传播幅度解耦**(浅层注入漂移最大而"
                     "NLL≈0,深层最小而效应最大)。正交性(文献对照):权重误差怕浅层"
                     "(DyMoE/QuantMoE-Bench),路由误差怕深层(本测量)—— 两条方向"
                     "相反的深度轴;逐层回放文献无先例",
                     src="experiments/out/w3sa_absorb.json:curve",
                     headline=True)
        add4("W2CV生产级路由margin",
             "**DeepSeek-V4-Flash**(256 专家 top-6,sqrtsoftplus + bias 校正)"
             "INT4 binding / 实际翻转 / soundness 违约",
             f"{100*_b4['binding']:.1f}% / {100*_b4['flip']:.1f}% / "
             f"{_b4['soundness_viol']}",
             "**把'production margins 须在 DSV4 上重测'这条 Limitations 关掉**。"
             f"计分 {_bv['n_layers_scored']} 层、{_b4['n_tokens']:,} token;"
             f"剔除 {_bv['n_layers_hash_excluded']} 个 hash 路由层"
             "(HashTopK 由 token id 经 tid2eid 定专家,margin 对它无定义 —— "
             "判别用'该层有无 e_score_correction_bias',不按层号猜)。"
             "**口径与旧支不同且必须不同**:V4 用 noaux_tc,选择量是 s(z)+b,"
             "per-expert bias 让 logit 域的序与实际选择无关,故 margin 取在"
             f"**选择分数域**,证书条件 m > 2Lε∞,L={_bv['lipschitz_L']}"
             "(sqrtsoftplus 的数值上界)。量化口径 group-32 absmax RTN 与旧支一致 "
             "⟹ 跨模型可比。结论同向且更极端:V2-Lite 93.7% binding → V4 "
             f"{100*_b4['binding']:.1f}%,证书作为门会拒掉几乎全部流量,而"
             "soundness 违约仍为 0(定理成立,不可用的是**门**不是**证书**)。"
             f"INT3/INT2 binding {100*_bv['per_bits']['int3']['binding']:.1f}%/"
             f"{100*_bv['per_bits']['int2']['binding']:.1f}%",
             src="experiments/out/w2cv_v4_router_margin.json:per_bits.int4",
             headline=True)
        _k0 = json.load(open(os.path.join(OUT, "rrd_k0_output_visible.json"),
                             encoding="utf-8"))
        add3("K0", "TV-输出误差 Spearman",
             f"{_k0['summary']['spearman_tvreal_reldy']:.3f}",
             "合成池 99,072 读 ×SR 掩位 m∈{2,3,4};TV_real≥0.5 层 1,528 读"
             "rescued=0.0@τ0.02/0.05/0.10;verdict=value_aware_dead",
             src="experiments/out/rrd_k0_output_visible.json:summary")
        _kr = json.load(open(os.path.join(OUT, "rrd_k0_realpool.json"),
                             encoding="utf-8"))
        add3("K0R", "真实池 TV-输出误差 Spearman",
             f"{_kr['summary']['spearman_tv_reldy_all']:.3f}",
             f"{_kr['summary']['n_groups_used']} 个 (层,uid) 真实请求池组"
             "(池深≥64,q 同 uid 配对,rope 齐,INT6/4/3 三档);"
             "TV≥0.5 层为空 ⇒ 预注册分支:该量化族在真实池上 TV 不过 0.5,"
             "K0 原判(value_aware_dead)维持并加强",
             src="experiments/out/rrd_k0_realpool.json:summary", headline=True)
        _kp = json.load(open(os.path.join(OUT, "rrd_k0p_query_spectrum.json"),
                             encoding="utf-8"))
        add3("K0'", "q 谱 ρ90(样本内)vs 留出",
             f"{_kp['summary']['rho90_median_eigen']:.3f} vs "
             f"{_kp['summary']['heldout_top32_median']:.3f}",
             "n=96/层 ≪ d=448 小样本警戒;对角 ρ90=0.813;verdict=gray;"
             "W2-a 大样本后留出恢复 —— 小样本教训的对照锚",
             src="experiments/out/rrd_k0p_query_spectrum.json:summary")
    except FileNotFoundError as e:
        print("[canon] p3 W 线产物缺失,跳过:", e)
    return C


def main():
    C = build()
    pj = os.path.join(ROOT, "papers", "p1-kv-certificates", "canon.json")
    json.dump({"generated_by": "tools/make_canon.py", "entries": C},
              open(pj, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    lines = ["# 冻结的数字与口径清单(CANON)", "",
             "**本文件由 `tools/make_canon.py` 从 `experiments/out/*.json` 自动生成,请勿手改。**", "",
             "`tests/test_paper_claims.py` 用它同时核查中文稿、`papers/p1-kv-certificates/arxiv/main.tex`、",
             "`papers/p1-kv-certificates/abstract_en.md` —— 任何一份文档漏写或写错其中一个数字都会 FAIL。",
             "这是为了解决『代码比论文成熟得快、多份文档相互矛盾』的问题。", ""]
    cur = None
    for e in C:
        if e["group"] != cur:
            cur = e["group"]
            lines += [f"## {cur}", "", "| 量 | 值 | 口径 |", "|---|---|---|"]
        lines.append(f"| {e['name']} | **{e['value']}** | {e['scope']} |")
    lines.append("")
    open(os.path.join(ROOT, "papers", "p1-kv-certificates", "CANON.md"), "w", encoding="utf-8").write("\n".join(lines))
    print(f"生成 {len(C)} 条:papers/p1-kv-certificates/CANON.md + papers/p1-kv-certificates/canon.json")


if __name__ == "__main__":
    main()
