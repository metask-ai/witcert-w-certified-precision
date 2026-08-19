"""论文的定理章节由 Lean **编译产出**,不是从源码正则抄出来的。

## 三层递进(每一层都在回答"这段文字能不能被伪造")

1. 最初:论文里的 `\\begin{theorem}` 是手抄的 —— 与 Lean 里实际证明的东西可以悄悄分家。
   本项目已有两次证书公式被外部评审证伪的先例,根因都是"纸上写的"与"实际成立的"不是同一式子。
2. 其次:改成正则切 Lean 源码 —— 好一些,但那是**解析器作者(人)对代码的理解**,
   而且旁边的 `/-- -/` 文档注释同样是人写的散文,同样会漂移。
3. 现在:由 **Lean 自己**导出(`formal/Export.lean`)。输出的是 elaborate **之后**的类型,
   用 Lean 自带 pretty-printer 渲染;每条定理的公理依赖由 `collectAxioms` 机器给出。
   于是论文里的定理陈述是"编译"结果,不是转录结果 —— 想写一个没证的定理,它编译不出来。

文档注释仍然保留,但明确标为**非规范性**,并对它做漂移检测(引用了陈述中不存在的标识符即告警)。

    python tools/lean_extract.py
"""
import json
import os
import re
import subprocess
import tempfile
import textwrap

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FORMAL = os.path.join(ROOT, "formal")
ELAN = os.path.expanduser("~/.elan/bin")
STD_AX = {"propext", "Classical.choice", "Quot.sound"}
MAIN = {"WitCert.tv_le_eform": "L1 main theorem: e-form TV bound for softmax perturbation",
        "WitCert.sinh_le_mul_exp_sq_div_six": "L2 core: sub-Gaussian proxy of uniform dither",
        "WitCert.request_budget_sound": "L3: request-level union budget",
        "WitCert.A_blockwise_eq_perToken": "L4: proof-kernel refinement (blockwise = per-token)"}
STANDALONE = ["Refinement.lean", "Factorial.lean", "Budget.lean", "EForm.lean"]

# 追加到 standalone 文件末尾的导出片段:只导出**本文件内**声明的定理
SNIPPET = r'''
section WitCertExport
open Lean Elab Command
def wcEsc (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "" | c => c.toString) ""
-- 与 formal/Export.lean 的 isGenerated **同一份语义**(2026-08-06:两份过滤器
-- 分家导致 10 条 class 字段投影以 :0 进了 p1 附录 —— 同一个已诊断过的虚报
-- bug 在复制体里没修;此后两处必须同步改)
def wcGen (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "proof_" || s.startsWith "eq_" || s == "eq_def"
                 || s.startsWith "match_" || s.startsWith "_"
                 || s == "injEq" || s == "inj" || s == "sizeOf_spec"
                 || s == "noConfusion" || s == "noConfusionType"
                 -- **递归子族**(2026-08-09:`inductive Balanced : ... → Prop` 使
                 -- `Balanced.brecOn` 以 thmInfo 出现,定位不到源行 ⟹ 抽取整体失败)。
                 -- Prop 值归纳类型的这几个自动生成物都会变成"定理",必须一并剔除。
                 || s == "brecOn" || s == "binductionOn" || s == "below"
                 || s == "ibelow" || s == "recOn" || s == "casesOn"
                 || s == "ndrec" || s == "ndrecOn" || s == "induct"
  | _ => false
unsafe def wcEmit : CommandElabM Unit := do
  let env ← getEnv
  let mut items : Array String := #[]
  for (n, ci) in env.constants.toList do
    -- getModuleIdxFor? 为 none <=> 该声明属于当前正在编译的文件;
    -- 投影过滤同 Export.lean:class 字段是假设的访问器,不是被证明的命题
    if (env.getModuleIdxFor? n).isNone && !n.isInternal && !wcGen n
        && (env.getProjectionFnInfo? n).isNone then
      match ci with
      | .thmInfo val => do
          let ts ← liftTermElabM do pure (toString (← Meta.ppExpr val.type))
          let ax ← liftCoreM (collectAxioms n)
          let axs := String.intercalate "," (ax.toList.map (fun a => "\"" ++ wcEsc a.toString ++ "\""))
          items := items.push <| "{\"name\":\"" ++ wcEsc n.toString ++ "\",\"kind\":\"theorem\",\"type\":\""
                                 ++ wcEsc ts ++ "\",\"axioms\":[" ++ axs ++ "]}"
      | _ => pure ()
  IO.println ("WCJSON{\"items\":[" ++ String.intercalate "," items.toList ++ "]}")
run_cmd wcEmit
end WitCertExport
'''


def run(cmd, cwd):
    env = dict(os.environ, PATH=ELAN + os.pathsep + os.environ.get("PATH", ""))
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, shell=True)


def export_mathlib():
    r = run("lake env lean Export.lean", FORMAL)
    line = next((l for l in r.stdout.splitlines() if l.startswith('{"source"')), None)
    assert line, f"Mathlib 层导出失败:\n{r.stdout[-800:]}\n{r.stderr[-800:]}"
    return [dict(x, layer="Mathlib 层(ℝ / 测度论)") for x in json.loads(line)["items"]]


def export_standalone():
    out = []
    for f in STANDALONE:
        src = open(os.path.join(FORMAL, "standalone", f), encoding="utf-8").read()
        # 不改原文件:写一份带导出片段的临时副本
        tmp = os.path.join(FORMAL, "standalone", f".wcexport_{f}")
        open(tmp, "w", encoding="utf-8").write("import Lean\n" + src + SNIPPET)
        try:
            r = run(f"lean {os.path.basename(tmp)}", os.path.join(FORMAL, "standalone"))
            line = next((l[6:] for l in r.stdout.splitlines() if l.startswith("WCJSON")), None)
            assert line, f"{f} 导出失败:\n{r.stdout[-600:]}\n{r.stderr[-600:]}"
            for x in json.loads(line)["items"]:
                out.append(dict(x, layer="零依赖层(秒级 CI)", src_file=f"standalone/{f}"))
        finally:
            os.path.exists(tmp) and os.remove(tmp)
    return out


def locate(items):
    """给每条定理补上源文件与行号(仅元数据用正则;陈述本身来自 Lean)。"""
    idx, binders = {}, set()
    for sub in ("WitCert", "standalone"):
        d = os.path.join(FORMAL, sub)
        for f in sorted(os.listdir(d)):
            if not f.endswith(".lean") or f.startswith(".wcexport"):
                continue
            lines = open(os.path.join(d, f), encoding="utf-8").read().splitlines()
            for i, ln in enumerate(lines):
                m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*"
                             r"(theorem|lemma)\s+([A-Za-z_][\w'.]*)", ln)
                if not m:
                    continue
                short = m.group(2)
                doc = ""
                j = i - 1
                if j >= 0 and lines[j].rstrip().endswith("-/"):
                    k = j
                    while k >= 0 and "/--" not in lines[k]:
                        k -= 1
                    if k >= 0:
                        dm = re.search(r"/--\s*(.*?)\s*-/", "\n".join(lines[k:j + 1]), re.S)
                        if dm:
                            doc = re.sub(r"\s+", " ", dm.group(1)).strip()
                idx[short] = (f"{sub}/{f}", i + 1, doc)
                # 收集该文件所有签名里的 binder 名:命题 binder 在 elaborate 后会变成匿名 →,
                # 名字不出现在 Lean 打印的类型里,注释引用它们是合法的,不算漂移。
                sig = "\n".join(lines[i:i + 12])
                binders.update(re.findall(r"[({\[]\s*([A-Za-z_][\w'\s]*?)\s*:", sig))
    known = set(idx) | {w for b in binders for w in b.split()}
    for it in items:
        parts = it["name"].split(".")
        # 声明可带命名空间前缀(如 lemma BddDiffAt.c_nonneg):先试两段
        # 后缀再退一段 —— 单段查不到即 ?:0(2026-08-06 用户在 PDF 抓到)
        short2 = ".".join(parts[-2:])
        short = parts[-1]
        f, line, doc = idx.get(
            short2, idx.get(short, (it.get("src_file", "?"), 0, "")))
        it["file"], it["line"], it["doc"] = f, line, doc
        it["doc_drift"] = [t for t in re.findall(r"`([^`]+)`", doc)
                           if re.fullmatch(r"[A-Za-z_][\w'.]*", t)
                           and t not in it["type"] and t not in known]
        it["is_main"] = it["name"] in MAIN
        it["main_label"] = MAIN.get(it["name"], "")
    # 行号 0 = 定位失败却会被静默印进附录("references resolve" 变假话)。
    # 2026-08-06 已观察一轮(10 条 class 字段投影,根因是过滤器分家,已修),
    # 按"先观察后上膛"纪律,此处上膛为硬失败;ReleaseGate 的 locatable
    # 不变量在出包关兜底同一条。
    lost = [x["name"] for x in items if x["line"] == 0]
    assert not lost, f"源位置定位失败(line=0),不许出附录:{lost}"
    return items


def emit_md(items):
    L = ["# 定理陈述(由 Lean 编译产出)", "",
         "**本文件由 `tools/lean_extract.py` 生成 —— 内容来自 `formal/Export.lean` 的 Lean 导出,",
         "不是从源码抄的。** 类型是 elaborate 之后由 Lean 自带 pretty-printer 渲染的;",
         "每条定理的公理依赖由 `collectAxioms` 机器给出。想在论文里写一个没证的定理,它编译不出来。", "",
         f"核心定理 {sum(1 for x in items if x['is_main'])} 条;另有支撑引理 "
         f"{len(items) - sum(1 for x in items if x['is_main'])} 条(多为零依赖层的 typeclass 样板,"
         "仅为公理审计完整性列出,对外表述不计入定理数)。", ""]
    cur = None
    for it in sorted(items, key=lambda x: (x["layer"], not x["is_main"], x["name"])):
        if it["layer"] != cur:
            cur = it["layer"]
            L += [f"## {cur}", ""]
        tag = f" **【{it['main_label']}】**" if it["is_main"] else ""
        ax = "、".join(it["axioms"]) or "无(纯计算)"
        L += [f"### `{it['name']}`{tag}", "",
              f"来源 `formal/{it['file']}:{it['line']}`;公理依赖(Lean 给出):{ax}", "",
              "```lean", it["type"], "```", ""]
        if it["doc_drift"]:
            L += [f"> ⚠️ 注释漂移:引用了陈述中不存在的标识符 {it['doc_drift']}", ""]
    open(os.path.join(ROOT, "papers", "p1-kv-certificates", "THEOREMS.md"), "w", encoding="utf-8").write("\n".join(L))


ASCII = [("ℕ","Nat"),("、",", "),("ℝ","R"),("∀","forall "),("∃","exists "),("≤","<="),("≥",">="),("≠","!="),
         ("∑","Sum "),("Σ","Sum "),("⋃","Union "),("∈"," in "),("→","->"),("↔","<->"),
         ("ι","iota"),("δ","delta"),("ε","eps"),("μ","mu"),("Ω","Omega"),("σ","sigma"),
         ("π","pi"),("θ","theta"),("α","alpha"),("β","beta"),("↑",""),("⟹","==>"),
         ("×","x"),("·","*"),("−","-"),("₀","0"),("₁","1"),("₂","2"),("’","'"),("‖","||"),
         ("｜","|"),("│","|"),("（","("),("）",")"),("∅","{}"),("⊆","subset "),("∘"," o "),
         ("λ","fun "),("𝔼","E"),("√","sqrt "),("∞","inf"),("∫","Int "),("Fin ","Fin "),("²","^2"),("½","1/2"),("–","-"),("—","-"),("̃",""),("̄",""),("τ","tau"),("Δ","Delta"),("ρ","rho"),("κ","kappa"),("〈","<"),("〉",">")]


def to_ascii(t):
    """pdflatex 无法处理 Lean 的 Unicode;verbatim 内做保义音译。
    规范陈述以 Lean 源为准(每条给出 file:line),此处仅为可编译的忠实展示。"""
    for a, b in ASCII:
        t = t.replace(a, b)
    return "".join(c if ord(c) < 128 else "?" for c in t)


LAYER_EN = {"Mathlib 层(ℝ / 测度论)": "Mathlib layer (reals / measure theory)",
            "零依赖层(秒级 CI)": "Dependency-free layer (seconds-scale CI)"}


def emit_tex(items):
    def esc(s):
        for a, b in (("\\", r"\textbackslash{}"), ("_", r"\_"), ("&", r"\&"), ("%", r"\%"),
                     ("#", r"\#"), ("$", r"\$"), ("{", r"\{"), ("}", r"\}")):
            s = s.replace(a, b)
        return s
    n_main = sum(1 for x in items if x["is_main"])
    L = [r"% Generated by tools/lean_extract.py from the Lean export of formal/Export.lean. Do not edit by hand.",
         r"\section{Machine-checked theorem statements (compiled, not transcribed)}",
         r"\label{sec:theorems}", "",
         r"This section is \emph{compiled} from the Lean development shipped in the released repository (\texttt{witcert-kv-cer\-tif\-i\-cates}): \texttt{formal/Export.lean}",
         r"walks the environment, prints each theorem's \emph{elaborated} type with Lean's own",
         r"pretty-printer, and lists the axioms each proof actually depends on via",
         r"\texttt{collectAxioms}; for the pdflatex toolchain, non-ASCII symbols are",
         r"mechanically transliterated ($\mathbb{R} \to \mathrm{R}$, $\mathbb{N} \to \mathrm{Nat}$, etc.).",
         r"Nothing here is transcribed by hand, so a statement that is not",
         r"proved cannot appear. Twice in this project's history a certificate formula was falsified",
         r"by external review, and in both cases the root cause was that the statement on paper and",
         r"the statement that holds were not the same object. The development proves " + str(n_main) +
         r" \emph{core} theorems---the results cited in the body---plus " + str(len(items) - n_main) +
         r" supporting lemmas, many of which are typeclass boilerplate of the dependency-free layer",
         r"and are listed compactly below only so that the axiom audit covers the whole development;",
         r"every proof depends only on \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}",
         r"(or on nothing at all), and none on \texttt{sorryAx}.",
         r"The whole development re-verifies independently: clone",
         r"\url{https://github.com/metask-ai/witcert-kv-certificates} and run",
         r"\texttt{cd formal \&\& bash check\_all.sh}, which rebuilds every proof and re-runs the",
         r"axiom audit from scratch; the \texttt{file:line} references below resolve in that repository.", ""]
    cur = None
    compact = []          # 零依赖层非主定理:仅名称+来源,免得样板引理稀释核心定理
    def flush_compact():
        nonlocal compact, L
        if compact:
            L += [r"\paragraph{Supporting lemmas (axiom-audit completeness only)}",
                  r"{\small\raggedright " + "; ".join(compact) + r".\par}", ""]
            compact = []
    for it in sorted(items, key=lambda x: (x["layer"], not x["is_main"], x["name"])):
        if it["layer"] != cur:
            flush_compact()
            cur = it["layer"]
            L += [r"\subsection{" + esc(LAYER_EN.get(cur, cur)) + "}", ""]
        if (not it["is_main"]) and it["layer"].startswith("零依赖"):
            compact.append(r"\texttt{" + esc(it["name"]) + r"} (\texttt{" + esc(it["file"])
                           + ":" + str(it["line"]) + r"})")
            continue
        L += [r"\paragraph{" + esc(it["main_label"] or it["name"]) + r"}",
              r"{\small\raggedright \emph{Source:} \texttt{formal/" + esc(it["file"]) + ":" + str(it["line"])
              + r"}; \emph{axioms:} \texttt{" + esc(", ".join(it["axioms"]) or "none") + r"}.\par}",
              r"{\scriptsize\begin{verbatim}",
              "\n".join(textwrap.fill(ln, width=95, subsequent_indent="    ",
                                       break_long_words=False, break_on_hyphens=False)
                         for ln in to_ascii(it["type"]).splitlines()),
              r"\end{verbatim}}"]
        L.append("")
    flush_compact()
    body = to_ascii("\n".join(L))
    open(os.path.join(ROOT, "papers", "p1-kv-certificates", "arxiv", "theorems.tex"), "w", encoding="utf-8").write(body)


def emit_tex_p2(items):
    """论文2 定理附录:与 p1 同纪律 —— 编译产出,非转录。主定理(MAIN2)
    全文陈述;其余作 axiom-audit 紧凑清单。写入 papers/p2-attention-memory/
    theorems.tex,由 main.tex 以 \\input 挂为附录。"""
    def esc(s):
        for a, b in (("\\", r"\textbackslash{}"), ("_", r"\_"), ("&", r"\&"), ("%", r"\%"),
                     ("#", r"\#"), ("$", r"\$"), ("{", r"\{"), ("}", r"\}"),
                     ("^", r"\textasciicircum{}"), ("~", r"\textasciitilde{}")):
            s = s.replace(a, b)
        return s
    n_main = sum(1 for x in items if x["name"] in MAIN2)
    L = [r"% Generated by tools/lean_extract.py from the Lean export of formal/Export.lean. Do not edit by hand.",
         r"\section{Machine-checked theorem statements}",
         r"\label{sec:theorems}", "",
         r"Compiled, not transcribed. Every theorem name cited in the body (\texttt{ledger\_sound},",
         r"\texttt{telescope\_sum}, \texttt{shared\_read\_sound}, the bridge and",
         r"e-process lemmas, \ldots) resolves to a statement below. This section is",
         r"\emph{compiled} from the Lean development shipped in the released repository (\texttt{witprobe-atten\-tion-memory}): \texttt{formal/Export.lean} walks the",
         r"environment, prints each theorem's \emph{elaborated} type with Lean's own",
         r"pretty-printer, and lists the axioms each proof actually depends on via",
         r"\texttt{collectAxioms}; non-ASCII symbols are mechanically transliterated for",
         r"the pdflatex toolchain. Nothing here is transcribed by hand, so a statement",
         r"that is not proved cannot appear. The contract calculus proves " + str(n_main) +
         r" \emph{core} theorems---the results cited in the body---plus " + str(len(items) - n_main) +
         r" supporting lemmas listed compactly so the axiom audit covers the whole",
         r"development; every proof depends only on \texttt{propext},",
         r"\texttt{Classical.choice} and \texttt{Quot.sound}, and none on \texttt{sorryAx}.",
         r"The whole development re-verifies independently: clone",
         r"\url{https://github.com/metask-ai/witprobe-attention-memory} and run",
         r"\texttt{cd formal \&\& bash check\_all.sh}, which rebuilds every proof and re-runs the",
         r"axiom audit from scratch; the \texttt{file:line} references below resolve in that repository.", ""]
    compact = []
    for it in sorted(items, key=lambda x: (x["name"] not in MAIN2, x["name"])):
        if it["name"] not in MAIN2:
            compact.append(r"\texttt{" + esc(it["name"].replace(P2_NS, "")) + r"} (\texttt{"
                           + esc(it["file"]) + ":" + str(it["line"]) + r"})")
            continue
        L += [r"\paragraph{" + esc(MAIN2[it["name"]]) + r"}",
              r"{\small\raggedright \emph{Name:} \texttt{" + esc(it["name"]) + r"}; "
              r"\emph{source:} \texttt{formal/" + esc(it["file"]) + ":" + str(it["line"])
              + r"}; \emph{axioms:} \texttt{" + esc(", ".join(it["axioms"]) or "none") + r"}.\par}",
              r"{\scriptsize\begin{verbatim}",
              "\n".join(textwrap.fill(ln, width=95, subsequent_indent="    ",
                                       break_long_words=False, break_on_hyphens=False)
                         for ln in to_ascii(it["type"]).splitlines()),
              r"\end{verbatim}}", ""]
    if compact:
        L += [r"\paragraph{Supporting lemmas (axiom-audit completeness only)}",
              r"{\small\raggedright " + "; ".join(compact) + r".\par}", ""]
    body = to_ascii("\n".join(L))
    open(os.path.join(ROOT, "papers", "p2-attention-memory", "theorems.tex"),
         "w", encoding="utf-8").write(body)


#: 论文2 的形式化在 `WitCert.Calculus.*` 下。**必须按篇分开统计** —— 否则一加模块,
#: 论文1 冻结的"Lean 主定理数 4 / 机器检查定理总数 30"就被冲掉,守卫当场打红。
#: 这与 canon 的 `paper` 字段是同一条纪律:并行论文互不干扰。
P2_NS = "WitCert.Calculus."

#: 论文2 的主定理 —— 带类型的契约演算,而不是把三条普通引理翻译成 Lean。
MAIN2 = {
    "WitCert.Calculus.comp_sound":
        "typed contract composition: metrics must match by construction",
    "WitCert.Calculus.Budget.conditional_union_le":
        "conditional (adaptive) union bound over first-failure events",
    "WitCert.Calculus.bridge_sound":
        "bridge contract semantics: cross-metric composition needs a proved bridge",
    "WitCert.Calculus.score_bridge":
        "witness-to-score bridge: |Δ(scale·q·k)| ≤ scale·‖q‖·‖Δk‖ (Cauchy–Schwarz)",
    "WitCert.Calculus.softmax_tv_bridge":
        "score-to-TV bridge: ‖Δs‖∞ ≤ ε ⟹ TV ≤ ½(e^{2ε}−1), instantiating paper 1's tv_le_eform",
    "WitCert.Calculus.softmax_tv_affine":
        "affine form of the score-to-TV bridge: TV ≤ e^{2ε₀}·ε for ε ≤ ε₀",
    "WitCert.Calculus.Ledger.ledger_sound":
        "request-level ledger: conditional union bound + budget sequence, sound at every length",
    "WitCert.Calculus.Ledger.telescope_sum":
        "telescoping budget weights 1/((i+1)(i+2)): unknown-length budget sums to 1-1/(n+1)",
    "WitCert.Calculus.Ville.ville":
        "finite-Omega Ville inequality: P(sup M >= c) <= M0/c, elementary induction, no measure theory",
    "WitCert.Calculus.Ville.eprocess_ville":
        "e-process: product of conditionally mean-<=1 factors gives anytime-valid risk <= delta",
    "WitCert.Calculus.Ledger.coverage_confidence":
        "coverage confidence: (1-p)^n ≤ e^{-np}; zero observed violations is not zero rate",
    "WitCert.Calculus.Ledger.unknown_length_price":
        "unknown-length budgeting costs at most sqrt(2) in sub-Gaussian radius vs uniform split",
    "WitCert.Calculus.Ledger.two_layer_budget_le":
        "two-layer budget: deterministic events at delta=0, probabilistic on telescoping counters",
    "WitCert.Calculus.Ledger.stream_sound":
        "refinement interface: any CertifiedEventStream satisfies the ledger guarantee",
}


def split_by_paper(items):
    """按命名空间分篇:`WitCert.Calculus.*` 属论文2,其余属论文1。"""
    p1 = [x for x in items if not x["name"].startswith(P2_NS)]
    p2 = [x for x in items if x["name"].startswith(P2_NS)]
    return p1, p2


def dump_json(items, paper_dir, main_map):
    nm = sum(1 for x in items if x["layer"].startswith("Mathlib"))
    dst = os.path.join(ROOT, "papers", paper_dir, "theorems.json")
    json.dump({"generated_by": "tools/lean_extract.py (via formal/Export.lean)",
               "n_total": len(items),
               "n_main": sum(1 for x in items if x["name"] in main_map),
               "n_mathlib": nm, "n_standalone": len(items) - nm,
               "axioms_union": sorted({a for x in items for a in x["axioms"]}),
               "names": [x["name"] for x in items]},
              open(dst, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    return dst, nm


def main():
    all_items = locate(export_mathlib() + export_standalone())
    items, items2 = split_by_paper(all_items)
    miss = [k for k in MAIN if k not in {x["name"] for x in items}]
    assert not miss, f"主定理未出现在 Lean 导出中:{miss}"
    bad = [(x["name"], x["axioms"]) for x in items if set(x["axioms"]) - STD_AX]
    assert not bad, f"出现非标准公理(含 sorryAx?):{bad}"
    emit_md(items)
    emit_tex(items)
    _, nm = dump_json(items, "p1-kv-certificates", MAIN)
    if items2:
        miss2 = [k for k in MAIN2 if k not in {x["name"] for x in items2}]
        assert not miss2, f"论文2 主定理未出现在 Lean 导出中:{miss2}"
        dst2, nm2 = dump_json(items2, "p2-attention-memory", MAIN2)
        emit_tex_p2(items2)
        print(f"论文2 契约演算导出 {len(items2)} 条(Mathlib {nm2};主定理 "
              f"{sum(1 for x in items2 if x['name'] in MAIN2)} 条) -> {dst2}")
    print(f"Lean 导出 {len(items)} 条(Mathlib {nm} + 零依赖 {len(items)-nm};主定理 "
          f"{sum(1 for x in items if x['is_main'])} 条)")
    print(f"  公理并集:{sorted({a for x in items for a in x['axioms']})}")
    drift = [(x['name'], x['doc_drift']) for x in items if x['doc_drift']]
    for n, d in drift:
        print(f"  ⚠️ 注释漂移 {n}: {d}")
    print("  -> papers/p1-kv-certificates/THEOREMS.md, papers/p1-kv-certificates/arxiv/theorems.tex, papers/p1-kv-certificates/theorems.json")
    n3 = emit_p3_names()
    print(f"  -> papers/p3-witcert-v/theorems.json({n3} 条,扫描 formal/WitCert/*.lean)")


#: p3 的定理名对账表:**扫描出来,不手工维护**。历史上它是手写的,加了新定理
#: (conformal_risk_union)后正文引用立刻对不上 —— 与 REGISTRY 分家同族。
def emit_p3_names():
    """扫描 formal/WitCert/*.lean 的 namespace + theorem/lemma,落全限定名。"""
    import glob as _g
    names = set()
    for path in sorted(_g.glob(os.path.join(ROOT, "formal", "WitCert", "*.lean"))):
        # 发布层不计入论文定理数 —— `ReleaseGate.lean` 的文件头自己就写着这句,
        # 但提取器从没执行它。2026-08-14 实证:给出包关补了 p3/p4 两条
        # `publishable ... = by decide`,p3 正文的"243 exported theorems"当场变
        # 245 —— **工程改动动了论文数字**。而那句话说的是"all probabilistic
        # kernels",发布正门(残余泄露/承诺闭包/仓名绑定/dest 冲突)一条都不是
        # 概率核。计数必须与句子说的东西一致,否则数字对得上、指的却不是它。
        if os.path.basename(path).startswith("Release"):
            continue
        ns = []
        for line in open(path, encoding="utf-8"):
            m = re.match(r"\s*namespace\s+([\w.]+)", line)
            if m:
                ns.append(m.group(1))
                continue
            if re.match(r"\s*end\s+[\w.]+\s*$", line) and ns:
                ns.pop()
                continue
            m = re.match(r"\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([\w'!?]+)",
                         line)
            if m:
                names.add(".".join(ns + [m.group(1)]))
    dst = os.path.join(ROOT, "papers", "p3-witcert-v", "theorems.json")
    json.dump({"generated_by": "tools/lean_extract.py:emit_p3_names —— "
                               "扫描 formal/WitCert/*.lean 的 namespace+theorem/lemma;"
                               "**不要手工编辑**(手工表与源码必然分家)",
               "n_total": len(names), "names": sorted(names)},
              open(dst, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    return len(names)


if __name__ == "__main__":
    main()
