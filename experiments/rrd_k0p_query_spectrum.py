# -*- coding: utf-8 -*-
"""K0'(离线,零 GPU):Σ_q 谱衰减曲线 —— 椭球线(RRD-1/G1)最便宜的 kill-shot。

出处:p3 门序(docs/research/p3-scoping/README.md §3)与 ASSESSMENT §2.2 的
谱分析义务 —— 负先验 Q3(对角 q-加权仅 −1.6%)必须被谱曲线解释:
对角形式丢掉全部 off-diagonal 结构,而 SQuat 式主张恰是 query 集中在
低维**子空间**。若谱平坦,椭球线在此模型上没有物理基础,G1 大概率不过。

**预注册判读(先于计算写死,勿改)** —— 以逐层 ρ90 的中位数为主判据,
ρ90 = 非中心二阶矩 Σ_q=E[qqᵀ] 的特征值前 r 个覆盖 90% 能量所需的 r/d:

    ρ90_median ≤ 0.15   → spectrum_concentrated:低维子空间存在,
                           椭球线有物理基础,进 G1 full-cov oracle;
    ρ90_median ≥ 0.50   → spectrum_flat:能量不集中,椭球线无物理
                           基础,G1 预判不过 —— 椭球线杀,p3 主轴
                           转输出可见(K0)与传输/分配面;
    其间                 → gray:不判死;进 G1 但带既有早退门
                           (p95 score-shift 收紧 <1.3× 即停线)。

附带义务(ASSESSMENT §2.2):同时报告**坐标基**集中度(diag(Σ_q) 的
ρ90_diag)与 Q3 的 w 跨度统计 (max/mean)^(1/4) —— 若 ρ90_eigen ≪
ρ90_diag,即"对角弱而子空间强"的谱解释成立;若两者同平,则与 kill
分支互证。

数据:experiments/out/p101_wc_q05_raw.rank0.pt(与 Q3 同源):
q|L* 真实 query(含 scale)、centry_c4|L* 真实 c4 条目,21 个共有层。
量化误差只落在前 NOPE=448 维(7×64 tile),谱取 q[:, :448] —— 与
椭球度量作用的 Δk 空间严格同域。

G0 论证(现存 trace 用于 oracle 的显式论证,G0-REVIEW.md §K0/K0'):
本实验只消费 q 侧样本;q 从不进 packed pool,不落入跨代读污染面。

python3 experiments/rrd_k0p_query_spectrum.py
"""
import hashlib
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(EXP, "out")
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402

NOPE = 448
SRC = os.path.join(OUT, "p101_wc_q05_raw.rank0.pt")

# 预注册阈值(见 docstring;计算前写死)
RHO90_GO, RHO90_KILL = 0.15, 0.50
ENERGY_MARKS = (0.50, 0.80, 0.90, 0.95, 0.99)

# 稳健性检查(首跑后发现 n=96 ≪ d=448,样本秩上限 96,集中度可能被小样本
# 高估 —— 本检查在**读到其数值之前**加入并写死判据):split-half 留出:
# 前半样本拟合 top-32 特征子空间,测后半样本能量落入比例。平谱基线下
# 任意 32 维子空间只能接住 32/448≈7%;留出能量 ≥0.70 即子空间真实。
HELDOUT_R, HELDOUT_PASS = 32, 0.70


def sha256(path, cap=1 << 30):
    h, n = hashlib.sha256(), 0
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
            n += len(blk)
            if n >= cap:  # 超大文件截断哈希,记 truncated
                return h.hexdigest()[:16] + "-trunc"
    return h.hexdigest()[:16]


def spectrum_stats(mat):
    """mat: [N, d] 样本;返回非中心/中心两套谱统计。"""
    n, d = mat.shape
    res = {}
    for kind in ("uncentered", "centered"):
        x = mat - mat.mean(0, keepdim=True) if kind == "centered" else mat
        s2 = (x.T @ x) / n                       # [d, d]
        ev = torch.linalg.eigvalsh(s2).flip(0).clamp_min(0)
        tot = float(ev.sum())
        cum = torch.cumsum(ev, 0) / max(tot, 1e-30)
        rho = {f"rho{int(m*100)}": float((int((cum < m).sum()) + 1) / d)
               for m in ENERGY_MARKS}
        pr = float(ev.sum() ** 2 / (ev ** 2).sum())          # participation ratio
        dg = s2.diag().sort(descending=True).values.clamp_min(0)
        cumd = torch.cumsum(dg, 0) / max(float(dg.sum()), 1e-30)
        res[kind] = {
            **rho,
            "effective_rank_pr": pr,
            "lam1_over_mean": float(ev[0] / (tot / d)) if tot > 0 else None,
            "top8_energy": float(cum[7]),
            "top32_energy": float(cum[31]),
            "rho90_diag": float((int((cumd < 0.90).sum()) + 1) / d),
            "w_quarter_span": float((dg[0] / dg.mean()) ** 0.25),  # Q3 口径
        }
    return res, n, d


def _proj_energy(fit, ev, r):
    if fit.shape[0] < r or ev.shape[0] == 0:
        return None
    s2 = (fit.T @ fit) / fit.shape[0]
    _, vecs = torch.linalg.eigh(s2)
    P = vecs[:, -r:]                                  # top-r 特征向量
    return float(((ev @ P) ** 2).sum() / (ev ** 2).sum().clamp_min(1e-30))


def heldout_cross_record(q3, r=HELDOUT_R):
    """跨记录切分(门用):前半 record(全头)拟合 → 后半 record 评估。
    q3: [R, H, d];同头跨时间泛化,heldout_pass 的载体。"""
    R, d = q3.shape[0], q3.shape[-1]
    return _proj_energy(q3[: R // 2].reshape(-1, d), q3[R // 2:].reshape(-1, d), r)


def heldout_cross_head(q3, r=HELDOUT_R):
    """跨头切分(诊断用,非门):偶数头拟合 → 奇数头评估。
    注:首跑曾把 even/odd 行切分误标为「时间交错」——实测行序为
    record×head(头在内层),该切分切开的是头,据实改名。此值低于
    跨记录值 ⇒ 子空间按头分化,G1 的 G 应按 (layer, head) 建而非池化。"""
    d = q3.shape[-1]
    return _proj_energy(q3[:, 0::2].reshape(-1, d), q3[:, 1::2].reshape(-1, d), r)


def main():
    raw = torch.load(SRC, map_location="cpu", weights_only=False)
    layers = sorted(int(k.split("|L")[1]) for k in raw if k.startswith("q|"))
    rows = []
    for L in layers:
        recs = raw["q|L%d" % L]
        q3 = torch.stack([r["q"].float()[:, :NOPE] * float(r["scale"])
                          for r in recs])            # [R, H, 448]
        q = q3.reshape(-1, q3.shape[-1])
        st, n, d = spectrum_stats(q)
        rows.append({"layer": L, "n_q": n, "dim": d,
                     "n_records": int(q3.shape[0]), "n_heads": int(q3.shape[1]),
                     "heldout_top%d_energy" % HELDOUT_R: heldout_cross_record(q3),
                     "heldout_cross_head": heldout_cross_head(q3), **st})

    med = sorted(r["uncentered"]["rho90"] for r in rows)
    rho90_med = med[len(med) // 2]
    if rho90_med <= RHO90_GO:
        verdict = "spectrum_concentrated"
    elif rho90_med >= RHO90_KILL:
        verdict = "spectrum_flat"
    else:
        verdict = "gray"
    diag_med = sorted(r["uncentered"]["rho90_diag"] for r in rows)[len(rows) // 2]
    ho_key = "heldout_top%d_energy" % HELDOUT_R
    ho = sorted(r[ho_key] for r in rows if r[ho_key] is not None)
    ho_med = ho[len(ho) // 2] if ho else None
    heldout_ok = ho_med is not None and ho_med >= HELDOUT_PASS
    if verdict == "spectrum_concentrated" and not heldout_ok:
        verdict = "gray"  # 小样本稳健性未过:降级,不给 go

    rep = {
        "what": "K0':Σ_q 谱衰减 —— 椭球线(RRD-1/G1)kill-shot",
        "kind": "shadow 离线(零 GPU);真实 q,谱域=前 448 维(c4 量化误差同域)",
        "preregistered": {
            "primary": "median ρ90(uncentered eigen)",
            "go": f"≤{RHO90_GO} → concentrated,进 G1",
            "kill": f"≥{RHO90_KILL} → flat,椭球线杀",
            "gray": "其间 → 进 G1 但带早退门(p95 score-shift <1.3× 停线)",
        },
        "verdict": verdict,
        "summary": {
            "rho90_median_eigen": rho90_med,
            "rho90_median_diag": diag_med,
            "diag_vs_eigen_gap": diag_med - rho90_med,
            "heldout_top%d_median" % HELDOUT_R: ho_med,
            "heldout_pass": heldout_ok,
            "heldout_flat_baseline": HELDOUT_R / NOPE,
            "heldout_cross_head_median": (lambda v: v[len(v) // 2] if v else None)(
                sorted(r["heldout_cross_head"] for r in rows
                       if r["heldout_cross_head"] is not None)),
            "layers": len(rows),
        },
        "q3_negative_prior_explained": (
            "ρ90_diag ≫ ρ90_eigen ⇒ 结构在 off-diagonal,对角形式(Q3 −1.6%)"
            "本就看不见 —— 谱解释成立" if diag_med - rho90_med > 0.15 else
            "对角与特征基集中度相近 ⇒ Q3 的弱不是基选择问题,与谱判读互证"),
        "per_layer": rows,
        "inputs": [{
            "path": os.path.relpath(SRC, EXP),
            "bytes": os.path.getsize(SRC),
            "sha256_16": sha256(SRC),
            "freshness_argument": "仅消费 q 侧样本;q 从不进 packed pool,"
                                  "不落入跨代读污染面(G0-REVIEW.md)",
        }],
        "caliber": [
            "谱=非中心 E[qqᵀ](与 E[(qᵀe)²]=eᵀΣ_q e 严格对应);中心谱附列",
            "q 取前 448 维(NOPE)×scale,与 Q3/量化误差空间同域",
            "单 rank(rank0)采集;DeepSeek-V4 c4 池口径,层集见 per_layer",
            "**样本量警戒**:每层 n≈96 ≪ d=448,样本谱集中度有小样本偏置;"
            "主判据必须与 split-half 留出能量(heldout_pass)同读,"
            "缺 heldout 通过则 verdict 已降级 gray;G1 oracle 复核时需更大 n",
            "谱集中只说明椭球有物理基础,不自动等于 tightness 收益 —— "
            "G1 oracle 才是收益判据(禁止表述清单第 6 条)",
        ],
        "manifest": stamp(run_id="rrd_k0p", seed=None,
                          stack="local cpu offline (torch eigvalsh)"),
        "generated_by": "rrd_k0p_query_spectrum.py",
    }
    dst = os.path.join(OUT, "rrd_k0p_query_spectrum.json")
    json.dump(rep, open(dst, "w"), ensure_ascii=False, indent=1)
    print("verdict:", verdict)
    print("median ρ90 eigen=%.4f | diag=%.4f | gap=%.4f | heldout_top%d=%s(≥%.2f:%s)"
          % (rho90_med, diag_med, diag_med - rho90_med, HELDOUT_R,
             "%.3f" % ho_med if ho_med is not None else "NA",
             HELDOUT_PASS, heldout_ok))
    for r in rows[:5]:
        u = r["uncentered"]
        print("L%02d n=%d ρ90=%.3f PR=%.1f top32=%.3f diagρ90=%.3f"
              % (r["layer"], r["n_q"], u["rho90"], u["effective_rank_pr"],
                 u["top32_energy"], u["rho90_diag"]))


if __name__ == "__main__":
    main()
