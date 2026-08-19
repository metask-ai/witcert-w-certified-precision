# -*- coding: utf-8 -*-
"""K0(离线,零 GPU):TV 空洞/高 TV 读中,真实输出误差小的占比 ——
value-aware 主线(RRD-2/G3/G4)的 kill-shot。

出处:p3 门序(docs/research/p3-scoping/README.md §3 K0)。物理问题:
TV 只看概率质量搬动了多少,不看搬去哪 —— 若质量在 value 相近的条目间
搬动,TV 大而 ‖Δy‖ 小(W1(p,p̂;d_V) 才是对的尺子,MATHEMATICAL_SPEC W1)。
K0 测这件事在真实数据上是否发生、发生多少。

数据:wc_e1raw.rank0-7.pt(E1/p90 同源):写站点捕获的 fp8 条目字节
(43 层,rank 间复制,取 rank0 去重)+ 逐 rank 逐头真实 q(768 读/层)。
对象:掩 m 位尾数的随机舍入(SR),θ/Δ 由字节离线重建(p90 同款解码,
推广到 m∈{2,3,4} —— 扫粗档以填充高 TV 区;结构性问题与工作点无关)。

每读 (layer, q, m) 计算:
  TV_cert  = tanh(osc_bound/4),osc_bound = max(D+u4)−min(D−u4)
             (p90 胜出家族 C2/osc+tanh,u4=精确两点 MGF 半径,δ=1e-6/E 联合)
  TV_real  = ½‖softmax(s)−softmax(ŝ_d)‖₁,SR 实现 d=1..NDRAWS
  rel_dy   = ‖p̂_dᵀX̂_d − pᵀX‖/‖pᵀX‖(MLA:X 即 value 载体,latent 域精确)

**预注册判读(先于计算写死,勿改)**:
  主判据:空洞读层 = {TV_cert ≥ 0.99};τ_y = 0.05(主,附 0.02/0.10 敏感性)
    rescued = P(max_d rel_dy ≤ τ_y | TV_cert ≥ 0.99)
    rescued ≥ 0.5 → value_aware_alive(证书判死的读,输出实际无恙者过半
                     ⇒ 输出可见认证有真实救回空间)
    rescued ≤ 0.2 → value_aware_dead(TV 空洞 ⇒ 输出确实坏,TV 已够用)
    其间          → gray
  预注册回退:若全部 m 档下空洞读集合为空,主判据改用实现层
    {TV_real ≥ 0.5}(逐 (读,draw) 点),同阈同分支 —— 回退在看到任何
    数值之前写死。
  附:Spearman(TV_real, rel_dy)、Spearman(TV_cert, max_d rel_dy) ——
    相关性弱本身即"TV 与输出误差解耦"的独立证据(G3 方向)。

G0 论证(现存 trace 用于 oracle):字节+scale 于写站点同批捕获,解码是
字节的确定函数;q 同批捕获 —— 全程不经 packed pool 槽位往返,不落入
跨代读污染面(G0-REVIEW.md)。

口径警示:池 = 同层 rank0 条目合并(记录无 uid,合成读,非单请求
attention 池);score 只含 nope 448 维(rope 未捕获,p90 同款近似);
绝对 TV/Δy 数值不作 serving 声明,本实验只裁"TV 与输出误差的结构关系"。

python3 experiments/rrd_k0_output_visible.py
"""
import glob
import hashlib
import json
import math
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(EXP, "out")
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402

LUT = torch.arange(256, dtype=torch.uint8).view(torch.float8_e4m3fn).float()
DELTA0 = 1e-6                 # 联合预算:逐池取 δ/E(p90 六审同款)
NDRAWS = 16
MASKS = (2, 3, 4)             # 掩尾数位数
VAC_TH = 0.99                 # 空洞读定义
TVR_TH = 0.5                  # 回退层:实现 TV 高位
TAUS = (0.02, 0.05, 0.10)     # τ_y,主 0.05
TAU_MAIN = 0.05
ALIVE, DEAD = 0.5, 0.2        # 预注册分支
LAM = [2.0 ** k for k in range(-6, 14)]
QCHUNK = 128


def sha256(path, cap=1 << 30):
    h, n = hashlib.sha256(), 0
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
            n += len(blk)
            if n >= cap:
                return h.hexdigest()[:16] + "-trunc"
    return h.hexdigest()[:16]


def decode_entries_m(rec, m):
    """p90 decode_entries 推广:掩 m 位尾数网格。返回 x, lo, hi, Δ, θ, det_e。"""
    nope, scales = rec["nope"], rec["scales"]
    x8 = LUT[nope.long()]
    sc = torch.exp2(scales.float() - 127.0).repeat_interleave(64, dim=1)
    x = x8 * sc
    mag = nope & 0x7F
    step = 1 << m
    keep = 0x7F & ~(step - 1)
    gf = mag & keep
    gc = torch.minimum(gf + step, torch.full_like(gf, keep))   # 顶部夹取(p90 同款)
    vf = LUT[((nope & 0x80) | gf).long()] * sc
    vc = LUT[((nope & 0x80) | gc).long()] * sc
    lo, hi = torch.minimum(vf, vc), torch.maximum(vf, vc)
    delta = (hi - lo).clamp_min(0)
    theta = torch.where(delta > 0, (x - lo) / delta.clamp_min(1e-30), torch.zeros_like(x))
    theta = theta.clamp(0, 1)
    det_e = torch.where(delta > 0, torch.zeros_like(x), lo - x)
    return x, lo, hi, delta, theta, det_e


def u4_radius(qs, delta_j, theta, scale, delta_prob):
    """精确两点 MGF 半径(p90 C4 随机部),向量化到多查询。
    qs [Q,448] 未乘温度;返回 [Q,E]。双侧 = 两单侧 max,各付 δ/2。"""
    interior = (theta > 0) & (theta < 1)                       # [E,448]
    out = []
    for sgn in (1.0, -1.0):
        a = sgn * scale * qs[:, None, :] * delta_j[None]       # [Q,E,448]
        best = torch.full(a.shape[:2], float("inf"))
        for l in LAM:
            t1 = -l * theta[None] * a
            t2 = l * (1 - theta[None]) * a
            mx = torch.maximum(t1, t2)
            lse = mx + ((1 - theta[None]) * (t1 - mx).exp()
                        + theta[None] * (t2 - mx).exp()).log()
            psi = torch.where(interior[None], lse, torch.zeros_like(lse)).sum(-1)
            best = torch.minimum(best, (math.log(2 / delta_prob) + psi) / l)
        assert torch.isfinite(best).all(), "ψ 非有限 —— p90 已知陷阱重现"
        out.append(best)
    return torch.maximum(out[0], out[1])


def main():
    files = sorted(glob.glob(os.path.join(OUT, "wc_e1raw.rank*.pt")))
    assert len(files) == 8, f"应有 8 个 rank 文件,实得 {len(files)}"
    r0 = torch.load(files[0], map_location="cpu", weights_only=False)
    layers = sorted(int(k.split("|L")[1]) for k in r0 if k.startswith("swa_bytes|"))
    # q:全 rank 合并(rank 间 q 不同);条目:rank0(rank 间复制,已实测字节相等)
    qs_by_layer = {L: [] for L in layers}
    for f in files:
        d = r0 if f == files[0] else torch.load(f, map_location="cpu",
                                                weights_only=False)
        for L in layers:
            for r in d.get("q|L%d" % L, []):
                qs_by_layer[L].append((r["q"].float()[:, :448], float(r["scale"])))

    g = torch.Generator().manual_seed(7)
    pts_cert, pts_real = [], []          # (tv_cert, max_rel_dy) / (tv_real, rel_dy)
    per_m = {m: {"n_reads": 0, "n_vac": 0} for m in MASKS}
    n_viol, n_trials = 0, 0
    per_layer = {}
    for L in layers:
        recs = [r for r in r0["swa_bytes|L%d" % L]]
        X_parts = [decode_entries_m(r, 2)[0] for r in recs]    # x 与 m 无关
        X = torch.cat(X_parts)                                 # [E,448]
        E = X.shape[0]
        scale = qs_by_layer[L][0][1]
        Q = torch.cat([q for q, _ in qs_by_layer[L]])          # [Q,448]
        lay_stat = {"E": E, "Q": int(Q.shape[0])}
        for m in MASKS:
            parts = [decode_entries_m(r, m) for r in recs]
            dj = torch.cat([p[3] for p in parts])
            th = torch.cat([p[4] for p in parts])
            de = torch.cat([p[5] for p in parts])
            D_coef = scale * de                                # [E,448]
            # SR 实现(共享 across queries)
            lo = torch.cat([p[1] for p in parts])
            hi = torch.cat([p[2] for p in parts])
            up = (torch.rand(NDRAWS, E, 448, generator=g) < th[None]).float()
            e_real = torch.where(up.bool(), (hi - X)[None], (lo - X)[None])
            Xh = X[None] + e_real                              # [ND,E,448]
            lay_reads = lay_vac = 0
            for i0 in range(0, Q.shape[0], QCHUNK):
                q = Q[i0:i0 + QCHUNK]                          # [Qc,448]
                u4 = u4_radius(q, dj, th, scale, DELTA0 / E)   # [Qc,E]
                D = (q[:, None, :] * D_coef[None]).sum(-1)     # [Qc,E]
                osc = (D + u4).max(-1).values - (D - u4).min(-1).values
                tvc = torch.tanh(osc / 4)                      # [Qc]
                s = scale * (X @ q.T).T                        # [Qc,E]
                sh = scale * torch.einsum("dek,qk->qde", Xh, q)  # [Qc,ND,E]
                p = torch.softmax(s, -1)
                ph = torch.softmax(sh, -1)
                tvr = 0.5 * (ph - p[:, None]).abs().sum(-1)    # [Qc,ND]
                y = p @ X                                      # [Qc,448]
                yh = torch.einsum("qde,dek->qdk", ph, Xh)      # [Qc,ND,448]
                rel = ((yh - y[:, None]).norm(dim=-1)
                       / y.norm(dim=-1)[:, None].clamp_min(1e-12))  # [Qc,ND]
                # soundness 自检:随机部 |Δs_rand| 对 u4(δ 水平允许极少越界)
                dsr = scale * torch.einsum("dek,qk->qde", e_real - de[None], q)
                n_viol += int((dsr.abs() > u4[:, None, :] + 1e-9).sum())
                n_trials += dsr.numel()
                mx_rel = rel.max(-1).values                    # [Qc]
                for j in range(q.shape[0]):
                    pts_cert.append((float(tvc[j]), float(mx_rel[j]), m, L))
                per_m[m]["n_reads"] += int(q.shape[0])
                per_m[m]["n_vac"] += int((tvc >= VAC_TH).sum())
                lay_reads += int(q.shape[0])
                lay_vac += int((tvc >= VAC_TH).sum())
                keep = tvr.reshape(-1)
                relf = rel.reshape(-1)
                idx = torch.randperm(keep.shape[0], generator=g)[:256]
                pts_real.extend((float(keep[i]), float(relf[i])) for i in idx)
            lay_stat["m%d_vac_frac" % m] = lay_vac / max(lay_reads, 1)
        per_layer[L] = lay_stat

    exp_viol = n_trials * DELTA0 / 65.0                        # 量级参考
    vac = [(c, r) for c, r, m, L in pts_cert if c >= VAC_TH]
    if vac:
        basis = "certified(TV_cert≥%.2f)" % VAC_TH
        strat = vac
        rescued = {t: sum(1 for _, r in vac if r <= t) / len(vac) for t in TAUS}
    else:
        basis = "fallback_realized(TV_real≥%.1f)" % TVR_TH
        strat = [(t, r) for t, r in pts_real if t >= TVR_TH]
        rescued = {t: (sum(1 for _, r in strat if r <= t) / len(strat))
                   if strat else None for t in TAUS}
    rmain = rescued[TAU_MAIN]
    if rmain is None:
        verdict = "inconclusive_no_high_tv_reads"
    elif rmain >= ALIVE:
        verdict = "value_aware_alive"
    elif rmain <= DEAD:
        verdict = "value_aware_dead"
    else:
        verdict = "gray"

    def spearman(pairs):
        if len(pairs) < 10:
            return None
        a = torch.tensor([p[0] for p in pairs])
        b = torch.tensor([p[1] for p in pairs])
        ra = a.argsort().argsort().float()
        rb = b.argsort().argsort().float()
        va, vb = ra - ra.mean(), rb - rb.mean()
        return float((va * vb).sum() / (va.norm() * vb.norm()).clamp_min(1e-12))

    rep = {
        "what": "K0:TV 空洞/高 TV 读中真实输出误差小的占比 —— value-aware kill-shot",
        "kind": "shadow 离线(零 GPU);E1 同源字节,SR 掩位 m∈%s" % (MASKS,),
        "preregistered": {
            "primary": "P(max_d rel_dy ≤ 0.05 | TV_cert ≥ 0.99)",
            "fallback": "空洞集为空时改用 P(rel_dy ≤ τ | TV_real ≥ 0.5)(预注册)",
            "alive": "≥0.5", "dead": "≤0.2", "gray": "其间",
        },
        "verdict": verdict,
        "stratum_basis": basis,
        "summary": {
            "n_reads_total": sum(v["n_reads"] for v in per_m.values()),
            "n_vacuous_reads": len(vac),
            "n_stratum": len(strat),
            "rescued_frac": {("tau%.2f" % t): v for t, v in rescued.items()},
            "spearman_tvreal_reldy": spearman(pts_real),
            "spearman_tvcert_maxreldy": spearman([(c, r) for c, r, _, _ in pts_cert]),
            "soundness_viol": {"n": n_viol, "n_trials": n_trials,
                               "delta_expected_order": exp_viol},
        },
        "per_m": {str(m): v for m, v in per_m.items()},
        "per_layer": {str(k): v for k, v in per_layer.items()},
        "inputs": [{"path": os.path.relpath(f, EXP), "bytes": os.path.getsize(f),
                    "sha256_16": sha256(f)} for f in files],
        "freshness_argument": "字节+scale 写站点同批捕获,解码为字节的确定函数;"
                              "q 同批;全程不经 packed pool 槽位往返(G0-REVIEW.md)",
        "caliber": [
            "池=同层 rank0 条目合并(合成读,记录无 uid);score 仅 nope 448 维",
            "TV_cert=C2 osc+tanh(p90 胜出家族),u4 精确 MGF,δ=1e-6/E 联合",
            "rel_dy 在 MLA latent 域(X 即 value 载体);绝对值非 serving 声明",
            "soundness_viol 允许 δ 量级极少越界(概率证书语义,非 unsound)",
            "本实验只裁 TV↔输出误差的结构关系;G3 的 Spearman 提升判据"
            "需 RRD-2 四臂在真实读上重测",
        ],
        "manifest": stamp(run_id="rrd_k0", seed=7,
                          stack="local cpu offline (torch)"),
        "generated_by": "rrd_k0_output_visible.py",
    }
    dst = os.path.join(OUT, "rrd_k0_output_visible.json")
    json.dump(rep, open(dst, "w"), ensure_ascii=False, indent=1)
    print("verdict:", verdict, "| basis:", basis)
    print("rescued:", {("%.2f" % t): (round(v, 3) if v is not None else None)
                       for t, v in rescued.items()},
          "| n_vac=%d n_stratum=%d" % (len(vac), len(strat)))
    print("spearman real=%.3f cert=%.3f | viol %d/%d(δ 期望量级 %.1f)"
          % (rep["summary"]["spearman_tvreal_reldy"] or -9,
             rep["summary"]["spearman_tvcert_maxreldy"] or -9,
             n_viol, n_trials, exp_viol))


if __name__ == "__main__":
    main()
