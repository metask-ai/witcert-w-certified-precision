# -*- coding: utf-8 -*-
"""K0-R(离线,零 GPU):真实请求池上的 TV vs ‖Δy‖ —— K0 合成池疑点的复核轮。

K0(rrd_k0_output_visible)判 value_aware_dead,其口径唯一疑点 = 合成池
(65 条混记录、无 rope、跨请求 q×池)。本轮全部修复:
  池   = w1_dsv4pool run-4 的 centry_c4,按 (layer, uid) 分组 —— 同请求条目;
  读   = 同 uid 的真实 q(uid 配对,443/512 → 全 512 维打分,rope 齐);
  量化 = 生产族 Hadamard + tile-absmax RTN,INT{6,4,3} 档,只作用前 448 维
         (nope;rope 段保精确,生产同口径);
  TV_real = ½‖softmax(s)−softmax(ŝ)‖₁;rel_dy = ‖p̂ᵀX̂−pᵀX‖/‖pᵀX‖(latent 域)。

**预注册判读(与 K0 回退层完全同构,先于看数写死)**:
  层集 = {TV_real ≥ 0.5 的 (读,档) 点};τ_y = 0.05 主(附 0.02/0.10)
    rescued ≥ 0.5 → value_aware_revived(K0 结论被真实池推翻 —— 重开);
    rescued ≤ 0.2 → value_aware_dead_confirmed(永久结案);
    其间 → gray。
  层集为空(真实池上 TV 拉不高)→ inconclusive_no_high_tv:降一档位宽重扫,
    仍空则记「该量化族在真实池上 TV 不过 0.5」为独立观测,K0 原判维持。
  附:Spearman(TV_real, rel_dy) —— 与 K0 的 0.872 对拍。
  最小池深:|pool| < 64 的 (layer,uid) 组丢弃(池太浅无 softmax 意义);
  丢弃数入报告。

python3 experiments/rrd_k0_realpool.py
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

NOPE, TILE = 448, 64
BITS = (6, 4, 3)
TV_TH, TAUS, TAU_MAIN = 0.5, (0.02, 0.05, 0.10), 0.05
ALIVE, DEAD = 0.5, 0.2
MIN_POOL = 64
SCALE = 512 ** -0.5


def had(n):
    H = torch.tensor([[1.0]])
    while H.shape[0] < n:
        H = torch.cat([torch.cat([H, H], 1), torch.cat([H, -H], 1)], 0)
    return H / math.sqrt(n)


_H = had(TILE)


def quant_bits(x, bits):
    """q3 同族:Hadamard + tile absmax + fp8 scale 舍入 + RTN。x: [N,448]"""
    qmax = 2 ** (bits - 1) - 1
    y = x.view(-1, NOPE // TILE, TILE) @ _H.T
    s = (y.abs().amax(-1, keepdim=True).clamp_min(1e-12) / qmax)
    s = s.to(torch.float8_e4m3fn).float()
    yq = torch.round(y / s).clamp(-qmax - 1, qmax) * s
    return (yq @ _H).view(-1, NOPE)


def sha256_16(path, cap=1 << 30):
    h, n = hashlib.sha256(), 0
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
            n += len(blk)
            if n >= cap:
                return h.hexdigest()[:16] + "-trunc"
    return h.hexdigest()[:16]


def main():
    files = sorted(glob.glob(os.path.join(OUT, "w1_wc_w1pool_raw.rank*.pt")))
    assert files, "无 run-4 产物"
    pools, qs = {}, {}          # (layer, uid) -> rows
    for f in files:
        raw = torch.load(f, map_location="cpu", weights_only=False)
        for k, recs in raw.items():
            if k.startswith("centry_c4|") and f == files[0]:   # 条目 rank 间复制
                L = int(k.split("|L")[1])
                for r in recs:
                    pools.setdefault((L, int(r["uid"])), []).append(
                        r["x"].float())
            elif k.startswith("q|"):                           # q 逐 rank 不同,合并
                L = int(k.split("|L")[1])
                for r in recs:
                    qs.setdefault((L, int(r["uid"])), []).append(
                        r["q"].float() * float(r["scale"]))
    pts, dropped, groups = [], 0, 0
    tvs_all, dys_all = [], []
    for key in sorted(set(pools) & set(qs)):
        X = torch.cat(pools[key])                              # [E,512]
        Q = torch.cat(qs[key])                                 # [Nq,512]
        if X.shape[0] < MIN_POOL:
            dropped += 1
            continue
        groups += 1
        for b in BITS:
            Xh = X.clone()
            Xh[:, :NOPE] = quant_bits(X[:, :NOPE], b)
            s = SCALE * (Q @ X.T)                              # [Nq,E]
            sh = SCALE * (Q @ Xh.T)
            p, ph = torch.softmax(s, -1), torch.softmax(sh, -1)
            tv = 0.5 * (ph - p).abs().sum(-1)
            y, yh = p @ X, ph @ Xh
            rel = (yh - y).norm(dim=-1) / y.norm(dim=-1).clamp_min(1e-12)
            tvs_all.append(tv)
            dys_all.append(rel)
            m = tv >= TV_TH
            pts.extend((float(t), float(r)) for t, r in
                       zip(tv[m].tolist(), rel[m].tolist()))
    tvc = torch.cat(tvs_all)
    dyc = torch.cat(dys_all)
    ra = tvc.argsort().argsort().float()
    rb = dyc.argsort().argsort().float()
    va, vb = ra - ra.mean(), rb - rb.mean()
    spear = float((va * vb).sum() / (va.norm() * vb.norm()).clamp_min(1e-12))
    if pts:
        rescued = {t: sum(1 for _, r in pts if r <= t) / len(pts) for t in TAUS}
        rmain = rescued[TAU_MAIN]
        if rmain >= ALIVE:
            verdict = "value_aware_revived"
        elif rmain <= DEAD:
            verdict = "value_aware_dead_confirmed"
        else:
            verdict = "gray"
    else:
        rescued, verdict = {}, "inconclusive_no_high_tv"
    n_uids = len({u for (_, u) in set(pools) & set(qs)})
    # 非退化硬断言(frozen_key_inadequate;run-2/4 的 uid 冻结即在此判死)
    assert n_uids >= 2, f"uid 基数 {n_uids} < 2 —— 键退化,逐请求结论不成立"
    rep = {
        "what": "K0-R:真实请求池 TV vs ‖Δy‖(K0 合成池疑点复核)",
        "snapshot": {"realpool_reads": {
            "key_dims": ["layer", "uid"],
            "key_card": {"uid": n_uids,
                         "layer": len({L for (L, _) in pools})},
        }},
        "preregistered": {
            "stratum": f"TV_real≥{TV_TH}", "tau_main": TAU_MAIN,
            "revived": f"rescued≥{ALIVE}", "dead_confirmed": f"rescued≤{DEAD}",
            "min_pool": MIN_POOL},
        "verdict": verdict,
        "summary": {
            "n_groups_used": groups, "n_groups_dropped_shallow": dropped,
            "n_stratum_points": len(pts),
            "rescued_frac": {("tau%.2f" % t): v for t, v in rescued.items()},
            "spearman_tv_reldy_all": spear,
            "n_points_all": int(tvc.numel()),
            "tv_p50_int4": None,
        },
        "caliber": [
            "池=同请求 (layer,uid) 条目组(rank0,rank 间复制);q 同 uid 配对,四 rank 合并",
            "打分全 512 维(rope 齐);量化只动前 448 维(生产同口径)",
            "K0 对拍参照:合成池 Spearman=0.872,rescued=0.0@τ0.10",
            "uid 语义=身份状态机分组(radix-on 口径),非逐 token 精确请求边界",
        ],
        "inputs": [{"path": os.path.relpath(f, EXP), "bytes": os.path.getsize(f),
                    "sha256_16": sha256_16(f)} for f in files],
        "manifest": stamp(run_id="rrd_k0_realpool", seed=None,
                          stack="local cpu offline (torch)"),
        "generated_by": "rrd_k0_realpool.py",
    }
    dst = os.path.join(OUT, "rrd_k0_realpool.json")
    json.dump(rep, open(dst, "w"), ensure_ascii=False, indent=1)
    print("K0R verdict:", verdict, "| groups=", groups, "dropped=", dropped,
          "| stratum n=", len(pts))
    print("rescued:", {("%.2f" % t): round(v, 3) for t, v in rescued.items()},
          "| spearman(all)=%.3f" % spear)


if __name__ == "__main__":
    main()
