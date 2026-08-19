# -*- coding: utf-8 -*-
"""W2-a(离线,零 GPU):逐模块激活谱 + 留出 —— 激活椭球(W 线几何面)kill-shot。

输入:w1_act_capture 产物(Σ=XᵀX 按 (层,流,相,uid%2) 累加)。
对每 (层, 流, 相):
  谱 = eig(Σ_even + Σ_odd)(合并二阶矩,非中心);
  ρ90 = 前 r 特征值覆盖 90% 能量所需 r/d;
  留出 = Σ_even 的 top-r 特征子空间在 Σ_odd 上的能量占比
         tr(PᵀΣ_odd P)/tr(Σ_odd),r = round(0.0714·d)(K0' 的 32/448 同比例,
         平谱基线 ≈ 7.1%);
  对角对照 = diag(Σ) 的 ρ90(「为什么对角弱」义务,ASSESSMENT §2.2 同款)。

**预注册判读(先于看数写死,与 K0' 同构)**:
  主判据 = 各 (层,流) 在 prefill 相的 ρ90 中位数:
    ≤0.15 且 留出中位 ≥0.70 → concentrated:激活椭球有物理基础;
    ≥0.50 → flat:椭球面杀;
    其间或留出 <0.70 → gray:进下一级实验但带早退门。
  按流分判(x_attn / x_o / x_mlp 各自出 verdict)—— 流之间不互相救。
  样本量:Σ 的 n 由采集验收保证(每流每相 >0);n < 5d 的流标
  small_sample 警戒,verdict 降不升。

python3 experiments/rrd_w2a_module_spectrum.py <capture.pt> <out.json>
"""
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402

RHO_GO, RHO_KILL, HELD_PASS, R_FRAC = 0.15, 0.50, 0.70, 0.0714


def main():
    src, dst = sys.argv[1], sys.argv[2]
    blob = torch.load(src, map_location="cpu", weights_only=False)
    acc = blob["acc"]
    # key 形如 "(层, '流', '相', 奇偶)"
    keys = {}
    for k in acc:
        lay, stream, ph, par = eval(k)  # noqa: S307 —— 自产 repr,受控
        keys.setdefault((lay, stream, ph), {})[par] = acc[k]
    rows = []
    for (lay, stream, ph), parts in sorted(keys.items()):
        if 0 not in parts or 1 not in parts:
            continue
        s0 = parts[0]["sigma"].double()
        s1 = parts[1]["sigma"].double()
        d = s0.shape[0]
        n = parts[0]["n"] + parts[1]["n"]
        # fp16 落盘 + massive 激活的动态范围 → eigh 病态:double + 对称化 +
        # 按最大对角归一(谱形状不变,ρ90/能量比不受尺度影响);对角用 fp32 原值
        for s, p in ((s0, parts[0]), (s1, parts[1])):
            s[range(d), range(d)] = p["sigma_diag_fp32"].double()
            s.copy_(0.5 * (s + s.T))
        scale = max(float(s0.diagonal().max()), float(s1.diagonal().max()), 1e-30)
        s0 /= scale
        s1 /= scale                                     # 同尺度因子,合并谱无偏
        tot = s0 + s1
        ev = torch.linalg.eigvalsh(tot).flip(0).clamp_min(0)
        cum = torch.cumsum(ev, 0) / ev.sum().clamp_min(1e-30)
        rho90 = float((int((cum < 0.90).sum()) + 1) / d)
        dg = tot.diagonal().sort(descending=True).values.clamp_min(0)
        cumd = torch.cumsum(dg, 0) / dg.sum().clamp_min(1e-30)
        rho90_diag = float((int((cumd < 0.90).sum()) + 1) / d)
        r = max(1, round(R_FRAC * d))
        _, vec = torch.linalg.eigh(s0)
        P = vec[:, -r:]
        held = float((P.T @ s1 @ P).trace() / s1.trace().clamp_min(1e-30))
        rows.append({"layer": lay, "stream": stream, "phase": ph, "d": d, "n": n,
                     "small_sample": n < 5 * d, "rho90": rho90,
                     "rho90_diag": rho90_diag, "heldout_topr": held,
                     "r_frac": r / d})
    verdicts = {}
    for stream in sorted({r["stream"] for r in rows}):
        pf = [r for r in rows if r["stream"] == stream and r["phase"] == "prefill"]
        med = sorted(x["rho90"] for x in pf)[len(pf) // 2]
        hmed = sorted(x["heldout_topr"] for x in pf)[len(pf) // 2]
        if med <= RHO_GO and hmed >= HELD_PASS:
            v = "concentrated"
        elif med >= RHO_KILL:
            v = "flat"
        else:
            v = "gray"
        if any(x["small_sample"] for x in pf) and v == "concentrated":
            v = "gray"
        verdicts[stream] = {"verdict": v, "rho90_median": med,
                            "heldout_median": hmed,
                            "rho90_diag_median": sorted(
                                x["rho90_diag"] for x in pf)[len(pf) // 2]}
    rep = {"what": "W2-a:逐模块激活谱 + 留出(激活椭球 kill-shot)",
           "preregistered": {"go": f"ρ90≤{RHO_GO} 且留出≥{HELD_PASS}",
                             "kill": f"ρ90≥{RHO_KILL}", "r_frac": R_FRAC,
                             "note": "按流分判,不互救;small_sample 只降不升"},
           "verdicts": verdicts, "per_key": rows,
           "inputs": [{"path": os.path.relpath(src, EXP),
                       "manifest_of_input": blob.get("manifest")}],
           "caliber": ["Σ 合并奇偶后取谱;留出=偶Σ子空间在奇Σ上的能量占比",
                       "down_proj 输入未采(W1 口径);对角对照承接 Q3 义务"],
           "manifest": stamp(run_id="rrd_w2a", seed=None,
                             stack="local cpu offline (torch eigh)"),
           "generated_by": "rrd_w2a_module_spectrum.py"}
    json.dump(rep, open(dst, "w"), ensure_ascii=False, indent=1)
    print("W2A", {k: v["verdict"] for k, v in verdicts.items()})


if __name__ == "__main__":
    main()
