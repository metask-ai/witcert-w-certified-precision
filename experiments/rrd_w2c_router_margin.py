# -*- coding: utf-8 -*-
"""W2-c(离线,零 GPU):MoE router margin 覆盖率 —— W 线支柱 B 的 kill-shot。

输入:w1_act_capture 的 router 模式产物(x_mlp 原始行 + 逐层 gate 权重 + moe 配置)。
对每 MoE 层每 token:
  z = x @ Wᵀ(fp32,gate 线性部;softmax/sigmoid 单调不改序,margin 取 logit 域)
  m = z_(k) − z_(k+1)(top-k 边界余量,k = num_experts_per_tok)
  扰动:对 W 做 group-32 absmax RTN 的 INT{4,3,2} 量化 → ẑ,ε∞ = ‖ẑ−z‖∞
  证书判据:m > 2ε∞ ⇒ top-k 集不变(S1 严格 gap 版);
  实际翻转:top-k(ẑ) ≠ top-k(z)。

**预注册判读(先于看数写死)** —— 以 INT4 为主档:
  binding = P(m ≤ 2ε∞):证书需要介入(fallback/提精度)的 token 占比
    0.005 ≤ binding ≤ 0.5 → margin_certificate_alive:证书有时介入、多数放行,
                             恰是在线判据的用武之地;
    binding < 0.005 且实际翻转率 < 0.001 → int4_trivially_safe:INT4 档无用武
        之地 —— 看 INT3/INT2 档同判据,若存在档位落入 alive 区间则
        alive_at_lower_bits,全部档位仍平凡 → 杀;
    binding > 0.5 → margin_too_small:证书拒绝过半流量,不可用为门控 —— 杀。
  soundness 自检(定理,违约=0 必须成立):m > 2ε∞ 的 token 不得实际翻转;
    违约 >0 即实现 bug,裁决作废。
  附:prefill vs decode 分相报 binding(相位差异是 P/D 分离精度计划的依据)。

python3 experiments/rrd_w2c_router_margin.py <capture.pt> <out.json>
"""
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402

BITS = (4, 3, 2)
GROUP = 32
ALIVE_LO, ALIVE_HI, FLIP_TRIVIAL = 0.005, 0.5, 0.001


def quant_rtn(w, bits, group=GROUP):
    """group-wise absmax RTN(按行内分组;族标准做法)。w: [E, d]"""
    E, d = w.shape
    pad = (group - d % group) % group
    x = torch.nn.functional.pad(w, (0, pad)).view(E, -1, group)
    qmax = 2 ** (bits - 1) - 1
    s = x.abs().amax(-1, keepdim=True).clamp_min(1e-12) / qmax
    xq = torch.round(x / s).clamp(-qmax - 1, qmax) * s
    return xq.view(E, -1)[:, :d]


def main():
    src, dst = sys.argv[1], sys.argv[2]
    blob = torch.load(src, map_location="cpu", weights_only=False)
    gates, raw = blob["gates"], blob["raw"]
    k = int(blob["moe_config"].get("num_experts_per_tok", 6))
    per_layer, agg = [], {b: {ph: {"n": 0, "bind": 0, "flip": 0, "viol": 0}
                              for ph in ("prefill", "decode")} for b in BITS}
    for key, v in raw.items():
        lay, stream, ph = eval(key)  # noqa: S307 —— 自产 repr
        if stream != "x_mlp" or lay not in gates or v["rows"] is None:
            continue
        x = v["rows"].float()
        W = gates[lay].float()
        z = x @ W.T                                     # [N, E]
        top = z.topk(k + 1, dim=-1).values
        m = top[:, k - 1] - top[:, k]                   # [N]
        idx = z.topk(k, dim=-1).indices.sort(-1).values
        st = {"layer": lay, "phase": ph, "n": int(x.shape[0]),
              "margin_median": float(m.median()), "margin_p05": float(m.quantile(0.05))}
        for b in BITS:
            zh = x @ quant_rtn(W, b).T
            eps = (zh - z).abs().amax(-1)               # [N] ε∞
            bind = m <= 2 * eps
            idxh = zh.topk(k, dim=-1).indices.sort(-1).values
            flip = (idxh != idx).any(-1)
            viol = int((flip & ~bind).sum())            # 定理违约(必须 0)
            st[f"int{b}"] = {"binding_frac": float(bind.float().mean()),
                             "flip_frac": float(flip.float().mean()),
                             "eps_median": float(eps.median()),
                             "soundness_viol": viol}
            a = agg[b][ph]
            a["n"] += int(x.shape[0]); a["bind"] += int(bind.sum())
            a["flip"] += int(flip.sum()); a["viol"] += viol
        per_layer.append(st)
    assert per_layer, "无 (x_mlp × gate) 交集 —— 采集或发现逻辑失配"
    summary, verdict = {}, None
    for b in BITS:
        for ph in ("prefill", "decode"):
            a = agg[b][ph]
            summary[f"int{b}_{ph}"] = {
                "binding": a["bind"] / max(a["n"], 1),
                "flip": a["flip"] / max(a["n"], 1),
                "soundness_viol": a["viol"], "n": a["n"]}
    n_viol = sum(agg[b][ph]["viol"] for b in BITS for ph in ("prefill", "decode"))
    assert n_viol == 0, f"S1 定理违约 {n_viol} 次 —— 实现 bug,裁决作废"

    def classify(b):
        n = sum(agg[b][ph]["n"] for ph in ("prefill", "decode"))
        bind = sum(agg[b][ph]["bind"] for ph in ("prefill", "decode")) / max(n, 1)
        flip = sum(agg[b][ph]["flip"] for ph in ("prefill", "decode")) / max(n, 1)
        if ALIVE_LO <= bind <= ALIVE_HI:
            return "alive", bind, flip
        if bind < ALIVE_LO and flip < FLIP_TRIVIAL:
            return "trivial", bind, flip
        if bind > ALIVE_HI:
            return "too_small", bind, flip
        return "gray", bind, flip

    cls = {b: classify(b) for b in BITS}
    if cls[4][0] == "alive":
        verdict = "margin_certificate_alive"
    elif cls[4][0] == "trivial":
        verdict = ("alive_at_lower_bits"
                   if any(cls[b][0] == "alive" for b in (3, 2))
                   else "margin_certificate_dead_trivial")
    elif cls[4][0] == "too_small":
        verdict = "margin_certificate_dead_too_small"
    else:
        verdict = "gray"
    rep = {"what": "W2-c:MoE router margin 覆盖率(支柱 B kill-shot)",
           "preregistered": {
               "alive": f"INT4 binding∈[{ALIVE_LO},{ALIVE_HI}]",
               "trivial": f"binding<{ALIVE_LO} 且 flip<{FLIP_TRIVIAL} → 看 INT3/2",
               "too_small": f"binding>{ALIVE_HI}",
               "soundness": "m>2ε∞ 不得翻转,违约=0 硬断言"},
           "verdict": verdict,
           "per_bits_class": {f"int{b}": {"class": c[0], "binding": c[1],
                                          "flip": c[2]} for b, c in cls.items()},
           "summary": summary, "per_layer": per_layer,
           "topk": k, "moe_config": blob["moe_config"],
           "inputs": [{"path": os.path.relpath(src, EXP),
                       "manifest_of_input": blob.get("manifest")}],
           "caliber": [
               "margin/ε 在 gate 线性 logit 域(softmax/sigmoid 单调不改序)",
               "只量化 gate 权重本身的扰动;上游层量化传入的 Δx 不在本发覆盖"
               "(那是支柱 A 的账,W2-c 只裁 margin 的量级与可用性)",
               "RTN group-32 absmax;V2-Lite 27 层代理,非生产 DSV4 口径",
               "GEMQ 41.31% 变化率是 1.5-bit 全模型口径,与本发 gate-only 不可直比"],
           "manifest": stamp(run_id="rrd_w2c", seed=None,
                             stack="local cpu offline (torch)"),
           "generated_by": "rrd_w2c_router_margin.py"}
    json.dump(rep, open(dst, "w"), ensure_ascii=False, indent=1)
    print("W2C verdict:", verdict)
    for b in BITS:
        print(f"  int{b}: class={cls[b][0]} binding={cls[b][1]:.4f} flip={cls[b][2]:.5f}")


if __name__ == "__main__":
    main()
