# -*- coding: utf-8 -*-
"""W2-c-v(离线,零 GPU):**bias 校正路由**下的 MoE router margin 证书。

为什么要新写一支(2026-08-08):rrd_w2c_router_margin.py 在 **logit 域**取
margin,理由是"softmax/sigmoid 单调不改序"。那对 DeepSeek-V2-Lite 成立
(softmax + greedy top-k,无 bias),但对本文真正跑主线的两个模型**不成立**:

    模型              scoring        选择方式            per-expert bias
    V2-Lite           softmax        greedy top-k        无
    DeepSeek-V4-Flash sqrtsoftplus   noaux_tc            **有**
    GLM-5.2           sigmoid        noaux_tc            **有**

`noaux_tc` 的选择量是 `s(z) + b`,`b` 逐专家不同 ⟹ **顺序不再由 z 决定**,
logit 域的 margin 与实际选择无关。这正是本文反复批判的"仪器前提与设计不符",
所以不复用旧脚本,而是按实际选择规则重写:

    z = x Wᵀ                       gate logits
    s = scoring(z) + b             **选择分数**(sglang topk.py 的 scores_for_choice)
    m = s_(k) − s_(k+1)            top-k 边界余量,取在选择分数域
    权重量化 W → Ŵ,ẑ = x Ŵᵀ,ε∞ = ‖ẑ − z‖∞
    |s(ẑ)−s(z)| ≤ L·ε∞             L = scoring 的 Lipschitz 常数
    证书:m > 2L·ε∞ ⟹ top-k 集不变

L 由 scoring 决定并在此写死(数值上界,不是估计):
    sigmoid       L = 1/4        = 0.25
    sqrtsoftplus  L = 0.319087   (数值极大值 0.319086343169 **向上**取整,z*≈0.9214)
    softmax       无逐坐标 L(耦合),仅在无 bias 时退化为 logit 域比较

**soundness 自检**(定理,违约必须为 0):m > 2L·ε∞ 的 token 不得实际翻转。
违约 > 0 即实现或推导有误,裁决作废 —— 与旧支同一纪律。

用法:
    python3 experiments/w2cv_biased_router_margin.py <capture.pt> <out.json>
capture.pt 需含 {"x_mlp": {layer: [n,H]}, "gates": {layer: [E,H]},
                "gate_bias": {layer: [E]}, "cfg": {...}}
"""
import json
import os
import sys

import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from provenance import stamp  # noqa: E402

#: scoring 函数 → (实现, Lipschitz 上界)。**L 是数值上界不是估计**:
#: sigmoid 的 1/4 是解析极大;sqrtsoftplus 的 0.319087 由三分搜索定 z*=0.9214225、
#: 真值 0.319086343169476 **向上**取整到 6 位。2026-08-13 外部评审 P0-1:此前写
#: 0.319086,比真值小 3.4e-7 —— **不是上界**。相对量级 1e-6,但 soundness 是二值:
#: L 偏小则 m > 2Lε 可能放行真会翻的 token。取整方向现由 tests/test_lipschitz_sound
#: 保证,不再靠"作者当时记得向上取";它同时禁止过松(>1% 即判红)。旧注里"网格取极大
#: 后向上取整"这句在四百万点网格上也不成立 —— 网格极大值本身就低于真极大。
#: 向上取整到 6 位 —— 用它乘 ε∞ 得到的是 sound 上界。
SCORING = {
    "sigmoid": (torch.sigmoid, 0.25),
    "sqrtsoftplus": (lambda z: torch.sqrt(torch.nn.functional.softplus(z)),
                     0.319087),
    # 无 bias 时选择完全由 z 的序决定(任何单调 scoring 都不改序),margin 取在
    # **logit 域**、L=1 —— 这与旧支 rrd_w2c_router_margin 的口径**逐字相同**,
    # 于是 Qwen3/V2-Lite 这类 greedy 模型与 V4/GLM 这类 bias 校正模型可以放在
    # 同一张表里比。判据是"有没有 bias",不是"哪个模型"。
    "_logit_domain_no_bias": (lambda z: z, 1.0),
}

#: 预注册判读(先于数据写死),与旧支同一口径以便跨模型比较。
PREREG = {
    "binding": "P(m ≤ 2Lε∞):证书需介入的 token 占比",
    "alive": "0.005 ≤ binding ≤ 0.5 —— 证书有时介入、多数放行",
    "trivially_safe": "binding < 0.005 且实际翻转 < 0.001 —— 该档无用武之地",
    "too_small": "binding > 0.5 —— 证书拒绝过半流量,不可用为门控",
    "soundness": "m > 2Lε∞ 却实际翻转的 token 数必须为 0",
}


def rtn_quant(w, bits, group=32):
    """group-32 absmax RTN,与旧支同一量化口径(跨模型可比的前提)。"""
    E, H = w.shape
    n = H // group * group
    q = w[:, :n].reshape(E, -1, group)
    qmax = 2 ** (bits - 1) - 1
    scale = q.abs().amax(-1, keepdim=True).clamp_min(1e-12) / qmax
    deq = torch.round(q / scale).clamp(-qmax - 1, qmax) * scale
    out = w.clone()
    out[:, :n] = deq.reshape(E, n)
    return out


def cert_pass(m_group, m_expert, L, eps, grouped):
    """证书判据的**单一真理源**:实验与守卫共用同一个函数。

    分组时两段都要稳:组分数是组内 top-2 之和 ⟹ 逐组扰动 ≤ 2Lε,两组之差 ⟹
    **4Lε**;专家阶段是单项之差 ⟹ **2Lε**。
    (守卫若自己重抄一遍公式,测的就不是实验用的那个 —— 2026-08-08 变异检验
    当场发现:改了这里的常数,守卫毫无反应。)
    """
    ok = m_expert > 2 * L * eps
    if grouped:
        ok = ok & (m_group > 4 * L * eps)
    return ok


def _grouped_select(s, topk, n_group, topk_group):
    """复刻 sglang 的 biased_grouped_topk:组分数=组内 top-2 之和 → 选组 → 组内 top-k。

    返回 (topk_ids 排序后, 组阶段 margin, 专家阶段 margin)。
    """
    n, E = s.shape
    gs = s.view(n, n_group, -1).topk(2, dim=-1)[0].sum(-1)      # [n, n_group]
    gtop = gs.topk(min(topk_group + 1, n_group), dim=-1)
    gidx = gtop.indices[:, :topk_group]
    # 组阶段 margin:第 topk_group 名组分 − 第 topk_group+1 名组分
    m_g = (gtop.values[:, topk_group - 1] - gtop.values[:, topk_group]
           if n_group > topk_group
           else torch.full((n,), float("inf")))
    mask = torch.zeros_like(gs).scatter_(1, gidx, 1.0)
    smask = mask.unsqueeze(-1).expand(n, n_group, E // n_group).reshape(n, E)
    tmp = s.masked_fill(~smask.bool(), float("-inf"))
    t = tmp.topk(topk + 1, dim=-1)
    return t.indices[:, :topk].sort(-1).values, m_g, t.values[:, topk - 1] - t.values[:, topk]


def analyze(x, w, b, topk, scoring, bits, n_group=1, topk_group=1, wb=None):
    """返回 (binding, flip, soundness_viol, n)。全部在**选择分数域**。

    分组路由(n_group>1,DeepSeek-V3 系)是**两段**选择,两段都稳才算证书放行:
      组阶段:组分数是组内 top-2 之和 ⟹ 逐组扰动 ≤ 2Lε(和式的 ℓ∞ Lipschitz),
             两组之差 ⟹ 4Lε,故要求 m_group > 4Lε;
      专家阶段:被选组内的 s_(k) − s_(k+1) > 2Lε。
    平铺 top-k 的旧式(只查后者)会**高估**稳定性 —— 组选错了整个候选集就变了。
    """
    fn, L = SCORING[scoring]
    # **线性层 bias 直接进 logit**(gpt-oss 的 router.bias)。漏掉它 z 本身就错,
    # 而不是只影响选择分数 —— 2026-08-08 第三种 bias 形态。
    z = (x @ w.T).float()
    zq = (x @ rtn_quant(w, bits).T).float()
    if wb is not None:
        z, zq = z + wb, zq + wb
    eps = (zq - z).abs().amax(-1)
    s, sq = fn(z) + b, fn(zq) + b
    if n_group > 1:
        ids, m_g, m_e = _grouped_select(s, topk, n_group, topk_group)
        idsq, _, _ = _grouped_select(sq, topk, n_group, topk_group)
        cert = cert_pass(m_g, m_e, L, eps, grouped=True)
        flip = (ids != idsq).any(-1)
    else:
        top = s.topk(topk + 1, dim=-1).values
        cert = cert_pass(None, top[:, topk - 1] - top[:, topk], L, eps,
                         grouped=False)
        flip = (s.topk(topk, -1).indices.sort(-1).values
                != sq.topk(topk, -1).indices.sort(-1).values).any(-1)
    return (float((~cert).float().mean()), float(flip.float().mean()),
            int((cert & flip).sum()), int(x.shape[0]))


def main():
    cap_path, out_path = sys.argv[1], sys.argv[2]
    cap = torch.load(cap_path, map_location="cpu", weights_only=False)
    cfg = cap["cfg"]
    topk = int(cfg["num_experts_per_tok"])
    # **口径由"有没有 bias"决定,不由模型名决定**:有 bias ⟹ 选择分数域 + 该
    # scoring 的 L;无 bias ⟹ logit 域 + L=1(单调不改序,退化为旧支口径)。
    has_bias = any(v is not None for v in (cap.get("gate_bias") or {}).values())
    scoring = cfg.get("scoring_func") if has_bias else "_logit_domain_no_bias"
    assert scoring in SCORING, (
        f"scoring={scoring} 未登记 Lipschitz 常数 —— 不许用别的常数凑")
    # **hash 路由层的判别**(2026-08-08 两次修正):
    #   首版按"该层无 bias"判 hash —— 那只在 DeepSeek-V4 上成立。Qwen3-MoE
    #   **全部层都无 bias 却都是 score-routed**(softmax greedy),一换模型就错。
    #   正确判别 = config 的 num_hash_layers(hash 层永远是**前** n 层)且该层
    #   确无 bias。两个条件都要,单看任一个都会误判。
    all_layers = sorted(cap["x_mlp"], key=int)
    n_hash_cfg = int(cfg.get("num_hash_layers") or 0)
    layers = [L for L in all_layers
              if not (int(L) < n_hash_cfg
                      and cap.get("gate_bias", {}).get(L) is None)]
    n_hash = len(all_layers) - len(layers)
    assert layers, "无 score-routed 层 —— 该模型整段 hash 路由?margin 证书无定义"
    per_bits = {}
    for bits in (4, 3, 2):
        acc = []
        for L_ in layers:
            x = cap["x_mlp"][L_].float()
            w = cap["gates"][L_].float()
            _b = (cap.get("gate_bias") or {}).get(L_)
            b = _b.float() if _b is not None else 0.0
            _wb = (cap.get("gate_linear_bias") or {}).get(L_)
            acc.append(analyze(x, w, b, topk, scoring, bits,
                               int(cfg.get("n_group") or 1),
                               int(cfg.get("topk_group") or 1),
                               wb=(_wb.float() if _wb is not None else None)))
        n_tot = sum(a[3] for a in acc)
        per_bits[f"int{bits}"] = {
            "binding": sum(a[0] * a[3] for a in acc) / n_tot,
            "flip": sum(a[1] * a[3] for a in acc) / n_tot,
            "soundness_viol": sum(a[2] for a in acc),
            "n_tokens": n_tot, "n_layers": len(acc),
        }
    i4 = per_bits["int4"]
    verdict = ("INVALID_soundness" if any(v["soundness_viol"] for v in per_bits.values())
               else "margin_too_small" if i4["binding"] > 0.5
               else "margin_certificate_alive" if i4["binding"] >= 0.005
               else "int4_trivially_safe")
    rep = {
        "what": f"{cfg.get('model','?')} bias 校正路由下的 margin 证书(选择分数域)",
        "n_layers_scored": len(layers),
        "n_layers_hash_excluded": n_hash,
        "verdict": verdict,
        "model": cfg.get("model"),
        "scoring_func": cfg.get("scoring_func"),
        "margin_domain": "selection_score" if has_bias else "logit",
        "has_per_expert_bias": has_bias,
        "lipschitz_L": SCORING[scoring][1],
        "n_routed_experts": cfg.get("n_routed_experts"), "topk": topk,
        "n_group": int(cfg.get("n_group") or 1),
        "topk_group": int(cfg.get("topk_group") or 1),
        "routing_mode": ("grouped" if int(cfg.get("n_group") or 1) > 1
                         else "flat"),
        "per_bits": per_bits,
        "preregistered": PREREG,
        "caliber": [
            ("margin 取在**选择分数域** s(z)+b —— bias 逐专家不同,logit 域的序"
             "与实际选择无关" if has_bias else
             "该模型**无 per-expert bias**,选择完全由 z 的序决定(单调 scoring "
             "不改序)⟹ margin 取在 **logit 域**、L=1,与旧支 "
             "rrd_w2c_router_margin 口径逐字相同,故两类模型可同表比较"),
            f"scoring={scoring},Lipschitz L={SCORING[scoring][1]} 为**数值上界**;"
            "证书条件 m > 2Lε∞ 因此是 sound 的",
            "量化口径 group-32 absmax RTN,与旧支一致 ⟹ 跨模型可比",
            "x_mlp 为真实前向捕获的 MoE gate 输入(非合成),权重与激活同源",
            (f"**剔除了 {n_hash} 个 hash 路由层**(HashTopK:专家由 token id 经 "
             "tid2eid 决定,不由分数 top-k 选 ⟹ margin 证书对它们无定义);"
             "判别用'该层有无 e_score_correction_bias',不按层号猜"
             if n_hash else "全部层均为 score-routed"),
        ],
        "manifest": stamp(run_id=f"w2cv_{cfg.get('model','?')}", seed=None,
                          stack="offline, zero-GPU"),
        "generated_by": "w2cv_biased_router_margin.py",
    }
    json.dump(rep, open(out_path, "w"), ensure_ascii=False, indent=1)
    print(f"{cfg.get('model')}: verdict={verdict} | scoring={scoring} L={SCORING[scoring][1]}")
    for k, v in per_bits.items():
        print(f"  {k}: binding={v['binding']:.4f} flip={v['flip']:.4f} "
              f"soundness_viol={v['soundness_viol']} n={v['n_tokens']}")


if __name__ == "__main__":
    main()
