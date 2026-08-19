# -*- coding: utf-8 -*-
"""W2-c-x:**换被认证量** —— 从"top-k 集合不变"改成"路由分布搬动的质量"。

动机(2026-08-09):集合不变是个**二值**且过强的性质。翻转恰恰发生在
s_(k)≈s_(k+1) 处,而那里两个专家的**路由权重几乎相等** ⟹ 换进换出搬动的质量
极小,输出几乎不动:
    ‖Δy‖ ≤ max_i‖E_i(x)‖ · ‖w′−w‖₁,     w = 路由权重(归一化后的门控分数)
‖w′−w‖₁/2 就是路由分布的 total variation,与 §5 的 served-output TV 同族。

本脚本只做**判别**,不出证书:先测实测路由 TV 的分布。若它不小,路三不成立,
不必再去构造界(判别先于修复)。若它小,再写 sound 上界。

权重口径(逐族,与实现对齐;**这是诊断量不是认证量**,口径写在产物里):
  · 有 per-expert bias(DeepSeek/GLM/Kimi/MiniMax):bias 只参与**选择**,
    权重 = 选中者的 fn(z) 归一化 —— 不含 bias。
  · 无 bias(Mixtral/Qwen3/gpt-oss/Llama-4):权重 = 选中 logit 的 softmax。
翻转比较必须在**同一支持集并集**上做,否则 ‖w′−w‖₁ 会漏掉换出的那部分。

    python experiments/w2cx_routing_tv.py <cap.pt> <out.json>
    python experiments/w2cx_routing_tv.py --smoke
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from provenance import stamp  # noqa: E402


def _weights(z, s, ids, has_bias, fn, torch):
    """选中集合上的路由权重,散布回 [n,E] 全向量(未选处为 0)。"""
    n, E = z.shape
    w = torch.zeros_like(z)
    if has_bias:                       # bias 只管选择,权重用不含 bias 的 fn(z)
        v = fn(z).gather(1, ids)
        v = v / v.sum(-1, keepdim=True).clamp_min(1e-30)
    else:                              # 无 bias:选中 logit 的 softmax
        v = torch.softmax(z.gather(1, ids), dim=-1)
    return w.scatter_(1, ids, v)


def routing_tv(x, w_, b, topk, scoring, bits, n_group=1, topk_group=1,
               wb=None):
    """返回 (tv_total, tv_set, tv_drift, flip)。

    **分解是本脚本的要点**:支持集不相交,故 ‖w′−w‖₁ 精确分成两块 ——
      tv_set   = 对称差上的质量(集合真的换了人);
      tv_drift = 交集上的权重漂移(同一批专家,权重变了)。
    现行证书只保护前者。若 tv_drift 与 tv_set 同量级甚至更大,那么"集合不变"
    这个被认证量**连输出都界不住** —— 它证明的东西不蕴含它想要的东西。
    """
    import torch
    from w2cv_biased_router_margin import SCORING, rtn_quant, _grouped_select
    fn, _L = SCORING[scoring]
    has_bias = not isinstance(b, float)
    z = (x @ w_.T).float()
    zq = (z.clone() if bits is None
          else (x @ rtn_quant(w_, bits).T).float())
    if wb is not None:
        z, zq = z + wb, zq + wb
    s, sq = fn(z) + b, fn(zq) + b
    if n_group > 1:
        ids, _, _ = _grouped_select(s, topk, n_group, topk_group)
        idsq, _, _ = _grouped_select(sq, topk, n_group, topk_group)
    else:
        ids = s.topk(topk, -1).indices.sort(-1).values
        idsq = sq.topk(topk, -1).indices.sort(-1).values
    W = _weights(z, s, ids, has_bias, fn, torch)
    Wq = _weights(zq, sq, idsq, has_bias, fn, torch)
    both = (W > 0) & (Wq > 0)                  # 交集(两边都选中)
    diff = (Wq - W).abs()
    zero = torch.zeros_like(diff)
    # **两块都直接算,不用相减**:换进换出的权重可以小到 1e-9,tv−tv_drift 会被
    # 抵消误差吃成 0,于是"有翻转却 tv_set=0"(2026-08-09 冒烟当场抓出)。
    tv_drift = 0.5 * torch.where(both, diff, zero).sum(-1)
    tv_set = 0.5 * torch.where(both, zero, diff).sum(-1)
    tv = tv_set + tv_drift
    flip = (ids != idsq).any(-1)
    return tv, tv_set, tv_drift, flip


def _q(t, torch, qs=(0.5, 0.95, 0.99)):
    return [float(torch.quantile(t, q)) for q in qs]


def _smoke():
    import torch
    fails = []
    from w2cv_biased_router_margin import SCORING
    # ① 管路:零扰动(bits=None ⟹ zq≡z)必须 TV 恒 0。
    #    注意**不能**断言"未翻转 ⟹ TV=0" —— 集合不变时权重仍随 logit 连续漂移,
    #    那是真实现象不是 bug(2026-08-09 首版判据写反,当场判红)。
    torch.manual_seed(5)
    x = torch.randn(500, 32)
    w_ = torch.randn(16, 32) * 0.05
    t0, s0, d0, f0 = routing_tv(x, w_, 0.0, 4, "_logit_domain_no_bias", None)
    if float(t0.abs().max()) > 1e-6 or bool(f0.any()):
        fails.append(f"①零扰动下 TV={float(t0.abs().max()):.2e}、flip={int(f0.sum())}"
                     " —— 权重散布/归一化写错了")
    # ② 分解恒等式 tv = tv_set + tv_drift,且 TV∈[0,1]
    tv, ts, td, flip = routing_tv(x, torch.randn(16, 32) * 2.0, 0.0, 4,
                                  "_logit_domain_no_bias", 2)
    if float((tv - ts - td).abs().max()) > 1e-5:
        fails.append("②tv ≠ tv_set + tv_drift —— 支持集划分写错了")
    if float(tv.min()) < -1e-9 or float(tv.max()) > 1.0 + 1e-6:
        fails.append(f"②TV 越界 [{float(tv.min()):.3f}, {float(tv.max()):.3f}]")
    if not flip.any():
        fails.append("②构造未产生任何翻转,该用例零区分度")
    elif float(ts[flip].min()) <= 0:
        fails.append("②存在翻转但 tv_set=0 —— 换出项被漏掉了")
    if float(ts[~flip].abs().max()) > 1e-6:
        fails.append("②未翻转却有 tv_set —— 对称差非空但 flip 判 False,两者不一致")
    # ③ 单调:扰动更狠 ⟹ TV 中位更大(证明它在测东西,不是常数)
    tv4, _, _, _ = routing_tv(x, torch.randn(16, 32) * 2.0, 0.0, 4,
                              "_logit_domain_no_bias", 4)
    if float(tv4.median()) >= float(tv.median()):
        fails.append(f"③INT4 的 TV 中位 {float(tv4.median()):.4f} 不小于 INT2 的 "
                     f"{float(tv.median()):.4f} —— 零区分度")
    # ④ 有 bias 支路:bias 只影响选择,不该进权重
    b = torch.randn(16) * 3.0
    tvb, _, _, _ = routing_tv(x, w_, b, 4, "sigmoid", 8)
    if float(tvb.max()) > 1.0 + 1e-6:
        fails.append("④有 bias 支路 TV 越界")
    if fails:
        print("ROUTING TV SMOKE FAILED:")
        for f in fails:
            print("   " + f)
        sys.exit(1)
    print("ROUTING TV SMOKE PASSED(零扰动⟹TV=0、分解恒等、翻⟹tv_set>0、"
          "位宽单调、bias 不进权重)")


def main():
    if "--smoke" in sys.argv:
        return _smoke()
    import torch
    cap_path, out_path = sys.argv[1], sys.argv[2]
    cap = torch.load(cap_path, map_location="cpu", weights_only=False)
    cfg = cap["cfg"]
    topk = int(cfg["num_experts_per_tok"])
    has_bias = any(v is not None for v in (cap.get("gate_bias") or {}).values())
    scoring = cfg.get("scoring_func") if has_bias else "_logit_domain_no_bias"
    ng, tg = int(cfg.get("n_group") or 1), int(cfg.get("topk_group") or 1)
    all_layers = sorted(cap["x_mlp"], key=int)
    nh = int(cfg.get("num_hash_layers") or 0)
    layers = [L for L in all_layers
              if not (int(L) < nh and cap.get("gate_bias", {}).get(L) is None)]
    tvs, sets, drifts, flips = [], [], [], []
    for L_ in layers:
        _b = (cap.get("gate_bias") or {}).get(L_)
        _wb = (cap.get("gate_linear_bias") or {}).get(L_)
        t, ts_, td_, f = routing_tv(
            cap["x_mlp"][L_].float(), cap["gates"][L_].float(),
            _b.float() if _b is not None else 0.0, topk, scoring, 4,
            n_group=ng, topk_group=tg,
            wb=_wb.float() if _wb is not None else None)
        tvs.append(t); sets.append(ts_); drifts.append(td_); flips.append(f)
    tv = torch.cat(tvs); flip = torch.cat(flips)
    tv_set = torch.cat(sets); tv_drift = torch.cat(drifts)
    ft = tv[flip]
    res = {"model": cfg.get("model", "?"), "topk": topk, "scoring": scoring,
           "n_routed_experts": int(cfg["n_routed_experts"]),
           "manifest": stamp(run_id="w2cx_%s" % cfg.get("model", "?"),
                             seed=None, stack="offline, zero-GPU"),
           "generated_by": "w2cx_routing_tv.py",
           "n_tokens": int(tv.numel()), "flip_rate": float(flip.float().mean()),
           "tv_all": {"median": _q(tv, torch)[0], "p95": _q(tv, torch)[1],
                      "p99": _q(tv, torch)[2], "max": float(tv.max())},
           "tv_flipped_only": ({"median": _q(ft, torch)[0],
                                "p95": _q(ft, torch)[1],
                                "p99": _q(ft, torch)[2],
                                "max": float(ft.max())} if ft.numel() else None),
           "frac_tv_gt": {f"{t}": float((tv > t).float().mean())
                          for t in (0.01, 0.02, 0.05, 0.10)},
           "tv_set": {"median": _q(tv_set, torch)[0],
                      "p95": _q(tv_set, torch)[1], "max": float(tv_set.max())},
           "tv_drift": {"median": _q(tv_drift, torch)[0],
                        "p95": _q(tv_drift, torch)[1],
                        "max": float(tv_drift.max())},
           "drift_share_of_total": float(tv_drift.sum() / tv.sum().clamp_min(1e-30)),
           # **证书通过者的条件分布**才是要害:集合不变 ⟹ TV 全部来自漂移,
           # 而现行证书对漂移不设任何界。全体中位混了翻转者,不能拿来说这句话。
           "tv_given_no_flip": ({"median": _q(tv[~flip], torch)[0],
                                 "p95": _q(tv[~flip], torch)[1],
                                 "p99": _q(tv[~flip], torch)[2],
                                 "max": float(tv[~flip].max())}
                                if int((~flip).sum()) else None),
           "caliber": "权重口径:有 bias ⟹ fn(z) 归一化(bias 只管选择);"
                      "无 bias ⟹ 选中 logit softmax。**诊断量,非认证量**"}
    a = res["tv_all"]
    print(f"{res['model']}: k={topk} E={res['n_routed_experts']} "
          f"n={res['n_tokens']:,} flip={100*res['flip_rate']:.1f}%")
    print(f"   路由 TV  中位 {a['median']:.5f}  p95 {a['p95']:.5f}  "
          f"p99 {a['p99']:.5f}  max {a['max']:.4f}")
    if res["tv_flipped_only"]:
        b_ = res["tv_flipped_only"]
        print(f"   仅翻转者 中位 {b_['median']:.5f}  p95 {b_['p95']:.5f}  "
              f"max {b_['max']:.4f}")
    print(f"   分解:  换人 tv_set 中位 {res['tv_set']['median']:.5f} "
          f"p95 {res['tv_set']['p95']:.5f} | 漂移 tv_drift 中位 "
          f"{res['tv_drift']['median']:.5f} p95 {res['tv_drift']['p95']:.5f}"
          f" | 漂移占总量 {100*res['drift_share_of_total']:.1f}%")
    if res["tv_given_no_flip"]:
        c = res["tv_given_no_flip"]
        print(f"   **证书通过者**(集合不变) TV 中位 {c['median']:.5f} "
              f"p95 {c['p95']:.5f} p99 {c['p99']:.5f} max {c['max']:.4f}"
              f" —— 证书对这块不设界")
    print("   TV>0.01/0.02/0.05/0.10 的占比: " +
          " / ".join(f"{100*v:.2f}%" for v in res["frac_tv_gt"].values()))
    json.dump(res, open(out_path, "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
