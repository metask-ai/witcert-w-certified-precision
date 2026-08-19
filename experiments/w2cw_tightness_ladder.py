# -*- coding: utf-8 -*-
"""W2-c-w:路由 margin 证书的**保守性分解**(离线、零 GPU)。

问题:跨族扫描给出的"证书拒掉 99.8% 流量"是**物理**还是**仪器**?
实测翻转率只有 47%,即一半 token 其实不翻。那 200-800 倍的差距,有多少能靠
把界写紧拿回来,有多少是最坏情形假设的本质代价?

四档阶梯,每档只放松**一个**假设,前三档全部仍是确定性最坏情形界(主张类型不变):

  T0  现状          d_i = L_global · ε∞      ε∞ = 逐 token 对**全体**专家取 max
  T1  逐专家 ε      d_i = L_global · |Δz_i|  只用该专家自己的误差幅度
  T2  局部 Lipschitz d_i = L_i(z_i,|Δz_i|) · |Δz_i|
                                             L_i = scoring 导数在 [z_i±|Δz_i|] 上的 sup
  T3  oracle        真实是否翻转             任何路由证书的上限(符号已知)

统一判据(比"m > 2Lε"更一般,且 T0 会**退化成它** —— 这是本脚本的自检):
    专家阶段: min_{i∈选中}(s_i − d_i) > max_{j∉选中}(s_j + d_j)
    组阶段(分组路由): min_{G∈选中}(g_G − D_G) > max_{H∉选中}(g_H + D_H),
                      D_G = 组内 d_i 的**前二之和**(组分数是组内 top-2 之和)
d_i ≡ Lε 时前者化为 m_expert > 2Lε、后者化为 m_group > 4Lε,即现行判据。
**T0 必须逐模型复现已发表的 binding**,不复现就是判据写错了,不是发现了什么。

用法:
    python experiments/w2cw_tightness_ladder.py <cap.pt> <out.json> [--expect-binding X]
自检:
    python experiments/w2cw_tightness_ladder.py --smoke
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from provenance import stamp  # noqa: E402


def _local_L(scoring, z, e, torch):
    """scoring 的导数在区间 [z-e, z+e] 上的上确界(逐元素)。

    两个 scoring 的导数都是**单峰**的(sigmoid 峰在 0,sqrtsoftplus 峰在
    z*≈0.921) ⟹ 区间上的 sup 取在 clip(峰位, z-e, z+e)。单峰性在 smoke 里
    用网格验过,不是假设。
    """
    # 峰位真值由三分搜索定(0.9214225);此前写 0.9209,当区间含真峰时 clip 取到
    # 错误点 ⟹ 区间上确界被低估(同 P0-1 一族,tests/test_lipschitz_sound 现在挡住)
    peak = {"sigmoid": 0.0, "sqrtsoftplus": 0.9214225}[scoring]
    t = torch.clamp(torch.full_like(z, peak), z - e, z + e)
    if scoring == "sigmoid":
        sg = torch.sigmoid(t)
        return sg * (1 - sg)
    sp = torch.nn.functional.softplus(t)
    return torch.sigmoid(t) / (2 * torch.sqrt(sp.clamp_min(1e-30)))


def _stage_ok(s, d, sel_mask, torch, avail=None):
    """min_{选中}(s−d) > max_{可竞争但未选}(s+d),逐 token。

    `avail` 是"有资格参与竞争"的掩码。分组路由必须传:未选中组里的专家分数再高
    也进不了 top-k(除非组选择本身变了,而那由组阶段管)。不传 avail 会把它们算成
    竞争者,判据比现行证书**更严** —— smoke ② 当场抓出 25/400 不一致。
    """
    NEG, POS = float("-inf"), float("inf")
    lo = torch.where(sel_mask, s - d, torch.full_like(s, POS)).amin(-1)
    comp = ~sel_mask if avail is None else (avail & ~sel_mask)
    hi = torch.where(comp, s + d, torch.full_like(s, NEG)).amax(-1)
    return lo > hi


def ladder(x, w, b, topk, scoring, bits, n_group=1, topk_group=1, wb=None):
    import torch
    from w2cv_biased_router_margin import SCORING, rtn_quant, _grouped_select
    fn, Lg = SCORING[scoring]
    z = (x @ w.T).float()
    zq = (x @ rtn_quant(w, bits).T).float()
    if wb is not None:
        z, zq = z + wb, zq + wb
    dz = (zq - z).abs()
    eps = dz.amax(-1, keepdim=True)
    s, sq = fn(z) + b, fn(zq) + b
    n, E = s.shape
    grouped = n_group > 1

    # 选中集合(未扰动),分组路由要先定组
    avail = None
    if grouped:
        ids, _, _ = _grouped_select(s, topk, n_group, topk_group)
        idsq, _, _ = _grouped_select(sq, topk, n_group, topk_group)
        gs = s.view(n, n_group, -1).topk(2, -1)[0].sum(-1)
        gsel = torch.zeros_like(gs, dtype=torch.bool).scatter_(
            1, gs.topk(topk_group, -1).indices, True)
        avail = gsel.unsqueeze(-1).expand(n, n_group,
                                          E // n_group).reshape(n, E)
    else:
        ids = s.topk(topk, -1).indices.sort(-1).values
        idsq = sq.topk(topk, -1).indices.sort(-1).values
    sel = torch.zeros_like(s, dtype=torch.bool).scatter_(1, ids, True)
    flip = (ids != idsq).any(-1)

    tiers = {
        "T0_global_eps": Lg * eps.expand_as(dz),
        "T1_per_expert_eps": Lg * dz,
        "T2_local_lipschitz": (dz if scoring == "_logit_domain_no_bias"
                               else _local_L(scoring, z, dz, torch) * dz),
    }
    out = {}
    for name, d in tiers.items():
        ok = _stage_ok(s, d, sel, torch, avail=avail)
        if grouped:
            # 组分数扰动 ≤ 组内 d 的前二之和(组分数是组内 top-2 之和)
            D = d.view(n, n_group, -1).topk(2, -1)[0].sum(-1)
            ok = ok & _stage_ok(gs, D, gsel, torch)
        out[name] = {"admit": float(ok.float().mean()),
                     "soundness_viol": int((ok & flip).sum())}
    out["T3_oracle"] = {"admit": float((~flip).float().mean()),
                        "soundness_viol": 0}
    out["n_tokens"] = int(n)
    return out


def _smoke():
    import torch
    import torch.nn.functional as F
    fails = []
    # ① 单峰性:两个 scoring 的导数在网格上确实各只有一个峰
    g = torch.linspace(-40, 40, 400001)
    for name, f in (("sigmoid", torch.sigmoid),
                    ("sqrtsoftplus",
                     lambda t: torch.sqrt(F.softplus(t)))):
        gg = g.clone().requires_grad_(True)
        d = torch.autograd.grad(f(gg).sum(), gg)[0]
        am = int(d.argmax())
        rising = (d[1:am] >= d[:am - 1]).float().mean()
        falling = (d[am + 1:] <= d[am:-1]).float().mean()
        if min(float(rising), float(falling)) < 0.999:
            fails.append(f"①{name} 导数非单峰(升段 {rising:.3f} 降段 {falling:.3f})"
                         " —— _local_L 用 clip(峰位) 取 sup 的前提不成立")
        peak = float(g[am])
        want = {"sigmoid": 0.0, "sqrtsoftplus": 0.9214225}[name]
        if abs(peak - want) > 0.01:
            fails.append(f"①{name} 峰位实测 {peak:.4f} ≠ 表里的 {want}")
    # ② T0 必须**恒等于**现行判据 m>2Lε(∧ m_group>4Lε)
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from w2cv_biased_router_margin import cert_pass, _grouped_select, SCORING
    torch.manual_seed(11)
    for grouped in (False, True):
        n, E, G, TG, K = 400, 64, (8 if grouped else 1), (4 if grouped else 1), 4
        s = torch.rand(n, E)
        d = torch.rand(n, 1).expand(n, E) * 0.05          # 逐 token 常数 = Lε
        if grouped:
            ids, m_g, m_e = _grouped_select(s, K, G, TG)
            gs = s.view(n, G, -1).topk(2, -1)[0].sum(-1)
            gsel = torch.zeros_like(gs, dtype=torch.bool).scatter_(
                1, gs.topk(TG, -1).indices, True)
        else:
            ids = s.topk(K, -1).indices.sort(-1).values
            top = s.topk(K + 1, -1).values
            m_g, m_e = None, top[:, K - 1] - top[:, K]
        sel = torch.zeros_like(s, dtype=torch.bool).scatter_(1, ids, True)
        av = (gsel.unsqueeze(-1).expand(n, G, E // G).reshape(n, E)
              if grouped else None)
        mine = _stage_ok(s, d, sel, torch, avail=av)
        if grouped:
            D = d.reshape(n, G, -1).topk(2, -1)[0].sum(-1)
            mine = mine & _stage_ok(gs, D, gsel, torch)
        theirs = cert_pass(m_g, m_e, 1.0, d[:, 0], grouped=grouped)
        bad = int((mine != theirs).sum())
        if bad:
            fails.append(f"②grouped={grouped}:统一判据与 cert_pass 不一致 "
                         f"{bad}/{n} —— T0 不复现现行证书,阶梯无意义")
    # ③ 变异:把 T1 的逐专家误差换回全局 max,admit 必须**下降**(否则 T1 没生效)
    x = torch.randn(300, 64)
    w = torch.randn(32, 64) * 0.3
    b = torch.zeros(32)
    r = ladder(x, w, b, 4, "sigmoid", 4)
    if not (r["T0_global_eps"]["admit"] <= r["T1_per_expert_eps"]["admit"]
            <= r["T2_local_lipschitz"]["admit"] <= r["T3_oracle"]["admit"]):
        fails.append(f"③阶梯非单调:{ {k: round(v['admit'], 4) for k, v in r.items() if isinstance(v, dict)} }"
                     " —— 每档只放松一个假设,admit 必须单调不减")
    if any(v["soundness_viol"] for v in r.values() if isinstance(v, dict)):
        fails.append("③放松后出现 soundness 违约 —— 某一档的界写错了")
    if fails:
        print("TIGHTNESS LADDER SMOKE FAILED:")
        for f in fails:
            print("   " + f)
        sys.exit(1)
    print("TIGHTNESS LADDER SMOKE PASSED(导数单峰 + T0 恒等于现行判据 + "
          "阶梯单调且无违约)")


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
    n_group = int(cfg.get("n_group") or 1)
    topk_group = int(cfg.get("topk_group") or 1)
    # **层筛选口径必须与 w2cv 逐字一致**,否则 T0 复现不了已发表的 binding,
    # 而那时分不清是判据错了还是层集合不同(hash 层:config 的 num_hash_layers
    # 且该层确无 bias,两个条件都要)。
    all_layers = sorted(cap["x_mlp"], key=int)
    n_hash_cfg = int(cfg.get("num_hash_layers") or 0)
    layers = [L for L in all_layers
              if not (int(L) < n_hash_cfg
                      and cap.get("gate_bias", {}).get(L) is None)]
    assert layers, "无 score-routed 层"
    res = {"model": cfg.get("model", "?"), "topk": topk, "scoring": scoring,
           "n_routed_experts": int(cfg["n_routed_experts"]),
           "n_group": n_group, "topk_group": topk_group,
           "manifest": stamp(run_id="w2cw_%s" % cfg.get("model", "?"),
                             seed=None, stack="offline, zero-GPU"),
           "generated_by": "w2cw_tightness_ladder.py",
           "n_layers_scored": len(layers),
           "n_layers_hash_excluded": len(all_layers) - len(layers),
           "per_bits": {}}
    accs = []
    for L_ in layers:
        _b = (cap.get("gate_bias") or {}).get(L_)
        _wb = (cap.get("gate_linear_bias") or {}).get(L_)
        accs.append(ladder(cap["x_mlp"][L_].float(), cap["gates"][L_].float(),
                           _b.float() if _b is not None else 0.0,
                           topk, scoring, 4, n_group=n_group,
                           topk_group=topk_group,
                           wb=_wb.float() if _wb is not None else None))
    n_tot = sum(a["n_tokens"] for a in accs)
    acc = {"n_tokens": n_tot}
    for k in accs[0]:
        if k == "n_tokens":
            continue
        acc[k] = {
            "admit": sum(a[k]["admit"] * a["n_tokens"] for a in accs) / n_tot,
            "soundness_viol": sum(a[k]["soundness_viol"] for a in accs)}
    res["per_bits"]["int4"] = acc
    a = res["per_bits"]["int4"]
    print(f"{res['model']}: k={topk} E={res['n_routed_experts']} "
          f"n={a['n_tokens']:,}")
    for k in ("T0_global_eps", "T1_per_expert_eps", "T2_local_lipschitz",
              "T3_oracle"):
        print(f"   {k:22s} admit={100*a[k]['admit']:6.2f}%  "
              f"viol={a[k]['soundness_viol']}")
    json.dump(res, open(out_path, "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    print("->", out_path)


if __name__ == "__main__":
    main()
