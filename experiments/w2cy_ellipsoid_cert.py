# -*- coding: utf-8 -*-
"""W2-c-y:路二 —— 把扰动集合从**球**换成**实测椭球**,并诚实标注可部署性。

已发表的 binding 用的是 ε∞ = max_i|Δz_i|,那是**实测量**:拿到它等于已经把量化
路径算完了。所以现行数字是"给了 oracle 幅度之后证书还拒 99.9%",作为**负面**
结论它更强,但它不是一把能上线的尺子。

本脚本量的是另一件事:**一把真能上线的尺子能做到多好**。上线意味着扰动方向
未知,只知道它落在某个集合里。两个集合:

  D0 球     δ = Δz 满足 ‖x‖ ≤ ρ ⟹ |δ_i| ≤ ρ‖ΔW_i‖₂            (Cauchy--Schwarz)
  D1 椭球   δ 落在 {δ : δᵀC⁻¹δ ≤ r²},C = Cov(Δz) 离线拟合
            ⟹ |δ_i| ≤ r√C_ii;logit 域可用**成对**式 r√(C_ii+C_jj−2C_ij),
              它吃掉专家间的共模误差(同一个 x 打进所有专家 ⟹ C_ij 显著非零)

留出纪律(W2-a 的教训:样本内 ρ90=0.094 而留出 0.538,in-sample 集中度是幻觉):
C 与 r 只用**拟合半**的 token 估,admit 与违约只在**评估半**上报。评估半出现
soundness 违约 ⟹ r 没覆盖住,该档直接判 INVALID —— 这是本脚本的 fail-loud。

对照锚点(与 w2cw 的阶梯同源):
  T0 = 现行(实测 ε∞)、T3 = oracle(真实是否翻转)。D0/D1 与它们同表可比。

    python experiments/w2cy_ellipsoid_cert.py <cap.pt> <out.json>
    python experiments/w2cy_ellipsoid_cert.py --smoke
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from provenance import stamp  # noqa: E402


def _fit_cov(d, shrink, torch):
    """拟合半的 Δz 协方差 + 收缩(n≈E 时必须收缩,否则 C 奇异、r 爆掉)。"""
    dc = d - d.mean(0, keepdim=True)
    C = (dc.T @ dc) / max(dc.shape[0] - 1, 1)
    tr = float(torch.diagonal(C).mean())
    return (1 - shrink) * C + shrink * tr * torch.eye(C.shape[0],
                                                      dtype=C.dtype)


def _whitened_radii(d, C, torch, alphas=(0.01, 0.05)):
    """拟合半上 √(δᵀC⁻¹δ) 的最大值,以及各 α 的**共形**半径。

    max 给确定性半径(该批必然覆盖,但对新点无保证 —— 它是极值统计,又贵又没
    正式保证)。共形半径取第 ⌈(1−α)(n+1)⌉ 小的白化范数:在可交换性假设下
    Pr(新点落在椭球外) ≤ α。这与本文历史外推用的是**同一台仪器**,α 进同一本
    账。**主张类型随之改变**(确定性 → 边际覆盖),必须分栏报,不能混比。
    """
    Lc = torch.linalg.cholesky(C)
    y = torch.linalg.solve_triangular(Lc, (d - d.mean(0, keepdim=True)).T,
                                      upper=False)
    u = y.pow(2).sum(0).sqrt()
    us, n = u.sort().values, u.numel()
    conf = {}
    for a in alphas:
        k = min(n - 1, max(0, -(-int((1 - a) * (n + 1)) // 1) - 1))
        conf[a] = float(us[k])
    return float(u.max()), conf, d.mean(0)


def tiers(x, w_, b, topk, scoring, bits, n_group, topk_group, wb, shrink,
          split):
    import torch
    from w2cv_biased_router_margin import SCORING, rtn_quant, _grouped_select
    from w2cw_tightness_ladder import _stage_ok, _local_L
    fn, Lg = SCORING[scoring]
    dW = rtn_quant(w_, bits) - w_
    z = (x @ w_.T).float()
    zq = (x @ rtn_quant(w_, bits).T).float()
    if wb is not None:
        z, zq = z + wb, zq + wb
    dz = (zq - z)
    s, sq = fn(z) + b, fn(zq) + b
    n, E = s.shape
    grouped = n_group > 1
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

    ev = torch.zeros(n, dtype=torch.bool); ev[split:] = True
    fit = ~ev
    if int(fit.sum()) < 8 or int(ev.sum()) < 1:
        return None

    # --- D0 可部署球:|δ_i| ≤ ρ‖ΔW_i‖,ρ = 拟合半 ‖x‖ 的最大值 ---
    rho = float(x[fit].float().norm(dim=-1).max())
    d0 = Lg * rho * dW.float().norm(dim=-1).unsqueeze(0).expand(n, E)
    # --- D1 椭球:C、r 都只用拟合半 ---
    C = _fit_cov(dz[fit].double(), shrink, torch)
    r, rconf, mu = _whitened_radii(dz[fit].double(), C, torch)
    sd = torch.diagonal(C).clamp_min(0).sqrt().float()
    d1 = Lg * (r * sd + mu.abs().float()).unsqueeze(0).expand(n, E)
    # --- D1L 椭球 + 局部 Lipschitz(有 scoring 非线性时才不同) ---
    if scoring == "_logit_domain_no_bias":
        d1l = d1
    else:
        e = (r * sd + mu.abs().float()).unsqueeze(0).expand(n, E)
        d1l = _local_L(scoring, z, e, torch) * e
    # --- 锚点 ---
    eps = dz.abs().amax(-1, keepdim=True)
    t0 = Lg * eps.expand(n, E)

    # --- D3 共形半径:用显式记账的 α 换紧度(主张类型 = 边际覆盖,单独分栏) ---
    conf_tiers = {}
    for a, ra in rconf.items():
        e = ra * sd + mu.abs().float()
        da = (Lg * e if scoring == "_logit_domain_no_bias"
              else _local_L(scoring, z, e.unsqueeze(0).expand(n, E), torch)
              * e.unsqueeze(0).expand(n, E))
        conf_tiers[f"D3_conformal_a{a}"] = (da if da.dim() == 2
                                            else da.unsqueeze(0).expand(n, E))
    out = {}
    for name, d in (list((("T0_realized_eps", t0), ("D0_ball", d0),
                          ("D1_ellipsoid", d1), ("D1L_ellipsoid_localL", d1l)))
                    + list(conf_tiers.items())):
        ok = _stage_ok(s, d, sel, torch, avail=avail)
        if grouped:
            D = d.view(n, n_group, -1).topk(2, -1)[0].sum(-1)
            ok = ok & _stage_ok(gs, D, gsel, torch)
        out[name] = {"admit": float(ok[ev].float().mean()),
                     "soundness_viol": int((ok & flip)[ev].sum())}
    out["T3_oracle"] = {"admit": float((~flip[ev]).float().mean()),
                        "soundness_viol": 0}
    # 诊断:椭球相对球拿回多少,以及 Δz 的有效维数(稳定秩)
    lam = torch.linalg.eigvalsh(C).clamp_min(0)
    out["_diag"] = {"rho": rho, "r_whitened": r,
                    "stable_rank": float(lam.sum() / lam.max().clamp_min(1e-30)),
                    "E": E,
                    "d0_over_d1": float((d0[0] / d1[0].clamp_min(1e-30)).median())}
    out["n_eval"] = int(ev.sum())
    return out


def _smoke():
    import torch
    fails = []
    torch.manual_seed(7)
    x = torch.randn(600, 48)
    w_ = torch.randn(24, 48) * 0.4
    r = tiers(x, w_, 0.0, 4, "_logit_domain_no_bias", 4, 1, 1, None, 0.1, 300)
    if r is None:
        fails.append("①样本足够却返回 None")
    else:
        # ① 确定性档在评估半上**必须零违约**;共形档按设计会用掉 α,判据是
        #    "违约率 ≤ α(留 3 倍余量给有限样本波动)",不是"零违约" —— 两类主张
        #    用同一条判据,守卫就在说谎(证据种类必须匹配主张种类)。
        ne = r["n_eval"]
        for k, v in r.items():
            if not isinstance(v, dict) or "admit" not in v:
                continue
            if k.startswith("D3_conformal_a"):
                a = float(k.split("_a")[1])
                if v["soundness_viol"] / ne > 3 * a:
                    fails.append(f"①{k} 违约率 {v['soundness_viol']/ne:.4f} "
                                 f"远超 α={a} —— 共形半径没给出它承诺的覆盖")
            elif v["soundness_viol"]:
                fails.append(f"①{k} 是确定性档却出现 {v['soundness_viol']} 个违约")
        # ② 单调:D0(球) ≤ D1(椭球);任何一档 ≤ oracle
        if r["D0_ball"]["admit"] > r["D1_ellipsoid"]["admit"] + 1e-9:
            fails.append(f"②球 {r['D0_ball']['admit']:.4f} 竟然优于椭球 "
                         f"{r['D1_ellipsoid']['admit']:.4f} —— 椭球是球的加细,不可能")
        for k in ("T0_realized_eps", "D0_ball", "D1_ellipsoid"):
            if r[k]["admit"] > r["T3_oracle"]["admit"] + 1e-9:
                fails.append(f"②{k} 超过 oracle —— 该档不 sound")
        # ③ 变异:把留出打掉(全部数据拟合)admit 必须**上升**,否则留出没生效
        r2 = tiers(x, w_, 0.0, 4, "_logit_domain_no_bias", 4, 1, 1, None, 0.1,
                   len(x) - 1)
        if r2 and r2["D1_ellipsoid"]["admit"] < r["D1_ellipsoid"]["admit"] - 1e-6:
            fails.append("③几乎全量拟合反而更差 —— 留出切分没生效")
    if fails:
        print("ELLIPSOID SMOKE FAILED:")
        for f in fails:
            print("   " + f)
        sys.exit(1)
    print(f"ELLIPSOID SMOKE PASSED(无违约、球≤椭球≤oracle、留出生效;"
          f"实测 D0 {100*r['D0_ball']['admit']:.1f}% → D1 "
          f"{100*r['D1_ellipsoid']['admit']:.1f}% vs oracle "
          f"{100*r['T3_oracle']['admit']:.1f}%)")


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
    accs = []
    for L_ in layers:
        _b = (cap.get("gate_bias") or {}).get(L_)
        _wb = (cap.get("gate_linear_bias") or {}).get(L_)
        x = cap["x_mlp"][L_].float()
        r = tiers(x, cap["gates"][L_].float(),
                  _b.float() if _b is not None else 0.0, topk, scoring, 4,
                  ng, tg, _wb.float() if _wb is not None else None,
                  0.05, x.shape[0] // 2)
        if r:
            accs.append(r)
    assert accs, "无可用层"
    n_tot = sum(a["n_eval"] for a in accs)
    keys = [k for k in accs[0] if isinstance(accs[0][k], dict)
            and k != "_diag"]
    agg = {k: {"admit": sum(a[k]["admit"] * a["n_eval"] for a in accs) / n_tot,
               "soundness_viol": sum(a[k]["soundness_viol"] for a in accs)}
           for k in keys}
    dg = {k: sum(a["_diag"][k] for a in accs) / len(accs)
          for k in accs[0]["_diag"]}
    res = {"model": cfg.get("model", "?"), "topk": topk, "scoring": scoring,
           "n_routed_experts": int(cfg["n_routed_experts"]),
           "manifest": stamp(run_id="w2cy_%s" % cfg.get("model", "?"),
                             seed=None, stack="offline, zero-GPU"),
           "generated_by": "w2cy_ellipsoid_cert.py",
           "n_eval_tokens": n_tot, "n_layers": len(accs),
           "tiers": agg, "diag_layer_mean": dg,
           "protocol": "C 与 r 只用逐层前半 token 拟合,admit/违约只在后半评估"}
    print(f"{res['model']}: k={topk} E={res['n_routed_experts']} "
          f"eval n={n_tot:,} (留出后半)")
    for k in ("T0_realized_eps", "D0_ball", "D1_ellipsoid",
              "D1L_ellipsoid_localL", "D3_conformal_a0.05",
              "D3_conformal_a0.01", "T3_oracle"):
        if k not in agg:
            continue
        vr = agg[k]["soundness_viol"] / max(n_tot, 1)
        print(f"   {k:22s} admit={100*agg[k]['admit']:6.2f}%  "
              f"viol={agg[k]['soundness_viol']} ({100*vr:.3f}%)")
    print(f"   诊断: Δz 稳定秩 {dg['stable_rank']:.1f} / E={int(dg['E'])}, "
          f"球界/椭球界 中位 {dg['d0_over_d1']:.1f}×")
    json.dump(res, open(out_path, "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
