# -*- coding: utf-8 -*-
"""W2-c′(单卡,~30 分钟):上游权重量化 → router logit 漂移 vs margin
—— 支柱 B(在线路由 margin 证书)的决定性 kill-shot。

W2-c 首臂(门权重量化)判 dead_too_small,但那一臂回答的是"能否量化
gate 本身"(答案:不能,ε≈0.19 ≫ margin 中位 0.03-0.07;全行业保 gate
高精度由此有了自家数字)。支柱 B 的真问题是本臂:**gate 保 bf16,量化
其余权重**,测真实 Δx 传导到 router logit 的漂移 ε_t 对 margin m_t 的
覆盖结构。

方法(matched 三过):
  ①基线模型对 16 条 prompt 贪心生成 64 token(记 token 流);
  ②基线模型全序列一次前向(prompt+生成,teacher-forced),hook gate 输入
    x 现算 z_base[t] = x @ W_gateᵀ(fp32);
  ③量化模型(除外清单:gate/lm_head/embed;两臂:A=仅 expert 投影
    [AMD 生产口径],B=expert+attention+shared[激进])同一 token 流
    全序列前向 → z_q[t]。
  ε_t = ‖z_q[t]−z_base[t]‖∞;m_t = z_base 的 top6/top7 边距;
  binding = P(m ≤ 2ε);flip = P(top6 变);soundness:m>2ε 处不得翻
  (S1 定理,违约=0 硬断言 —— 这里 ε 是精确值非上界,违约即实现 bug)。

**预注册判读(先于看数写死;主档 = 臂 A × INT4)**:
    binding ∈ [0.005, 0.5] → upstream_margin_alive(证书有真实用武之地);
    binding < 0.005 且 flip < 0.001 → 看 INT3;INT3 亦然 → trivial 杀;
    binding > 0.5 → margins_hopeless 杀(上游噪声也淹没 margin,
      在线证书只会拒绝过半流量)。
  臂 B 与 decode/prefill 分相数据全量落盘作次级判读,不改主判据。

env:W2CP_MODEL, W2CP_OUT;W2CP_SMOKE=1(2 prompt/16 tok/8 步)
python3 experiments/w2cp_upstream_router.py
"""
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402
from w1_act_capture import BASES  # noqa: E402  (同一 prompt 集,口径连续)

SMOKE = os.environ.get("W2CP_SMOKE") == "1"
# .get 而非 []:w2cq 复用本模块 arm_targets/quant_rtn_ 时不得因缺 env 炸 import
MODEL = os.environ.get("W2CP_MODEL")
OUT = os.environ.get("W2CP_OUT")
P_TOK = 128 if SMOKE else 2048
D_STEP = 8 if SMOKE else 64
PROMPTS = BASES[:2] if SMOKE else BASES
BITS = (4, 3)
GROUP = 32
ALIVE_LO, ALIVE_HI, FLIP_TRIVIAL = 0.005, 0.5, 0.001

_CAP = {"z": {}}          # (layer) -> list of [T,E] logits(当前过程内)


def quant_rtn_(w, bits, group=GROUP):
    """就地 group-wise absmax RTN。"""
    E, d = w.shape
    pad = (group - d % group) % group
    x = torch.nn.functional.pad(w.float(), (0, pad)).view(E, -1, group)
    qmax = 2 ** (bits - 1) - 1
    s = x.abs().amax(-1, keepdim=True).clamp_min(1e-12) / qmax
    xq = torch.round(x / s).clamp(-qmax - 1, qmax) * s
    w.copy_(xq.view(E, -1)[:, :d].to(w.dtype))


def arm_targets(model, arm):
    """返回要量化的 Linear 模块列表。gate/lm_head/embed 永不量化。"""
    tgts = []
    for name, m in model.named_modules():
        if not isinstance(m, torch.nn.Linear):
            continue
        if "gate" == name.split(".")[-1] or "lm_head" in name:
            continue
        is_expert = ".experts." in name or ".shared_experts." in name
        is_attn = ".self_attn." in name
        is_mlp = ".mlp." in name and not is_expert
        if arm == "A" and is_expert:
            tgts.append((name, m))
        elif arm == "B" and (is_expert or is_attn or is_mlp):
            tgts.append((name, m))
    return tgts


def hook_gates(model):
    handles, weights = [], {}
    for i, L in enumerate(model.model.layers):
        g = getattr(L.mlp, "gate", None)
        w = getattr(g, "weight", None) if g is not None else None
        if w is None or w.dim() != 2 or w.shape[0] >= w.shape[1]:
            continue
        weights[i] = w

        def mk(idx):
            def h(module, args, kwargs=None):
                x = args[0] if args else kwargs["hidden_states"]
                z = x.reshape(-1, x.shape[-1]).float() @ weights[idx].float().T
                _CAP["z"].setdefault(idx, []).append(z.cpu())
            return h
        handles.append(g.register_forward_pre_hook(mk(i)))
    assert weights, "未发现 gate —— 非 MoE 或发现逻辑失配"
    return handles, weights


def full_forward(model, ids):
    _CAP["z"] = {}
    with torch.no_grad():
        model(ids, attention_mask=torch.ones_like(ids), use_cache=False)
    return {L: torch.cat(v) for L, v in _CAP["z"].items()}


def main():
    assert MODEL and OUT, "需设 W2CP_MODEL 与 W2CP_OUT"
    from transformers import AutoModelForCausalLM, AutoTokenizer
    try:
        from transformers.cache_utils import DynamicCache
        if not hasattr(DynamicCache, "get_usable_length"):
            DynamicCache.get_usable_length = (
                lambda self, new_seq_length=0, layer_idx=0:
                self.get_seq_length(layer_idx))
    except ImportError:
        pass
    tok = AutoTokenizer.from_pretrained(MODEL, trust_remote_code=True)
    kw = dict(torch_dtype=torch.bfloat16, trust_remote_code=True)
    model = AutoModelForCausalLM.from_pretrained(MODEL, **kw).to("cuda").eval()

    # ① 基线贪心生成 token 流(无 hook)
    seqs = []
    for uid, base in enumerate(PROMPTS):
        ids = tok((base * 400)[: P_TOK * 6],
                  return_tensors="pt").input_ids[:, :P_TOK].to("cuda")
        cur, past = ids.shape[1], None
        out_ids = ids
        with torch.no_grad():
            out = model(ids, use_cache=True,
                        attention_mask=torch.ones(1, cur, device="cuda",
                                                  dtype=torch.long))
            past, nxt = out.past_key_values, out.logits[:, -1:].argmax(-1)
            for _ in range(D_STEP):
                out_ids = torch.cat([out_ids, nxt], 1)
                cur += 1
                out = model(nxt, past_key_values=past, use_cache=True,
                            attention_mask=torch.ones(1, cur, device="cuda",
                                                      dtype=torch.long))
                past, nxt = out.past_key_values, out.logits[:, -1:].argmax(-1)
        seqs.append((uid, out_ids, ids.shape[1]))
        print(f"gen uid {uid} done", flush=True)

    # ② 基线全序列前向 → z_base
    handles, _ = hook_gates(model)
    zb = {}
    for uid, ids, plen in seqs:
        zb[uid] = full_forward(model, ids)
    for h in handles:
        h.remove()

    # ③ 两臂 × 两档:量化其余权重 → z_q(每臂档独立从盘重载,避免误差叠加)
    res, per_layer = {}, []
    n_viol_total = 0
    for arm in ("A", "B"):
        for bits in BITS:
            del model
            torch.cuda.empty_cache()
            model = AutoModelForCausalLM.from_pretrained(
                MODEL, **kw).to("cuda").eval()
            tgts = arm_targets(model, arm)
            with torch.no_grad():
                for _, m in tgts:
                    quant_rtn_(m.weight.data, bits)
            handles, _ = hook_gates(model)
            agg = {ph: {"n": 0, "bind": 0, "flip": 0, "viol": 0}
                   for ph in ("prefill", "decode")}
            for uid, ids, plen in seqs:
                zq = full_forward(model, ids)
                for L, zB in zb[uid].items():
                    zQ = zq[L]
                    T = min(zB.shape[0], zQ.shape[0])
                    zB2, zQ2 = zB[:T], zQ[:T]
                    top = zB2.topk(7, -1).values
                    m = top[:, 5] - top[:, 6]
                    eps = (zQ2 - zB2).abs().amax(-1)
                    ib = zB2.topk(6, -1).indices.sort(-1).values
                    iq = zQ2.topk(6, -1).indices.sort(-1).values
                    flip = (ib != iq).any(-1)
                    bind = m <= 2 * eps
                    viol = int((flip & ~bind).sum())
                    n_viol_total += viol
                    for ph, sl in (("prefill", slice(0, plen)),
                                   ("decode", slice(plen, T))):
                        a = agg[ph]
                        a["n"] += int(bind[sl].numel())
                        a["bind"] += int(bind[sl].sum())
                        a["flip"] += int(flip[sl].sum())
            for h in handles:
                h.remove()
            key = f"arm{arm}_int{bits}"
            res[key] = {ph: {"binding": a["bind"] / max(a["n"], 1),
                             "flip": a["flip"] / max(a["n"], 1), "n": a["n"]}
                        for ph, a in agg.items()}
            print(key, res[key], flush=True)
    assert n_viol_total == 0, f"S1 违约 {n_viol_total} —— ε 为精确值,违约即 bug"

    def tot(key, f):
        r = res[key]
        n = r["prefill"]["n"] + r["decode"]["n"]
        v = r["prefill"][f] * r["prefill"]["n"] + r["decode"][f] * r["decode"]["n"]
        return v / max(n, 1)

    b4, f4 = tot("armA_int4", "binding"), tot("armA_int4", "flip")
    if ALIVE_LO <= b4 <= ALIVE_HI:
        verdict = "upstream_margin_alive"
    elif b4 > ALIVE_HI:
        verdict = "margins_hopeless"
    else:
        b3, f3 = tot("armA_int3", "binding"), tot("armA_int3", "flip")
        if f4 < FLIP_TRIVIAL and (ALIVE_LO <= b3 <= ALIVE_HI):
            verdict = "alive_at_int3"
        elif f4 < FLIP_TRIVIAL and b3 < ALIVE_LO and f3 < FLIP_TRIVIAL:
            verdict = "trivial_dead"
        else:
            verdict = "gray"
    rep = {"what": "W2-c′:上游量化 → router logit 漂移 vs margin(支柱 B 决定臂)",
           "preregistered": {"primary": "armA(仅 expert,AMD 生产口径)× INT4",
                             "alive": f"binding∈[{ALIVE_LO},{ALIVE_HI}]",
                             "hopeless": f">{ALIVE_HI}",
                             "trivial": f"binding<{ALIVE_LO}∧flip<{FLIP_TRIVIAL}→查 INT3"},
           "verdict": verdict, "results": res,
           "soundness_viol": n_viol_total,
           "caliber": [
               "teacher-forced 基线 token 流,三过 matched;ε 为精确 ‖Δz‖∞ 非上界",
               "gate/lm_head/embed 永不量化;臂 A=仅 expert 投影,臂 B=+attention+dense mlp",
               "V2-Lite 27 层代理;margin 在 gate 线性 logit 域",
               f"P_TOK={P_TOK} D_STEP={D_STEP} 16 prompt(p101 同源)"],
           "manifest": stamp(run_id="w2cp_upstream", seed=None,
                             stack=f"transformers, {MODEL.split('/')[-1]}, bf16 vs INT4/3"),
           "generated_by": "w2cp_upstream_router.py"}
    json.dump(rep, open(OUT, "w"), ensure_ascii=False, indent=1)
    print("W2CP verdict:", verdict, "| armA_int4 binding=%.4f flip=%.5f" % (b4, f4))


if __name__ == "__main__":
    main()
