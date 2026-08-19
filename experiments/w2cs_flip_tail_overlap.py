# -*- coding: utf-8 -*-
"""W2-c⁗(追加判别,单卡 ~15 分钟):路由翻转 × 尾部损伤重合度。

W2-c‴ 定谳:自然文本上量化损伤是**尾部事件**(ΔNLL 中位 0.0002 而
p95=0.518;任务分不掉),翻转率 35.3%。最后一问:尾部损伤 token 与
翻转 token 重合吗?
  —— 无富集 ⇒ 支柱 B 终葬(翻转连预警价值都没有),损伤须由输出侧
     记账(支柱 A)独立捕捉;
  —— 强富集 ⇒ margin 信号以『尾部预警器』(诊断,非门控)身份复活,
     且可做 AV 账本的廉价 side-information。

方法:同 W2-c‴ 口径(natural 12+code 4 各 4k token,armA INT4-expert),
逐 token 记 ΔNLL 与「本 token 任一 MoE 层翻转」;tail = ΔNLL 前 5% 分位。
**预注册**:富集比 OR = P(tail|flip)/P(tail|¬flip):
  OR ≥ 3 → flip_predicts_tail(预警器复活);
  OR ≤ 1.5 → flip_uninformative(支柱 B 终葬);
  其间 → gray。
  附:逐层深度分组 OR(浅/中/深),AUROC(用逐 token 翻转层数当分数)。

env:W2CS_MODEL, W2CS_OUT;复用 w2cr 的语料与量化口径。
"""
import glob
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402
from w2cp_upstream_router import arm_targets, quant_rtn_  # noqa: E402
from w2cr_natural_discriminator import load_model, gate_hooks  # noqa: E402

MODEL = os.environ.get("W2CS_MODEL")
OUT = os.environ.get("W2CS_OUT")
CORP = os.environ.get("W2CS_CORPUS", "/workspace/corpus")
SMOKE = os.environ.get("W2CS_SMOKE") == "1"
P_TOK = 256 if SMOKE else 4096
N_NAT, N_CODE = (2, 1) if SMOKE else (12, 4)
TAIL_Q, OR_HI, OR_LO = 0.95, 3.0, 1.5


def run(model, ids):
    sink = {}
    handles = gate_hooks(model, sink)
    with torch.no_grad():
        out = model(ids, attention_mask=torch.ones_like(ids), use_cache=False)
    for h in handles:
        h.remove()
    logp = torch.log_softmax(out.logits[:, :-1].float(), -1)
    nll = -logp.gather(-1, ids[:, 1:, None]).squeeze(-1)[0].cpu()
    topk = {L: torch.cat(v) for L, v in sink.items()}
    return nll, topk


def auroc_of(score, pos):
    """Mann--Whitney AUC。**首版有 +0.5 的常数偏移**(2026-08-09 查出):
    写成 (mean(rank0)−(P+1)/2)/N + 0.5,完美分离给 1.50、随机给 0.99 —— 报出的
    0.9169 真值是 0.4169,与 OR=0.72 同向(弱反预测),却被读成"强预测"。
    正确式:秩取 1-based **中位秩**,AUC = (Σrank⁺ − P(P+1)/2)/(P·N)。
    两个缺陷,只有一个能事后补救:
      · **偏移**是常数 ⟹ 已存产物可解析改正(true = buggy − 0.5 + 1/N);
      · **并列**不能 —— score 是整数计数、单个并列组上万,argsort 在组内按 token
        次序定序,而尾部事件可能与位置相关,偏差方向无法从存下来的标量反推。
    ⟹ **已存产物的该字段仍不可引用**,要用须重跑。本函数改用中位秩,供重跑。
    `_smoke` 用完美分离/随机/完美反预测三点钉住 1.0/0.5/0.0,偏移无处藏。
    """
    P, N = float(pos.sum()), float((~pos).sum())
    if P == 0 or N == 0:
        return None
    M = score.numel()
    o = score.argsort(stable=True)
    r1 = torch.empty(M, dtype=torch.float)
    r1[o] = torch.arange(1, M + 1, dtype=torch.float)
    # **中位秩**:score 是"翻转了几层"的整数计数(0..L),并列组极大(实测单组上万)。
    # 用 argsort 秩会让组内定序按 token 次序,而尾部事件可能与位置相关 ⟹ 偏差
    # 方向不可界。Mann--Whitney 在有并列时必须取组内平均秩。
    u, inv, cnt = torch.unique(score, return_inverse=True, return_counts=True)
    r1 = (torch.zeros(len(u)).scatter_add_(0, inv, r1) / cnt)[inv]
    return float((r1[pos].sum() - P * (P + 1) / 2) / (P * N))


def _smoke():
    """三点钉住 AUC:完美分离 1.0 / 随机 0.5 / 完美反预测 0.0。

    首版的 +0.5 偏移正是被"只看真实数据、没有已知答案的桩"放过去的 ——
    0.9169 看起来像个漂亮的强预测数,没人会怀疑它。有了这三点,任何常数
    偏移、任何秩基准错位都会当场判红。
    """
    import torch
    fails = []
    M, P = 10000, 500
    sc = torch.arange(M).float()
    hi = torch.zeros(M, dtype=torch.bool); hi[-P:] = True     # 正类分数最高
    lo = torch.zeros(M, dtype=torch.bool); lo[:P] = True      # 正类分数最低
    rnd = torch.zeros(M, dtype=torch.bool)
    rnd[torch.Generator().manual_seed(0) and
        torch.randperm(M, generator=torch.Generator().manual_seed(0))[:P]] = True
    for tag, pos, want in (("完美分离", hi, 1.0), ("完美反预测", lo, 0.0)):
        got = auroc_of(sc, pos)
        if abs(got - want) > 1e-6:
            fails.append("%s 应为 %.1f,实得 %.4f" % (tag, want, got))
    got = auroc_of(torch.randn(M, generator=torch.Generator().manual_seed(1)), rnd)
    if abs(got - 0.5) > 0.05:
        fails.append("随机应 ≈0.50,实得 %.4f" % got)
    if fails:
        print("W2CS AUROC SMOKE FAILED:")
        for f in fails:
            print("   " + f)
        sys.exit(1)
    print("W2CS AUROC SMOKE PASSED(完美分离=1.0 / 随机≈0.5 / 完美反预测=0.0)")


def main():
    if "--smoke" in sys.argv:
        return _smoke()
    assert MODEL and OUT
    from transformers import AutoTokenizer
    os.environ.setdefault("W2CR_MODEL", MODEL)   # load_model 复用
    tok = AutoTokenizer.from_pretrained(MODEL, trust_remote_code=True)
    files = (sorted(glob.glob(os.path.join(CORP, "natural", "*")))[:N_NAT]
             + sorted(glob.glob(os.path.join(CORP, "code", "*")))[:N_CODE])
    idss = [tok(open(f, errors="ignore").read()[:P_TOK * 8],
                return_tensors="pt").input_ids[:, :P_TOK].to("cuda")
            for f in files]
    res = {}
    import w2cr_natural_discriminator as w2cr
    w2cr.MODEL = MODEL
    for tag, q in (("base", False), ("int4exp", True)):
        m = w2cr.load_model(q)
        res[tag] = [run(m, ids) for ids in idss]
        del m
        torch.cuda.empty_cache()
        print(tag, "done", flush=True)
    dn, nflip = [], []
    layers = sorted(res["base"][0][1].keys())
    deep_groups = {"shallow": layers[: len(layers) // 3],
                   "mid": layers[len(layers) // 3: 2 * len(layers) // 3],
                   "deep": layers[2 * len(layers) // 3:]}
    grp_flip = {g: [] for g in deep_groups}
    for (nb, tb), (nq, tq) in zip(res["base"], res["int4exp"]):
        T = min(nb.shape[0], nq.shape[0])
        dn.append(nq[:T] - nb[:T])
        fl = torch.zeros(T)
        for g, ls in deep_groups.items():
            gfl = torch.zeros(T)
            for L in ls:
                Tl = min(tb[L].shape[0] - 1, T)
                f = (tb[L][1:Tl + 1] != tq[L][1:Tl + 1]).any(-1).float()
                gfl[:Tl] += f[:Tl]
                fl[:Tl] += f[:Tl]
            grp_flip[g].append(gfl)
        nflip.append(fl)
    d = torch.cat(dn)
    f = torch.cat(nflip)
    tail = d >= d.quantile(TAIL_Q)
    anyf = f > 0

    def orate(t, fl):
        pt_f = float(t[fl].float().mean()) if int(fl.sum()) else 0.0
        pt_n = float(t[~fl].float().mean()) if int((~fl).sum()) else 0.0
        return pt_f / max(pt_n, 1e-9), pt_f, pt_n
    OR, ptf, ptn = orate(tail, anyf)

    auroc = auroc_of(f, tail)
    per_group = {}
    for g in deep_groups:
        gf = torch.cat(grp_flip[g]) > 0
        o, a, b = orate(tail, gf)
        per_group[g] = {"or": o, "p_tail_flip": a, "p_tail_noflip": b,
                        "flip_rate": float(gf.float().mean())}
    verdict = ("flip_predicts_tail" if OR >= OR_HI else
               "flip_uninformative" if OR <= OR_LO else "gray")
    rep = {"what": "W2-c⁗:翻转×尾部损伤重合度(支柱 B 终审)",
           "preregistered": {"tail": "ΔNLL 前 5%", "OR≥3": "预警器复活",
                             "OR≤1.5": "终葬", "其间": "gray"},
           "verdict": verdict,
           "summary": {"odds_ratio": OR, "p_tail_given_flip": ptf,
                       "p_tail_given_noflip": ptn,
                       "flip_rate_any_layer": float(anyf.float().mean()),
                       "auroc_nfliplayers": auroc,
                       "per_depth_group": per_group,
                       "n_tokens": int(d.numel())},
           "caliber": ["armA INT4-expert,gate bf16;natural12+code4×4k;"
                       "flip=该 token 任一 MoE 层 top-6 变;tail 阈取自本分布",
                       "OR 混杂告警:flip 与 tail 都随文本难度上升,富集≠因果"],
           "manifest": stamp(run_id="w2cs_overlap", seed=None,
                             stack="transformers bf16 vs INT4-expert"),
           "generated_by": "w2cs_flip_tail_overlap.py"}
    json.dump(rep, open(OUT, "w"), ensure_ascii=False, indent=1)
    print("W2CS verdict:", verdict,
          "| OR=%.2f p(tail|flip)=%.4f p(tail|~flip)=%.4f auroc=%s"
          % (OR, ptf, ptn, auroc))


if __name__ == "__main__":
    main()
