# -*- coding: utf-8 -*-
"""W2-c‴(E10 分叉点,单卡 ~40 分钟):自然语料 + 任务级判别 ——
W2-c″ 的 flips_benign 是否在真实文本上存活。

内部效度威胁(自查发现):W2-c″ 的 prompt 是 16 条短句 ×300 重复,
重复文本熵趋零,teacher-forced ΔNLL 天然不敏感 —— p95=0.0011 可能是
假阴性。本轮双指标复判,armA 同口径(仅 expert INT4 g32,gate bf16):
  ①自然语料 NLL:natural(Gutenberg)12 篇 + code 4 篇,各 4k token
    前缀,逐 token 配对 ΔNLL;逐文件 bootstrap CI(文件内 token 相关,
    重采样单位=文件);同场记录 router 翻转率(自然文本口径);
  ②任务:ARC-Easy 0-shot choice-logprob,N≤500 题,配对 Δacc +
    逐题 bootstrap CI。

**预注册判读(先于看数写死)**:
  NLL 分支:benign 若 ΔNLL 中位 ≤0.02 且 p95 ≤0.10(承 W2-c″ 同门槛);
  任务分支:有效性前提 base acc ≥45%(随机 25%);benign 若
    Δacc ≥ −1.0pp 且其 95% CI 下界 ≥ −3.0pp;
  总判:两分支皆 benign → dissociation_confirmed(分析型论文主叙事定);
        任一 harmful(NLL 中位 ≥0.10 或 Δacc ≤ −3.0pp)→
        dissociation_broken(支柱 B 复活,W 线重排);
        其余 → gray(升级臂:更大 N/更多语料)。
  附:自然文本翻转率(与 58.3% 重复文本口径对拍,入文用)。

env:W2CR_MODEL, W2CR_OUT, W2CR_ARC(jsonl 路径,缺则跳过任务分支并记
inconclusive_task_missing), W2CR_SMOKE=1
python3 experiments/w2cr_natural_discriminator.py
"""
import glob
import json
import os
import random
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402
from w2cp_upstream_router import arm_targets, quant_rtn_  # noqa: E402

SMOKE = os.environ.get("W2CR_SMOKE") == "1"
MODEL = os.environ.get("W2CR_MODEL")
OUT = os.environ.get("W2CR_OUT")
ARC = os.environ.get("W2CR_ARC")
CORP = os.environ.get("W2CR_CORPUS", "/workspace/corpus")
P_TOK = 256 if SMOKE else 4096
N_NAT, N_CODE = (2, 1) if SMOKE else (12, 4)
N_ARC = 20 if SMOKE else 500
NLL_MED, NLL_P95, TASK_PP, TASK_CI, TASK_HARM = 0.02, 0.10, -1.0, -3.0, -3.0
BASE_ACC_MIN = 0.45


def load_model(quant):
    from transformers import AutoModelForCausalLM
    try:
        from transformers.cache_utils import DynamicCache
        if not hasattr(DynamicCache, "get_usable_length"):
            DynamicCache.get_usable_length = (
                lambda self, new_seq_length=0, layer_idx=0:
                self.get_seq_length(layer_idx))
    except ImportError:
        pass
    m = AutoModelForCausalLM.from_pretrained(
        MODEL, torch_dtype=torch.bfloat16,
        trust_remote_code=True).to("cuda").eval()
    if quant:
        with torch.no_grad():
            for _, mod in arm_targets(m, "A"):
                quant_rtn_(mod.weight.data, 4)
    return m


def gate_hooks(model, sink):
    handles = []
    for i, L in enumerate(model.model.layers):
        g = getattr(L.mlp, "gate", None)
        w = getattr(g, "weight", None) if g is not None else None
        if w is None or w.dim() != 2 or w.shape[0] >= w.shape[1]:
            continue

        def mk(idx, wt):
            def h(module, args, kwargs=None):
                x = args[0] if args else kwargs["hidden_states"]
                z = x.reshape(-1, x.shape[-1]).float() @ wt.float().T
                sink.setdefault(idx, []).append(z.topk(6, -1).indices
                                               .sort(-1).values.cpu())
            return h
        handles.append(g.register_forward_pre_hook(mk(i, w)))
    return handles


def nll_and_topk(model, ids, want_topk):
    sink = {}
    handles = gate_hooks(model, sink) if want_topk else []
    with torch.no_grad():
        out = model(ids, attention_mask=torch.ones_like(ids), use_cache=False)
    for h in handles:
        h.remove()
    logp = torch.log_softmax(out.logits[:, :-1].float(), -1)
    nll = -logp.gather(-1, ids[:, 1:, None]).squeeze(-1)[0].cpu()
    topk = {L: torch.cat(v) for L, v in sink.items()} if want_topk else None
    return nll, topk


def choice_logprob(model, tok, q, choices):
    scores = []
    for c in choices:
        ids = tok(q + " " + c, return_tensors="pt").input_ids.to("cuda")
        qlen = tok(q + " ", return_tensors="pt").input_ids.shape[1]
        with torch.no_grad():
            out = model(ids, attention_mask=torch.ones_like(ids))
        logp = torch.log_softmax(out.logits[:, :-1].float(), -1)
        lp = logp.gather(-1, ids[:, 1:, None]).squeeze(-1)[0]
        scores.append(float(lp[max(qlen - 1, 0):].mean()))
    return int(max(range(len(scores)), key=lambda i: scores[i]))


def main():
    assert MODEL and OUT, "需设 W2CR_MODEL/W2CR_OUT"
    from transformers import AutoTokenizer
    tok = AutoTokenizer.from_pretrained(MODEL, trust_remote_code=True)
    rng = random.Random(7)
    nat = sorted(glob.glob(os.path.join(CORP, "natural", "*")))[:N_NAT]
    cod = sorted(glob.glob(os.path.join(CORP, "code", "*")))[:N_CODE]
    files = nat + cod
    assert files, "语料缺失"
    texts = [open(f, errors="ignore").read()[:P_TOK * 8] for f in files]
    idss = [tok(t, return_tensors="pt").input_ids[:, :P_TOK].to("cuda")
            for t in texts]

    arc = []
    if ARC and os.path.exists(ARC):
        for line in open(ARC, encoding="utf-8"):
            d = json.loads(line)
            ch = d["question"]["choices"]
            labs = [c["label"] for c in ch]
            if d["answerKey"] not in labs:
                continue
            arc.append((d["question"]["stem"], [c["text"] for c in ch],
                        labs.index(d["answerKey"])))
        rng.shuffle(arc)
        arc = arc[:N_ARC]

    res = {}
    for tag, quant in (("base", False), ("int4exp", True)):
        model = load_model(quant)
        nlls, topks = [], []
        for ids in idss:
            n, tk = nll_and_topk(model, ids, want_topk=True)
            nlls.append(n)
            topks.append(tk)
        preds = [choice_logprob(model, tok, q, ch) for q, ch, _ in arc]
        res[tag] = {"nll": nlls, "topk": topks, "preds": preds}
        del model
        torch.cuda.empty_cache()
        print(tag, "done", flush=True)

    dn = [q - b for q, b in zip(res["int4exp"]["nll"], res["base"]["nll"])]
    dcat = torch.cat(dn)
    med, p95 = float(dcat.median()), float(dcat.quantile(0.95))
    boots = []
    for _ in range(2000):
        pick = [dn[rng.randrange(len(dn))] for _ in dn]
        boots.append(float(torch.cat(pick).median()))
    boots.sort()
    med_ci = (boots[49], boots[1949])
    flips = []
    for tb, tq in zip(res["base"]["topk"], res["int4exp"]["topk"]):
        for L in tb:
            T = min(tb[L].shape[0], tq[L].shape[0])
            flips.append((tb[L][:T] != tq[L][:T]).any(-1).float())
    flip_rate = float(torch.cat(flips).mean())

    task = {"n": len(arc)}
    if arc:
        gold = [g for _, _, g in arc]
        accb = sum(p == g for p, g in zip(res["base"]["preds"], gold)) / len(arc)
        accq = sum(p == g for p, g in zip(res["int4exp"]["preds"], gold)) / len(arc)
        diffs = [(int(res["int4exp"]["preds"][i] == gold[i])
                  - int(res["base"]["preds"][i] == gold[i])) for i in range(len(arc))]
        bs = []
        for _ in range(2000):
            s = [diffs[rng.randrange(len(diffs))] for _ in diffs]
            bs.append(100 * sum(s) / len(s))
        bs.sort()
        task.update(acc_base=accb, acc_quant=accq, dacc_pp=100 * (accq - accb),
                    dacc_ci95=(bs[49], bs[1949]), valid=accb >= BASE_ACC_MIN)
    nll_benign = med <= NLL_MED and p95 <= NLL_P95
    nll_harm = med >= 0.10
    if arc and task.get("valid"):
        t_ok = task["dacc_pp"] >= TASK_PP and task["dacc_ci95"][0] >= TASK_CI
        t_harm = task["dacc_pp"] <= TASK_HARM
        if nll_benign and t_ok:
            verdict = "dissociation_confirmed"
        elif nll_harm or t_harm:
            verdict = "dissociation_broken"
        else:
            verdict = "gray"
    else:
        verdict = ("inconclusive_task_missing" if nll_benign else
                   ("dissociation_broken" if nll_harm else "gray"))
    rep = {"what": "W2-c‴:自然语料+任务级判别(E10 分叉点)",
           "preregistered": {"nll": f"benign 中位≤{NLL_MED}∧p95≤{NLL_P95};harm 中位≥0.10",
                             "task": f"有效 base≥{BASE_ACC_MIN};benign Δacc≥{TASK_PP}pp∧CI下界≥{TASK_CI}pp",
                             "verdict 规则": "双 benign=confirmed;任一 harm=broken;余 gray"},
           "verdict": verdict,
           "summary": {"dnll_median": med, "dnll_p95": p95,
                       "dnll_median_ci95": med_ci,
                       "flip_rate_natural": flip_rate,
                       "n_tokens": int(dcat.numel()), "task": task},
           "caliber": [
               "armA=仅 expert INT4 g32,gate bf16(W2-c′/c″ 同口径)",
               "语料=Gutenberg 12 + code 4,各 4k token;CI 重采样单位=文件",
               "ARC-Easy 0-shot choice-logprob(长度归一均值);V2-Lite 代理",
               "对拍参照:重复文本口径 ΔNLL p95=0.0011、翻转 58.3%"],
           "manifest": stamp(run_id="w2cr_natural", seed=7,
                             stack="transformers bf16 vs INT4-expert, natural+ARC"),
           "generated_by": "w2cr_natural_discriminator.py"}
    json.dump(rep, open(OUT, "w"), ensure_ascii=False, indent=1)
    print("W2CR verdict:", verdict)
    print("dNLL med=%.4f ci(%.4f,%.4f) p95=%.4f | flip_nat=%.3f | task=%s"
          % (med, med_ci[0], med_ci[1], p95, flip_rate, task))


if __name__ == "__main__":
    main()
