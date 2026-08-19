# -*- coding: utf-8 -*-
"""W2-c″(判别臂,单卡 ~10 分钟):路由翻转 vs 质量解耦判别。

W2-c′ 实测:仅 expert INT4(gate 精确)翻转 58.3% 的 top-6 路由
(margins_hopeless)。而行业实证(AMD MXFP4 DeepSeek 族)同类量化任务
质量几乎不掉。若两者在同批数据上同真 ⇒ **逐 token 路由不变性是非承载
不变量**(专家冗余,翻转≠伤害)——支柱 B 保护的对象错了。

方法:同一 teacher-forced token 流(W2-c′ ①的贪心续写),bf16 与
INT4-expert 两模型逐 token NLL;配对差即质量影响,与翻转率并置。

**预注册判读(先看数前写死;ΔNLL = 量化臂 − 基线,nats/token)**:
  ΔNLL 中位 ≤ 0.02 且 p95 ≤ 0.10 → flips_benign:
      翻转大面积存在而质量不动 ⇒ 路由不变性非承载,支柱 B 的对象证伪
      (不是"margin 太小"而是"根本不该护这个");
  ΔNLL 中位 ≥ 0.10 → flips_harmful:质量真掉,支柱 B 对象成立但
      INT4 已过界,证书语义转向"何时必须回退整层精度";
  其间 → gray。

env:W2CQ_MODEL, W2CQ_OUT;W2CQ_SMOKE=1
python3 experiments/w2cq_flip_vs_quality.py
"""
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402
from w1_act_capture import BASES  # noqa: E402
from w2cp_upstream_router import arm_targets, quant_rtn_  # noqa: E402

SMOKE = os.environ.get("W2CQ_SMOKE") == "1"
MODEL = os.environ["W2CQ_MODEL"]
OUT = os.environ["W2CQ_OUT"]
P_TOK = 128 if SMOKE else 2048
D_STEP = 8 if SMOKE else 64
PROMPTS = BASES[:2] if SMOKE else BASES
MED_BENIGN, P95_BENIGN, MED_HARM = 0.02, 0.10, 0.10


def nll_per_token(model, ids):
    with torch.no_grad():
        out = model(ids, attention_mask=torch.ones_like(ids), use_cache=False)
    logp = torch.log_softmax(out.logits[:, :-1].float(), -1)
    tgt = ids[:, 1:]
    return -logp.gather(-1, tgt[..., None]).squeeze(-1)[0]      # [T-1]


def main():
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
    # ① 贪心续写(与 W2-c′ ①同构)
    seqs = []
    for uid, base in enumerate(PROMPTS):
        ids = tok((base * 400)[: P_TOK * 6],
                  return_tensors="pt").input_ids[:, :P_TOK].to("cuda")
        cur, out_ids = ids.shape[1], ids
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
        seqs.append(out_ids)
    # ② 基线 NLL
    base_nll = [nll_per_token(model, ids).cpu() for ids in seqs]
    # ③ INT4-expert 臂(armA 同 W2-c′)
    del model
    torch.cuda.empty_cache()
    model = AutoModelForCausalLM.from_pretrained(MODEL, **kw).to("cuda").eval()
    with torch.no_grad():
        for _, m in arm_targets(model, "A"):
            quant_rtn_(m.weight.data, 4)
    q_nll = [nll_per_token(model, ids).cpu() for ids in seqs]
    d = torch.cat([q - b for q, b in zip(q_nll, base_nll)])
    med, p95 = float(d.median()), float(d.quantile(0.95))
    if med <= MED_BENIGN and p95 <= P95_BENIGN:
        verdict = "flips_benign"
    elif med >= MED_HARM:
        verdict = "flips_harmful"
    else:
        verdict = "gray"
    rep = {"what": "W2-c″:路由翻转 vs 质量解耦判别(armA INT4 同 W2-c′)",
           "preregistered": {"benign": f"ΔNLL 中位≤{MED_BENIGN} 且 p95≤{P95_BENIGN}",
                             "harmful": f"中位≥{MED_HARM}"},
           "verdict": verdict,
           "summary": {"dnll_median": med, "dnll_p95": p95,
                       "dnll_mean": float(d.mean()),
                       "base_nll_mean": float(torch.cat(base_nll).mean()),
                       "n_tokens": int(d.numel())},
           "caliber": ["同 W2-c′ token 流与量化臂(armA=仅 expert INT4 g32);"
                       "teacher-forced NLL 配对差;V2-Lite 代理",
                       "与 W2-c′ 的 58.3% 翻转率并置读:benign ⇒ 路由不变性"
                       "非承载;harmful ⇒ 对象成立但 INT4 过界"],
           "manifest": stamp(run_id="w2cq_quality", seed=None,
                             stack="transformers bf16 vs INT4-expert"),
           "generated_by": "w2cq_flip_vs_quality.py"}
    json.dump(rep, open(OUT, "w"), ensure_ascii=False, indent=1)
    print("W2CQ verdict:", verdict, "| dNLL med=%.4f p95=%.4f n=%d"
          % (med, p95, d.numel()))


if __name__ == "__main__":
    main()
