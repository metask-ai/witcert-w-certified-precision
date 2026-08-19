# -*- coding: utf-8 -*-
"""把 dsv2-moegate 的 RAW 捕获打包成 w2cv 裁决要的输入。

RAW 里是 {"moegate|L{i}": [{"x": [n,H]}...], "moegate_w|L{i}": [{"w","b"}]},
层号是**首见顺序**。裁决要 {"x_mlp": {L: [N,H]}, "gates": {L: [E,H]},
"gate_bias": {L: [E] 或 None}, "cfg": {...}}。

cfg 从模型 config.json 读 —— **不从捕获里猜**:scoring_func / topk / 专家数
决定了整个 margin 口径,猜错就是"仪器前提与设计不符"。

用法:python3 experiments/w2cv_pack_capture.py <raw.pt> <model_dir> <out.pt>
"""
import json
import os
import sys

import torch

raw_p, model_dir, out_p = sys.argv[1], sys.argv[2], sys.argv[3]
d = torch.load(raw_p, map_location="cpu", weights_only=False)
cfg_j = json.load(open(os.path.join(model_dir, "config.json")))
# **多模态/复合模型把文本侧参数放在子结构里**(Llama-4 的 text_config)。
# 直接取顶层会 KeyError,而更坏的情形是某些键在顶层"恰好存在"却是别的语义 ——
# 故显式合并:子结构优先,顶层兜底。
_sub = cfg_j.get("text_config") or {}
cfg_j = {**cfg_j, **_sub}
xs, ws, bs, wbs = {}, {}, {}, {}
for k in d:
    if k.startswith("moegate|L"):
        L = k.split("|L")[1]
        rows = [r["x"] for r in d[k]]
        if rows:
            xs[L] = torch.cat(rows, 0)
    elif k.startswith("moegate_w|L"):
        L = k.split("|L")[1]
        if d[k]:
            ws[L] = d[k][0]["w"]
            bs[L] = d[k][0]["b"]
            wbs[L] = d[k][0].get("wb")          # 线性层 bias(进 logit)
common = sorted(set(xs) & set(ws), key=int)
cap = {
    "x_mlp": {L: xs[L] for L in common},
    "gates": {L: ws[L] for L in common},
    "gate_bias": {L: bs[L] for L in common},
    "gate_linear_bias": {L: wbs.get(L) for L in common},
    "cfg": {
        "model": os.path.basename(model_dir.rstrip("/")),
        "num_experts_per_tok": cfg_j["num_experts_per_tok"],
        "scoring_func": cfg_j.get("scoring_func"),
        "n_routed_experts": cfg_j.get("n_routed_experts")
        or cfg_j.get("num_experts") or cfg_j.get("num_local_experts"),
        "topk_method": cfg_j.get("topk_method"),
        "num_hash_layers": cfg_j.get("num_hash_layers", 0),
        # 分组路由(DeepSeek-V3 系):两段选择,margin 形态完全不同
        "n_group": cfg_j.get("n_group", 1),
        "topk_group": cfg_j.get("topk_group", 1),
    },
}
torch.save(cap, out_p)
nb = sum(1 for L in common if bs[L] is not None)
print(f"打包 {len(common)} 层 | 带 bias {nb} 层 | token 行 "
      f"{sum(v.shape[0] for v in cap['x_mlp'].values())} | "
      f"scoring={cap['cfg']['scoring_func']} topk={cap['cfg']['num_experts_per_tok']}")
