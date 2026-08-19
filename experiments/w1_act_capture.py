# -*- coding: utf-8 -*-
"""W1(采集,单卡):逐模块输入激活二阶矩 + MoE router 素材 —— W2 三发 kill-shot 的数据源。

设计(docs/research/p3-scoping/W1-CAPTURE-PLAN.md;判读阈值在 W2 脚本定稿):
  - **不落全量原始行**(K0' 教训:n≫d 才有谱,但 n×d 落盘爆炸)——
    每 (层, 流, 相, uid 奇偶) 在线累加 Σ=XᵀX(fp32)与 n:
      · 相 = prefill / decode(手动两段前向,不靠形状猜);
      · uid 奇偶双 Σ = split-half 留出(W2-a),prefill Σ vs decode Σ = 转移(W2-b);
  - 三条激活流(同层线性组共享输入,q/k/v 同源、gate/up 同源,只采代表):
      x_attn = self_attn.q*_proj 的输入;x_o = self_attn.o_proj 的输入;
      x_mlp = layer.mlp 模块的输入(Qwen MLP 与 DeepseekMoE 通吃);
  - router 模式(W1_ROUTER=1):额外落 x_mlp 原始行(逐相 cap)+ 每 MoE 层
    gate 权重(fp16)+ moe 配置 —— margin 分布离线重算(logits = x @ Wᵀ),
    不依赖各版本 gate.forward 返回值形状;
  - 每流小样本原始行(cap 256)作量纲/有限性抽检;
  - 验收(跑完立即自检,零触发=采集失败):每选中层每流每相 n>0;
    router 模式 gate 层数>0 且 x_mlp 原始行>0;全部有限。

用法(env):
  W1_MODEL=<hf 目录>  W1_OUT=<输出.pt 前缀>  W1_ROUTER=0/1
  W1_PROMPT_TOKENS=2048  W1_DECODE_STEPS=128  W1_LAYER_STRIDE=4
  W1_RAWCAP=256  W1_MLP_RAWCAP=8192  W1_SMOKE=1(2 prompt/8 步/256 tok)
  python3 experiments/w1_act_capture.py
"""
import json
import os
import sys

import torch

EXP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, EXP)
from provenance import stamp  # noqa: E402

# 与 p101 逐字同源的 16 条 prompt(口径连续性;uid = 下标)
BASES = [
    "Summarize the history of the printing press and its impact on literacy. ",
    "def quicksort(arr): explain this algorithm step by step with an example. ",
    "A train leaves at 60 km/h and another at 80 km/h in the opposite direction; reason about when they meet. ",
    "Translate the following sentence into French and explain the grammar: the cat sat on the mat. ",
    "List the planets of the solar system with one distinguishing fact each. ",
    "What causes ocean tides? Answer for a curious ten-year-old. ",
    "Produce a JSON object describing a fictional book with title, author, year, and genres. ",
    "If all bloops are razzies and some razzies are lazzies, what can we conclude? Think carefully. ",
    "Explain the difference between TCP and UDP with a real-world analogy. ",
    "Write a haiku about autumn rain, then explain each line's imagery. ",
    "A farmer has chickens and rabbits, 35 heads and 94 legs; solve step by step. ",
    "Describe how photosynthesis converts light into chemical energy. ",
    "Refactor this pseudocode to remove the nested loop: for i in A: for j in B: if i==j: out.append(i). ",
    "What were the main causes of the fall of the Western Roman Empire? ",
    "Explain Bayes' theorem with a medical-testing example and actual numbers. ",
    "Compose a short dialogue between a skeptic and an optimist about weather forecasts. ",
]

SMOKE = os.environ.get("W1_SMOKE") == "1"
# .get 而非 []:本模块被 w2cp 等复用 BASES 时不得因缺 env 炸 import
MODEL = os.environ.get("W1_MODEL")
OUT = os.environ.get("W1_OUT")
ROUTER = os.environ.get("W1_ROUTER") == "1"
P_TOK = 256 if SMOKE else int(os.environ.get("W1_PROMPT_TOKENS", "2048"))
D_STEP = 8 if SMOKE else int(os.environ.get("W1_DECODE_STEPS", "128"))
STRIDE = int(os.environ.get("W1_LAYER_STRIDE", "4"))
RAWCAP = int(os.environ.get("W1_RAWCAP", "256"))
MLP_RAWCAP = int(os.environ.get("W1_MLP_RAWCAP", "8192"))
PROMPTS = BASES[:2] if SMOKE else BASES

_PHASE = {"cur": "prefill", "uid": 0}     # hook 读的全局相位/身份(主循环显式翻转)
_ACC, _RAW, _NONFIN = {}, {}, {"n": 0}


def _accum(key, x):
    """x: [rows, d] -> Σ/n 累加 + 小样本原始行。key=(layer, stream)。"""
    ph, uid = _PHASE["cur"], _PHASE["uid"]
    x = x.detach()
    if not torch.isfinite(x).all():          # 量纲纪律:不 crash,记账并剔除
        _NONFIN["n"] += int((~torch.isfinite(x)).any(-1).sum())
        x = x[torch.isfinite(x).all(-1)]
        if x.shape[0] == 0:
            return
    xf = x.float()
    k = key + (ph, uid % 2)
    st = _ACC.get(k)
    if st is None:
        d = xf.shape[-1]
        st = _ACC[k] = {"sigma": torch.zeros(d, d, device=xf.device), "n": 0}
    st["sigma"] += xf.T @ xf
    st["n"] += xf.shape[0]
    cap = MLP_RAWCAP if (ROUTER and key[1] == "x_mlp") else RAWCAP
    rk = key + (ph,)
    lst = _RAW.setdefault(rk, {"rows": [], "n_seen": 0, "uids": []})
    lst["n_seen"] += xf.shape[0]
    have = sum(t.shape[0] for t in lst["rows"])
    if have < cap:
        take = min(cap - have, xf.shape[0])
        step = max(1, xf.shape[0] // take)
        _rows = x[::step][:take].half().cpu()
        lst["rows"].append(_rows)
        lst["uids"].extend([uid] * _rows.shape[0])


def _mk_hook(key):
    def h(module, args, kwargs=None):
        x = args[0] if args else kwargs["hidden_states"]
        _accum(key, x.reshape(-1, x.shape[-1]))
    return h


def find_streams(model):
    """按后缀发现三条流的挂点;返回 {(layer_idx, stream): module}。fail-loud。"""
    layers = model.model.layers
    picked = {}
    sel = list(range(0, len(layers), STRIDE))
    for i in sel:
        L = layers[i]
        qp = None
        for name in ("q_proj", "q_a_proj", "q_b_proj"):
            qp = getattr(L.self_attn, name, None)
            if qp is not None:
                break
        assert qp is not None, f"L{i} 未找到 q 侧投影"
        picked[(i, "x_attn")] = qp
        assert hasattr(L.self_attn, "o_proj"), f"L{i} 无 o_proj"
        picked[(i, "x_o")] = L.self_attn.o_proj
        picked[(i, "x_mlp")] = L.mlp
    return picked, sel


def find_gates(model):
    """MoE gate 发现:mlp 下名为 gate 的子模块,weight 形状 [n_experts, hidden]。"""
    gates = {}
    for i, L in enumerate(model.model.layers):
        g = getattr(L.mlp, "gate", None)
        w = getattr(g, "weight", None) if g is not None else None
        if w is not None and w.dim() == 2 and w.shape[0] < w.shape[1]:
            gates[i] = w.detach().half().cpu()
    return gates


def main():
    assert MODEL and OUT, "需设 W1_MODEL 与 W1_OUT"
    from transformers import AutoModelForCausalLM, AutoTokenizer
    # 老 remote-code(V2-Lite 2024 era)× 新 transformers 的 cache API 断裂:
    # get_usable_length 已被移除,非滑窗语义 = get_seq_length。仅缺失时补别名。
    try:
        from transformers.cache_utils import DynamicCache
        if not hasattr(DynamicCache, "get_usable_length"):
            DynamicCache.get_usable_length = (
                lambda self, new_seq_length=0, layer_idx=0:
                self.get_seq_length(layer_idx))
    except ImportError:
        pass
    tok = AutoTokenizer.from_pretrained(MODEL, trust_remote_code=True)
    # 不用 device_map(需 accelerate,4090 sgl 环境无):两个目标模型都
    # 整卡放得下,直接 .to("cuda")
    kw = dict(torch_dtype=torch.bfloat16, trust_remote_code=True)
    try:
        model = AutoModelForCausalLM.from_pretrained(
            MODEL, attn_implementation="eager", **kw)
    except TypeError:                 # remote-code 模型不认 attn_implementation
        model = AutoModelForCausalLM.from_pretrained(MODEL, **kw)
    model = model.to("cuda")
    model.eval()
    picked, sel = find_streams(model)
    handles = [m.register_forward_pre_hook(_mk_hook(k)) for k, m in picked.items()]
    gates = find_gates(model) if ROUTER else {}
    if ROUTER:
        assert gates, "router 模式但未发现任何 gate —— 模型不是 MoE 或发现逻辑失配"

    dev = next(model.parameters()).device
    for uid, base in enumerate(PROMPTS):
        text = (base * 400)[: P_TOK * 6]
        ids = tok(text, return_tensors="pt").input_ids[:, :P_TOK].to(dev)
        _PHASE.update(cur="prefill", uid=uid)
        # 老 remote-code 断言 attention_mask 非空(新 transformers 不再默认造):
        # 全程显式传 2D 全 1 mask(past+当前全长),对新模型同样合法
        cur = ids.shape[1]
        with torch.no_grad():
            out = model(ids, use_cache=True,
                        attention_mask=torch.ones(1, cur, dtype=torch.long,
                                                  device=ids.device))
        _PHASE["cur"] = "decode"
        past, nxt = out.past_key_values, out.logits[:, -1:].argmax(-1)
        for _ in range(D_STEP):
            cur += 1
            with torch.no_grad():
                out = model(nxt, past_key_values=past, use_cache=True,
                            attention_mask=torch.ones(1, cur, dtype=torch.long,
                                                      device=ids.device))
            past, nxt = out.past_key_values, out.logits[:, -1:].argmax(-1)
        print(f"uid {uid} done", flush=True)

    for h in handles:
        h.remove()

    # ---- 验收:覆盖 → 量纲(零触发 = 采集失败,当场红) ----
    miss = [(i, s, ph) for i in sel for s in ("x_attn", "x_o", "x_mlp")
            for ph in ("prefill", "decode")
            if sum(v["n"] for k, v in _ACC.items() if k[:2] == (i, s) and k[2] == ph) == 0]
    assert not miss, f"零触发流:{miss}"
    if ROUTER:
        xm = sum(sum(t.shape[0] for t in v["rows"])
                 for k, v in _RAW.items() if k[1] == "x_mlp")
        assert xm > 0, "router 模式无 x_mlp 原始行"

    cfg = model.config
    moe_cfg = {k: getattr(cfg, k) for k in
               ("n_routed_experts", "num_experts_per_tok", "n_group",
                "topk_group", "norm_topk_prob", "routed_scaling_factor",
                "n_shared_experts", "num_experts", "moe_intermediate_size")
               if hasattr(cfg, k)}
    blob = {
        # Σ 必须 fp32 落盘:massive 激活的二阶矩对角可达 1e5+,fp16(上限
        # 65504)溢出成 Inf —— 首轮 Qwen7B 实测 52/84 矩阵含非有限元。
        # 落盘前有限断言 + sigma_dtype 声明(test_key_conformance 存储域检查)
        "acc": {str(k): {"sigma": v["sigma"].cpu(),
                         "sigma_diag_fp32": v["sigma"].diagonal().cpu().clone(),
                         "n": v["n"]} for k, v in _ACC.items()},
        "raw": {str(k): {"rows": torch.cat(v["rows"]) if v["rows"] else None,
                         "uids": v["uids"], "n_seen": v["n_seen"]}
                for k, v in _RAW.items()},
        "gates": gates, "moe_config": moe_cfg,
        "layers_selected": sel, "layer_stride": STRIDE,
        "caliber": [
            "Σ=XᵀX fp32 累加、fp16 落盘(对角另存 fp32);key=(层,流,相,uid%2)",
            "x_attn 即 q/k/v 共享输入;x_mlp 即 gate/up/router 共享输入;"
            "down_proj 输入(inter 维)本轮不采,W2 口径自注",
            "prefill/decode 相位由主循环显式翻转,非形状推断;温度 0",
            f"prompt=p101 同源 16 条,P_TOK={P_TOK},D_STEP={D_STEP}",
            f"非有限行剔除计数={_NONFIN['n']}(>0 需在 W2 判读时说明)",
        ],
        "nonfinite_rows_dropped": _NONFIN["n"],
        "manifest": stamp(run_id=os.environ.get("RUN_ID", "w1_capture"), seed=None,
                          stack=f"transformers hooks, {MODEL.split('/')[-1]}, bf16"),
        "generated_by": "w1_act_capture.py",
    }
    torch.save(blob, OUT + ".pt")
    for k, v in _ACC.items():
        assert torch.isfinite(v["sigma"]).all(), f"Σ 非有限:{k} —— 拒绝落盘"
        assert v["sigma"].dtype == torch.float32, f"Σ dtype 漂移:{k}"
    rep = {"model": MODEL, "router_mode": ROUTER, "smoke": SMOKE,
           "layers": sel, "n_gates": len(gates),
           "streams": {str(k): v["n"] for k, v in _ACC.items()},
           "nonfinite_rows_dropped": _NONFIN["n"],
           "sigma_dtype": "float32",
           "manifest": blob["manifest"], "generated_by": "w1_act_capture.py"}
    json.dump(rep, open(OUT + ".json", "w"), ensure_ascii=False, indent=1)
    print("W1_CAPTURE_OK", OUT, "gates=", len(gates),
          "streams=", len(_ACC), "nonfinite=", _NONFIN["n"])


if __name__ == "__main__":
    main()
