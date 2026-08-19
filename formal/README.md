# WitCert 形式化层

## 为什么需要它

本项目两次栽在"看似合理的化简"上:
1. **2026-07-27 事故一**:注意力加权的「界离散度」形式 TV 证书 —— 两 token 反例,真实 TV 为其 7.8 倍;
2. **2026-07-27 事故二**:M3 kernel 为省一次矩阵乘,把 A = Σ p̃ e^{u_t} 换成"先平均方差再开根" —— δ=1e-8 下实测违约 1.71%。

两次都通过了人工审阅与大量数值实验才被外部评审抓住。结论:**数学真理源不能是一段 Markdown,必须是 CI 中无法绕过的可机器检查对象。**

## 四层结构与当前状态

**零依赖层(`standalone/`,秒级 CI 闸门,全部无 `sorryAx`)**

| 定理 | 文件 | 内容 | 公理依赖 |
|---|---|---|---|
| L4 refinement | `Refinement.lean` | 块内权重恒定 ⟹ 分块累加器 ≡ 逐 token 求和(**M3 事故的那步优化**) | `[propext]` |
| L4 反面 | `Refinement.lean` | 块内权重变化时恒等式失效 | `decide` |
| L2 组合核心 | `Factorial.lean` | `6^k · k! ≤ (2k+1)!`(proxy = 方差 s²/12 的算术根源) | `[propext, Quot.sound]` |
| L3 预算算术 | `Budget.lean` | 各项 ≤ δ_loc ⟹ 和 ≤ n·δ_loc;与联合界合成得请求级 soundness | **无任何公理** |
| L1 AM-GM 核心 | `EForm.lean` | `2x ≤ x² + 1`(实数域即 x + 1/x ≥ 2,逐点界的下侧保证) | `[propext, Quot.sound]` |
| L1 传播 | `EForm.lean` | 逐点 d ≤ u ⟹ Σd ≤ Σu(**撤回公式违反的正是这条**) | `[propext]` |

运行:`./check_standalone.sh`(同时检查编译错误、`sorryAx` 依赖、定理存在性)

**Mathlib 层(`WitCert/`,实数与测度论版本)——全部已机器检查,无 `sorryAx`**

| 层 | 定理 | 内容 |
|---|---|---|
| **L1** | `tv_le_eform` | **主定理**:\|ε_t\| ≤ c_t ⟹ TV(p,p̃) ≤ ½((E_p̃[e^c])²−1) |
| L1 | `one_le_Acert_mul_Znorm` | 1 ≤ A·Z(经 Jensen + exp 凸性,替代 Cauchy–Schwarz) |
| L1 | `pointwise_ratio_bound` | 逐点比值界(含 AM-GM 步) |
| **L2** | `sinh_le_mul_exp_sq_div_six` | **sinh x ≤ x·e^{x²/6}**(泰勒逐项比较)⟹ proxy = 方差 s²/12 |
| L2 | `six_pow_mul_factorial_le` | 6^n·n! ≤ (2n+1)!(逐项比较的组合核心) |
| **L3** | `request_budget_sound` | 测度论联合界 + 预算:n 个事件各 ≤ δ_loc 且 n·δ_loc ≤ δ_req ⟹ P(∪) ≤ δ_req |
| **L4** | `A_blockwise_eq_perToken` | ℝ 版 refinement:块内权重恒定 ⟹ 分块累加器 ≡ 逐 token 求和 |

公理依赖均为 `[propext, Classical.choice, Quot.sound]`(Lean 标准公理),**无 `sorryAx`**。
完整验证:`./check_all.sh`

**分层原因**:把每个定理拆成「代数/组合核心」与「分析/测度部分」,前者零依赖秒级可查、可当 CI 闸门;
后者需 Mathlib。两次事故(界离散度形式、聚合式)**全部发生在代数核心层**,而非分析层——
故零依赖层的守卫价值最高。

## L4 为何最优先

`Refinement.lean` 证明的正是**导致事故二的那一步优化**:当 u 在块内恒定时(WitCert 的 scale 逐块 +
tile 整除块保证),分块累加器与逐 token 求和**恒等**。有了它,任何 agent 再提出"把公式化简成更便宜的
累加器",必须先证明等价或上界关系——证明失败就不能进 kernel。

## 编译

```bash
# 秒级 CI 闸门(零依赖,检查 L1/L2/L3 核心 + L4 refinement)
./check_standalone.sh

# 全量(需 Mathlib;macOS ARM 上预编译 cache 二进制 dyld 失败,须源码编译)
export PATH="$HOME/.elan/bin:$PATH" && lake build
```

**验证输出**(2026-07-27 实测):
```
[standalone/Refinement.lean] PASS (2 个定理已机器检查)
[standalone/Factorial.lean]  PASS (3 个定理已机器检查)
[standalone/Budget.lean]     PASS (2 个定理已机器检查)
[standalone/EForm.lean]      PASS (2 个定理已机器检查)
=== 全部通过:L1核心/L2核心/L3核心/L4 refinement 均无 sorryAx ===
```

## 诚实说明

带 `sorry` 的定理**尚未机器检查**,它们目前的可信度来自:
- `src/witcert/operators/cert_reference.py` 的高精度可执行实现;
- `tests/test_formal_counterexamples.py` 的属性测试(mgf 引理 400 例、e-form soundness 600 例、
  refinement 等价 300 例、撤回式反例证伪、单调性 200 例);
- `tests/test_certificates.py` 的 50 万次对抗测试与两个历史反例守卫。

**已证明的**(可写入论文):L1 主定理、L2 MGF 界、L3 请求级预算、L4 refinement,
全部在 Lean 4 + Mathlib 中机器检查,无 `sorryAx`。

**尚未覆盖的**(论文**不得**声称"端到端形式化验证"):
1. **随机源**:定理设 u ~ U[−½,½) 为理想独立均匀变量;实现用 32 位 Philox(离散、给定 seed 后确定)。
   正确表述是"在 Philox 输出可视为独立离散均匀变量的假设下"。
2. **浮点**:定理在 ℝ 上;实现为 fp32/fp16(scale 存储、exp/logsumexp、Philox 位运算)。
   浮点误差界宜用 Gappa 单独验证,或让 kernel 返回带已证明安全余量的上界。
3. **kernel 本身**:GPU 实现与已证明公式的一致性由差分测试(`tests/test_tiled_contract.py`,
   Δcert=6.0e-7、0 违约)保证,不是形式化验证。

因此可诚实声称的是:

> "核心请求级风险定理由机器检查(Lean 4 + Mathlib,无 sorryAx),
> 并通过可执行 refinement 测试保证 GPU 实现与已证明的数学对象一致。"
