"""证书回归测试(红队审计后必过):两token反例 + 随机对抗 + 旧公式必须被反例杀死。
python3 tests/test_certificates.py
"""
import math, os, random, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))


def tv_exact(pt, eps):
    u = [pt[i] * math.exp(-eps[i]) for i in range(len(pt))]
    U = sum(u)
    return 0.5 * sum(abs(pt[i] - u[i] / U) for i in range(len(pt)))


def cert_D(pt, c):
    Ec = sum(pt[i] * math.exp(c[i]) for i in range(len(pt)))
    return 0.5 * (Ec * Ec - 1)


def cert_old_invalid(pt, c):
    cbar = sum(pt[i] * c[i] for i in range(len(pt)))
    dev = sum(pt[i] * abs(c[i] - cbar) for i in range(len(pt)))
    cmax = max(c)
    return 0.5 * math.exp(2 * cmax) * (dev + cbar * (math.exp(cmax) - 1))


# T1 两token反例:旧公式必须违约,新公式必须成立
pt, c, eps = [0.5, 0.5], [0.1, 0.1], [0.1, -0.1]
tv = tv_exact(pt, eps)
assert tv > cert_old_invalid(pt, c), "旧公式竟然覆盖反例?"
assert tv <= cert_D(pt, c) + 1e-12, f"新公式违约: tv={tv} bound={cert_D(pt, c)}"
print(f"T1 反例: tv={tv:.6f} 旧界={cert_old_invalid(pt,c):.6f}(违约✓) 新界={cert_D(pt,c):.6f}(成立✓)")

# T2 随机对抗 50 万次(含极端符号、尖峰/平坦分布、大c)
random.seed(1)
viol = 0
for _ in range(500000):
    n = random.randint(2, 10)
    c = [random.uniform(0, 0.8) for _ in range(n)]
    mode = random.random()
    if mode < 0.4:
        eps = [ci * random.choice([-1, 1]) for ci in c]      # 极端符号
    elif mode < 0.7:
        eps = [ci * random.uniform(-1, 1) for ci in c]
    else:
        eps = [random.choice([1, -1]) * ci for ci in c]; eps[0] = -eps[0]
    w = [random.random() ** random.choice([1, 4]) for _ in range(n)]  # 含尖峰分布
    Z = sum(w); pt = [x / Z for x in w]
    if tv_exact(pt, eps) > cert_D(pt, c) + 1e-10:
        viol += 1
assert viol == 0, f"cert_D 对抗违约 {viol}"
print("T2 50万次对抗: cert_D 违约 0 ✓")

# T3 单调性:c 逐点增大界不应减小
pt = [0.3, 0.7]
b1, b2 = cert_D(pt, [0.1, 0.2]), cert_D(pt, [0.2, 0.3])
assert b2 >= b1
print("T3 单调性 ✓")
print("ALL CERT TESTS PASSED")

# ---- T6(2026-07-27 红队第九轮):聚合式证书的不 sound 性 ----
# M3 kernel 曾用 V̄=Σp̃V_t → u=√(2V̄ln) → ½(e^{2u}−1);正确式为 A=Σp̃e^{u_t} → ½(A²−1)。
# 反例机制:量化噪声压低某 token 的注意力时,先平均方差会隐藏其大方差。
def _agg_wrong(pt, V, ln):
    Vb = sum(p * v for p, v in zip(pt, V))
    return min(0.5 * math.expm1(2 * math.sqrt(2 * Vb * ln)), 1.0)

def _agg_right(pt, V, ln):
    A = sum(p * math.exp(min(math.sqrt(2 * v * ln), 50)) for p, v in zip(pt, V))
    return min(0.5 * (A * A - 1), 1.0)

random.seed(1)
S_, delta_ = 8192, 1e-8
ln_ = math.log(2 * S_ / delta_)
V_ = [0.0, 10.0 ** 2 / 3]
vw = vr = 0
for _ in range(200000):
    eps = random.uniform(-10.0, 10.0)
    m_ = max(0.0, eps)
    e1, e2 = math.exp(-m_), math.exp(eps - m_)
    Z = e1 + e2
    pt_ = [e1 / Z, e2 / Z]
    tv_ = abs(pt_[0] - 0.5)
    if tv_ > _agg_wrong(pt_, V_, ln_) + 1e-12:
        vw += 1
    if tv_ > _agg_right(pt_, V_, ln_) + 1e-12:
        vr += 1
print(f"T6 聚合式反例(δ=1e-8, 20万次): 错误式违约 {vw} ({vw/2000:.2f}%),正确式违约 {vr}")
assert vw > 1000, "反例失效(错误式应大量违约)——若此断言失败,说明测试本身退化"
assert vr == 0, f"正确式违约 {vr},sound 性被破坏"
print("T6 PASSED(错误式被反例杀死,正确式存活)")


# ---------------------------------------------------------------- 契约的度量类型检查
# 2026-07-31:给契约加度量类型后,论文里那条 存储→选择 的链**被拒绝** ——
# 存储段输出 kv_entry:rel_witness(无量纲比值),选择段输入 attn_dist:tv(概率质量),
# 原来的 a₂·b₁+b₂ 把两者直接相加,得到的量不属于任何一个度量。
# 形式化对应:formal/WitCert/Contract.lean 的 comp / #check_failure。
def _t_metric_typing():
    import sys, os
    _root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sys.path.insert(0, os.path.join(_root, "src"))
    sys.path.insert(0, _root)   # 发布仓布局:witcert 包在仓根
    from witcert.probe import contracts as C

    kv = C.Metric("kv_entry", "rel_witness")
    tv = C.Metric("attn_dist", "tv")
    c1 = C.Contract(name="store", a=1.0, b=0.02, m_in=C.Metric("kv_entry", "l2"), m_out=kv)
    c2 = C.Contract(name="select", a=1.0, b=0.003, m_in=tv, m_out=tv)

    # 阴性:跨度量必须被拒绝
    try:
        C.Chain().then(c1).then(c2)
        raise AssertionError("跨度量组合被放行了 —— 类型检查没生效")
    except C.MetricMismatch:
        pass
    # 阳性:同度量必须放行,且系数与 (C1) 一致
    ok = C.Chain().then(c1).then(
        C.Contract(name="s2", a=2.0, b=0.001, m_in=kv, m_out=kv)).compose()
    assert abs(ok.b - (2.0 * 0.02 + 0.001)) < 1e-12, "串联系数不符 (C1)"
    # 桥接:必须带已证定理才能换单位
    try:
        C.bridge("无证桥", kv, C.Metric("kv_entry", "tv"), 1.0, 0.0, proof="")
        raise AssertionError("无证桥被接受了")
    except ValueError:
        pass
    br = C.bridge("witness->tv", kv, C.Metric("kv_entry", "tv"), 1.0, 0.0,
                  proof="WitCert.Calculus.bridge_sound")
    assert br.is_bridge and br.proof
    # 桥只换度量不换对象
    try:
        C.bridge("跨对象", kv, tv, 1.0, 0.0, proof="X")
        raise AssertionError("跨对象的'桥'被接受了")
    except ValueError:
        pass
    print("T7 PASSED(跨度量组合被拒;同度量放行;无证桥与跨对象桥都被拒)")


_t_metric_typing()


# 2026-07-31 二审:**手工标签错误是类型系统防不住的**,只能靠把真实语义钉进用例。
# b_S 的 m_out/m_in 来自 softmax(索引 logits)(meters.topk_margin),度量是
# selector_dist:tv;一审曾手写成 attn_dist:tv 并接进注意力链。本用例锁死:
# 选择段契约的类型必须是 selector_dist,且接到注意力链上必须被拒。
def _t_selection_typing():
    import sys, os
    _root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sys.path.insert(0, os.path.join(_root, "src"))
    sys.path.insert(0, _root)   # 发布仓布局:witcert 包在仓根
    from witcert.probe import contracts as C
    sel = C.selection_contract(0.002, 0.0002)
    assert sel.m_in == C.M_SEL_TV and sel.m_out == C.M_SEL_TV, \
        "选择段度量被改回 attn_dist —— 那是一审犯过的标签错误"
    ch = C.v4_bridged_chain({0: 1.0}, {0: 0.3})
    try:
        ch.then(sel)
        raise AssertionError("选择段接上了注意力链 —— selector→attention 桥并不存在")
    except C.MetricMismatch:
        pass
    # 并联算子(三审):独立误差源在同一输出度量上相加。
    # 桥接后的选择项(m_out=attn)可并联;未桥接的(m_out=selector)必须被拒。
    br = C.empirical_selector_to_attn_bridge(2.0, 21, "截断集", "换手集")
    sel_attn = C.Chain().then(sel).then(br).compose()
    ch2 = C.v4_bridged_chain({0: 1.0}, {0: 0.3})
    ch2.also(sel_attn)
    assert abs(ch2.compose().b - 2.0 * 0.002) < 1e-12, "并联的 b 没按桥后单位相加"
    assert ch2.compose().tier == C.EMPIRICAL, "并联后档位没降到 empirical"
    try:
        C.v4_bridged_chain({0: 1.0}, {0: 0.3}).also(sel)
        raise AssertionError("未桥接的选择项被并联进注意力链")
    except C.MetricMismatch:
        pass
    # 经验桥必须写明测于哪/外推到哪
    try:
        C.empirical_selector_to_attn_bridge(2.0, 21, "", "")
        raise AssertionError("没写校准范围的经验桥被接受了")
    except ValueError:
        pass
    # 账本铁律:empirical 绝不入 certified 账本
    L = C.RequestLedger(0.01)
    assert L.empirical_event(can_fallback=True) == "fallback"
    assert L.empirical_event(can_fallback=False) == "degraded" and L.degraded
    assert L.certify_deterministic(True) == "certified"
    assert L.certify_probabilistic(1.0) == "fallback", "超预算的概率证书应回退"
    # 三审 P0:非法 δ 必须被拒(负值曾被接受并倒扣 delta_spent)
    L2 = C.RequestLedger(0.01)
    for bad in (-0.1, float("nan"), 1.5):
        try:
            L2.certify_probabilistic(bad)
            raise AssertionError("非法 δ 被账本接受:%r" % bad)
        except ValueError:
            pass
    L2.certify_probabilistic(1e-5, assumption="dither 条件独立(Tier B)")
    assert L2.assumptions == ["dither 条件独立(Tier B)"], "refinement 依据未留痕"
    r2 = L2.report()
    assert 0.0 <= r2["delta_spent"] <= 0.01, "不变量断言未生效"
    print("T8 PASSED(选择段钉死 selector_dist:tv,接注意力链被拒;并联/经验桥/账本铁律/输入校验齐)")


_t_selection_typing()
