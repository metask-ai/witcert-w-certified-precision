/- Q11 判别链的机器裁决实例(2026-08-04)。

  每条定理是一次推断的**可判定验证**:`by decide` 展开 premisesHold 对
  登记字段逐一对账 —— 编译通过 = 推断受控;负例定理证明历史上的无效
  推断在本演算下**构造不出来**。数据由 tools/adjudication_export.py 从
  产物 JSON 机械导出,不许手写。-/
import WitCert.AdjudicationData

namespace WitCert.Adjudication

/-! ## 负例一:q6o 混杂错误(TinyKG 10770 更正的形式化)

    历史推断:"串行(W1)干净 / 并发(W4)劣化 ⇒ 腐坏并发依赖"。
    两臂在已登记中介 evict128/evict4 上不同(0/0 vs 216/215)且未声明
    为中介 —— 前提不成立,结论构造不出。 -/
theorem q6o_naive_inference_rejected :
    ¬ premisesHold ⟨q6o, q6n, [.workers], []⟩ := by decide

/-- 同一比较,**显式声明驱逐为并发的中介**后才受控 —— 结论被迫写成
    "W4 经驱逐致劣化"(因果通路显式),这正是 q6p3-q6p9 后来证实的
    结构。演算不禁止这条推断,只强迫它诚实。 -/
def q6o_honest : CausalFinding :=
  ⟨⟨q6o, q6n, [.workers], [.evict128, .evict4]⟩, by decide, by decide⟩

/-! ## 负例二:跨代码比较(review P0-1 的形式化)

    q6n 与 q6p2 同配置但 codeTag 不同(efb8e95 vs e22d5d8)——
    把它们的 acc 差读作"run-to-run 方差"是无效推断。 -/
theorem cross_code_comparison_rejected :
    ¬ premisesHold ⟨q6n, q6p2, [], []⟩ := by decide

/-! ## 正例:q6p3 环判别 + q6p5 分池解离(同 codeTag=e22d5d8 内) -/

/-- q6p3:双环联合操纵(1025 vs 513),驱逐为声明中介。
    结论粒度:**环容量组**(联合操纵不许归因到单池)。效应 +167‰。 -/
def q6p3_ring_discriminator : CausalFinding :=
  ⟨⟨q6p3ring1025, q6p3ring513, [.ring128, .ring4],
    [.evict128, .evict4]⟩, by decide, by decide⟩

/-- q6p5-A:仅操纵 c128 环(1025→513),仅 evict128 为中介,
    对照零驱逐基线 —— 效应 0‰:**c128 驱逐无害**(阴性发现)。 -/
def q6p5_c128_null : CausalFinding :=
  ⟨⟨q6p5c128, q6p3ring1025, [.ring128], [.evict128]⟩, by decide, by decide⟩

/-- q6p5-B:仅操纵 c4 环,仅 evict4 为中介 —— 效应 -333‰:
    **c4 驱逐致害**。与上一条构成双解离。 -/
def q6p5_c4_harm : CausalFinding :=
  ⟨⟨q6p5c4, q6p3ring1025, [.ring4], [.evict4]⟩, by decide, by decide⟩

/-- 双解离的机器复述:同一基线、互补操纵,一零一负。 -/
theorem dissociation :
    q6p5_c128_null.effectPm = 0 ∧ q6p5_c4_harm.effectPm = -333 := by decide

/-! ## q6p11:第 4 次解离复现(同轮双臂,天然同 codeTag/probeSet) -/

/-- q6p11 双臂互为对照:联合操纵双环方向相反,双驱逐皆中介。
    效应 -250‰,与 q6p5/q6p6/q6p7 同向 —— c4 驱逐致害第 4 次受控复现。 -/
def q6p11_dissociation : CausalFinding :=
  ⟨⟨q6p11c4, q6p11c128, [.ring128, .ring4],
    [.evict128, .evict4]⟩, by decide, by decide⟩

theorem q6p11_effect : q6p11_dissociation.effectPm = -250 := by decide

/-! ## q6p14:必要性消融(机制链收口轮) -/

/-- 预填 extra 贡献消融:同轮双臂,操纵 ablateExtra;驱逐计数是
    **后处理变量**(消融毁输出 → 生成行为变 → 驱逐数变),按因果语义
    声明为中介而非混杂。效应 -667‰(0.000 vs 0.667)——
    预填 extra 读是任务必要通道。 -/
def q6p14_ablation : CausalFinding :=
  ⟨⟨q6p14ablate, q6p14ctl, [.ablateExtra],
    [.evict128, .evict4]⟩, by decide, by decide⟩

theorem q6p14_effect : q6p14_ablation.effectPm = -667 := by decide

/-! ## 观测趋势(非受控 —— 演算自审实例)

    剂量五点(evict4: 0/227/289/353/1030 → acc: 1.000/0.917/0.750/
    0.667/0.417)横跨三个 codeTag 与不同 probeSet —— 任意两点的受控
    比较都会被 premisesHold 拒绝。review #2 中作者本试图将其编码为
    因果定理,被自己的演算挡下;故仅以**观测趋势**入档(严格单调),
    因果地位由受控的 q6p5/q6p6/q6p7 解离对承担。 -/
theorem dose_trend_observational :
    q6p3ring1025.reads .evict4 < q6p7c4.reads .evict4 ∧
    q6p7c4.reads .evict4 < q6p6c4.reads .evict4 ∧
    q6p6c4.reads .evict4 < q6p5c4.reads .evict4 ∧
    q6p5c4.reads .evict4 < q6p9c4.reads .evict4 ∧
    q6p9c4.accPm < q6p5c4.accPm ∧ q6p5c4.accPm < q6p6c4.accPm ∧
    q6p6c4.accPm < q6p7c4.accPm ∧ q6p7c4.accPm < q6p3ring1025.accPm := by
  decide

/-- 且它**不是**受控比较:五点中相邻两点的直接比较被演算拒绝
    (示例:q6p5c4 与 q6p6c4 跨 codeTag 且 probeSet 不同)。 -/
theorem dose_pairs_not_controlled :
    ¬ premisesHold ⟨q6p6c4, q6p5c4, [.ring4], [.evict4]⟩ := by decide

/-! ## q11t2:修复干预(46 轮判别链收官) -/

/-- decode extra 逻辑→物理翻译干预:同轮双臂,操纵 decodeTranslate,
    **零中介豁免** —— 驱逐数两臂相等(20/20),混杂全部对齐,这是
    整条链上前提最干净的一次比较。效应 +500‰(1.000 vs 0.500):
    decode extra 未翻译逻辑读是 Q11 伤害通道(干预式因果确认)。
    机制:恒等映射仅在零驱逐+单请求下侥幸成立;翻译后非驻留条目
    折 -1(诚实驱逐语义),掉 ~26% extra 行仍 1.000。 -/
def q11t2_fix : CausalFinding :=
  ⟨⟨q11t2fix, q11t2ctl, [.decodeTranslate], []⟩, by decide, by decide⟩

theorem q11t2_effect : q11t2_fix.effectPm = 500 := by decide

/-! ## 税制合成健全性(实例) -/
example :
    ([Verdict.pass, .partialV, .pass].foldl Verdict.weakest .pass)
      = .partialV := by decide

end WitCert.Adjudication
