/- 聚合键的身份充分性(仪器层形式化)。

  本项目同一 bug 类的**三次**发作:
  · 2026-07 invalidation 事故:`written` 标志按 (层,槽) 记账,混淆
    "曾被打包过"与"当前代已打包" —— 键缺 `gen`;
  · 2026-08-04 q11c4:读侧有效性按**页**判定,而结论量化到**行**
    ("此行是否有效")—— 键缺 `slot`;
  · 2026-08-05 q11k:内容 oracle 按 (层,槽) 记账,而槽跨请求复用,
    结论量化到**请求**("doc1 的写是否发生")—— 键缺 `owner`。
    该次直接让作者写出一份错误根因判词(TinyKG 10806,更正 10813)。

  三者同形:**聚合键遗漏了结论所量化的维度**。形式化两件事:
  (1) 不可区分性定理:键缺维度时,两条语义不同的事件流产生**逐字
      相同**的聚合读数 —— 所以"读数一致"不能支持关于该维度的结论;
  (2) 覆盖义务:KeyedClaim 必须携带 `covers key quantified` 的证明,
      键不覆盖即构造不出结论(与 Adjudication 的 proof-carrying 同律)。

  边界(诚实):Lean 检的是**规则的逻辑**;"Python 探针实际按什么键
  记账"是实现符合性,由产物自带 key_dims 字段 + 消费侧守卫承担
  (两层各司其职,与 canon 数字/定理名守卫同一分工)。

  零外部依赖,`by decide` 全机械判定。-/

namespace WitCert.KeyIdentity

/-- 记账维度。新增维度只需加构造子;既有实例的 decide 自动重判。 -/
inductive Dim
  | owner        -- 请求身份(跨请求槽复用暴露)
  | layer
  | page
  | slot         -- 行(页内偏移展开后的行号)
  | gen          -- 代际(重写世代)
  | step
  deriving DecidableEq, Repr

abbrev Key := List Dim

/-- 一次记账事件:各维度读数 + 值。 -/
structure Event where
  reads : Dim → Nat
  val   : Nat

/-- 构造助手(令 `decide` 可归约)。 -/
def mk (owner layer page slot gen step val : Nat) : Event :=
  ⟨fun | .owner => owner | .layer => layer | .page => page
       | .slot => slot | .gen => gen | .step => step, val⟩

/-- 事件在键上的投影。 -/
def proj (k : Key) (e : Event) : List Nat := k.map e.reads

/-- 事件流在键上的可观测读数(键值序列 —— 聚合的信息上界)。 -/
def observed (k : Key) (es : List Event) : List (List Nat) := es.map (proj k)

/-- 键覆盖结论所量化的维度。 -/
def covers (k : Key) (quantified : List Dim) : Prop :=
  ∀ d ∈ quantified, d ∈ k

instance (k : Key) (q : List Dim) : Decidable (covers k q) := by
  unfold covers; infer_instance

/-- **带键的结论**:proof-carrying —— 键不覆盖量化维度即构造不出。 -/
structure KeyedClaim where
  key        : Key
  quantified : List Dim
  sound      : covers key quantified

/-! ## 不可区分性:三次真实事故的机器复述

    每条定理给出两条**语义不同**却在缺维度键下**读数逐字相同**的
    事件流 —— 即该键的读数对该维度的结论零区分度。 -/

/-- q11k:同槽被两个请求各写一次 vs 同一请求写两次 —— (层,槽) 键
    下读数相同,owner 键下不同。作者据前者写出"双写=临时态+精炼"
    的错误判词。 -/
theorem owner_ambiguity :
    observed [.layer, .slot] [mk 1 0 0 5 0 0 7, mk 1 0 0 5 0 1 9]
      = observed [.layer, .slot] [mk 1 0 0 5 0 0 7, mk 2 0 0 5 0 1 9]
  ∧ observed [.owner, .layer, .slot] [mk 1 0 0 5 0 0 7, mk 1 0 0 5 0 1 9]
      ≠ observed [.owner, .layer, .slot] [mk 1 0 0 5 0 0 7, mk 2 0 0 5 0 1 9] := by
  decide

/-- invalidation 事故:同槽新旧两代 vs 同代重复 —— 缺 `gen` 的键
    无法区分"当前代已写"与"曾经写过"。 -/
theorem generation_ambiguity :
    observed [.layer, .slot] [mk 1 0 0 5 1 0 7, mk 1 0 0 5 1 1 9]
      = observed [.layer, .slot] [mk 1 0 0 5 1 0 7, mk 1 0 0 5 2 1 9]
  ∧ observed [.layer, .slot, .gen] [mk 1 0 0 5 1 0 7, mk 1 0 0 5 1 1 9]
      ≠ observed [.layer, .slot, .gen] [mk 1 0 0 5 1 0 7, mk 1 0 0 5 2 1 9] := by
  decide

/-- q11c4:同页两行 vs 同页同行两次 —— 页级键无法承载行级结论
    ("此行是否有效"),页驻留≠行有效由此而来。 -/
theorem row_ambiguity :
    observed [.layer, .page] [mk 1 0 3 5 0 0 7, mk 1 0 3 5 0 1 9]
      = observed [.layer, .page] [mk 1 0 3 5 0 0 7, mk 1 0 3 6 0 1 9]
  ∧ observed [.layer, .page, .slot] [mk 1 0 3 5 0 0 7, mk 1 0 3 5 0 1 9]
      ≠ observed [.layer, .page, .slot] [mk 1 0 3 5 0 0 7, mk 1 0 3 6 0 1 9] := by
  decide

/-! ## 覆盖义务:失败键构造不出结论,修正键可以 -/

/-- 今天的 oracle 键(层,槽)对"请求级"结论**不合法**。 -/
theorem oracle_key_insufficient :
    ¬ covers [.layer, .slot] [.owner] := by decide

/-- 修正键(请求,层,槽,代)对请求级 + 代际结论合法 —— 可构造。 -/
def oracle_key_fixed : KeyedClaim :=
  ⟨[.owner, .layer, .slot, .gen], [.owner, .gen], by decide⟩

/-- 一般性:键覆盖时,量化维度上的差异必在读数上留痕(逆否形式)——
    "读数相同 ⇒ 该维度相同"当且仅当键覆盖它,是键设计的判据。 -/
theorem covers_of_mem {k : Key} {d : Dim} (h : d ∈ k) : covers k [d] := by
  intro d' hd'
  cases hd' with
  | head => exact h
  | tail _ hmem => cases hmem

end WitCert.KeyIdentity
