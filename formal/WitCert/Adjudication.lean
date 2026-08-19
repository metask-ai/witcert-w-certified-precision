/- 实验裁决演算(工程管理的形式化层)。

  动机(2026-08-04,Q11 十一轮判别复盘):最贵的推理错误是 q6o——
  从"串行干净 / 并发劣化"得出"并发依赖"因果结论,而两臂在**驱逐数**
  这一已观测变量上也不同(0 vs 216),混杂未受控,推断无效(更正节点
  TinyKG 10770)。这类错误是纯逻辑错误,应当在"构造结论"处就被拒绝,
  而不是靠三轮后的复盘发现。

  本文件把"受控比较"做成证明义务:
  · Run:一轮实验的登记字段(配置混杂 + 观测中介 + 结果),数字由
    tools/adjudication_export.py 从产物 JSON 机械导出(AdjudicationData);
  · Comparison 携带**显式操纵变量与显式中介声明**——操纵环容量必然改变
    驱逐数(中介),豁免匹配的只能是声明过的中介,于是结论的因果通路
    被迫写明("W 经驱逐致腐坏"而非"W 致腐坏");
  · premisesHold 可判定:除操纵与声明中介外,全部登记字段两臂相等;
  · CausalFinding 是 proof-carrying 结构:premisesHold 的证明是字段,
    构造不出 = 推断无效,elaboration 失败即裁决;
  · Verdict 五级税制 + 最弱链合成(与论文 tier 语义同构)。

  零外部依赖(core Lean),`by decide` 全部机械判定。
  编译入口:formal/check_all.sh(不进 Export.lean —— 这是工程层,
  不计入论文定理数)。-/

namespace WitCert.Adjudication

/-- 登记字段全集。新增混杂必须加在这里 —— 加了字段而漏登记,所有既有
    比较的 premisesHold 会因缺 case 而编译失败,即"登记表强制完整"。 -/
inductive Field
  | workers      -- 并发度
  | ring128      -- c128 环容量(页)
  | ring4        -- c4 环容量(页)
  | codeTag      -- 被测代码(哈希 id;同测代码等价类由导出器裁决)
  | seed
  | probeSet     -- 探针/扰动开关(forensic / evict-ahead 等时序扰动源)
  | evict128     -- 观测中介:c128 实际驱逐数
  | evict4       -- 观测中介:c4 实际驱逐数
  | ablateExtra  -- 预填 extra 贡献消融开关(q6p14 判别变量)
  | decodeTranslate -- decode extra 逻辑→物理翻译开关(q11t2 干预变量)
  deriving DecidableEq, Repr

/-- 一轮实验:读数是 **Field 上的全函数** + 结果(acc 千分点 ‰)。
    review R1:此前 Run 用具名字段,往 Run 加新观测量而不登记 Field
    什么都不会失败(危险方向未守住);函数式定义使"未登记的观测量"
    在类型上不存在 —— 任何进入比较的量必经 Field 枚举。 -/
structure Run where
  reads : Field → Nat
  accPm : Nat

def proj (f : Field) (r : Run) : Nat := r.reads f

def REGISTERED : List Field :=
  [.workers, .ring128, .ring4, .codeTag, .seed, .probeSet,
   .evict128, .evict4, .ablateExtra, .decodeTranslate]

/-- review R2:REGISTERED 静默漏项 = 前提静默变弱。完备性定理钉死:
    删任何一项本定理即失败。 -/
theorem REGISTERED_complete : ∀ f : Field, f ∈ REGISTERED := by
  intro f; cases f <;> decide

/-- 受控比较:操纵一组变量(联合操纵削弱归因粒度 —— q6p3 双环同调只能
    得出"环容量组"结论,单池归因必须靠 q6p5 解离,该逻辑在此显式),
    并声明因果通路上的中介。 -/
structure Comparison where
  a           : Run
  b           : Run
  manipulated : List Field
  mediators   : List Field := []

/-- 前提:除操纵变量与**声明过的**中介外,所有登记字段两臂相等。 -/
def premisesHold (c : Comparison) : Prop :=
  ∀ f ∈ REGISTERED, f ∉ c.manipulated → f ∉ c.mediators →
    proj f c.a = proj f c.b

instance (c : Comparison) : Decidable (premisesHold c) := by
  unfold premisesHold; infer_instance

/-- 操纵实锤:声明操纵的每个字段两臂必须真的不同(review R3:
    否则可声明伪操纵得空结论)。 -/
def manipulationActive (c : Comparison) : Prop :=
  ∀ f ∈ c.manipulated, proj f c.a ≠ proj f c.b

instance (c : Comparison) : Decidable (manipulationActive c) := by
  unfold manipulationActive; infer_instance

/-- 因果发现:proof-carrying —— 没有前提证明就构造不出结论。
    **边界(诚实声明,review R4)**:中介声明是建模主张,演算只强迫
    其显式、不验证其真 —— 全字段声明为中介可空洞化前提,该滥用由
    人工/TinyKG 审计;税制中段排序任意,仅 pass 顶 / failMethod 底
    有语义;空链 foldl 得 pass,调用方须保证链非空。 -/
structure CausalFinding where
  cmp    : Comparison
  sound  : premisesHold cmp
  active : manipulationActive cmp

/-- 效应量(千分点 ‰,acc×1000;曾误称基点 bp —— 单位更正 2026-08-05):
    0 = 无效应(阴性同样是发现)。 -/
def CausalFinding.effectPm (f : CausalFinding) : Int :=
  (f.cmp.a.accPm : Int) - (f.cmp.b.accPm : Int)

/-- 五级税制(与 p110 矩阵同构)。 -/
inductive Verdict
  | pass | partialV | notMeasured | blockedUpstream | failMethod
  deriving DecidableEq, Repr

/-- 强度序(pass 最强):合成取最弱。 -/
def Verdict.rank : Verdict → Nat
  | .pass => 4 | .partialV => 3 | .notMeasured => 2
  | .blockedUpstream => 1 | .failMethod => 0

def Verdict.weakest (v w : Verdict) : Verdict :=
  if v.rank ≤ w.rank then v else w

theorem weakest_le_left (v w : Verdict) :
    (v.weakest w).rank ≤ v.rank := by
  unfold Verdict.weakest
  by_cases h : v.rank ≤ w.rank <;> simp [h] <;> omega

theorem weakest_le_right (v w : Verdict) :
    (v.weakest w).rank ≤ w.rank := by
  unfold Verdict.weakest
  by_cases h : v.rank ≤ w.rank <;> simp [h] <;> omega

/-- 辅助:foldl 只会让税级变弱或持平,不会回升。 -/
theorem foldl_rank_le_acc (t : List Verdict) (acc : Verdict) :
    (t.foldl Verdict.weakest acc).rank ≤ acc.rank := by
  induction t generalizing acc with
  | nil => exact Nat.le_refl _
  | cons th tt ih =>
      exact Nat.le_trans (ih _) (weakest_le_left acc th)

/-- 合成不可能凭空升级:链上任何一环的税级是合成结果的上界。
    这是"end-to-end certified 必须每环挣来"的机器形态。 -/
theorem weakest_no_upgrade (l : List Verdict) (v : Verdict) (h : v ∈ l) :
    ∀ acc, (l.foldl Verdict.weakest acc).rank ≤ v.rank := by
  induction h with
  | head as =>
      intro acc
      exact Nat.le_trans (foldl_rank_le_acc as _) (weakest_le_right acc v)
  | tail b _ ih =>
      intro acc
      exact ih (acc.weakest b)

end WitCert.Adjudication
