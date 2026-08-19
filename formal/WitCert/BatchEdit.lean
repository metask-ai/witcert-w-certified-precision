/-
  WitCert 形式化 · L15:**量词降级** —— `∃ 改变` 不蕴含 `∀ 命中`。

  2026-08-08 的直接起因:一次批量文本编辑写成"三处 replace + 一句
  `assert s != o`"。其中一处因换行不同没命中,而另外两处命中了,于是
  `s != o` 成立、断言通过、commit message 宣称三处都改了 —— 实际漏一处,
  下一轮评审才发现。

  但这不是一次手滑,而是本项目反复出现的**同一个形状**:

    * 聚合 odds ratio 通过了,就以为**每个深度组**都通过(未翻转样本只剩 29 个);
    * **端点**累计的 realized ≤ bound,就以为**每一步**都成立;
    * 主张"批量改了 canon",实际只有部分条目重生成;
    * 本例:`∃ 处改变` 被当作 `∀ 处命中`。

  四个实例共享一条逻辑事实:**一个存在性观测对全称义务零信息**。观测到
  "有变化"与"某一条编辑没命中"完全相容 —— 正因如此它做不了判据。

  本文件把这条写成可机器检查的形式,并给出反例(否则规则是装饰品):
    * `applyAll_isSome_iff_allHit` —— 逐条失败的批量应用,成功当且仅当每条都命中;
    * `changed_but_not_all_applied` —— **反例**:跳过未命中的批量应用可以"有变化"
      而同时存在未命中的编辑,故 `结果 ≠ 原文` 不是全称判据;
    * `overlap_makes_order_matter` —— **反例**:两条编辑的作用域重叠时,批量结果
      依赖顺序,故"每条至少命中一次"仍不够,需要"恰好命中一次 + 互不重叠"。

  闭环边界(诚实说明):Lean 管不到 Python 临时脚本。真正让这条生效的是
  `tools/textedit.py` —— 它对**每一条**编辑单独校验命中数,把正确形态做成
  唯一可用的形态。已提交代码里该反模式实例数为 0,故本仓**不**为它加扫描
  守卫(那会是装饰品);守卫的位置留给工具自身的回归测试。
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace WitCert.Calculus.BatchEdit

/-- 抽象的一条编辑:`app d = none` 表示它的模式在 `d` 中**未命中**。 -/
structure Edit (D : Type*) where
  app : D → Option D

variable {D : Type*}

/-- **逐条失败**的批量应用:任何一条未命中,整批失败。这是正确的形态。 -/
def applyAll : List (Edit D) → D → Option D
  | [], d => some d
  | e :: es, d => (e.app d).bind (applyAll es)

/-- **跳过未命中**的批量应用:未命中就当没这条。这是出事的那种写法 ——
    它总能返回一个文档,于是调用者只能观测"变了没有"。 -/
def applySome : List (Edit D) → D → D
  | [], d => d
  | e :: es, d => applySome es ((e.app d).getD d)

/-- 全称义务:每一条编辑在**轮到它时**都命中。 -/
def AllHit : List (Edit D) → D → Prop
  | [], _ => True
  | e :: es, d => ∃ d', e.app d = some d' ∧ AllHit es d'

/-- 逐条失败的批量应用成功 ⟺ 全称义务成立。**这就是正确判据的形式化**。 -/
theorem applyAll_isSome_iff_allHit :
    ∀ (es : List (Edit D)) (d : D), (applyAll es d).isSome ↔ AllHit es d := by
  intro es
  induction es with
  | nil => intro d; simp [applyAll, AllHit]
  | cons e es ih =>
    intro d
    cases h : e.app d with
    | none => simp [applyAll, AllHit, h]
    | some d' => simp [applyAll, AllHit, h, ih d']

/-! ### 反例一:`结果 ≠ 原文` 对全称义务零信息 -/

/-- 恒命中的编辑(把 `n` 变成 `n+1`)。 -/
def bump : Edit ℕ := ⟨fun n => some (n + 1)⟩

/-- 恒不命中的编辑(模式不在文本里)。 -/
def miss : Edit ℕ := ⟨fun _ => none⟩

/-- **反例**:`applySome [bump, miss] 0 = 1 ≠ 0` —— 观测到"文本变了" ——
    而 `miss` 根本没命中,`applyAll` 判失败。故 `s ≠ o` 通过**不能**推出
    每一条编辑都生效:一条命中就足以让它成立。 -/
theorem changed_but_not_all_applied :
    ∃ (es : List (Edit ℕ)) (d : ℕ),
      applySome es d ≠ d ∧ applyAll es d = none ∧ ¬ AllHit es d := by
  refine ⟨[bump, miss], 0, ?_, ?_, ?_⟩
  · simp [applySome, bump, miss]
  · simp [applyAll, bump, miss]
  · simp [AllHit, bump, miss]

/-- 更强的说法(取 $5$ 条未命中为例):一条命中就足以掩盖任意多条未命中,
    故"变了"这个观测的信息量**不随批量规模增长** —— 批量越大,该判据越无力。 -/
theorem one_hit_masks_many_misses :
    applySome (bump :: List.replicate 5 miss) 0 ≠ 0 ∧
      applyAll (bump :: List.replicate 5 miss) 0 = none := by
  constructor <;> simp [applySome, applyAll, bump, miss, List.replicate]

/-! ### 反例二:"每条至少命中一次"仍不够 —— 作用域重叠时结果依赖顺序 -/

/-- 两条编辑作用于同一处:`double` 与 `succ` 都恒命中,但复合不交换。
    故批量编辑的正确义务不止"每条命中",还要求**恰好一次 + 互不重叠**,
    否则结果依赖书写顺序(而顺序通常是无意的)。 -/
theorem overlap_makes_order_matter :
    ∃ (e₁ e₂ : Edit ℕ) (d : ℕ),
      applyAll [e₁, e₂] d ≠ applyAll [e₂, e₁] d ∧
      AllHit [e₁, e₂] d ∧ AllHit [e₂, e₁] d := by
  refine ⟨⟨fun n => some (2 * n)⟩, ⟨fun n => some (n + 1)⟩, 1, ?_, ?_, ?_⟩
  · simp [applyAll]
  · exact ⟨2, rfl, 3, rfl, trivial⟩
  · exact ⟨2, rfl, 4, rfl, trivial⟩

end WitCert.Calculus.BatchEdit
