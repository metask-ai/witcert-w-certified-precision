/-
  **证据与主张的类型化**(仪器层逻辑关:2026-08-08 三次同族事故 + 一次自我纠正)。

  三次事故形状相同 —— **拿一个"典型值"去完成一个"认证主张"**:
    ① `√ρ_ℓ`(随机方向的矩)被当作局部 Lipschitz 常数(一个 **sup**),
       结论从"每层收缩"翻转为 σ_max≈16,差 251×;
    ② 经验 MGF `Ê[e^δ]`(无偏**估计**)被当作根定理要的上界 `B_v`;
    ③ 留出历史的**样本均值**被拿去比 `μ_cal`(校准侧的**置信上界**),
       结论从"外推成功 0/6"翻转为"2/6 未获认证"。

  **本文件的首版是装饰品,必须记下来**:它定义的是"数值可比性",而在那套规则里
  `moment ≤ ucb` 是**合法**的 —— 可事故 ③ 恰恰就是这个形状,于是规则拦不住它。
  正确的类型化对象不是"两个数能不能比",而是 **"哪一种证据能完成哪一种主张"**:
    * `Claim.pass`(认证通过)**只能**由同 target/scope 的**上**置信界构造;
    * `Claim.violation`(认证违约)**只能**由同 target/scope 的**下**置信界构造;
    * 两者都不可得时是 `undetermined` —— 它**既不是通过也不是违约**。
  第三态正是 2026-08-08 第四次纠正:`UCB > 阈值` 只说明**未获认证**,不说明真实
  均值已经违约(那需要 `LCB > 阈值`)。`Moment` 不出现在任何构造子里,于是
  "拿样本均值去完成认证"在**类型层面**就写不出来。

  并按本仓惯例给出**反例定理**(否则规则是装饰品):
    * `undetermined_consistent_with_both` —— 未获认证与"真实均值合规"和"真实均值
      违约"都相容,故不可读作违约;
    * `sample_mean_below_threshold_not_certifying` —— 样本均值低于阈值时真实均值
      仍可高于阈值,故矩不能完成认证。
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace WitCert.Calculus.QuantityKind

/-- 主张的**指向**:量在什么总体/范围上被断言。target 或 scope 不同的证据不能
    互相完成主张(手选 12 个历史族 ≠ 运行时流量总体)。 -/
structure Target where
  quantity : String     -- 例:"E_omega[TV]"
  scope : String        -- 例:"history-h7" / "heldout-family" / "runtime-traffic"
  deriving DecidableEq, Repr

/-- **上**置信界:以概率 ≥ 1−α 有 `真值 ≤ value`。 -/
structure UpperCB where
  target : Target
  value : ℝ
  alpha : ℝ

/-- **下**置信界:以概率 ≥ 1−α 有 `value ≤ 真值`。 -/
structure LowerCB where
  target : Target
  value : ℝ
  alpha : ℝ

/-- **矩 / 样本均值**:没有 `alpha`,因为它**不是**一个置信陈述。
    可以报告,但不能完成任何认证主张 —— 这正是三次事故的根。 -/
structure Moment where
  target : Target
  value : ℝ

/-- 对 `t` 在阈值 `thr` 上的**认证结论**,三态。构造子决定了什么证据能完成什么
    主张;`Moment` **不出现在任何构造子里**。 -/
inductive Claim (t : Target) (thr : ℝ) : Type
  /-- 认证通过:同 target 的**上**置信界不超过阈值。 -/
  | pass (u : UpperCB) (ht : u.target = t) (h : u.value ≤ thr) : Claim t thr
  /-- 认证违约:同 target 的**下**置信界高于阈值。 -/
  | violation (l : LowerCB) (ht : l.target = t) (h : thr < l.value) : Claim t thr
  /-- 未获认证:两者都不可得。**既非通过也非违约。** -/
  | undetermined : Claim t thr

namespace Claim

/-- 该主张消耗的置信预算(未获认证不消耗)。总账须把每条主张的 α 相加。 -/
def alphaSpent {t : Target} {thr : ℝ} : Claim t thr → ℝ
  | pass u _ _ => u.alpha
  | violation l _ _ => l.alpha
  | undetermined => 0

def isCertified {t : Target} {thr : ℝ} : Claim t thr → Bool
  | undetermined => false
  | _ => true

end Claim

/-! ## 反例:未获认证 ≠ 违约(2026-08-08 第四次纠正的机器复述) -/

/-- **`undetermined` 与两种真相都相容**:存在真实均值 `mu1 ≤ thr` 与 `mu2 > thr`,
    二者都落在同一个"下界低于阈值、上界高于阈值"的置信区间内,因而都只能被判为
    未获认证。故把 `undetermined` 读作"违约"是错的 —— 正确说法是**该项未获认证**。 -/
theorem undetermined_consistent_with_both (thr : ℝ) :
    ∃ mu1 mu2 lo hi : ℝ,
      mu1 ≤ thr ∧ thr < mu2 ∧
      lo ≤ mu1 ∧ mu1 ≤ hi ∧ lo ≤ mu2 ∧ mu2 ≤ hi ∧
      lo ≤ thr ∧ thr < hi :=
  ⟨thr, thr + 1, thr - 1, thr + 2, le_refl thr, by linarith,
   by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **样本均值低于阈值不能完成认证**:真实均值仍可高于阈值(抽样涨落)。
    故 `Moment` 不进 `Claim` 的构造子不是保守,是必需。 -/
theorem sample_mean_below_threshold_not_certifying (thr : ℝ) :
    ∃ sampleMean trueMean : ℝ, sampleMean ≤ thr ∧ thr < trueMean :=
  ⟨thr, thr + 1, le_refl thr, by linarith⟩

/-- **跨 scope 不能互相完成主张**:同一 quantity 在不同 scope 上是不同的 `Target`,
    故一个 scope 的上置信界构造不出另一个 scope 的 `pass`。 -/
theorem scope_mismatch_blocks_pass (q s1 s2 : String) (hne : s1 ≠ s2) :
    (⟨q, s1⟩ : Target) ≠ (⟨q, s2⟩ : Target) := by
  simp [Target.mk.injEq, hne]

/-! ## α 记账:每条认证主张都要付,不能只付一次 -/

/-- 一组主张的总置信开销逐条相加(Bonferroni 的形式化理由:H 个历史各建一个
    1−α 的界,总失败概率至多 `∑ α`)。 -/
def totalAlpha {t : Target} {thr : ℝ} (cs : List (Claim t thr)) : ℝ :=
  (cs.map Claim.alphaSpent).sum

theorem totalAlpha_nil {t : Target} {thr : ℝ} :
    totalAlpha ([] : List (Claim t thr)) = 0 := rfl

/-- 未获认证的主张不消耗预算(它没有做出任何概率陈述)。 -/
theorem undetermined_costs_nothing {t : Target} {thr : ℝ} :
    (Claim.undetermined : Claim t thr).alphaSpent = 0 := rfl

end WitCert.Calculus.QuantityKind
