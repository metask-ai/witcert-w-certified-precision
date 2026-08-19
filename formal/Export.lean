/-
  由 Lean 自己导出定理数据 —— 而不是用正则去切源码。

  区别很实质:正则切出来的是"源文本",反映的是解析器作者(人)对代码的理解;
  这里输出的是 Lean **elaborate 之后**的类型,由 Lean 自带的 pretty-printer 渲染,
  并用 `collectAxioms` 机器化地列出每条定理真正依赖的公理。
  论文里的定理陈述由此"编译"得到,而非转录。

  用法(见 tools/lean_extract.py 自动调用):
      lake env lean --run Export.lean > paper/theorems_lean.json
-/
import Lean
import WitCert

open Lean Elab Command Meta

/-- JSON 字符串转义。 -/
def esc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => ""
      | c    => c.toString) ""

/-- 排除 Lean 自动生成的方程引理与证明义务(`.proof_1` / `.eq_1` / `.eq_def` 等)。

    2026-07-31 补:`structure` 还会生成 `.mk.injEq` / `.mk.inj` / `.mk.sizeOf_spec`
    与 `.noConfusion`,它们都是 `theorem`。把这些计进"机器检查定理数"是**虚报** ——
    论文1 没有 structure 所以从没暴露,论文2 的契约演算一引入结构体就冒出 15 条。 -/
def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "proof_" || s.startsWith "eq_" || s == "eq_def"
                 || s.startsWith "match_" || s.startsWith "_"
                 || s == "injEq" || s == "inj" || s == "sizeOf_spec"
                 || s == "noConfusion" || s == "noConfusionType"
                 -- **递归子族**(2026-08-09:`inductive Balanced : ... → Prop` 使
                 -- `Balanced.brecOn` 以 thmInfo 出现,定位不到源行 ⟹ 抽取整体失败)。
                 -- Prop 值归纳类型的这几个自动生成物都会变成"定理",必须一并剔除。
                 || s == "brecOn" || s == "binductionOn" || s == "below"
                 || s == "ibelow" || s == "recOn" || s == "casesOn"
                 || s == "ndrec" || s == "ndrecOn" || s == "induct"
  | _ => false

/-- 我们关心的命名空间(Mathlib 层);零依赖层无 Mathlib,由 tools/lean_extract.py 单独导出。 -/
def wanted (n : Name) : Bool :=
  (`WitCert).isPrefixOf n && !n.isInternal && !isGenerated n

unsafe def emit : CommandElabM Unit := do
  let env ← getEnv
  let mut items : Array String := #[]
  for (n, ci) in env.constants.toList do
    -- **结构体的 Prop 字段投影也是 theorem**(如 `Contract.sound`),但它是"假设的访问器"
    -- 而不是被证明的命题。计进定理数同样是虚报,故用 Lean 自己的投影信息剔除。
    if wanted n && (env.getProjectionFnInfo? n).isNone then
      match ci with
      | .thmInfo val => do
          let typeStr ← liftTermElabM do
            let fmt ← Meta.ppExpr val.type
            pure (toString fmt)
          let ax ← liftCoreM (collectAxioms n)
          let axs := String.intercalate "," (ax.toList.map (fun a => "\"" ++ esc a.toString ++ "\""))
          items := items.push <|
            "{\"name\":\"" ++ esc n.toString ++ "\"," ++
            "\"kind\":\"theorem\"," ++
            "\"type\":\"" ++ esc typeStr ++ "\"," ++
            "\"axioms\":[" ++ axs ++ "]}"
      | _ => pure ()
  IO.println ("{\"source\":\"lean-export\",\"items\":[" ++
              String.intercalate "," items.toList ++ "]}")

run_cmd emit
