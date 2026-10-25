import Lean4Lean.Research.Inductive.Spec
import Lean4Lean.Theory.Meta

/-! Explicit positive-native/negative-spec controls for the abstract model's scope. -/

namespace SpecLimits
open Lean Lean4Lean

def Predicate := Nat → Prop

#eval show MetaM Unit from do
  let env := (← getEnv).toKernelEnv
  let u := Level.param `u
  let v := Level.param `v
  let types : List InductiveType := [
    { name := `ScopeMaxUV, type := .sort (.max u v), ctors := [] },
    { name := `ScopeMaxVU, type := .sort (.max v u), ctors := [] }]
  unless (env.addDecl {} (.inductDecl [`u, `v] 0 types false)).isOk do
    throwError "native kernel rejected equivalent result levels"
  let abstractTypes ← types.mapM fun t => do
    let ty ← Lean4Lean.Meta.ofExpr [`u, `v] {} t.type
    return ({ name := t.name, uvars := 2, type := ty, ctors := [] } : VInductiveType)
  unless (IndSpec.mkViews { uvars := 2, nparams := 0, types := abstractTypes }).isNone do
    throwError "expected the spec's syntactic-level restriction"

  let hidden : InductiveType := { name := `ScopeHiddenTelescope, type := mkConst ``Predicate, ctors := [] }
  unless (env.addDecl {} (.inductDecl [] 0 [hidden] false)).isOk do
    throwError "native kernel rejected the definition-hidden index telescope"
  let abstractHidden : VInductiveType :=
    { name := hidden.name, uvars := 0, type := ← Lean4Lean.Meta.ofExpr [] {} hidden.type, ctors := [] }
  unless (IndSpec.mkViews { uvars := 0, nparams := 0, types := [abstractHidden] }).isNone do
    throwError "expected the spec's literal-telescope restriction"
  logInfo "spec limits: native accepts equivalent result levels and a hidden telescope; the abstract spec rejects both"

end SpecLimits
