import Lean4Lean.Verify.Expr

/-!
Reproductions of upstream issues #48 and #52, not new discoveries.
The contradiction uses the imported model axiom `Expr.looseBVarRange_eq`.
It is not a contradiction derived from Lean's standard axioms.
-/

namespace Lean4Lean.Research
open Lean

theorem inheritedModelContradiction : False := by
  have h := Expr.Data.looseBVarRange_le (d := (Expr.bvar (2^20)).data)
  have h2 := Expr.looseBVarRange_eq (Expr.bvar (2^20))
  simp only [Expr.looseBVarRange, Expr.looseBVarRange'] at h2
  omega

#print axioms inheritedModelContradiction

#eval show IO Unit from do
  let actualAbstract := (Expr.bvar 0).abstract #[.fvar ⟨`x⟩]
  let modelAbstract := (Expr.bvar 0).abstractList [⟨`x⟩]
  let actualInst := (Expr.bvar 0).instantiate #[.bvar 0, .const `C []]
  let modelInst := (Expr.bvar 0).instantiateList [.bvar 0, .const `C []]
  unless actualAbstract == .bvar 0 && modelAbstract == .bvar 1 do
    throw <| IO.userError "abstract model mismatch changed"
  unless actualInst == .bvar 0 && modelInst == .const `C [] do
    throw <| IO.userError "instantiate model mismatch changed"
  IO.println "inherited models: both issue #48 mismatches reproduced"

end Lean4Lean.Research
