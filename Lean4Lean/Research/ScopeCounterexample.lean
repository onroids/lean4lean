import Lean4Lean.Inductive.Add

/-!
Runtime counterexample to the old `InductScope.hwpo` premise, which quantified
over *every* AddInductive.Context without requiring freshness of block names.
This does not assert a formal refutation of the complete InductScope structure.
-/

namespace ScopeCounterexample
open Lean

inductive Block where | mk
def alias := Block

#eval show CoreM Unit from do
  let c : Lean4Lean.AddInductive.Context :=
    { env := (← getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let names := #[mkConst ``Block]
  let input := mkConst ``alias
  unless Lean4Lean.AddInductive.hasIndOcc names input == false do
    throwError "input unexpectedly mentions block"
  let action : Lean4Lean.AddInductive.M Expr := monadLift (Lean4Lean.TypeChecker.whnf input)
  match action c with
  | .error _ => throwError "weak-head normalization failed"
  | .ok output =>
    unless output == mkConst ``Block && Lean4Lean.AddInductive.hasIndOcc names output do
      throwError "unexpected normal form"
  logInfo "scope: empty local context, valid environment; alias unfolds to the block (occurrence false -> true)"

end ScopeCounterexample
