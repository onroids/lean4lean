import Lean4Lean.Research.RecursiveBlockWitness
import Lean4Lean.Research.PatternHypothesis
import Lean4Lean.Research.SpecLimits
import Lean4Lean.Research.ConstructorEnvironment
import Lean4Lean.Research.CtorIsType
import Lean4Lean.Research.EmptyBlockWitness
import Lean4Lean.Research.Inductive.Exists
import Lean4Lean.Research.Inductive.Spec
import Lean4Lean.Research.Inductive.Transport
import Lean4Lean.Research.Inductive.WF
import Lean4Lean.Research.InductiveDifferential
import Lean4Lean.Research.InheritedModelCounterexample
import Lean4Lean.Research.KernelRecursorChecks
import Lean4Lean.Research.PatternRefutation
import Lean4Lean.Research.ProjectionCounterexample
import Lean4Lean.Research.ReplayTests
import Lean4Lean.Research.ScopeCounterexample
import Lean4Lean.Research.TelescopeWitness
import Lean4Lean.Research.Uniformity
import Lean4Lean.Research.UniformityTests
import Lean.Util.CollectAxioms
open Lean

-- Check transitive dependencies, including definition bodies in the abstract core.
-- The three explicitly named refutations are expected to use their disputed axiom.
run_meta
  let env ← getEnv
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut records : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let moduleName := env.header.moduleNames[idx]!.toString
      if moduleName.startsWith "Lean4Lean.Research." && !n.isInternal &&
          (ci.isTheorem || moduleName.startsWith "Lean4Lean.Research.Inductive.") then
        let axioms ← collectAxioms n
        let extra : Array Name :=
          if n == `Lean4Lean.extra_pat_false || n == `Lean4Lean.ExtraPatRefutation.sexpr_extra_pat_inconsistent then
            #[`Lean4Lean.SExpr.Params.extra_pat]
          else if n == `Lean4Lean.Research.inheritedModelContradiction then
            #[`Lean.Expr.looseBVarRange_eq, `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7]
          else #[]
        for ax in axioms do
          unless standard.contains ax || extra.contains ax do
            throwError "unexpected axiom {ax} in {n} ({moduleName})"
        for ax in extra do
          unless axioms.contains ax do throwError "expected disputed axiom {ax} absent from {n}"
        records := records.push <| Json.mkObj [
          ("name", toJson n.toString), ("module", toJson moduleName),
          ("axioms", toJson (axioms.map Name.toString))]
        checked := checked + 1
  unless checked > 300 do throwError "axiom audit unexpectedly small: {checked}"
  IO.FS.createDirAll ".lake/research-checks"
  IO.FS.writeFile ".lake/research-checks/axioms.json" (Json.arr records).pretty
  logInfo m!"axiom audit: {checked} declarations; only standard axioms outside the three named refutations"
