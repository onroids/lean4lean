import Lean4Lean.Replay

open Lean

namespace ReplayTests

theorem proof : True := True.intro
opaque hidden : Nat := 0
def value : Nat := 0
inductive Item where | mk

-- The old experiment's comparison, retained only as a negative control.
private def oldComparison (a b : ConstantInfo) : Bool :=
  a.levelParams == b.levelParams && a.type == b.type && a.value? == b.value?

#eval show CoreM Unit from do
  let env := (← getEnv).toKernelEnv
  let names := [``proof, ``hidden, ``value, ``propext, ``Item, ``Item.mk, ``Item.rec, ``Quot]
  let mut identical : Nat := 0
  for name in names do
    let some ci := env.find? name | throwError "missing fixture {name}"
    let (added, _) ← Lean4Lean.Replay.replay
      { newConstants := ({} : Std.HashMap Name ConstantInfo).insert name ci, checkQuot := false } env
    unless added == 0 do throwError "duplicate unexpectedly added: {name}"
    identical := identical + 1

  let some (.thmInfo thm) := env.find? ``proof | throwError "missing theorem"
  let some (.opaqueInfo opq) := env.find? ``hidden | throwError "missing opaque"
  let some (.defnInfo defn) := env.find? ``value | throwError "missing definition"
  let some (.axiomInfo ax) := env.find? ``propext | throwError "missing axiom"
  let some (.inductInfo ind) := env.find? ``Item | throwError "missing inductive"
  let some (.ctorInfo ctor) := env.find? ``Item.mk | throwError "missing constructor"
  let some (.recInfo rec) := env.find? ``Item.rec | throwError "missing recursor"
  let some (.quotInfo quot) := env.find? ``Quot | throwError "missing quotient"
  let wrongProof := ConstantInfo.thmInfo { thm with value := mkConst ``False.elim }
  let wrongKind := ConstantInfo.axiomInfo { thm.toConstantVal with isUnsafe := false }
  unless oldComparison (.thmInfo thm) wrongProof && oldComparison (.thmInfo thm) wrongKind do
    throwError "negative control no longer reproduces the old comparator defect"
  let conflicts : List (String × ConstantInfo) := [
    ("theorem body", wrongProof),
    ("kind", wrongKind),
    ("type", .thmInfo { thm with type := mkConst ``False }),
    ("universes", .thmInfo { thm with levelParams := [`u] }),
    ("theorem block metadata", .thmInfo { thm with all := [] }),
    ("opaque body", .opaqueInfo { opq with value := .lit (.natVal 1) }),
    ("opaque safety", .opaqueInfo { opq with isUnsafe := !opq.isUnsafe }),
    ("definition body", .defnInfo { defn with value := .lit (.natVal 1) }),
    ("definition hints", .defnInfo { defn with hints := if defn.hints == .opaque then .abbrev else .opaque }),
    ("definition safety", .defnInfo { defn with safety := if defn.safety == .unsafe then .safe else .unsafe }),
    ("definition partiality", .defnInfo { defn with safety := .partial }),
    ("axiom safety", .axiomInfo { ax with isUnsafe := !ax.isUnsafe }),
    ("inductive metadata", .inductInfo { ind with numNested := ind.numNested + 1 }),
    ("constructor metadata", .ctorInfo { ctor with numFields := ctor.numFields + 1 }),
    ("recursor flag", .recInfo { rec with k := !rec.k }),
    ("recursor rules", .recInfo { rec with rules := [] }),
    ("quotient kind", .quotInfo { quot with kind := .lift })]
  for (label, ci) in conflicts do
    if env.find? ci.name == some ci then
      throwError "negative control did not change the entry: {label}"
    let outcome ← try
      let _ ← Lean4Lean.Replay.replay
        { newConstants := ({} : Std.HashMap Name ConstantInfo).insert ci.name ci,
          checkQuot := false } env
      pure (none : Option String)
    catch e => pure (some (← e.toMessageData.toString))
    match outcome with
    | none => throwError "conflicting duplicate accepted: {label}"
    | some message =>
      unless (message.splitOn "already declared, with different content").length > 1 do
        throwError "{label}: failed for the wrong reason: {message}"

  let fresh : ConstantInfo := .thmInfo { thm with name := `freshReplayProof, all := [`freshReplayProof] }
  let (added, result) ← Lean4Lean.Replay.replay
    { newConstants := ({} : Std.HashMap Name ConstantInfo).insert fresh.name fresh,
      checkQuot := false } env
  unless added == 1 && result.find? fresh.name == some fresh do
    throwError "fresh theorem replay failed"
  let unsafeFresh : ConstantInfo := .defnInfo
    { defn with name := `freshUnsafeReplay, all := [`freshUnsafeReplay], safety := .unsafe }
  let (addedUnsafe, resultUnsafe) ← Lean4Lean.Replay.replay
    { newConstants := ({} : Std.HashMap Name ConstantInfo).insert unsafeFresh.name unsafeFresh,
      checkQuot := false } env
  unless addedUnsafe == 0 && (resultUnsafe.find? unsafeFresh.name).isNone do
    throwError "fresh unsafe declaration was not skipped as before"
  logInfo m!"replay: {identical} identical kinds reused, {conflicts.length} conflicts rejected, fresh theorem added"

end ReplayTests
