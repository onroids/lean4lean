import Lean4Lean.Research.Uniformity

open Lean
open Lean4Lean.Research

namespace UniformityTests

private def fixture (name : Name) (uniform : Bool) (eraseWithLet : Bool) : InductiveType := Id.run do
  let type0 := Expr.sort (.succ .zero)
  let arg := if uniform then Expr.bvar 0 else mkConst ``Nat
  let occurrence := mkApp (mkConst name) arg
  let hidden := if eraseWithLet then
      Expr.letE `ignored type0 occurrence (mkConst ``Nat) true
    else mkApp (.lam `ignored type0 (mkConst ``Nat) .default) occurrence
  let ctorType := Expr.forallE `alpha type0
    (.forallE `field hidden (mkApp (mkConst name) (.bvar 1)) .default) .default
  return {
    name, type := .forallE `alpha type0 type0 .default
    ctors := [{ name := name.str "mk", type := ctorType }]
  }

-- Compare complete entry points, using raw declarations to avoid elaborator filtering.
#eval show CoreM Unit from do
  let env := (← getEnv).toKernelEnv
  for uniform in [false, true] do
    for eraseWithLet in [false, true] do
      let ind := fixture `UniformityFixture uniform eraseWithLet
      let decl := Declaration.inductDecl [] 1 [ind] false
      let native := (env.addDecl {} decl).isOk
      let upstream := (Lean4Lean.Environment.addInductive env [] 1 [ind] false false).isOk
      let checked := (addInductiveChecked env [] 1 [ind] false false).isOk
      unless native == uniform && checked == uniform && upstream do
        throwError "uniformity fixture failed: uniform={uniform}, let={eraseWithLet}, native={native}, upstream={upstream}, candidate={checked}"
  logInfo "uniformity: 4 raw declarations; native/candidate agree, upstream accepts both erased nonuniform cases"

-- Exercise parameter depth, over-application (indices), and universe arguments.
#eval show CoreM Unit from do
  let name := `T
  let u := Level.param `u
  let check := uniformIndOccs [name] [u] 1
  let t := mkConst name [u]
  let good := mkApp t (.bvar 0)
  let bad := mkApp t (mkConst ``Nat)
  let cases : List (String × Expr × Nat × Bool) := [
    ("uniform", good, 1, true),
    ("wrong parameter", bad, 1, false),
    ("missing parameter", t, 1, false),
    ("wrong universe", mkApp (mkConst name [.succ u]) (.bvar 0), 1, false),
    ("insufficient depth", good, 0, false),
    ("index", mkApp good (.lit (.natVal 0)), 1, true),
    ("nonuniform occurrence in index", mkApp good bad, 1, false),
    ("lambda", .lam `a (.sort u) good .default, 0, true),
    ("forall", .forallE `a (.sort u) good .default, 0, true),
    ("let value", .letE `a (.sort u) bad good false, 1, false),
    ("metadata", .mdata {} bad, 1, false),
    ("projection payload", .proj `S 0 bad, 1, false)]
  for (label, e, depth, expected) in cases do
    unless check e depth == expected do throwError "uniformity walk: {label}"
  unless uniformIndOccs [name] [u] 0 t 0 do throwError "nullary uniform occurrence"
  if uniformIndOccs [name] [u] 0 (mkConst name []) 0 then throwError "nullary universe mismatch"
  logInfo "uniformity: 14 traversal controls passed"

-- Every imported native constructor is a positive control for the candidate pass.
#eval show CoreM Unit from do
  let env ← getEnv
  let mut blocks : Nat := 0
  let mut ctors : Nat := 0
  for (n, ci) in env.constants.toList do
    if let .inductInfo ind := ci then
      if ind.all.head? == some n then
        let mut types := []
        for name in ind.all do
          let some (.inductInfo member) := env.find? name | throwError "missing member {name}"
          let mut constructors := []
          for c in member.ctors do
            let some info := env.find? c | throwError "missing constructor {c}"
            constructors := constructors ++ [{ name := c, type := info.type : Constructor }]
            ctors := ctors + 1
          types := types ++ [{ name, type := member.type, ctors := constructors : InductiveType }]
        match checkUniformIndOccs ind.levelParams ind.numParams types with
        | .error _ => throwError "candidate rejects native block {n}"
        | .ok () => blocks := blocks + 1
  unless blocks != 0 && ctors != 0 do throwError "empty positive-control corpus"
  logInfo m!"uniformity: {blocks} imported native blocks / {ctors} constructors accepted"

end UniformityTests
