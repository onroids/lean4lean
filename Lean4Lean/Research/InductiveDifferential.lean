import Lean4Lean.Research.Inductive.Spec
import Lean4Lean.Theory.Meta

/-!
# Differential test of `IndSpec.addInductCore` against the C++ kernel

For each test inductive: read the block the kernel stored, translate it to a
`VInductDecl` (via `Meta.ofExpr`), run the draft construction, and compare

* the computed recursor type of every type in the block against the
  translation of the kernel-generated `T.rec` type, and
* the computed iota rule right-hand sides against the translations of the
  kernel-generated `RecursorRule.rhs`.

Both comparisons are syntactic equality of `VExpr`s, so any de Bruijn slip or
divergence from `inductive.cpp`'s construction shows up as a mismatch.
-/

open Lean Meta Elab Lean4Lean Lean4Lean.IndSpec

deriving instance Repr for VLevel
deriving instance Repr for VExpr

namespace IndSpecTest

/-- Translate the kernel's stored inductive block rooted at `name` into a
`VInductDecl`, and read off whether the kernel granted large elimination
(one extra universe parameter on the recursor). -/
def trIndDecl (name : Name) : MetaM (VInductDecl × Bool) := do
  let .inductInfo ind ← getConstInfo name | throwError "not inductive: {name}"
  let lps := ind.levelParams
  let types ← ind.all.mapM fun n => do
    let .inductInfo i ← getConstInfo n | unreachable!
    let ctors ← i.ctors.mapM fun c => do
      let .ctorInfo ci ← getConstInfo c | unreachable!
      return { name := c, uvars := lps.length,
               type := ← Lean4Lean.Meta.ofExpr lps {} ci.type : VConstVal }
    return { name := n, uvars := lps.length,
             type := ← Lean4Lean.Meta.ofExpr lps {} i.type, ctors : VInductiveType }
  let .recInfo r ← getConstInfo (mkRecName name) | throwError "no recursor for {name}"
  let large := r.levelParams.length == lps.length + 1
  return ({ uvars := lps.length, nparams := ind.numParams, types }, large)

def checkInd (name : Name) : MetaM Unit := do
  let (decl, large) ← trIndDecl name
  let some v := mkViews decl
    | throwError "{name}: mkViews failed"
  let Θ := mkRecCtx v large
  let .inductInfo ind ← getConstInfo name | unreachable!
  let some myRules := iotaRules Θ
    | throwError "{name}: iotaRules failed"
  let mut q := 0
  for n in ind.all, i in [0:ind.all.length] do
    let .recInfo r ← getConstInfo (mkRecName n) | unreachable!
    -- recursor type
    let expected ← Lean4Lean.Meta.ofExpr r.levelParams {} r.type
    let some got := recType Θ i
      | throwError "{name}: recType failed for {n}"
    unless got == expected do
      throwError "{name}: recursor type mismatch for {n}:\
        \n  computed: {reprStr got}\n  kernel:   {reprStr expected}"
    -- iota rules: recursor `i` carries the rules for type `i`'s ctors, with
    -- a block-global minor premise index
    for rule in r.rules do
      let some df := myRules[q]?
        | throwError "{name}: missing iota rule #{q} ({rule.ctor})"
      let expected ← Lean4Lean.Meta.ofExpr r.levelParams {} rule.rhs
      unless df.rhs == expected do
        throwError "{name}: iota rhs mismatch for ctor {rule.ctor}:\
          \n  computed: {reprStr df.rhs}\n  kernel:   {reprStr expected}"
      unless df.uvars == Θ.recUvars do
        throwError "{name}: iota uvars mismatch for {rule.ctor}"
      q := q + 1
  unless q == myRules.length do
    throwError "{name}: iota rule count mismatch: {myRules.length} vs {q}"
  logInfo m!"{name}: OK ({ind.all.length} types, {q} iota rules, largeElim={large})"

elab "#checkInd " n:ident : command =>
  Elab.Command.liftTermElabM do checkInd n.getId

end IndSpecTest

-- basic recursion
#checkInd Nat
-- parameters
#checkInd List
-- parameters + indices, large elim from a Prop (subsingleton elimination)
#checkInd Eq
-- Prop, two ctors: small elim
#checkInd Or
-- Prop, one ctor, Prop fields: large elim by the single-ctor rule
#checkInd And
-- Prop, one ctor, non-Prop field not in indices: small elim
#checkInd Exists
-- no ctors
#checkInd False
#checkInd Empty
-- reflexive (higher-order recursive field with its own telescope)
#checkInd Acc
-- structure-like with two universe params
#checkInd Prod
#checkInd PProd
#checkInd Sigma
-- large elim with a Prop field
#checkInd Subtype
-- enumerations
#checkInd Bool
#checkInd Ordering

-- a mutual block
mutual
  inductive EvenT where
    | zero
    | succ (n : OddT)
  inductive OddT where
    | succ (n : EvenT) (m : EvenT)
end

#checkInd EvenT

-- mutual with parameters, indices, and cross-recursive higher-order fields
mutual
  inductive TreeT (α : Sort u) : Nat → Sort (max 1 u) where
    | leaf (a : α) : TreeT α 0
    | node (f : Bool → ForestT α 1) : TreeT α 2
  inductive ForestT (α : Sort u) : Nat → Sort (max 1 u) where
    | nil : ForestT α 0
    | cons (n k : Nat) (t : TreeT α n) (rest : ForestT α k) : ForestT α 1
end

#checkInd TreeT

/-! ## Mass differential test: every non-nested inductive block in scope -/

open IndSpecTest in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut skippedNested := 0
  let mut skippedBigLit := 0
  let mut failures : Array (Name × String) := #[]
  -- `ofExpr` expands nat literals to unary numerals, so a large literal in a
  -- constructor type would blow the stack; skip those blocks.
  let hasBigLit (e : Expr) : Bool :=
    (e.find? fun
      | .lit (.natVal n) => n > 10000
      | .lit (.strVal s) => s.length > 1000
      | _ => false).isSome
  for (name, ci) in env.constants.toList do
    let .inductInfo val := ci | continue
    unless val.all.head? == some name do continue -- one check per block
    if val.numNested != 0 then skippedNested := skippedNested + 1; continue
    let mut big := false
    for n in val.all do
      if let .inductInfo i := env.find? n |>.get! then
        if hasBigLit i.type then big := true
        for c in i.ctors do
          if let .ctorInfo cv := env.find? c |>.get! then
            if hasBigLit cv.type then big := true
    if big then skippedBigLit := skippedBigLit + 1; continue
    total := total + 1
    try
      let (decl, large) ← trIndDecl name
      let some v := mkViews decl
        | throwError "mkViews failed"
      let Θ := mkRecCtx v large
      let some myRules := iotaRules Θ
        | throwError "iotaRules failed"
      let mut q := 0
      for n in val.all, i in [0:val.all.length] do
        let .recInfo r ← getConstInfo (mkRecName n) | throwError "missing recursor for {n}"
        let expected ← Lean4Lean.Meta.ofExpr r.levelParams {} r.type
        let some got := recType Θ i | throwError "recType failed for {n}"
        unless got == expected do throwError "rec type mismatch for {n}"
        for rule in r.rules do
          let some df := myRules[q]? | throwError "missing iota rule {rule.ctor}"
          let expected ← Lean4Lean.Meta.ofExpr r.levelParams {} rule.rhs
          unless df.rhs == expected do throwError "iota rhs mismatch for {rule.ctor}"
          q := q + 1
      unless q == myRules.length do throwError "iota count mismatch"
    catch e =>
      failures := failures.push (name, ← e.toMessageData.toString)
  logInfo m!"mass check: {total} blocks checked, {skippedNested} nested and {skippedBigLit} big-literal blocks skipped, {failures.size} failures"
  for (n, msg) in failures do
    logInfo m!"FAIL {n}: {msg}"

  unless total != 0 && failures.isEmpty do throwError "inductive differential test failed"

/-! ## Typing validation of the iota rules' `lhs`/`type` fields

The kernel stores only the RHS of each recursor rule, so `lhs` and `type`
cannot be compared syntactically. Instead: translate them back to `Expr` and
check with the elaborator that both sides of every constructed defeq are
well-typed at the constructed type. -/

namespace IndSpecTest

def vlevelToLevel (lps : List Name) : VLevel → Level
  | .zero => .zero
  | .succ u => .succ (vlevelToLevel lps u)
  | .max u v => .max (vlevelToLevel lps u) (vlevelToLevel lps v)
  | .imax u v => .imax (vlevelToLevel lps u) (vlevelToLevel lps v)
  | .param i => .param lps[i]!

def vexprToExpr (lps : List Name) : VExpr → Expr
  | .bvar i => .bvar i
  | .sort u => .sort (vlevelToLevel lps u)
  | .const c us => .const c (us.map (vlevelToLevel lps))
  | .app f a => .app (vexprToExpr lps f) (vexprToExpr lps a)
  | .lam A b => .lam `x (vexprToExpr lps A) (vexprToExpr lps b) .default
  | .forallE A b => .forallE `x (vexprToExpr lps A) (vexprToExpr lps b) .default

end IndSpecTest

set_option maxRecDepth 100000 in
open IndSpecTest in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut rules := 0
  let mut failures : Array (Name × String) := #[]
  let hasBigLit (e : Expr) : Bool :=
    (e.find? fun
      | .lit (.natVal n) => n > 10000
      | .lit (.strVal s) => s.length > 1000
      | _ => false).isSome
  for (name, ci) in env.constants.toList do
    let .inductInfo val := ci | continue
    unless val.all.head? == some name do continue
    if val.numNested != 0 then continue
    let mut big := false
    for n in val.all do
      if let .inductInfo i := env.find? n |>.get! then
        if hasBigLit i.type then big := true
        for c in i.ctors do
          if let .ctorInfo cv := env.find? c |>.get! then
            if hasBigLit cv.type then big := true
    if big then continue
    total := total + 1
    try
      let (decl, large) ← trIndDecl name
      let some v := mkViews decl | throwError "mkViews failed"
      let Θ := mkRecCtx v large
      let some myRules := iotaRules Θ | throwError "iotaRules failed"
      let .recInfo r0 ← getConstInfo (mkRecName name) | unreachable!
      let lps := r0.levelParams
      for df in myRules do
        let lhs := vexprToExpr lps df.lhs
        let rhs := vexprToExpr lps df.rhs
        let ty := vexprToExpr lps df.type
        Meta.check ty
        Meta.check lhs
        Meta.check rhs
        unless ← Meta.isDefEq (← Meta.inferType lhs) ty do
          throwError "lhs type mismatch"
        unless ← Meta.isDefEq (← Meta.inferType rhs) ty do
          throwError "rhs type mismatch"
        unless ← Meta.isDefEq lhs rhs do
          throwError "lhs/rhs not defeq"
        rules := rules + 1
    catch e =>
      failures := failures.push (name, ← e.toMessageData.toString)
  logInfo m!"iota typing check: {total} blocks, {rules} rules verified, {failures.size} failures"
  for (n, msg) in failures.toList.take 10 do
    logInfo m!"FAIL {n}: {msg}"

  unless total != 0 && rules != 0 && failures.isEmpty do throwError "iota typing test failed"
