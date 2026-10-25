import Lean

/-!
# Native recursor consistency controls

These checks inspect the pinned native kernel's stored recursor data. They
exercise typing and auxiliary-name hygiene; they do not validate lean4lean's
nested-inductive implementation. The final reduction check uses the very rule
under test, so the independent typing checks and planted faults matter.

Three checks, none of which rely on `IndSpec`:

1. **Erasure.** The auxiliary types introduced by nested elimination use the
   reserved `_nested` prefix and must not survive into the final
   environment — not as declarations, and not inside any type or value.
   (This is the invariant leanprover/lean4#14616 hardened.)

2. **Iota coherence.** For every recursor in the environment and every rule
   of it, recompute the iota equation from the stored data alone:
   instantiate the recursor's parameter/motive/minor telescope, unify the
   constructor's result type with the major premise (which fixes the
   constructor's own parameters and universes — for a restored nested
   recursor these differ from the recursor's), and check that
   `rec ps Ms ms is (ctor ..)` and `rule.rhs ps Ms ms fields` are both
   well-typed and definitionally equal. A slip in `restore_nested`'s name
   surgery on rule right-hand sides would show up here.

3. **Rule/constructor coherence.** Every rule names a real constructor whose
   result type matches the major premise, and `nfields` is within its arity.
   (For nested recursors `nfields` legitimately differs from the
   constructor's `numParams` accounting, so that is reported, not failed.)

Where the discriminating power lies: the final `isDefEq lhs rhs` is close to
circular, since whnf of the left side just fires the very rule under test.
The content is in the *typing* checks — that both sides are well-typed and
have the *same* type. A defeq rule between terms of different types is
exactly what would be unsound, and that is what a mistake in the name
surgery produces: the wrong constructor or right-hand side gives
`motive (cons a l)` on one side and `motive nil` on the other. The negative
control at the end of the file plants those faults and confirms they are
caught.
-/

open Lean Meta Elab

inductive NestedFixture where
  | leaf
  | branch (children : List NestedFixture)

namespace NestedTest

/-- Does `e` mention a `_nested` auxiliary name? -/
def mentionsNested (e : Expr) : Bool :=
  (e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false).isSome

/-- Check every rule of one recursor. Returns an error message on failure. -/
def checkRules (recName : Name) (r : RecursorVal) : MetaM (Option String) := do
  let recLvls := r.levelParams.map Level.param
  forallBoundedTelescope r.type (some (r.numParams + r.numMotives + r.numMinors))
      fun xs body => do
    unless xs.size == r.numParams + r.numMotives + r.numMinors do
      return some s!"{recName}: telescope shorter than numParams+numMotives+numMinors"
    for rule in r.rules do
      let some ci := (← getEnv).find? rule.ctor
        | return some s!"{recName}/{rule.ctor}: rule names an unknown constant"
      let .ctorInfo cv := ci
        | return some s!"{recName}/{rule.ctor}: rule names a non-constructor"
      -- fresh instance of the recursor's indices + major premise
      let (mvs, _, _) ← forallMetaTelescope body
      unless mvs.size ≥ 1 do
        return some s!"{recName}: no major premise"
      let majorMvar := mvs.back!
      let idxMvars := mvs.pop
      let majorType ← inferType majorMvar
      -- fresh instance of the constructor; unification against the major
      -- premise fixes its parameters and universe arguments
      let ctorLvls ← mkFreshLevelMVars cv.levelParams.length
      let ctorType := cv.type.instantiateLevelParams cv.levelParams ctorLvls
      let (ctorArgs, _, ctorConcl) ← forallMetaTelescope ctorType
      unless ← isDefEq ctorConcl majorType do
        return some s!"{recName}/{rule.ctor}: constructor result type does not \
          match the major premise"
      unless rule.nfields ≤ ctorArgs.size do
        return some s!"{recName}/{rule.ctor}: nfields {rule.nfields} exceeds \
          constructor arity {ctorArgs.size}"
      let ctorApp := mkAppN (mkConst rule.ctor ctorLvls) ctorArgs
      let fields := ctorArgs.extract (ctorArgs.size - rule.nfields) ctorArgs.size
      let lhs := mkAppN (mkConst recName recLvls) (xs ++ idxMvars ++ #[ctorApp])
      let rhs := mkAppN rule.rhs (xs ++ fields)
      try check lhs
      catch e => return some s!"{recName}/{rule.ctor}: lhs ill-typed: \
        {← e.toMessageData.toString}"
      try check rhs
      catch e => return some s!"{recName}/{rule.ctor}: rhs ill-typed: \
        {← e.toMessageData.toString}"
      unless ← isDefEq (← inferType lhs) (← inferType rhs) do
        return some s!"{recName}/{rule.ctor}: the two sides have different types"
      unless ← isDefEq lhs rhs do
        return some s!"{recName}/{rule.ctor}: IOTA EQUATION FAILS"
    return none

end NestedTest

open NestedTest in
#eval show MetaM Unit from do
  let env ← getEnv
  -- 1. erasure of the `_nested` auxiliary namespace
  let mut leakedDecls : Array Name := #[]
  let mut leakedUses : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`_nested).isPrefixOf n then leakedDecls := leakedDecls.push n
    if mentionsNested ci.type || ((ci.value? (allowOpaque := true)).map mentionsNested).getD false then
      leakedUses := leakedUses.push n
  logInfo m!"erasure: {leakedDecls.size} leaked `_nested` declarations, \
    {leakedUses.size} constants mentioning one"
  for n in leakedDecls.toList.take 5 do logInfo m!"  LEAKED DECL {n}"
  for n in leakedUses.toList.take 5 do logInfo m!"  LEAKED USE {n}"

  unless leakedDecls.isEmpty && leakedUses.isEmpty do throwError "nested name leak"

  -- 2/3. iota coherence for every recursor, nested blocks tallied separately
  let mut nestedBlocks : Array Name := #[]
  let mut nestedRecs : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if let .inductInfo val := ci then
      if val.numNested != 0 && val.all.head? == some n then
        nestedBlocks := nestedBlocks.push n
        -- the block's own recursors, plus the auxiliary ones the kernel
        -- generates for the nested occurrences (`T.rec_1`, `T.rec_2`, ...)
        for m in val.all do
          if env.contains (mkRecName m) then nestedRecs := nestedRecs.push (mkRecName m)
        for i in [1:val.numNested+1] do
          let auxName := (mkRecName n).appendIndexAfter i
          if env.contains auxName then nestedRecs := nestedRecs.push auxName
  logInfo m!"nested blocks: {nestedBlocks.size}, their recursors: {nestedRecs.size}"

  let mut checkedRules : Nat := 0
  let mut checkedRecs : Nat := 0
  let mut failures : Array String := #[]
  -- nested recursors first, then everything else
  let mut allRecs : Array Name := nestedRecs
  for (n, ci) in env.constants.toList do
    if let .recInfo _ := ci then
      unless nestedRecs.contains n do allRecs := allRecs.push n
  for recName in allRecs do
    let .recInfo r ← getConstInfo recName | continue
    checkedRecs := checkedRecs + 1
    checkedRules := checkedRules + r.rules.length
    match ← (checkRules recName r).run' with
    | some msg => failures := failures.push msg
    | none => pure ()
  logInfo m!"iota coherence: {checkedRecs} recursors, {checkedRules} rules, \
    {failures.size} failures"
  for msg in failures.toList.take 20 do logInfo m!"  FAIL {msg}"

  unless checkedRules != 0 && nestedBlocks.size != 0 && failures.isEmpty do
    throwError "native recursor consistency check failed"

/-! ## Negative control

A test that cannot fail proves nothing. These plant the two faults that a
mistake in `restore_nested`'s name surgery would actually produce — a rule
pointing at the wrong constructor, and a rule carrying the wrong right-hand
side — and confirm the checker rejects them. The environment is not
modified; only the `RecursorVal` handed to the checker is. -/

open NestedTest in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut controls : Array (String × Option String) := #[]
  -- (a) swap the right-hand sides of Nat.rec's two rules
  let .recInfo natRec ← getConstInfo ``Nat.rec | unreachable!
  match natRec.rules with
  | [z, s] =>
    let swapped := { natRec with
      rules := [{ z with rhs := s.rhs, nfields := s.nfields },
                { s with rhs := z.rhs, nfields := z.nfields }] }
    controls := controls.push ("Nat.rec rules swapped", ← checkRules ``Nat.rec swapped)
  | _ => throwError "unexpected Nat.rec rule count"
  -- (b) point a rule at the wrong constructor of the same type
  match natRec.rules with
  | [z, s] =>
    let misnamed := { natRec with rules := [{ z with ctor := s.ctor }, s] }
    controls := controls.push ("Nat.rec rule misnamed", ← checkRules ``Nat.rec misnamed)
  | _ => pure ()
  -- (c) same two faults on a nested block's recursor, if one is available
  for (n, ci) in env.constants.toList do
    if let .inductInfo val := ci then
      if val.numNested != 0 && val.all.head? == some n && controls.size < 3 then
        if let some (.recInfo r) := env.find? (mkRecName n) then
          if r.rules.length ≥ 2 then
            let a := r.rules[0]!
            let b := r.rules[1]!
            let swapped := { r with
              rules := [{ a with rhs := b.rhs, nfields := b.nfields },
                        { b with rhs := a.rhs, nfields := a.nfields }] ++ r.rules.drop 2 }
            controls := controls.push
              (s!"{mkRecName n} (nested) rules swapped", ← checkRules (mkRecName n) swapped)
  let caught := controls.filter (·.2.isSome)
  logInfo m!"negative control: {caught.size}/{controls.size} planted faults caught"
  for (what, res) in controls do
    match res with
    | some msg => logInfo m!"  caught [{what}]: {msg}"
    | none => logInfo m!"  MISSED [{what}] — the checker is not discriminating"

  unless controls.size >= 3 ∧ caught.size == controls.size do
    throwError "recursor negative control failed"
