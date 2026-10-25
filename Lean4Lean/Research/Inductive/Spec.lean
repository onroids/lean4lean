import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl

/-!
# A syntactic model of non-nested inductive declarations

This research module constructs recursor types and iota rules without replacing
upstream's `VInductDecl.WF` or `VEnv.addInduct`. Its preservation theorem is
`IndSpec.addInductCore_WF4` in `Transport.lean`: it requires `WFCore`,
`WFExact`, and `WFTele`, not merely the input's acceptance by a checker.

The model requires literal telescopes, syntactically equal parameter telescopes
and result levels, and the reassembly/typing conditions recorded in those
predicates. `SpecLimits.lean` exhibits native-accepted blocks outside this scope.
Telescopes are stored outermost first; the corresponding context is reversed.
Large elimination is an explicit Boolean argument, with its justification
required by `WFCore` when true. No correspondence with the executable checker,
consistency theorem, or coverage percentage is claimed here.

The sources originate in the preserved September research branch; provenance
and the full disposition record are in `research/REVIEW.md`.
-/

namespace Lean4Lean

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

namespace IndSpec

/-! ## Expression helpers -/

/-- Apply `f` to `args` (in application order). -/
def mkAppList (f : VExpr) (args : List VExpr) : VExpr := args.foldl .app f

/-- Decompose an application spine; returns the head and args in application
order. -/
def getAppList : VExpr → VExpr × List VExpr := go []
where go (acc : List VExpr) : VExpr → VExpr × List VExpr
  | .app f a => go (a :: acc) f
  | e => (e, acc)

/-- Strip top-level `outParam`/`semiOutParam`/`optParam`/`autoParam`
applications (cf. `Expr.consumeTypeAnnotations`; the kernel applies it to
every binder domain it introduces, so the annotations do not survive into
recursor types). -/
def consumeAnnots : VExpr → VExpr
  | e@(.app (.app (.const c _) t) _) =>
    if c = ``optParam ∨ c = ``autoParam then consumeAnnots t else e
  | e@(.app (.const c _) t) =>
    if c = ``outParam ∨ c = ``semiOutParam then consumeAnnots t else e
  | e => e

/-- Split off exactly `n` leading `∀`-binders. Result telescope is
outermost-first, with binder domains annotation-consumed. -/
def teleSplit : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n+1, .forallE A B => do let (Δ, e) ← teleSplit n B; return (consumeAnnots A :: Δ, e)
  | _+1, _ => none

/-- Split off all leading `∀`-binders (outermost-first, domains
annotation-consumed). -/
def teleAll : VExpr → List VExpr × VExpr
  | .forallE A B => let (Δ, e) := teleAll B; (consumeAnnots A :: Δ, e)
  | e => ([], e)

/-- Rebuild `∀ Δ, e` from an outermost-first telescope. Inverse of
`teleSplit`/`teleAll`. -/
def mkForallOF (Δ : List VExpr) (e : VExpr) : VExpr := Δ.foldr .forallE e

/-- Rebuild `fun Δ => e` from an outermost-first telescope. -/
def mkLamOF (Δ : List VExpr) (e : VExpr) : VExpr := Δ.foldr .lam e

/-- Lift a telescope (outermost-first) over `m` binders inserted at its base:
entry at position `s` has `s` telescope binders below it, so it is lifted at
cutoff `s`. -/
def liftTele (m : Nat) : List VExpr → (s : Nat := 0) → List VExpr
  | [], _ => []
  | A :: Δ, s => A.liftN m s :: liftTele m Δ (s+1)

/-- Lift an expression whose context was `Δ' ++ Γ₂ ++ Γ₀` (with `|Δ'| = s`
binders of the enclosing telescope below it and `|Γ₂| = k₂`) after inserting
`m₁` binders between `Δ'` and `Γ₂`, and `m₂` binders between `Γ₂` and `Γ₀`. -/
def lift2 (m₁ m₂ s k₂ : Nat) (e : VExpr) : VExpr :=
  (e.liftN m₂ (s + k₂)).liftN m₁ s

/-- `liftTele` version of `lift2` for a whole (outermost-first) telescope. -/
def liftTele2 (m₁ m₂ k₂ : Nat) : List VExpr → (s : Nat := 0) → List VExpr
  | [], _ => []
  | A :: Δ, s => lift2 m₁ m₂ s k₂ A :: liftTele2 m₁ m₂ k₂ Δ (s+1)

/-- Does `e` mention any of the block's inductive types?
(cf. `has_ind_occ` / `hasIndOcc`) -/
def hasIndOcc (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => names.contains c
  | .app f a
  | .lam f a
  | .forallE f a => hasIndOcc names f || hasIndOcc names a

/-! ## Views

`mkViews` performs all the *syntactic* destructuring of a `VInductDecl`; the
typing side conditions live in `WF`. -/

/-- A constructor, destructured. -/
structure CtorView where
  name : Name
  /-- Field types: telescope (outermost-first) over the parameter context. -/
  fields : List VExpr
  /-- The index arguments of the result type, in context
  `fields.reverse ++ params.reverse`. -/
  rIndices : List VExpr

/-- One inductive type of the block, destructured. -/
structure TypeView where
  name : Name
  /-- Index types: telescope (outermost-first) over the parameter context. -/
  indices : List VExpr
  ctors : List CtorView

/-- The whole block, destructured. -/
structure View where
  uvars : Nat
  nparams : Nat
  /-- Parameter types: telescope (outermost-first) over `[]`,
  shared syntactically by all types and constructors of the block. -/
  params : List VExpr
  /-- The common result sort level. -/
  lvl : VLevel
  types : List TypeView

def View.names (v : View) : List Name := v.types.map (·.name)
def View.nidx (v : View) : List Nat := v.types.map (·.indices.length)

/-- If `e`, in a context of length `L` whose *last* `np` entries are the block
parameters, is `I_i ls ps is` for one of the block's types — where `ls` is the
expected level list `lvls`, `ps` are exactly the parameter variables and the
index args `is` do not mention the block — return `(i, is)`.
(cf. `is_valid_ind_app`) -/
def validIndApp? (names : List Name) (nidx : List Nat) (lvls : List VLevel)
    (np L : Nat) (e : VExpr) : Option (Nat × List VExpr) := do
  let (f, args) := getAppList e
  let .const c ls := f | failure
  let i ← names.idxOf? c
  guard (ls = lvls)
  let ni ← nidx[i]?
  guard (args.length = np + ni)
  guard (args.take np = (List.range np).map fun k => .bvar (L - 1 - k))
  let ris := args.drop np
  guard (ris.all fun a => !hasIndOcc names a)
  return (i, ris)

/-- Destructure a field type `F` (in a context with `pf` field binders above
the parameters) as a recursive argument `∀ xs, I_it ps is`; returns
`(xs, it, is)`. (cf. `is_rec_argument`; DIVERGENCE: no `whnf`.) -/
def recArg? (names : List Name) (nidx : List Nat) (lvls : List VLevel)
    (np pf : Nat) (F : VExpr) : Option (List VExpr × Nat × List VExpr) := do
  let (xs, body) := teleAll F
  let (it, ris) ← validIndApp? names nidx lvls np (xs.length + pf + np) body
  return (xs, it, ris)

/-- Syntactic destructuring and shape checks for a block.

DIVERGENCE: the parameter telescopes of the block's types and constructors
must agree *syntactically* where the C++ kernel checks `is_def_eq`
(`inductive.cpp:227,418`), and the result sort levels must agree syntactically
where it uses `is_equivalent` (`inductive.cpp:250`). -/
def mkViews (decl : VInductDecl) : Option View := do
  let t₀ :: _ := decl.types | failure
  let (params, _) ← teleSplit decl.nparams t₀.type
  let names := decl.types.map (·.name)
  let headers ← decl.types.mapM fun t => do
    let (params', rest) ← teleSplit decl.nparams t.type
    guard (params' = params)
    let (indices, s) := teleAll rest
    let .sort l := s | failure
    return (indices, l)
  let (_, lvl) ← headers.head?
  guard (headers.all fun (_, l) => l = lvl)
  let nidx := headers.map fun (i, _) => i.length
  let np := decl.nparams
  let types ← (decl.types.zip headers).zipIdx.mapM fun ((t, indices, _), i) => do
    let ctors ← t.ctors.mapM fun c => do
      let (params', rest) ← teleSplit np c.type
      guard (params' = params)
      let (fields, res) := teleAll rest
      let (i', ris) ← validIndApp? names nidx (VLevel.params decl.uvars) np
        (fields.length + np) res
      guard (i' = i)
      return { name := c.name, fields, rIndices := ris : CtorView }
    return { name := t.name, indices, ctors : TypeView }
  return { uvars := decl.uvars, nparams := np, params, lvl, types }

/-! ## Recursor construction

Context discipline: the recursor for type `i` has the binder blocks
(outermost → innermost)

    params (np) | motives (n) | minors (K) | indices_i (nᵢ) | major

matching `mk_rec_infos` in `inductive.cpp` / `Inductive/Add.lean` (all motives
and all minors of the block appear in every recursor). -/

/-- Data for the recursor construction. All `VExpr`s in `params`/`types` are
already level-shifted when `elim` is a fresh parameter. -/
structure RecCtx where
  /-- number of universe parameters of the *recursor* -/
  recUvars : Nat
  np : Nat
  /-- number of types in the block -/
  n : Nat
  /-- total number of minor premises (constructors) in the block -/
  K : Nat
  names : List Name
  nidx : List Nat
  /-- level arguments for references to the block's types/ctors -/
  lvls : List VLevel
  /-- the elimination sort level -/
  elim : VLevel
  params : List VExpr
  types : List TypeView

/-- The type of the `j`-th motive, at its binder (context:
`motives_{<j} ++ params.reverse`):
`∀ (ix : indices_j) (t : I_j params ix), Sort elim`. -/
def motiveType (Θ : RecCtx) (j : Nat) : Option VExpr := do
  let t ← Θ.types[j]?
  let ni := t.indices.length
  let indApp := mkAppList (.const t.name Θ.lvls)
    (((List.range Θ.np).map fun k => .bvar (ni + j + Θ.np - 1 - k)) ++
     ((List.range ni).map fun m => .bvar (ni - 1 - m)))
  return mkForallOF (liftTele j t.indices) (.forallE indApp (.sort Θ.elim))

/-- The recursive fields of a constructor: `(pf, xs, it, ris)` for each field
at position `pf` whose type is `∀ xs, I_it params ris`. -/
def recFields (Θ : RecCtx) (c : CtorView) : List (Nat × List VExpr × Nat × List VExpr) :=
  c.fields.zipIdx.filterMap fun (F, pf) =>
    (recArg? Θ.names Θ.nidx Θ.lvls Θ.np pf F).map fun r => (pf, r)

/-- The induction hypotheses of a minor premise: one per recursive field
`f : ∀ xs, I_it ps is`, of type `∀ xs, motive_it is (f xs)`. Context of the
`ρ`-th hypothesis, innermost first:
`xs | IHs_{<ρ} | fields | minors_{<q} | motives | params`, against the
field's own context `xs | fields_{<pf} | params`. -/
def minorIHs (Θ : RecCtx) (q : Nat) (c : CtorView) : List VExpr :=
  let nf := c.fields.length
  (recFields Θ c).zipIdx.map fun ((pf, xs, it, ris), ρ) =>
    let nx := xs.length
    let xs' := liftTele2 (ρ + (nf - pf)) (q + Θ.n) pf xs
    let ris' := ris.map fun e => lift2 (ρ + (nf - pf)) (q + Θ.n) nx pf e
    let fvar := VExpr.bvar (nx + ρ + (nf - 1 - pf))
    let motiveIdx := nx + ρ + nf + q + (Θ.n - 1 - it)
    mkForallOF xs' (.app (mkAppList (.bvar motiveIdx) ris')
      (mkAppList fvar ((List.range nx).map fun s => .bvar (nx - 1 - s))))

/-- The target of a minor premise: `motive_i (rIndices b) (ctor params b)`,
in context `IHs | fields | minors_{<q} | motives | params`. -/
def minorConcl (Θ : RecCtx) (i q : Nat) (c : CtorView) : VExpr :=
  let nf := c.fields.length
  let R := (recFields Θ c).length
  let ris' := c.rIndices.map fun e => ((e.liftN (q + Θ.n) nf).liftN R 0)
  let ctorApp := mkAppList (.const c.name Θ.lvls)
    (((List.range Θ.np).map fun k => .bvar (R + nf + q + Θ.n + Θ.np - 1 - k)) ++
     ((List.range nf).map fun p => .bvar (R + (nf - 1 - p))))
  .app (mkAppList (.bvar (R + nf + q + (Θ.n - 1 - i))) ris') ctorApp

/-- The type of the minor premise for constructor `c` of type `i`, at its
binder; `q` is the number of *prior* minor premises in the block (context:
`minors_{<q} ++ motives ++ params.reverse`):

`∀ (b : fields) (ih : IHs), motive_i (rIndices b) (ctor params b)`. -/
def minorType (Θ : RecCtx) (i q : Nat) (c : CtorView) : VExpr :=
  mkForallOF (liftTele (q + Θ.n) c.fields)
    (mkForallOF (minorIHs Θ q c) (minorConcl Θ i q c))

/-- All minor premise types, flattened over the block in declaration order
(the telescope after `params ++ motives`). -/
def minorTele (Θ : RecCtx) : List VExpr :=
  (Θ.types.zipIdx.foldl (init := (0, [])) fun (q, acc) (t, i) =>
    t.ctors.foldl (init := (q, acc)) fun (q, acc) c =>
      (q + 1, acc ++ [minorType Θ i q c])).2

/-- The type of the recursor for type `i`:
`∀ (P : params) (M : motives) (m : minors) (ix : indices_i)
   (t : I_i P ix), M_i ix t`. -/
def recType (Θ : RecCtx) (i : Nat) : Option VExpr := do
  let motives ← (List.range Θ.n).mapM (motiveType Θ)
  let minors := minorTele Θ
  guard (minors.length = Θ.K)
  let t ← Θ.types[i]?
  let ni := t.indices.length
  let indices' := liftTele (Θ.K + Θ.n) t.indices
  let majorTy := mkAppList (.const t.name Θ.lvls)
    (((List.range Θ.np).map fun k => .bvar (ni + Θ.K + Θ.n + Θ.np - 1 - k)) ++
     ((List.range ni).map fun m => .bvar (ni - 1 - m)))
  let body := .app (mkAppList (.bvar (1 + ni + Θ.K + (Θ.n - 1 - i)))
      ((List.range ni).map fun m => .bvar (1 + (ni - 1 - m)))) (.bvar 0)
  return mkForallOF Θ.params (mkForallOF motives (mkForallOF minors
    (mkForallOF indices' (.forallE majorTy body))))

/-- The iota rule for constructor `c` (the `q`-th of the block) of type `i`,
as a `VDefEq` abstracted over `params ++ motives ++ minors ++ fields`
(instances are recovered by `β`; cf. how `quotDefEq` is stated):

`rec P M m (rIndices b) (ctor P b) ≡ m_q b (IH-values)`

where each recursive field `f : ∀ xs, I_it ps is` contributes the IH value
`fun xs => rec_it P M m is (f xs)` (cf. `mk_rec_rules`). -/
def iotaRule (Θ : RecCtx) (i q : Nat) (c : CtorView)
    (motives minors : List VExpr) : Option VDefEq := do
  let nf := c.fields.length
  let fields' := liftTele (Θ.K + Θ.n) c.fields
  -- context: fields (nf) | minors (K) | motives (n) | params (np)
  let L := nf + Θ.K + Θ.n + Θ.np
  let paramVars := (List.range Θ.np).map fun k => VExpr.bvar (L - 1 - k)
  let motiveVars := (List.range Θ.n).map fun j => VExpr.bvar (nf + Θ.K + (Θ.n - 1 - j))
  let minorVars := (List.range Θ.K).map fun p => VExpr.bvar (nf + (Θ.K - 1 - p))
  let fieldVars := (List.range nf).map fun p => VExpr.bvar (nf - 1 - p)
  let ris' := c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) nf
  let ctorApp := mkAppList (.const c.name Θ.lvls) (paramVars ++ fieldVars)
  let recLvls := VLevel.params Θ.recUvars
  let recNameI ← Θ.names[i]?
  let lhsBody := mkAppList (.const (Lean.mkRecName recNameI) recLvls)
    (paramVars ++ motiveVars ++ minorVars ++ ris' ++ [ctorApp])
  let ihVals ← (recFields Θ c).mapM fun (pf, xs, it, ris) => do
    let nx := xs.length
    -- context inside `xs`: xs (nx) | fields (nf) | minors (K) | motives (n) | params (np)
    -- vs the original context: xs | fields_{<pf} | params
    let xs' := liftTele2 (nf - pf) (Θ.K + Θ.n) pf xs
    let ris' := ris.map fun e => lift2 (nf - pf) (Θ.K + Θ.n) nx pf e
    let pv := (List.range Θ.np).map fun k => VExpr.bvar (nx + L - 1 - k)
    let mv := (List.range Θ.n).map fun j => VExpr.bvar (nx + nf + Θ.K + (Θ.n - 1 - j))
    let miv := (List.range Θ.K).map fun p => VExpr.bvar (nx + nf + (Θ.K - 1 - p))
    let fvar := VExpr.bvar (nx + (nf - 1 - pf))
    let recNameIt ← Θ.names[it]?
    return mkLamOF xs' (mkAppList (.const (Lean.mkRecName recNameIt) recLvls)
      (pv ++ mv ++ miv ++ ris' ++
        [mkAppList fvar ((List.range nx).map fun s => .bvar (nx - 1 - s))]))
  let rhsBody := mkAppList (.bvar (nf + (Θ.K - 1 - q))) (fieldVars ++ ihVals)
  let tele (e : VExpr) := mkForallOF Θ.params (mkForallOF motives (mkForallOF minors
    (mkForallOF fields' e)))
  let lam (e : VExpr) := mkLamOF Θ.params (mkLamOF motives (mkLamOF minors
    (mkLamOF fields' e)))
  return {
    uvars := Θ.recUvars
    lhs := lam lhsBody
    rhs := lam rhsBody
    type := tele (.app (mkAppList (.bvar (nf + Θ.K + (Θ.n - 1 - i))) ris') ctorApp)
  }

/-- All iota rules of the block, in declaration order. -/
def iotaRules (Θ : RecCtx) : Option (List VDefEq) := do
  let motives ← (List.range Θ.n).mapM (motiveType Θ)
  let minors := minorTele Θ
  (Θ.types.zipIdx.foldlM (init := (0, [])) fun (q, acc) (t, i) =>
    t.ctors.foldlM (init := (q, acc)) fun (q, acc) c => do
      let df ← iotaRule Θ i q c motives minors
      return (q + 1, acc ++ [df])) <&> (·.2)

/-! ## Assembling the environment extension -/

/-- Recursor universe data: with large elimination the recursor gets a fresh
elimination level *prepended* to the block's levels (cf. `get_rec_levels` /
`get_rec_level_params`), so references to the block's constants inside
recursor types shift every level parameter up by one. -/
def elimData (U : Nat) (largeElim : Bool) : Nat × VLevel × List VLevel :=
  if largeElim then (U + 1, .param 0, (List.range U).map fun i => .param (i + 1))
  else (U, .zero, VLevel.params U)

/-- Add the block's type constants (used by `WF` to state constructor
conditions in the right environment). -/
def addTypeConsts (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  decl.types.foldlM (fun env t => env.addConst t.name ⟨decl.uvars, t.type⟩) env

/-- Build the recursor-construction context from a destructured block. -/
def mkRecCtx (v : View) (largeElim : Bool) : RecCtx :=
  let (recUvars, elim, lvls) := elimData v.uvars largeElim
  let shift : VExpr → VExpr := if largeElim then (·.instL lvls) else id
  { recUvars, elim, lvls
    np := v.nparams
    n := v.types.length
    K := v.types.foldl (fun k t => k + t.ctors.length) 0
    names := v.names
    nidx := v.nidx
    params := v.params.map shift
    types := v.types.map fun t => { t with
      indices := t.indices.map shift
      ctors := t.ctors.map fun c => { c with
        fields := c.fields.map shift
        rIndices := c.rIndices.map shift } } }

/-- Add an inductive block to the environment: the type constants, the
constructor constants, one recursor per type, and the iota rules.
Returns `none` if the block is not syntactically well-shaped (`mkViews`) or
any name is duplicated (`addConst`). -/
def addInductCore (env : VEnv) (decl : VInductDecl) (largeElim : Bool) : Option VEnv := do
  let v ← mkViews decl
  let env ← addTypeConsts env decl
  let env ← decl.types.foldlM (init := env) fun env t =>
    t.ctors.foldlM (fun env c => env.addConst c.name ⟨decl.uvars, c.type⟩) env
  let Θ := mkRecCtx v largeElim
  let env ← v.types.zipIdx.foldlM (init := env) fun env (t, i) => do
    let ty ← recType Θ i
    env.addConst (Lean.mkRecName t.name) ⟨Θ.recUvars, ty⟩
  let rules ← iotaRules Θ
  return rules.foldl VEnv.addDefEq env

/-! ## The well-formedness predicate -/

/-- The context of the `pf`-th field of a constructor (fields before it, then
the parameters). -/
def fieldCtx (params fields : List VExpr) (pf : Nat) : List VExpr :=
  (fields.take pf).reverse ++ params.reverse

section
variable (envI : VEnv) (U : Nat) (names : List Name) (nidx : List Nat) (np : Nat)

/-- Strict positivity of a constructor field type (cf. `check_positivity`).
The block's types may only occur (a) not at all, (b) as the field type's
final valid target, or (c) to the right of arrows whose domains do not
mention them; closure under definitional equality plays the role of the
kernel's `whnf`. -/
inductive Positive : List VExpr → VExpr → Prop
  | noOcc : hasIndOcc names A = false → Positive Γ A
  | validApp : (validIndApp? names nidx (VLevel.params U) np Γ.length A).isSome →
      Positive Γ A
  | arrow : hasIndOcc names dom = false → Positive (dom :: Γ) body →
      Positive Γ (.forallE dom body)
  | defeq : envI.IsDefEqU U Γ A B → Positive Γ B → Positive Γ A

end

/-- Conditions under which the block may eliminate into arbitrary sorts
(cf. `elim_only_at_universe_zero`, inverted): the result level is never zero;
or the block is a single type with no constructors; or a single type with a
single constructor each of whose fields either is a proof (its type lives in
`Prop`) or occurs literally among the result's index arguments. -/
def LargeElimOk (envI : VEnv) (v : View) : Prop :=
  v.lvl.IsNeverZero ∨
  match v.types with
  | [t] =>
    match t.ctors with
    | [] => True
    | [c] =>
      ∀ pf F, c.fields[pf]? = some F →
        (∃ u, envI.HasType v.uvars (fieldCtx v.params c.fields pf) F (.sort u) ∧
          u ≈ .zero) ∨
        VExpr.bvar (c.fields.length - 1 - pf) ∈ c.rIndices
    | _ => False
  | _ => False

/-- Well-formedness of an inductive block (cf. `check_inductive_types` /
`check_constructors`): the block destructures (`mkViews`); each type's type
is a type in the ambient environment; each constructor's type is a type in
the environment extended with the block's type constants; each field
satisfies the universe bound (its sort is bounded by the result level unless
the block lands in `Prop`) and strict positivity; and if `largeElim` is
claimed, it is justified. (`largeElim = false` is always sound.) -/
def WFCore (env : VEnv) (decl : VInductDecl) (largeElim : Bool) : Prop :=
  ∃ v envI, mkViews decl = some v ∧ addTypeConsts env decl = some envI ∧
  (∀ t ∈ decl.types, env.IsType decl.uvars [] t.type) ∧
  (∀ t ∈ decl.types, ∀ c ∈ t.ctors, envI.IsType decl.uvars [] c.type) ∧
  (∀ t ∈ v.types, ∀ c ∈ t.ctors, ∀ pf F, c.fields[pf]? = some F →
    (∃ u, envI.HasType decl.uvars (fieldCtx v.params c.fields pf) F (.sort u) ∧
      (v.lvl ≈ .zero ∨ u ≤ v.lvl)) ∧
    Positive envI decl.uvars v.names v.nidx decl.nparams
      (fieldCtx v.params c.fields pf) F) ∧
  (largeElim = true → LargeElimOk envI v)

end IndSpec
