import Lean4Lean.Inductive.Add

namespace Lean4Lean.Research
open Lean hiding Environment Exception
open Kernel

/-- One-node uniformity walk (`check_uniform_ind_occs`, kernel/inductive.cpp,
added by lean4#14582 and present in v4.35.0): every occurrence of a datatype
being declared must be applied exactly to the declaration's universe levels
and to its parameters, which at binder depth `offset` are the bound variables
`#(offset-1) … #(offset-nparams)`. A conforming application is not descended
into (its arguments are parameter bvars); an over-applied occurrence is
descended into so the parameter application itself and the indices are
checked as subterms. -/
def uniformIndOccs (indNames : List Name) (lvls : List Level) (np : Nat) :
    Expr → Nat → Bool
  | .app f a, offset =>
    match (Expr.app f a).getAppFn with
    | .const n ls =>
      if indNames.contains n then
        if (Expr.app f a).getAppNumArgs > np then
          uniformIndOccs indNames lvls np f offset &&
          uniformIndOccs indNames lvls np a offset
        else
          (Expr.app f a).getAppNumArgs == np && np ≤ offset && ls == lvls &&
          ((List.range np).all fun i =>
            (Expr.app f a).getAppArgs[i]! == Expr.bvar (offset - 1 - i))
      else
        uniformIndOccs indNames lvls np f offset &&
        uniformIndOccs indNames lvls np a offset
    | _ =>
      uniformIndOccs indNames lvls np f offset &&
      uniformIndOccs indNames lvls np a offset
  | .const n ls, _ =>
    !(indNames.contains n) || (np == 0 && ls == lvls)
  | .lam _ d b _, offset =>
    uniformIndOccs indNames lvls np d offset &&
    uniformIndOccs indNames lvls np b (offset+1)
  | .forallE _ d b _, offset =>
    uniformIndOccs indNames lvls np d offset &&
    uniformIndOccs indNames lvls np b (offset+1)
  | .letE _ t v b _, offset =>
    uniformIndOccs indNames lvls np t offset &&
    uniformIndOccs indNames lvls np v offset &&
    uniformIndOccs indNames lvls np b (offset+1)
  | .mdata _ b, offset => uniformIndOccs indNames lvls np b offset
  | .proj _ _ b, offset => uniformIndOccs indNames lvls np b offset
  | _, _ => true

/-- The uniformity pass over a block's constructor types (member types cannot
mention the block: its names are not yet in the environment when they are
checked). The wrapper below runs it before `Environment.addInductive`, mirroring
`environment::add_inductive`. -/
def checkUniformIndOccs (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) : Except Exception Unit := do
  let lvls := lparams.map Level.param
  let indNames := types.map (·.name)
  for indType in types do
    for ctor in indType.ctors do
      unless uniformIndOccs indNames lvls nparams ctor.type 0 do
        throw <| .other s!"invalid occurrence of datatype being declared in \
          '{ctor.name}': it must be applied to the parameters and universe \
          levels of the mutual declaration"

/-- Candidate precheck, kept separate so the same fixture exercises the upstream entry point. -/
def addInductiveChecked (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  checkUniformIndOccs lparams nparams types
  Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel

end Lean4Lean.Research
