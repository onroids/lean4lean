import Lean4Lean.Experimental.SExpr
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.QuotLemmas

/-!
# A refutation of the global experimental pattern axiom

`quotDefEq.lhs` begins with a lambda, but `Pattern.MatchesS` has only
constant, variable and application constructors. The proof uses the MatchesS
conjunct, so choosing a different pattern classifier cannot rescue the axiom.
The concrete environment below is Ordered, constructed directly to avoid
upstream's admitted inductive-ordering lemma.

This concerns `Experimental/SExpr.lean`. PR #56 repairs a different, related
field in the main confluence interface; it does not introduce this axiom.
-/

namespace Lean4Lean

open Params

section
variable [Params]

/-- No pattern matches a `lam`-headed `SExpr`. -/
theorem Pattern.MatchesS.not_lam {p : Pattern} {A b m1 m2} :
    ¬ p.MatchesS (SExpr.lam A b) m1 m2 := nofun

/-- `SExpr.mk` then `instL` preserve the `lam` head. -/
theorem SExpr.mk_instL_lam {A b : VExpr} {ls} :
    SExpr.instL ls (SExpr.mk (.lam A b)) =
    SExpr.lam (SExpr.instL ls (SExpr.mk A)) (SExpr.instL ls (SExpr.mk b)) := rfl

/-- Any `Params` instance whose environment contains `quotDefEq` makes
the axiom `SExpr.Params.extra_pat` deliver `False`. -/
theorem extra_pat_false {ls : List SLevel}
    (hq : Params.env.defeqs quotDefEq) (hls : ls.length = quotDefEq.uvars) :
    False := by
  obtain ⟨p, r, m1, m2, dfs, -, hm, -⟩ := SExpr.Params.extra_pat [] hq hls
  rw [show quotDefEq.lhs = .lam _ _ from rfl, SExpr.mk_instL_lam] at hm
  exact hm.not_lam

end

namespace ExtraPatRefutation

open VEnv

/-- The empty environment plus the constant `Eq`. -/
def env₀ : VEnv :=
  { constants := fun n => if ``Eq = n then some eqConst else none
    defeqs := VEnv.empty.defeqs }

theorem addConst_eq : VEnv.empty.addConst ``Eq eqConst = some env₀ := rfl

theorem eqConst_WF : VConstant.WF VEnv.empty eqConst := by
  have hp0 : (VLevel.param 0).WF 1 := Nat.zero_lt_one
  have hsort : IsDefEq VEnv.empty 1 [] (.sort (.param 0)) (.sort (.param 0))
      (.sort (.succ (.param 0))) := .sortDF hp0 hp0 rfl
  have hb0 : IsDefEq VEnv.empty 1 [.sort (.param 0)] (.bvar 0) (.bvar 0)
      (.sort (.param 0)) := .bvar .zero
  have hb1 : IsDefEq VEnv.empty 1 [.bvar 0, .sort (.param 0)] (.bvar 1) (.bvar 1)
      (.sort (.param 0)) := .bvar (.succ .zero)
  have hs0 : IsDefEq VEnv.empty 1 [.bvar 1, .bvar 0, .sort (.param 0)]
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial rfl
  exact ⟨_, .forallEDF hsort (.forallEDF hb0 (.forallEDF hb1 hs0))⟩

theorem quotReady : env₀.QuotReady := rfl

theorem addQuot_isSome : env₀.addQuot.isSome = true := rfl

/-- `env₀` plus the four `Quot` constants and `quotDefEq`. -/
def env₁ : VEnv := env₀.addQuot.get addQuot_isSome

theorem addQuot_env₀ : env₀.addQuot = some env₁ := (Option.some_get addQuot_isSome).symm

/-- `Ordered` from its constructors directly (`VEnv.WF.ordered` would
drag in the `InductiveLemmas` sorry). -/
theorem env₁_ordered : Ordered env₁ :=
  addQuot_WF (.const .empty eqConst_WF addConst_eq) quotReady addQuot_env₀

theorem env₁_quotDefEq : env₁.defeqs quotDefEq := addQuot_defeq addQuot_env₀

set_option warn.classDefReducibility false in
/-- A concrete `Params` instance containing `quotDefEq`. -/
def badParams : Params where
  env := env₁
  henv := env₁_ordered
  univs := 0
  Pat _ _ := False
  classify _ := none
  pat_simple := False.elim
  pat_wf := False.elim
  pat_uniq h := h.elim

/-- The Experimental axiom set proves `False`:
`[propext, Quot.sound, SExpr.Params.extra_pat]`. -/
theorem sexpr_extra_pat_inconsistent : False :=
  letI : Params := badParams
  extra_pat_false (ls := [.zero, .zero]) env₁_quotDefEq rfl

#print axioms sexpr_extra_pat_inconsistent

end ExtraPatRefutation

end Lean4Lean
