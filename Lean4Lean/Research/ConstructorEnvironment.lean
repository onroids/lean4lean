import Lean4Lean.Research.TelescopeWitness
import Lean4Lean.Theory.Typing.Strong

/-!
# Regression for a repaired defect in our draft specification

An earlier version of our `WFExact` demanded constructor typing before the
block's type constants existed. The old clause is refuted here, and the repaired
clause is witnessed at the types-added environment for the same recursive block.
`WFExact` was introduced by our experiment: this was not a defect in upstream
lean4lean. Both results are checked independently of admitted typing lemmas.
-/

namespace Lean4Lean
namespace WFExactRefutation
open IndSpec WFTeleProbe

def venv0 : VEnv := {}

theorem venv0_ordered : VEnv.Ordered venv0 :=
  VEnv.Ordered.empty

theorem venv0_none (n : Name) : venv0.constants n = none := rfl

/-- The constructor clause of `WFExact` as it stood before the repair. -/
def ctorClauseAtBase (env : VEnv) (decl : VInductDecl) : Prop :=
  ∀ v, mkViews decl = some v →
    ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ restc,
      teleSplit decl.nparams c.type = some (v.params, restc) →
      ∃ u, env.IsDefEq decl.uvars [] c.type
        (mkForallOF v.params (mkForallOF (teleAll restc).1 (teleAll restc).2))
        (.sort u)

/-- The typed-context facts the inversions need, under the two binders of `mk`. -/
theorem ctx2 : OnCtx [VExpr.bvar 0, .sort (.param 0)] (venv0.IsType 1) :=
  ⟨⟨trivial, ⟨_, .sortDF (by decide) (by decide) (VLevel.equiv_def.2 fun _ => rfl)⟩⟩,
    ⟨_, .bvar .zero⟩⟩

theorem params_pinned {v : View} (hv : mkViews decl = some v) : v.params = [.sort (.param 0)] := by
  obtain ⟨-, -, -, -, hlen, hty⟩ := mkViews_inv hv
  have h0 : v.types[0]? = some (v.types[0]'(by rw [hlen]; decide)) := List.getElem?_eq_getElem _
  obtain ⟨t, ht, -, ⟨rest, hsplit, -⟩, -⟩ := hty 0 _ h0
  have ht' : t = decl.types[0] := by
    have : decl.types[0]? = some decl.types[0] := List.getElem?_eq_getElem _
    exact Option.some.inj (ht.symm.trans this)
  subst ht'
  have e : teleSplit decl.nparams (decl.types[0]).type
      = some ([.sort (.param 0)], .forallE (.bvar 0) (.sort .zero)) := rfl
  rw [e] at hsplit
  exact (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hsplit).1.symm

/-- **The refutation** of the base-environment clause. -/
theorem wfexact_unsat : ¬ ctorClauseAtBase venv0 decl := by
  intro h
  have hsome : (mkViews decl).isSome := by decide
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  have hparams := params_pinned hv
  have hmem : (⟨⟨1, mkty⟩, `T.mk⟩ : VConstVal) ∈ (decl.types[0]).ctors := List.mem_singleton.2 rfl
  obtain ⟨u, hdq⟩ := h v hv (decl.types[0]) (List.mem_singleton.2 rfl) _ hmem
    (.forallE (.bvar 0) (.forallE Tapp (.app (.app (.const `T [.param 0]) (.bvar 2)) (.bvar 1))))
    (by rw [hparams]; rfl)
  have hT : venv0.HasType 1 [] mkty (.sort u) := hdq.hasType.1
  have h1 := (hT.forallE_inv venv0_ordered).2
  obtain ⟨_, h2⟩ := (h1.forallE_inv venv0_ordered).2
  obtain ⟨_, h3⟩ := (h2.forallE_inv venv0_ordered).1
  obtain ⟨A, B, h4, -⟩ := h3.app_inv venv0_ordered ctx2
  obtain ⟨A', B', h5, -⟩ := h4.app_inv venv0_ordered ctx2
  obtain ⟨ci, hci, -⟩ := h5.const_inv venv0_ordered ctx2
  rw [venv0_none] at hci
  cases hci

/-! ### The repaired clause has a model at the same block -/

theorem envI_T : envI.constants `T = some ⟨1, Tty⟩ := by
  exact addTypeConsts_lookup hIeq _ (List.mem_singleton.2 rfl)

theorem sortu_ty {Γ : List VExpr} :
    envI.HasType 1 Γ (.sort (.param 0)) (.sort (.succ (.param 0))) :=
  .sortDF (by decide) (by decide) (VLevel.equiv_def.2 fun _ => rfl)

theorem T_ty {Γ : List VExpr} : envI.HasType 1 Γ (.const `T [.param 0]) Tty :=
  show envI.HasType 1 Γ (.const `T [.param 0]) ((⟨1, Tty⟩ : VConstant).type.instL [.param 0]) from
    .constDF (ci := ⟨1, Tty⟩) envI_T
      (by intro l hl; simp only [List.mem_singleton] at hl; subst hl; decide)
      (by intro l hl; simp only [List.mem_singleton] at hl; subst hl; decide)
      rfl (.cons (VLevel.equiv_def.2 fun _ => rfl) .nil)

/-- `mk`'s type is a type at `envI`. -/
theorem mkty_isType : envI.IsType 1 [] mkty := by
  have hα : envI.HasType 1 [.sort (.param 0)] (.bvar 0) (.sort (.param 0)) := .bvar .zero
  have hα1 : envI.HasType 1 [.bvar 0, .sort (.param 0)] (.bvar 1) (.sort (.param 0)) :=
    .bvar (.succ .zero)
  have ha : envI.HasType 1 [.bvar 0, .sort (.param 0)] (.bvar 0) (.bvar 1) := .bvar .zero
  have hTα : envI.HasType 1 [.bvar 0, .sort (.param 0)] (.app (.const `T [.param 0]) (.bvar 1))
      (.forallE (.bvar 1) (.sort .zero)) := .appDF T_ty hα1
  have hTapp : envI.HasType 1 [.bvar 0, .sort (.param 0)] Tapp (.sort .zero) := .appDF hTα ha
  have hα2 : envI.HasType 1 [Tapp, .bvar 0, .sort (.param 0)] (.bvar 2) (.sort (.param 0)) :=
    .bvar (.succ (.succ .zero))
  have ha1 : envI.HasType 1 [Tapp, .bvar 0, .sort (.param 0)] (.bvar 1) (.bvar 2) :=
    .bvar (.succ .zero)
  have hTα2 : envI.HasType 1 [Tapp, .bvar 0, .sort (.param 0)]
      (.app (.const `T [.param 0]) (.bvar 2)) (.forallE (.bvar 2) (.sort .zero)) :=
    .appDF T_ty hα2
  have hres : envI.HasType 1 [Tapp, .bvar 0, .sort (.param 0)]
      (.app (.app (.const `T [.param 0]) (.bvar 2)) (.bvar 1)) (.sort .zero) :=
    .appDF hTα2 ha1
  exact ⟨_, .forallEDF sortu_ty (.forallEDF hα (.forallEDF hTapp hres))⟩

/-- **The witness**: the repaired (types-added) constructor clause holds for `mk`. -/
theorem wfexact_ctor_sat :
    ∀ v, mkViews decl = some v →
      ∀ restc, teleSplit decl.nparams mkty = some (v.params, restc) →
      ∃ u, envI.IsDefEq decl.uvars [] mkty
        (mkForallOF v.params (mkForallOF (teleAll restc).1 (teleAll restc).2))
        (.sort u) := by
  intro v hv restc hsplit
  rw [params_pinned hv] at hsplit ⊢
  have e : teleSplit decl.nparams mkty = some ([.sort (.param 0)],
      .forallE (.bvar 0) (.forallE Tapp (.app (.app (.const `T [.param 0]) (.bvar 2)) (.bvar 1)))) := rfl
  rw [e] at hsplit
  obtain ⟨-, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj hsplit
  obtain ⟨u, hu⟩ := mkty_isType
  exact ⟨u, hu⟩

end WFExactRefutation
end Lean4Lean
