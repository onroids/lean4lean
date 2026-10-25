import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Research.Inductive.Spec

/-!
# Constructor-type witnesses

Concrete abstract typing derivations for Nat, parameterized PAnd, and
universe-polymorphic List, including the level shift used by large elimination.
These witness individual typing conditions. They do not instantiate the full
legacy InductScope or discharge the general typing-injectivity frontier.
-/

namespace Lean4Lean
namespace CtorIsTypeProbe
open VEnv

/-! Each sub-derivation is stated at its intended type with `have`/`show`:
the rules' implicit levels and constants do not unify through `lift`/
`inst`/`instL` on closed sorts, though the results are definitionally equal. -/

/-! ### Block 1: `Nat` (no params, `Type`) -/

def natV : VEnv where
  constants n := if `Nat = n then some ⟨0, .sort (.succ .zero)⟩ else none
  defeqs _ := False

theorem nat_const {Γ : List VExpr} : natV.HasType 0 Γ (.const `Nat []) (.sort (.succ .zero)) :=
  show natV.HasType 0 Γ (.const `Nat []) ((⟨0, .sort (.succ .zero)⟩ : VConstant).type.instL []) from
    .constDF (ci := ⟨0, .sort (.succ .zero)⟩) (by simp [natV]) (by simp) (by simp) rfl .nil

/-- `Nat.zero : Nat` — the constructor type `Nat` is a type. -/
theorem nat_zero : natV.IsType 0 [] (.const `Nat []) := ⟨_, nat_const⟩

/-- `Nat.succ : Nat → Nat`. -/
theorem nat_succ : natV.IsType 0 [] (.forallE (.const `Nat []) (.const `Nat [])) :=
  ⟨_, .forallEDF nat_const nat_const⟩

/-! ### Block 2: `PAnd (a b : Prop) : Prop` (params, small elim, bvar fields) -/

def pandTy : VExpr := .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))

def pandV : VEnv where
  constants n := if `PAnd = n then some ⟨0, pandTy⟩ else none
  defeqs _ := False

theorem prop_sort {Γ : List VExpr} : pandV.HasType 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF ⟨⟩ ⟨⟩ (VLevel.equiv_def.2 fun _ => rfl)

/-- `PAnd.intro : ∀ (a b : Prop), a → b → PAnd a b`. -/
theorem pand_intro : pandV.IsType 0 []
    (.forallE (.sort .zero) (.forallE (.sort .zero)
      (.forallE (.bvar 1) (.forallE (.bvar 1)
        (.app (.app (.const `PAnd []) (.bvar 3)) (.bvar 2)))))) := by
  have ha : pandV.HasType 0 [.sort .zero, .sort .zero] (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have hb : pandV.HasType 0 [.bvar 1, .sort .zero, .sort .zero] (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have hP : pandV.HasType 0 [.bvar 1, .bvar 1, .sort .zero, .sort .zero]
      (.const `PAnd []) pandTy :=
    show pandV.HasType 0 _ (.const `PAnd []) ((⟨0, pandTy⟩ : VConstant).type.instL []) from
      .constDF (ci := ⟨0, pandTy⟩) (by simp [pandV]) (by simp) (by simp) rfl .nil
  have h3 : pandV.HasType 0 [.bvar 1, .bvar 1, .sort .zero, .sort .zero] (.bvar 3) (.sort .zero) :=
    .bvar (.succ (.succ (.succ .zero)))
  have h2 : pandV.HasType 0 [.bvar 1, .bvar 1, .sort .zero, .sort .zero] (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  have hPa : pandV.HasType 0 [.bvar 1, .bvar 1, .sort .zero, .sort .zero]
      (.app (.const `PAnd []) (.bvar 3)) (.forallE (.sort .zero) (.sort .zero)) :=
    .appDF hP h3
  have hres : pandV.HasType 0 [.bvar 1, .bvar 1, .sort .zero, .sort .zero]
      (.app (.app (.const `PAnd []) (.bvar 3)) (.bvar 2)) (.sort .zero) :=
    .appDF hPa h2
  exact ⟨_, .forallEDF prop_sort (.forallEDF prop_sort (.forallEDF ha (.forallEDF hb hres)))⟩

/-! ### Block 3: `List (α : Type u) : Type u` (params, LARGE elim, `Us = [u]`) -/

def listTy : VExpr := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))

def listV : VEnv where
  constants n := if `List = n then some ⟨1, listTy⟩ else none
  defeqs _ := False

theorem list_const {Γ : List VExpr} :
    listV.HasType 1 Γ (.const `List [.param 0]) listTy :=
  show listV.HasType 1 Γ (.const `List [.param 0]) ((⟨1, listTy⟩ : VConstant).type.instL [.param 0]) from
    .constDF (ci := ⟨1, listTy⟩) (by simp [listV])
      (by intro l hl; simp only [List.mem_singleton] at hl; subst hl; decide)
      (by intro l hl; simp only [List.mem_singleton] at hl; subst hl; decide)
      rfl (.cons (VLevel.equiv_def.2 fun _ => rfl) .nil)

theorem typeu_sort {Γ : List VExpr} :
    listV.HasType 1 Γ (.sort (.succ (.param 0))) (.sort (.succ (.succ (.param 0)))) :=
  .sortDF (by decide) (by decide) (VLevel.equiv_def.2 fun _ => rfl)

/-- `List.nil : ∀ α : Type u, List α`. -/
theorem list_nil : listV.IsType 1 []
    (.forallE (.sort (.succ (.param 0))) (.app (.const `List [.param 0]) (.bvar 0))) := by
  have h0 : listV.HasType 1 [.sort (.succ (.param 0))] (.bvar 0) (.sort (.succ (.param 0))) :=
    .bvar .zero
  have hres : listV.HasType 1 [.sort (.succ (.param 0))]
      (.app (.const `List [.param 0]) (.bvar 0)) (.sort (.succ (.param 0))) :=
    .appDF list_const h0
  exact ⟨_, .forallEDF typeu_sort hres⟩

/-- `List.cons : ∀ α : Type u, α → List α → List α`. -/
theorem list_cons : listV.IsType 1 []
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0)
        (.forallE (.app (.const `List [.param 0]) (.bvar 1))
          (.app (.const `List [.param 0]) (.bvar 2))))) := by
  have hα : listV.HasType 1 [.sort (.succ (.param 0))] (.bvar 0) (.sort (.succ (.param 0))) :=
    .bvar .zero
  have h1 : listV.HasType 1 [.bvar 0, .sort (.succ (.param 0))] (.bvar 1) (.sort (.succ (.param 0))) :=
    .bvar (.succ .zero)
  have hL1 : listV.HasType 1 [.bvar 0, .sort (.succ (.param 0))]
      (.app (.const `List [.param 0]) (.bvar 1)) (.sort (.succ (.param 0))) :=
    .appDF list_const h1
  have h2 : listV.HasType 1 [.app (.const `List [.param 0]) (.bvar 1), .bvar 0, .sort (.succ (.param 0))]
      (.bvar 2) (.sort (.succ (.param 0))) :=
    .bvar (.succ (.succ .zero))
  have hL2 : listV.HasType 1 [.app (.const `List [.param 0]) (.bvar 1), .bvar 0, .sort (.succ (.param 0))]
      (.app (.const `List [.param 0]) (.bvar 2)) (.sort (.succ (.param 0))) :=
    .appDF list_const h2
  exact ⟨_, .forallEDF typeu_sort (.forallEDF hα (.forallEDF hL1 hL2))⟩

/-- **The `Us → Us*` lineup.** The hypothesis is stated at the block's
`Us = [u]` (`U = 1`); the recursor half consumes it at the extended
`Us* = [v, u]` (`U = 2`) along `elimData 1 true`'s shift `[.param 1]`.
`IsType.instL` carries it across; the shift list is exactly `elimData`'s. -/
theorem list_cons_at_recUs :
    listV.IsType 2 []
      ((.forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2)))) : VExpr).instL [.param 1]) :=
  list_cons.instL (by intro l hl; simp only [List.mem_singleton] at hl; subst hl; decide)

/-- The shift used above is `elimData`'s, not a hand-picked one. -/
example : (IndSpec.elimData 1 true).2.2 = [.param 1] := by decide

/-! ### From the probe environments to the run's

The witnesses above live in hand-built environments (one constant each, no
defeqs). `hctorIsType` is discharged at the run-produced types-added
`venvT`, which is at least as large on both components: it contains the
block's type constant with the same `VConstant` (`⟨uvars, type-translation⟩`,
what `addTypeConsts` inserts) and any set of defeqs is `≥ (fun _ => False)`.
The step from the probe environment to the run's is `IsType.mono`
(`Theory/Typing/Lemmas.lean`), cited here rather than left implicit. -/

/-- The `List` witnesses transport to any environment extending `listV`. -/
theorem list_cons_at_venvT {venvT : VEnv} (hle : listV ≤ venvT) :
    venvT.IsType 1 []
      (.forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))) :=
  list_cons.mono hle

/-- And the `≤` premise is discharged by the run's `List` constant being
`⟨1, listTy⟩`: `VEnv.LE` asks only that `listV`'s constants and defeqs be
present. -/
theorem listV_le {venvT : VEnv} (hL : venvT.constants `List = some ⟨1, listTy⟩) :
    listV ≤ venvT := by
  refine ⟨fun {n a} h => ?_, fun {df} h => h.elim⟩
  simp only [listV] at h
  split at h
  · rename_i heq; cases h; exact heq ▸ hL
  · cases h

end CtorIsTypeProbe
end Lean4Lean
