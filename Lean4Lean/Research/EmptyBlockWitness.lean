import Lean4Lean.Research.Inductive.Exists

/-!
A joint witness for the three abstract specification predicates, for both
elimination modes. This empty datatype is deliberately a small nonvacuity
control; constructor, parameter and index behavior have separate tests.
-/

namespace Lean4Lean.EmptyBlockWitness
open IndSpec

def decl : VInductDecl :=
  { uvars := 0, nparams := 0,
    types := [{ name := `ReviewEmpty, uvars := 0, type := .sort (.succ .zero), ctors := [] }] }
def view : View := ⟨0, 0, [], .succ .zero, [⟨`ReviewEmpty, [], []⟩]⟩
def envI : VEnv :=
  { constants := fun n => if `ReviewEmpty = n then some ⟨0, .sort (.succ .zero)⟩ else none,
    defeqs := VEnv.empty.defeqs }

theorem views : mkViews decl = some view := rfl
theorem typesAdded : addTypeConsts VEnv.empty decl = some envI := rfl
theorem sort_typed : VEnv.empty.IsType 0 [] (.sort (.succ .zero)) :=
  ⟨_, .sortDF trivial trivial rfl⟩

theorem core (large : Bool) : WFCore VEnv.empty decl large := by
  refine ⟨view, envI, views, typesAdded, ?_, ?_, ?_, ?_⟩
  · simpa [decl] using sort_typed
  · simp [decl]
  · simp [view]
  · intro _; exact Or.inr trivial

theorem exactness (large : Bool) : WFExact VEnv.empty decl large := by
  intro v hv
  rw [views] at hv
  cases hv
  refine ⟨?_, ?_, ?_⟩
  · simpa [decl, view, teleSplit, mkForallOF, teleAll, VEnv.IsType, VEnv.HasType] using sort_typed
  · simp [decl]
  · cases large <;> simp [mkRecCtx, view, elimData]

theorem telescopes (large : Bool) : WFTele VEnv.empty decl large := by
  intro v hv ei ec _ _ _
  rw [views] at hv
  cases hv
  have noC : ∀ t ∈ (mkRecCtx view large).types, t.ctors = [] := by
    cases large <;> simp [mkRecCtx, view, elimData]
  constructor
  · cases large <;> trivial
  · cases large <;> simp [mkRecCtx, view, elimData, TeleWF]
  · intro i t ht c hc
    have := noC t (List.mem_of_getElem? ht)
    simp_all
  · intro t ht c hc
    simp [noC t ht] at hc
  · intro t ht c hc
    simp [noC t ht] at hc

theorem succeeds_and_ordered (large : Bool) :
    ∃ result, addInductCore VEnv.empty decl large = some result ∧ VEnv.Ordered result := by
  obtain ⟨v, ei, ec, er, rules, _, _, _, _, _, h⟩ :=
    addInductCore_exists .empty (core large) (exactness large) (telescopes large)
      (by simp [decl]) (by intros; rfl) (by decide)
  exact ⟨_, h, addInductCore_WF4 .empty (core large) (exactness large) (telescopes large) h⟩

#print axioms succeeds_and_ordered

end Lean4Lean.EmptyBlockWitness
