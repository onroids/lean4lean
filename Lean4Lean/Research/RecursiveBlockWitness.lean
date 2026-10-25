import Lean4Lean.Research.Inductive.Exists

/-! A joint witness with two constructors, a recursive field, and large elimination. -/

namespace Lean4Lean.RecursiveBlockWitness
open IndSpec

def n : VExpr := .const `ReviewNat []
def z : VConstVal := ⟨⟨0, n⟩, `ReviewNat.zero⟩
def s : VConstVal := ⟨⟨0, .forallE n n⟩, `ReviewNat.succ⟩
def member : VInductiveType :=
  { name := `ReviewNat, uvars := 0, type := .sort (.succ .zero), ctors := [z, s] }
def decl : VInductDecl := ⟨0, 0, [member]⟩
def zv : CtorView := ⟨z.name, [], []⟩
def sv : CtorView := ⟨s.name, [n], []⟩
def tv : TypeView := ⟨member.name, [], [zv, sv]⟩
def view : View := ⟨0, 0, [], .succ .zero, [tv]⟩
def envI : VEnv :=
  { constants := fun k => if `ReviewNat = k then some ⟨0, .sort (.succ .zero)⟩ else none,
    defeqs := VEnv.empty.defeqs }

theorem views : mkViews decl = some view := rfl
theorem typesAdded : addTypeConsts VEnv.empty decl = some envI := rfl
theorem sort_typed : VEnv.empty.IsType 0 [] (.sort (.succ .zero)) :=
  ⟨_, .sortDF trivial trivial rfl⟩
theorem n_typed {Γ : List VExpr} : envI.HasType 0 Γ n (.sort (.succ .zero)) :=
  .constDF (ci := ⟨0, .sort (.succ .zero)⟩) (by rfl) (by simp) (by simp) rfl .nil
theorem ctor_typed : ∀ c ∈ member.ctors, envI.IsType 0 [] c.type := by
  intro c hc
  rcases (show c = z ∨ c = s from by simpa [member] using hc) with rfl | rfl
  · exact ⟨_, n_typed⟩
  · exact ⟨_, .forallEDF n_typed n_typed⟩

theorem core : WFCore VEnv.empty decl true := by
  refine ⟨view, envI, views, typesAdded, ?_, ?_, ?_, ?_⟩
  · simpa [decl, member] using sort_typed
  · simpa [decl] using ctor_typed
  · intro t ht c hc pf F hF
    have : t = tv := by simpa [view] using ht
    subst t
    rcases (show c = zv ∨ c = sv from by simpa [tv] using hc) with rfl | rfl
    · simp [zv] at hF
    · cases pf with
      | zero =>
        have : n = F := by simpa [sv] using hF
        subst F
        exact ⟨⟨_, n_typed, Or.inr (VLevel.le_refl _)⟩, .validApp (by decide)⟩
      | succ pf => simp [sv] at hF
  · intro _
    exact Or.inl (by intro ls; simp [view, VLevel.eval])

theorem exactness : WFExact VEnv.empty decl true := by
  intro v hv
  rw [views] at hv
  cases hv
  refine ⟨?_, ?_, ?_⟩
  · simpa [decl, member, view, teleSplit, teleAll, mkForallOF, VEnv.IsType, VEnv.HasType]
      using sort_typed
  · intro ei hei t ht c hc rest hr
    rw [typesAdded] at hei
    cases hei
    have : t = member := by simpa [decl] using ht
    subst t
    rcases (show c = z ∨ c = s from by simpa [member] using hc) with rfl | rfl
    · have : n = rest := by simpa [decl, view, z, teleSplit] using hr
      subst rest
      exact ⟨_, n_typed⟩
    · have : VExpr.forallE n n = rest := by simpa [decl, view, s, teleSplit] using hr
      subst rest
      exact ⟨_, .forallEDF n_typed n_typed⟩
  · intro t ht c hc pf xs it ris hf F hF
    have : t = tv := by simpa [mkRecCtx, view, tv, zv, sv, n, elimData, VExpr.instL] using ht
    subst t
    rcases (show c = zv ∨ c = sv from by simpa [tv] using hc) with rfl | rfl
    · simp [zv] at hF
    · cases pf with
      | zero =>
        have : n = F := by simpa [sv] using hF
        subst F
        rfl
      | succ pf => simp [sv] at hF

theorem telescopes : WFTele VEnv.empty decl true := by
  intro v hv ei ec _ _ _
  rw [views] at hv
  cases hv
  have types : (mkRecCtx view true).types = [tv] := rfl
  have rz : recFields (mkRecCtx view true) zv = [] := rfl
  have rs : recFields (mkRecCtx view true) sv = [(0, [], 0, [])] := rfl
  constructor
  · trivial
  · intro t ht
    have : t = tv := by simpa [types] using ht
    subst t
    trivial
  · intro i t ht c hc
    have : t = tv := by simpa [types] using List.mem_of_getElem? ht
    subst t
    rcases (show c = zv ∨ c = sv from by simpa [tv] using hc) with rfl | rfl <;> trivial
  · intro t ht c hc pf xs it ris hf
    have : t = tv := by simpa [types] using ht
    subst t
    rcases (show c = zv ∨ c = sv from by simpa [tv] using hc) with rfl | rfl
    · simp [rz] at hf
    · have : (pf, xs, it, ris) = (0, [], 0, []) := by simpa [rs] using hf
      cases this
      trivial
  · intro t ht c hc pf xs it ris hf t' ht'
    have : t = tv := by simpa [types] using ht
    subst t
    have : t' = tv := by simpa [types] using List.mem_of_getElem? ht'
    subst t'
    rcases (show c = zv ∨ c = sv from by simpa [tv] using hc) with rfl | rfl
    · simp [rz] at hf
    · have : (pf, xs, it, ris) = (0, [], 0, []) := by simpa [rs] using hf
      cases this
      trivial

theorem succeeds_and_ordered :
    ∃ result, addInductCore VEnv.empty decl true = some result ∧ VEnv.Ordered result := by
  obtain ⟨v, ei, ec, er, rules, _, _, _, _, _, h⟩ :=
    addInductCore_exists .empty core exactness telescopes
      (by intros; rfl) (by intros; rfl) (by decide)
  exact ⟨_, h, addInductCore_WF4 .empty core exactness telescopes h⟩

#print axioms succeeds_and_ordered

end Lean4Lean.RecursiveBlockWitness
