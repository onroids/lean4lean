import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean.ProjectionControl

def TrProj (env : VEnv) (U : Nat) (Γ : List VExpr) (structName : Name)
    (idx : Nat) (e : VExpr) (e' : VExpr) : Prop :=
  ∃ (ls ls' : List VLevel) (params : List VExpr) (motive minor A₀ B₀ : VExpr),
    e' = ((params ++ [motive, minor]).foldl VExpr.app
      (VExpr.const (Lean.mkRecName structName) ls)).app e ∧
    env.HasType U Γ ((params ++ [motive, minor]).foldl VExpr.app
      (VExpr.const (Lean.mkRecName structName) ls)) (.forallE A₀ B₀) ∧
    env.HasType U Γ e A₀ ∧
    env.HasType U Γ e (params.foldl VExpr.app (VExpr.const structName ls'))


-- This copies no admitted interface lemma: it tests the draft definition itself.
def S : VExpr := .const `ReviewS []
def x : VExpr := .const `reviewX []
def recTy : VExpr :=
  .forallE (.sort (.succ .zero))
    (.forallE (.sort .zero) (.forallE S (.sort .zero)))
def envS : VEnv where
  constants n := if `ReviewS = n then some ⟨0, .sort .zero⟩ else none
  defeqs _ := False
def envX : VEnv where
  constants n := if `reviewX = n then some ⟨0, S⟩ else envS.constants n
  defeqs _ := False
def env : VEnv where
  constants n := if `ReviewS.rec = n then some ⟨0, recTy⟩ else envX.constants n
  defeqs _ := False

theorem env_ordered : VEnv.Ordered env := by
  have hS : VEnv.Ordered envS :=
    .const (n := `ReviewS) (ci := ⟨0, .sort .zero⟩)
      .empty ⟨_, .sortDF trivial trivial rfl⟩ rfl
  have hx : VEnv.Ordered envX := .const (n := `reviewX) (ci := ⟨0, S⟩) hS
    ⟨_, .constDF (ci := ⟨0, .sort .zero⟩) (by rfl) (by simp) (by simp) rfl .nil⟩ rfl
  have hsort {Γ : List VExpr} : envX.HasType 0 Γ (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) := .sortDF trivial trivial rfl
  have hprop {Γ : List VExpr} : envX.HasType 0 Γ (.sort .zero)
      (.sort (.succ .zero)) := .sortDF trivial trivial rfl
  have hs {Γ : List VExpr} : envX.HasType 0 Γ S (.sort .zero) :=
    .constDF (ci := ⟨0, .sort .zero⟩) (by rfl) (by simp) (by simp) rfl .nil
  exact .const (n := `ReviewS.rec) (ci := ⟨0, recTy⟩) hx
    ⟨_, .forallEDF hsort (.forallEDF hprop (.forallEDF hs hprop))⟩ rfl

def output : VExpr :=
  .app (.app (.app (.const `ReviewS.rec []) (.sort .zero)) (.bvar 0)) x

theorem subject_typed : env.HasType 0 [.sort .zero] x S :=
  .constDF (ci := ⟨0, S⟩) (by rfl) (by simp) (by simp) rfl .nil

theorem translated (idx : Nat) : TrProj env 0 [.sort .zero] `ReviewS idx x output := by
  have hr : env.HasType 0 [.sort .zero] (.const `ReviewS.rec []) recTy :=
    .constDF (ci := ⟨0, recTy⟩) (by rfl) (by simp) (by simp) rfl .nil
  have hp : env.HasType 0 [.sort .zero] (.sort .zero) (.sort (.succ .zero)) :=
    .sortDF trivial trivial rfl
  have hb : env.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  exact ⟨[], [], [], .sort .zero, .bvar 0, S, .sort .zero, rfl,
    .appDF (.appDF hr hp) hb, subject_typed, subject_typed⟩

theorem subject_closed : x.ClosedN 0 := trivial
theorem output_not_closed : ¬ output.ClosedN 0 := by
  simp [output, VExpr.ClosedN]

/-- The draft projection relation cannot preserve closedness as claimed. -/
theorem closedness_counterexample :
    ∃ env U Γ s i e e', VEnv.Ordered env ∧
      TrProj env U Γ s i e e' ∧ e.ClosedN 0 ∧ ¬ e'.ClosedN 0 :=
  ⟨env, 0, [.sort .zero], `ReviewS, 0, x, output,
    env_ordered, translated 0, subject_closed, output_not_closed⟩

#print axioms closedness_counterexample

end Lean4Lean.ProjectionControl
