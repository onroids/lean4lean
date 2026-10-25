import Lean4Lean.Research.Inductive.Transport
import Lean4Lean.Theory.Typing.Meta

/-!
# A parameterized recursive telescope witness

For `T (α : Sort u) : α → Prop`, with constructor
`mk : ∀ a, T α a → T α a`, direct typings establish
`RecCtxTelescopeWF`. Its index arguments are variables, so their typings have
direct witnesses. The old translation-inversion probe depended on upstream's
admitted projection definition; this witness uses no translation relation.
Computed-index cases and a general checker-to-spec correspondence are not
established by this example.
-/

namespace Lean4Lean
namespace WFTeleProbe
open IndSpec VEnv

/-- `T`'s type: `∀ (α : Sort u), α → Prop`. -/
def Tty : VExpr := .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.sort .zero))

/-- The target `T α a` (under binders α, a). -/
def Tapp : VExpr := .app (.app (.const `T [.param 0]) (.bvar 1)) (.bvar 0)

/-- `mk`'s type: `∀ (α : Sort u) (a : α), T α a → T α a`. -/
def mkty : VExpr := .forallE (.sort (.param 0)) (.forallE (.bvar 0)
  (.forallE Tapp (.app (.app (.const `T [.param 0]) (.bvar 2)) (.bvar 1))))

def decl : VInductDecl := ⟨1, 1, [⟨⟨⟨1, Tty⟩, `T⟩, [⟨⟨1, mkty⟩, `T.mk⟩]⟩]⟩

/-- The environment after `addTypeConsts`. -/
def envI : VEnv :=
  { constants := fun n => if `T = n then some ⟨1, Tty⟩ else none
    defeqs := VEnv.empty.defeqs }

/-- The environment after also adding the constructor. -/
def envC : VEnv :=
  { constants := fun n => if `T.mk = n then some ⟨1, mkty⟩ else envI.constants n
    defeqs := VEnv.empty.defeqs }

theorem hIeq : addTypeConsts VEnv.empty decl = some envI := rfl

theorem hCeq : decl.types.foldlM (fun env t =>
    t.ctors.foldlM (fun env c =>
      env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI = some envC := rfl

theorem hV : mkViews decl = some
    ⟨1, 1, [.sort (.param 0)], .zero,
      [⟨`T, [.bvar 0], [⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩]⟩]⟩ := rfl

theorem le1 : VEnv.empty ≤ envC where
  constants h := nomatch h
  defeqs h := h.elim

theorem le2 : envI ≤ envC where
  constants {n ci} h := by
    show (if `T.mk = n then some ⟨1, mkty⟩ else envI.constants n) = some ci
    split
    · rename_i hn
      rw [← hn] at h
      exact absurd h (by rw [show envI.constants `T.mk = none from rfl]; exact nofun)
    · exact h
  defeqs h := h.elim

/-- The view of the block (as computed by `mkViews`, see `hV`). -/
def v : View :=
  ⟨1, 1, [.sort (.param 0)], .zero,
    [⟨`T, [.bvar 0], [⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩]⟩]⟩

/-- The five recursor telescope clauses for the concrete parameterized block. -/
theorem probe : RecCtxTelescopeWF envC (mkRecCtx v false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- params_wf : TeleWF envC 1 [] [.sort (.param 0)]
    exact ⟨⟨_, .sortDF (by decide) (by decide) rfl⟩, trivial⟩
  · -- idx_wf
    intro t ht
    obtain rfl : t = ⟨`T, [.bvar 0], [⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩]⟩ :=
      List.mem_singleton.1 ht
    exact ⟨⟨_, .bvar .zero⟩, trivial⟩
  · -- rIndices_fill : the constructor target's index is a variable, so the
    -- fill is canonical `bvar` typing — no evidence pinning
    intro i t hti c hc
    cases i with
    | succ i => cases hti
    | zero =>
      cases hti
      obtain rfl : c = ⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩ := List.mem_singleton.1 hc
      exact ⟨.bvar (by lookup_tac), trivial⟩
  · -- recField_tele (degenerate here: the recursive field binds nothing)
    intro t ht c hc pf xs it ris hmem
    obtain rfl : t = ⟨`T, [.bvar 0], [⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩]⟩ :=
      List.mem_singleton.1 ht
    obtain rfl : c = ⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩ := List.mem_singleton.1 hc
    have hmem' : (pf, xs, it, ris) = ((1 : Nat), ([] : List VExpr), (0 : Nat),
      [VExpr.bvar 0]) := List.mem_singleton.1 hmem
    simp only [Prod.mk.injEq] at hmem'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem'
    exact trivial
  · -- recField_fill : again canonical `bvar` typing
    intro t ht c hc pf xs it ris hmem
    obtain rfl : t = ⟨`T, [.bvar 0], [⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩]⟩ :=
      List.mem_singleton.1 ht
    obtain rfl : c = ⟨`T.mk, [.bvar 0, Tapp], [.bvar 1]⟩ := List.mem_singleton.1 hc
    have hmem' : (pf, xs, it, ris) = ((1 : Nat), ([] : List VExpr), (0 : Nat),
      [VExpr.bvar 0]) := List.mem_singleton.1 hmem
    simp only [Prod.mk.injEq] at hmem'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem'
    intro t' ht'
    cases ht'
    exact ⟨.bvar (by lookup_tac), trivial⟩

#print axioms probe

end WFTeleProbe
end Lean4Lean
