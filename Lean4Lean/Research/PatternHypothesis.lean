import Lean4Lean.Experimental.NormalEq
import Lean4Lean.Theory.Quot

namespace Lean4Lean

/-! ## The `Typing.extra_pat` field (Experimental/NormalEq.lean)

The same defect in hypothesis-class form: `Typing.extra_pat` requires
`Pattern.Matches` (const/app spines only) to match the lhs instance of
every environment defeq, so no `Typing` instance exists for an
environment containing `quotDefEq`. Being a structure field rather than
a global axiom, this makes the `Experimental/ParallelReduction.lean`
results vacuous for such environments rather than inconsistent. -/

theorem Pattern.Matches.not_lam {p : Pattern} {A b : VExpr} {m1 m2} :
    ¬ p.Matches (.lam A b) m1 m2 := nofun

theorem Typing.extra_pat_unsat (TY : Typing) (hq : TY.env.defeqs quotDefEq)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF TY.univs)
    (hlen : ls.length = quotDefEq.uvars) : False := by
  obtain ⟨p, r, m1, m2, -, hm, -⟩ := TY.extra_pat (Γ := []) hq hls hlen
  rw [show quotDefEq.lhs = .lam _ _ from rfl] at hm
  exact hm.not_lam

end Lean4Lean
