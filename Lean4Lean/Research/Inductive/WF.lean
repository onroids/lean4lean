import Lean4Lean.Research.Inductive.Spec
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Ordered-environment preservation for the abstract construction

This file proves recursor and iota-rule typing from the explicit `RecCtxWF`
bundle, then proves `addInductCore_WF`. `Transport.lean` packages the assumptions
as `WFCore ∧ WFExact ∧ WFTele` in `addInductCore_WF4`. The dependency audit checks
both theorem bodies and the specification definitions against standard axioms.

The proof is organized into telescope identities, telescope/application typing,
recursor typing, and iota-rule typing. None of these results by themselves
establish that the executable checker supplies the required premises.
-/

namespace Lean4Lean
namespace IndSpec

open VExpr

/-! ## Syntactic layer -/

/-- Instantiate the base variable of a telescope: if `Δ` is a telescope whose
base context has an entry at depth `k`, substitute `e` for it. Entry at
position `s` in `Δ` sits under `s` extra binders, so it is instantiated at
`k + s`. -/
def instTele (e : VExpr) : List VExpr → (k : Nat := 0) → List VExpr
  | [], _ => []
  | A :: Δ, k => A.inst e k :: instTele e Δ (k+1)

@[simp] theorem instTele_nil : instTele e [] k = [] := rfl
@[simp] theorem instTele_cons :
    instTele e (A :: Δ) k = A.inst e k :: instTele e Δ (k+1) := rfl

@[simp] theorem instTele_length : ∀ {Δ k}, (instTele e Δ k).length = Δ.length
  | [], _ => rfl
  | _ :: _, _ => congrArg Nat.succ instTele_length

@[simp] theorem liftTele_nil : liftTele m ([] : List VExpr) k = [] := rfl
@[simp] theorem liftTele_cons :
    liftTele m (A :: Δ) k = A.liftN m k :: liftTele m Δ (k+1) := rfl

@[simp] theorem liftTele_length : ∀ {Δ k}, (liftTele m Δ k).length = Δ.length
  | [], _ => rfl
  | _ :: _, _ => congrArg Nat.succ liftTele_length

@[simp] theorem mkForallOF_nil : mkForallOF [] B = B := rfl
@[simp] theorem mkForallOF_cons :
    mkForallOF (A :: Δ) B = .forallE A (mkForallOF Δ B) := rfl

/-- Substituting under a whole telescope commutes with `mkForallOF`. -/
theorem mkForallOF_inst : ∀ {Δ : List VExpr} {B e k},
    (mkForallOF Δ B).inst e k = mkForallOF (instTele e Δ k) (B.inst e (k + Δ.length))
  | [], _, _, _ => rfl
  | A :: Δ, B, e, k => by
    have h : k + (A::Δ).length = (k+1) + Δ.length := by simp; omega
    rw [h, instTele_cons]
    show VExpr.forallE (A.inst e k) ((mkForallOF Δ B).inst e (k+1)) = _
    rw [mkForallOF_inst (Δ := Δ), mkForallOF_cons]

/-- Lifting a whole telescope commutes with `mkForallOF`. -/
theorem mkForallOF_liftN : ∀ {Δ : List VExpr} {B n k},
    (mkForallOF Δ B).liftN n k = mkForallOF (liftTele n Δ k) (B.liftN n (k + Δ.length))
  | [], _, _, _ => rfl
  | A :: Δ, B, n, k => by
    have h : k + (A::Δ).length = (k+1) + Δ.length := by simp; omega
    rw [h, liftTele_cons]
    show VExpr.forallE (A.liftN n k) ((mkForallOF Δ B).liftN n (k+1)) = _
    rw [mkForallOF_liftN (Δ := Δ), mkForallOF_cons]

@[simp] theorem mkAppList_nil : mkAppList f [] = f := rfl
@[simp] theorem mkAppList_cons : mkAppList f (a :: es) = mkAppList (.app f a) es := rfl

theorem mkAppList_liftN : ∀ {es f},
    (mkAppList f es).liftN n k = mkAppList (f.liftN n k) (es.map (VExpr.liftN n · k))
  | [], _ => rfl
  | _ :: _, _ => by simp [mkAppList_liftN (es := _)]; rfl

/-! ## Typing layer -/

variable (env : VEnv) (U : Nat) in
/-- `Δ` (outermost-first) is a well-formed telescope over `Γ₀`. -/
def TeleWF : List VExpr → List VExpr → Prop
  | _, [] => True
  | Γ₀, A :: Δ => env.IsType U Γ₀ A ∧ TeleWF (A :: Γ₀) Δ

variable (env : VEnv) (U : Nat) (Γ : List VExpr) in
/-- `es` fills the telescope `Δ` in ambient context `Γ`: the first argument
has the first entry's type, and the rest fill the instantiated remainder.
All entries of `Δ` here are types over `Γ` (with the telescope's own binders
substituted away as the spine is consumed). -/
def FillsTele : List VExpr → List VExpr → Prop
  | [], [] => True
  | A :: Δ, e :: es => env.HasType U Γ e A ∧ FillsTele (instTele e Δ) es
  | _, _ => False

theorem FillsTele.length_eq : ∀ {Δ es}, FillsTele env U Γ Δ es → Δ.length = es.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by
    have := h.length_eq; simp at this; simp [this]
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- The type of `f es` when `f : ∀ Δ, B` and `es` fills `Δ`: substitute each
argument into `B` at the depth of its binder (arguments are consumed
outermost-first, so the head argument's binder sits under the remaining
`es.length` binders). -/
def instUnder (B : VExpr) : List VExpr → VExpr
  | [] => B
  | e :: es => instUnder (B.inst e es.length) es

@[simp] theorem instUnder_nil : instUnder B [] = B := rfl
@[simp] theorem instUnder_cons :
    instUnder B (e :: es) = instUnder (B.inst e es.length) es := rfl

/-- Spine application: applying a function of telescope type to a spine that
fills the telescope. -/
theorem FillsTele.appList : ∀ {Δ es B f}, FillsTele env U Γ Δ es →
    env.HasType U Γ f (mkForallOF Δ B) →
    env.HasType U Γ (mkAppList f es) (instUnder B es)
  | [], [], _, _, _, hf => hf
  | A :: Δ, e :: es, B, f, ⟨he, hes⟩, hf => by
    have happ : env.HasType U Γ (.app f e) ((mkForallOF Δ B).inst e) :=
      hf.app he
    rw [mkForallOF_inst, Nat.zero_add] at happ
    have hlen : Δ.length = es.length := by have := hes.length_eq; simpa using this
    rw [instUnder_cons, ← hlen]
    exact hes.appList happ
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => nomatch h

/-! ## Variable spines

Applying a head to the variables that point at (lifted copies of) its own
telescope's binders. The key invariant: consuming the outermost variable
`bvar (n-1)` of a telescope lifted by `n` leaves the tail lifted by `n-1`. -/

/-- Substituting `bvar (n-1)` for the variable a lift by `n` skipped over:
one binder's worth of the lift is consumed by the substitution. -/
theorem inst_liftN_bvar' : ∀ (e : VExpr) (n j : Nat),
    (e.liftN (n+1) (j+1)).inst (.bvar n) j = e.liftN n j
  | .bvar i, n, j => by
    simp only [liftN, inst, instVar, liftVar]
    split <;> rename_i h₁
    · rcases Nat.lt_or_ge i j with h | h
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · have : i = j := by omega
        subst this
        rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_right (by omega)]
        simp; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1; omega
  | .sort .., _, _ | .const .., _, _ => rfl
  | .app .., n, j => by simp only [liftN, inst, inst_liftN_bvar']
  | .lam .., n, j | .forallE .., n, j => by simp only [liftN, inst, inst_liftN_bvar']

/-- Telescope version of `inst_liftN_bvar'`. -/
theorem instTele_liftTele : ∀ {Δ : List VExpr} {n k},
    instTele (.bvar n) (liftTele (n+1) Δ (k+1)) k = liftTele n Δ k
  | [], _, _ => rfl
  | A :: Δ, n, k => by
    simp only [liftTele_cons, instTele_cons, inst_liftN_bvar', instTele_liftTele]

/-- Peeling one element off a variable spine. -/
theorem spine_succ {p n : Nat} :
    (List.range (p+1)).map (fun k => VExpr.bvar (n + 1 - 1 - k))
      = .bvar n :: (List.range p).map fun k => .bvar (n - 1 - k) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  show VExpr.bvar (n + 1 - 1 - (k + 1)) = _
  congr 1; omega

/-- The variable spine `[bvar (n-1), ..., bvar (n - Δ.length)]` fills the
telescope `liftTele n Δ`, provided the context looks up each variable at the
matching (lift of the) telescope entry. -/
theorem fills_varSpine : ∀ {Δ : List VExpr} {n : Nat} {Γ},
    Δ.length ≤ n →
    (∀ j A, Δ[j]? = some A → Lookup Γ (n - 1 - j) (A.liftN (n - j))) →
    FillsTele env U Γ (liftTele n Δ)
      ((List.range Δ.length).map fun k => .bvar (n - 1 - k))
  | [], _, _, _, _ => trivial
  | A :: Δ, n, Γ, hn, hlk => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 :=
      ⟨n - 1, by have h := hn; simp at h; omega⟩
    have hhead : env.HasType U Γ (.bvar n) (A.liftN (n+1)) := by
      have := hlk 0 A rfl
      exact .bvar (by simpa using this)
    rw [List.length_cons, spine_succ]
    refine ⟨hhead, ?_⟩
    show FillsTele env U Γ (instTele (.bvar n) (liftTele (n+1) Δ 1)) _
    rw [show (1 : Nat) = 0 + 1 from rfl, instTele_liftTele]
    refine fills_varSpine (by have h := hn; simp at h; omega)
      (fun j A h => ?_)
    have := hlk (j+1) A (by simpa using h)
    rwa [show n + 1 - 1 - (j+1) = n - 1 - j by omega,
      show n + 1 - (j+1) = n - j by omega] at this

/-! ## Context anchoring -/

/-- `Lookup` only inspects entries up to its index, so a context can be
extended below. -/
theorem lookup_append_left : ∀ {Ξ Ξ₂ : List VExpr} {i A},
    Lookup Ξ i A → Lookup (Ξ ++ Ξ₂) i A
  | _ :: _, _, _, _, .zero => .zero
  | _ :: _, _, _, _, .succ h => .succ (lookup_append_left h)

/-- Looking up the entry just below a context block. -/
theorem lookup_at_length : ∀ (Ξ : List VExpr) (A : VExpr),
    Lookup (Ξ ++ [A]) Ξ.length (A.liftN (Ξ.length + 1))
  | [], _ => .zero
  | B :: Ξ, A => by
    have h := (lookup_at_length Ξ A).succ (A := B)
    simpa [VExpr.liftN_succ] using h

/-- Looking up the `j`-th entry of a telescope block placed as a context
(reversed, so entry `0` is deepest). -/
theorem lookup_teleBlock : ∀ {Ψ : List VExpr} {j A}, Ψ[j]? = some A →
    Lookup Ψ.reverse (Ψ.length - 1 - j) (A.liftN (Ψ.length - j))
  | B :: Ψ', 0, A, hA => by
    have hBA : B = A := by simpa using hA
    subst hBA
    have := lookup_at_length Ψ'.reverse B
    simpa using this
  | B :: Ψ', j+1, A, hA => by
    have IH := lookup_teleBlock (Ψ := Ψ') (j := j) (by simpa using hA)
    have h := lookup_append_left (Ξ₂ := [B]) IH
    rw [List.reverse_cons,
        show (B::Ψ').length - 1 - (j+1) = Ψ'.length - 1 - j by simp; omega,
        show (B::Ψ').length - (j+1) = Ψ'.length - j by simp]
    exact h

/-- Prefix-closed telescope: entry `j` may only mention the `k + j` binders
below it. -/
def ClosedTele : List VExpr → (k : Nat := 0) → Prop
  | [], _ => True
  | A :: Δ, k => A.ClosedN k ∧ ClosedTele Δ (k+1)

theorem liftTele_eq_of_closed : ∀ {Δ k}, ClosedTele Δ k → liftTele n Δ k = Δ
  | [], _, _ => rfl
  | A :: Δ, k, ⟨h1, h2⟩ => by
    simp [liftTele_cons, h1.liftN_eq (Nat.le_refl _), liftTele_eq_of_closed h2]

/-- A prefix-closed telescope `Ψ` whose binder block sits at the bottom of
the context is filled by the variables that point at it. -/
theorem fills_varSpine_bottom {Ψ Γtop : List VExpr} (hcl : ClosedTele Ψ) :
    FillsTele env U (Γtop ++ Ψ.reverse) Ψ
      ((List.range Ψ.length).map fun k => .bvar (Γtop.length + Ψ.length - 1 - k)) := by
  have main := fills_varSpine (env := env) (U := U) (Δ := Ψ)
    (n := Γtop.length + Ψ.length)
    (Γ := Γtop ++ Ψ.reverse) (by omega) (fun j A hA => by
      have hj : j < Ψ.length := (List.getElem?_eq_some_iff.1 hA).1
      have h1 := lookup_teleBlock hA
      have h2 := h1.weakN (Ctx.LiftN.zero (n := Γtop.length) Γtop rfl)
      rw [liftVar_base] at h2
      rw [show Γtop.length + Ψ.length - 1 - j = Γtop.length + (Ψ.length - 1 - j) by omega,
        show Γtop.length + Ψ.length - j = Ψ.length - j + Γtop.length by omega,
        ← VExpr.liftN_liftN]
      exact h2)
  rwa [liftTele_eq_of_closed hcl] at main

/-! ## Consuming a bottom-block spine ahead of further arguments

For heads like `I params indices`, the parameters are consumed first (as
variables pointing at the bottom of the context) and the indices after. The
residual telescope left by the parameter phase is a pure lift, by iterating
`inst_liftN_bvar'`. -/

/-- `instUnder` with an explicit base cutoff: substitute each argument at the
depth of its binder, all offset by `k`. -/
def instUnderK (B : VExpr) : List VExpr → Nat → VExpr
  | [], _ => B
  | e :: es, k => instUnderK (B.inst e (k + es.length)) es k

@[simp] theorem instUnderK_nil : instUnderK B [] k = B := rfl
@[simp] theorem instUnderK_cons :
    instUnderK B (e :: es) k = instUnderK (B.inst e (k + es.length)) es k := rfl

theorem instUnderK_append : ∀ {es₁ : List VExpr} {B es₂ k},
    instUnderK B (es₁ ++ es₂) k = instUnderK (instUnderK B es₁ (k + es₂.length)) es₂ k
  | [], _, _, _ => rfl
  | e :: es₁, B, es₂, k => by
    simp only [List.cons_append, instUnderK_cons, List.length_append]
    rw [instUnderK_append (es₁ := es₁), show k + (es₁.length + es₂.length)
      = k + es₂.length + es₁.length by omega]

/-- A variable spine, split at its last (deepest) element. -/
theorem spine_snoc {p m : Nat} :
    (List.range (p+1)).map (fun k => VExpr.bvar (m + (p+1) - 1 - k))
      = ((List.range p).map fun k => .bvar ((m+1) + p - 1 - k)) ++ [.bvar m] := by
  rw [List.range_succ, List.map_append]
  congr 1
  · exact List.map_congr_left fun k _ => by congr 1; omega
  · simp

/-- Iterating `inst_liftN_bvar'`: consuming an entire bottom-block variable
spine from a prefix-closed expression is a pure lift. -/
theorem instUnderK_bottomSpine : ∀ {p : Nat} {e : VExpr} {m k : Nat},
    e.ClosedN (k + p) →
    instUnderK e ((List.range p).map fun i => .bvar (m + p - 1 - i)) k = e.liftN m k
  | 0, e, m, k, h => by simpa using (h.liftN_eq (Nat.le_refl _)).symm
  | p+1, e, m, k, h => by
    rw [spine_snoc, instUnderK_append]
    have IH := instUnderK_bottomSpine (p := p) (e := e) (m := m+1) (k := k+1)
      (by rw [Nat.add_right_comm]; exact h)
    simp only [List.length_cons, List.length_nil] at IH ⊢
    rw [IH]
    simp only [instUnderK_cons, instUnderK_nil]
    exact inst_liftN_bvar' e m k

/-- Consuming a block-variable spine cancels one block's worth of a lift:
if `h` was lifted over `m + p` binders starting at depth `k + p`, applying
the `p` variables that point at the block just below (at depths
`m, …, m+p-1` from the cutoff) leaves `h` lifted by `m` at `k`. Unlike
`instUnderK_bottomSpine` this holds for arbitrary `h`. -/
theorem instUnderK_blockSpine : ∀ {p : Nat} {h : VExpr} {m k : Nat},
    instUnderK (h.liftN (m + p) (k + p))
      ((List.range p).map fun i => .bvar (m + p - 1 - i)) k
      = h.liftN m k
  | 0, _, _, _ => rfl
  | p+1, h, m, k => by
    rw [spine_snoc, instUnderK_append]
    have IH := instUnderK_blockSpine (p := p) (h := h) (m := m+1) (k := k+1)
    simp only [List.length_cons, List.length_nil] at IH ⊢
    rw [show m + (p+1) = (m+1) + p by omega, show k + (p+1) = (k+1) + p by omega,
      IH]
    simp only [instUnderK_cons, instUnderK_nil]
    exact inst_liftN_bvar' h m k

theorem instTele_append : ∀ {Δ₁ Δ₂ : List VExpr} {e k},
    instTele e (Δ₁ ++ Δ₂) k = instTele e Δ₁ k ++ instTele e Δ₂ (k + Δ₁.length)
  | [], _, _, _ => by simp
  | A :: Δ₁, Δ₂, e, k => by
    simp only [List.cons_append, instTele_cons, instTele_append (Δ₁ := Δ₁)]
    rw [show k + (A :: Δ₁).length = k + 1 + Δ₁.length by simp; omega]

/-- The telescope left over after `FillsTele` consumes a prefix spine `es`:
entry at position `s` has been instantiated at cutoffs `s + |es| - 1, …, s`. -/
def instTeleUnder (Δ : List VExpr) : List VExpr → List VExpr
  | [] => Δ
  | e :: es => instTeleUnder (instTele e Δ es.length) es

@[simp] theorem instTeleUnder_nil : instTeleUnder Δ [] = Δ := rfl
@[simp] theorem instTeleUnder_cons :
    instTeleUnder Δ (e :: es) = instTeleUnder (instTele e Δ es.length) es := rfl

theorem instTeleUnder_length : ∀ {es Δ}, (instTeleUnder Δ es).length = Δ.length
  | [], _ => rfl
  | _ :: es, _ => by simp [instTeleUnder_length (es := es)]

/-- Splitting a spine across an appended telescope. -/
theorem FillsTele.append : ∀ {Δ₁ es₁ Δ₂ es₂}, FillsTele env U Γ Δ₁ es₁ →
    FillsTele env U Γ (instTeleUnder Δ₂ es₁) es₂ →
    FillsTele env U Γ (Δ₁ ++ Δ₂) (es₁ ++ es₂)
  | [], [], _, _, _, h₂ => h₂
  | A :: Δ₁, e :: es₁, Δ₂, es₂, ⟨he, h₁⟩, h₂ => by
    have hlen : Δ₁.length = es₁.length := by have := h₁.length_eq; simpa using this
    refine ⟨he, ?_⟩
    show FillsTele env U Γ (instTele e (Δ₁ ++ Δ₂)) (es₁ ++ es₂)
    rw [instTele_append, Nat.zero_add, hlen]
    exact FillsTele.append h₁ h₂
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => nomatch h

/-- Lifting twice at the same base composes. -/
theorem liftTele_liftTele : ∀ {Δ : List VExpr} {n₁ n₂ k},
    liftTele n₂ (liftTele n₁ Δ k) k = liftTele (n₁ + n₂) Δ k
  | [], _, _, _ => rfl
  | A :: Δ, n₁, n₂, k => by
    simp only [liftTele_cons, liftTele_liftTele (Δ := Δ)]
    rw [VExpr.liftN'_liftN_hi]

/-- `instTeleUnder` with an explicit base cutoff (the whole telescope block
sits under `k` untouched binders). -/
def instTeleUnderK (Δ : List VExpr) : List VExpr → Nat → List VExpr
  | [], _ => Δ
  | e :: es, k => instTeleUnderK (instTele e Δ (k + es.length)) es k

@[simp] theorem instTeleUnderK_nil : instTeleUnderK Δ [] k = Δ := rfl
@[simp] theorem instTeleUnderK_cons :
    instTeleUnderK Δ (e :: es) k = instTeleUnderK (instTele e Δ (k + es.length)) es k := rfl

theorem instTeleUnder_eq : ∀ {es Δ}, instTeleUnder Δ es = instTeleUnderK Δ es 0
  | [], _ => rfl
  | _ :: es, _ => by
    simp only [instTeleUnder_cons, instTeleUnderK_cons, Nat.zero_add]
    exact instTeleUnder_eq (es := es)

theorem instTeleUnderK_nilΔ : ∀ {es k}, instTeleUnderK [] es k = []
  | [], _ => rfl
  | _ :: es, _ => by
    simp only [instTeleUnderK_cons, instTele_nil]
    exact instTeleUnderK_nilΔ (es := es)

/-- `instTeleUnderK` acts pointwise: `instUnderK` on the head, shifted base
on the tail. -/
theorem instTeleUnderK_consΔ : ∀ {es A Δ k},
    instTeleUnderK (A :: Δ) es k = instUnderK A es k :: instTeleUnderK Δ es (k+1)
  | [], _, _, _ => rfl
  | e :: es, A, Δ, k => by
    simp only [instTeleUnderK_cons, instTele_cons, instUnderK_cons]
    rw [show k + es.length + 1 = k + 1 + es.length by omega]
    exact instTeleUnderK_consΔ (es := es)

/-- Consuming a bottom-block variable spine from a prefix-closed telescope
lifts it: the residual telescope for the remaining arguments. -/
theorem instTeleUnderK_bottomSpine : ∀ {Δ : List VExpr} {p m k : Nat},
    ClosedTele Δ (p + k) →
    instTeleUnderK Δ ((List.range p).map fun i => .bvar (m + p - 1 - i)) k
      = liftTele m Δ k
  | [], _, _, _, _ => instTeleUnderK_nilΔ
  | A :: Δ, p, m, k, ⟨h1, h2⟩ => by
    rw [instTeleUnderK_consΔ, liftTele_cons,
      instUnderK_bottomSpine (by rwa [Nat.add_comm p k] at h1),
      instTeleUnderK_bottomSpine (by rwa [Nat.add_assoc] at h2)]

theorem instTeleUnder_bottomSpine {Δ : List VExpr} {p m : Nat}
    (h : ClosedTele Δ p) :
    instTeleUnder Δ ((List.range p).map fun i => .bvar (m + p - 1 - i))
      = liftTele m Δ := by
  rw [instTeleUnder_eq]
  exact instTeleUnderK_bottomSpine (by simpa using h)

/-- Adding the block's type constants preserves `Ordered`. -/
theorem foldl_addConst_ordered {U : Nat} :
    ∀ {ts : List VInductiveType} {env env' : VEnv},
    VEnv.Ordered env →
    (∀ t ∈ ts, env.IsType U [] t.type) →
    ts.foldlM (fun env t => env.addConst t.name ⟨U, t.type⟩) env = some env' →
    VEnv.Ordered env' ∧ env ≤ env'
  | [], env, _, henv, _, h => by cases h; exact ⟨henv, .rfl⟩
  | t :: ts, env, env', henv, H, h => by
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have hord : VEnv.Ordered env1 :=
      .const henv (show VConstant.WF env ⟨U, t.type⟩ from H t (.head _)) h1
    have hle : env ≤ env1 := VEnv.addConst_le h1
    have ⟨ho, hl⟩ := foldl_addConst_ordered hord
      (fun t' ht' => (H t' (.tail _ ht')).mono hle) h2
    exact ⟨ho, hle.trans hl⟩

/-- Adding the block's constructor constants preserves `Ordered`. -/
theorem foldl_addCtors_ordered {U : Nat} :
    ∀ {ts : List VInductiveType} {env env' : VEnv},
    VEnv.Ordered env →
    (∀ t ∈ ts, ∀ c ∈ t.ctors, env.IsType U [] c.type) →
    ts.foldlM (fun env t =>
      t.ctors.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env) env = some env' →
    VEnv.Ordered env' ∧ env ≤ env' := by
  have inner : ∀ {cs : List VConstVal} {env env' : VEnv},
      VEnv.Ordered env →
      (∀ c ∈ cs, env.IsType U [] c.type) →
      cs.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env = some env' →
      VEnv.Ordered env' ∧ env ≤ env' := by
    intro cs
    induction cs with
    | nil => intro env env' henv _ h; cases h; exact ⟨henv, .rfl⟩
    | cons c cs ih =>
      intro env env' henv H h
      obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      have hord : VEnv.Ordered env1 :=
        .const henv (show VConstant.WF env ⟨U, c.type⟩ from H c (.head _)) h1
      have hle : env ≤ env1 := VEnv.addConst_le h1
      have ⟨ho, hl⟩ := ih hord (fun c' hc' => (H c' (.tail _ hc')).mono hle) h2
      exact ⟨ho, hle.trans hl⟩
  intro ts
  induction ts with
  | nil => intro env env' henv _ h; cases h; exact ⟨henv, .rfl⟩
  | cons t ts ih =>
    intro env env' henv H h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have ⟨ho1, hle1⟩ := inner henv (H t (.head _)) h1
    have ⟨ho, hl⟩ := ih ho1 (fun t' ht' c hc => (H t' (.tail _ ht') c hc).mono hle1) h2
    exact ⟨ho, hle1.trans hl⟩

/-! ## Telescope formation and weakening -/

@[simp] theorem instUnder_sort : ∀ {es : List VExpr} {u},
    instUnder (.sort u) es = .sort u
  | [], _ => rfl
  | _ :: es, _ => instUnder_sort (es := es)

theorem TeleWF.mkForallOF_isType : ∀ {Δ Γ₀ B}, TeleWF env U Γ₀ Δ →
    env.IsType U (Δ.reverse ++ Γ₀) B → env.IsType U Γ₀ (mkForallOF Δ B)
  | [], _, _, _, hB => by simpa using hB
  | A :: Δ, Γ₀, B, ⟨hA, hΔ⟩, hB => by
    rw [mkForallOF_cons]
    refine hA.forallE (TeleWF.mkForallOF_isType hΔ ?_)
    rwa [show Δ.reverse ++ (A :: Γ₀) = (A :: Δ).reverse ++ Γ₀ by simp]

theorem TeleWF.weakN (henv : VEnv.Ordered env) (W : Ctx.LiftN n k Γ Γ') :
    ∀ {Δ}, TeleWF env U Γ Δ → TeleWF env U Γ' (liftTele n Δ k)
  | [], _ => trivial
  | _ :: _, ⟨hA, hΔ⟩ => ⟨hA.weakN henv W, TeleWF.weakN henv W.succ hΔ⟩

/-- Looking up the `m`-th entry of the topmost telescope block. -/
theorem lookup_topBlock {Δ : List VExpr} {Γrest : List VExpr} {m : Nat} {A}
    (h : Δ[m]? = some A) :
    Lookup (Δ.reverse ++ Γrest) (Δ.length - 1 - m) (A.liftN (Δ.length - m)) :=
  lookup_append_left (Ξ₂ := Γrest) (lookup_teleBlock h)

theorem mkForallOF_append {Δ₁ Δ₂ : List VExpr} {B} :
    mkForallOF (Δ₁ ++ Δ₂) B = mkForallOF Δ₁ (mkForallOF Δ₂ B) :=
  List.foldr_append

/-- Lifting again just above an earlier lift's range collapses
(pointwise `liftN'_liftN'` at the edge). -/
theorem liftTele_liftTele_hi : ∀ {Δ : List VExpr} {n₁ n₂ k},
    liftTele n₂ (liftTele n₁ Δ k) (k + n₁) = liftTele (n₁ + n₂) Δ k
  | [], _, _, _ => rfl
  | A :: Δ, n₁, n₂, k => by
    simp only [liftTele_cons]
    rw [show k + n₁ + 1 = (k + 1) + n₁ by omega, liftTele_liftTele_hi (Δ := Δ),
      VExpr.liftN'_liftN' (Nat.le_add_right k n₁) (Nat.le_of_eq (Nat.add_comm k n₁))]

/-- Lifting through a telescope instantiation (pointwise `liftN_instN_hi`). -/
theorem liftTele_instTele : ∀ {Δ : List VExpr} {e n k j},
    liftTele n (instTele e Δ j) (k + j)
      = instTele (e.liftN n k) (liftTele n Δ (k + j + 1)) j
  | [], _, _, _, _ => rfl
  | A :: Δ, e, n, k, j => by
    simp only [instTele_cons, liftTele_cons]
    rw [VExpr.liftN_instN_hi,
      show k + j + 1 = k + (j + 1) by omega,
      liftTele_instTele (Δ := Δ),
      show k + (j + 1) + 1 = k + j + 1 + 1 by omega]

/-- Weakening a filled spine: both the telescope and the arguments lift. -/
theorem FillsTele.weakN (henv : VEnv.Ordered env) (W : Ctx.LiftN n k Γ Γ') :
    ∀ {Δ es}, FillsTele env U Γ Δ es →
    FillsTele env U Γ' (liftTele n Δ k) (es.map (VExpr.liftN n · k))
  | [], [], _ => trivial
  | A :: Δ, e :: es, ⟨he, hes⟩ => by
    refine ⟨he.weakN henv W, ?_⟩
    have IH := FillsTele.weakN henv W hes
    rwa [show (k : Nat) = k + 0 by omega, liftTele_instTele,
      show k + 0 + 1 = k + 1 by omega, show k + 0 = k by omega] at IH
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- `liftTele2` is the composition of two `liftTele`s. -/
theorem liftTele2_eq : ∀ {Δ : List VExpr} {m₁ m₂ k₂ s},
    liftTele2 m₁ m₂ k₂ Δ s = liftTele m₁ (liftTele m₂ Δ (k₂ + s)) s
  | [], _, _, _, _ => rfl
  | A :: Δ, m₁, m₂, k₂, s => by
    simp only [liftTele2, liftTele_cons, lift2]
    rw [liftTele2_eq (Δ := Δ), show k₂ + s + 1 = k₂ + (s + 1) by omega,
      Nat.add_comm s k₂]

/-- Weakening a whole (reversed) telescope block along a context lift. -/
theorem ctxLiftN_teleBlock {n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') : ∀ {Δ : List VExpr},
    Ctx.LiftN n (k + Δ.length) (Δ.reverse ++ Γ) ((liftTele n Δ k).reverse ++ Γ')
  | [] => by simpa using W
  | A :: Δ => by
    have IH := ctxLiftN_teleBlock (W.succ (A := A)) (Δ := Δ)
    rw [show (A :: Δ).reverse ++ Γ = Δ.reverse ++ (A :: Γ) by simp,
      show ((liftTele n (A :: Δ) k).reverse : List VExpr) ++ Γ'
        = (liftTele n Δ (k+1)).reverse ++ (A.liftN n k :: Γ') by simp,
      show k + (A :: Δ).length = (k + 1) + Δ.length by simp; omega]
    exact IH

theorem mkAppList_inst : ∀ {es : List VExpr} {f e k},
    (mkAppList f es).inst e k = mkAppList (f.inst e k) (es.map (VExpr.inst · e k))
  | [], _, _, _ => rfl
  | _ :: es, _, _, _ => by
    simp only [List.map_cons, mkAppList_cons, mkAppList_inst (es := es)]; rfl

theorem instUnder_mkAppList : ∀ {spine : List VExpr} {f es},
    instUnder (mkAppList f es) spine
      = mkAppList (instUnder f spine) (es.map fun e => instUnder e spine)
  | [], _, _ => by simp
  | a :: spine, f, es => by
    simp only [instUnder_cons, mkAppList_inst, instUnder_mkAppList (spine := spine),
      List.map_map]
    rfl

/-! ## Typing the motive -/

/-- The motive for type `j` is well-typed at its binder: in any context that
extends the parameter block by `j` binders. -/
theorem motiveType_isType {envI : VEnv} {Θ : RecCtx} {j : Nat} {t : TypeView}
    {ℓ' : VLevel} {Δj : List VExpr}
    (henvI : VEnv.Ordered envI)
    (ht : Θ.types[j]? = some t)
    (hj : Δj.length = j)
    (hnp : Θ.np = Θ.params.length)
    (helim : Θ.elim.WF Θ.recUvars)
    (hlvls : ∀ l ∈ Θ.lvls, l.WF Θ.recUvars)
    (hclP : ClosedTele Θ.params)
    (hclI : ClosedTele t.indices Θ.np)
    (hidxWF : TeleWF envI Θ.recUvars Θ.params.reverse t.indices)
    (hconst : ∀ Γ, envI.HasType Θ.recUvars Γ (.const t.name Θ.lvls)
      (mkForallOF Θ.params (mkForallOF t.indices (.sort ℓ')))) :
    ∃ M, motiveType Θ j = some M ∧
      envI.IsType Θ.recUvars (Δj.reverse ++ Θ.params.reverse) M := by
  have hM : motiveType Θ j = some (mkForallOF (liftTele j t.indices)
      (.forallE (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (t.indices.length + j + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            .bvar (t.indices.length - 1 - m))))
        (.sort Θ.elim))) := by
    simp [motiveType, ht]
  refine ⟨_, hM, ?_⟩
  have W : Ctx.LiftN j 0 Θ.params.reverse (Δj.reverse ++ Θ.params.reverse) :=
    .zero Δj.reverse (by simp [hj])
  refine TeleWF.mkForallOF_isType (TeleWF.weakN henvI W hidxWF) ?_
  -- the head constant, at its (appended) telescope type
  have hconstT : envI.HasType Θ.recUvars
      ((liftTele j t.indices).reverse ++ (Δj.reverse ++ Θ.params.reverse))
      (.const t.name Θ.lvls)
      (mkForallOF (Θ.params ++ t.indices) (.sort ℓ')) := by
    have h := hconst ((liftTele j t.indices).reverse ++ (Δj.reverse ++ Θ.params.reverse))
    rwa [← mkForallOF_append] at h
  -- phase 1: the parameter spine
  have hfillP : FillsTele envI Θ.recUvars
      ((liftTele j t.indices).reverse ++ (Δj.reverse ++ Θ.params.reverse))
      Θ.params
      ((List.range Θ.np).map fun k =>
        .bvar (t.indices.length + j + Θ.np - 1 - k)) := by
    have h := fills_varSpine_bottom (env := envI) (U := Θ.recUvars)
      (Ψ := Θ.params)
      (Γtop := (liftTele j t.indices).reverse ++ Δj.reverse) hclP
    rw [show ((liftTele j t.indices).reverse ++ Δj.reverse).length
        = t.indices.length + j by simp [hj],
      List.append_assoc, ← hnp] at h
    exact h
  -- phase 2: the index spine, against the residual telescope
  have hfillI : FillsTele envI Θ.recUvars
      ((liftTele j t.indices).reverse ++ (Δj.reverse ++ Θ.params.reverse))
      (instTeleUnder t.indices
        ((List.range Θ.np).map fun k =>
          .bvar (t.indices.length + j + Θ.np - 1 - k)))
      ((List.range t.indices.length).map fun m =>
        .bvar (t.indices.length - 1 - m)) := by
    rw [show instTeleUnder t.indices
        ((List.range Θ.np).map fun k =>
          .bvar (t.indices.length + j + Θ.np - 1 - k))
        = liftTele t.indices.length (liftTele j t.indices) by
      rw [hnp, instTeleUnder_bottomSpine (by rwa [← hnp]),
        liftTele_liftTele, Nat.add_comm]]
    have h := fills_varSpine (env := envI) (U := Θ.recUvars)
      (Δ := liftTele j t.indices) (n := t.indices.length)
      (Nat.le_of_eq liftTele_length) (fun m A hA => by
        have := lookup_topBlock (Γrest := Δj.reverse ++ Θ.params.reverse) hA
        simpa using this)
    rwa [liftTele_length] at h
  -- assemble
  have happ := (hfillP.append hfillI).appList hconstT
  rw [instUnder_sort] at happ
  exact VEnv.IsType.forallE ⟨_, happ⟩ ⟨_, VEnv.HasType.sort helim⟩

/-! ## The interface bundle and the top-level theorem

`RecCtxWF` is the working interface between the `WFCore` hypotheses (about
the raw declaration) and the construction-typing lemmas (about the shifted
`RecCtx` data). Deriving it from `WFCore` — the elim-shift transport — is a
separate step. Every clause is monotone in the environment. -/

structure RecCtxWF (envC : VEnv) (Θ : RecCtx) : Prop where
  np_eq : Θ.np = Θ.params.length
  n_eq : Θ.n = Θ.types.length
  K_eq : Θ.K = Θ.types.foldl (fun k t => k + t.ctors.length) 0
  names_eq : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
    Θ.names[i]? = some t.name
  nidx_eq : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
    Θ.nidx[i]? = some t.indices.length
  elim_wf : Θ.elim.WF Θ.recUvars
  lvls_wf : ∀ l ∈ Θ.lvls, l.WF Θ.recUvars
  params_closed : ClosedTele Θ.params
  params_wf : TeleWF envC Θ.recUvars [] Θ.params
  idx_closed : ∀ t ∈ Θ.types, ClosedTele t.indices Θ.np
  idx_wf : ∀ t ∈ Θ.types, TeleWF envC Θ.recUvars Θ.params.reverse t.indices
  -- Stated as a typing fact rather than a syntactic equality: the kernel
  -- consumes binder annotations (`outParam` etc.) when it builds recursor
  -- binders, so the reconstructed telescope is only *definitionally* equal
  -- to the stored constant type, never syntactically equal.
  type_const : ∀ t ∈ Θ.types, ∃ ℓ' : VLevel, ∀ Γ,
    envC.HasType Θ.recUvars Γ (.const t.name Θ.lvls)
      (mkForallOF Θ.params (mkForallOF t.indices (.sort ℓ')))
  fields_closed : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors, ClosedTele c.fields Θ.np
  fields_wf : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    TeleWF envC Θ.recUvars Θ.params.reverse c.fields
  ctor_const : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
    ∀ c ∈ t.ctors, ∀ Γ,
    envC.HasType Θ.recUvars Γ (.const c.name Θ.lvls)
      (mkForallOF Θ.params (mkForallOF c.fields
        (mkAppList (.const t.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              VExpr.bvar (c.fields.length + Θ.np - 1 - k)) ++ c.rIndices))))
  rIndices_fill : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
    ∀ c ∈ t.ctors,
    FillsTele envC Θ.recUvars (c.fields.reverse ++ Θ.params.reverse)
      (liftTele c.fields.length t.indices) c.rIndices
  -- The decomposed form of each recursive constructor field. `recFields`
  -- reports a field at position `pf` whose type is `∀ xs, I_it params ris`;
  -- these are the facts about that decomposition the induction hypothesis
  -- in `minorType` needs. They are stated rather than derived from
  -- `fields_wf`: recovering them would mean inverting `IsType` through a
  -- `∀`-telescope, and `∀`-injectivity is itself one of the open `sorry`s
  -- in `Theory/Typing/Injectivity.lean`. The `WFCore → RecCtxWF` transport
  -- is the honest place to discharge them, since the C++ checker
  -- establishes exactly these while walking the constructor telescope.
  recField_tele : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      TeleWF envC Θ.recUvars
        ((c.fields.take pf).reverse ++ Θ.params.reverse) xs
  recField_closed : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      ClosedTele xs (Θ.np + pf)
  /-- The index arguments of a recursive field's target fill that type's
  index telescope, in the context of the field's own arguments. -/
  recField_fill : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      ∀ t', Θ.types[it]? = some t' →
      FillsTele envC Θ.recUvars
        (xs.reverse ++ (c.fields.take pf).reverse ++ Θ.params.reverse)
        (liftTele (xs.length + pf) t'.indices) ris
  /-- The syntactic shape of a recursive field: the stored field type *is*
  the `∀`-telescope over the decomposition `recFields` reports, with the
  target type's constant applied to the parameter variables and the
  reported index arguments.

  DIVERGENCE (assumption, not derivable): `recArg?` walks the field with
  `teleAll`, which consumes binder annotations (`optParam` etc.), so this
  clause is *false* for a field whose inner binder domains carry
  annotations — the stored type keeps them while `xs` has them stripped.
  This is the same gap `type_const` documents (there it is merely a
  definitional mismatch): the C++ kernel walks with
  `consumeTypeAnnotations`, and its recursor is then well-typed only up to
  conversion. A `WFCore → RecCtxWF` transport discharges this clause
  exactly for declarations whose recursive-field binder domains are
  annotation-free; covering annotated ones requires conversion-aware
  typing of the construction (the `Positive.defeq`-style closure). -/
  recField_shape : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      ∀ nm, Θ.names[it]? = some nm →
      c.fields[pf]? = some (mkForallOF xs (mkAppList (.const nm Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (xs.length + pf + Θ.np - 1 - k)) ++ ris)))
  names_len : Θ.names.length = Θ.types.length

/-- The recursor fold: preserves `Ordered` and records the added recursor
constants. -/
theorem foldl_addRecs_ordered {Θ : RecCtx} {envC : VEnv} :
    ∀ {ts : List (TypeView × Nat)} {env env' : VEnv},
    VEnv.Ordered env → envC ≤ env →
    (∀ p ∈ ts, ∃ T, recType Θ p.2 = some T ∧ envC.IsType Θ.recUvars [] T) →
    ts.foldlM (fun env (t, i) => do
      let ty ← recType Θ i
      env.addConst (Lean.mkRecName t.name) ⟨Θ.recUvars, ty⟩) env = some env' →
    VEnv.Ordered env' ∧ env ≤ env' ∧
    ∀ p ∈ ts, ∃ T, recType Θ p.2 = some T ∧
      env'.constants (Lean.mkRecName p.1.name) = some ⟨Θ.recUvars, T⟩
  | [], env, _, henv, hle, _, h => by
    cases h; exact ⟨henv, .rfl, nofun⟩
  | (t, i) :: ts, env, env', henv, hle, hty, h => by
    obtain ⟨T, hT, hTy⟩ := hty _ (.head _)
    have hT' : recType Θ i = some T := hT
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ty, hty2, h1'⟩ := Option.bind_eq_some_iff.1 h1
    rw [hT'] at hty2
    cases hty2
    have hord : VEnv.Ordered env1 :=
      .const henv (show VConstant.WF env ⟨Θ.recUvars, T⟩ from hTy.mono hle) h1'
    have hle1 : env ≤ env1 := VEnv.addConst_le h1'
    have hc1 : env1.constants (Lean.mkRecName t.name) = some ⟨Θ.recUvars, T⟩ :=
      VEnv.addConst_self h1'
    have ⟨ho, hl, hcs⟩ := foldl_addRecs_ordered hord (hle.trans hle1)
      (fun p hp => hty p (.tail _ hp)) h2
    refine ⟨ho, hle1.trans hl, ?_⟩
    intro p hp
    cases hp with
    | head => exact ⟨T, hT, hl.constants hc1⟩
    | tail _ hp => exact hcs _ hp

/-- The defeq fold: adding well-formed defeqs preserves `Ordered`. -/
theorem foldl_addDefEqs_ordered {envR : VEnv} :
    ∀ {dfs : List VDefEq} {env : VEnv},
    VEnv.Ordered env → envR ≤ env →
    (∀ df ∈ dfs, VDefEq.WF envR df) →
    VEnv.Ordered (dfs.foldl VEnv.addDefEq env)
  | [], _, henv, _, _ => henv
  | df :: dfs, env, henv, hle, H => by
    show VEnv.Ordered (dfs.foldl VEnv.addDefEq (env.addDefEq df))
    have hdf := H df (.head _)
    exact foldl_addDefEqs_ordered
      (.defeq henv ⟨hdf.1.mono hle, hdf.2.mono hle⟩)
      (hle.trans VEnv.addDefEq_le) (fun df' h => H df' (.tail _ h))

/-- Elements of `zipIdx` are indexed lookups. -/
theorem mem_zipIdx_getElem? {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) : l[i]? = some a := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_zipIdx] at hj
  obtain ⟨b, hb, hba⟩ := Option.map_eq_some_iff.1 hj
  obtain ⟨rfl, rfl⟩ : b = a ∧ j = i := by
    cases hba; exact ⟨rfl, by omega⟩
  simpa using hb

theorem getElem?_mem_zipIdx {l : List α} {a : α} {i : Nat}
    (h : l[i]? = some a) : (a, i) ∈ l.zipIdx := by
  refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
  rw [List.getElem?_zipIdx, h]; simp

/-! ## The motive telescope

Assembling the individual motives into the telescope `recType` binds. The
induction adds one motive at a time, extending the context at the *outer*
end: motive `j` is checked under the `j` motives already bound, which as a
telescope prefix is `Δ ++ [M]` (reversing to `M :: Δ.reverse`). -/

/-- Bundled form of `motiveType_isType`, drawing its side conditions from
`RecCtxWF`. -/
theorem motiveType_isType' {envC : VEnv} {Θ : RecCtx} {j : Nat} {t : TypeView}
    {Δj : List VExpr} (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (ht : Θ.types[j]? = some t) (hj : Δj.length = j) :
    ∃ M, motiveType Θ j = some M ∧
      envC.IsType Θ.recUvars (Δj.reverse ++ Θ.params.reverse) M := by
  have hmem : t ∈ Θ.types := by
    have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
    exact he ▸ List.getElem_mem hlt
  obtain ⟨ℓ', hconst⟩ := h.type_const t hmem
  exact motiveType_isType henv ht hj h.np_eq h.elim_wf h.lvls_wf h.params_closed
    (h.idx_closed t hmem) (h.idx_wf t hmem) hconst

/-- The motive telescope is well-formed: `mapM` over `[s, s+1, ...]`
succeeds, and the resulting telescope is well-formed over any context that
already binds `s` motives. -/
theorem motiveTele_wf {envC : VEnv} {Θ : RecCtx}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) :
    ∀ (m s : Nat), s + m = Θ.types.length →
    ∃ Ms, (List.range' s m).mapM (motiveType Θ) = some Ms ∧
      ∀ (Δ : List VExpr), Δ.length = s →
        TeleWF envC Θ.recUvars (Δ.reverse ++ Θ.params.reverse) Ms
  | 0, _, _ => ⟨[], rfl, fun _ _ => trivial⟩
  | m+1, s, hs => by
    have hlt : s < Θ.types.length := by omega
    obtain ⟨t, ht⟩ : ∃ t, Θ.types[s]? = some t :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    -- the motive's value does not depend on the ambient context, so it can
    -- be obtained at a dummy one of the right length
    obtain ⟨M, hM, -⟩ :=
      motiveType_isType' (Δj := List.replicate s default) henv h ht (by simp)
    obtain ⟨Ms, hMs, hMsWF⟩ := motiveTele_wf henv h m (s+1) (by omega)
    refine ⟨M :: Ms, ?_, fun Δ hΔ => ⟨?_, ?_⟩⟩
    · show (s :: List.range' (s+1) m).mapM (motiveType Θ) = _
      simp [List.mapM_cons, hM, hMs]
    · obtain ⟨M', hM', hty⟩ := motiveType_isType' (Δj := Δ) henv h ht hΔ
      rw [hM] at hM'
      cases hM'
      exact hty
    · have := hMsWF (Δ ++ [M]) (by simp [hΔ])
      simpa using this

/-! ## Telescopes of the recursor, weakened into place

Both the constructor fields (inside a minor premise) and a type's indices
(inside the recursor) are declared over the parameter context and used under
`d` further binders — the motives and preceding minors for the former, the
motives and all minors for the latter. -/

/-- A constructor's field telescope, weakened under `d` binders above the
parameters. -/
theorem minorFields_wf {envC : VEnv} {Θ : RecCtx} {t : TypeView} {c : CtorView}
    {Γtop : List VExpr} {d : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors) (hd : Γtop.length = d) :
    TeleWF envC Θ.recUvars (Γtop ++ Θ.params.reverse) (liftTele d c.fields) :=
  TeleWF.weakN henv (.zero Γtop hd) (h.fields_wf t htm c hcm)

/-- A type's index telescope, weakened under `d` binders above the
parameters. -/
theorem indices_wf_weak {envC : VEnv} {Θ : RecCtx} {t : TypeView}
    {Γtop : List VExpr} {d : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hd : Γtop.length = d) :
    TeleWF envC Θ.recUvars (Γtop ++ Θ.params.reverse) (liftTele d t.indices) :=
  TeleWF.weakN henv (.zero Γtop hd) (h.idx_wf t htm)

/-! ## The minor premise

`minorType` is `∀ (fields) (IHs), motive_i (rIndices) (ctor params fields)`,
so it is a type as soon as its three parts are. The fields part is
`minorFields_wf`; the induction hypotheses and the target are proved in the following lemmas. -/

/-- A minor premise is a type once its fields telescope, its induction
hypotheses and its target are. -/
theorem minorType_isType_of_parts {envC : VEnv} {Θ : RecCtx} {i q : Nat}
    {c : CtorView} {Γq : List VExpr}
    (hfields : TeleWF envC Θ.recUvars Γq (liftTele (q + Θ.n) c.fields))
    (hihs : TeleWF envC Θ.recUvars
      ((liftTele (q + Θ.n) c.fields).reverse ++ Γq) (minorIHs Θ q c))
    (hconcl : envC.IsType Θ.recUvars
      ((minorIHs Θ q c).reverse ++ ((liftTele (q + Θ.n) c.fields).reverse ++ Γq))
      (minorConcl Θ i q c)) :
    envC.IsType Θ.recUvars Γq (minorType Θ i q c) :=
  hfields.mkForallOF_isType (hihs.mkForallOF_isType hconcl)

/-- The minor premise's fields telescope, in the context `recType` uses:
`q` preceding minors and `Θ.n` motives above the parameters. -/
theorem minorFields_wf' {envC : VEnv} {Θ : RecCtx} {t : TypeView} {c : CtorView}
    {Ms Ns : List VExpr} {q : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hM : Ms.length = Θ.n) (hN : Ns.length = q) :
    TeleWF envC Θ.recUvars ((Ns ++ Ms) ++ Θ.params.reverse)
      (liftTele (q + Θ.n) c.fields) :=
  minorFields_wf henv h htm hcm (by simp [hM, hN])

/-! ## Variable spines against a block at depth

The fields of a minor premise (and the indices of the recursor) are bound
below further binders — the induction hypotheses, or nothing yet — so the
spine that refills them starts at a positive depth `d`. No closedness is
needed: the expected telescope carries the full lift, and the depth splits
off of it. -/

/-- Pointwise `instUnderK_blockSpine` for a telescope. -/
theorem instTeleUnderK_blockSpine : ∀ {Δ : List VExpr} {p m k : Nat},
    instTeleUnderK (liftTele (m + p) Δ (k + p))
      ((List.range p).map fun i => .bvar (m + p - 1 - i)) k
      = liftTele m Δ k
  | [], _, _, _ => instTeleUnderK_nilΔ
  | A :: Δ, p, m, k => by
    rw [liftTele_cons, liftTele_cons, instTeleUnderK_consΔ,
      instUnderK_blockSpine,
      show k + p + 1 = (k + 1) + p by omega,
      instTeleUnderK_blockSpine]

/-- Looking up the `j`-th entry of a telescope block sitting at depth
`Γtop.length` in the context. -/
theorem lookup_midBlock {Δ Γtop Γrest : List VExpr} {j : Nat} {A}
    (h : Δ[j]? = some A) :
    Lookup (Γtop ++ (Δ.reverse ++ Γrest))
      (Γtop.length + (Δ.length - 1 - j))
      ((A.liftN (Δ.length - j)).liftN Γtop.length 0) := by
  have h1 := lookup_topBlock (Γrest := Γrest) h
  have h2 := h1.weakN (Ctx.LiftN.zero (n := Γtop.length) Γtop rfl)
  rwa [liftVar_base] at h2

/-- The variables pointing at a binder block at depth `d` fill the
(fully lifted) telescope the block was declared from. -/
theorem fills_varSpine_mid {Δ Γtop Γrest : List VExpr} :
    FillsTele env U (Γtop ++ (Δ.reverse ++ Γrest))
      (liftTele (Γtop.length + Δ.length) Δ)
      ((List.range Δ.length).map fun k =>
        .bvar (Γtop.length + Δ.length - 1 - k)) := by
  refine fills_varSpine (by omega) fun j A hA => ?_
  have := lookup_midBlock (Γtop := Γtop) (Γrest := Γrest) hA
  rw [VExpr.liftN_liftN,
    show Δ.length - j + Γtop.length = Γtop.length + Δ.length - j by
      have := (List.getElem?_eq_some_iff.1 hA).1; omega,
    show Γtop.length + (Δ.length - 1 - j) = Γtop.length + Δ.length - 1 - j by
      have := (List.getElem?_eq_some_iff.1 hA).1; omega] at this
  exact this

/-! ## Closedness plumbing

The `instUnder` evaluation below needs the constructors' index arguments
to be closed under their declaring context; that follows from their
`FillsTele` clauses, because well-typed expressions are closed. -/

theorem ClosedTele.take : ∀ {Δ : List VExpr} {k m : Nat},
    ClosedTele Δ k → ClosedTele (Δ.take m) k
  | [], k, m, _ => by cases m <;> trivial
  | _ :: _, _, 0, _ => trivial
  | A :: Δ, k, m+1, ⟨h1, h2⟩ => ⟨h1, ClosedTele.take h2⟩

theorem closedTele_ctxClosed : ∀ {Ψ Γ₀ : List VExpr},
    CtxClosed Γ₀ → ClosedTele Ψ Γ₀.length → CtxClosed (Ψ.reverse ++ Γ₀)
  | [], _, h, _ => h
  | A :: Ψ, Γ₀, h, ⟨h1, h2⟩ => by
    rw [show (A :: Ψ).reverse ++ Γ₀ = Ψ.reverse ++ (A :: Γ₀) by simp]
    exact closedTele_ctxClosed (Γ₀ := A :: Γ₀) ⟨h, h1⟩ (by simpa using h2)

theorem FillsTele.closedN (henv : VEnv.Ordered env) (hΓ : CtxClosed Γ) :
    ∀ {Δ es}, FillsTele env U Γ Δ es → ∀ e ∈ es, e.ClosedN Γ.length
  | _ :: _, _ :: _, ⟨he, hes⟩, e, hmem => by
    cases hmem with
    | head => exact VExpr.WF.closedN henv ⟨_, he⟩ hΓ
    | tail _ hmem => exact FillsTele.closedN henv hΓ hes e hmem
  | [], [], _, _, hmem => by cases hmem
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => nomatch h

/-! ## Inverting `recFields` -/

theorem validIndApp?_it_lt {names : List Name} {nidx : List Nat}
    {lvls : List VLevel} {np L : Nat} {e : VExpr} {i : Nat} {is : List VExpr}
    (h : validIndApp? names nidx lvls np L e = some (i, is)) :
    i < names.length := by
  unfold validIndApp? at h
  rcases hga : getAppList e with ⟨f, args⟩
  rw [hga] at h
  cases f with
  | const c ls =>
    obtain ⟨i', hidx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ni, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    injection h with h'
    injection h' with h1 h2
    subst h1
    unfold List.idxOf? at hidx
    exact (List.findIdx?_eq_some_iff_findIdx_eq.1 hidx).1
  | bvar v => exact absurd h (by simp)
  | sort u => exact absurd h (by simp)
  | app f a => exact absurd h (by simp)
  | lam A b => exact absurd h (by simp)
  | forallE A b => exact absurd h (by simp)

/-- A `recFields` entry's target index is a valid position in `names`. -/
theorem recFields_it_lt {Θ : RecCtx} {c : CtorView} {pf : Nat}
    {xs : List VExpr} {it : Nat} {ris : List VExpr}
    (h : (pf, xs, it, ris) ∈ recFields Θ c) : it < Θ.names.length := by
  obtain ⟨⟨F, pf'⟩, hmem, heq⟩ := List.mem_filterMap.1 h
  obtain ⟨⟨xs', it', ris'⟩, hrec, hpe⟩ := Option.map_eq_some_iff.1 heq
  cases hpe
  unfold recArg? at hrec
  obtain ⟨⟨it'', ris''⟩, hva, hre⟩ := Option.bind_eq_some_iff.1 hrec
  cases hre
  exact validIndApp?_it_lt hva

/-! ## `instUnderK` computation rules

`FillsTele.appList` delivers types of the form `instUnder B es`; these
lemmas evaluate them: `instUnderK` distributes over the expression
constructors, substituting a variable spine reproduces the (lifted)
arguments, and substituting under a lift cancels it. -/

theorem instUnder_eq_instUnderK : ∀ {es : List VExpr} {B},
    instUnder B es = instUnderK B es 0
  | [], _ => rfl
  | _ :: es, _ => by
    simp only [instUnder_cons, instUnderK_cons, Nat.zero_add]
    exact instUnder_eq_instUnderK (es := es)

theorem instUnderK_sort : ∀ {es : List VExpr} {u k},
    instUnderK (.sort u) es k = .sort u
  | [], _, _ => rfl
  | _ :: es, _, _ => instUnderK_sort (es := es)

theorem instUnderK_const : ∀ {es : List VExpr} {c ls k},
    instUnderK (.const c ls) es k = .const c ls
  | [], _, _, _ => rfl
  | _ :: es, _, _, _ => instUnderK_const (es := es)

theorem instUnderK_forallE : ∀ {es : List VExpr} {A B k},
    instUnderK (.forallE A B) es k
      = .forallE (instUnderK A es k) (instUnderK B es (k+1))
  | [], _, _, _ => rfl
  | e :: es, A, B, k => by
    show instUnderK (.forallE (A.inst e (k + es.length))
      (B.inst e (k + es.length + 1))) es k = _
    rw [instUnderK_forallE (es := es),
      show k + es.length + 1 = k + 1 + es.length by omega]
    simp only [instUnderK_cons]

theorem instUnderK_mkAppList : ∀ {es args : List VExpr} {f k},
    instUnderK (mkAppList f args) es k
      = mkAppList (instUnderK f es k) (args.map (instUnderK · es k))
  | [], _, _, _ => by simp
  | e :: es, args, f, k => by
    simp only [instUnderK_cons, mkAppList_inst, instUnderK_mkAppList (es := es),
      List.map_map]
    rfl

/-- Instantiating anywhere inside a lift's range consumes one lift
(generalizes `inst_liftN'` and `inst_liftN_lo'` to a mid-range cutoff). -/
theorem inst_liftN_mid {j n : Nat} (e a : VExpr) (k : Nat) (h : j ≤ n) :
    (VExpr.liftN (n+1) e k).inst a (k+j) = e.liftN n k := by
  have h1 := VExpr.liftN'_liftN' (e := e) (n1 := j) (n2 := n-j+1) (k1 := k)
    (k2 := k+j) (Nat.le_add_right k j) (Nat.le_of_eq (Nat.add_comm k j))
  have h2 := VExpr.liftN'_liftN' (e := e) (n1 := j) (n2 := n-j) (k1 := k)
    (k2 := k+j) (Nat.le_add_right k j) (Nat.le_of_eq (Nat.add_comm k j))
  rw [show n+1 = j+(n-j+1) by omega, ← h1, VExpr.inst_liftN', h2,
    show j+(n-j) = n by omega]

theorem inst_bvar_lt {v k : Nat} (h : v < k) (a : VExpr) :
    (VExpr.bvar v).inst a k = .bvar v := by
  simp only [VExpr.inst, instVar]
  rw [ite_eq_left h]

theorem inst_bvar_gt {v k : Nat} (h : k < v) (a : VExpr) :
    (VExpr.bvar v).inst a k = .bvar (v-1) := by
  simp only [VExpr.inst, instVar]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem inst_bvar_self {k : Nat} (a : VExpr) :
    (VExpr.bvar k).inst a k = a.liftN k := by
  simp [VExpr.inst, instVar]

/-- Substituting a whole spine under a lift that skips all of it cancels
the spine's worth of the lift, for arbitrary arguments. -/
theorem instUnderK_liftN0_cancel : ∀ {es : List VExpr} {x : VExpr} {k : Nat},
    instUnderK (x.liftN (k + es.length)) es k = x.liftN k
  | [], _, _ => by simp
  | e :: es, x, k => by
    simp only [instUnderK_cons, List.length_cons]
    have h := inst_liftN_mid (j := k + es.length) (n := k + es.length) x e 0
      (Nat.le_refl _)
    rw [Nat.zero_add] at h
    rw [show k + (es.length + 1) = (k + es.length) + 1 by omega, h]
    exact instUnderK_liftN0_cancel (es := es)

/-- Substituting a spine into the variable that points at its `m`-th binder
yields the `m`-th argument (lifted over the `k` untouched binders). -/
theorem instUnderK_spine_bvar : ∀ {es : List VExpr} {m k : Nat} {A},
    es[m]? = some A →
    instUnderK (.bvar (k + (es.length - 1 - m))) es k = A.liftN k
  | e :: es, 0, k, A, hA => by
    cases (by simpa using hA : e = A)
    simp only [instUnderK_cons, List.length_cons, Nat.add_sub_cancel,
      Nat.sub_zero]
    rw [inst_bvar_self, instUnderK_liftN0_cancel]
  | e :: es, m+1, k, A, hA => by
    have hm : m < es.length := (List.getElem?_eq_some_iff.1 (by simpa using hA)).1
    simp only [instUnderK_cons, List.length_cons]
    rw [show es.length + 1 - 1 - (m+1) = es.length - 1 - m by omega,
      inst_bvar_lt (by omega)]
    exact instUnderK_spine_bvar (by simpa using hA)

theorem instUnderK_bvar_ge : ∀ {es : List VExpr} {v k : Nat},
    k + es.length ≤ v →
    instUnderK (.bvar v) es k = .bvar (v - es.length)
  | [], v, k, _ => by simp
  | e :: es, v, k, h => by
    simp only [List.length_cons] at h
    simp only [instUnderK_cons, List.length_cons]
    rw [inst_bvar_gt (by omega), instUnderK_bvar_ge (by omega)]
    congr 1; omega

/-- Substituting the full variable spine into each of the spine's own
argument positions reproduces the spine's arguments. -/
theorem instUnder_spineArgs {es : List VExpr} :
    (List.range es.length).map (fun m => instUnder (.bvar (es.length - 1 - m)) es)
      = es := by
  refine List.ext_getElem? fun m => ?_
  rcases Nat.lt_or_ge m es.length with h | h
  · rw [List.getElem?_map, List.getElem?_range h]
    obtain ⟨A, hA⟩ : ∃ A, es[m]? = some A := ⟨_, List.getElem?_eq_getElem h⟩
    have h0 := instUnderK_spine_bvar (k := 0) hA
    rw [Nat.zero_add, VExpr.liftN_zero] at h0
    rw [hA, Option.map_some, instUnder_eq_instUnderK, h0]
  · rw [List.getElem?_map, List.getElem?_eq_none (by simpa using h),
      List.getElem?_eq_none h]
    rfl

/-- Lifting a variable spine that sits entirely above the cutoff. -/
theorem liftN_varSpine {p c n cut : Nat} (h : cut + p ≤ c) :
    ((List.range p).map fun i => VExpr.bvar (c - 1 - i)).map (VExpr.liftN n · cut)
      = (List.range p).map fun i => VExpr.bvar (n + c - 1 - i) := by
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hip : i < p := List.mem_range.1 hi
  show VExpr.liftN n (.bvar (c-1-i)) cut = _
  simp only [VExpr.liftN]
  rw [liftVar_le (by omega)]
  congr 1; omega

/-! ## More telescope-lift algebra -/

/-- Composition of telescope lifts when the outer cutoff lies anywhere
inside the inner lift's range (pointwise `liftN'_liftN'`); generalizes both
`liftTele_liftTele` (`j = 0`) and `liftTele_liftTele_hi` (`j = n₁`). -/
theorem liftTele_liftTele_mid : ∀ {Δ : List VExpr} {n₁ n₂ k j}, j ≤ n₁ →
    liftTele n₂ (liftTele n₁ Δ k) (k + j) = liftTele (n₁ + n₂) Δ k
  | [], _, _, _, _, _ => rfl
  | A :: Δ, n₁, n₂, k, j, hj => by
    simp only [liftTele_cons]
    rw [show k + j + 1 = (k+1) + j by omega, liftTele_liftTele_mid hj,
      VExpr.liftN'_liftN' (Nat.le_add_right k j) (by omega)]

theorem getElem?_liftTele {m : Nat} : ∀ {Δ : List VExpr} {k j : Nat},
    (liftTele m Δ k)[j]? = Δ[j]?.map fun A => A.liftN m (k + j) := by
  intro Δ
  induction Δ with
  | nil => intro k j; simp
  | cons A Δ ih =>
    intro k j
    cases j with
    | zero => simp
    | succ j =>
      simp only [liftTele_cons, List.getElem?_cons_succ, ih,
        show ∀ j', k + 1 + j' = k + (j'+1) from fun _ => by omega]

@[simp] theorem liftTele2_length {Δ : List VExpr} {m₁ m₂ k₂ s} :
    (liftTele2 m₁ m₂ k₂ Δ s).length = Δ.length := by
  simp [liftTele2_eq]

/-! ## Variable spines at a depth other than the lift amount

`fills_varSpine` requires the spine depth to equal the telescope's lift.
In the minor premise the constructor-field variables sit below the
induction hypotheses while the head constant's telescope is lifted over
both, so the two numbers differ; the residual telescope tracked by the
induction is a *two-stage* lift. -/

/-- The spine `bvar (b-1), …, bvar (b-|Δ|)` fills `liftTele b (liftTele a Δ t)`
provided each variable looks up the corresponding doubly-lifted entry.
Subsumes `fills_varSpine` (`a = 0`, `t = 0`). -/
theorem fills_varSpine2 : ∀ {Δ : List VExpr} {a b t : Nat} {Γ},
    Δ.length ≤ b →
    (∀ j A, Δ[j]? = some A → Lookup Γ (b-1-j) ((A.liftN a (t+j)).liftN (b-j))) →
    FillsTele env U Γ (liftTele b (liftTele a Δ t))
      ((List.range Δ.length).map fun k => .bvar (b-1-k))
  | [], _, _, _, _, _, _ => trivial
  | A :: Δ, a, b, t, Γ, hb, hlk => by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 :=
      ⟨b - 1, by have h := hb; simp at h; omega⟩
    have hhead : env.HasType U Γ (.bvar b) ((A.liftN a t).liftN (b+1)) := by
      have := hlk 0 A rfl
      exact .bvar (by simpa using this)
    rw [List.length_cons, spine_succ]
    refine ⟨hhead, ?_⟩
    show FillsTele env U Γ
      (instTele (.bvar b) (liftTele (b+1) (liftTele a Δ (t+1)) 1)) _
    rw [show (1 : Nat) = 0 + 1 from rfl, instTele_liftTele]
    refine fills_varSpine2 (by have h := hb; simp at h; omega)
      (fun j A hA => ?_)
    have := hlk (j+1) A (by simpa using hA)
    rwa [show b + 1 - 1 - (j+1) = b - 1 - j by omega,
      show b + 1 - (j+1) = b - j by omega,
      show t + (j+1) = (t+1) + j by omega] at this

/-- Build `TeleWF` entrywise: each entry must be a type under an arbitrary
context extension of the right length. (The recursor telescopes only use
the *length* of the preceding binders, so this is how they are all
checked; same pattern as `motiveTele_wf`.) -/
theorem TeleWF.of_isType_at : ∀ {Δ : List VExpr} {Γ₀},
    (∀ j A, Δ[j]? = some A → ∀ Γtop : List VExpr, Γtop.length = j →
      env.IsType U (Γtop ++ Γ₀) A) →
    TeleWF env U Γ₀ Δ
  | [], _, _ => trivial
  | A :: Δ, Γ₀, H => by
    refine ⟨by simpa using H 0 A rfl [] rfl, ?_⟩
    refine TeleWF.of_isType_at fun j B hB Γtop hlen => ?_
    have := H (j+1) B (by simpa using hB) (Γtop ++ [A]) (by simp [hlen])
    simpa using this

/-! ## Applying a motive variable

The recursor construction applies a bound motive three times: in the
induction hypotheses, in the minor premise's conclusion, and in the
recursor's final target. Each time the head is `bvar (D + (n-1-j))` for
`D` binders above the motive block, applied to a spine filling the
`(D+n)`-lifted index telescope and then to a major argument. -/

theorem mapM_getElem? {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ {j : Nat} {a}, l[j]? = some a →
    ∃ b, l'[j]? = some b ∧ f a = some b := by
  intro l
  induction l with
  | nil => intro l' _ j a ha; simp at ha
  | cons x xs ih =>
    intro l' h j a ha
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.1 h
    injection h with h
    subst h
    cases j with
    | zero => cases (by simpa using ha : x = a); exact ⟨b, rfl, hb⟩
    | succ j => exact ih hbs (by simpa using ha)

theorem mapM_length {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → l'.length = l.length := by
  intro l
  induction l with
  | nil => intro l' h; cases h; rfl
  | cons x xs ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.1 h
    injection h with h
    subst h
    simp [ih hbs]

/-- Uniform tool for the index arithmetic inside variable spines. -/
theorem varSpine_congr {p a b : Nat} (h : a = b) :
    ((List.range p).map fun i => VExpr.bvar (a - 1 - i))
      = (List.range p).map fun i => VExpr.bvar (b - 1 - i) := by rw [h]

theorem liftN_varSpine_lo {p c n cut : Nat} (h1 : p ≤ c) (h2 : c ≤ cut) :
    ((List.range p).map fun i => VExpr.bvar (c - 1 - i)).map (VExpr.liftN n · cut)
      = (List.range p).map fun i => VExpr.bvar (c - 1 - i) := by
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hip : i < p := List.mem_range.1 hi
  show VExpr.liftN n (.bvar (c-1-i)) cut = _
  simp only [VExpr.liftN]
  rw [liftVar_lt (by omega)]

/-- The lifted form of a motive's type: lifting `motiveType Θ j` by `m`
re-anchors its index telescope and parameter spine `m` deeper while its
own binders are untouched. -/
theorem motiveType_liftN {Θ : RecCtx} {j : Nat} {t' : TypeView} {Mj : VExpr}
    (ht : Θ.types[j]? = some t') (hMjTy : motiveType Θ j = some Mj) (m : Nat) :
    Mj.liftN m = mkForallOF (liftTele (j + m) t'.indices)
      (.forallE (mkAppList (.const t'.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (t'.indices.length + (j + m) + Θ.np - 1 - k)) ++
         ((List.range t'.indices.length).map fun i =>
            .bvar (t'.indices.length - 1 - i))))
        (.sort Θ.elim)) := by
  have h0 := hMjTy
  simp only [motiveType, ht] at h0
  obtain ⟨t'', ht'', hM⟩ := Option.bind_eq_some_iff.1 h0
  injection ht'' with ht''
  subst ht''
  injection hM with hM
  subst hM
  rw [mkForallOF_liftN, liftTele_liftTele]
  show _ = mkForallOF _ (.forallE _ _)
  congr 1
  rw [show (0 : Nat) + (liftTele j t'.indices).length = t'.indices.length by
    simp]
  show VExpr.forallE _ _ = _
  congr 1
  rw [mkAppList_liftN, List.map_append]
  show mkAppList (.const t'.name Θ.lvls) _ = _
  congr 1
  rw [liftN_varSpine (by omega), liftN_varSpine_lo (Nat.le_refl _) (Nat.le_refl _)]
  congr 1
  exact varSpine_congr (by omega)

/-- Applying a motive variable: `bvar (D + (n-1-j))` at `D` binders above
the motive block, applied to an index spine and a major argument, lands in
`Sort elim`. The context below the motive block is arbitrary — the lifted
motive type carries everything the application needs. -/
theorem motiveApp_hasType {Θ : RecCtx} {j D : Nat} {t' : TypeView} {Mj : VExpr}
    {Ms ΓD Γrest : List VExpr} {is : List VExpr} {a : VExpr}
    (ht : Θ.types[j]? = some t')
    (hjn : j < Θ.n)
    (hMs : Ms.length = Θ.n)
    (hMj : Ms[j]? = some Mj) (hMjTy : motiveType Θ j = some Mj)
    (hD : ΓD.length = D)
    (hfill : FillsTele env U (ΓD ++ (Ms.reverse ++ Γrest))
      (liftTele (D + Θ.n) t'.indices) is)
    (ha : env.HasType U (ΓD ++ (Ms.reverse ++ Γrest)) a
      (mkAppList (.const t'.name Θ.lvls)
        (((List.range Θ.np).map fun k => .bvar (D + Θ.n + Θ.np - 1 - k)) ++ is))) :
    env.HasType U (ΓD ++ (Ms.reverse ++ Γrest))
      (.app (mkAppList (.bvar (D + (Θ.n - 1 - j))) is) a) (.sort Θ.elim) := by
  have hisLen : is.length = t'.indices.length := by
    have := hfill.length_eq
    simpa using this.symm
  -- the head variable and its (computed) lifted type
  have hlk := lookup_midBlock (Γtop := ΓD) (Γrest := Γrest) hMj
  rw [hD, VExpr.liftN_liftN, hMs] at hlk
  have hhead := VEnv.IsDefEq.bvar (env := env) (uvars := U) hlk
  rw [motiveType_liftN ht hMjTy, show j + (Θ.n - j + D) = D + Θ.n by omega] at hhead
  -- apply the index spine
  have happ := hfill.appList hhead
  -- evaluate the resulting type
  rw [instUnder_eq_instUnderK, instUnderK_forallE, instUnderK_sort,
    instUnderK_mkAppList, instUnderK_const, List.map_append] at happ
  have hp : (((List.range Θ.np).map fun k =>
      VExpr.bvar (t'.indices.length + (D + Θ.n) + Θ.np - 1 - k)).map
        (instUnderK · is 0))
      = (List.range Θ.np).map fun k => .bvar (D + Θ.n + Θ.np - 1 - k) := by
    rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hkp : k < Θ.np := List.mem_range.1 hk
    show instUnderK (.bvar (t'.indices.length + (D + Θ.n) + Θ.np - 1 - k)) is 0 = _
    rw [instUnderK_bvar_ge (by omega), hisLen]
    congr 1; omega
  have hi : (((List.range t'.indices.length).map fun i =>
      VExpr.bvar (t'.indices.length - 1 - i)).map (instUnderK · is 0)) = is := by
    rw [← hisLen, List.map_map]
    refine Eq.trans (List.map_congr_left fun m hm => ?_)
      (instUnder_spineArgs (es := is))
    exact (instUnder_eq_instUnderK (es := is)).symm
  rw [hp, hi] at happ
  exact happ.app ha

/-! ## The constructor application

Both the minor premise's conclusion and the iota rules apply a
constructor to the parameter and field variables. The type evaluation is
factored out as a pure computation (`instUnder_ctorTarget`), and the
typing itself refills the constructor's telescope with the two spines. -/

/-- Applying an expression lifted over its own binder block to that
block's variable spine cancels the block's worth of the lift. -/
theorem instUnder_selfSpine {e : VExpr} {nx Y : Nat} :
    instUnder (e.liftN (nx + Y) nx) ((List.range nx).map fun s => .bvar (nx - 1 - s))
      = e.liftN Y nx := by
  have hsplit : e.liftN (nx + Y) nx = (e.liftN Y nx).liftN (0 + nx) (0 + nx) := by
    rw [Nat.zero_add,
      VExpr.liftN'_liftN' (Nat.le_refl nx) (Nat.le_add_left nx Y),
      Nat.add_comm Y nx]
  rw [instUnder_eq_instUnderK, hsplit,
    show ((List.range nx).map fun s => VExpr.bvar (nx - 1 - s))
        = (List.range nx).map fun s => VExpr.bvar (0 + nx - 1 - s) from
      List.map_congr_left fun s hs => by rw [Nat.zero_add],
    instUnderK_blockSpine, VExpr.liftN_zero]

/-- Evaluating the substitution of the parameter and field variable spines
into a constructor's target type: the parameter variables re-point at the
deep parameter binders and the constructor indices pick up the two-stage
lift. `M` is the depth of the parameter block below the application. -/
theorem instUnder_ctorTarget {nm : Name} {lvls : List VLevel}
    {P F R Q M : Nat} {ris : List VExpr}
    (hM : M = R + F + Q)
    (hcl : ∀ e ∈ ris, e.ClosedN (F + P)) :
    instUnder (mkAppList (.const nm lvls)
        (((List.range P).map fun k => VExpr.bvar (F + P - 1 - k)) ++ ris))
      (((List.range P).map fun k => VExpr.bvar (M + P - 1 - k)) ++
       ((List.range F).map fun p => VExpr.bvar (R + (F - 1 - p))))
      = mkAppList (.const nm lvls)
        (((List.range P).map fun k => VExpr.bvar (M + P - 1 - k)) ++
         ris.map fun e => (e.liftN Q F).liftN R) := by
  rw [instUnder_eq_instUnderK, instUnderK_mkAppList, instUnderK_const,
    List.map_append]
  have hlenES : (((List.range P).map fun k => VExpr.bvar (M + P - 1 - k)) ++
      ((List.range F).map fun p => VExpr.bvar (R + (F - 1 - p)))).length
      = P + F := by simp
  congr 1
  congr 1
  · -- the parameter variables: each picks out a spine entry
    rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hkP := List.mem_range.1 hk
    show instUnderK (.bvar (F + P - 1 - k)) _ 0 = _
    have hidx : (((List.range P).map fun k => VExpr.bvar (M + P - 1 - k)) ++
        ((List.range F).map fun p => VExpr.bvar (R + (F - 1 - p))))[k]?
        = some (VExpr.bvar (M + P - 1 - k)) := by
      rw [List.getElem?_append_left (by simp [hkP]),
        List.getElem?_map, List.getElem?_range hkP]
      rfl
    have h0 := instUnderK_spine_bvar (k := 0) hidx
    rw [Nat.zero_add, VExpr.liftN_zero, hlenES] at h0
    rw [show F + P - 1 - k = P + F - 1 - k by omega]
    exact h0
  · -- the constructor indices: two-phase substitution = two-stage lift
    refine List.map_congr_left fun e he => ?_
    have hcle := hcl e he
    show instUnderK e _ 0 = _
    rw [instUnderK_append]
    rw [show (0 : Nat) + ((List.range F).map fun p =>
        VExpr.bvar (R + (F - 1 - p))).length = F by simp]
    rw [instUnderK_bottomSpine (m := M) (by simpa using hcle)]
    have hsplit : e.liftN M F = ((e.liftN Q F).liftN (R + F) (0 + F)) := by
      rw [Nat.zero_add,
        VExpr.liftN'_liftN' (Nat.le_refl F) (Nat.le_add_left F Q),
        hM]
      congr 1
      omega
    rw [hsplit,
      show ((List.range F).map fun p => VExpr.bvar (R + (F - 1 - p)))
          = (List.range F).map fun p => VExpr.bvar (R + F - 1 - p) from
        List.map_congr_left fun p hp => by
          have := List.mem_range.1 hp; congr 1; omega,
      instUnderK_blockSpine]

/-- Typing the constructor application `ctor params fields` of a minor
premise's conclusion (with `ΓR` the induction-hypothesis block above the
fields) or of an iota rule (`ΓR = []`, `Ns` the whole minor block). -/
theorem ctorApp_hasType {envC : VEnv} {Θ : RecCtx} {i q : Nat} {t : TypeView}
    {c : CtorView} {Ms Ns ΓR : List VExpr} {R : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (ht : Θ.types[i]? = some t) (hcm : c ∈ t.ctors)
    (hMsLen : Ms.length = Θ.n)
    (hN : Ns.length = q) (hR : ΓR.length = R) :
    envC.HasType Θ.recUvars
      (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
      (mkAppList (.const c.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (R + c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
         ((List.range c.fields.length).map fun p =>
            .bvar (R + (c.fields.length - 1 - p)))))
      (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (R + c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
         c.rIndices.map fun e =>
           (e.liftN (q + Θ.n) c.fields.length).liftN R)) := by
  have htm : t ∈ Θ.types := by
    have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
    exact he ▸ List.getElem_mem hlt
  -- closedness of the constructor indices
  have hPrev : CtxClosed Θ.params.reverse := by
    have := closedTele_ctxClosed (Γ₀ := []) trivial
      (by simpa using h.params_closed)
    simpa using this
  have hΓc : CtxClosed (c.fields.reverse ++ Θ.params.reverse) :=
    closedTele_ctxClosed hPrev (by
      rw [List.length_reverse, ← h.np_eq]
      exact h.fields_closed t htm c hcm)
  have hrisC : ∀ e ∈ c.rIndices, e.ClosedN (c.fields.length + Θ.np) := by
    intro e he
    have := FillsTele.closedN henv hΓc (h.rIndices_fill i t ht c hcm) e he
    simpa [h.np_eq] using this
  -- the constant, at the appended telescope
  have hctorC := h.ctor_const i t ht c hcm
    (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
      (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
  rw [← mkForallOF_append] at hctorC
  -- the parameter spine
  have hfillP := fills_varSpine_bottom (env := envC) (U := Θ.recUvars)
    (Ψ := Θ.params)
    (Γtop := ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++ (Ns ++ Ms.reverse)))
    h.params_closed
  rw [show (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++ (Ns ++ Ms.reverse)))
        ++ Θ.params.reverse
      = ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))) by
    simp [List.append_assoc]] at hfillP
  rw [← h.np_eq] at hfillP
  rw [show (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++ (Ns ++ Ms.reverse))).length
      = R + c.fields.length + q + Θ.n by
    simp [hR, hN, hMsLen]; omega] at hfillP
  -- the residual field telescope and its spine
  have hres := instTeleUnder_bottomSpine (Δ := c.fields) (p := Θ.np)
    (m := R + c.fields.length + q + Θ.n)
    (h.fields_closed t htm c hcm)
  have hfillF : FillsTele envC Θ.recUvars
      (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (R + c.fields.length + q + Θ.n) c.fields)
      ((List.range c.fields.length).map fun p =>
        .bvar (R + (c.fields.length - 1 - p))) := by
    rw [show R + c.fields.length + q + Θ.n
        = (q + Θ.n) + (R + c.fields.length) by omega,
      ← liftTele_liftTele (n₁ := q + Θ.n)
        (n₂ := R + c.fields.length) (k := 0),
      show ((List.range c.fields.length).map fun p =>
          VExpr.bvar (R + (c.fields.length - 1 - p)))
          = (List.range c.fields.length).map fun p =>
            VExpr.bvar (R + c.fields.length - 1 - p) from
        List.map_congr_left fun p hp => by
          have := List.mem_range.1 hp; congr 1; omega]
    refine fills_varSpine2 (by omega) (fun p A hA => ?_)
    have hp : p < c.fields.length := (List.getElem?_eq_some_iff.1 hA).1
    have hA' : (liftTele (q + Θ.n) c.fields)[p]? = some (A.liftN (q + Θ.n) p) := by
      rw [getElem?_liftTele, hA]; simp
    have hlk := lookup_midBlock (Γtop := ΓR)
      (Γrest := Ns ++ (Ms.reverse ++ Θ.params.reverse)) hA'
    rw [liftTele_length, VExpr.liftN_liftN, hR,
      show R + (c.fields.length - 1 - p)
        = R + c.fields.length - 1 - p by omega,
      show c.fields.length - p + R
        = R + c.fields.length - p by omega] at hlk
    rw [Nat.zero_add]
    exact hlk
  rw [← hres] at hfillF
  -- assemble and evaluate
  have happC := (hfillP.append hfillF).appList hctorC
  rw [instUnder_ctorTarget (R := R) (Q := q + Θ.n)
    (hM := by omega) hrisC] at happC
  exact happC

/-- The minor premise's conclusion `motive_i (rIndices) (ctor params b)` is
well-typed: the constructor application is `ctorApp_hasType`, the index
arguments fill the motive's index telescope by weakening their
`RecCtxWF` clause into place, and `motiveApp_hasType` puts them together. -/
theorem minorConcl_hasType {envC : VEnv} {Θ : RecCtx} {i q : Nat} {t : TypeView}
    {c : CtorView} {Ms Ns ΓR : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (ht : Θ.types[i]? = some t) (hcm : c ∈ t.ctors)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hin : i < Θ.n)
    (hN : Ns.length = q) (hR : ΓR.length = (recFields Θ c).length) :
    envC.HasType Θ.recUvars
      (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
      (minorConcl Θ i q c) (.sort Θ.elim) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  obtain ⟨Mi, hMi, hMiTy⟩ := mapM_getElem? hMs (List.getElem?_range hin)
  -- the typed constructor application
  have hctor := ctorApp_hasType henv h ht hcm hMsLen hN hR
  -- the index arguments, weakened into the conclusion's context
  have hfill0 := h.rIndices_fill i t ht c hcm
  have W0 : Ctx.LiftN (q + Θ.n) 0 Θ.params.reverse
      ((Ns ++ Ms.reverse) ++ Θ.params.reverse) :=
    .zero (Ns ++ Ms.reverse) (by simp [hN, hMsLen])
  have h1 := FillsTele.weakN henv (ctxLiftN_teleBlock W0 (Δ := c.fields)) hfill0
  simp only [Nat.zero_add] at h1
  rw [show liftTele (q + Θ.n) (liftTele c.fields.length t.indices) c.fields.length
      = liftTele (c.fields.length + (q + Θ.n)) t.indices from by
    have := liftTele_liftTele_hi (Δ := t.indices) (n₁ := c.fields.length)
      (n₂ := q + Θ.n) (k := 0)
    simpa using this] at h1
  have W1 : Ctx.LiftN (recFields Θ c).length 0
      ((liftTele (q + Θ.n) c.fields).reverse ++
        ((Ns ++ Ms.reverse) ++ Θ.params.reverse))
      (ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        ((Ns ++ Ms.reverse) ++ Θ.params.reverse))) :=
    .zero ΓR hR
  have h2 := FillsTele.weakN henv W1 h1
  rw [liftTele_liftTele, List.map_map,
    show c.fields.length + (q + Θ.n) + (recFields Θ c).length
      = (recFields Θ c).length + c.fields.length + q + Θ.n by omega] at h2
  -- assemble via the motive application
  have happF := motiveApp_hasType (env := envC) (U := Θ.recUvars)
    (Θ := Θ) (j := i) (t' := t)
    (D := (recFields Θ c).length + c.fields.length + q)
    (ΓD := ΓR ++ ((liftTele (q + Θ.n) c.fields).reverse ++ Ns))
    (Γrest := Θ.params.reverse) (Ms := Ms)
    (is := c.rIndices.map fun e =>
      (e.liftN (q + Θ.n) c.fields.length).liftN (recFields Θ c).length)
    ht hin hMsLen hMi hMiTy
    (by simp [hR, hN]; omega)
    (by
      refine Eq.mp ?_ h2
      congr 1
      simp [List.append_assoc])
    (by
      refine Eq.mp ?_ hctor
      congr 1
      simp [List.append_assoc])
  refine Eq.mp ?_ happF
  simp only [minorConcl]
  congr 1
  simp [List.append_assoc]

/-! ## The induction hypotheses

The `ρ`-th induction hypothesis of a minor premise re-abstracts a
recursive field's argument telescope `xs` and applies the target type's
motive to the field's index arguments and the re-applied field variable.
Everything lives two lifts away from the `RecCtxWF` clauses: `q + n`
binders (minors and motives) inserted between the field prefix and the
parameters, and `ρ + (nf - pf)` binders (previous IHs and the remaining
fields) inserted directly above `xs`. -/

theorem liftTele_take : ∀ {Δ : List VExpr} {m k j : Nat},
    liftTele m (Δ.take j) k = (liftTele m Δ k).take j
  | [], _, _, _ => by simp
  | A :: Δ, m, k, 0 => rfl
  | A :: Δ, m, k, j+1 => by
    simp only [List.take_succ_cons, liftTele_cons, liftTele_take (Δ := Δ)]

theorem reverse_drop_take {α} {l : List α} {j : Nat} :
    (l.drop j).reverse ++ (l.take j).reverse = l.reverse := by
  rw [← List.reverse_append, List.take_append_drop]

/-- The recursive field's index arguments, weakened into the induction
hypothesis's context: the `RecCtxWF` fill clause pushed under the two
binder-block insertions. -/
theorem recField_fill_deep {envC : VEnv} {Θ : RecCtx} {q ρ pf it : Nat}
    {t t' : TypeView} {c : CtorView} {xs ris Ms Ns Γρ : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hmem : (pf, xs, it, ris) ∈ recFields Θ c)
    (ht' : Θ.types[it]? = some t')
    (hpf : pf ≤ c.fields.length)
    (hMsLen : Ms.length = Θ.n) (hN : Ns.length = q) (hρ : Γρ.length = ρ) :
    FillsTele envC Θ.recUvars
      ((liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++
        (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
          (Ns ++ (Ms.reverse ++ Θ.params.reverse)))))
      (liftTele (xs.length + ρ + c.fields.length + q + Θ.n) t'.indices)
      (ris.map fun e => lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e) := by
  have hfill0 := h.recField_fill t htm c hcm pf xs it ris hmem t' ht'
  rw [List.append_assoc] at hfill0
  have W0 : Ctx.LiftN (q + Θ.n) 0 Θ.params.reverse
      ((Ns ++ Ms.reverse) ++ Θ.params.reverse) :=
    .zero (Ns ++ Ms.reverse) (by simp [hN, hMsLen])
  have W2 := ctxLiftN_teleBlock (ctxLiftN_teleBlock W0 (Δ := c.fields.take pf))
    (Δ := xs)
  simp only [Nat.zero_add, List.length_take, Nat.min_eq_left hpf] at W2
  have h1 := FillsTele.weakN henv W2 hfill0
  have hmid1 := liftTele_liftTele_mid (Δ := t'.indices)
    (n₁ := xs.length + pf) (n₂ := q + Θ.n) (k := 0) (j := pf + xs.length)
    (by omega)
  rw [Nat.zero_add] at hmid1
  rw [hmid1] at h1
  have W1 := ctxLiftN_teleBlock
    (Ctx.LiftN.zero (n := ρ + (c.fields.length - pf))
      (Γ := (liftTele (q + Θ.n) (c.fields.take pf)).reverse ++
        ((Ns ++ Ms.reverse) ++ Θ.params.reverse))
      (Γρ ++ ((liftTele (q + Θ.n) c.fields).drop pf).reverse)
      (by simp [hρ]))
    (Δ := liftTele (q + Θ.n) xs pf)
  simp only [Nat.zero_add, liftTele_length] at W1
  have h2 := FillsTele.weakN henv W1 h1
  have hmid2 := liftTele_liftTele_mid (Δ := t'.indices)
    (n₁ := xs.length + pf + (q + Θ.n)) (n₂ := ρ + (c.fields.length - pf))
    (k := 0) (j := xs.length) (by omega)
  rw [Nat.zero_add] at hmid2
  rw [hmid2] at h2
  refine Eq.mp ?_ h2
  congr 1
  · rw [liftTele2_eq]
    simp only [Nat.add_zero, List.append_assoc, liftTele_take]
    rw [← List.append_assoc Γρ, ← List.append_assoc (Γρ ++ _),
      List.append_assoc Γρ, reverse_drop_take]
    simp [List.append_assoc]
  · congr 1
    omega
  · rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    show VExpr.liftN (ρ + (c.fields.length - pf))
        (VExpr.liftN (q + Θ.n) e (pf + xs.length)) xs.length
      = lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e
    rw [lift2, Nat.add_comm pf xs.length]

/-- The re-applied recursive field variable `f xs` of an induction
hypothesis, at the type the motive application needs: the field's stored
type is the reassembled telescope (`recField_shape`), its variable is
looked up through the two binder-block insertions, and applying the `xs`
variable spine cancels the telescope. -/
theorem recFieldApp_hasType {envC : VEnv} {Θ : RecCtx} {q ρ pf it : Nat}
    {t t' : TypeView} {c : CtorView} {xs ris Ms Ns Γρ : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hmem : (pf, xs, it, ris) ∈ recFields Θ c)
    (ht' : Θ.types[it]? = some t')
    (hMsLen : Ms.length = Θ.n) (hN : Ns.length = q) (hρ : Γρ.length = ρ) :
    envC.HasType Θ.recUvars
      ((liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++
        (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
          (Ns ++ (Ms.reverse ++ Θ.params.reverse)))))
      (mkAppList (.bvar (xs.length + ρ + (c.fields.length - 1 - pf)))
        ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s)))
      (mkAppList (.const t'.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (xs.length + ρ + c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
         ris.map fun e => lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e)) := by
  have hnm := h.names_eq it t' ht'
  have hF := h.recField_shape t htm c hcm pf xs it ris hmem t'.name hnm
  have hpf : pf < c.fields.length := (List.getElem?_eq_some_iff.1 hF).1
  -- look up the field variable through the two insertions
  have hA' : (liftTele (q + Θ.n) c.fields)[pf]?
      = some ((mkForallOF xs (mkAppList (.const t'.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              VExpr.bvar (xs.length + pf + Θ.np - 1 - k)) ++ ris))).liftN
        (q + Θ.n) pf) := by
    rw [getElem?_liftTele, hF]; simp
  have hlk := lookup_midBlock
    (Γtop := (liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++ Γρ)
    (Γrest := Ns ++ (Ms.reverse ++ Θ.params.reverse)) hA'
  rw [List.append_assoc, liftTele_length,
    show ((liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++ Γρ).length
      = xs.length + ρ by simp [hρ],
    VExpr.liftN_liftN] at hlk
  have hbv := VEnv.IsDefEq.bvar (env := envC) (uvars := Θ.recUvars) hlk
  rw [mkForallOF_liftN, mkForallOF_liftN,
    show (liftTele (q + Θ.n) xs pf).length = xs.length from liftTele_length,
    Nat.zero_add,
    show c.fields.length - pf + (xs.length + ρ) = xs.length + (ρ + (c.fields.length - pf))
      by omega] at hbv
  -- the xs variable spine fills the doubly-lifted telescope
  have hxs : FillsTele envC Θ.recUvars
      ((liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++
        (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
          (Ns ++ (Ms.reverse ++ Θ.params.reverse)))))
      (liftTele (xs.length + (ρ + (c.fields.length - pf)))
        (liftTele (q + Θ.n) xs pf))
      ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s)) := by
    rw [show xs.length + (ρ + (c.fields.length - pf))
        = (ρ + (c.fields.length - pf)) + xs.length by omega,
      ← liftTele_liftTele (n₁ := ρ + (c.fields.length - pf)) (n₂ := xs.length)
        (k := 0)]
    have hmid := fills_varSpine_mid (env := envC) (U := Θ.recUvars)
      (Δ := liftTele (ρ + (c.fields.length - pf)) (liftTele (q + Θ.n) xs pf))
      (Γtop := ([] : List VExpr))
      (Γrest := Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
    simp only [List.nil_append, List.length_nil, Nat.zero_add,
      liftTele_length] at hmid
    refine Eq.mp ?_ hmid
    congr 2
    rw [liftTele2_eq, Nat.add_zero]
  have happ := hxs.appList hbv
  -- evaluate the application's type
  rw [instUnder_selfSpine, mkAppList_liftN, mkAppList_liftN,
    List.map_append, List.map_append, List.map_map] at happ
  rw [show VExpr.liftN (ρ + (c.fields.length - pf))
      (VExpr.liftN (q + Θ.n) (VExpr.const t'.name Θ.lvls) (pf + xs.length))
      xs.length = VExpr.const t'.name Θ.lvls from rfl] at happ
  have hEp : List.map ((fun x => VExpr.liftN (ρ + (c.fields.length - pf)) x xs.length)
        ∘ fun x => VExpr.liftN (q + Θ.n) x (pf + xs.length))
      (List.map (fun k => VExpr.bvar (xs.length + pf + Θ.np - 1 - k))
        (List.range Θ.np))
      = (List.range Θ.np).map fun k =>
          VExpr.bvar (xs.length + ρ + c.fields.length + q + Θ.n + Θ.np - 1 - k) := by
    rw [← List.map_map, liftN_varSpine (by omega), liftN_varSpine (by omega)]
    exact varSpine_congr (by omega)
  have hEr : List.map (fun x => VExpr.liftN (ρ + (c.fields.length - pf)) x xs.length)
      (List.map (fun x => VExpr.liftN (q + Θ.n) x (pf + xs.length)) ris)
      = ris.map fun e =>
          lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    show VExpr.liftN (ρ + (c.fields.length - pf))
        (VExpr.liftN (q + Θ.n) e (pf + xs.length)) xs.length
      = lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e
    rw [lift2, Nat.add_comm pf xs.length]
  rw [hEp, hEr] at happ
  exact happ

/-- The recursive field's argument telescope, weakened into the induction
hypothesis's binder position. -/
theorem recField_tele_deep {envC : VEnv} {Θ : RecCtx} {q ρ pf it : Nat}
    {t : TypeView} {c : CtorView} {xs ris Ms Ns Γρ : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hmem : (pf, xs, it, ris) ∈ recFields Θ c)
    (hpf : pf ≤ c.fields.length)
    (hMsLen : Ms.length = Θ.n) (hN : Ns.length = q) (hρ : Γρ.length = ρ) :
    TeleWF envC Θ.recUvars
      (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs) := by
  have base := h.recField_tele t htm c hcm pf xs it ris hmem
  have W0 : Ctx.LiftN (q + Θ.n) 0 Θ.params.reverse
      ((Ns ++ Ms.reverse) ++ Θ.params.reverse) :=
    .zero (Ns ++ Ms.reverse) (by simp [hN, hMsLen])
  have W2 := ctxLiftN_teleBlock W0 (Δ := c.fields.take pf)
  simp only [Nat.zero_add, List.length_take, Nat.min_eq_left hpf] at W2
  have T1 := TeleWF.weakN henv W2 base
  have W1 : Ctx.LiftN (ρ + (c.fields.length - pf)) 0
      ((liftTele (q + Θ.n) (c.fields.take pf)).reverse ++
        ((Ns ++ Ms.reverse) ++ Θ.params.reverse))
      ((Γρ ++ ((liftTele (q + Θ.n) c.fields).drop pf).reverse) ++
        ((liftTele (q + Θ.n) (c.fields.take pf)).reverse ++
          ((Ns ++ Ms.reverse) ++ Θ.params.reverse))) :=
    .zero (Γρ ++ ((liftTele (q + Θ.n) c.fields).drop pf).reverse) (by simp [hρ])
  have T2 := TeleWF.weakN henv W1 T1
  refine Eq.mp ?_ T2
  congr 1
  · simp only [List.append_assoc, liftTele_take]
    rw [← List.append_assoc Γρ, ← List.append_assoc (Γρ ++ _),
      List.append_assoc Γρ, reverse_drop_take]
    simp [List.append_assoc]
  · rw [liftTele2_eq, Nat.add_zero]

@[simp] theorem minorIHs_length {Θ : RecCtx} {q : Nat} {c : CtorView} :
    (minorIHs Θ q c).length = (recFields Θ c).length := by
  simp [minorIHs]

/-- A single induction hypothesis is a type in its binder's context:
the re-abstracted argument telescope (`recField_tele_deep`) over the
motive applied to the field's indices (`recField_fill_deep`) and the
re-applied field variable (`recFieldApp_hasType`). -/
theorem minorIH_isType {envC : VEnv} {Θ : RecCtx} {q ρ pf it : Nat}
    {t : TypeView} {c : CtorView} {xs ris Ms Ns Γρ : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hrf : (recFields Θ c)[ρ]? = some (pf, xs, it, ris))
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hN : Ns.length = q) (hρ : Γρ.length = ρ) :
    envC.IsType Θ.recUvars
      (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse))))
      (mkForallOF (liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs)
        (.app (mkAppList
            (.bvar (xs.length + ρ + c.fields.length + q + (Θ.n - 1 - it)))
            (ris.map fun e =>
              lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e))
          (mkAppList (.bvar (xs.length + ρ + (c.fields.length - 1 - pf)))
            ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s))))) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  have hmem : (pf, xs, it, ris) ∈ recFields Θ c := List.mem_of_getElem? hrf
  have hitn : it < Θ.n := by
    have := recFields_it_lt hmem
    rw [h.names_len, ← h.n_eq] at this
    exact this
  obtain ⟨t', ht'⟩ : ∃ t', Θ.types[it]? = some t' :=
    ⟨_, List.getElem?_eq_getElem (by rw [← h.n_eq]; exact hitn)⟩
  obtain ⟨Mit, hMit, hMitTy⟩ := mapM_getElem? hMs (List.getElem?_range hitn)
  have hpf : pf ≤ c.fields.length := by
    have hF := h.recField_shape t htm c hcm pf xs it ris hmem t'.name
      (h.names_eq it t' ht')
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hF).1
  have hTele := recField_tele_deep (t := t) henv h htm hcm hmem hpf hMsLen hN hρ
  have hfill := recField_fill_deep henv h htm hcm hmem ht' hpf hMsLen hN hρ
  have ha := recFieldApp_hasType henv h htm hcm hmem ht' hMsLen hN hρ
  have happB := motiveApp_hasType (env := envC) (U := Θ.recUvars)
    (Θ := Θ) (j := it) (t' := t')
    (D := xs.length + ρ + c.fields.length + q)
    (ΓD := (liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs).reverse ++
      (Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++ Ns)))
    (Γrest := Θ.params.reverse) (Ms := Ms)
    (is := ris.map fun e =>
      lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e)
    ht' hitn hMsLen hMit hMitTy
    (by simp [hρ, hN]; omega)
    (by
      refine Eq.mp ?_ hfill
      congr 1
      simp [List.append_assoc])
    (by
      refine Eq.mp ?_ ha
      congr 1
      simp [List.append_assoc])
  refine TeleWF.mkForallOF_isType hTele ⟨Θ.elim, ?_⟩
  refine Eq.mp ?_ happB
  congr 1
  simp [List.append_assoc]

theorem TeleWF.append : ∀ {Δ₁ Δ₂ : List VExpr} {Γ₀},
    TeleWF env U Γ₀ Δ₁ → TeleWF env U (Δ₁.reverse ++ Γ₀) Δ₂ →
    TeleWF env U Γ₀ (Δ₁ ++ Δ₂)
  | [], _, _, _, h2 => by simpa using h2
  | A :: Δ₁, Δ₂, Γ₀, ⟨hA, h1⟩, h2 => by
    refine ⟨hA, ?_⟩
    refine TeleWF.append h1 ?_
    rwa [show Δ₁.reverse ++ (A :: Γ₀) = (A :: Δ₁).reverse ++ Γ₀ by simp]

/-- The full induction-hypothesis telescope of a minor premise. -/
theorem minorIHs_wf {envC : VEnv} {Θ : RecCtx} {q : Nat}
    {t : TypeView} {c : CtorView} {Ms Ns : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hN : Ns.length = q) :
    TeleWF envC Θ.recUvars
      ((liftTele (q + Θ.n) c.fields).reverse ++
        (Ns ++ (Ms.reverse ++ Θ.params.reverse)))
      (minorIHs Θ q c) := by
  refine TeleWF.of_isType_at fun ρ A hA Γρ hρ => ?_
  rw [minorIHs, List.getElem?_map, List.getElem?_zipIdx] at hA
  obtain ⟨⟨⟨pf, xs, it, ris⟩, ρ'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hA
  obtain ⟨r, hr, h3⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨rfl, rfl⟩ : r = (pf, xs, it, ris) ∧ ρ' = ρ := by
    cases h3; exact ⟨rfl, by omega⟩
  subst h2
  have := minorIH_isType (Γρ := Γρ) henv h htm hcm hr hMs hN hρ
  refine Eq.mp ?_ this
  rw [show Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
      (Ns ++ (Ms.reverse ++ Θ.params.reverse)))
    = Γρ ++ ((liftTele (q + Θ.n) c.fields).reverse ++
      (Ns ++ (Ms.reverse ++ Θ.params.reverse))) from rfl]

/-- A minor premise is a type in the recursor's context: its fields
telescope, induction hypotheses and conclusion assembled. -/
theorem minorType_isType' {envC : VEnv} {Θ : RecCtx} {i q : Nat}
    {t : TypeView} {c : CtorView} {Ms Ns : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (ht : Θ.types[i]? = some t) (hcm : c ∈ t.ctors)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hin : i < Θ.n) (hN : Ns.length = q) :
    envC.IsType Θ.recUvars (Ns ++ (Ms.reverse ++ Θ.params.reverse))
      (minorType Θ i q c) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  have htm : t ∈ Θ.types := by
    have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
    exact he ▸ List.getElem_mem hlt
  have hfields : TeleWF envC Θ.recUvars (Ns ++ (Ms.reverse ++ Θ.params.reverse))
      (liftTele (q + Θ.n) c.fields) := by
    have W0 : Ctx.LiftN (q + Θ.n) 0 Θ.params.reverse
        ((Ns ++ Ms.reverse) ++ Θ.params.reverse) :=
      .zero (Ns ++ Ms.reverse) (by simp [hN, hMsLen])
    have := TeleWF.weakN henv W0 (h.fields_wf t htm c hcm)
    refine Eq.mp ?_ this
    congr 1
    simp [List.append_assoc]
  have hihs := minorIHs_wf henv h htm hcm hMs hN
  have hconcl := minorConcl_hasType (ΓR := (minorIHs Θ q c).reverse)
    henv h ht hcm hMs hin hN (by simp)
  exact minorType_isType_of_parts hfields hihs ⟨Θ.elim, hconcl⟩

/-- The constructor fold of `minorTele`, one type's worth: the counter
tracks the accumulated telescope's length, and each appended minor
premise is a type over the prefix. -/
theorem minorCtorFold_wf {envC : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    {t : TypeView} {i : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (ht : Θ.types[i]? = some t) (hin : i < Θ.n) :
    ∀ (cs : List CtorView) (st : Nat × List VExpr),
    (∀ c ∈ cs, c ∈ t.ctors) →
    st.1 = st.2.length →
    TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse) st.2 →
    (cs.foldl (fun (p : Nat × List VExpr) c =>
        (p.1 + 1, p.2 ++ [minorType Θ i p.1 c])) st).1
      = (cs.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ i p.1 c])) st).2.length ∧
    (cs.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ i p.1 c])) st).1
      = st.1 + cs.length ∧
    TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse)
      (cs.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ i p.1 c])) st).2
  | [], st, _, h1, h2 => ⟨h1, by simp, h2⟩
  | c :: cs, ⟨q, acc⟩, hcs, h1, h2 => by
    simp only at h1
    have hstep : TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse)
        (acc ++ [minorType Θ i q c]) := by
      refine TeleWF.append h2 ⟨?_, trivial⟩
      exact minorType_isType' (Ns := acc.reverse) henv h ht (hcs c (.head _))
        hMs hin (by simp [h1])
    have IH := minorCtorFold_wf henv h hMs ht hin cs
      (q + 1, acc ++ [minorType Θ i q c])
      (fun c' hc' => hcs c' (.tail _ hc')) (by simp [h1]) hstep
    simp only [List.foldl_cons]
    exact ⟨IH.1, by rw [IH.2.1]; simp; omega, IH.2.2⟩

/-- The full minor-premise telescope: well-formed over the motives and
parameters, with its length equal to the block's constructor count. -/
theorem minorTele_wf {envC : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms) :
    TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse) (minorTele Θ) ∧
    (minorTele Θ).length = Θ.K := by
  have main : ∀ (L : List (TypeView × Nat)) (st : Nat × List VExpr),
      (∀ p ∈ L, Θ.types[p.2]? = some p.1) →
      st.1 = st.2.length →
      TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse) st.2 →
      (L.foldl (fun (p : Nat × List VExpr) (ti : TypeView × Nat) =>
          ti.1.ctors.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p)
          st).1
        = (L.foldl (fun p ti =>
            ti.1.ctors.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p)
            st).2.length ∧
      (L.foldl (fun p ti =>
          ti.1.ctors.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p)
          st).1
        = L.foldl (fun k ti => k + ti.1.ctors.length) st.1 ∧
      TeleWF envC Θ.recUvars (Ms.reverse ++ Θ.params.reverse)
        (L.foldl (fun p ti =>
          ti.1.ctors.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p)
          st).2 := by
    intro L
    induction L with
    | nil => exact fun st _ h1 h2 => ⟨h1, rfl, h2⟩
    | cons ti L ihL =>
      intro st hL h1 h2
      obtain ⟨t, i⟩ := ti
      have hti := hL (t, i) (.head _)
      have hin : i < Θ.n := by
        rw [h.n_eq]
        exact (List.getElem?_eq_some_iff.1 hti).1
      have step := minorCtorFold_wf henv h hMs hti hin t.ctors st
        (fun c hc => hc) h1 h2
      simp only [List.foldl_cons]
      have IH := ihL _ (fun p hp => hL p (.tail _ hp)) step.1 step.2.2
      refine ⟨IH.1, ?_, IH.2.2⟩
      rw [IH.2.1, step.2.1]
  have hmem : ∀ p ∈ Θ.types.zipIdx, Θ.types[p.2]? = some p.1 := by
    intro ⟨t, i⟩ hp
    exact mem_zipIdx_getElem? hp
  have res := main Θ.types.zipIdx (0, []) hmem rfl trivial
  have hK : Θ.types.zipIdx.foldl (fun k (ti : TypeView × Nat) =>
      k + ti.1.ctors.length) 0 = Θ.K := by
    rw [h.K_eq]
    suffices hz : ∀ (l : List TypeView) (off k : Nat),
        (l.zipIdx off).foldl (fun k ti => k + ti.1.ctors.length) k
          = l.foldl (fun k t => k + t.ctors.length) k by
      exact hz Θ.types 0 0
    intro l
    induction l with
    | nil => intro off k; rfl
    | cons t l ih =>
      intro off k
      simp only [List.zipIdx_cons, List.foldl_cons]
      exact ih _ _
  have hMT : minorTele Θ
      = (List.foldl (fun (p : Nat × List VExpr) (ti : TypeView × Nat) =>
          List.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p
            ti.1.ctors)
          (0, []) Θ.types.zipIdx).2 := rfl
  rw [hMT]
  exact ⟨res.2.2, by rw [← res.1]; exact res.2.1.trans hK⟩

/-- The recursor type for each type of the block is a type in the empty
context: parameters, motives, minor premises, indices, major premise, and
the motive application assembled in order. -/
theorem recType_isType {envC : VEnv} {Θ : RecCtx}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    {i : Nat} {t : TypeView} (ht : Θ.types[i]? = some t) :
    ∃ T, recType Θ i = some T ∧ envC.IsType Θ.recUvars [] T := by
  have htm : t ∈ Θ.types := by
    have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
    exact he ▸ List.getElem_mem hlt
  have hin : i < Θ.n := by
    rw [h.n_eq]; exact (List.getElem?_eq_some_iff.1 ht).1
  obtain ⟨Ms, hMs0, hMsWF⟩ := motiveTele_wf henv h Θ.n 0 (by rw [← h.n_eq]; omega)
  have hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms := by
    rwa [List.range_eq_range']
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  obtain ⟨hMWF, hMlen⟩ := minorTele_wf henv h hMs
  have hT : recType Θ i = some (mkForallOF Θ.params (mkForallOF Ms
      (mkForallOF (minorTele Θ)
      (mkForallOF (liftTele (Θ.K + Θ.n) t.indices)
        (.forallE (mkAppList (.const t.name Θ.lvls)
            (((List.range Θ.np).map fun k =>
                .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
             ((List.range t.indices.length).map fun m =>
                .bvar (t.indices.length - 1 - m))))
          (.app (mkAppList (.bvar (1 + t.indices.length + Θ.K + (Θ.n - 1 - i)))
              ((List.range t.indices.length).map fun m =>
                .bvar (1 + (t.indices.length - 1 - m))))
            (.bvar 0))))))) := by
    rw [recType, hMs]
    simp [hMlen, ht]
    exact ⟨(), rfl⟩
  refine ⟨_, hT, ?_⟩
  refine TeleWF.mkForallOF_isType h.params_wf ?_
  rw [List.append_nil]
  refine TeleWF.mkForallOF_isType (hMsWF [] rfl) ?_
  refine TeleWF.mkForallOF_isType hMWF ?_
  refine TeleWF.mkForallOF_isType (Eq.mp (by congr 1; simp [List.append_assoc])
    (indices_wf_weak (Γtop := (minorTele Θ).reverse ++ Ms.reverse)
      (d := Θ.K + Θ.n) henv h htm (by simp [hMlen, hMsLen]))) ?_
  -- the innermost `∀ (x : I params ix), motive_i ix x`
  obtain ⟨ℓ', hconst⟩ := h.type_const t htm
  have hmaj : envC.HasType Θ.recUvars
      ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
      (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            .bvar (t.indices.length - 1 - m))))
      (.sort ℓ') := by
    have hconstT := hconst ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
      ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
    rw [← mkForallOF_append] at hconstT
    have hfillP := fills_varSpine_bottom (env := envC) (U := Θ.recUvars)
      (Ψ := Θ.params)
      (Γtop := (liftTele (Θ.K + Θ.n) t.indices).reverse ++
        ((minorTele Θ).reverse ++ Ms.reverse))
      h.params_closed
    rw [show ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ Ms.reverse)) ++ Θ.params.reverse
        = (liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)) by
      simp [List.append_assoc]] at hfillP
    rw [← h.np_eq] at hfillP
    rw [show ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ Ms.reverse)).length
        = t.indices.length + Θ.K + Θ.n by
      simp [hMlen, hMsLen]; omega] at hfillP
    have hres := instTeleUnder_bottomSpine (Δ := t.indices) (p := Θ.np)
      (m := t.indices.length + Θ.K + Θ.n) (h.idx_closed t htm)
    have hfillI : FillsTele envC Θ.recUvars
        ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
        (liftTele (t.indices.length + Θ.K + Θ.n) t.indices)
        ((List.range t.indices.length).map fun m =>
          .bvar (t.indices.length - 1 - m)) := by
      rw [show t.indices.length + Θ.K + Θ.n
          = (Θ.K + Θ.n) + t.indices.length by omega,
        ← liftTele_liftTele (n₁ := Θ.K + Θ.n) (n₂ := t.indices.length) (k := 0)]
      refine fills_varSpine2 (by omega) (fun j A hA => ?_)
      have hj : j < t.indices.length := (List.getElem?_eq_some_iff.1 hA).1
      have hA' : (liftTele (Θ.K + Θ.n) t.indices)[j]?
          = some (A.liftN (Θ.K + Θ.n) j) := by
        rw [getElem?_liftTele, hA]; simp
      have hlk := lookup_topBlock
        (Γrest := (minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)) hA'
      rw [liftTele_length] at hlk
      rw [Nat.zero_add]
      exact hlk
    rw [← hres] at hfillI
    have happM := (hfillP.append hfillI).appList hconstT
    rwa [instUnder_eq_instUnderK, instUnderK_sort] at happM
  refine VEnv.IsType.forallE ⟨ℓ', hmaj⟩ ⟨Θ.elim, ?_⟩
  -- the motive application under the major binder
  obtain ⟨Mi, hMi, hMiTy⟩ := mapM_getElem? hMs (List.getElem?_range hin)
  have hfillB : FillsTele envC Θ.recUvars
      ((mkAppList (.const t.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
           ((List.range t.indices.length).map fun m =>
              .bvar (t.indices.length - 1 - m)))) ::
        ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (1 + t.indices.length + Θ.K + Θ.n) t.indices)
      ((List.range t.indices.length).map fun m =>
        .bvar (1 + (t.indices.length - 1 - m))) := by
    rw [show 1 + t.indices.length + Θ.K + Θ.n
        = (Θ.K + Θ.n) + (1 + t.indices.length) by omega,
      ← liftTele_liftTele (n₁ := Θ.K + Θ.n) (n₂ := 1 + t.indices.length) (k := 0),
      show ((List.range t.indices.length).map fun m =>
          VExpr.bvar (1 + (t.indices.length - 1 - m)))
        = (List.range t.indices.length).map fun m =>
          VExpr.bvar (1 + t.indices.length - 1 - m) from
      List.map_congr_left fun m hm => by
        have := List.mem_range.1 hm; congr 1; omega]
    refine fills_varSpine2 (by omega) (fun j A hA => ?_)
    have hj : j < t.indices.length := (List.getElem?_eq_some_iff.1 hA).1
    have hA' : (liftTele (Θ.K + Θ.n) t.indices)[j]?
        = some (A.liftN (Θ.K + Θ.n) j) := by
      rw [getElem?_liftTele, hA]; simp
    have hlk := lookup_midBlock
      (Γtop := [mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            .bvar (t.indices.length - 1 - m)))])
      (Γrest := (minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)) hA'
    rw [liftTele_length, VExpr.liftN_liftN] at hlk
    rw [Nat.zero_add,
      show 1 + t.indices.length - 1 - j = 1 + (t.indices.length - 1 - j) by omega,
      show 1 + t.indices.length - j = t.indices.length - j + 1 by omega]
    exact hlk
  have haB : envC.HasType Θ.recUvars
      ((mkAppList (.const t.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
           ((List.range t.indices.length).map fun m =>
              .bvar (t.indices.length - 1 - m)))) ::
        ((liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (.bvar 0)
      (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (1 + t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
          .bvar (1 + (t.indices.length - 1 - m))))) := by
    have hbv := VEnv.IsDefEq.bvar (env := envC) (uvars := Θ.recUvars)
      (Lookup.zero (Γ := (liftTele (Θ.K + Θ.n) t.indices).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
        (ty := mkAppList (.const t.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
           ((List.range t.indices.length).map fun m =>
              .bvar (t.indices.length - 1 - m)))))
    refine Eq.mp ?_ hbv
    congr 1
    show VExpr.lift (mkAppList _ _) = _
    rw [show (VExpr.lift (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            VExpr.bvar (t.indices.length - 1 - m)))))
        = (mkAppList (.const t.name Θ.lvls)
          ((((List.range Θ.np).map fun k =>
              VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
           ((List.range t.indices.length).map fun m =>
              VExpr.bvar (t.indices.length - 1 - m))).map
            (VExpr.liftN 1 · 0))) from mkAppList_liftN]
    rw [List.map_append, liftN_varSpine (by omega), liftN_varSpine (by omega)]
    congr 2
    · exact varSpine_congr (by omega)
    · refine List.map_congr_left fun m hm => ?_
      have := List.mem_range.1 hm
      congr 1
      omega
  have hbody := motiveApp_hasType (env := envC) (U := Θ.recUvars)
    (Θ := Θ) (j := i) (t' := t)
    (D := 1 + t.indices.length + Θ.K)
    (ΓD := (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            .bvar (t.indices.length - 1 - m)))) ::
      ((liftTele (Θ.K + Θ.n) t.indices).reverse ++ (minorTele Θ).reverse))
    (Γrest := Θ.params.reverse) (Ms := Ms)
    (is := (List.range t.indices.length).map fun m =>
      .bvar (1 + (t.indices.length - 1 - m)))
    ht hin hMsLen hMi hMiTy
    (by simp [hMlen]; omega)
    (by
      refine Eq.mp ?_ hfillB
      congr 1
      simp [List.append_assoc])
    (by
      refine Eq.mp ?_ haB
      congr 1
      simp [List.append_assoc])
  refine Eq.mp ?_ hbody
  congr 1
  simp [List.append_assoc]

/-! ## Toward the iota rules

The iota rules apply the recursor constant to the parameter, motive,
minor and field variable spines. The pieces: lambda-telescope typing,
closedness of the motive and minor telescopes (extracted from their
typing), residual-telescope algebra for multi-block spines, and the
recursor constant at its stored type under the identity level
substitution. -/

@[simp] theorem mkLamOF_nil : mkLamOF [] e = e := rfl
@[simp] theorem mkLamOF_cons :
    mkLamOF (A :: Δ) e = .lam A (mkLamOF Δ e) := rfl

theorem TeleWF.mkLamOF_hasType : ∀ {Δ : List VExpr} {Γ₀ e B},
    TeleWF env U Γ₀ Δ → env.HasType U (Δ.reverse ++ Γ₀) e B →
    env.HasType U Γ₀ (mkLamOF Δ e) (mkForallOF Δ B)
  | [], _, _, _, _, he => by simpa using he
  | A :: Δ, Γ₀, e, B, ⟨⟨u, hA⟩, hΔ⟩, he => by
    rw [mkLamOF_cons, mkForallOF_cons]
    refine VEnv.HasType.lam hA (TeleWF.mkLamOF_hasType hΔ ?_)
    rwa [show Δ.reverse ++ (A :: Γ₀) = (A :: Δ).reverse ++ Γ₀ by simp]

theorem liftTele_zero : ∀ {Δ : List VExpr} {k}, liftTele 0 Δ k = Δ
  | [], _ => rfl
  | A :: Δ, k => by simp [liftTele_cons, liftTele_zero (Δ := Δ)]

theorem instUnderK_app : ∀ {es : List VExpr} {f a k},
    instUnderK (.app f a) es k = .app (instUnderK f es k) (instUnderK a es k)
  | [], _, _, _ => rfl
  | e :: es, f, a, k => by
    show instUnderK (.app (f.inst e (k + es.length)) (a.inst e (k + es.length))) es k = _
    rw [instUnderK_app (es := es)]
    simp only [instUnderK_cons]

theorem instTeleUnderK_append : ∀ {es₁ : List VExpr} {Δ es₂ k},
    instTeleUnderK Δ (es₁ ++ es₂) k
      = instTeleUnderK (instTeleUnderK Δ es₁ (k + es₂.length)) es₂ k
  | [], _, _, _ => rfl
  | e :: es₁, Δ, es₂, k => by
    simp only [List.cons_append, instTeleUnderK_cons, List.length_append]
    rw [instTeleUnderK_append (es₁ := es₁), show k + (es₁.length + es₂.length)
      = k + es₂.length + es₁.length by omega]

/-- Well-formed telescopes over closed contexts are closed. -/
theorem TeleWF.closedTele (henv : VEnv.Ordered env) :
    ∀ {Δ Γ₀ : List VExpr}, CtxClosed Γ₀ → TeleWF env U Γ₀ Δ →
    ClosedTele Δ Γ₀.length
  | [], _, _, _ => trivial
  | A :: Δ, Γ₀, hΓ₀, ⟨⟨u, hA⟩, hΔ⟩ => by
    have hAc : A.ClosedN Γ₀.length := VExpr.WF.closedN henv ⟨_, hA⟩ hΓ₀
    refine ⟨hAc, ?_⟩
    have := TeleWF.closedTele henv (Γ₀ := A :: Γ₀) ⟨hΓ₀, hAc⟩ hΔ
    simpa using this

theorem ClosedTele.liftTele : ∀ {Δ : List VExpr} {k m k'' : Nat},
    ClosedTele Δ k → ClosedTele (liftTele m Δ k'') (k + m)
  | [], _, _, _, _ => trivial
  | A :: Δ, k, m, k'', ⟨h1, h2⟩ => by
    refine ⟨h1.liftN, ?_⟩
    have := ClosedTele.liftTele (m := m) (k'' := k'' + 1) h2
    rwa [show k + 1 + m = k + m + 1 by omega] at this

/-- A constant with the identity level substitution has its stored type. -/
theorem hasType_const_id {env : VEnv} {c : Name} {ci : VConstant}
    (Γ : List VExpr) (H : env.constants c = some ci) (wf : VConstant.WF env ci) :
    env.HasType ci.uvars Γ (.const c (VLevel.params ci.uvars)) ci.type := by
  have h0 := VEnv.HasType.const (Γ := Γ) H VLevel.params_wf VLevel.params_length
  have ⟨_, h⟩ := wf
  rwa [(VEnv.IsDefEq.levelWF h trivial).1.instL_id] at h0

/-- The motive telescope is closed over the parameters. -/
theorem motiveTele_closed {envC : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms) :
    ClosedTele Ms Θ.np := by
  obtain ⟨Ms', hMs', hWF⟩ := motiveTele_wf henv h Θ.n 0 (by rw [← h.n_eq]; omega)
  rw [← List.range_eq_range'] at hMs'
  cases hMs.symm.trans hMs'
  have hP : CtxClosed Θ.params.reverse := by
    have := closedTele_ctxClosed (Γ₀ := []) trivial
      (by simpa using h.params_closed)
    simpa using this
  have := TeleWF.closedTele henv hP (by simpa using hWF [] rfl)
  rwa [List.length_reverse, ← h.np_eq] at this

/-- The minor-premise telescope is closed over the motives and
parameters. -/
theorem minorTele_closed {envC : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms) :
    ClosedTele (minorTele Θ) (Θ.n + Θ.np) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  have hP : CtxClosed Θ.params.reverse := by
    have := closedTele_ctxClosed (Γ₀ := []) trivial
      (by simpa using h.params_closed)
    simpa using this
  have hPM : CtxClosed (Ms.reverse ++ Θ.params.reverse) :=
    closedTele_ctxClosed hP (by
      rw [List.length_reverse, ← h.np_eq]
      exact motiveTele_closed henv h hMs)
  have := TeleWF.closedTele henv hPM (minorTele_wf henv h hMs).1
  rwa [List.length_append, List.length_reverse, List.length_reverse,
    hMsLen, ← h.np_eq] at this

theorem instUnderK_bvar_lt : ∀ {es : List VExpr} {v k : Nat}, v < k →
    instUnderK (.bvar v) es k = .bvar v
  | [], _, _, _ => rfl
  | e :: es, v, k, h => by
    simp only [instUnderK_cons]
    rw [inst_bvar_lt (by omega), instUnderK_bvar_lt (es := es) h]

/-- Substituting a spine whose suffix block contains the pointed-at
binder: the prefix substitutions pass over the variable. -/
theorem instUnderK_spine_suffix {es₁ es₂ : List VExpr} {m k : Nat} {A : VExpr}
    (h : es₂[m]? = some A) :
    instUnderK (.bvar (k + (es₂.length - 1 - m))) (es₁ ++ es₂) k = A.liftN k := by
  have hm : m < es₂.length := (List.getElem?_eq_some_iff.1 h).1
  rw [instUnderK_append, instUnderK_bvar_lt (by omega), instUnderK_spine_bvar h]

theorem FillsTele.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {Δ es}, FillsTele env U Γ Δ es → FillsTele env' U Γ Δ es
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨he, hes⟩ => ⟨he.mono hle, FillsTele.mono hle hes⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem TeleWF.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {Δ Γ₀}, TeleWF env U Γ₀ Δ → TeleWF env' U Γ₀ Δ
  | [], _, _ => trivial
  | _ :: _, _, ⟨hA, hΔ⟩ => ⟨hA.mono hle, TeleWF.mono hle hΔ⟩

/-- Applying the recursor constant to the parameter, motive, minor and
index-argument spines and a major premise: the central typing fact behind
both sides of an iota rule. The spine variables are stated in the "flat"
depth forms; `X` is the number of binders above the field block (`0` at
the rule's top level, `|xs|` inside an induction-hypothesis value). -/
theorem recApp_hasType {envC envR : VEnv} {Θ : RecCtx} {X i : Nat}
    {t : TypeView} {c : CtorView} {Ms ΓX : List VExpr} {T : VExpr}
    {is : List VExpr} {a : VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) (hle : envC ≤ envR)
    (ht : Θ.types[i]? = some t)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hX : ΓX.length = X)
    (hTt : recType Θ i = some T)
    (hconst : envR.constants (Lean.mkRecName t.name) = some ⟨Θ.recUvars, T⟩)
    (hTwf : envR.IsType Θ.recUvars [] T)
    (hfill : FillsTele envR Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (X + c.fields.length) (liftTele (Θ.K + Θ.n) t.indices)) is)
    (ha : envR.HasType Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      a
      (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            .bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++ is))) :
    envR.HasType Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (mkAppList (.const (Lean.mkRecName t.name) (VLevel.params Θ.recUvars))
        ((((((List.range Θ.np).map fun k =>
              .bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
            ((List.range Θ.n).map fun j =>
              .bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            .bvar (X + c.fields.length + Θ.K - 1 - p))) ++
          is) ++ [a]))
      (.app (mkAppList (.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - i)) is) a) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  have hin : i < Θ.n := by
    rw [h.n_eq]; exact (List.getElem?_eq_some_iff.1 ht).1
  have hisLen : is.length = t.indices.length := by
    have := hfill.length_eq
    simpa using this.symm
  obtain ⟨-, hMlen⟩ := minorTele_wf henv h hMs
  -- the shape of the recursor type
  have hTsh := hTt
  rw [recType, hMs] at hTsh
  simp [hMlen, ht] at hTsh
  obtain ⟨-, hTsh⟩ := hTsh
  subst hTsh
  -- the recursor constant, with its telescope collapsed to one append
  have hrc : envR.HasType Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (.const (Lean.mkRecName t.name) (VLevel.params Θ.recUvars))
      (mkForallOF Θ.params (mkForallOF Ms (mkForallOF (minorTele Θ)
        (mkForallOF (liftTele (Θ.K + Θ.n) t.indices)
          (.forallE (mkAppList (.const t.name Θ.lvls)
              (((List.range Θ.np).map fun k =>
                  .bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
               ((List.range t.indices.length).map fun m =>
                  .bvar (t.indices.length - 1 - m))))
            (.app (mkAppList (.bvar (1 + t.indices.length + Θ.K + (Θ.n - 1 - i)))
                ((List.range t.indices.length).map fun m =>
                  .bvar (1 + (t.indices.length - 1 - m))))
              (.bvar 0))))))) :=
    hasType_const_id _ hconst hTwf
  rw [show (VExpr.forallE (mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            VExpr.bvar (t.indices.length - 1 - m))))
      (.app (mkAppList (.bvar (1 + t.indices.length + Θ.K + (Θ.n - 1 - i)))
          ((List.range t.indices.length).map fun m =>
            VExpr.bvar (1 + (t.indices.length - 1 - m))))
        (.bvar 0)))
      = mkForallOF [mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            VExpr.bvar (t.indices.length - 1 - m)))]
      (.app (mkAppList (.bvar (1 + t.indices.length + Θ.K + (Θ.n - 1 - i)))
          ((List.range t.indices.length).map fun m =>
            VExpr.bvar (1 + (t.indices.length - 1 - m))))
        (.bvar 0)) from rfl,
    ← mkForallOF_append, ← mkForallOF_append, ← mkForallOF_append,
    ← mkForallOF_append] at hrc
  -- Phase 1: the parameter spine
  have hF1 := fills_varSpine_bottom (env := envR) (U := Θ.recUvars)
    (Ψ := Θ.params)
    (Γtop := ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
      ((minorTele Θ).reverse ++ Ms.reverse)))
    h.params_closed
  rw [show (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ Ms.reverse))) ++ Θ.params.reverse
      = ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))) by
    simp [List.append_assoc]] at hF1
  rw [← h.np_eq] at hF1
  rw [show (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ Ms.reverse))).length
      = X + c.fields.length + Θ.K + Θ.n by
    simp [hX, hMlen, hMsLen]; omega] at hF1
  -- Phase 2: the motive spine
  have hres2 := instTeleUnder_bottomSpine (Δ := Ms) (p := Θ.np)
    (m := X + c.fields.length + Θ.K + Θ.n)
    (motiveTele_closed henv h hMs)
  have hF2 : FillsTele envR Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (X + c.fields.length + Θ.K + Θ.n) Ms)
      ((List.range Θ.n).map fun j =>
        .bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j)) := by
    have h0 := fills_varSpine (env := envR) (U := Θ.recUvars) (Δ := Ms)
      (n := X + c.fields.length + Θ.K + Θ.n)
      (Γ := ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (by omega) (fun j Mj hMj => ?_)
    · rwa [hMsLen] at h0
    · have hj : j < Ms.length := (List.getElem?_eq_some_iff.1 hMj).1
      have hlk := lookup_midBlock
        (Γtop := ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
          (minorTele Θ).reverse))
        (Γrest := Θ.params.reverse) hMj
      rw [show (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
            (minorTele Θ).reverse)) ++ (Ms.reverse ++ Θ.params.reverse)
          = ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
            ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))) by
        simp [List.append_assoc],
        VExpr.liftN_liftN,
        show (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
            (minorTele Θ).reverse)).length = X + c.fields.length + Θ.K by
          simp [hX, hMlen]; omega] at hlk
      rwa [show X + c.fields.length + Θ.K + (Ms.length - 1 - j)
          = X + c.fields.length + Θ.K + Θ.n - 1 - j by omega,
        show Ms.length - j + (X + c.fields.length + Θ.K)
          = X + c.fields.length + Θ.K + Θ.n - j by omega] at hlk
  -- Phase 3: the minor spine
  have hminC : ClosedTele (minorTele Θ) (Θ.np + Θ.n) := by
    have := minorTele_closed henv h hMs
    rwa [Nat.add_comm] at this
  have hres3 : instTeleUnder (minorTele Θ)
      ((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))))
      = liftTele (X + c.fields.length + Θ.K) (minorTele Θ) := by
    rw [instTeleUnder_eq, instTeleUnderK_append,
      show (0 : Nat) + ((List.range Θ.n).map fun j =>
        VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j)).length = Θ.n by simp,
      instTeleUnderK_bottomSpine (m := X + c.fields.length + Θ.K + Θ.n) hminC]
    have hbs := instTeleUnderK_blockSpine (Δ := minorTele Θ) (p := Θ.n)
      (m := X + c.fields.length + Θ.K) (k := 0)
    rwa [Nat.zero_add] at hbs
  have hF3 : FillsTele envR Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (X + c.fields.length + Θ.K) (minorTele Θ))
      ((List.range Θ.K).map fun p =>
        .bvar (X + c.fields.length + Θ.K - 1 - p)) := by
    have h0 := fills_varSpine (env := envR) (U := Θ.recUvars) (Δ := minorTele Θ)
      (n := X + c.fields.length + Θ.K)
      (Γ := ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (by omega) (fun p Np hNp => ?_)
    · rwa [hMlen] at h0
    · have hp : p < (minorTele Θ).length := (List.getElem?_eq_some_iff.1 hNp).1
      have hlk := lookup_midBlock
        (Γtop := ΓX ++ (liftTele (Θ.K + Θ.n) c.fields).reverse)
        (Γrest := Ms.reverse ++ Θ.params.reverse) hNp
      rw [show (ΓX ++ (liftTele (Θ.K + Θ.n) c.fields).reverse) ++
            ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))
          = ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
            ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))) by
        simp [List.append_assoc],
        VExpr.liftN_liftN,
        show (ΓX ++ (liftTele (Θ.K + Θ.n) c.fields).reverse).length
          = X + c.fields.length by simp [hX]] at hlk
      rwa [show X + c.fields.length + ((minorTele Θ).length - 1 - p)
          = X + c.fields.length + Θ.K - 1 - p by omega,
        show (minorTele Θ).length - p + (X + c.fields.length)
          = X + c.fields.length + Θ.K - p by omega] at hlk
  -- Phase 4: the index-argument spine, against the computed residual
  have hres4 : instTeleUnder (liftTele (Θ.K + Θ.n) t.indices)
      (((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))))
      = liftTele (X + c.fields.length) (liftTele (Θ.K + Θ.n) t.indices) := by
    rw [instTeleUnder_eq, instTeleUnderK_append,
      show (0 : Nat) + ((List.range Θ.K).map fun p =>
        VExpr.bvar (X + c.fields.length + Θ.K - 1 - p)).length = Θ.K by simp,
      instTeleUnderK_append,
      show (Θ.K : Nat) + ((List.range Θ.n).map fun j =>
        VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j)).length
        = Θ.K + Θ.n by simp,
      instTeleUnderK_bottomSpine (m := X + c.fields.length + Θ.K + Θ.n)
        (ClosedTele.liftTele (h.idx_closed t (by
          have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
          exact he ▸ List.getElem_mem hlt))),
      instTeleUnderK_blockSpine (Δ := liftTele (Θ.K + Θ.n) t.indices)
        (p := Θ.n) (m := X + c.fields.length + Θ.K) (k := Θ.K)]
    have hbs := instTeleUnderK_blockSpine (Δ := liftTele (Θ.K + Θ.n) t.indices)
      (p := Θ.K) (m := X + c.fields.length) (k := 0)
    rwa [Nat.zero_add] at hbs
  -- Phase 5: the major premise
  have hres5 : instTeleUnder [mkAppList (.const t.name Θ.lvls)
      (((List.range Θ.np).map fun k =>
          VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
       ((List.range t.indices.length).map fun m =>
          VExpr.bvar (t.indices.length - 1 - m)))]
      ((((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is))
      = [mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++ is)] := by
    rw [instTeleUnder_eq, instTeleUnderK_consΔ, instTeleUnderK_nilΔ]
    congr 1
    rw [instUnderK_mkAppList, instUnderK_const, List.map_append]
    congr 1
    congr 1
    · rw [List.map_map]
      refine List.map_congr_left fun k hk => ?_
      have hkP := List.mem_range.1 hk
      show instUnderK (.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) _ 0 = _
      have hidx : ((((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is))[k]?
          = some (VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) := by
        rw [List.getElem?_append_left (by simp; omega),
          List.getElem?_append_left (by simp; omega),
          List.getElem?_append_left (by simp; omega),
          List.getElem?_map, List.getElem?_range hkP]
        rfl
      have h0 := instUnderK_spine_bvar (k := 0) hidx
      rw [Nat.zero_add, VExpr.liftN_zero,
        show ((((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is)).length
          = Θ.np + Θ.n + Θ.K + t.indices.length by simp [hisLen]; omega] at h0
      rw [show t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k
          = Θ.np + Θ.n + Θ.K + t.indices.length - 1 - k by omega]
      exact h0
    · refine List.ext_getElem? fun m => ?_
      rcases Nat.lt_or_ge m t.indices.length with hm | hm
      · rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hm]
        obtain ⟨A, hA⟩ : ∃ A, is[m]? = some A :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have h0 := instUnderK_spine_suffix (k := 0)
          (es₁ := ((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p)))) hA
        rw [Nat.zero_add, VExpr.liftN_zero] at h0
        rw [hA, Option.map_some, Option.map_some,
          show t.indices.length - 1 - m = is.length - 1 - m by omega, h0]
      · rw [List.getElem?_map, List.getElem?_eq_none (by simpa using hm),
          List.getElem?_eq_none (by omega)]
        rfl
  -- assemble the full spine
  rw [← hres2] at hF2
  rw [← hres3] at hF3
  have hF4 := hfill
  rw [← hres4] at hF4
  have hF5 : FillsTele envR Θ.recUvars
      (ΓX ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (instTeleUnder [mkAppList (.const t.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (t.indices.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
         ((List.range t.indices.length).map fun m =>
            VExpr.bvar (t.indices.length - 1 - m)))]
        ((((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is)))
      [a] := by
    rw [hres5]
    exact ⟨ha, trivial⟩
  have hFull := (((hF1.append hF2).append hF3).append hF4).append hF5
  have happ := hFull.appList hrc
  -- evaluate the resulting type
  rw [instUnder_eq_instUnderK, instUnderK_app, instUnderK_mkAppList] at happ
  have hlenES : ((((((List.range Θ.np).map fun k =>
      VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
    ((List.range Θ.n).map fun j =>
      VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
    ((List.range Θ.K).map fun p =>
      VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is) ++ [a]).length
      = Θ.np + Θ.n + Θ.K + t.indices.length + 1 := by
    simp [hisLen]; omega
  have hbv0 : instUnderK (.bvar 0)
      ((((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is) ++ [a]) 0 = a := by
    have h0 := instUnderK_spine_suffix (k := 0) (m := 0)
      (es₁ := (((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is))
      (es₂ := [a]) rfl
    simpa using h0
  have hhead : instUnderK
      (.bvar (1 + t.indices.length + Θ.K + (Θ.n - 1 - i)))
      ((((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is) ++ [a]) 0
      = .bvar (X + c.fields.length + Θ.K + Θ.n - 1 - i) := by
    have hidx : (((((((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
        ((List.range Θ.n).map fun j =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
        ((List.range Θ.K).map fun p =>
          VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is) ++ [a]))[Θ.np + i]?
        = some (VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - i)) := by
      rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_left (by simp; omega),
        List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by simp),
        show Θ.np + i - ((List.range Θ.np).map fun k =>
          VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)).length
          = i by simp,
        List.getElem?_map, List.getElem?_range hin]
      rfl
    have h0 := instUnderK_spine_bvar (k := 0) hidx
    rw [Nat.zero_add, VExpr.liftN_zero, hlenES] at h0
    rw [show 1 + t.indices.length + Θ.K + (Θ.n - 1 - i)
        = Θ.np + Θ.n + Θ.K + t.indices.length + 1 - 1 - (Θ.np + i) by omega]
    exact h0
  have hivs : (((List.range t.indices.length).map fun m =>
      VExpr.bvar (1 + (t.indices.length - 1 - m))).map
        (instUnderK · ((((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p))) ++ is) ++ [a]) 0))
      = is := by
    rw [List.map_map, List.append_assoc]
    refine List.ext_getElem? fun m => ?_
    rcases Nat.lt_or_ge m t.indices.length with hm | hm
    · rw [List.getElem?_map, List.getElem?_range hm]
      obtain ⟨A, hA⟩ : ∃ A, is[m]? = some A :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hA' : (is ++ [a])[m]? = some A := by
        rw [List.getElem?_append_left (by omega)]
        exact hA
      have h0 := instUnderK_spine_suffix (k := 0)
        (es₁ := ((((List.range Θ.np).map fun k =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
          ((List.range Θ.n).map fun j =>
            VExpr.bvar (X + c.fields.length + Θ.K + Θ.n - 1 - j))) ++
          ((List.range Θ.K).map fun p =>
            VExpr.bvar (X + c.fields.length + Θ.K - 1 - p)))) hA'
      rw [Nat.zero_add, VExpr.liftN_zero] at h0
      rw [hA, Option.map_some]
      show some (instUnderK (.bvar (1 + (t.indices.length - 1 - m))) _ 0) = some A
      rw [show 1 + (t.indices.length - 1 - m)
          = (is ++ [a]).length - 1 - m by simp [hisLen]; omega, h0]
    · rw [List.getElem?_map, List.getElem?_eq_none (by simpa using hm),
        List.getElem?_eq_none (by omega)]
      rfl
  rw [hbv0, hhead, hivs] at happ
  exact happ

/-! ## The flat constructor list

`minorTele` and `iotaRules` enumerate the block's constructors in the
same interleaved order; `ctorsFlat` names that order so the `q`-th minor
premise can be looked up when typing the `q`-th iota rule's right-hand
side. -/

/-- The block's constructors in declaration order, tagged with their
type's index. -/
def ctorsFlat (Θ : RecCtx) : List (Nat × CtorView) :=
  Θ.types.zipIdx.flatMap fun ti => ti.1.ctors.map fun c => (ti.2, c)

theorem minorCtorFold_eq {Θ : RecCtx} {i : Nat} :
    ∀ (cs : List CtorView) (st : Nat × List VExpr),
    cs.foldl (fun (p : Nat × List VExpr) c =>
        (p.1 + 1, p.2 ++ [minorType Θ i p.1 c])) st
      = (st.1 + cs.length,
         st.2 ++ (cs.zipIdx st.1).map fun p => minorType Θ i p.2 p.1)
  | [], st => by simp
  | c :: cs, st => by
    simp only [List.foldl_cons]
    rw [minorCtorFold_eq cs (st.1 + 1, st.2 ++ [minorType Θ i st.1 c])]
    simp [List.zipIdx_cons, List.append_assoc, Prod.ext_iff]
    omega

theorem minorTypeFold_eq {Θ : RecCtx} :
    ∀ (L : List (TypeView × Nat)) (st : Nat × List VExpr),
    L.foldl (fun (p : Nat × List VExpr) (ti : TypeView × Nat) =>
        ti.1.ctors.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p) st
      = (st.1 + (L.flatMap fun ti => ti.1.ctors.map fun c => (ti.2, c)).length,
         st.2 ++ (((L.flatMap fun ti => ti.1.ctors.map fun c => (ti.2, c)).zipIdx st.1).map
           fun p => minorType Θ p.1.1 p.2 p.1.2))
  | [], st => by simp
  | (t, i) :: L, st => by
    simp only [List.foldl_cons]
    rw [minorCtorFold_eq, minorTypeFold_eq L]
    simp only [List.flatMap_cons, List.zipIdx_append, List.map_append,
      List.length_append, List.length_map, List.append_assoc,
      List.zipIdx_map, List.map_map]
    rw [Prod.mk.injEq]
    refine ⟨by omega, ?_⟩
    congr 1

theorem minorTele_flat {Θ : RecCtx} :
    minorTele Θ = (ctorsFlat Θ).zipIdx.map fun p => minorType Θ p.1.1 p.2 p.1.2 := by
  have hMT : minorTele Θ
      = (List.foldl (fun (p : Nat × List VExpr) (ti : TypeView × Nat) =>
          List.foldl (fun p c => (p.1 + 1, p.2 ++ [minorType Θ ti.2 p.1 c])) p
            ti.1.ctors)
          (0, []) Θ.types.zipIdx).2 := rfl
  rw [hMT, minorTypeFold_eq]
  simp [ctorsFlat]

theorem minorTele_getElem? {Θ : RecCtx} {q i : Nat} {c : CtorView}
    (h : (ctorsFlat Θ)[q]? = some (i, c)) :
    (minorTele Θ)[q]? = some (minorType Θ i q c) := by
  rw [minorTele_flat, List.getElem?_map, List.getElem?_zipIdx, h]
  simp

theorem ctorsFlat_getElem {Θ : RecCtx} {q i : Nat} {c : CtorView}
    (h : (ctorsFlat Θ)[q]? = some (i, c)) :
    ∃ t, Θ.types[i]? = some t ∧ c ∈ t.ctors := by
  have hmem := List.mem_of_getElem? h
  rw [ctorsFlat] at hmem
  obtain ⟨⟨t, i'⟩, hti, hin⟩ := List.mem_flatMap.1 hmem
  obtain ⟨c', hc', heq⟩ := List.mem_map.1 hin
  obtain ⟨rfl, rfl⟩ : i' = i ∧ c' = c := by
    cases heq; exact ⟨rfl, rfl⟩
  exact ⟨t, mem_zipIdx_getElem? hti, hc'⟩

/-! ## Filling a bottom-lifted telescope

The induction-hypothesis slots of a minor premise never mention the
preceding hypotheses, only their number: as a telescope the `ρ`-th entry
is a base type lifted by `ρ` at the bottom. Filling such a telescope
requires each value at its base type, with no substitution interplay. -/

theorem instTele_liftIdx {v : VExpr} :
    ∀ {Cs : List VExpr} {off : Nat},
    instTele v ((Cs.zipIdx (off+1)).map fun p => p.1.liftN p.2) off
      = (Cs.zipIdx off).map fun p => p.1.liftN p.2
  | [], _ => rfl
  | C :: Cs, off => by
    simp only [List.zipIdx_cons, List.map_cons, instTele_cons]
    have h0 := inst_liftN_mid (j := off) (n := off) C v 0 (Nat.le_refl off)
    rw [Nat.zero_add] at h0
    rw [instTele_liftIdx (Cs := Cs), h0]

/-- Fill a telescope whose `ρ`-th entry is `Cs[ρ]` lifted by `ρ`: each
value is checked at its base type. -/
theorem fills_liftIdx : ∀ {Cs vs : List VExpr},
    (∀ (ρ : Nat) (C : VExpr), Cs[ρ]? = some C →
      ∃ v, vs[ρ]? = some v ∧ env.HasType U Γ v C) →
    vs.length = Cs.length →
    FillsTele env U Γ ((Cs.zipIdx).map fun p => p.1.liftN p.2) vs
  | [], [], _, _ => trivial
  | C :: Cs, v :: vs, H, hlen => by
    simp only [List.zipIdx_cons, List.map_cons]
    obtain ⟨v', hv', hty⟩ := H 0 C rfl
    cases (by simpa using hv' : v = v')
    refine ⟨by simpa using hty, ?_⟩
    show FillsTele env U Γ
      (instTele v ((Cs.zipIdx (0+1)).map fun p => p.1.liftN p.2)) vs
    rw [show (0:Nat)+1 = 0+1 from rfl, instTele_liftIdx]
    refine fills_liftIdx (fun ρ C' hC' => ?_) (by simpa using hlen)
    obtain ⟨w, hw, hwty⟩ := H (ρ+1) C' (by simpa using hC')
    exact ⟨w, by simpa using hw, hwty⟩
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen

/-! ## The induction-hypothesis block as a bottom-lifted telescope -/

/-- The `ρ = 0` instance of a minor premise's induction hypothesis; the
`ρ`-th entry of `minorIHs` is this lifted by `ρ`, and lifting it by
`(K - q)` over the fields turns the `q`-anchored form into the
`K`-anchored form the iota rules use. -/
def minorIH0 (Θ : RecCtx) (q : Nat) (c : CtorView)
    (r : Nat × List VExpr × Nat × List VExpr) : VExpr :=
  mkForallOF (liftTele2 (c.fields.length - r.1) (q + Θ.n) r.1 r.2.1)
    (.app (mkAppList
        (.bvar (r.2.1.length + c.fields.length + q + (Θ.n - 1 - r.2.2.1)))
        (r.2.2.2.map fun e =>
          lift2 (c.fields.length - r.1) (q + Θ.n) r.2.1.length r.1 e))
      (mkAppList (.bvar (r.2.1.length + (c.fields.length - 1 - r.1)))
        ((List.range r.2.1.length).map fun s => .bvar (r.2.1.length - 1 - s))))

theorem lift2_liftN_same {X : VExpr} {m₁ m₂ s k₂ ρ : Nat} :
    (lift2 m₁ m₂ s k₂ X).liftN ρ s = lift2 (m₁ + ρ) m₂ s k₂ X := by
  rw [lift2, lift2, VExpr.liftN'_liftN' (Nat.le_refl s) (Nat.le_add_left s m₁)]

theorem liftTele_liftTele2 : ∀ {xs : List VExpr} {ρ m₁ m₂ k₂ s : Nat},
    liftTele ρ (liftTele2 m₁ m₂ k₂ xs s) s = liftTele2 (m₁ + ρ) m₂ k₂ xs s
  | [], _, _, _, _, _ => rfl
  | A :: xs, ρ, m₁, m₂, k₂, s => by
    simp only [liftTele2, liftTele_cons]
    rw [liftTele_liftTele2 (xs := xs), lift2_liftN_same]

/-- Lifting a `ρ = 0` induction hypothesis by `ρ` produces the `ρ`-th
entry of `minorIHs`. -/
theorem minorIH0_liftN {Θ : RecCtx} {q : Nat} {c : CtorView} {pf : Nat}
    {xs : List VExpr} {it : Nat} {ris : List VExpr} {ρ : Nat} :
    (minorIH0 Θ q c (pf, xs, it, ris)).liftN ρ
      = mkForallOF (liftTele2 (ρ + (c.fields.length - pf)) (q + Θ.n) pf xs)
        (.app (mkAppList
            (.bvar (xs.length + ρ + c.fields.length + q + (Θ.n - 1 - it)))
            (ris.map fun e =>
              lift2 (ρ + (c.fields.length - pf)) (q + Θ.n) xs.length pf e))
          (mkAppList (.bvar (xs.length + ρ + (c.fields.length - 1 - pf)))
            ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s)))) := by
  rw [minorIH0, mkForallOF_liftN]
  congr 1
  · rw [liftTele_liftTele2, Nat.add_comm]
  · rw [Nat.zero_add, liftTele2_length]
    show VExpr.app _ _ = _
    congr 1
    · rw [mkAppList_liftN, List.map_map]
      congr 1
      · show VExpr.liftN ρ _ xs.length = _
        simp only [VExpr.liftN]
        rw [liftVar_le (by omega)]
        congr 1
        omega
      · refine List.map_congr_left fun e he => ?_
        show (lift2 (c.fields.length - pf) (q + Θ.n) xs.length pf e).liftN ρ
          xs.length = _
        rw [lift2_liftN_same, Nat.add_comm]
    · rw [mkAppList_liftN]
      congr 1
      · show VExpr.liftN ρ _ xs.length = _
        simp only [VExpr.liftN]
        rw [liftVar_le (by omega)]
        congr 1
        omega
      · exact liftN_varSpine_lo (Nat.le_refl _) (Nat.le_refl _)

theorem lift2_liftK {X : VExpr} {nf pf s q K n : Nat}
    (hq : q ≤ K) (hpf : pf ≤ nf) :
    (lift2 (nf - pf) (q + n) s pf X).liftN (K - q) (nf + s)
      = lift2 (nf - pf) (K + n) s pf X := by
  rw [lift2, lift2]
  have hc2 := VExpr.liftN'_comm (X.liftN (q+n) (s+pf)) (K - q) (nf - pf)
    (s + pf) s (Nat.le_add_right s pf)
  rw [show nf + s = (nf - pf) + (s + pf) by omega, ← hc2,
    VExpr.liftN'_liftN' (Nat.le_refl (s+pf)) (Nat.le_add_left (s+pf) (q+n)),
    show q + n + (K - q) = K + n by omega]

theorem liftTele2_liftK : ∀ {xs : List VExpr} {nf pf q K n s : Nat},
    q ≤ K → pf ≤ nf →
    liftTele (K - q) (liftTele2 (nf - pf) (q + n) pf xs s) (nf + s)
      = liftTele2 (nf - pf) (K + n) pf xs s
  | [], _, _, _, _, _, _, _, _ => rfl
  | A :: xs, nf, pf, q, K, n, s, hq, hpf => by
    simp only [liftTele2, liftTele_cons]
    rw [lift2_liftK hq hpf,
      show nf + s + 1 = nf + (s + 1) by omega,
      liftTele2_liftK hq hpf]

/-- Lifting the `q`-anchored base hypothesis over the fields by `K - q`
gives the `K`-anchored base hypothesis. -/
theorem minorIH0_liftK {Θ : RecCtx} {q : Nat} {c : CtorView} {pf : Nat}
    {xs : List VExpr} {it : Nat} {ris : List VExpr}
    (hq : q ≤ Θ.K) (hpf : pf < c.fields.length) :
    (minorIH0 Θ q c (pf, xs, it, ris)).liftN (Θ.K - q) c.fields.length
      = minorIH0 Θ Θ.K c (pf, xs, it, ris) := by
  rw [minorIH0, minorIH0, mkForallOF_liftN]
  congr 1
  · have hlk := liftTele2_liftK (xs := xs) (nf := c.fields.length) (pf := pf)
      (q := q) (K := Θ.K) (n := Θ.n) (s := 0) hq (Nat.le_of_lt hpf)
    rw [Nat.add_zero] at hlk
    exact hlk
  · rw [liftTele2_length]
    show VExpr.app _ _ = _
    congr 1
    · rw [mkAppList_liftN, List.map_map]
      congr 1
      · show VExpr.liftN (Θ.K - q) _ (c.fields.length + xs.length) = _
        simp only [VExpr.liftN]
        rw [liftVar_le (by omega)]
        congr 1
        omega
      · refine List.map_congr_left fun e he => ?_
        show (lift2 (c.fields.length - pf) (q + Θ.n) xs.length pf e).liftN
          (Θ.K - q) (c.fields.length + xs.length) = _
        exact lift2_liftK hq (Nat.le_of_lt hpf)
    · rw [mkAppList_liftN]
      congr 1
      · show VExpr.liftN (Θ.K - q) _ (c.fields.length + xs.length) = _
        simp only [VExpr.liftN]
        rw [liftVar_lt (by omega)]
      · exact liftN_varSpine_lo (Nat.le_refl _) (by omega)

theorem recFields_pf_lt {Θ : RecCtx} {c : CtorView} {pf it : Nat}
    {xs ris : List VExpr}
    (h : (pf, xs, it, ris) ∈ recFields Θ c) : pf < c.fields.length := by
  obtain ⟨⟨F, pf'⟩, hmem, heq⟩ := List.mem_filterMap.1 h
  obtain ⟨⟨xs', it', ris'⟩, hrec, hpe⟩ := Option.map_eq_some_iff.1 heq
  cases hpe
  have := mem_zipIdx_getElem? hmem
  exact (List.getElem?_eq_some_iff.1 this).1

/-- The lifted induction-hypothesis telescope in bottom-lift form: the
residual left for the IH values after the fields are refilled. -/
theorem liftTele_minorIHs_eq {Θ : RecCtx} {q : Nat} {c : CtorView}
    (hq : q ≤ Θ.K) :
    liftTele (Θ.K - q) (minorIHs Θ q c) c.fields.length
      = ((((recFields Θ c).map (minorIH0 Θ Θ.K c)).zipIdx).map
          fun p => p.1.liftN p.2) := by
  refine List.ext_getElem? fun ρ => ?_
  rw [getElem?_liftTele, minorIHs, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_map, List.getElem?_zipIdx, List.getElem?_map]
  cases hr : (recFields Θ c)[ρ]? with
  | none => rfl
  | some r =>
    obtain ⟨pf, xs, it, ris⟩ := r
    have hmem := List.mem_of_getElem? hr
    have hpf := recFields_pf_lt hmem
    simp only [Option.map_some, Nat.zero_add]
    congr 1
    rw [← minorIH0_liftN]
    have hc := VExpr.liftN'_comm (minorIH0 Θ q c (pf, xs, it, ris))
      (Θ.K - q) ρ c.fields.length 0 (Nat.zero_le _)
    rw [show c.fields.length + ρ = ρ + c.fields.length by omega, ← hc,
      minorIH0_liftK hq hpf]

/-! ## Evaluating the substituted minor-premise conclusion

Applying the `q`-th minor premise to the field variables and the
induction-hypothesis values computes the iota rule's declared type. The
conclusion never mentions the hypotheses, so their substitution merely
cancels a bottom lift, and the field substitution is a self-spine. -/

/-- The minor premise's conclusion with the IH-block offset stripped;
`minorConcl` is this lifted by the number of recursive fields. -/
def minorConcl0 (Θ : RecCtx) (i q : Nat) (c : CtorView) : VExpr :=
  .app (mkAppList (.bvar (c.fields.length + q + (Θ.n - 1 - i)))
      (c.rIndices.map fun e => e.liftN (q + Θ.n) c.fields.length))
    (mkAppList (.const c.name Θ.lvls)
      (((List.range Θ.np).map fun k =>
          .bvar (c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
       ((List.range c.fields.length).map fun p =>
          .bvar (c.fields.length - 1 - p))))

theorem minorConcl_eq_lift {Θ : RecCtx} {i q : Nat} {c : CtorView} :
    minorConcl Θ i q c = (minorConcl0 Θ i q c).liftN (recFields Θ c).length := by
  simp only [minorConcl, minorConcl0]
  show VExpr.app _ _ = VExpr.app _ _
  rw [mkAppList_liftN, mkAppList_liftN, List.map_map, List.map_append]
  congr 1
  · congr 1
    simp only [VExpr.liftN]
    rw [liftVar_le (Nat.zero_le _)]
    congr 1
    omega
  · congr 1
    congr 1
    · rw [liftN_varSpine (by omega)]
      exact varSpine_congr (by omega)
    · rw [List.map_map]
      refine (List.map_congr_left fun p hp => ?_).symm
      have := List.mem_range.1 hp
      show VExpr.liftN _ (VExpr.bvar _) _ = _
      simp only [VExpr.liftN]
      rw [liftVar_le (Nat.zero_le _)]

/-- Substitution below a bottom lift commutes out of it. -/
theorem instUnderK_liftN_comm : ∀ {es : List VExpr} {Z : VExpr} {R j : Nat},
    instUnderK (Z.liftN R) es (R + j) = (instUnderK Z es j).liftN R
  | [], _, _, _ => rfl
  | e :: es, Z, R, j => by
    simp only [instUnderK_cons]
    have h0 := VExpr.liftN_instN_lo R Z e (j + es.length) 0 (Nat.zero_le _)
    rw [show R + j + es.length = R + (j + es.length) by omega, ← h0,
      instUnderK_liftN_comm (es := es)]

/-- The core evaluation: the conclusion, lifted into the iota context and
applied to the field variables and any `R` values for the hypotheses,
is the iota rule's declared type body. -/
theorem instUnder_minorConclEval {Θ : RecCtx} {i q : Nat} {c : CtorView}
    {bs : List VExpr}
    (hq : q ≤ Θ.K)
    (hbs : bs.length = (recFields Θ c).length) :
    instUnder ((minorConcl Θ i q c).liftN ((Θ.K - q) + c.fields.length)
        (c.fields.length + (recFields Θ c).length))
      ((((List.range c.fields.length).map fun p =>
          VExpr.bvar (c.fields.length - 1 - p))) ++ bs)
      = .app (mkAppList (.bvar (c.fields.length + Θ.K + (Θ.n - 1 - i)))
          (c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length))
        (mkAppList (.const c.name Θ.lvls)
          (((List.range Θ.np).map fun k =>
              .bvar (c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
           ((List.range c.fields.length).map fun p =>
              .bvar (c.fields.length - 1 - p)))) := by
  rw [minorConcl_eq_lift]
  have hcomm := VExpr.liftN'_comm (minorConcl0 Θ i q c)
    ((Θ.K - q) + c.fields.length) (recFields Θ c).length
    c.fields.length 0 (Nat.zero_le _)
  rw [show c.fields.length + (recFields Θ c).length
      = (recFields Θ c).length + c.fields.length by omega, ← hcomm,
    instUnder_eq_instUnderK, instUnderK_append, hbs, Nat.zero_add]
  have hphase1 := instUnderK_liftN_comm (Z := (minorConcl0 Θ i q c).liftN
      ((Θ.K - q) + c.fields.length) c.fields.length)
    (es := (List.range c.fields.length).map fun p =>
      VExpr.bvar (c.fields.length - 1 - p))
    (R := (recFields Θ c).length) (j := 0)
  rw [Nat.add_zero] at hphase1
  rw [hphase1]
  have hcancel := instUnderK_liftN0_cancel (es := bs)
    (x := instUnderK ((minorConcl0 Θ i q c).liftN
      ((Θ.K - q) + c.fields.length) c.fields.length)
      ((List.range c.fields.length).map fun p =>
        VExpr.bvar (c.fields.length - 1 - p)) 0)
    (k := 0)
  rw [Nat.zero_add, hbs] at hcancel
  rw [hcancel, VExpr.liftN_zero]
  -- evaluate the single field-spine substitution
  rw [minorConcl0]
  show instUnderK (VExpr.app _ _) _ 0 = _
  rw [instUnderK_app]
  congr 1
  · rw [show (mkAppList (VExpr.bvar (c.fields.length + q + (Θ.n - 1 - i)))
          (c.rIndices.map fun e => e.liftN (q + Θ.n) c.fields.length)).liftN
            ((Θ.K - q) + c.fields.length) c.fields.length
          = mkAppList ((VExpr.bvar (c.fields.length + q + (Θ.n - 1 - i))).liftN
              ((Θ.K - q) + c.fields.length) c.fields.length)
            ((c.rIndices.map fun e => e.liftN (q + Θ.n) c.fields.length).map
              (VExpr.liftN ((Θ.K - q) + c.fields.length) · c.fields.length))
          from mkAppList_liftN, instUnderK_mkAppList]
    congr 1
    · show instUnderK (VExpr.liftN _ (.bvar _) _) _ 0 = _
      simp only [VExpr.liftN]
      rw [liftVar_le (by omega)]
      rw [instUnderK_bvar_ge (by simp; omega)]
      congr 1
      simp
      omega
    · rw [List.map_map, List.map_map]
      refine List.map_congr_left fun e he => ?_
      show instUnderK ((e.liftN (q + Θ.n) c.fields.length).liftN
        ((Θ.K - q) + c.fields.length) c.fields.length) _ 0 = _
      rw [VExpr.liftN'_liftN' (Nat.le_refl _)
          (Nat.le_add_left c.fields.length (q + Θ.n)),
        show q + Θ.n + ((Θ.K - q) + c.fields.length)
          = c.fields.length + (Θ.K + Θ.n) by omega,
        ← instUnder_eq_instUnderK, instUnder_selfSpine]
  · rw [show (mkAppList (VExpr.const c.name Θ.lvls)
        (((List.range Θ.np).map fun k =>
            VExpr.bvar (c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
         ((List.range c.fields.length).map fun p =>
            VExpr.bvar (c.fields.length - 1 - p)))).liftN
          ((Θ.K - q) + c.fields.length) c.fields.length
        = mkAppList (VExpr.const c.name Θ.lvls)
          ((((List.range Θ.np).map fun k =>
              VExpr.bvar (c.fields.length + q + Θ.n + Θ.np - 1 - k)) ++
           ((List.range c.fields.length).map fun p =>
              VExpr.bvar (c.fields.length - 1 - p))).map
            (VExpr.liftN ((Θ.K - q) + c.fields.length) · c.fields.length))
        from mkAppList_liftN, List.map_append, instUnderK_mkAppList,
      instUnderK_const, List.map_append]
    congr 1
    congr 1
    · rw [liftN_varSpine (by omega), List.map_map]
      refine List.map_congr_left fun k hk => ?_
      have hkP := List.mem_range.1 hk
      show instUnderK (.bvar ((Θ.K - q) + c.fields.length +
        (c.fields.length + q + Θ.n + Θ.np) - 1 - k)) _ 0 = _
      rw [instUnderK_bvar_ge (by simp; omega)]
      congr 1
      simp
      omega
    · rw [liftN_varSpine_lo (Nat.le_refl _) (Nat.le_refl _), List.map_map]
      refine List.map_congr_left fun p hp => ?_
      have hpP := List.mem_range.1 hp
      show instUnderK (.bvar (c.fields.length - 1 - p)) _ 0 = _
      have hidx : (((List.range c.fields.length).map fun p =>
          VExpr.bvar (c.fields.length - 1 - p)))[p]?
          = some (VExpr.bvar (c.fields.length - 1 - p)) := by
        rw [List.getElem?_map, List.getElem?_range hpP]
        rfl
      have h0 := instUnderK_spine_bvar (k := 0) hidx
      rw [Nat.zero_add, VExpr.liftN_zero,
        show (((List.range c.fields.length).map fun p =>
          VExpr.bvar (c.fields.length - 1 - p))).length = c.fields.length
          by simp] at h0
      exact h0

/-! ## Typing the induction-hypothesis values -/

/-- Each IH value of an iota rule — the lambda-abstracted recursive call —
has the corresponding (K-anchored) induction-hypothesis type. -/
theorem ihVal_hasType {envC envR : VEnv} {Θ : RecCtx} {pf it : Nat}
    {t t' : TypeView} {c : CtorView} {xs ris Ms : List VExpr} {T : VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) (hle : envC ≤ envR)
    (htm : t ∈ Θ.types) (hcm : c ∈ t.ctors)
    (hmem : (pf, xs, it, ris) ∈ recFields Θ c)
    (ht' : Θ.types[it]? = some t')
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hK : ((minorTele Θ).reverse).length = Θ.K)
    (hTt : recType Θ it = some T)
    (hconst : envR.constants (Lean.mkRecName t'.name) = some ⟨Θ.recUvars, T⟩)
    (hTwf : envR.IsType Θ.recUvars [] T) :
    envR.HasType Θ.recUvars
      ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
      (mkLamOF (liftTele2 (c.fields.length - pf) (Θ.K + Θ.n) pf xs)
        (mkAppList (.const (Lean.mkRecName t'.name) (VLevel.params Θ.recUvars))
          (((List.range Θ.np).map fun k =>
              VExpr.bvar (xs.length +
                (c.fields.length + Θ.K + Θ.n + Θ.np) - 1 - k)) ++
            ((List.range Θ.n).map fun j =>
              VExpr.bvar (xs.length + c.fields.length + Θ.K + (Θ.n - 1 - j))) ++
            ((List.range Θ.K).map fun p =>
              VExpr.bvar (xs.length + c.fields.length + (Θ.K - 1 - p))) ++
            (ris.map fun e =>
              lift2 (c.fields.length - pf) (Θ.K + Θ.n) xs.length pf e) ++
            [mkAppList (.bvar (xs.length + (c.fields.length - 1 - pf)))
              ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s))])))
      (minorIH0 Θ Θ.K c (pf, xs, it, ris)) := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  have hpf := recFields_pf_lt hmem
  have hitn : it < Θ.n := by
    have := recFields_it_lt hmem
    rw [h.names_len, ← h.n_eq] at this
    exact this
  -- the abstracted argument telescope
  have hTele0 := recField_tele_deep (t := t) (ρ := 0) (q := Θ.K)
    (Γρ := ([] : List VExpr)) (Ns := (minorTele Θ).reverse)
    henv h htm hcm hmem (Nat.le_of_lt hpf) hMsLen hK rfl
  simp only [Nat.zero_add, List.nil_append] at hTele0
  have hTele := hTele0.mono hle
  -- the recursive-call body via the recursor application
  have hfill0 := recField_fill_deep (ρ := 0) (q := Θ.K)
    (Γρ := ([] : List VExpr)) (Ns := (minorTele Θ).reverse)
    henv h htm hcm hmem ht' (Nat.le_of_lt hpf) hMsLen hK rfl
  simp only [Nat.zero_add, Nat.add_zero, List.nil_append] at hfill0
  have ha0 := recFieldApp_hasType (ρ := 0) (q := Θ.K)
    (Γρ := ([] : List VExpr)) (Ns := (minorTele Θ).reverse)
    henv h htm hcm hmem ht' hMsLen hK rfl
  simp only [Nat.zero_add, Nat.add_zero, List.nil_append] at ha0
  have happ := recApp_hasType (X := xs.length) (i := it) (t := t') (c := c)
    (ΓX := (liftTele2 (c.fields.length - pf) (Θ.K + Θ.n) pf xs).reverse)
    (is := ris.map fun e =>
      lift2 (c.fields.length - pf) (Θ.K + Θ.n) xs.length pf e)
    (a := mkAppList (.bvar (xs.length + (c.fields.length - 1 - pf)))
      ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s)))
    henv h hle ht' hMs (by simp) hTt hconst hTwf
    (by
      refine Eq.mp ?_ (hfill0.mono hle)
      congr 1
      rw [liftTele_liftTele,
        show xs.length + c.fields.length + Θ.K + Θ.n
          = Θ.K + Θ.n + (xs.length + c.fields.length) by omega])
    (ha0.mono hle)
  -- massage the applied spines into the iota literals
  have hpv : ((List.range Θ.np).map fun k =>
      VExpr.bvar (xs.length + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k))
      = (List.range Θ.np).map fun k =>
        VExpr.bvar (xs.length + (c.fields.length + Θ.K + Θ.n + Θ.np) - 1 - k) :=
    varSpine_congr (by omega)
  have hmv : ((List.range Θ.n).map fun j =>
      VExpr.bvar (xs.length + c.fields.length + Θ.K + Θ.n - 1 - j))
      = (List.range Θ.n).map fun j =>
        VExpr.bvar (xs.length + c.fields.length + Θ.K + (Θ.n - 1 - j)) :=
    List.map_congr_left fun j hj => by
      have := List.mem_range.1 hj; congr 1; omega
  have hmiv : ((List.range Θ.K).map fun p =>
      VExpr.bvar (xs.length + c.fields.length + Θ.K - 1 - p))
      = (List.range Θ.K).map fun p =>
        VExpr.bvar (xs.length + c.fields.length + (Θ.K - 1 - p)) :=
    List.map_congr_left fun p hp => by
      have := List.mem_range.1 hp; congr 1; omega
  have hhd : (VExpr.bvar (xs.length + c.fields.length + Θ.K + Θ.n - 1 - it))
      = .bvar (xs.length + c.fields.length + Θ.K + (Θ.n - 1 - it)) := by
    congr 1; omega
  rw [hpv, hmv, hmiv, hhd] at happ
  show envR.HasType Θ.recUvars _ _ (mkForallOF
    (liftTele2 (c.fields.length - pf) (Θ.K + Θ.n) pf xs) _)
  exact TeleWF.mkLamOF_hasType hTele happ

/-- `mapM` with a choice of witnesses: if every element maps to `some`
value satisfying a position-indexed property, the whole `mapM` succeeds
and the results satisfy it. -/
theorem mapM_choose {α β} {f : α → Option β} {P : Nat → β → Prop} :
    ∀ {l : List α},
    (∀ (ρ : Nat) a, l[ρ]? = some a → ∃ b, f a = some b ∧ P ρ b) →
    ∃ bs, l.mapM f = some bs ∧ bs.length = l.length ∧
      ∀ (ρ : Nat) b, bs[ρ]? = some b → P ρ b
  | [], _ => ⟨[], rfl, rfl, fun ρ b h => by simp at h⟩
  | a :: l, H => by
    obtain ⟨b, hb, hP⟩ := H 0 a rfl
    obtain ⟨bs, hbs, hlen, hPs⟩ :=
      mapM_choose (l := l) (P := fun ρ => P (ρ+1))
        (fun ρ a' h' => H (ρ+1) a' (by simpa using h'))
    refine ⟨b :: bs, ?_, by simp [hlen], fun ρ b' hb' => ?_⟩
    · rw [List.mapM_cons, hb, hbs]
      rfl
    · cases ρ with
      | zero => cases (by simpa using hb' : b = b'); exact hP
      | succ ρ => exact hPs ρ b' (by simpa using hb')

/-- One iota rule is well-formed: given the block's data, the `q`-th
constructor's rule elaborates and both sides have the declared type. -/
theorem iotaRule_wf {envC envR : VEnv} {Θ : RecCtx} {q i : Nat}
    {t : TypeView} {c : CtorView} {Ms : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) (hle : envC ≤ envR)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hqpos : (ctorsFlat Θ)[q]? = some (i, c))
    (ht : Θ.types[i]? = some t) (hcm : c ∈ t.ctors)
    (hrec : ∀ (i' : Nat) (t'' : TypeView), Θ.types[i']? = some t'' →
      ∃ T, recType Θ i' = some T ∧
        envR.constants (Lean.mkRecName t''.name) = some ⟨Θ.recUvars, T⟩) :
    ∃ df, iotaRule Θ i q c Ms (minorTele Θ) = some df ∧ VDefEq.WF envR df := by
  have hMsLen : Ms.length = Θ.n := by simpa using mapM_length hMs
  obtain ⟨hMWF, hMlen⟩ := minorTele_wf henv h hMs
  have hK : ((minorTele Θ).reverse).length = Θ.K := by simpa using hMlen
  have hMsWF : TeleWF envC Θ.recUvars Θ.params.reverse Ms := by
    obtain ⟨Ms', hMs0', hWF⟩ := motiveTele_wf henv h Θ.n 0 (by rw [← h.n_eq]; omega)
    rw [← List.range_eq_range'] at hMs0'
    cases hMs.symm.trans hMs0'
    simpa using hWF [] rfl
  have htm : t ∈ Θ.types := by
    have ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 ht
    exact he ▸ List.getElem_mem hlt
  have hin : i < Θ.n := by
    rw [h.n_eq]; exact (List.getElem?_eq_some_iff.1 ht).1
  have hqK : q < Θ.K := by
    have h1 : q < (ctorsFlat Θ).length := (List.getElem?_eq_some_iff.1 hqpos).1
    have h2 : (minorTele Θ).length = (ctorsFlat Θ).length := by
      rw [minorTele_flat]; simp
    omega
  have hnmi := h.names_eq i t ht
  -- the induction-hypothesis values
  obtain ⟨bs, hbsEq, hbsLen, hbsP⟩ := mapM_choose
    (l := recFields Θ c)
    (f := fun r =>
      match r with
      | (pf, xs, it, ris) => do
        let nx := xs.length
        let xs' := liftTele2 (c.fields.length - pf) (Θ.K + Θ.n) pf xs
        let ris' := ris.map fun e =>
          lift2 (c.fields.length - pf) (Θ.K + Θ.n) nx pf e
        let pv := (List.range Θ.np).map fun k =>
          VExpr.bvar (nx + (c.fields.length + Θ.K + Θ.n + Θ.np) - 1 - k)
        let mv := (List.range Θ.n).map fun j =>
          VExpr.bvar (nx + c.fields.length + Θ.K + (Θ.n - 1 - j))
        let miv := (List.range Θ.K).map fun p =>
          VExpr.bvar (nx + c.fields.length + (Θ.K - 1 - p))
        let fvar := VExpr.bvar (nx + (c.fields.length - 1 - pf))
        let recNameIt ← Θ.names[it]?
        return mkLamOF xs' (mkAppList
          (.const (Lean.mkRecName recNameIt) (VLevel.params Θ.recUvars))
          (pv ++ mv ++ miv ++ ris' ++
            [mkAppList fvar ((List.range nx).map fun s => .bvar (nx - 1 - s))])))
    (P := fun ρ b => ∀ r, (recFields Θ c)[ρ]? = some r →
      envR.HasType Θ.recUvars
        ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
          ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
        b (minorIH0 Θ Θ.K c r))
    (by
      rintro ρ ⟨pf, xs, it, ris⟩ hρ
      have hmem := List.mem_of_getElem? hρ
      have hitn : it < Θ.n := by
        have := recFields_it_lt hmem
        rw [h.names_len, ← h.n_eq] at this
        exact this
      obtain ⟨t', ht'⟩ : ∃ t', Θ.types[it]? = some t' :=
        ⟨_, List.getElem?_eq_getElem (by rw [← h.n_eq]; exact hitn)⟩
      have hnmit := h.names_eq it t' ht'
      obtain ⟨T, hTt, hconst⟩ := hrec it t' ht'
      have hTwf : envR.IsType Θ.recUvars [] T := by
        obtain ⟨T', hT', hTy'⟩ := recType_isType henv h ht'
        rw [hTt] at hT'
        cases hT'
        exact hTy'.mono hle
      refine ⟨mkLamOF (liftTele2 (c.fields.length - pf) (Θ.K + Θ.n) pf xs)
        (mkAppList (.const (Lean.mkRecName t'.name) (VLevel.params Θ.recUvars))
          (((List.range Θ.np).map fun k =>
              VExpr.bvar (xs.length +
                (c.fields.length + Θ.K + Θ.n + Θ.np) - 1 - k)) ++
            ((List.range Θ.n).map fun j =>
              VExpr.bvar (xs.length + c.fields.length + Θ.K + (Θ.n - 1 - j))) ++
            ((List.range Θ.K).map fun p =>
              VExpr.bvar (xs.length + c.fields.length + (Θ.K - 1 - p))) ++
            (ris.map fun e =>
              lift2 (c.fields.length - pf) (Θ.K + Θ.n) xs.length pf e) ++
            [mkAppList (.bvar (xs.length + (c.fields.length - 1 - pf)))
              ((List.range xs.length).map fun s => .bvar (xs.length - 1 - s))])),
        ?_, fun r' hr' => ?_⟩
      · show (Θ.names[it]? >>= _) = some _
        rw [hnmit]
        rfl
      · cases (by rw [hρ] at hr'; exact (Option.some_inj.1 hr').symm :
          r' = (pf, xs, it, ris))
        exact ihVal_hasType henv h hle htm hcm hmem ht' hMs hK hTt hconst hTwf)
  -- data for the recursor application on the left-hand side
  obtain ⟨T, hTt, hconst⟩ := hrec i t ht
  have hTwf : envR.IsType Θ.recUvars [] T := by
    obtain ⟨T', hT', hTy'⟩ := recType_isType henv h ht
    rw [hTt] at hT'
    cases hT'
    exact hTy'.mono hle
  have hfillL : FillsTele envR Θ.recUvars
      (([] : List VExpr) ++ ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse))))
      (liftTele (0 + c.fields.length) (liftTele (Θ.K + Θ.n) t.indices))
      (c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length) := by
    have hfL0 := h.rIndices_fill i t ht c hcm
    have W0K : Ctx.LiftN (Θ.K + Θ.n) 0 Θ.params.reverse
        (((minorTele Θ).reverse ++ Ms.reverse) ++ Θ.params.reverse) :=
      .zero ((minorTele Θ).reverse ++ Ms.reverse) (by simp [hMlen, hMsLen])
    have h1 := FillsTele.weakN henv (ctxLiftN_teleBlock W0K (Δ := c.fields)) hfL0
    simp only [Nat.zero_add] at h1
    rw [show liftTele (Θ.K + Θ.n) (liftTele c.fields.length t.indices)
          c.fields.length
        = liftTele (c.fields.length + (Θ.K + Θ.n)) t.indices from by
      have := liftTele_liftTele_hi (Δ := t.indices) (n₁ := c.fields.length)
        (n₂ := Θ.K + Θ.n) (k := 0)
      simpa using this] at h1
    refine Eq.mp ?_ (h1.mono hle)
    congr 1
    · simp [List.append_assoc]
    · rw [Nat.zero_add, liftTele_liftTele]
      congr 1
      omega
  have haL := ctorApp_hasType (R := 0) (ΓR := ([] : List VExpr)) (q := Θ.K)
    (Ns := (minorTele Θ).reverse) (Ms := Ms)
    henv h ht hcm hMsLen hK rfl
  rw [show (c.rIndices.map fun e =>
      VExpr.liftN 0 (VExpr.liftN (Θ.K + Θ.n) e c.fields.length))
      = c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length from
    List.map_congr_left fun e he => VExpr.liftN_zero _ _] at haL
  have happL := recApp_hasType (X := 0) (ΓX := ([] : List VExpr))
    (i := i) (t := t) (c := c)
    (is := c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length)
    (a := mkAppList (.const c.name Θ.lvls)
      (((List.range Θ.np).map fun k =>
          .bvar (0 + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
       ((List.range c.fields.length).map fun p =>
          .bvar (0 + (c.fields.length - 1 - p)))))
    henv h hle ht hMs rfl hTt hconst hTwf hfillL (haL.mono hle)
  simp only [List.nil_append] at happL
  -- massage the left-hand side into the iota literals (X = 0)
  have hpvL : ((List.range Θ.np).map fun k =>
      VExpr.bvar (0 + c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k))
      = (List.range Θ.np).map fun k =>
        VExpr.bvar (c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k) :=
    varSpine_congr (by omega)
  have hmvL : ((List.range Θ.n).map fun j =>
      VExpr.bvar (0 + c.fields.length + Θ.K + Θ.n - 1 - j))
      = (List.range Θ.n).map fun j =>
        VExpr.bvar (c.fields.length + Θ.K + (Θ.n - 1 - j)) :=
    List.map_congr_left fun j hj => by
      have := List.mem_range.1 hj; congr 1; omega
  have hmivL : ((List.range Θ.K).map fun p =>
      VExpr.bvar (0 + c.fields.length + Θ.K - 1 - p))
      = (List.range Θ.K).map fun p =>
        VExpr.bvar (c.fields.length + (Θ.K - 1 - p)) :=
    List.map_congr_left fun p hp => by
      have := List.mem_range.1 hp; congr 1; omega
  have hfvL : ((List.range c.fields.length).map fun p =>
      VExpr.bvar (0 + (c.fields.length - 1 - p)))
      = (List.range c.fields.length).map fun p =>
        VExpr.bvar (c.fields.length - 1 - p) :=
    List.map_congr_left fun p hp => by rw [Nat.zero_add]
  have hhdL : (VExpr.bvar (0 + c.fields.length + Θ.K + Θ.n - 1 - i))
      = .bvar (c.fields.length + Θ.K + (Θ.n - 1 - i)) := by
    congr 1; omega
  rw [hpvL, hmvL, hmivL, hfvL, hhdL] at happL
  -- the right-hand side: the q-th minor premise applied to the fields and
  -- the induction-hypothesis values
  have hminQ := minorTele_getElem? hqpos
  have hlkQ := lookup_midBlock (Γtop := (liftTele (Θ.K + Θ.n) c.fields).reverse)
    (Γrest := Ms.reverse ++ Θ.params.reverse) hminQ
  rw [VExpr.liftN_liftN,
    show ((liftTele (Θ.K + Θ.n) c.fields).reverse).length = c.fields.length by
      simp,
    hMlen] at hlkQ
  rw [show minorType Θ i q c = mkForallOF (liftTele (q + Θ.n) c.fields)
      (mkForallOF (minorIHs Θ q c) (minorConcl Θ i q c)) from rfl,
    mkForallOF_liftN, mkForallOF_liftN] at hlkQ
  simp only [Nat.zero_add, liftTele_length, minorIHs_length] at hlkQ
  rw [← mkForallOF_append,
    show Θ.K - q + c.fields.length = (Θ.K - q) + c.fields.length from rfl] at hlkQ
  have hbvQ := VEnv.IsDefEq.bvar (env := envR) (uvars := Θ.recUvars) hlkQ
  -- the field variables refill the (doubly lifted) field telescope
  have hFf : FillsTele envR Θ.recUvars
      ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
      (liftTele (Θ.K - q + c.fields.length) (liftTele (q + Θ.n) c.fields))
      ((List.range c.fields.length).map fun p =>
        .bvar (c.fields.length - 1 - p)) := by
    rw [show liftTele (Θ.K - q + c.fields.length) (liftTele (q + Θ.n) c.fields)
        = liftTele c.fields.length (liftTele (Θ.K + Θ.n) c.fields) from by
      rw [liftTele_liftTele, liftTele_liftTele]
      congr 1
      omega]
    refine fills_varSpine2 (a := Θ.K + Θ.n) (b := c.fields.length) (t := 0)
      (by omega) (fun p A hA => ?_)
    have hp : p < c.fields.length := (List.getElem?_eq_some_iff.1 hA).1
    have hA' : (liftTele (Θ.K + Θ.n) c.fields)[p]?
        = some (A.liftN (Θ.K + Θ.n) p) := by
      rw [getElem?_liftTele, hA]; simp
    have hlk := lookup_topBlock
      (Γrest := (minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)) hA'
    rw [liftTele_length] at hlk
    rw [Nat.zero_add]
    exact hlk
  -- the IH values fill the residual telescope
  have hresIH : instTeleUnder
      (liftTele (Θ.K - q + c.fields.length) (minorIHs Θ q c) c.fields.length)
      ((List.range c.fields.length).map fun p =>
        VExpr.bvar (c.fields.length - 1 - p))
      = liftTele (Θ.K - q) (minorIHs Θ q c) c.fields.length := by
    rw [show liftTele (Θ.K - q + c.fields.length) (minorIHs Θ q c) c.fields.length
        = liftTele c.fields.length
          (liftTele (Θ.K - q) (minorIHs Θ q c) c.fields.length)
          c.fields.length from by rw [liftTele_liftTele]]
    rw [instTeleUnder_eq]
    have hbs2 := instTeleUnderK_blockSpine
      (Δ := liftTele (Θ.K - q) (minorIHs Θ q c) c.fields.length)
      (p := c.fields.length) (m := 0) (k := 0)
    simp only [Nat.zero_add] at hbs2
    rw [hbs2, liftTele_zero]
  have hFih : FillsTele envR Θ.recUvars
      ((liftTele (Θ.K + Θ.n) c.fields).reverse ++
        ((minorTele Θ).reverse ++ (Ms.reverse ++ Θ.params.reverse)))
      (instTeleUnder
        (liftTele (Θ.K - q + c.fields.length) (minorIHs Θ q c) c.fields.length)
        ((List.range c.fields.length).map fun p =>
          VExpr.bvar (c.fields.length - 1 - p)))
      bs := by
    rw [hresIH, liftTele_minorIHs_eq (Nat.le_of_lt hqK)]
    refine fills_liftIdx (fun ρ C hC => ?_) (by simp [hbsLen])
    rw [List.getElem?_map] at hC
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hC
    obtain ⟨b, hb⟩ : ∃ b, bs[ρ]? = some b := by
      have hρlt : ρ < (recFields Θ c).length := (List.getElem?_eq_some_iff.1 hr).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨b, hb, hbsP ρ b hb r hr⟩
  have happR := (hFf.append hFih).appList hbvQ
  rw [instUnder_minorConclEval (Nat.le_of_lt hqK) hbsLen] at happR
  -- the rule elaborates, and both sides are typed at its declared type
  refine ⟨⟨Θ.recUvars,
    mkLamOF Θ.params (mkLamOF Ms (mkLamOF (minorTele Θ)
      (mkLamOF (liftTele (Θ.K + Θ.n) c.fields)
        (mkAppList (.const (Lean.mkRecName t.name) (VLevel.params Θ.recUvars))
          (((List.range Θ.np).map fun k =>
              VExpr.bvar (c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
            ((List.range Θ.n).map fun j =>
              VExpr.bvar (c.fields.length + Θ.K + (Θ.n - 1 - j))) ++
            ((List.range Θ.K).map fun p =>
              VExpr.bvar (c.fields.length + (Θ.K - 1 - p))) ++
            (c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length) ++
            [mkAppList (.const c.name Θ.lvls)
              (((List.range Θ.np).map fun k =>
                  VExpr.bvar (c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
                ((List.range c.fields.length).map fun p =>
                  VExpr.bvar (c.fields.length - 1 - p)))]))))),
    mkLamOF Θ.params (mkLamOF Ms (mkLamOF (minorTele Θ)
      (mkLamOF (liftTele (Θ.K + Θ.n) c.fields)
        (mkAppList (.bvar (c.fields.length + (Θ.K - 1 - q)))
          (((List.range c.fields.length).map fun p =>
              VExpr.bvar (c.fields.length - 1 - p)) ++ bs))))),
    mkForallOF Θ.params (mkForallOF Ms (mkForallOF (minorTele Θ)
      (mkForallOF (liftTele (Θ.K + Θ.n) c.fields)
        (.app (mkAppList (.bvar (c.fields.length + Θ.K + (Θ.n - 1 - i)))
            (c.rIndices.map fun e => e.liftN (Θ.K + Θ.n) c.fields.length))
          (mkAppList (.const c.name Θ.lvls)
            (((List.range Θ.np).map fun k =>
                VExpr.bvar (c.fields.length + Θ.K + Θ.n + Θ.np - 1 - k)) ++
              ((List.range c.fields.length).map fun p =>
                VExpr.bvar (c.fields.length - 1 - p))))))))⟩,
    ?_, ?_, ?_⟩
  · show (Θ.names[i]? >>= _) = some _
    rw [hnmi]
    show ((recFields Θ c).mapM _ >>= _) = some _
    rw [hbsEq]
    rfl
  · -- the left-hand side
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle h.params_wf) ?_
    rw [List.append_nil]
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle hMsWF) ?_
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle hMWF) ?_
    refine TeleWF.mkLamOF_hasType ?_ ?_
    · have W0K : Ctx.LiftN (Θ.K + Θ.n) 0 Θ.params.reverse
          (((minorTele Θ).reverse ++ Ms.reverse) ++ Θ.params.reverse) :=
        .zero ((minorTele Θ).reverse ++ Ms.reverse) (by simp [hMlen, hMsLen])
      have := TeleWF.weakN henv W0K (h.fields_wf t htm c hcm)
      refine TeleWF.mono hle (Eq.mp ?_ this)
      congr 1
      simp [List.append_assoc]
    · exact happL
  · -- the right-hand side
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle h.params_wf) ?_
    rw [List.append_nil]
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle hMsWF) ?_
    refine TeleWF.mkLamOF_hasType (TeleWF.mono hle hMWF) ?_
    refine TeleWF.mkLamOF_hasType ?_ ?_
    · have W0K : Ctx.LiftN (Θ.K + Θ.n) 0 Θ.params.reverse
          (((minorTele Θ).reverse ++ Ms.reverse) ++ Θ.params.reverse) :=
        .zero ((minorTele Θ).reverse ++ Ms.reverse) (by simp [hMlen, hMsLen])
      have := TeleWF.weakN henv W0K (h.fields_wf t htm c hcm)
      refine TeleWF.mono hle (Eq.mp ?_ this)
      congr 1
      simp [List.append_assoc]
    · exact happR

/-- The constructor-level fold of `iotaRules`: every rule in one type's
block elaborates and is well-formed, threading the flat position. -/
theorem iotaCtorFoldM_wf {envC envR : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    {t : TypeView} {i : Nat}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) (hle : envC ≤ envR)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (ht : Θ.types[i]? = some t)
    (hrec : ∀ (i' : Nat) (t'' : TypeView), Θ.types[i']? = some t'' →
      ∃ T, recType Θ i' = some T ∧
        envR.constants (Lean.mkRecName t''.name) = some ⟨Θ.recUvars, T⟩) :
    ∀ (cs : List CtorView) (st : Nat × List VDefEq),
    (∀ c' ∈ cs, c' ∈ t.ctors) →
    (∀ (ρ : Nat) c', cs[ρ]? = some c' → (ctorsFlat Θ)[st.1 + ρ]? = some (i, c')) →
    (∀ df ∈ st.2, VDefEq.WF envR df) →
    ∃ st', (cs.foldlM (fun (p : Nat × List VDefEq) c => do
        let df ← iotaRule Θ i p.1 c Ms (minorTele Θ)
        return (p.1 + 1, p.2 ++ [df])) st) = some st' ∧
      st'.1 = st.1 + cs.length ∧ (∀ df ∈ st'.2, VDefEq.WF envR df)
  | [], st, _, _, hWF => ⟨st, rfl, by simp, hWF⟩
  | c :: cs, st, hmem, hflat, hWF => by
    obtain ⟨df, hdf, hdfWF⟩ := iotaRule_wf henv h hle hMs
      (by simpa using hflat 0 c rfl) ht (hmem c (.head _)) hrec
    obtain ⟨st', hst', hlen', hWF'⟩ := iotaCtorFoldM_wf henv h hle hMs ht hrec
      cs (st.1 + 1, st.2 ++ [df])
      (fun c' hc' => hmem c' (.tail _ hc'))
      (fun ρ c' hc' => by
        have := hflat (ρ + 1) c' (by simpa using hc')
        rwa [show st.1 + (ρ + 1) = st.1 + 1 + ρ by omega] at this)
      (fun df' hdf' => by
        rcases List.mem_append.1 hdf' with h' | h'
        · exact hWF df' h'
        · cases (by simpa using h' : df' = df); exact hdfWF)
    refine ⟨st', ?_, by rw [hlen']; simp; omega, hWF'⟩
    rw [List.foldlM_cons]
    show ((iotaRule Θ i st.1 c Ms (minorTele Θ) >>= _) >>= _) = some st'
    rw [hdf]
    exact hst'

/-- The type-level fold of `iotaRules`. -/
theorem iotaTypeFoldM_wf {envC envR : VEnv} {Θ : RecCtx} {Ms : List VExpr}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ) (hle : envC ≤ envR)
    (hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms)
    (hrec : ∀ (i' : Nat) (t'' : TypeView), Θ.types[i']? = some t'' →
      ∃ T, recType Θ i' = some T ∧
        envR.constants (Lean.mkRecName t''.name) = some ⟨Θ.recUvars, T⟩) :
    ∀ (L : List (TypeView × Nat)) (st : Nat × List VDefEq),
    (∀ p ∈ L, Θ.types[p.2]? = some p.1) →
    (∀ (ρ : Nat) ic,
      (L.flatMap fun ti => ti.1.ctors.map fun c' => (ti.2, c'))[ρ]? = some ic →
      (ctorsFlat Θ)[st.1 + ρ]? = some ic) →
    (∀ df ∈ st.2, VDefEq.WF envR df) →
    ∃ st', (L.foldlM (fun (p : Nat × List VDefEq) (ti : TypeView × Nat) =>
        ti.1.ctors.foldlM (fun (p : Nat × List VDefEq) c => do
          let df ← iotaRule Θ ti.2 p.1 c Ms (minorTele Θ)
          return (p.1 + 1, p.2 ++ [df])) p) st) = some st' ∧
      (∀ df ∈ st'.2, VDefEq.WF envR df)
  | [], st, _, _, hWF => ⟨st, rfl, hWF⟩
  | (t, i) :: L, st, hL, hflat, hWF => by
    obtain ⟨st1, hst1, hlen1, hWF1⟩ := iotaCtorFoldM_wf henv h hle hMs
      (hL (t, i) (.head _)) hrec t.ctors st (fun c' hc' => hc')
      (fun ρ c' hc' => hflat ρ (i, c') (by
        rw [List.flatMap_cons, List.getElem?_append_left
            (by simp; exact (List.getElem?_eq_some_iff.1 hc').1),
          List.getElem?_map, hc']
        rfl))
      hWF
    obtain ⟨st', hst', hWF'⟩ := iotaTypeFoldM_wf henv h hle hMs hrec L st1
      (fun p hp => hL p (.tail _ hp))
      (fun ρ ic hic => by
        have := hflat (t.ctors.length + ρ) ic (by
          rw [List.flatMap_cons, List.getElem?_append_right (by simp)]
          simpa using hic)
        rwa [show st.1 + (t.ctors.length + ρ) = st1.1 + ρ by omega] at this)
      hWF1
    refine ⟨st', ?_, hWF'⟩
    rw [List.foldlM_cons]
    show (t.ctors.foldlM _ _ >>= _) = some st'
    rw [hst1]
    exact hst'

/-- Every constructed iota rule is a well-formed defeq in an environment
that also contains the recursor constants at their constructed types. -/
theorem iotaRules_wf {envC envR : VEnv} {Θ : RecCtx}
    (henv : VEnv.Ordered envC) (h : RecCtxWF envC Θ)
    (hle : envC ≤ envR)
    (hrec : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
      ∃ T, recType Θ i = some T ∧
        envR.constants (Lean.mkRecName t.name) = some ⟨Θ.recUvars, T⟩) :
    ∃ rules, iotaRules Θ = some rules ∧ ∀ df ∈ rules, VDefEq.WF envR df := by
  obtain ⟨Ms, hMs0, -⟩ := motiveTele_wf henv h Θ.n 0 (by rw [← h.n_eq]; omega)
  have hMs : (List.range Θ.n).mapM (motiveType Θ) = some Ms := by
    rwa [List.range_eq_range']
  obtain ⟨st', hst', hWF'⟩ := iotaTypeFoldM_wf henv h hle hMs hrec
    Θ.types.zipIdx (0, [])
    (fun p hp => mem_zipIdx_getElem? hp)
    (fun ρ ic hic => by
      rw [show (ctorsFlat Θ) = Θ.types.zipIdx.flatMap fun ti =>
          ti.1.ctors.map fun c' => (ti.2, c') from rfl, Nat.zero_add]
      exact hic)
    (fun df hdf => by simp at hdf)
  refine ⟨st'.2, ?_, hWF'⟩
  rw [iotaRules]
  show ((List.range Θ.n).mapM (motiveType Θ) >>= _) = some _
  rw [hMs]
  show (Θ.types.zipIdx.foldlM _ _ <&> _) = some _
  rw [hst']
  rfl

/-- Preserve `Ordered` given declared-type typing, constructor typing, and
the explicit `RecCtxWF` bundle at the constructed environment. For the version
using the three specification predicates, see `addInductCore_WF4`. -/
theorem addInductCore_WF {env env' : VEnv} {decl : VInductDecl} {largeElim : Bool}
    (henv : VEnv.Ordered env)
    (hty : ∀ t ∈ decl.types, env.IsType decl.uvars [] t.type)
    (hctor : ∀ {envI}, addTypeConsts env decl = some envI →
      ∀ t ∈ decl.types, ∀ c ∈ t.ctors, envI.IsType decl.uvars [] c.type)
    (hbundle : ∀ {v envI envC}, mkViews decl = some v →
      addTypeConsts env decl = some envI →
      decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c =>
          env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI = some envC →
      VEnv.Ordered envC → env ≤ envC → RecCtxWF envC (mkRecCtx v largeElim))
    (H : addInductCore env decl largeElim = some env') :
    VEnv.Ordered env' := by
  obtain ⟨v, hv, H⟩ := Option.bind_eq_some_iff.1 H
  obtain ⟨envI, hI, H⟩ := Option.bind_eq_some_iff.1 H
  obtain ⟨envC, hC, H⟩ := Option.bind_eq_some_iff.1 H
  obtain ⟨envR, hR, H⟩ := Option.bind_eq_some_iff.1 H
  obtain ⟨rules, hrules, H⟩ := Option.bind_eq_some_iff.1 H
  cases H
  have ⟨hordI, hleI⟩ := foldl_addConst_ordered henv hty hI
  have ⟨hordC, hleC⟩ := foldl_addCtors_ordered hordI (hctor hI) hC
  have hbC := hbundle hv hI hC hordC (hleI.trans hleC)
  have hrecs : ∀ p ∈ v.types.zipIdx, ∃ T,
      recType (mkRecCtx v largeElim) p.2 = some T ∧
      envC.IsType (mkRecCtx v largeElim).recUvars [] T := by
    intro ⟨t, i⟩ hp
    have h0 : ((mkRecCtx v largeElim).types)[i]? = _ :=
      List.getElem?_map (l := v.types) (i := i)
    rw [mem_zipIdx_getElem? hp] at h0
    exact recType_isType hordC hbC h0
  have ⟨hordR, hleR, hcs⟩ := foldl_addRecs_ordered hordC .rfl hrecs hR
  obtain ⟨rules', hrules', hwf⟩ := iotaRules_wf hordC hbC hleR fun i t' ht' => by
    have h0 := ht'
    rw [show (mkRecCtx v largeElim).types = v.types.map _ from rfl,
      List.getElem?_map] at h0
    obtain ⟨t, hti, hft⟩ := Option.map_eq_some_iff.1 h0
    obtain ⟨T, hT, hc⟩ := hcs (t, i) (getElem?_mem_zipIdx hti)
    refine ⟨T, hT, ?_⟩
    rw [← hft]
    exact hc
  rw [hrules'] at hrules; cases hrules
  exact foldl_addDefEqs_ordered hordR .rfl hwf

end IndSpec
