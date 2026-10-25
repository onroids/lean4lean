import Lean4Lean.Research.Inductive.WF

/-!
# Transport to the recursor-typing bundle

Syntactic facts come from `mkViews` and closedness. The remaining reassembly
and telescope-typing obligations are explicit in `WFExact` and `WFTele`.
`addInductCore_WF4` preserves `Ordered` from these predicates together with
`WFCore`; it does not derive the whole bundle from `WFCore` alone.
-/

namespace Lean4Lean
namespace IndSpec

open VExpr

/-! ## Telescope decomposition and closedness -/

theorem consumeAnnots_closedN {A : VExpr} {k} (h : A.ClosedN k) :
    (consumeAnnots A).ClosedN k := by
  fun_induction consumeAnnots A with
  | case1 _ _ _ _ _ ih => exact ih h.1.2
  | case2 => exact h
  | case3 _ _ _ _ ih => exact ih h.2
  | case4 => exact h
  | case5 => exact h

theorem teleSplit_length : ∀ {n : Nat} {e Δ rest},
    teleSplit n e = some (Δ, rest) → Δ.length = n
  | 0, e, _, _, h => by
    cases h; rfl
  | n+1, .forallE A B, Δ, rest, h => by
    simp only [teleSplit] at h
    obtain ⟨⟨Δ', rest'⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases h2
    simp [teleSplit_length h1]

theorem teleSplit_closedN : ∀ {n : Nat} {e Δ rest} {k},
    e.ClosedN k → teleSplit n e = some (Δ, rest) →
    ClosedTele Δ k ∧ rest.ClosedN (k + n)
  | 0, e, _, _, k, he, h => by
    cases h
    exact ⟨trivial, he⟩
  | n+1, .forallE A B, Δ, rest, k, he, h => by
    simp only [teleSplit] at h
    obtain ⟨⟨Δ', rest'⟩, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases h2
    have ⟨ih1, ih2⟩ := teleSplit_closedN he.2 h1
    exact ⟨⟨consumeAnnots_closedN he.1, ih1⟩,
      by rwa [show k + 1 + n = k + (n+1) by omega] at ih2⟩

theorem teleAll_closedN : ∀ {e : VExpr} {k}, e.ClosedN k →
    ClosedTele (teleAll e).1 k ∧ (teleAll e).2.ClosedN (k + (teleAll e).1.length)
  | .bvar _, _, h | .sort _, _, h | .const _ _, _, h | .app _ _, _, h
  | .lam _ _, _, h => ⟨trivial, h⟩
  | .forallE A B, k, h => by
    have ⟨ih1, ih2⟩ := teleAll_closedN (e := B) h.2
    refine ⟨⟨consumeAnnots_closedN h.1, ih1⟩, ?_⟩
    show ClosedN _ (k + (_ :: (teleAll B).1).length)
    rwa [show k + (consumeAnnots A :: (teleAll B).1).length
      = k + 1 + (teleAll B).1.length by simp; omega]

theorem closedTele_instL {ls : List VLevel} : ∀ {Δ : List VExpr} {k},
    ClosedTele Δ k → ClosedTele (Δ.map (VExpr.instL ls)) k
  | [], _, _ => trivial
  | _ :: _, _, ⟨h1, h2⟩ => ⟨h1.instL, closedTele_instL h2⟩

theorem guard_some {p : Prop} [Decidable p] {u : Unit}
    (h : (guard p : Option Unit) = some u) : p := by
  unfold guard at h
  split at h
  · assumption
  · cases h

theorem closedTele_getElem {Δ : List VExpr} {k i : Nat} {A : VExpr}
    (h : ClosedTele Δ k) (hA : Δ[i]? = some A) : A.ClosedN (k + i) := by
  induction Δ generalizing k i with
  | nil => cases hA
  | cons B Δ ih =>
    cases i with
    | zero => cases hA; exact h.1
    | succ i =>
      have := ih h.2 hA
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

/-! ## App-spine and `validIndApp?`/`recArg?` inversion -/

theorem getAppList_go_eq : ∀ {e : VExpr} {acc},
    mkAppList (getAppList.go acc e).1 (getAppList.go acc e).2 = mkAppList e acc
  | .app f a, acc => by
    show mkAppList (getAppList.go (a :: acc) f).1 (getAppList.go (a :: acc) f).2 = _
    rw [getAppList_go_eq (e := f)]; rfl
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _ => rfl

/-- `mkAppList` is a left inverse of `getAppList`. -/
theorem getAppList_eq {e : VExpr} :
    mkAppList (getAppList e).1 (getAppList e).2 = e := by
  have := getAppList_go_eq (e := e) (acc := [])
  simpa [getAppList, mkAppList] using this

/-- The syntactic content of a successful `validIndApp?`: the expression *is*
the named type constant at the expected levels applied to the parameter
variable spine and the reported index arguments. -/
theorem validIndApp?_shape {names : List Name} {nidx : List Nat} {lvls : List VLevel}
    {np L : Nat} {e : VExpr} {i : Nat} {ris : List VExpr}
    (h : validIndApp? names nidx lvls np L e = some (i, ris)) :
    ∃ nm, names[i]? = some nm ∧
      e = mkAppList (.const nm lvls)
        (((List.range np).map fun k => .bvar (L - 1 - k)) ++ ris) := by
  unfold validIndApp? at h
  rcases hga : getAppList e with ⟨f, args⟩
  rw [hga] at h
  cases f with
  | const c ls =>
    obtain ⟨i', hidx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, hls, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ni, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, htake, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    injection h with h'
    injection h' with h1 h2
    subst h1; subst h2
    replace hls : ls = lvls := guard_some hls
    replace htake : args.take np = (List.range np).map fun k => .bvar (L - 1 - k) :=
      guard_some htake
    refine ⟨c, ?_, ?_⟩
    · obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.1 hidx
      simp [List.getElem?_eq_getElem hlt, heq]
    · have he := getAppList_eq (e := e)
      rw [hga] at he
      calc e = mkAppList (.const c ls) args := he.symm
        _ = mkAppList (.const c lvls) (args.take np ++ args.drop np) := by
          rw [hls, List.take_append_drop]
        _ = _ := by rw [htake]
  | bvar v => exact absurd h (by simp)
  | sort u => exact absurd h (by simp)
  | app f a => exact absurd h (by simp)
  | lam A b => exact absurd h (by simp)
  | forallE A b => exact absurd h (by simp)

/-- Inversion for a `recFields` entry: it comes from a field at position `pf`
whose `recArg?` decomposition succeeded. -/
theorem recFields_inv {Θ : RecCtx} {c : CtorView} {pf : Nat}
    {xs : List VExpr} {it : Nat} {ris : List VExpr}
    (h : (pf, xs, it, ris) ∈ recFields Θ c) :
    ∃ F, c.fields[pf]? = some F ∧
      recArg? Θ.names Θ.nidx Θ.lvls Θ.np pf F = some (xs, it, ris) := by
  obtain ⟨⟨F, pf'⟩, hmem, heq⟩ := List.mem_filterMap.1 h
  obtain ⟨⟨xs', it', ris'⟩, hrec, hpe⟩ := Option.map_eq_some_iff.1 heq
  cases hpe
  obtain ⟨-, hlt, hFeq⟩ := List.mem_zipIdx hmem
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hFeq
  exact ⟨F, by simp [List.getElem?_eq_getElem hlt, hFeq], hrec⟩

/-- The syntactic content of a successful `recArg?`, given that the field's
`teleAll` decomposition reassembles exactly (i.e. its binder domains carry no
`optParam`-style annotations): the field type *is* the `∀`-telescope over the
reported binders ending in the valid target application. -/
theorem recArg?_shape {names : List Name} {nidx : List Nat} {lvls : List VLevel}
    {np pf : Nat} {F : VExpr} {xs : List VExpr} {it : Nat} {ris : List VExpr}
    (h : recArg? names nidx lvls np pf F = some (xs, it, ris))
    (hexact : mkForallOF (teleAll F).1 (teleAll F).2 = F) :
    ∃ nm, names[it]? = some nm ∧
      F = mkForallOF xs (mkAppList (.const nm lvls)
        (((List.range np).map fun k => .bvar (xs.length + pf + np - 1 - k)) ++ ris)) := by
  unfold recArg? at h
  obtain ⟨⟨it', ris'⟩, hva, hre⟩ := Option.bind_eq_some_iff.1 h
  injection hre with hre'
  injection hre' with h1 h2
  subst h1
  injection h2 with h1 h2
  subst h1; subst h2
  obtain ⟨nm, hnm, hbody⟩ := validIndApp?_shape hva
  exact ⟨nm, hnm, hexact.symm.trans (congrArg _ hbody)⟩

/-! ## `mkViews` inversion -/

theorem forall₂_length {α β} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_length h]

theorem forall₂_getElem_right {α β} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {i : Nat} {b : β} (hb : l₂[i]? = some b) :
    ∃ a, l₁[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => cases hb
  | cons hR t ih =>
    cases i with
    | zero => cases hb; exact ⟨_, rfl, hR⟩
    | succ i => exact ih hb

/-- What `mkViews` success says about the views, per type and per
constructor: names carry over, index/field telescopes are the `teleAll`
decompositions of the declared types after splitting off the (shared)
parameter telescope. -/
theorem mkViews_inv {decl : VInductDecl} {v : View} (h : mkViews decl = some v) :
    v.uvars = decl.uvars ∧ v.nparams = decl.nparams ∧
    v.params.length = decl.nparams ∧
    0 < decl.types.length ∧
    v.types.length = decl.types.length ∧
    ∀ (i : Nat) (t' : TypeView), v.types[i]? = some t' →
      ∃ t : VInductiveType, decl.types[i]? = some t ∧
      t'.name = t.name ∧
      (∃ rest, teleSplit decl.nparams t.type = some (v.params, rest) ∧
        t'.indices = (teleAll rest).1 ∧ ∃ l, (teleAll rest).2 = .sort l) ∧
      ∀ (j : Nat) (c' : CtorView), t'.ctors[j]? = some c' →
        ∃ c : VConstVal, t.ctors[j]? = some c ∧
        c'.name = c.name ∧
        ∃ restc, teleSplit decl.nparams c.type = some (v.params, restc) ∧
          c'.fields = (teleAll restc).1 ∧
          ∃ nidxs, validIndApp? (decl.types.map (·.name)) nidxs
            (VLevel.params decl.uvars) decl.nparams
            (c'.fields.length + decl.nparams) (teleAll restc).2 =
            some (i, c'.rIndices) := by
  unfold mkViews at h
  rcases hts : decl.types with _ | ⟨t₀, ts⟩
  · rw [hts] at h; exact absurd h (by simp)
  rw [hts] at h
  obtain ⟨⟨params, rest₀⟩, hsplit₀, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨headers, hheaders, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hd0, hhd0, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨fst0, lvl⟩ := hd0
  dsimp only at h
  unfold guard at h
  split at h
  case isFalse => cases h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨types, htypes, h⟩ := Option.bind_eq_some_iff.1 h
  injection h with h
  subst h
  rw [← hts] at hheaders htypes ⊢
  replace hheaders := List.mapM_eq_some.1 hheaders
  replace htypes := List.mapM_eq_some.1 htypes
  refine ⟨rfl, rfl, teleSplit_length hsplit₀, by simp [hts], ?_, ?_⟩
  · have h1 := (forall₂_length htypes).symm
    have h2 := forall₂_length hheaders
    simpa [← h2] using h1
  intro i t' ht'
  obtain ⟨⟨⟨t, hdr⟩, i'⟩, hzi, hg⟩ := forall₂_getElem_right htypes ht'
  obtain ⟨hi', hzip⟩ : i' = i ∧ (decl.types.zip headers)[i]? = some (t, hdr) := by
    have h1 := List.getElem?_zipIdx (l := decl.types.zip headers) (i := 0) (j := i)
    rw [hzi] at h1
    obtain ⟨a, hzip, heq⟩ := Option.map_eq_some_iff.1 h1.symm
    injection heq with h2 h3
    exact ⟨h3.symm.trans (by simp), h2 ▸ hzip⟩
  rw [hi'] at hg
  have ⟨ht, hhdr⟩ : decl.types[i]? = some t ∧ headers[i]? = some hdr := by
    have h1 := List.getElem?_zip_eq_some.1 hzip
    exact ⟨h1.1, h1.2⟩
  refine ⟨t, ht, ?_⟩
  -- invert the header entry for this type
  obtain ⟨thdr, hthdr, hhd⟩ := forall₂_getElem_right hheaders hhdr
  have hthdr' : thdr = t := by
    rw [ht] at hthdr; exact (Option.some_inj.1 hthdr).symm
  subst hthdr'
  obtain ⟨⟨params', restT⟩, hsplitT, hhd1⟩ := Option.bind_eq_some_iff.1 hhd
  obtain ⟨_, hpeqT, hhd2⟩ := Option.bind_eq_some_iff.1 hhd1
  rw [show params' = params from guard_some hpeqT] at hsplitT
  -- destructure the sort match on the header result (structure eta lets the
  -- pair match reduce to a match on the second projection)
  have hhd' : (match (teleAll restT).2 with
      | .sort l => some ((teleAll restT).1, l)
      | _ => (failure : Option (List VExpr × VLevel))) = some hdr := hhd2
  obtain ⟨lT, hs, rfl⟩ : ∃ l, (teleAll restT).2 = .sort l ∧
      hdr = ((teleAll restT).1, l) := by
    rcases hs : (teleAll restT).2 with _ | l | _ | _ | _ | _ <;> rw [hs] at hhd'
    case sort =>
      injection hhd' with h1
      exact ⟨l, rfl, h1.symm⟩
    all_goals cases hhd'
  -- invert the per-type constructor builder
  obtain ⟨ctors', hctors, hg2⟩ := Option.bind_eq_some_iff.1 hg
  injection hg2 with hg2
  cases hg2
  refine ⟨rfl, ⟨restT, hsplitT, rfl, lT, hs⟩, ?_⟩
  intro j c' hc'
  replace hctors := List.mapM_eq_some.1 hctors
  obtain ⟨c, hc, hgc⟩ := forall₂_getElem_right hctors hc'
  refine ⟨c, hc, ?_⟩
  obtain ⟨⟨params'', restC⟩, hsplitC, hgc1⟩ := Option.bind_eq_some_iff.1 hgc
  obtain ⟨_, hpeqC, hgc2⟩ := Option.bind_eq_some_iff.1 hgc1
  rw [show params'' = params from guard_some hpeqC] at hsplitC
  obtain ⟨⟨i'', ris⟩, hva, hgc3⟩ := Option.bind_eq_some_iff.1 hgc2
  obtain ⟨_, hgi, hgc4⟩ := Option.bind_eq_some_iff.1 hgc3
  replace hgi : i'' = i := guard_some hgi
  subst hgi
  injection hgc4 with hgc4
  cases hgc4
  exact ⟨rfl, restC, hsplitC, rfl, _, hva⟩

/-! ## The transport: syntactic `RecCtxWF` clauses from `mkViews` -/

theorem recArg?_xs {names : List Name} {nidx : List Nat} {lvls : List VLevel}
    {np pf : Nat} {F : VExpr} {xs : List VExpr} {it : Nat} {ris : List VExpr}
    (h : recArg? names nidx lvls np pf F = some (xs, it, ris)) :
    xs = (teleAll F).1 := by
  unfold recArg? at h
  obtain ⟨⟨it', ris'⟩, -, hre⟩ := Option.bind_eq_some_iff.1 h
  injection hre with hre'
  injection hre' with h1 h2
  exact h1.symm

/-- Exactly the *typing* clauses of `RecCtxWF` — the residue the syntactic
transport cannot derive from `mkViews` success and closedness. Producing
these from `WFCore`'s typing facts requires inverting `IsType` through
`∀`-telescopes, which rests on the open `forallE_inv` sorries in
`Theory/Typing/Injectivity.lean`. -/
structure RecCtxTypingWF (envC : VEnv) (Θ : RecCtx) : Prop where
  params_wf : TeleWF envC Θ.recUvars [] Θ.params
  idx_wf : ∀ t ∈ Θ.types, TeleWF envC Θ.recUvars Θ.params.reverse t.indices
  type_const : ∀ t ∈ Θ.types, ∃ ℓ' : VLevel, ∀ Γ,
    envC.HasType Θ.recUvars Γ (.const t.name Θ.lvls)
      (mkForallOF Θ.params (mkForallOF t.indices (.sort ℓ')))
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
  recField_tele : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      TeleWF envC Θ.recUvars
        ((c.fields.take pf).reverse ++ Θ.params.reverse) xs
  recField_fill : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      ∀ t', Θ.types[it]? = some t' →
      FillsTele envC Θ.recUvars
        (xs.reverse ++ (c.fields.take pf).reverse ++ Θ.params.reverse)
        (liftTele (xs.length + pf) t'.indices) ris

/-- The syntactic half of the `WFCore → RecCtxWF` transport: every clause of
`RecCtxWF` except the eight `RecCtxTypingWF` typing clauses follows from
`mkViews` succeeding, closedness of the declared types, and (for
`recField_shape`) annotation-freeness of the recursive fields' binder
domains. -/
theorem RecCtxWF.ofViews {decl : VInductDecl} {v : View} {largeElim : Bool}
    {envC : VEnv}
    (hv : mkViews decl = some v)
    (hclT : ∀ t ∈ decl.types, VExpr.ClosedN t.type 0)
    (hclC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, VExpr.ClosedN c.type 0)
    (hexact : ∀ t ∈ (mkRecCtx v largeElim).types, ∀ c ∈ t.ctors,
      ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields (mkRecCtx v largeElim) c →
      ∀ (F : VExpr), c.fields[pf]? = some F → mkForallOF (teleAll F).1 (teleAll F).2 = F)
    (hT : RecCtxTypingWF envC (mkRecCtx v largeElim)) :
    RecCtxWF envC (mkRecCtx v largeElim) := by
  obtain ⟨huv, hnp, hplen, hne, hlen, hty⟩ := mkViews_inv hv
  obtain ⟨Θ, hΘeq⟩ : ∃ Θ, mkRecCtx v largeElim = Θ := ⟨_, rfl⟩
  rw [hΘeq] at hexact hT ⊢
  have hnp' : Θ.np = v.nparams := by rw [← hΘeq]; cases largeElim <;> rfl
  have hn' : Θ.n = v.types.length := by rw [← hΘeq]; cases largeElim <;> rfl
  have hK' : Θ.K = v.types.foldl (fun k t => k + t.ctors.length) 0 := by
    rw [← hΘeq]; cases largeElim <;> rfl
  have hnames' : Θ.names = v.types.map (·.name) := by
    rw [← hΘeq]; cases largeElim <;> rfl
  have hnidx' : Θ.nidx = v.types.map (·.indices.length) := by
    rw [← hΘeq]; cases largeElim <;> rfl
  obtain ⟨sh, hshcl, hparamsΘ, htypesΘ⟩ :
      ∃ sh : VExpr → VExpr,
        (∀ (Δ : List VExpr) (k : Nat), ClosedTele Δ k → ClosedTele (Δ.map sh) k) ∧
        Θ.params = v.params.map sh ∧
        Θ.types = v.types.map (fun t => { t with
          indices := t.indices.map sh
          ctors := t.ctors.map fun c => { c with
            fields := c.fields.map sh, rIndices := c.rIndices.map sh } }) := by
    rw [← hΘeq]
    cases largeElim
    · exact ⟨id, fun Δ k h => by simpa using h, rfl, rfl⟩
    · exact ⟨(·.instL ((List.range v.uvars).map fun i => .param (i+1))),
        fun Δ k h => closedTele_instL h, rfl, rfl⟩
  -- closedness of the (unshifted) parameter telescope
  have hvparams_cl : ClosedTele v.params := by
    obtain ⟨t', ht'⟩ : ∃ t', v.types[0]? = some t' :=
      ⟨_, List.getElem?_eq_getElem (by omega : 0 < v.types.length)⟩
    obtain ⟨t, ht0, -, ⟨rest, hsplit, -⟩, -⟩ := hty 0 t' ht'
    have := teleSplit_closedN (hclT t (List.mem_of_getElem? ht0)) hsplit
    exact this.1
  -- closedness of each type's index telescope and each ctor's field telescope
  have hidx_cl : ∀ t ∈ Θ.types, ClosedTele t.indices Θ.np := by
    rw [htypesΘ]
    intro t ht
    obtain ⟨tv, htvmem, rfl⟩ := List.mem_map.1 ht
    obtain ⟨i, htv⟩ := List.getElem?_of_mem htvmem
    obtain ⟨t'', ht'', -, ⟨rest, hsplit, hidx, -⟩, -⟩ := hty i tv htv
    have h1 := (teleSplit_closedN (hclT t'' (List.mem_of_getElem? ht'')) hsplit).2
    have h2 := (teleAll_closedN h1).1
    rw [Nat.zero_add] at h2
    rw [← hidx] at h2
    exact hnp' ▸ hnp ▸ hshcl _ _ h2
  have hfields_cl : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors, ClosedTele c.fields Θ.np := by
    rw [htypesΘ]
    intro t ht c hc
    obtain ⟨tv, htvmem, rfl⟩ := List.mem_map.1 ht
    obtain ⟨cv, hcvmem, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, htv⟩ := List.getElem?_of_mem htvmem
    obtain ⟨t'', ht'', -, -, hctors⟩ := hty i tv htv
    obtain ⟨j, hcv⟩ := List.getElem?_of_mem hcvmem
    obtain ⟨cd, hcd, -, ⟨restc, hsplitc, hfields, -⟩⟩ := hctors j cv hcv
    have h1 := (teleSplit_closedN
      (hclC t'' (List.mem_of_getElem? ht'') cd (List.mem_of_getElem? hcd)) hsplitc).2
    have h2 := (teleAll_closedN h1).1
    rw [Nat.zero_add] at h2
    rw [← hfields] at h2
    exact hnp' ▸ hnp ▸ hshcl _ _ h2
  refine {
    np_eq := by rw [hnp', hparamsΘ]; simp [hplen, hnp]
    n_eq := by rw [hn', htypesΘ]; simp
    K_eq := by rw [hK', htypesΘ]; simp [List.foldl_map]
    names_eq := ?_
    nidx_eq := ?_
    elim_wf := ?_
    lvls_wf := ?_
    params_closed := by rw [hparamsΘ]; exact hshcl _ _ hvparams_cl
    params_wf := hT.params_wf
    idx_closed := hidx_cl
    idx_wf := hT.idx_wf
    type_const := hT.type_const
    fields_closed := hfields_cl
    fields_wf := hT.fields_wf
    ctor_const := hT.ctor_const
    rIndices_fill := hT.rIndices_fill
    recField_tele := hT.recField_tele
    recField_closed := ?_
    recField_fill := hT.recField_fill
    recField_shape := ?_
    names_len := by rw [hnames', htypesΘ]; simp }
  · -- names_eq
    intro i t ht
    rw [htypesΘ, List.getElem?_map] at ht
    obtain ⟨tv, htv, rfl⟩ := Option.map_eq_some_iff.1 ht
    rw [hnames', List.getElem?_map, htv]
    rfl
  · -- nidx_eq
    intro i t ht
    rw [htypesΘ, List.getElem?_map] at ht
    obtain ⟨tv, htv, rfl⟩ := Option.map_eq_some_iff.1 ht
    rw [hnidx', List.getElem?_map, htv]
    simp
  · -- elim_wf
    rw [← hΘeq]
    cases largeElim
    · trivial
    · exact Nat.succ_pos _
  · -- lvls_wf
    rw [← hΘeq]
    cases largeElim
    · exact fun l hl => VLevel.params_wf hl
    · intro l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      exact Nat.succ_lt_succ (List.mem_range.1 hi)
  · -- recField_closed
    intro t ht c hc pf xs it ris hrec
    obtain ⟨F, hF, hrecA⟩ := recFields_inv hrec
    have h1 := closedTele_getElem (hfields_cl t ht c hc) hF
    have h2 := (teleAll_closedN h1).1
    rw [← recArg?_xs hrecA] at h2
    exact h2
  · -- recField_shape
    intro t ht c hc pf xs it ris hrec nm hnm
    obtain ⟨F, hF, hrecA⟩ := recFields_inv hrec
    obtain ⟨nm', hnm', hFeq⟩ :=
      recArg?_shape hrecA (hexact t ht c hc pf xs it ris hrec F hF)
    cases Option.some_inj.1 (hnm'.symm.trans hnm)
    rw [hF, hFeq]

/-- **The reduced interface**: `addInductCore` preserves `Ordered` given
`WFCore`'s two typing clauses, annotation-freeness of the constructor
fields, and exactly the eight `RecCtxTypingWF` typing clauses. Every other
`RecCtxWF` clause is discharged syntactically by `RecCtxWF.ofViews`. -/
theorem addInductCore_WF' {env env' : VEnv} {decl : VInductDecl} {largeElim : Bool}
    (henv : VEnv.Ordered env)
    (hty : ∀ t ∈ decl.types, env.IsType decl.uvars [] t.type)
    (hctor : ∀ {envI}, addTypeConsts env decl = some envI →
      ∀ t ∈ decl.types, ∀ c ∈ t.ctors, envI.IsType decl.uvars [] c.type)
    (hexact : ∀ {v}, mkViews decl = some v →
      ∀ t ∈ (mkRecCtx v largeElim).types, ∀ c ∈ t.ctors,
      ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields (mkRecCtx v largeElim) c →
      ∀ (F : VExpr), c.fields[pf]? = some F → mkForallOF (teleAll F).1 (teleAll F).2 = F)
    (hT : ∀ {v envI envC}, mkViews decl = some v →
      addTypeConsts env decl = some envI →
      decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c =>
          env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI = some envC →
      VEnv.Ordered envC → env ≤ envC →
      RecCtxTypingWF envC (mkRecCtx v largeElim))
    (H : addInductCore env decl largeElim = some env') :
    VEnv.Ordered env' := by
  obtain ⟨v0, hv0, H'⟩ := Option.bind_eq_some_iff.1 H
  obtain ⟨envI, hI, -⟩ := Option.bind_eq_some_iff.1 H'
  obtain ⟨hordI, -⟩ := foldl_addConst_ordered henv hty hI
  refine addInductCore_WF henv hty hctor
    (fun {v envI' envC} hv hI' hC' hordC hle => ?_) H
  refine RecCtxWF.ofViews hv (fun t htm => ?_) (fun t htm c hcm => ?_)
    (hexact hv) (hT hv hI' hC' hordC hle)
  · obtain ⟨u, h⟩ := hty t htm
    exact h.closedN henv trivial
  · obtain ⟨u, h⟩ := hctor hI t htm c hcm
    exact h.closedN hordI trivial

/-! ## Discharging typing clauses without `∀`-inversion

Three of the eight `RecCtxTypingWF` clauses do not need telescope
inversion: `type_const` and `ctor_const` follow from the constant rule
plus the syntactic reassembly of the declared types (under
annotation-freeness), and `fields_wf` is exactly `WFCore`'s per-field
typing clause transported along the level shift. The remaining five
(`params_wf`, `idx_wf`, `rIndices_fill`, `recField_tele`,
`recField_fill`) require inverting `IsType` through `∀`-telescopes. -/

theorem instL_mkForallOF {ls : List VLevel} : ∀ {Δ : List VExpr} {e},
    (mkForallOF Δ e).instL ls = mkForallOF (Δ.map (VExpr.instL ls)) (e.instL ls)
  | [], _ => rfl
  | A :: Δ, e => by
    show VExpr.instL ls (.forallE A (mkForallOF Δ e)) = _
    rw [show VExpr.instL ls (.forallE A (mkForallOF Δ e))
      = .forallE (A.instL ls) ((mkForallOF Δ e).instL ls) from rfl,
      instL_mkForallOF (Δ := Δ)]
    rfl

theorem instL_mkAppList {ls : List VLevel} : ∀ {es : List VExpr} {f},
    (mkAppList f es).instL ls = mkAppList (f.instL ls) (es.map (VExpr.instL ls))
  | [], _ => rfl
  | a :: es, f => by
    show (mkAppList (f.app a) es).instL ls = _
    rw [instL_mkAppList (es := es)]
    rfl

theorem params_map_inst {ls : List VLevel} (h : ls.length = n) :
    (VLevel.params n).map (VLevel.inst ls) = ls := by
  subst h
  apply List.ext_getElem (by simp [VLevel.params])
  intro i h1 h2
  simp [VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2]

theorem foldlM_addConst_le {U : Nat} : ∀ {ts : List VInductiveType} {env env' : VEnv},
    ts.foldlM (fun env t => env.addConst t.name ⟨U, t.type⟩) env = some env' →
    env ≤ env'
  | [], _, _, h => by cases h; exact .rfl
  | t₀ :: ts, env, env', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (VEnv.addConst_le h1).trans (foldlM_addConst_le h2)

theorem foldlM_addConst_lookup {U : Nat} : ∀ {ts : List VInductiveType} {env env' : VEnv},
    ts.foldlM (fun env t => env.addConst t.name ⟨U, t.type⟩) env = some env' →
    ∀ t ∈ ts, env'.constants t.name = some ⟨U, t.type⟩
  | [], _, _, _, _, ht => nomatch ht
  | t₀ :: ts, env, env', h, t, ht => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases ht with
    | head =>
      refine (foldlM_addConst_le h2).constants ?_
      unfold VEnv.addConst at h1
      split at h1 <;> cases h1
      simp
    | tail _ ht => exact foldlM_addConst_lookup h2 t ht

theorem addTypeConsts_lookup {env envI : VEnv} {decl : VInductDecl}
    (h : addTypeConsts env decl = some envI) :
    ∀ t ∈ decl.types, envI.constants t.name = some ⟨decl.uvars, t.type⟩ :=
  foldlM_addConst_lookup h

theorem mkRecCtx_lvls_length {v : View} {le : Bool} :
    (mkRecCtx v le).lvls.length = v.uvars := by
  cases le <;> simp [mkRecCtx, elimData, VLevel.params]

theorem mkRecCtx_lvls_wf {v : View} {le : Bool} :
    ∀ l ∈ (mkRecCtx v le).lvls, l.WF (mkRecCtx v le).recUvars := by
  cases le
  · exact fun l hl => VLevel.params_wf hl
  · intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
    exact Nat.succ_lt_succ (List.mem_range.1 hi)

/-- Build a `TeleWF` from positionwise typing in the prefix contexts. -/
theorem teleWF_of_getElem {envX : VEnv} {U : Nat} : ∀ {Δ : List VExpr} {Γ₀},
    (∀ (pf : Nat) (F : VExpr), Δ[pf]? = some F →
      envX.IsType U ((Δ.take pf).reverse ++ Γ₀) F) →
    TeleWF envX U Γ₀ Δ
  | [], _, _ => trivial
  | A :: Δ, Γ₀, h => by
    refine ⟨by simpa using h 0 A rfl, teleWF_of_getElem fun pf F hF => ?_⟩
    have := h (pf + 1) F hF
    rwa [show ((A :: Δ).take (pf + 1)).reverse ++ Γ₀
      = (Δ.take pf).reverse ++ (A :: Γ₀) by simp] at this

/-- `fields_wf` discharge: `WFCore`'s per-field typing clause *is* the
telescope well-formedness of the constructor fields, transported along the
level shift and the environment extension. No `∀`-inversion involved. -/
theorem discharge_fields_wf {decl : VInductDecl} {v : View} {largeElim : Bool}
    {envI envC : VEnv}
    (hv : mkViews decl = some v)
    (hle : envI ≤ envC)
    (hfield : ∀ t ∈ v.types, ∀ c ∈ t.ctors, ∀ (pf : Nat) (F : VExpr),
      c.fields[pf]? = some F →
      ∃ u, envI.HasType decl.uvars (fieldCtx v.params c.fields pf) F (.sort u)) :
    ∀ t' ∈ (mkRecCtx v largeElim).types, ∀ c' ∈ t'.ctors,
      TeleWF envC (mkRecCtx v largeElim).recUvars
        (mkRecCtx v largeElim).params.reverse c'.fields := by
  obtain ⟨huv, -, -, -, -, -⟩ := mkViews_inv hv
  intro t' ht' c' hc'
  cases largeElim with
  | false =>
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.1 ht'
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 hc'
    refine teleWF_of_getElem fun pf F hF => ?_
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hF
    obtain ⟨F₀, hF₀, rfl⟩ := hF
    obtain ⟨u, hu⟩ := hfield tv htv cv hcv pf F₀ hF₀
    have := (VEnv.IsType.mono hle ⟨u, hu⟩ : envC.IsType decl.uvars _ _)
    rw [← huv] at this
    show envC.IsType v.uvars
      (((cv.fields.map id).take pf).reverse ++ (v.params.map id).reverse) (id F₀)
    simpa [fieldCtx] using this
  | true =>
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.1 ht'
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 hc'
    refine teleWF_of_getElem fun pf F hF => ?_
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hF
    obtain ⟨F₀, hF₀, rfl⟩ := hF
    obtain ⟨u, hu⟩ := hfield tv htv cv hcv pf F₀ hF₀
    have h1 := VEnv.IsType.mono hle
      (VEnv.IsType.instL (ls := (mkRecCtx v true).lvls)
        (mkRecCtx_lvls_wf (le := true) · ·) ⟨u, hu⟩)
    simp only [mkRecCtx, elimData] at h1 ⊢
    simpa [fieldCtx, List.map_take] using h1

/-- `type_const` discharge: under annotation-freeness of the declared type
(its `teleSplit`/`teleAll` decompositions reassemble exactly), the clause is
just the constant rule plus `instL` distribution. -/
theorem discharge_type_const {decl : VInductDecl} {v : View} {largeElim : Bool}
    {env envC : VEnv}
    (hle : env ≤ envC) (hordC : VEnv.Ordered envC)
    (hv : mkViews decl = some v)
    (hconst : ∀ t ∈ decl.types, envC.constants t.name = some ⟨decl.uvars, t.type⟩)
    (hlwf : ∀ t ∈ decl.types, t.type.LevelWF decl.uvars)
    (hexT : ∀ t ∈ decl.types, ∀ rest,
      teleSplit decl.nparams t.type = some (v.params, rest) →
      ∃ u, env.IsDefEq decl.uvars [] t.type
        (mkForallOF v.params (mkForallOF (teleAll rest).1 (teleAll rest).2))
        (.sort u)) :
    ∀ t' ∈ (mkRecCtx v largeElim).types, ∃ ℓ' : VLevel, ∀ Γ,
      envC.HasType (mkRecCtx v largeElim).recUvars Γ
        (.const t'.name (mkRecCtx v largeElim).lvls)
        (mkForallOF (mkRecCtx v largeElim).params
          (mkForallOF t'.indices (.sort ℓ'))) := by
  obtain ⟨huv, hnp, -, -, -, hty⟩ := mkViews_inv hv
  intro t' ht'
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.1 ht'
  obtain ⟨i, hgi⟩ := List.getElem?_of_mem htv
  obtain ⟨t, hti, hname, ⟨rest, hsplit, hidx, l, hsort⟩, -⟩ := hty i tv hgi
  have htmem := List.mem_of_getElem? hti
  obtain ⟨u, hdq⟩ := hexT t htmem rest hsplit
  rw [← hidx] at hdq
  rw [hsort] at hdq
  have hdq := hdq.mono hle
  have hlen : (mkRecCtx v largeElim).lvls.length = decl.uvars := by
    rw [mkRecCtx_lvls_length, huv]
  cases largeElim with
  | false =>
    refine ⟨l, fun Γ => ?_⟩
    have hc := VEnv.HasType.const (env := envC) (Γ := Γ) (hconst t htmem)
      (fun l hl => mkRecCtx_lvls_wf l hl) hlen
    simp only [mkRecCtx, elimData, huv, ite_eq_right (by simp : ¬(false = true))] at hc
    rw [(hlwf t htmem).instL_id, ← hname] at hc
    have hc2 := VEnv.IsDefEq.defeqDF (hdq.weak0 hordC (Γ := Γ)) hc
    simp [mkRecCtx, elimData, huv]
    exact hc2
  | true =>
    refine ⟨l.inst (mkRecCtx v true).lvls, fun Γ => ?_⟩
    have hc := VEnv.HasType.const (env := envC) (Γ := Γ) (hconst t htmem)
      (fun l hl => mkRecCtx_lvls_wf l hl) hlen
    rw [← hname] at hc
    have hdq1 := hdq.instL (U' := (mkRecCtx v true).recUvars)
      (ls := (mkRecCtx v true).lvls) (fun l hl => mkRecCtx_lvls_wf l hl)
    rw [instL_mkForallOF, instL_mkForallOF] at hdq1
    simp only [List.map_nil] at hdq1
    have hc2 := VEnv.IsDefEq.defeqDF (hdq1.weak0 hordC (Γ := Γ)) hc
    simp [mkRecCtx, elimData, huv] at hc2 ⊢
    exact hc2

theorem bvar_spine_instL {ls : List VLevel} {np L : Nat} :
    ((List.range np).map fun k => VExpr.bvar (L - 1 - k)).map (VExpr.instL ls)
      = (List.range np).map fun k => VExpr.bvar (L - 1 - k) := by
  simp [List.map_map, Function.comp_def, VExpr.instL]

/-- `ctor_const` discharge: under annotation-freeness of the declared
constructor type, the clause is the constant rule plus the
`validIndApp?` shape of the target and `instL` distribution. -/
theorem discharge_ctor_const {decl : VInductDecl} {v : View} {largeElim : Bool}
    {envI envC : VEnv}
    (hle : envI ≤ envC) (hordC : VEnv.Ordered envC)
    (hv : mkViews decl = some v)
    (hconstC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
      envC.constants c.name = some ⟨decl.uvars, c.type⟩)
    (hlwfC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.type.LevelWF decl.uvars)
    (hexC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ restc,
      teleSplit decl.nparams c.type = some (v.params, restc) →
      ∃ u, envI.IsDefEq decl.uvars [] c.type
        (mkForallOF v.params (mkForallOF (teleAll restc).1 (teleAll restc).2))
        (.sort u)) :
    ∀ (i : Nat) (t : TypeView), (mkRecCtx v largeElim).types[i]? = some t →
      ∀ c ∈ t.ctors, ∀ Γ,
      envC.HasType (mkRecCtx v largeElim).recUvars Γ
        (.const c.name (mkRecCtx v largeElim).lvls)
        (mkForallOF (mkRecCtx v largeElim).params (mkForallOF c.fields
          (mkAppList (.const t.name (mkRecCtx v largeElim).lvls)
            (((List.range (mkRecCtx v largeElim).np).map fun k =>
                VExpr.bvar (c.fields.length + (mkRecCtx v largeElim).np - 1 - k))
              ++ c.rIndices)))) := by
  obtain ⟨huv, hnp, -, -, -, hty⟩ := mkViews_inv hv
  intro i t ht c hc Γ
  rw [show (mkRecCtx v largeElim).types = v.types.map _ from rfl,
    List.getElem?_map] at ht
  obtain ⟨tv, htv, rfl⟩ := Option.map_eq_some_iff.1 ht
  obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 hc
  obtain ⟨j, hcvj⟩ := List.getElem?_of_mem hcv
  obtain ⟨td, hti, hname, -, hctors⟩ := hty i tv htv
  obtain ⟨cd, hcdj, hnameC, restc, hsplitC, hfields, nidxs, hva⟩ := hctors j cv hcvj
  have htdmem := List.mem_of_getElem? hti
  have hcdmem := List.mem_of_getElem? hcdj
  obtain ⟨nm, hnm, hshape⟩ := validIndApp?_shape hva
  have hnm' : nm = td.name := by
    rw [List.getElem?_map, hti] at hnm
    exact (Option.some_inj.1 hnm).symm
  subst hnm'
  obtain ⟨u, hdq⟩ := hexC td htdmem cd hcdmem restc hsplitC
  rw [hshape, hfields] at hdq
  have hdq := hdq.mono hle
  have hlen : (mkRecCtx v largeElim).lvls.length = decl.uvars := by
    rw [mkRecCtx_lvls_length, huv]
  have hc := VEnv.HasType.const (env := envC) (Γ := Γ)
    (hconstC td htdmem cd hcdmem) (fun l hl => mkRecCtx_lvls_wf l hl) hlen
  cases largeElim with
  | false =>
    simp only [mkRecCtx, elimData, huv, ite_eq_right (by simp : ¬(false = true))] at hc
    rw [(hlwfC td htdmem cd hcdmem).instL_id] at hc
    have hc2 := VEnv.IsDefEq.defeqDF (hdq.weak0 hordC (Γ := Γ)) hc
    simp [mkRecCtx, elimData, huv, hnp] at hc2 ⊢
    rw [hnameC, hname]
    simp [hfields]
    exact hc2
  | true =>
    have hdq1 := hdq.instL (U' := (mkRecCtx v true).recUvars)
      (ls := (mkRecCtx v true).lvls) (fun l hl => mkRecCtx_lvls_wf l hl)
    rw [instL_mkForallOF, instL_mkForallOF, instL_mkAppList,
      List.map_append, bvar_spine_instL] at hdq1
    have hlvls : (VLevel.params decl.uvars).map
        (VLevel.inst (mkRecCtx v true).lvls) = (mkRecCtx v true).lvls :=
      params_map_inst hlen
    simp only [VExpr.instL, List.map_nil] at hdq1
    rw [hlvls] at hdq1
    have hc2 := VEnv.IsDefEq.defeqDF (hdq1.weak0 hordC (Γ := Γ)) hc
    simp [mkRecCtx, elimData, huv, hnp] at hc2 ⊢
    rw [hnameC, hname]
    simp [hfields]
    exact hc2

theorem foldlM_addConstV_le {U : Nat} : ∀ {cs : List VConstVal} {env env' : VEnv},
    cs.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env = some env' →
    env ≤ env'
  | [], _, _, h => by cases h; exact .rfl
  | c₀ :: cs, env, env', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (VEnv.addConst_le h1).trans (foldlM_addConstV_le h2)

theorem foldlM_addConstV_lookup {U : Nat} : ∀ {cs : List VConstVal} {env env' : VEnv},
    cs.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env = some env' →
    ∀ c ∈ cs, env'.constants c.name = some ⟨U, c.type⟩
  | [], _, _, _, _, hc => nomatch hc
  | c₀ :: cs, env, env', h, c, hc => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases hc with
    | head =>
      refine (foldlM_addConstV_le h2).constants ?_
      unfold VEnv.addConst at h1
      split at h1 <;> cases h1
      simp
    | tail _ hc => exact foldlM_addConstV_lookup h2 c hc

theorem foldl_addCtors_le {U : Nat} : ∀ {ts : List VInductiveType} {env env' : VEnv},
    ts.foldlM (fun env t =>
      t.ctors.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env) env = some env' →
    env ≤ env'
  | [], _, _, h => by cases h; exact .rfl
  | t₀ :: ts, env, env', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (foldlM_addConstV_le h1).trans (foldl_addCtors_le h2)

theorem foldl_addCtors_lookup {U : Nat} : ∀ {ts : List VInductiveType} {env env' : VEnv},
    ts.foldlM (fun env t =>
      t.ctors.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env) env = some env' →
    ∀ t ∈ ts, ∀ c ∈ t.ctors, env'.constants c.name = some ⟨U, c.type⟩
  | [], _, _, _, _, ht, _, _ => nomatch ht
  | t₀ :: ts, env, env', h, t, ht, c, hc => by
    rw [List.foldlM_cons] at h
    obtain ⟨env1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    cases ht with
    | head => exact (foldl_addCtors_le h2).constants (foldlM_addConstV_lookup h1 c hc)
    | tail _ ht => exact foldl_addCtors_lookup h2 t ht c hc

/-- The five clauses of `RecCtxTypingWF` that genuinely need `∀`-telescope
inversion (i.e. the open `Injectivity` sorries) to derive from `WFCore`:
the parameter/index telescope well-formedness, and the three
telescope-decomposition typing facts about constructor targets and
recursive fields. -/
structure RecCtxTelescopeWF (envC : VEnv) (Θ : RecCtx) : Prop where
  params_wf : TeleWF envC Θ.recUvars [] Θ.params
  idx_wf : ∀ t ∈ Θ.types, TeleWF envC Θ.recUvars Θ.params.reverse t.indices
  rIndices_fill : ∀ (i : Nat) (t : TypeView), Θ.types[i]? = some t →
    ∀ c ∈ t.ctors,
    FillsTele envC Θ.recUvars (c.fields.reverse ++ Θ.params.reverse)
      (liftTele c.fields.length t.indices) c.rIndices
  recField_tele : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      TeleWF envC Θ.recUvars
        ((c.fields.take pf).reverse ++ Θ.params.reverse) xs
  recField_fill : ∀ t ∈ Θ.types, ∀ c ∈ t.ctors,
    ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields Θ c →
      ∀ t', Θ.types[it]? = some t' →
      FillsTele envC Θ.recUvars
        (xs.reverse ++ (c.fields.take pf).reverse ++ Θ.params.reverse)
        (liftTele (xs.length + pf) t'.indices) ris

/-- **The fully reduced interface**: `addInductCore` preserves `Ordered`
given `WFCore`'s typing clauses (declared types, constructor types, and the
per-field clause), annotation-freeness of the declared telescopes, and the
five `RecCtxTelescopeWF` clauses. `type_const`, `ctor_const`, and
`fields_wf` are discharged; everything syntactic is derived. -/
theorem addInductCore_WF3 {env env' : VEnv} {decl : VInductDecl} {largeElim : Bool}
    (henv : VEnv.Ordered env)
    (hty : ∀ t ∈ decl.types, env.IsType decl.uvars [] t.type)
    (hctor : ∀ {envI}, addTypeConsts env decl = some envI →
      ∀ t ∈ decl.types, ∀ c ∈ t.ctors, envI.IsType decl.uvars [] c.type)
    (hfield : ∀ {v envI}, mkViews decl = some v →
      addTypeConsts env decl = some envI →
      ∀ t ∈ v.types, ∀ c ∈ t.ctors, ∀ (pf : Nat) (F : VExpr),
        c.fields[pf]? = some F →
        ∃ u, envI.HasType decl.uvars (fieldCtx v.params c.fields pf) F (.sort u))
    (hexT : ∀ {v}, mkViews decl = some v →
      ∀ t ∈ decl.types, ∀ rest,
      teleSplit decl.nparams t.type = some (v.params, rest) →
      ∃ u, env.IsDefEq decl.uvars [] t.type
        (mkForallOF v.params (mkForallOF (teleAll rest).1 (teleAll rest).2))
        (.sort u))
    (hexC : ∀ {v envI}, mkViews decl = some v → addTypeConsts env decl = some envI →
      ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ restc,
      teleSplit decl.nparams c.type = some (v.params, restc) →
      ∃ u, envI.IsDefEq decl.uvars [] c.type
        (mkForallOF v.params (mkForallOF (teleAll restc).1 (teleAll restc).2))
        (.sort u))
    (hexF : ∀ {v}, mkViews decl = some v →
      ∀ t ∈ (mkRecCtx v largeElim).types, ∀ c ∈ t.ctors,
      ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields (mkRecCtx v largeElim) c →
      ∀ (F : VExpr), c.fields[pf]? = some F → mkForallOF (teleAll F).1 (teleAll F).2 = F)
    (hT : ∀ {v envI envC}, mkViews decl = some v →
      addTypeConsts env decl = some envI →
      decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c =>
          env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI = some envC →
      VEnv.Ordered envC →
      RecCtxTelescopeWF envC (mkRecCtx v largeElim))
    (H : addInductCore env decl largeElim = some env') :
    VEnv.Ordered env' := by
  have hlwfT : ∀ t ∈ decl.types, t.type.LevelWF decl.uvars := fun t ht =>
    have ⟨_, h⟩ := hty t ht
    (VEnv.IsDefEq.levelWF h trivial).1
  refine addInductCore_WF' henv hty hctor (fun {v} hv => hexF hv)
    (fun {v envI envC} hv hI hC hordC hle => ?_) H
  have hlwfC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.type.LevelWF decl.uvars :=
    fun t ht c hc =>
    have ⟨_, h⟩ := hctor hI t ht c hc
    (VEnv.IsDefEq.levelWF h trivial).1
  have hleIC : envI ≤ envC := foldl_addCtors_le hC
  have hconstT : ∀ t ∈ decl.types, envC.constants t.name
      = some ⟨decl.uvars, t.type⟩ := fun t ht =>
    hleIC.constants (addTypeConsts_lookup hI t ht)
  have hconstC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, envC.constants c.name
      = some ⟨decl.uvars, c.type⟩ := foldl_addCtors_lookup hC
  have h5 := hT hv hI hC hordC
  exact {
    params_wf := h5.params_wf
    idx_wf := h5.idx_wf
    type_const := discharge_type_const hle hordC hv hconstT hlwfT (hexT hv)
    fields_wf := discharge_fields_wf hv hleIC (hfield hv hI)
    ctor_const := discharge_ctor_const hleIC hordC hv hconstC hlwfC (hexC hv hI)
    rIndices_fill := h5.rIndices_fill
    recField_tele := h5.recField_tele
    recField_fill := h5.recField_fill }

/-- The telescope-reassembly side of the spec, in definitional form.
`teleSplit`/`teleAll` consume `optParam`/`autoParam`/`outParam`/
`semiOutParam` annotations on binder domains, so reassembly via
`mkForallOF` is only *definitionally* equal to the stored type: pointwise,
each stripped domain is defeq to its annotated original via the
annotation constant's unfolding (`optParam A d ≡ A` by `extra` + beta).

TRUST NOTE: those unfoldings are environment defeqs of the four prelude
definitions `optParam`, `autoParam`, `outParam`, `semiOutParam` — the
same trust class as lean4lean's `Primitive.lean` prelude divergence. The
C++ kernel relies on exactly this without verifying it
(`inductive.cpp:179`: recursor binders are built from
`consumeTypeAnnotations`-stripped domains while constructor constants
keep the annotated types, so the construction typechecks only because
the annotation constants delta-unfold to the identity). Stating the
clauses as sort-typed defeqs carries that dependency visibly; a real
environment satisfies it because the prelude declares the four constants
as definitions, and a producer extracts the defeqs from the environment
rather than assuming them. The final clause (recursive-field reassembly,
consumed by `recField_shape`) remains syntactic: covering annotated
recursive-field inner binders needs conversion-aware typing of the
recursor construction itself. -/
def WFExact (env : VEnv) (decl : VInductDecl) (largeElim : Bool) : Prop :=
  ∀ v, mkViews decl = some v →
    (∀ t ∈ decl.types, ∀ rest, teleSplit decl.nparams t.type = some (v.params, rest) →
      ∃ u, env.IsDefEq decl.uvars [] t.type
        (mkForallOF v.params (mkForallOF (teleAll rest).1 (teleAll rest).2))
        (.sort u)) ∧
    (∀ envI, addTypeConsts env decl = some envI →
      ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ restc,
      teleSplit decl.nparams c.type = some (v.params, restc) →
      ∃ u, envI.IsDefEq decl.uvars [] c.type
        (mkForallOF v.params (mkForallOF (teleAll restc).1 (teleAll restc).2))
        (.sort u)) ∧
    (∀ t ∈ (mkRecCtx v largeElim).types, ∀ c ∈ t.ctors,
      ∀ pf xs it ris, (pf, xs, it, ris) ∈ recFields (mkRecCtx v largeElim) c →
      ∀ (F : VExpr), c.fields[pf]? = some F → mkForallOF (teleAll F).1 (teleAll F).2 = F)

/-- The residual typing side of the spec beyond `WFCore`: the five
`RecCtxTelescopeWF` telescope-typing clauses, at the environment that
already holds the block's type and constructor constants (pinned by the
`addTypeConsts` and constructor-fold equations — the clauses mention the
block's constants, so quantifying over arbitrary extensions of the *base*
environment would be unsatisfiable for recursive blocks). These are
conjecturally derivable from `WFCore` given forall-injectivity
(`Theory/Typing/Injectivity.lean`); until that lands they are spec
clauses. The earlier base-environment quantification was unsatisfiable for
recursive blocks and was repaired. `EmptyBlockWitness.lean` jointly witnesses
all three predicates for an empty datatype in both elimination modes, and
`RecursiveBlockWitness.lean` does so for a Nat-shaped datatype with large
elimination. `TelescopeWitness.lean` exercises a parameterized recursive example. These
examples do not prove a general correspondence with checker acceptance. -/
def WFTele (env : VEnv) (decl : VInductDecl) (largeElim : Bool) : Prop :=
  ∀ v, mkViews decl = some v →
    ∀ envI envC, addTypeConsts env decl = some envI →
      decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c =>
          env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI = some envC →
      VEnv.Ordered envC →
      RecCtxTelescopeWF envC (mkRecCtx v largeElim)

/-- `addInductCore_WF3` repackaged over the three spec predicates
(`WFCore` + `WFExact` + `WFTele`). This is an isolated research theorem;
upstream `VInductDecl.WF` is unchanged. -/
theorem addInductCore_WF4 {env env' : VEnv} {decl : VInductDecl} {largeElim : Bool}
    (henv : VEnv.Ordered env)
    (hcore : WFCore env decl largeElim)
    (hexact : WFExact env decl largeElim)
    (htele : WFTele env decl largeElim)
    (H : addInductCore env decl largeElim = some env') :
    VEnv.Ordered env' := by
  obtain ⟨v, envI, hv, hI, hty, hctor, hfield, -⟩ := hcore
  refine addInductCore_WF3 henv hty ?_ ?_ ?_ ?_ ?_ ?_ H
  · intro envI' hI'
    cases Option.some.inj (hI.symm.trans hI')
    exact hctor
  · intro v' envI' hv' hI' t ht c hc pf F hF
    cases Option.some.inj (hv.symm.trans hv')
    cases Option.some.inj (hI.symm.trans hI')
    obtain ⟨⟨u, hu, -⟩, -⟩ := hfield t ht c hc pf F hF
    exact ⟨u, hu⟩
  · intro v' hv'
    cases Option.some.inj (hv.symm.trans hv')
    exact (hexact v hv).1
  · intro v' envI' hv' hI'
    cases Option.some.inj (hv.symm.trans hv')
    exact (hexact v hv).2.1 envI' hI'
  · intro v' hv'
    cases Option.some.inj (hv.symm.trans hv')
    exact (hexact v hv).2.2
  · intro v' envI' envC hv' hI' hC' hord
    cases Option.some.inj (hv.symm.trans hv')
    exact htele v hv envI' envC hI' hC' hord

end IndSpec
end Lean4Lean
