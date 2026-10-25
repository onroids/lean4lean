import Lean4Lean.Research.Inductive.Transport
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Existence and monotonicity of the abstract construction

The construction can reject a declaration's syntax or duplicate names.
`addInductCore_exists` proves success under `WFCore`, `WFExact`, `WFTele`,
fresh constructor/recursor names, and pairwise distinct introduced names.
The other lemmas describe extension and transport of this isolated model.
-/

namespace Lean4Lean
namespace IndSpec

/-- The names an inductive declaration introduces: its types, then its
constructors, then its recursors. -/
def declNames (decl : VInductDecl) : List Lean.Name :=
  decl.types.map (·.name) ++
  decl.types.flatMap (fun t => t.ctors.map (·.name)) ++
  decl.types.map (fun t => Lean.mkRecName t.name)

/-- An `addConst` fold leaves the names it does not insert untouched. -/
theorem foldlM_addConst_preserve {α : Type} (nm : α → Lean.Name) (ci : α → VConstant) :
    ∀ {l : List α} {env env' : VEnv},
    l.foldlM (fun env a => env.addConst (nm a) (ci a)) env = some env' →
    ∀ n, (∀ a ∈ l, nm a ≠ n) → env'.constants n = env.constants n
  | [], _, _, h, _, _ => by cases h; rfl
  | a :: l, env, env', h, n, hn => by
    rw [List.foldlM_cons] at h
    obtain ⟨env₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    rw [foldlM_addConst_preserve nm ci h₂ n (fun b hb => hn b (.tail _ hb)),
      VEnv.addConst_constants_eq h₁]
    simp [hn a (.head _)]

/-- An `addConst` fold succeeds when its names are fresh and pairwise distinct. -/
theorem foldlM_addConst_exists {α : Type} (nm : α → Lean.Name) (ci : α → VConstant) :
    ∀ {l : List α} {env : VEnv},
    (∀ a ∈ l, env.constants (nm a) = none) → (l.map nm).Nodup →
    ∃ env', l.foldlM (fun env a => env.addConst (nm a) (ci a)) env = some env'
  | [], env, _, _ => ⟨env, rfl⟩
  | a :: l, env, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci a) (hfresh a (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := foldlM_addConst_exists nm ci (l := l) (env := env₁)
      (fun b hb => ?_) hnd.2
    · refine ⟨env₂, ?_⟩
      rw [List.foldlM_cons]
      exact Option.bind_eq_some_iff.2 ⟨env₁, h₁, h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : nm a ≠ nm b := fun h => hnd.1 (List.mem_map.2 ⟨b, hb, h.symm⟩)
      simp [this, hfresh b (.tail _ hb)]

/-- The nested constructor fold of `addInductCore` is the flat fold over all
constructors. -/
theorem foldlM_ctors_flat {U : Nat} : ∀ (ts : List VInductiveType) (env : VEnv),
    ts.foldlM (fun env t =>
      t.ctors.foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env) env =
    (ts.flatMap (·.ctors)).foldlM (fun env c => env.addConst c.name ⟨U, c.type⟩) env
  | [], _ => rfl
  | t :: ts, env => by
    simp only [List.foldlM_cons, List.flatMap_cons, List.foldlM_append]
    congr 1
    funext e
    exact foldlM_ctors_flat ts e

/-- The recursor fold of `addInductCore` succeeds when every recursor type
exists and the recursor names are fresh and pairwise distinct. -/
theorem foldlM_addRecs_exists {Θ : RecCtx} :
    ∀ {ts : List (TypeView × Nat)} {env : VEnv},
    (∀ p ∈ ts, ∃ T, recType Θ p.2 = some T) →
    (∀ p ∈ ts, env.constants (Lean.mkRecName p.1.name) = none) →
    (ts.map fun p => Lean.mkRecName p.1.name).Nodup →
    ∃ env', ts.foldlM (fun env (t, i) => do
      let ty ← recType Θ i
      env.addConst (Lean.mkRecName t.name) ⟨Θ.recUvars, ty⟩) env = some env'
  | [], env, _, _, _ => ⟨env, rfl⟩
  | (t, i) :: ts, env, hrec, hfresh, hnd => by
    obtain ⟨T, hT⟩ := hrec (t, i) (.head _)
    obtain ⟨env₁, h₁⟩ :=
      VEnv.addConst_eq_none (ci := ⟨Θ.recUvars, T⟩) (hfresh (t, i) (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := foldlM_addRecs_exists (Θ := Θ) (ts := ts) (env := env₁)
      (fun p hp => hrec p (.tail _ hp)) (fun p hp => ?_) hnd.2
    · refine ⟨env₂, ?_⟩
      rw [List.foldlM_cons]
      refine Option.bind_eq_some_iff.2 ⟨env₁, ?_, h₂⟩
      show Option.bind (recType Θ i) _ = some env₁
      rw [hT]
      exact h₁
    · rw [VEnv.addConst_constants_eq h₁]
      have : Lean.mkRecName t.name ≠ Lean.mkRecName p.1.name :=
        fun h => hnd.1 (List.mem_map.2 ⟨p, hp, h.symm⟩)
      simp [this, hfresh p (.tail _ hp)]

/-- **Existence of the abstract construction.** Given the three spec
predicates, base-freshness of the constructor and recursor names, and
pairwise distinctness of all introduced names (the type names' freshness is
already inside `WFCore`, via `addTypeConsts`), `addInductCore` succeeds; the
intermediate environments and the iota rules are exposed for consumers that
must match them against a concrete producer. -/
theorem addInductCore_exists {env : VEnv} {decl : VInductDecl} {le : Bool}
    (henv : VEnv.Ordered env)
    (hcore : WFCore env decl le) (hexact : WFExact env decl le) (htele : WFTele env decl le)
    (hfreshC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env.constants c.name = none)
    (hfreshR : ∀ t ∈ decl.types, env.constants (Lean.mkRecName t.name) = none)
    (hnd : (declNames decl).Nodup) :
    ∃ v envI envC envR rules,
      mkViews decl = some v ∧ addTypeConsts env decl = some envI ∧
      decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c => env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI
        = some envC ∧
      v.types.zipIdx.foldlM (fun env (t, i) => do
        let ty ← recType (mkRecCtx v le) i
        env.addConst (Lean.mkRecName t.name) ⟨(mkRecCtx v le).recUvars, ty⟩) envC
        = some envR ∧
      iotaRules (mkRecCtx v le) = some rules ∧
      addInductCore env decl le = some (rules.foldl VEnv.addDefEq envR) := by
  obtain ⟨v, envI, hv, hI, hty, hctor, hfield, -⟩ := hcore
  unfold declNames at hnd
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨-, hndC, hTC⟩, hndR, hTCR⟩ := hnd
  have ⟨hordI, hleI⟩ := foldl_addConst_ordered henv hty hI
  -- the constructor fold
  have hcname : ∀ c ∈ decl.types.flatMap (·.ctors),
      c.name ∈ decl.types.flatMap (fun t => t.ctors.map (·.name)) := by
    intro c hc
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 hc
    exact List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨c, hct, rfl⟩⟩
  have hfreshCI : ∀ c ∈ decl.types.flatMap (·.ctors), envI.constants c.name = none := by
    intro c hc
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 hc
    rw [foldlM_addConst_preserve (fun t : VInductiveType => t.name)
      (fun t => ⟨decl.uvars, t.type⟩) hI c.name ?_]
    · exact hfreshC t ht c hct
    · intro t' ht' heq
      exact hTC t'.name (List.mem_map.2 ⟨t', ht', rfl⟩) c.name (hcname c hc) heq
  have hndC' : ((decl.types.flatMap (·.ctors)).map (·.name)).Nodup := by
    rw [List.map_flatMap]; exact hndC
  obtain ⟨envC, hCflat⟩ := foldlM_addConst_exists (fun c : VConstVal => c.name)
    (fun c => ⟨decl.uvars, c.type⟩) hfreshCI hndC'
  have hC := hCflat
  rw [← foldlM_ctors_flat] at hC
  have ⟨hordC, hleC⟩ := foldl_addCtors_ordered hordI hctor hC
  have hleIC : env ≤ envC := hleI.trans hleC
  -- the recursor context is well-formed
  have hlwfT : ∀ t ∈ decl.types, t.type.LevelWF decl.uvars := fun t ht =>
    have ⟨_, h⟩ := hty t ht
    (VEnv.IsDefEq.levelWF h trivial).1
  have hlwfC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.type.LevelWF decl.uvars :=
    fun t ht c hc =>
    have ⟨_, h⟩ := hctor t ht c hc
    (VEnv.IsDefEq.levelWF h trivial).1
  have hconstT : ∀ t ∈ decl.types, envC.constants t.name = some ⟨decl.uvars, t.type⟩ :=
    fun t ht => hleC.constants (addTypeConsts_lookup hI t ht)
  have hconstC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
      envC.constants c.name = some ⟨decl.uvars, c.type⟩ := foldl_addCtors_lookup hC
  have h5 := htele v hv envI envC hI hC hordC
  have hT : RecCtxTypingWF envC (mkRecCtx v le) := {
    params_wf := h5.params_wf
    idx_wf := h5.idx_wf
    type_const := discharge_type_const hleIC hordC hv hconstT hlwfT (hexact v hv).1
    fields_wf := discharge_fields_wf hv hleC fun t ht c hc pf F hF =>
      (hfield t ht c hc pf F hF).1.imp fun _ h => h.1
    ctor_const := discharge_ctor_const hleC hordC hv hconstC hlwfC ((hexact v hv).2.1 envI hI)
    rIndices_fill := h5.rIndices_fill
    recField_tele := h5.recField_tele
    recField_fill := h5.recField_fill }
  have hRec : RecCtxWF envC (mkRecCtx v le) :=
    RecCtxWF.ofViews hv
      (fun t ht => have ⟨_, h⟩ := hty t ht; h.closedN henv trivial)
      (fun t ht c hc => have ⟨_, h⟩ := hctor t ht c hc; h.closedN hordI trivial)
      (hexact v hv).2.2 hT
  -- the recursor fold
  have hrecs : ∀ p ∈ v.types.zipIdx, ∃ T,
      recType (mkRecCtx v le) p.2 = some T ∧
      envC.IsType (mkRecCtx v le).recUvars [] T := by
    intro ⟨t, i⟩ hp
    have h0 : ((mkRecCtx v le).types)[i]? = _ :=
      List.getElem?_map (l := v.types) (i := i)
    rw [mem_zipIdx_getElem? hp] at h0
    exact recType_isType hordC hRec h0
  have hvinv := mkViews_inv hv
  have hvnames : ∀ p ∈ v.types.zipIdx, ∃ t ∈ decl.types, p.1.name = t.name := by
    intro ⟨t', i⟩ hp
    obtain ⟨t, ht, hn, -⟩ := hvinv.2.2.2.2.2 i t' (mem_zipIdx_getElem? hp)
    exact ⟨t, List.mem_of_getElem? ht, hn⟩
  have hfreshRC : ∀ p ∈ v.types.zipIdx, envC.constants (Lean.mkRecName p.1.name) = none := by
    intro p hp
    obtain ⟨t, ht, hn⟩ := hvnames p hp
    have hmemR : Lean.mkRecName t.name ∈ decl.types.map (fun t => Lean.mkRecName t.name) :=
      List.mem_map.2 ⟨t, ht, rfl⟩
    rw [hn, foldlM_addConst_preserve (fun c : VConstVal => c.name)
        (fun c => ⟨decl.uvars, c.type⟩) hCflat _ ?_,
      foldlM_addConst_preserve (fun t : VInductiveType => t.name)
        (fun t => ⟨decl.uvars, t.type⟩) hI _ ?_]
    · exact hfreshR t ht
    · intro t' ht' heq
      exact hTCR _ (List.mem_append_left _ (List.mem_map.2 ⟨t', ht', rfl⟩)) _ hmemR heq
    · intro c hc heq
      exact hTCR _ (List.mem_append_right _ (hcname c hc)) _ hmemR heq
  have hndR' : (v.types.zipIdx.map fun p => Lean.mkRecName p.1.name).Nodup := by
    have hlen := hvinv.2.2.2.2.1
    have : (v.types.zipIdx.map fun p => Lean.mkRecName p.1.name) =
        decl.types.map (fun t => Lean.mkRecName t.name) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
      cases h : v.types[i]? with
      | none =>
        rw [List.getElem?_eq_none_iff] at h
        rw [List.getElem?_eq_none_iff.2 (hlen ▸ h)]
        rfl
      | some t' =>
        obtain ⟨t, ht, hn, -⟩ := hvinv.2.2.2.2.2 i t' h
        rw [ht]
        simp [hn]
    rw [this]; exact hndR
  obtain ⟨envR, hR⟩ := foldlM_addRecs_exists (Θ := mkRecCtx v le)
    (fun p hp => (hrecs p hp).imp fun _ h => h.1) hfreshRC hndR'
  have ⟨_, hleR, hcs⟩ := foldl_addRecs_ordered hordC .rfl hrecs hR
  obtain ⟨rules, hrules, -⟩ := iotaRules_wf hordC hRec hleR fun i t' ht' => by
    have h0 := ht'
    rw [show (mkRecCtx v le).types = v.types.map _ from rfl,
      List.getElem?_map] at h0
    obtain ⟨t, hti, hft⟩ := Option.map_eq_some_iff.1 h0
    obtain ⟨T, hT, hc⟩ := hcs (t, i) (getElem?_mem_zipIdx hti)
    refine ⟨T, hT, ?_⟩
    rw [← hft]
    exact hc
  refine ⟨v, envI, envC, envR, rules, hv, hI, hC, hR, hrules, ?_⟩
  unfold addInductCore
  refine Option.bind_eq_some_iff.2 ⟨v, hv, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨envI, hI, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨envC, hC, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨envR, hR, ?_⟩
  exact Option.bind_eq_some_iff.2 ⟨rules, hrules, rfl⟩

/-- **The recursor context is well-formed under the spec's three predicates**,
at the environment holding the block's type and constructor constants
(the construction inside `addInductCore_exists`, factored for the
producer-side integration, where `envC` is the checker's
constructors-added environment). -/
theorem RecCtxWF.of_wf {env : VEnv} {decl : VInductDecl} {le : Bool}
    (henv : VEnv.Ordered env)
    (hcore : WFCore env decl le) (hexact : WFExact env decl le) (htele : WFTele env decl le)
    {v : View} {envI envC : VEnv}
    (hv : mkViews decl = some v) (hI : addTypeConsts env decl = some envI)
    (hC : decl.types.foldlM (fun env t =>
        t.ctors.foldlM (fun env c => env.addConst c.name ⟨decl.uvars, c.type⟩) env) envI
        = some envC) :
    RecCtxWF envC (mkRecCtx v le) := by
  obtain ⟨v', envI', hv', hI', hty, hctor, hfield, -⟩ := hcore
  cases Option.some.inj (hv.symm.trans hv')
  cases Option.some.inj (hI.symm.trans hI')
  have ⟨hordI, hleI⟩ := foldl_addConst_ordered henv hty hI
  have ⟨hordC, hleC⟩ := foldl_addCtors_ordered hordI hctor hC
  have hleIC : env ≤ envC := hleI.trans hleC
  have hlwfT : ∀ t ∈ decl.types, t.type.LevelWF decl.uvars := fun t ht =>
    have ⟨_, h⟩ := hty t ht
    (VEnv.IsDefEq.levelWF h trivial).1
  have hlwfC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.type.LevelWF decl.uvars :=
    fun t ht c hc =>
    have ⟨_, h⟩ := hctor t ht c hc
    (VEnv.IsDefEq.levelWF h trivial).1
  have hconstT : ∀ t ∈ decl.types, envC.constants t.name = some ⟨decl.uvars, t.type⟩ :=
    fun t ht => hleC.constants (addTypeConsts_lookup hI t ht)
  have hconstC : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
      envC.constants c.name = some ⟨decl.uvars, c.type⟩ := foldl_addCtors_lookup hC
  have h5 := htele v hv envI envC hI hC hordC
  have hT : RecCtxTypingWF envC (mkRecCtx v le) := {
    params_wf := h5.params_wf
    idx_wf := h5.idx_wf
    type_const := discharge_type_const hleIC hordC hv hconstT hlwfT (hexact v hv).1
    fields_wf := discharge_fields_wf hv hleC fun t ht c hc pf F hF =>
      (hfield t ht c hc pf F hF).1.imp fun _ h => h.1
    ctor_const := discharge_ctor_const hleC hordC hv hconstC hlwfC ((hexact v hv).2.1 envI hI)
    rIndices_fill := h5.rIndices_fill
    recField_tele := h5.recField_tele
    recField_fill := h5.recField_fill }
  exact RecCtxWF.ofViews hv
    (fun t ht => have ⟨_, h⟩ := hty t ht; h.closedN henv trivial)
    (fun t ht c hc => have ⟨_, h⟩ := hctor t ht c hc; h.closedN hordI trivial)
    (hexact v hv).2.2 hT

/-! ## Monotonicity of the spec predicates under environment extension

`WFCore`/`WFExact`/`WFTele` transport from an environment to any extension
in which the block's names are still fresh (the extension's own
`addTypeConsts` success pins that). Groundwork for the per-safety packaging
of the `AddInduct` producer: the checker runs against the smallest of the
per-safety models, and the others are extensions. -/

theorem addConst_le_of_le {env env' : VEnv} {n : Name} {ci : VConstant} (hle : env ≤ env')
    (hfr : env.constants n = none) (hfr' : env'.constants n = none) :
    ({ env with constants := fun n' => if n = n' then some ci else env.constants n' } : VEnv) ≤
    { env' with constants := fun n' => if n = n' then some ci else env'.constants n' } := by
  refine ⟨fun {n'} {c} hc => ?_, hle.2⟩
  have hc' : (if n = n' then some ci else env.constants n') = some c := hc
  show (if n = n' then some ci else env'.constants n') = some c
  by_cases hn : n = n'
  · rw [ite_eq_left hn]; rw [ite_eq_left hn] at hc'; exact hc'
  · rw [ite_eq_right hn]; rw [ite_eq_right hn] at hc'; exact hle.1 hc'

theorem addConst_mono' {env env' e : VEnv} {n : Name} {ci : VConstant} (hle : env ≤ env')
    (h : env.addConst n ci = some e) (hfr' : env'.constants n = none) :
    ∃ e', env'.addConst n ci = some e' ∧ e ≤ e' := by
  have hfr : env.constants n = none := by
    unfold VEnv.addConst at h
    cases h0 : env.constants n with
    | some _ => rw [h0] at h; cases h
    | none => rfl
  unfold VEnv.addConst at h ⊢
  rw [hfr] at h; rw [hfr']
  cases h
  exact ⟨_, rfl, addConst_le_of_le hle hfr hfr'⟩

theorem addConst_of_le {env env' e' : VEnv} {n : Name} {ci : VConstant} (hle : env ≤ env')
    (h : env'.addConst n ci = some e') : ∃ e, env.addConst n ci = some e ∧ e ≤ e' := by
  have hfr' : env'.constants n = none := by
    unfold VEnv.addConst at h
    cases h0 : env'.constants n with
    | some _ => rw [h0] at h; cases h
    | none => rfl
  have hfr : env.constants n = none := by
    cases h0 : env.constants n with
    | some c => have := hle.1 h0; rw [hfr'] at this; cases this
    | none => rfl
  unfold VEnv.addConst at h ⊢
  rw [hfr'] at h; rw [hfr]
  cases h
  exact ⟨_, rfl, addConst_le_of_le hle hfr hfr'⟩

theorem addConst_mono2 {env₁ env₂ e₁ e₂ : VEnv} {n : Name} {ci : VConstant} (hle : env₁ ≤ env₂)
    (h₁ : env₁.addConst n ci = some e₁) (h₂ : env₂.addConst n ci = some e₂) : e₁ ≤ e₂ := by
  have hfr₂ : env₂.constants n = none := by
    unfold VEnv.addConst at h₂
    cases h0 : env₂.constants n with
    | some _ => rw [h0] at h₂; cases h₂
    | none => rfl
  obtain ⟨e₂', h₂', hle'⟩ := addConst_mono' hle h₁ hfr₂
  rw [h₂] at h₂'
  cases h₂'
  exact hle'

/-- A fold of environment steps that are monotone and downward-closed. -/
structure StepMono {α : Type} (F : VEnv → α → Option VEnv) : Prop where
  mono : ∀ {env₁ env₂ e₁ e₂ : VEnv} {a : α}, env₁ ≤ env₂ → F env₁ a = some e₁ → F env₂ a = some e₂ →
    e₁ ≤ e₂
  of_le : ∀ {env₁ env₂ e₂ : VEnv} {a : α}, env₁ ≤ env₂ → F env₂ a = some e₂ →
    ∃ e₁, F env₁ a = some e₁ ∧ e₁ ≤ e₂

theorem StepMono.addConst {α : Type} (g : α → Name × VConstant) :
    StepMono fun env a => env.addConst (g a).1 (g a).2 where
  mono hle h₁ h₂ := addConst_mono2 hle h₁ h₂
  of_le hle h₂ := addConst_of_le hle h₂

theorem StepMono.foldlM {α : Type} {F : VEnv → α → Option VEnv} (H : StepMono F) :
    StepMono fun env (l : List α) => l.foldlM F env where
  mono := by
    intro env₁ env₂ e₁ e₂ l
    induction l generalizing env₁ env₂ with
    | nil => intro hle h₁ h₂; cases h₁; cases h₂; exact hle
    | cons a l ih =>
      intro hle h₁ h₂
      simp only [List.foldlM_cons, Option.bind_eq_bind] at h₁ h₂
      obtain ⟨m₁, hm₁, h₁⟩ := Option.bind_eq_some_iff.1 h₁
      obtain ⟨m₂, hm₂, h₂⟩ := Option.bind_eq_some_iff.1 h₂
      exact ih (H.mono hle hm₁ hm₂) h₁ h₂
  of_le := by
    intro env₁ env₂ e₂ l
    induction l generalizing env₁ env₂ with
    | nil => intro hle h₂; cases h₂; exact ⟨_, rfl, hle⟩
    | cons a l ih =>
      intro hle h₂
      simp only [List.foldlM_cons, Option.bind_eq_bind] at h₂ ⊢
      obtain ⟨m₂, hm₂, h₂⟩ := Option.bind_eq_some_iff.1 h₂
      obtain ⟨m₁, hm₁, hlem⟩ := H.of_le hle hm₂
      obtain ⟨e₁, h₁, hle'⟩ := ih hlem h₂
      exact ⟨e₁, by rw [hm₁]; exact h₁, hle'⟩

theorem addTypeConsts_stepMono (decl : VInductDecl) :
    StepMono fun env (t : VInductiveType) => env.addConst t.name ⟨decl.uvars, t.type⟩ :=
  StepMono.addConst fun (t : VInductiveType) => (t.name, ⟨decl.uvars, t.type⟩)

theorem addTypeConsts_mono {env env' envI envI' : VEnv} {decl : VInductDecl} (hle : env ≤ env')
    (hI : addTypeConsts env decl = some envI) (hI' : addTypeConsts env' decl = some envI') :
    envI ≤ envI' :=
  ((addTypeConsts_stepMono decl).foldlM).mono hle hI hI'

theorem addTypeConsts_of_le {env env' envI' : VEnv} {decl : VInductDecl} (hle : env ≤ env')
    (hI' : addTypeConsts env' decl = some envI') :
    ∃ envI, addTypeConsts env decl = some envI ∧ envI ≤ envI' :=
  ((addTypeConsts_stepMono decl).foldlM).of_le hle hI'

/-- The constructor fold of `addInductCore`/`WFTele`. -/
def ctorFoldF (decl : VInductDecl) (env : VEnv) (t : VInductiveType) : Option VEnv :=
  t.ctors.foldlM (fun env c => env.addConst c.name ⟨decl.uvars, c.type⟩) env

theorem ctorFold_stepMono (decl : VInductDecl) : StepMono (ctorFoldF decl) where
  mono hle h₁ h₂ := ((StepMono.addConst fun (c : VConstVal) => (c.name, ⟨decl.uvars, c.type⟩)).foldlM).mono hle h₁ h₂
  of_le hle h₂ := ((StepMono.addConst fun (c : VConstVal) => (c.name, ⟨decl.uvars, c.type⟩)).foldlM).of_le hle h₂

theorem ctorFold_mono {env env' e e' : VEnv} {decl : VInductDecl} (hle : env ≤ env')
    (h : decl.types.foldlM (ctorFoldF decl) env = some e)
    (h' : decl.types.foldlM (ctorFoldF decl) env' = some e') : e ≤ e' :=
  ((ctorFold_stepMono decl).foldlM).mono hle h h'

theorem ctorFold_of_le {env env' e' : VEnv} {decl : VInductDecl} (hle : env ≤ env')
    (h' : decl.types.foldlM (ctorFoldF decl) env' = some e') :
    ∃ e, decl.types.foldlM (ctorFoldF decl) env = some e ∧ e ≤ e' :=
  ((ctorFold_stepMono decl).foldlM).of_le hle h'

theorem Positive.mono {env env' : VEnv} (hle : env ≤ env') {U : Nat} {names : List Name}
    {nidx : List Nat} {np : Nat} :
    ∀ {Γ : List VExpr} {A : VExpr}, Positive env U names nidx np Γ A →
      Positive env' U names nidx np Γ A
  | _, _, .noOcc h => .noOcc h
  | _, _, .validApp h => .validApp h
  | _, _, .arrow h1 h2 => .arrow h1 (Positive.mono hle h2)
  | _, _, .defeq h1 h2 => .defeq (h1.mono hle) (Positive.mono hle h2)

theorem LargeElimOk.mono {env env' : VEnv} (hle : env ≤ env') {v : View}
    (h : LargeElimOk env v) : LargeElimOk env' v := by
  unfold LargeElimOk at h ⊢
  rcases h with h | h
  · exact .inl h
  · right
    split at h <;> try exact h
    split at h <;> try exact h
    intro pf F hF
    rcases h pf F hF with ⟨u, hu, hz⟩ | h
    · exact .inl ⟨u, hu.mono hle, hz⟩
    · exact .inr h

theorem RecCtxTelescopeWF.mono {env env' : VEnv} (hle : env ≤ env') {Θ : RecCtx}
    (h : RecCtxTelescopeWF env Θ) : RecCtxTelescopeWF env' Θ where
  params_wf := h.params_wf.mono hle
  idx_wf t ht := (h.idx_wf t ht).mono hle
  rIndices_fill i t ht c hc := (h.rIndices_fill i t ht c hc).mono hle
  recField_tele t ht c hc pf xs it ris hm := (h.recField_tele t ht c hc pf xs it ris hm).mono hle
  recField_fill t ht c hc pf xs it ris hm t' ht' :=
    (h.recField_fill t ht c hc pf xs it ris hm t' ht').mono hle

theorem WFCore.mono {env env' envI' : VEnv} {decl : VInductDecl} {le : Bool} (hle : env ≤ env')
    (hI' : addTypeConsts env' decl = some envI') (h : WFCore env decl le) : WFCore env' decl le := by
  obtain ⟨v, envI, hv, hI, hty, hcty, hfields, hlarge⟩ := h
  have hleI : envI ≤ envI' := addTypeConsts_mono hle hI hI'
  refine ⟨v, envI', hv, hI', fun t ht => (hty t ht).mono hle,
    fun t ht c hc => (hcty t ht c hc).mono hleI, fun t ht c hc pf F hF => ?_,
    fun hl => (hlarge hl).mono hleI⟩
  obtain ⟨⟨u, hu, hb⟩, hpos⟩ := hfields t ht c hc pf F hF
  exact ⟨⟨u, hu.mono hleI, hb⟩, hpos.mono hleI⟩

theorem WFExact.mono {env env' : VEnv} {decl : VInductDecl} {le : Bool} (hle : env ≤ env')
    (h : WFExact env decl le) : WFExact env' decl le := by
  intro v hv
  obtain ⟨h1, h2, h3⟩ := h v hv
  refine ⟨fun t ht rest hr => ?_, fun envI' hI' t ht c hc restc hr => ?_, h3⟩
  · obtain ⟨u, hu⟩ := h1 t ht rest hr
    exact ⟨u, hu.mono hle⟩
  · obtain ⟨envI, hI, hleI⟩ := addTypeConsts_of_le hle hI'
    obtain ⟨u, hu⟩ := h2 envI hI t ht c hc restc hr
    exact ⟨u, hu.mono hleI⟩

theorem Ordered.foldlM_addConst {α : Type} (g : α → Name × VConstant) :
    ∀ {l : List α} {env env' : VEnv}, VEnv.Ordered env →
    (∀ a ∈ l, (g a).2.WF env) →
    l.foldlM (fun env a => env.addConst (g a).1 (g a).2) env = some env' → VEnv.Ordered env'
  | [], _, _, h, _, e => by cases e; exact h
  | a :: l, env, env', h, hw, e => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at e
    obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 e
    exact Ordered.foldlM_addConst g (.const h (hw a (.head _)) h1)
      (fun b hb => (hw b (.tail _ hb)).mono (VEnv.addConst_le h1)) h2

theorem foldlM_addConst_le' {α : Type} (g : α → Name × VConstant) :
    ∀ {l : List α} {env env' : VEnv},
    l.foldlM (fun env a => env.addConst (g a).1 (g a).2) env = some env' → env ≤ env'
  | [], _, _, e => by cases e; exact .rfl
  | a :: l, env, env', e => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at e
    obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 e
    exact (VEnv.addConst_le h1).trans (foldlM_addConst_le' g h2)

theorem WFTele.mono {env env' : VEnv} {decl : VInductDecl} {le : Bool} (hle : env ≤ env')
    (hord : VEnv.Ordered env) (hcore : WFCore env decl le) (h : WFTele env decl le) :
    WFTele env' decl le := by
  intro v hv envI' envC' hI' hC' hordC'
  obtain ⟨envI, hI, hleI⟩ := addTypeConsts_of_le hle hI'
  obtain ⟨envC, hC, hleC⟩ := ctorFold_of_le (decl := decl) hleI hC'
  obtain ⟨v₀, envI₀, hv₀, hI₀, hty, hcty, -, -⟩ := hcore
  have hv₀' : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hI₀' : envI₀ = envI := Option.some.inj (hI₀.symm.trans hI)
  subst envI₀
  have hordI : VEnv.Ordered envI :=
    Ordered.foldlM_addConst (fun t : VInductiveType => (t.name, ⟨decl.uvars, t.type⟩)) hord
      (fun t ht => hty t ht) hI
  have hordC : VEnv.Ordered envC := by
    have hstep : ∀ {l : List VInductiveType} {e e' : VEnv}, VEnv.Ordered e → envI ≤ e →
        (∀ t ∈ l, ∀ c ∈ t.ctors, envI.IsType decl.uvars [] c.type) →
        l.foldlM (ctorFoldF decl) e = some e' → VEnv.Ordered e' := by
      intro l
      induction l with
      | nil => intro e e' h _ _ he; cases he; exact h
      | cons t l ih =>
        intro e e' h hle' hw he
        simp only [List.foldlM_cons, Option.bind_eq_bind] at he
        obtain ⟨e₁, h1, h2⟩ := Option.bind_eq_some_iff.1 he
        have h1' : VEnv.Ordered e₁ :=
          Ordered.foldlM_addConst (fun c : VConstVal => (c.name, ⟨decl.uvars, c.type⟩)) h
            (fun c hc => (hw t (.head _) c hc).mono hle') h1
        have hle₁ : envI ≤ e₁ := hle'.trans (foldlM_addConst_le'
          (fun c : VConstVal => (c.name, ⟨decl.uvars, c.type⟩)) h1)
        exact ih h1' hle₁ (fun t' ht' c hc => hw t' (.tail _ ht') c hc) h2
    exact hstep hordI .rfl hcty hC
  exact (h v hv envI envC hI hC hordC).mono hleC

/-! ### Existence of the type-constant fold, and monotonicity of the core fold -/

theorem addConst_constants_ne {env e : VEnv} {n n' : Lean.Name} {ci : VConstant}
    (h : env.addConst n ci = some e) (hne : n ≠ n') : e.constants n' = env.constants n' := by
  unfold VEnv.addConst at h
  cases h0 : env.constants n with
  | some _ => rw [h0] at h; cases h
  | none =>
    rw [h0] at h
    cases h
    show (if n = n' then some ci else env.constants n') = env.constants n'
    rw [ite_eq_right hne]

theorem addConst_exists_of_none {env : VEnv} {n : Lean.Name} {ci : VConstant}
    (h0 : env.constants n = none) : ∃ e, env.addConst n ci = some e := by
  unfold VEnv.addConst
  rw [h0]
  exact ⟨_, rfl⟩

theorem foldlM_addConst_exists₂ {α : Type} (g : α → Lean.Name × VConstant) :
    ∀ {l : List α} {env : VEnv},
    (∀ a ∈ l, env.constants (g a).1 = none) → (l.map fun a => (g a).1).Nodup →
    ∃ env', l.foldlM (fun env a => env.addConst (g a).1 (g a).2) env = some env'
  | [], env, _, _ => ⟨env, rfl⟩
  | a :: l, env, hfr, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨e, hadd⟩ := addConst_exists_of_none (ci := (g a).2) (hfr a (.head _))
    obtain ⟨env', h'⟩ := foldlM_addConst_exists₂ g (l := l) (env := e) (fun b hb => by
      rw [addConst_constants_ne hadd (fun h => hnd.1 (List.mem_map.2 ⟨b, hb, h.symm⟩))]
      exact hfr b (.tail _ hb)) hnd.2
    exact ⟨env', by rw [List.foldlM_cons, hadd]; exact h'⟩

theorem addTypeConsts_exists {env : VEnv} {decl : VInductDecl}
    (hfr : ∀ t ∈ decl.types, env.constants t.name = none)
    (hnd : (decl.types.map (·.name)).Nodup) : ∃ envI, addTypeConsts env decl = some envI :=
  foldlM_addConst_exists₂ (fun t : VInductiveType => (t.name, ⟨decl.uvars, t.type⟩)) hfr hnd

theorem addDefEq_le {env₁ env₂ : VEnv} {df : VDefEq} (H : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df where
  constants := H.constants
  defeqs := by rintro d (rfl | hd) <;> [exact .inl rfl; exact .inr (H.defeqs hd)]

theorem addDefEq_foldl_mono : ∀ (rules : List VDefEq) {env env' : VEnv}, env ≤ env' →
    rules.foldl VEnv.addDefEq env ≤ rules.foldl VEnv.addDefEq env'
  | [], _, _, h => h
  | _ :: rs, _, _, h => addDefEq_foldl_mono rs (addDefEq_le h)

theorem addInductCore_mono {env env' e e' : VEnv} {decl : VInductDecl} {le : Bool}
    (hle : env ≤ env') (h : addInductCore env decl le = some e)
    (h' : addInductCore env' decl le = some e') : e ≤ e' := by
  unfold addInductCore at h h'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h h'
  obtain ⟨v, hv, envI, hI, envC, hC, envR, hR, rules, hrules, rfl⟩ := h
  obtain ⟨v', hv', envI', hI', envC', hC', envR', hR', rules', hrules', rfl⟩ := h'
  cases hv.symm.trans hv'
  have h1 : envI ≤ envI' := addTypeConsts_mono hle hI hI'
  have h2 : envC ≤ envC' := ctorFold_mono h1 hC hC'
  have h3 : envR ≤ envR' := (StepMono.foldlM ?SM).mono h2 hR hR'
  case SM =>
    refine ⟨?_, ?_⟩
    · rintro _ _ _ _ ⟨t, i⟩ hle h1 h2
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
      obtain ⟨ty, hty, h1⟩ := h1
      obtain ⟨ty', hty', h2⟩ := h2
      cases hty.symm.trans hty'
      exact addConst_mono2 hle h1 h2
    · rintro _ _ _ ⟨t, i⟩ hle h2
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h2 ⊢
      obtain ⟨ty, hty, h2⟩ := h2
      obtain ⟨e₁, he₁, hle₁⟩ := addConst_of_le hle h2
      exact ⟨e₁, ⟨ty, hty, he₁⟩, hle₁⟩
  cases hrules.symm.trans hrules'
  exact addDefEq_foldl_mono rules h3

end IndSpec
end Lean4Lean
