import VCVio

open OracleComp OracleSpec

section simp_lemmas -- Some extra lemmas that still need to move to vcv

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ ω : Type u}

variable {m : Type u → Type v} [Monad m]
variable [HasEvalSPMF m] {mx : m α} {p q : α → Prop}

-- probFailure_bind_eq_zero_iff and loggingOracle.probFailure_simulateQ are in VCVio

namespace OptionT

lemma probFailure_mk {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (mx : m (Option α)) :
    Pr[⊥ | (OptionT.mk mx : OptionT m α)] = Pr[⊥ | mx] + Pr[= none | mx] := by
  simpa using (OptionT.probFailure_eq (m := m) (mx := (OptionT.mk mx : OptionT m α)))

lemma probEvent_mk {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (p : α → Prop) [DecidablePred p] (mx : m (Option α)) :
    Pr[p | (OptionT.mk mx : OptionT m α)] + Pr[= none | mx] = Pr[fun o => o.all p | mx] := by
  simpa using (OptionT.probEvent_eq (m := m) (mx := (OptionT.mk mx : OptionT m α)) (p := p))

@[simp]
lemma support_mk {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (mx : m (Option α)) :
    support (OptionT.mk mx : OptionT m α) = {x | some x ∈ support mx} := by
  ext x
  simp [OptionT.mem_support_iff]

@[simp]
lemma mem_support_mk {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (mx : m (Option α)) (x : α) :
    x ∈ support (OptionT.mk mx : OptionT m α) ↔ some x ∈ support mx := by
  simp [support_mk]

/-- Convenience name for support of `OptionT.pure`. -/
@[simp]
lemma support_OptionT_pure {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (x : α) :
    support (OptionT.pure x : OptionT m α) = {x} := by
  change support (pure x : OptionT m α) = {x}
  simp only [(_root_.support_pure (m := OptionT m) x)]

/-- Run-level support form of `OptionT.pure` (output is `some x`). -/
@[simp]
lemma support_OptionT_pure_run {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (x : α) :
    support (m := m) (α := Option α) (OptionT.pure x) = {some x} := by
  change support (pure (some x) : m (Option α)) = {some x}
  simp

/-- Run-level `some` membership form for `OptionT.pure`. -/
@[simp]
lemma mem_support_OptionT_pure_run_some_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (x y : α) :
    some y ∈ support (m := m) (α := Option α) (OptionT.pure x) ↔ y = x := by
  simp [support_OptionT_pure_run]

/-- OptionT-native alias of generic `probFailure_pure`. -/
@[simp]
lemma probFailure_OptionT_pure {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α : Type u} (x : α) :
    Pr[⊥ | (OptionT.pure x : OptionT m α)] = 0 := by
  change Pr[⊥ | (pure x : OptionT m α)] = 0
  simpa using (_root_.probFailure_pure (m := OptionT m) x)

/-- OptionT-native alias of generic `support_bind`. -/
@[simp]
lemma support_bind {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β : Type u} (mx : OptionT m α) (my : α → OptionT m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by
  simpa using (_root_.support_bind (m := OptionT m) mx my)

/-- OptionT-native alias of generic `mem_support_bind_iff`. -/
lemma mem_support_bind_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β : Type u} (mx : OptionT m α) (my : α → OptionT m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by
  simpa using (_root_.mem_support_bind_iff (m := OptionT m) mx my y)

/-- Bridge lemma to reason about failure of `OptionT.mk` over a monadic bind. -/
@[simp]
lemma probFailure_mk_bind_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    [LawfulMonad m]
    {α β : Type u} (mx : m α) (my : α → m (Option β)) :
    Pr[⊥ | (OptionT.mk (mx >>= my) : OptionT m β)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | (OptionT.mk (my x) : OptionT m β)] = 0 := by
  have h_bind_as_lift :
      (OptionT.mk (mx >>= my) : OptionT m β) =
        (((liftM (n := OptionT m) mx) >>= fun x => (OptionT.mk (my x) : OptionT m β)) :
          OptionT m β) := by
    simp
  rw [h_bind_as_lift]
  rw [probFailure_bind_eq_zero_iff]
  constructor
  · intro h
    constructor
    · simpa [OptionT.probFailure_liftM] using h.1
    · intro x hx
      have hx_lift : x ∈ support ((liftM (n := OptionT m) mx) : OptionT m α) := by
        simpa [OptionT.support_liftM] using hx
      exact h.2 x hx_lift
  · intro h
    constructor
    · simpa [OptionT.probFailure_liftM] using h.1
    · intro x hx
      have hx_base : x ∈ support mx := by
        simpa [OptionT.support_liftM] using hx
      exact h.2 x hx_base

/-- `do`-notation variant of `probFailure_mk_bind_eq_zero_iff`. -/
@[simp]
lemma probFailure_mk_do_bind_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    [LawfulMonad m]
    {α β : Type u} (mx : m α) (my : α → m (Option β)) :
    Pr[⊥ | (OptionT.mk (do
      let x ← mx
      my x) : OptionT m β)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | (OptionT.mk (my x) : OptionT m β)] = 0 := by
  simp only [mk_bind, probFailure_bind_eq_zero_iff, probFailure_liftM, support_liftM]

/-- Two-bind `do`-notation variant for easier rewriting of chained programs. -/
@[simp]
lemma probFailure_mk_do_bind_bind_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    [LawfulMonad m]
    {α β γ : Type u} (mx : m α) (my : α → m β) (mz : α → β → m (Option γ)) :
    Pr[⊥ | (OptionT.mk (do
      let x ← mx
      let y ← my x
      mz x y) : OptionT m γ)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx,
        Pr[⊥ | (OptionT.mk (do
          let y ← my x
          mz x y) : OptionT m γ)] = 0 := by
  simp only [mk_bind, probFailure_bind_eq_zero_iff, probFailure_liftM, support_liftM]

/-- `OptionT`-do-bind variant: use when the `do` block under `OptionT.mk` is in `OptionT`. -/
lemma probFailure_mk_do_bindT_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β : Type u} (mx : OptionT m α) (my : α → OptionT m β) :
    Pr[⊥ | (OptionT.mk ((do
      let x ← mx
      my x) : OptionT m β) : OptionT m β)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  change Pr[⊥ | ((do
    let x ← mx
    my x) : OptionT m β)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0
  exact (probFailure_bind_eq_zero_iff (mx := mx) (my := my))

/-- Two-bind `OptionT`-do variant for chained programs under `OptionT.mk`. -/
lemma probFailure_mk_do_bind_bindT_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β γ : Type u} (mx : OptionT m α) (my : α → OptionT m β) (mz : α → β → OptionT m γ) :
    Pr[⊥ | (OptionT.mk ((do
      let x ← mx
      let y ← my x
      mz x y) : OptionT m γ) : OptionT m γ)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧
        ∀ x ∈ support mx,
          Pr[⊥ | (OptionT.mk ((do
            let y ← my x
            mz x y) : OptionT m γ) : OptionT m γ)] = 0 := by
  change Pr[⊥ | ((do
    let x ← mx
    let y ← my x
    mz x y) : OptionT m γ)] = 0 ↔
      Pr[⊥ | mx] = 0 ∧
        ∀ x ∈ support mx,
          Pr[⊥ | ((do
          let y ← my x
          mz x y) : OptionT m γ)] = 0
  rw [probFailure_bind_eq_zero_iff]

/-- Binding into `OptionT.pure` preserves failure-freedom (`= 0`). -/
@[simp]
lemma probFailure_bind_pure_comp_eq_zero_iff {m : Type u → Type v} [Monad m] [HasEvalSPMF m]
    {α β : Type u} (mx : OptionT m α) (f : α → β) :
    Pr[⊥ | OptionT.bind mx (OptionT.pure ∘ f)] = 0 ↔ Pr[⊥ | mx] = 0 := by
  change Pr[⊥ | mx >>= (OptionT.pure ∘ f)] = 0 ↔ Pr[⊥ | mx] = 0
  rw [probFailure_bind_eq_zero_iff]
  constructor
  · intro h
    exact h.1
  · intro hmx
    constructor
    · exact hmx
    · intro x hx
      have h_pure : Pr[⊥ | (OptionT.pure (f x) : OptionT m β)] = 0 := by
        simpa using (probFailure_OptionT_pure (m := m) (x := f x))
      simpa only [Function.comp_apply] using h_pure

/-- Expand failure of lifted `OptionT` simulation into run-failure + `none` mass. -/
@[simp]
lemma probFailure_simulateQ_liftQuery_eq
    {ι' : Type w} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited]
    [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α : Type u} (oa : OptionT (OracleComp spec) α) :
    Pr[⊥ | (liftM oa : OptionT (OracleComp superSpec) α)] =
      Pr[⊥ | simulateQ (fun t ↦
        (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa] +
      Pr[= none | simulateQ (fun t ↦
        (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa] := by
  simpa [OracleComp.liftM_OptionT_eq] using
    (OptionT.probFailure_eq (mx := (liftM oa : OptionT (OracleComp superSpec) α)))

/-- `= 0` form of `probFailure_simulateQ_liftQuery_eq`. -/
@[simp]
lemma probFailure_simulateQ_liftQuery_eq_zero_iff
    {ι' : Type w} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited]
    [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α : Type u} (oa : OptionT (OracleComp spec) α) :
    Pr[⊥ | (liftM oa : OptionT (OracleComp superSpec) α)] = 0 ↔
      Pr[⊥ | simulateQ (fun t ↦
        (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa] = 0 ∧
      Pr[= none | simulateQ (fun t ↦
        (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa] = 0 := by
  rw [probFailure_simulateQ_liftQuery_eq (oa := oa), add_eq_zero]

/-- Run-level support membership bridge for `simulateQ ...` vs `liftM` on `OptionT` computations. -/
@[simp]
lemma mem_support_simulateQ_liftQuery_iff
    {ι' : Type w} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited]
    [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α : Type u} (oa : OptionT (OracleComp spec) α) (x : Option α) :
    x ∈ support (m := OracleComp superSpec) (α := Option α)
      (simulateQ (fun t ↦ (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa) ↔
    x ∈ support (m := OracleComp superSpec) (α := Option α)
      ((liftM oa : OptionT (OracleComp superSpec) α)) := by
  change x ∈ support (m := OracleComp superSpec) (α := Option α)
      (simulateQ (fun t ↦ (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa) ↔
    x ∈ support (m := OracleComp superSpec) (α := Option α)
      (simulateQ (fun t ↦ (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa)
  exact Iff.rfl

/-- Specialized `some` form of `mem_support_simulateQ_liftQuery_iff`. -/
@[simp]
lemma mem_support_simulateQ_liftQuery_some_iff
    {ι' : Type w} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited]
    [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α : Type u} (oa : OptionT (OracleComp spec) α) (x : α) :
    some x ∈ support (m := OracleComp superSpec) (α := Option α)
      (simulateQ (fun t ↦ (liftM (query (spec := spec) t) : OracleComp superSpec _)) oa) ↔
    some x ∈ support (m := OracleComp superSpec) (α := Option α)
      ((liftM oa : OptionT (OracleComp superSpec) α)) := by
  simpa using (mem_support_simulateQ_liftQuery_iff
    (spec := spec) (superSpec := superSpec) (oa := oa) (x := some x))

end OptionT

@[simp]
lemma probFailure_liftComp {ι' : Type w} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : Pr[⊥ | liftComp oa superSpec] = Pr[⊥ | oa] := by
  rw [liftComp_eq_liftM]; simp only [HasEvalPMF.probFailure_eq_zero]

/-- Monad-lifting preserves the failure probability. -/
@[simp]
lemma probFailure_liftM {ι' : Type w} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) :
    Pr[⊥ | (liftM oa : OracleComp superSpec α)] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- Spec-lifting preserves the failure probability. -/
@[simp]
lemma probFailure_liftComp_eq {ι' : Type} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : Pr[⊥ | liftComp oa superSpec] = Pr[⊥ | oa] := by
  rw [liftComp_eq_liftM]; simp only [HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma liftComp_support {ι' : Type w} {superSpec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited] [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : support (liftComp oa superSpec) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa h =>
    rw [liftComp_bind, support_bind, support_bind]
    have hq : support (liftComp (query t : OracleComp spec _) superSpec) = Set.univ := by
      simp only [liftComp_eq_liftM]
      sorry
    have hq' : support (query t : OracleComp spec _) = Set.univ := OracleComp.support_query t
    rw [hq, hq', Set.biUnion_univ, Set.biUnion_univ]
    simp_rw [h]

/-- Map preserves NeverFail. -/
lemma neverFail_map_iff' [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) (f : α → β) :
    NeverFail (f <$> oa) ↔ NeverFail oa :=
  HasEvalSPMF.neverFail_map_iff oa f

/-- Bridge between monadic support and deterministic results for pure ProbComp. -/
@[simp]
lemma support_pure_bind_pure {α β : Type} (x : α) (f : α → ProbComp β) :
    support (pure x >>= f) = support (f x) :=
  by simp only [pure_bind]

alias support_pure_bind := support_pure_bind_pure

/-- Split support membership for a mapped pair constructor. -/
@[simp]
lemma mem_support_map_prod_mk_iff [LawfulMonad m]
    {α β : Type u} (a : α) (mx : m β) (z : α × β) :
    z ∈ support (Prod.mk a <$> mx) ↔
      ∃ b ∈ support mx, (a, b) = z := by
  simp only [support_map, Set.mem_image]

/-- Split support membership for a two-bind chain ending in a mapped payload. -/
@[simp]
lemma mem_support_bind_bind_map_iff [LawfulMonad m]
    {α β γ ω : Type u}
    (mx : m α) (my : α → m β) (mz : α → β → m γ)
    (f : α → β → γ → ω) (z : ω) :
    z ∈ support (do
      let x ← mx
      let y ← my x
      f x y <$> mz x y) ↔
      ∃ x ∈ support mx,
        ∃ y ∈ support (my x),
          ∃ u ∈ support (mz x y), f x y u = z := by
  constructor
  · intro hz
    rcases (mem_support_bind_iff (mx := mx)
      (my := fun x => do
        let y ← my x
        f x y <$> mz x y) (y := z)).1 hz with ⟨x, hx, hz1⟩
    rcases (mem_support_bind_iff (mx := my x)
      (my := fun y => f x y <$> mz x y) (y := z)).1 hz1 with ⟨y, hy, hz2⟩
    rw [support_map] at hz2
    rcases hz2 with ⟨u, hu, h_eq⟩
    exact ⟨x, hx, y, hy, u, hu, h_eq⟩
  · rintro ⟨x, hx, y, hy, u, hu, h_eq⟩
    apply (mem_support_bind_iff (mx := mx)
      (my := fun x => do
        let y ← my x
        f x y <$> mz x y) (y := z)).2
    refine ⟨x, hx, ?_⟩
    apply (mem_support_bind_iff (mx := my x)
      (my := fun y => f x y <$> mz x y) (y := z)).2
    refine ⟨y, hy, ?_⟩
    rw [support_map]
    exact ⟨u, hu, h_eq⟩

/-- Generic 1-step map support extraction. -/
@[simp]
lemma mem_support_map_iff_generic {m : Type u → Type v} [Monad m] [HasEvalSPMF m] [LawfulMonad m]
    {α β : Type u} (mx : m α) (f : α → β) (y : β) :
    y ∈ support (f <$> mx) ↔ ∃ x ∈ support mx, f x = y := by
  simp only [support_map, Set.mem_image]

/-- Extract support from a 2-bind do block ending in a map, for ANY output type including Options. -/
@[simp]
lemma mem_support_bind_bind_map_generic_iff [LawfulMonad m]
    {α β γ ω : Type u}
    (mx : m α) (my : α → m β) (mz : α → β → m γ)
    (g : α → β → γ → ω) (z : ω) :
    z ∈ support (do
      let x ← mx
      let y ← my x
      g x y <$> mz x y) ↔
      ∃ x ∈ support mx,
        ∃ y ∈ support (my x),
          ∃ u ∈ support (mz x y), g x y u = z := by
  constructor
  · intro hz
    rcases (mem_support_bind_iff (mx := mx)
      (my := fun x => do let y ← my x; g x y <$> mz x y) (y := z)).1 hz with ⟨x, hx, hz1⟩
    rcases (mem_support_bind_iff (mx := my x)
      (my := fun y => g x y <$> mz x y) (y := z)).1 hz1 with ⟨y, hy, hz2⟩
    rw [support_map] at hz2
    rcases hz2 with ⟨u, hu, h_eq⟩
    exact ⟨x, hx, y, hy, u, hu, h_eq⟩
  · rintro ⟨x, hx, y, hy, u, hu, h_eq⟩
    apply (mem_support_bind_iff (mx := mx)
      (my := fun x => do let y ← my x; g x y <$> mz x y) (y := z)).2
    refine ⟨x, hx, ?_⟩
    apply (mem_support_bind_iff (mx := my x)
      (my := fun y => g x y <$> mz x y) (y := z)).2
    refine ⟨y, hy, ?_⟩
    rw [support_map]
    exact ⟨u, hu, h_eq⟩

namespace OptionT

/-- `some`-output support decomposition for a bind in the base monad. -/
@[simp]
lemma mem_support_bind_some_iff {α β : Type u}
    (ma : m α) (mb : α → m (Option β)) (y : β) :
    some y ∈ support (ma >>= mb) ↔
      ∃ x ∈ support ma, some y ∈ support (mb x) := by
  simpa using (mem_support_bind_iff (mx := ma) (my := mb) (y := some y))

/-- `some`-output support decomposition for a map in the base monad. -/
@[simp]
lemma mem_support_map_some_iff [LawfulMonad m] {α β : Type u}
    (ma : m α) (f : α → Option β) (y : β) :
    some y ∈ support (f <$> ma) ↔
      ∃ x ∈ support ma, f x = some y := by
  simp only [support_map, Set.mem_image]

/-- `OptionT.run` + bind decomposition for successful (`some`) outputs. -/
@[simp]
lemma mem_support_run_bind_some_iff {α β : Type u}
    (ma : OptionT m α) (mb : α → OptionT m β) (y : β) :
    some y ∈ support (OptionT.run (ma >>= mb)) ↔
      ∃ x ∈ support ma, some y ∈ support (OptionT.run (mb x)) := by
  constructor
  · intro hy
    have hy' : y ∈ support (ma >>= mb) := (OptionT.mem_support_iff (mx := ma >>= mb) (x := y)).2 hy
    rcases (OptionT.mem_support_bind_iff (mx := ma) (my := mb) (y := y)).1 hy' with ⟨x, hx, hyx⟩
    exact ⟨x, hx, (OptionT.mem_support_iff (mx := mb x) (x := y)).1 hyx⟩
  · rintro ⟨x, hx, hyx⟩
    have hy' : y ∈ support (mb x) := (OptionT.mem_support_iff (mx := mb x) (x := y)).2 hyx
    have hbind : y ∈ support (ma >>= mb) :=
      (OptionT.mem_support_bind_iff (mx := ma) (my := mb) (y := y)).2 ⟨x, hx, hy'⟩
    exact (OptionT.mem_support_iff (mx := ma >>= mb) (x := y)).1 hbind

/-- Base-support decomposition for `OptionT.bind` (explicit run-level shape). -/
@[simp]
lemma mem_support_OptionT_bind_run_some_iff [LawfulMonad m] {α β : Type u}
    (ma : OptionT m α) (mb : α → OptionT m β) (y : β) :
    some y ∈ support (m := m) (α := Option β) (OptionT.bind ma mb) ↔
      ∃ x, some x ∈ support (m := m) (α := Option α) ma ∧
        some y ∈ support (m := m) (α := Option β) (mb x) := by
  change some y ∈ support (OptionT.run (ma >>= mb)) ↔
      ∃ x, some x ∈ support (OptionT.run ma) ∧
        some y ∈ support (OptionT.run (mb x))
  rw [mem_support_run_bind_some_iff (ma := ma) (mb := mb) (y := y)]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, (OptionT.mem_support_iff (mx := ma) (x := x)).1 hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, (OptionT.mem_support_iff (mx := ma) (x := x)).2 hx, hy⟩

/-- Specialized `OptionT.bind`-to-`OptionT.pure` support decomposition. -/
@[simp]
lemma mem_support_OptionT_bind_pure_comp_run_some_iff [LawfulMonad m] {α β : Type u}
    (ma : OptionT m α) (f : α → β) (y : β) :
    some y ∈ support (m := m) (α := Option β) (OptionT.bind ma (OptionT.pure ∘ f)) ↔
      ∃ x, some x ∈ support (m := m) (α := Option α) ma ∧ f x = y := by
  rw [mem_support_OptionT_bind_run_some_iff (ma := ma) (mb := OptionT.pure ∘ f) (y := y)]
  constructor
  · rintro ⟨x, hx, hy⟩
    have hs : some y = some (f x) := by
      simpa [Function.comp, OptionT.pure, OptionT.mk, support_pure, Set.mem_singleton_iff] using hy
    exact ⟨x, hx, by simpa using hs.symm⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    simpa [Function.comp, OptionT.pure, OptionT.mk, support_pure, Set.mem_singleton_iff, hxy]

/-- `OptionT.run` + map decomposition for successful (`some`) outputs. -/
@[simp]
lemma mem_support_run_map_some_iff [LawfulMonad m] {α β : Type u}
    (ma : OptionT m α) (f : α → β) (y : β) :
    some y ∈ support (OptionT.run (f <$> ma)) ↔
      ∃ x ∈ support ma, f x = y := by
  constructor
  · intro hy
    have hy' : y ∈ support (f <$> ma) := (OptionT.mem_support_iff (mx := f <$> ma) (x := y)).2 hy
    exact (mem_support_map_iff_generic (mx := ma) (f := f) (y := y)).1 hy'
  · rintro ⟨x, hx, hxy⟩
    have hy' : y ∈ support (f <$> ma) :=
      (mem_support_map_iff_generic (mx := ma) (f := f) (y := y)).2 ⟨x, hx, hxy⟩
    exact (OptionT.mem_support_iff (mx := f <$> ma) (x := y)).1 hy'

---------------------------------------------------------------
/-- Extract a successful path natively from an OptionT bind. -/
@[simp]
lemma mem_support_OptionT_bind_some {m : Type u → Type v} [Monad m] [HasEvalSPMF m] [LawfulMonad m]
    {α β : Type u} (ma : OptionT m α) (mb : α → OptionT m β) (y : β) :
    y ∈ support (ma >>= mb) ↔
      ∃ x ∈ support ma, y ∈ support (mb x) := by
  simpa using (OptionT.mem_support_bind_iff (mx := ma) (my := mb) (y := y))

/-- Successful-path decomposition for bind at `OptionT.run` level. -/
@[simp]
lemma mem_support_OptionT_run_bind_some {m : Type u → Type v} [Monad m] [HasEvalSPMF m] [LawfulMonad m]
    {α β : Type u} (ma : OptionT m α) (mb : α → OptionT m β) (y : β) :
    some y ∈ support (OptionT.run (ma >>= mb)) ↔
      ∃ x ∈ support ma, some y ∈ support (OptionT.run (mb x)) := by
  simpa using mem_support_run_bind_some_iff (ma := ma) (mb := mb) (y := y)

/-- Extract a mapped successful value natively from an OptionT map. -/
@[simp]
lemma mem_support_OptionT_map_some {m : Type u → Type v} [Monad m] [HasEvalSPMF m] [LawfulMonad m]
    {α β : Type u} (ma : OptionT m α) (f : α → β) (y : β) :
    y ∈ support (f <$> ma) ↔
      ∃ x ∈ support ma, f x = y := by
  simpa using (mem_support_map_iff_generic (mx := ma) (f := f) (y := y))

/-- Successful-value decomposition for map at `OptionT.run` level. -/
@[simp]
lemma mem_support_OptionT_run_map_some {m : Type u → Type v} [Monad m] [HasEvalSPMF m] [LawfulMonad m]
    {α β : Type u} (ma : OptionT m α) (f : α → β) (y : β) :
    some y ∈ support (OptionT.run (f <$> ma)) ↔
      ∃ x ∈ support ma, f x = y := by
  simpa using mem_support_run_map_some_iff (ma := ma) (f := f) (y := y)
---------------------------------------------------------------

end OptionT

/-- Commute two curried implication antecedents. -/
theorem imp_comm {P Q R : Prop} : (P → Q → R) ↔ (Q → P → R) := by
  constructor <;> intro h h1 h2 <;> exact h h2 h1

/-- Two-level `forall`/membership elimination with an outer `Option.some` equality. -/
theorem forall_eq_lift_mem_2_some
    {α β γ : Type u} {S : Set α} {T : α → Set β}
    (f : α → β → γ) (p : γ → α → β → Prop) :
    (∀ (c : γ), ∀ a ∈ S, ∀ b ∈ T a, some c = some (f a b) → p c a b) ↔
    (∀ a ∈ S, ∀ b ∈ T a, p (f a b) a b) := by
  constructor
  · intro h a ha b hb
    exact h (f a b) a ha b hb rfl
  · intro h c a ha b hb hEq
    have hc : c = f a b := by simpa using hEq
    rw [hc]
    exact h a ha b hb

/-- Three-level `forall`/membership elimination (nested support bind form). -/
theorem forall_eq_lift_mem_3
    {α β γ δ : Type u} {S : Set α} {T : α → Set β} {U : α → β → Set γ}
    (f : α → β → γ → δ) (p : δ → α → β → γ → Prop) :
    (∀ (d : δ), ∀ a ∈ S, ∀ b ∈ T a, ∀ c ∈ U a b, d = f a b c → p d a b c) ↔
    (∀ a ∈ S, ∀ b ∈ T a, ∀ c ∈ U a b, p (f a b c) a b c) := by
  constructor
  · intro h a ha b hb c hc
    exact h (f a b c) a ha b hb c hc rfl
  · intro h d a ha b hb c hc hEq
    rw [hEq]
    exact h a ha b hb c hc

/-- Three-level variant with an outer `Option.some` equality. -/
theorem forall_eq_lift_mem_3_some
    {α β γ δ : Type u} {S : Set α} {T : α → Set β} {U : α → β → Set γ}
    (f : α → β → γ → δ) (p : δ → α → β → γ → Prop) :
    (∀ (d : δ), ∀ a ∈ S, ∀ b ∈ T a, ∀ c ∈ U a b, some d = some (f a b c) → p d a b c) ↔
    (∀ a ∈ S, ∀ b ∈ T a, ∀ c ∈ U a b, p (f a b c) a b c) := by
  constructor
  · intro h a ha b hb c hc
    exact h (f a b c) a ha b hb c hc rfl
  · intro h d a ha b hb c hc hEq
    have hd : d = f a b c := by simpa using hEq
    rw [hd]
    exact h a ha b hb c hc

/-- Simplifies the probability event of a deterministic pure result. -/
@[simp]
lemma probEvent_pure_iff {α : Type} (p : α → Prop) [DecidablePred p] (x : α) :
    Pr[p | (pure x : ProbComp α)] = 1 ↔ p x := by
  simp only [probEvent_pure, ite_eq_left_iff]
  exact ⟨fun h => by simpa using h, fun h => by simp [h]⟩

alias probEvent_eq_one_pure_iff := probEvent_pure_iff

end simp_lemmas

/-! ### StateT Helper Lemmas

Generic helper lemmas for `StateT` operations that simplify reasoning about
`run`, `run'`, and monadic operations in the probability monad.

These lemmas unfold stateful computations into their underlying probability distributions.
-/

namespace StateT

universe u v w

variable {m : Type u → Type v} {σ α β : Type u}

/-- Unfolding lemma for `run'` on `pure`. -/
@[simp]
theorem run'_pure_lib [Monad m] [LawfulMonad m] (x : α) (s : σ) :
    (pure x : StateT σ m α).run' s = (pure x : m α) := by
  simp only [run', pure, StateT.pure, map_pure]

/-- Unfolding lemma for `run'` on `bind`. -/
@[simp]
theorem run'_bind_lib [Monad m] [LawfulMonad m] (ma : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (ma >>= f).run' s = ((ma.run s) >>= fun (a, s') => (f a).run' s') := by
  simp only [run', bind, StateT.bind, map_bind, run]

/-- Unfolding lemma for `run` on `liftM`. -/
@[simp]
theorem run_liftM_lib [Monad m] [LawfulMonad m] (ma : m α) (s : σ) :
    (liftM ma : StateT σ m α).run s = (ma >>= fun a => pure (a, s)) := by
  simp only [run, liftM, bind_pure_comp]
  rw [map_eq_pure_bind]; rfl

/-- Simplify a bind following a pure initialization of state. -/
@[simp]
theorem run'_bind_pure [Monad m] [LawfulMonad m] {s : σ} (x : α) (f : α → StateT σ m β) :
    (StateT.run' (pure x >>= f) s) = (StateT.run' (f x) s) :=
by simp [StateT.run']

alias run'_pure_bind := run'_bind_pure

end StateT
