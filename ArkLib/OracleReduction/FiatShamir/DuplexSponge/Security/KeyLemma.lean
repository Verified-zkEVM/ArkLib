/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.Basic
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Nondegeneracy
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
public import ArkLib.OracleReduction.FiatShamir.SingleSalt
public import VCVio.EvalDist.DiscreteTVDist
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Section 5 hybrid experiments of the Chiesa-Orrù paper

This file provides the definitions needed by the Section 5 key-lemma argument:
- the DSFS and basic-FS game experiments,
- canonical abstractions for `D2SAlgo` and the Section 5.8 trace algorithms, and
- the hybrid experiments, numerical bounds, and query-bound predicates.

`StmtIn` is the Lean stand-in for the paper's hash-input space `{0,1}^{≤n}`. The paper's
instance-size bound is fixed by choosing this type, while `n` in this file is the protocol round
count from `pSpec : ProtocolSpec n`. Likewise, `codec.decodingBias` abstracts the paper's
`ε_cdc,i(λ,n)` values for the fixed ambient parameter instantiation.

The paper-level claims and Lemmas 5.8/5.1 are deferred to a later proof-focused PR. Lemma 5.1 is
stated as the proposition `Lemma5_1Statement`, so that its hypotheses (`NondegenerateRounds`,
`IsLemma5_1QueryBound`) and its bound (`ηStar`) have a consumer. Its "Moreover" clause (the
`θ★` query bound of `D2SAlgo`) is part of that proposition.

## Reading guide (CO25 Section 5.8 hybrid chain)

The file follows the paper's Section 5.8 layout. The five hybrid distributions appear in paper
order; the arrows record the claims that a later proof-focused PR will formalize:

```
Hyb_0  DSFS               (h,p,p⁻¹) ← 𝒟_𝔖           ── Claim 5.21 ─▶
Hyb_1  encoded  `g`       g ← 𝒟_Σ                   ── Claim 5.22 ─▶
Hyb_2  decoded  `e`       e ← 𝒟_e                   ── Claim 5.23 ─▶ (= 0)
Hyb_3  salted FS `f`      f ← 𝒟_IP_salted           ── Claim 5.24 ─▶
Hyb_4  basic FS           f ← 𝒟_IP_salted (same f, different algos)
```

The triangle-inequality sum of the four paper bounds gives `η★` (CO25 Eq. 5).

## Section map (top-to-bottom)

1. **Setup** — universe-quantified variable block, `SampleableType` bridge instances.
2. **`section SecurityGames`** — the experiment shells:
   - `liftFSSaltedQueriesToD2SChallengePlusUnit`, `filterD2SChallengePlusUnitQueryLog` —
     spec plumbing between basic-FS and wide D2S spec.
   - `BasicFiatShamirGameOutput`, `DSFSGameOutput` — output types.
   - `basicFiatShamirGame`, `dsfsGame` — paper game bodies.
   - `D2SAlgo`, `runSection58TraceMap` — §5.4 reduction and §5.8 line-4 trace map runners.
   - `hybChallengeImpl` — common eager-sample challenge
     handler shared by `Hyb_1`/`Hyb_2`/`Hyb_3`/`Hyb_4`.
   - `hyb0Init` / `hyb0Impl` — DSFS-side `(h,p,p⁻¹)` handler for `Hyb_0`.
   - `hybridGame` — the common Figure 4 skeleton (lines 2–3).
   - `hybridGameDist`, `basicFiatShamirGameDist`, `dsfsGameDist`,
     `mappedDSFSGameDist` — game-to-`ProbComp` distribution wrappers.
3. **`section KeyLemma`** — numerical bounds, hybrid chain, and future-proof interfaces:
   - **Bounds**: `θ★`, `CodecBias`, `η★`, `claim5_2{1,2,4}Bound`, and the Eq. (5) and Eq. (56)
     identities `ηStar_eq_claimBounds`, `claim5_24Bound_eq_sum`.
   - **Hybrid chain (paper order)**: `hyb_0` → `hyb_1` → `hyb_2` → `hyb_3` → `hyb_4`.
   - **Query interfaces**: `IsLemma5_1QueryBound`, `IsD2SAlgoChallengeQueryBound`.
   - **Lemma 5.1 statement**: `Lemma5_1Statement`.
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec

/-! ## Query bound of `D2SAlgo` (CO25 §5.4, "Query complexity of D2SAlgo")

`D2SAlgo(𝒫̃)` queries `f` only on a `tr_i` miss in the memoized codec bridge
(`d2sCodecBridgeImplMemo`), and the bridge is called only in D2SQuery Item 4(e)i, at most once per
forward-permutation query of `𝒫̃`. The lemmas below track this through the simulation layers:
`StateQueryBound` is a query bound for a `StateT σ (OptionT (OracleComp spec))` computation from
every initial state, and the `*_queryBound` lemmas bound the `gᵢ` / `fᵢ` queries of each
D2SQuery handler. The final statement is `KeyLemma.isD2SAlgoChallengeQueryBound_d2sAlgo`. -/

namespace DuplexSpongeFS.D2SAlgoQueryBound

open DuplexSpongeFS.ProverTransform

/-! ### Generic transfer lemmas -/

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  {q : ι' → Prop} [DecidablePred q]

/-- Query bound of a `StateT σ (OptionT (OracleComp spec'))` computation from every state. -/
def StateQueryBound {σ α : Type} (x : StateT σ (OptionT (OracleComp spec')) α) (q : ι' → Prop)
    [DecidablePred q] (k : ℕ) : Prop :=
  ∀ s, IsQueryBoundP (x.run s).run q k

lemma StateQueryBound.mono {σ α : Type} {x : StateT σ (OptionT (OracleComp spec')) α} {k k' : ℕ}
    (h : StateQueryBound x q k) (hk : k ≤ k') : StateQueryBound x q k' := fun s => (h s).mono hk

lemma stateQueryBound_pure {σ α : Type} (a : α) :
    StateQueryBound (pure a : StateT σ (OptionT (OracleComp spec')) α) q 0 := fun _ => trivial

lemma stateQueryBound_get {σ : Type} :
    StateQueryBound (get : StateT σ (OptionT (OracleComp spec')) σ) q 0 :=
  fun _ => trivial

lemma stateQueryBound_set {σ : Type} (s' : σ) :
    StateQueryBound (set s' : StateT σ (OptionT (OracleComp spec')) PUnit) q 0 := fun _ => trivial

lemma stateQueryBound_modify {σ : Type} (f : σ → σ) :
    StateQueryBound (modify f : StateT σ (OptionT (OracleComp spec')) PUnit) q 0 := fun _ => trivial

lemma stateQueryBound_failure {σ α : Type} :
    StateQueryBound (StateT.lift failure : StateT σ (OptionT (OracleComp spec')) α) q 0 :=
  fun _ => trivial

lemma stateQueryBound_lift {σ α : Type} {x : OracleComp spec' α} {k : ℕ}
    (hx : IsQueryBoundP x q k) :
    StateQueryBound (StateT.lift (OptionT.lift x) : StateT σ (OptionT (OracleComp spec')) α)
      q k := by
  intro s
  have h : ((StateT.lift (OptionT.lift x) : StateT σ (OptionT (OracleComp spec')) α).run s).run
      = (fun a => some (a, s)) <$> x := by
    simp only [StateT.run_lift, OptionT.run_bind, OptionT.lift, OptionT.mk, Option.elimM,
      map_eq_bind_pure_comp]
    change (x >>= pure ∘ some) >>= _ = _
    simp [bind_assoc, map_eq_bind_pure_comp]
  rw [h, isQueryBoundP_map_iff]
  exact hx

lemma stateQueryBound_bind {σ α β : Type} {x : StateT σ (OptionT (OracleComp spec')) α}
    {f : α → StateT σ (OptionT (OracleComp spec')) β} {k₁ k₂ : ℕ}
    (hx : StateQueryBound x q k₁) (hf : ∀ a, StateQueryBound (f a) q k₂) :
    StateQueryBound (x >>= f) q (k₁ + k₂) := by
  intro s
  simp only [StateT.run_bind, OptionT.run_bind]
  refine isQueryBoundP_bind (hx s) fun o _ => ?_
  rcases o with _ | ⟨a, s'⟩
  · exact trivial
  · exact hf a s'

lemma isQueryBoundP_bind_zero {α β : Type} {x : OracleComp spec' α} {f : α → OracleComp spec' β}
    (hx : IsQueryBoundP x q 0) (hf : ∀ a, IsQueryBoundP (f a) q 0) :
    IsQueryBoundP (x >>= f) q 0 := by
  simpa using isQueryBoundP_bind hx (fun a _ => hf a)

lemma stateQueryBound_bind_zero {σ α β : Type} {x : StateT σ (OptionT (OracleComp spec')) α}
    {f : α → StateT σ (OptionT (OracleComp spec')) β}
    (hx : StateQueryBound x q 0) (hf : ∀ a, StateQueryBound (f a) q 0) :
    StateQueryBound (x >>= f) q 0 :=
  stateQueryBound_bind hx hf

lemma stateQueryBound_liftOpt {σ α : Type} {z : OptionT (OracleComp spec') α} {k : ℕ}
    (hz : IsQueryBoundP z.run q k) :
    StateQueryBound (StateT.lift z : StateT σ (OptionT (OracleComp spec')) α) q k := by
  intro s
  simp only [StateT.run_lift, OptionT.run_bind, Option.elimM]
  have := isQueryBoundP_bind (m := 0) hz
    (ob := fun o => o.elim (pure none) fun x => pure (some (x, s))) fun o _ => by
      cases o <;> exact trivial
  simpa using this

/-- Stateless transfer through `simulateQ`. -/
lemma isQueryBoundP_simulateQ {ι₀ : Type} {spec₀ : OracleSpec ι₀} {p : ι₀ → Prop}
    [DecidablePred p] {impl : QueryImpl spec₀ (OracleComp spec')} {α : Type}
    {oa : OracleComp spec₀ α} {k : ℕ} (h : IsQueryBoundP oa p k)
    (hstep : ∀ t, IsQueryBoundP (impl t) q (if p t then 1 else 0)) :
    IsQueryBoundP (simulateQ impl oa) q k := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x => exact trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hbound : (if p t then 1 else 0) + (if p t then k - 1 else k) = k := by grind
      simpa [hbound] using isQueryBoundP_bind (hstep t) fun u _ => ih u (h.2 u)

/-- Transfer through `simulateQ` into `StateT σ (OptionT (OracleComp spec'))`. -/
lemma isQueryBoundP_simulateQ_StateT_OptionT {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    {p : ι₀ → Prop} [DecidablePred p] {σ : Type}
    {impl : QueryImpl spec₀ (StateT σ (OptionT (OracleComp spec')))} {α : Type}
    {oa : OracleComp spec₀ α} {k : ℕ} (h : IsQueryBoundP oa p k)
    (hstep : ∀ t, StateQueryBound (impl t) q (if p t then 1 else 0)) :
    StateQueryBound (simulateQ impl oa) q k := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x => exact fun _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query]
      have hbound : (if p t then 1 else 0) + (if p t then k - 1 else k) = k := by grind
      have := stateQueryBound_bind (q := q) (hstep t) fun u => ih u (h.2 u)
      simp only [hbound] at this
      exact this

/-- Transfer through `simulateQ` into `StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))`. -/
lemma isQueryBoundP_simulateQ_StateT_StateT_OptionT {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    {p : ι₀ → Prop} [DecidablePred p] {σ₁ σ₂ : Type}
    {impl : QueryImpl spec₀ (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec'))))} {α : Type}
    {oa : OracleComp spec₀ α} {k : ℕ} (h : IsQueryBoundP oa p k)
    (hstep : ∀ t s₁, StateQueryBound ((impl t).run s₁) q (if p t then 1 else 0)) (s₁ : σ₁) :
    StateQueryBound ((simulateQ impl oa).run s₁) q k := by
  induction oa using OracleComp.inductionOn generalizing k s₁ with
  | pure x => exact fun _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
      have hbound : (if p t then 1 else 0) + (if p t then k - 1 else k) = k := by grind
      have := stateQueryBound_bind (q := q) (hstep t s₁) fun us => ih us.1 (h.2 us.1) us.2
      simp only [hbound] at this
      exact this

lemma isQueryBoundP_bind_pure {α β : Type} {x : OracleComp spec' α} {f : α → β} {k : ℕ}
    (hx : IsQueryBoundP x q k) : IsQueryBoundP (x >>= fun a => pure (f a)) q k := by
  simpa using isQueryBoundP_bind (m := 0) (ob := fun a => (pure (f a) : OracleComp spec' β))
    hx fun _ _ => trivial

/-- A single query lifted along a sub-spec inclusion is one query at its image index. -/
lemma isQueryBoundP_liftM_query {ι₀ : Type} {spec₀ : OracleSpec ι₀} [h : spec₀ ⊂ₒ spec']
    (t : spec₀.Domain) {k : ℕ} (hk : q (h.onQuery t) → 0 < k) :
    IsQueryBoundP (liftM (spec₀.query t) : OracleComp spec' (spec₀.Range t)) q k := by
  rw [show (liftM (spec₀.query t) : OracleComp spec' (spec₀.Range t)) =
      liftM (spec'.query (h.onQuery t)) >>= fun u => pure (h.onResponse t u) by
    change ((liftM (spec₀.query t) : OracleQuery spec' (spec₀.Range t)) :
        OracleComp spec' (spec₀.Range t)) =
      (liftM (spec'.query (h.onQuery t)) >>= fun u => pure (h.onResponse t u))
    rw [show (liftM (spec₀.query t) : OracleQuery spec' (spec₀.Range t)) =
        ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _]
    rfl]
  exact isQueryBoundP_bind_pure ((isQueryBoundP_query_iff _ _ _).2 hk)

end Generic


section Samplers

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ}

/-- `gᵢ` queries in the `D2SQuery` oracle spec. -/
def isChallengeSlotQuery {κ : Type} {challengeSpec : OracleSpec κ} :
    (D2SChallengePlusUnitOracle (U := U) challengeSpec).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance {κ : Type} {challengeSpec : OracleSpec κ} :
    DecidablePred (isChallengeSlotQuery (U := U) (challengeSpec := challengeSpec)) := fun t =>
  match t with
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

local notation "G0" x => IsQueryBoundP x (isChallengeSlotQuery (U := U)
  (challengeSpec := gSpec (U := U) StmtIn pSpec δ)) 0

omit [SpongeSize] in
lemma d2sSampleUnit_queryBound :
    G0 (d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
  simp [d2sSampleUnit, isChallengeSlotQuery]

omit [SpongeSize] in
lemma d2sSampleArrayExact_queryBound (m : ℕ) :
    G0 (d2sSampleArrayExact (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m) := by
  induction m with
  | zero => exact trivial
  | succ m ih =>
    simp only [d2sSampleArrayExact]
    refine isQueryBoundP_bind_zero d2sSampleUnit_queryBound fun _ =>
      isQueryBoundP_bind_zero ih fun x => ?_
    obtain ⟨_, _⟩ := x
    exact trivial

omit [SpongeSize] in
lemma d2sSampleVector_queryBound (m : ℕ) :
    G0 (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m) := by
  refine isQueryBoundP_bind_zero (d2sSampleArrayExact_queryBound m) fun x => ?_
  obtain ⟨_, _⟩ := x
  exact trivial

lemma d2sSampleCapacityList_queryBound (m : ℕ) :
    G0 (d2sSampleCapacityList (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m) := by
  induction m with
  | zero => exact trivial
  | succ m ih =>
    simp only [d2sSampleCapacityList]
    exact isQueryBoundP_bind_zero (d2sSampleVector_queryBound _) fun _ =>
      isQueryBoundP_bind_zero ih fun _ => trivial

lemma d2sRateBlocksFromUnitsM_queryBound (m : ℕ) (units : List U) :
    G0 (d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m units) := by
  induction m generalizing units with
  | zero => exact trivial
  | succ m ih =>
    simp only [d2sRateBlocksFromUnitsM]
    split <;>
    repeat (first
      | exact trivial
      | exact ih _
      | exact d2sSampleVector_queryBound _
      | (refine isQueryBoundP_bind_zero ?_ ?_ <;> try intro x))

lemma d2sRateBlocksFromChallenge_queryBound {i : pSpec.ChallengeIdx}
    (c : Vector U (challengeSize (pSpec := pSpec) i)) :
    G0 (d2sRateBlocksFromChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) c) := by
  refine isQueryBoundP_bind_zero (d2sRateBlocksFromUnitsM_queryBound _ _) fun x => ?_
  obtain ⟨_, _⟩ := x
  exact trivial

omit [SpongeSize] in
lemma d2sQueryG_queryBound (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (msgs : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    IsQueryBoundP (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      i stmt salt msgs) (isChallengeSlotQuery (U := U)
        (challengeSpec := gSpec (U := U) StmtIn pSpec δ)) 1 := by
  unfold d2sQueryG
  exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

end Samplers

section Handlers

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

local notation "QG" x "," k => StateQueryBound x (isChallengeSlotQuery (U := U)
  (challengeSpec := gSpec (U := U) StmtIn pSpec δ)) k

macro "state_query_bound_zero" : tactic => `(tactic| repeat (first
  | with_reducible exact stateQueryBound_pure _
  | with_reducible exact stateQueryBound_get
  | with_reducible exact stateQueryBound_set _
  | with_reducible exact stateQueryBound_modify _
  | with_reducible exact stateQueryBound_failure
  | with_reducible exact stateQueryBound_lift (d2sSampleVector_queryBound _)
  | with_reducible exact stateQueryBound_lift (d2sSampleCapacityList_queryBound _)
  | with_reducible exact stateQueryBound_lift (d2sRateBlocksFromChallenge_queryBound _)
  | with_reducible refine stateQueryBound_bind_zero ?_ fun _ => ?_
  | fail_if_no_progress dsimp only
  | split))

omit [Fintype U] [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sHandleHashQuery_queryBound (stmt : StmtIn) :
    QG (d2sHandleHashQuery (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) stmt), 0 := by
  unfold d2sHandleHashQuery d2sSampleCapacity
  state_query_bound_zero

omit [Fintype U] [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sHandleInversePermQuery_queryBound (s : CanonicalSpongeState U) :
    QG (d2sHandleInversePermQuery (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) s), 0 := by
  unfold d2sHandleInversePermQuery d2sSampleState
  state_query_bound_zero

omit [Fintype U] [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sHandleBacktrackNoResult_queryBound (s : CanonicalSpongeState U) :
    QG (d2sHandleBacktrackNoResult (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) s), 0 := by
  unfold d2sHandleBacktrackNoResult d2sSampleState
  state_query_bound_zero

omit [Fintype U] [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sSynthesizeStateFromRateBlocks_queryBound (blocks : List (Vector U SpongeSize.R)) :
    QG (d2sSynthesizeStateFromRateBlocks (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) blocks), 0 := by
  unfold d2sSynthesizeStateFromRateBlocks
  refine stateQueryBound_bind_zero stateQueryBound_get fun st => ?_
  split
  · exact stateQueryBound_failure
  · refine stateQueryBound_bind_zero
      (stateQueryBound_lift (d2sSampleCapacityList_queryBound _)) fun caps => ?_
    dsimp only
    split
    · exact stateQueryBound_failure
    · exact stateQueryBound_pure _

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sHandleBacktrackSome_queryBound (s : CanonicalSpongeState U)
    (bt : Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    QG (d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) s bt), 1 := by
  unfold d2sHandleBacktrackSome
  refine (stateQueryBound_bind (k₁ := 0) (k₂ := 1) stateQueryBound_get fun st => ?_).mono le_rfl
  split
  · refine (stateQueryBound_bind (k₁ := 1) (k₂ := 0)
      (stateQueryBound_lift (d2sQueryG_queryBound _ _ _ _)) fun ρ => ?_).mono
      le_rfl
    state_query_bound_zero
    · exact d2sSynthesizeStateFromRateBlocks_queryBound _
    · rename_i x
      obtain ⟨_, _⟩ := x
      state_query_bound_zero
  · refine StateQueryBound.mono ?_ (Nat.zero_le 1)
    unfold d2sSampleState
    state_query_bound_zero

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sHandleForwardPermQuery_queryBound (s : CanonicalSpongeState U) :
    QG (d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) s), 1 := by
  unfold d2sHandleForwardPermQuery
  refine (stateQueryBound_bind (k₁ := 0) (k₂ := 1) stateQueryBound_get fun st => ?_).mono le_rfl
  split
  · exact stateQueryBound_failure.mono (Nat.zero_le 1)
  · exact (d2sHandleBacktrackNoResult_queryBound s).mono (Nat.zero_le 1)
  · exact d2sHandleBacktrackSome_queryBound s _

/-- Forward-permutation queries of the duplex-sponge spec. -/
def isDSPermQuery : (duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (isDSPermQuery (StmtIn := StmtIn) (U := U)) := fun t =>
  match t with
  | .inl _ => isFalse id
  | .inr (.inl _) => isTrue trivial
  | .inr (.inr _) => isFalse id

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sQueryStep_queryBound (dq : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    QG (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) dq), (if isDSPermQuery dq then 1 else 0) := by
  rcases dq with x | x | x
  · exact d2sHandleHashQuery_queryBound x
  · exact d2sHandleForwardPermQuery_queryBound x
  · exact d2sHandleInversePermQuery_queryBound x

end Handlers

section Bridge

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

local notation "QF" x "," k => StateQueryBound x (isChallengeSlotQuery (U := U)
  (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) k

omit [SpongeSize] [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sCodecBridgeImpl_queryBound (g : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    IsQueryBoundP (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (Salt := Salt) g).run (isChallengeSlotQuery (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) 1 := by
  unfold d2sCodecBridgeImpl
  dsimp only
  split
  · simp only [pure_bind, OptionT.run_bind, Option.elimM, Option.elim]
    refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ fun o _ => ?_).mono le_rfl
    · simp only [OptionT.lift, OptionT.run_mk]
      exact isQueryBoundP_bind_pure ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    · rcases o with _ | c
      · exact trivial
      · simp only [OptionT.lift, OptionT.run_mk]
        refine isQueryBoundP_bind_pure ?_
        unfold uniformDeserializePreimage sampleFromList
        exact isQueryBoundP_bind_zero ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim)
          fun _ => trivial
  · simp

omit [SpongeSize] [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sCodecBridgeImplMemo_queryBound (g : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    QF (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (Salt := Salt) g), 1 := by
  unfold d2sCodecBridgeImplMemo
  refine (stateQueryBound_bind (k₁ := 0) (k₂ := 1) stateQueryBound_get fun memo => ?_).mono le_rfl
  split
  · exact (stateQueryBound_pure _).mono (Nat.zero_le 1)
  · refine (stateQueryBound_bind (k₁ := 1) (k₂ := 0)
      (stateQueryBound_liftOpt (d2sCodecBridgeImpl_queryBound g)) fun r => ?_).mono
      le_rfl
    exact stateQueryBound_bind_zero (stateQueryBound_modify _) fun _ => stateQueryBound_pure _

variable {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]

omit [∀ i, DecidableEq (pSpec.Message i)] in
lemma d2sQueryImpl_queryBound
    {auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec)
      (StateT (D2SAlgoMemo StmtIn U δ Salt pSpec)
        (OptionT (OracleComp (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))))}
    (haux : ∀ aux, StateQueryBound (auxImpl aux) (isChallengeSlotQuery (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) 0)
    (dq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U)) :
    QF ((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U)
      (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      auxImpl dq).run s₁),
      (if isDSPermQuery dq then 1 else 0) := by
  unfold d2sQueryImpl
  dsimp only [StateT.run]
  refine (stateQueryBound_bind (k₂ := 0) (isQueryBoundP_simulateQ_StateT_OptionT
    (d2sQueryStep_queryBound (δ := δ) (T_H := T_H) (T_P := T_P) dq s₁) fun t => ?_)
      fun o => ?_).mono
      (by simp)
  · rcases t with g | aux
    · exact d2sCodecBridgeImplMemo_queryBound g
    · exact haux aux
  · rcases o with _ | ⟨_, _⟩
    · intro _
      simp only [StateT.run_failure, OptionT.run_failure]
      exact trivial
    · exact stateQueryBound_pure _

end Bridge

end DuplexSpongeFS.D2SAlgoQueryBound

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  -- CO25 Def 4.1 codec: supplies sizes and Serialize/Deserialize via projections.
  [codec : Codec pSpec U]
  {δ : Nat}
  -- Pre-encoded salt type used by FS-standard side (paper's `{0,1}^{δ⋆}`); bridged from the
  -- on-sponge `Vector U δ` salt via `SaltCodec.encode = bin` (CO25 §5.4 D2SAlgo Item 3(c);
  -- injectivity of `bin` is used in the proof of Claim 5.23).
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section SecurityGames

/-! ### Spec plumbing — lift verifier queries and project auxiliary log entries -/

/-- Simple query impl lift:
Lift salted basic-FS verifier queries into the external `f_i` oracle plus D2S auxiliary
sampling oracles used by `D2SAlgo^f`.  Salt is the pre-encoded type `{0,1}^{δ⋆}` (paper). -/
def liftFSSaltedQueriesToD2SChallengePlusUnit :
    QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      (OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  fun q =>
    match q with
    | .inl qShared =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
          (Sum.inl qShared)
    | .inr qFS =>
        query
          (spec := oSpec +
            D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
          (Sum.inr (Sum.inl qFS))

/-- CO25 §5.8. Project out the auxiliary unit-sampling queries from logs over
`oSpec + (challengeSpec + Unit →ₒ U)`, retaining only shared and challenge entries. -/
def filterD2SChallengePlusUnitQueryLog
    {κ : Type} {challengeSpec : OracleSpec κ}
    (log : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    QueryLog (oSpec + challengeSpec) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
    | ⟨.inr (.inl q), r⟩ => some ⟨.inr q, r⟩
    | ⟨.inr (.inr _), _⟩ => none

/-! ### Game output types and game bodies (`Hyb_0` / `Hyb_4`) -/

/-- CO25 Lemma 5.1. Output type for the salted basic Fiat-Shamir game (`Hyb_4`):
`(b, 𝕩, π = (τ̌, messages), tr)` where
- `τ̌ = bin (τ) ∈ {0,1}^{δ⋆}`
- `tr` is the combined query log over the salted `fsChallengeOracle (StmtIn × Salt) pSpec`

The games return `Option` of this type, and the decision bit `b` is refined to the output
statement. On acceptance a game returns `some (𝕩, stmtOut, π, tr)`. On rejection it returns
`none`, which discards `(𝕩, π, tr)`. CO25 Lemma 5.1 compares `(b, 𝕩, π, tr)` and keeps
`(𝕩, π, tr)` when `b = 0`, so a distance bound between these games is weaker than the paper's.
It is enough for the soundness reductions, which use `(𝕩, π, tr)` only on acceptance. -/
abbrev BasicFiatShamirGameOutput :=
  StmtIn × StmtOut × FSSaltedProof pSpec Salt ×
    TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)

/-- CO25 Lemma 5.1. Output type for the duplex-sponge Fiat-Shamir game (`Hyb_0` left-hand
experiment): statement-in, statement-out, salted proof, and combined query log over
`duplexSpongeChallengeOracle`. -/
abbrev DSFSGameOutput :=
  StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
    TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)

/-- CO25 Lemma 5.1. The basic-FS verifier `𝒱_std^f` as a standalone computation: derive the FS
transcript from the salted proof — routing `fsChallengeOracle` queries into the wide
`D2SChallengePlusUnitOracle` spec via `liftFSSaltedQueriesToD2SChallengePlusUnit`, lifting the
`V.verify` call (which uses only `oSpec`) the same way — and return the optional output statement.
Factored out of `basicFiatShamirGame` so the `hyb4_eq` log-strip treats it opaquely; it equals
the FS-NARG verifier `fsSaltedVerify` routed through the same lift (the `hyb4_eq` verifier part). -/
def basicFSVerifierComp (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtAndProof : StmtIn × FSSaltedProof pSpec Salt) :
    OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (Option StmtOut) :=
  -- `𝒱_std^f` IS the FS-NARG verifier `fsSaltedVerify`, with ALL its queries (the
  -- `deriveTranscriptFS` challenge queries AND the `oSpec`-only `V.verify` queries) routed into the
  -- wide spec by the single relabel `liftFSSaltedQueriesToD2SChallengePlusUnit`.  Defining it this
  -- way (not routing `deriveTranscriptFS` and `V.verify` separately) makes the `hyb4_eq` verifier
  -- collapse a one-liner: `simulateQ Hyb₄ (basicFSVerifierComp V p) = simulateQ ⟨Hyb₄ ∘ₛ liftFS⟩
  -- (fsSaltedVerify …).run` by `simulateQ_compose` + infra lemma 2.
  simulateQ
    (liftFSSaltedQueriesToD2SChallengePlusUnit
      (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    ((fsSaltedVerify (Salt := Salt) V stmtAndProof.1 stmtAndProof.2).run)

/-- CO25 Lemma 5.1. Right-hand game for Lemma 5.1 (the basic-FS game).
Runs `𝒱_std^f` against the compiled prover `D2SAlgo^f(𝒫̃~)`.
- Prover outputs `(𝕩, (τ̌, messages))`
- Verifier queries `f` at `(𝕩, τ̌, messages)`

If the prover aborts, the verifier runs on `(default, (SaltCodec.encode default, default))`, the
same fallback as `hybridGame`. The game returns `none` when the verifier rejects
(`stmtOut.getM`); see `BasicFiatShamirGameOutput`. -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  let ⟨stmtAndProof?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle P).run
  -- De-aborted via `getD default` bound to a *single, non-destructured* `let` (project with
  -- `.1`/`.2` below) — crucially NOT `let ⟨stmtIn, proof⟩ := …`, since the pair-destructure floats
  -- `getD`'s `some/none` match out and duplicates the verifier into both branches, blocking the
  -- `hyb4_eq` log-strip. A failed compiled prover yields the `default` statement and the proof
  -- `(SaltCodec.encode default, default)`: the proof `hybridGame` substitutes on a prover abort,
  -- after the `bin` re-encoding of D2SAlgo Items 4-6. So Hyb₃ and Hyb₄ continue from the same
  -- `(𝕩, π)`, and their verifiers query `f` at the same keys. An induced SR prover built from
  -- this game must use the same fallback.
  let stmtAndProof := stmtAndProof?.getD
    (default, (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) default, default))
  let verifierComp :
      OracleComp (oSpec +
        D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut) := basicFSVerifierComp V stmtAndProof
  let ⟨stmtOut, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp).run
  let proveQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) verifyQueryLogRaw
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtAndProof.1, ← stmtOut.getM, stmtAndProof.2, taggedP ++ taggedV⟩

/-- CO25 Lemma 5.1. Left-hand game for Lemma 5.1 (the DSFS game).
Runs `𝒱^{h,p}` against the malicious prover `𝒫̃~` (this is `Hyb_0`).
- Prover outputs `(𝕩, (τ, messages))`
- Verifier queries `h, p` only (no `p⁻¹` per Figure 4 line 3)

The game returns `none` when the verifier rejects (`stmtOut.getM`), discarding `(𝕩, π, tr)`;
see `BasicFiatShamirGameOutput`. -/
def dsfsGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  let ⟨⟨stmtIn, proof⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  -- Type-level CO25 Figure 4 line 3 (`𝒱^{h,p}`): the narrow forward-only verifier is built and
  -- lifted to the wide spec (`liftDuplexSpongeForward`) by `runForwardVerifierWide`; the subsequent
  -- `simulateQ loggingOracle` emits a wide-spec query log with no `p⁻¹` entries from `V`.
  let verifyCompWide := runForwardVerifierWide δ V stmtIn proof
  let ⟨stmtOut, verifyQueryLog⟩ ← liftM (simulateQ loggingOracle verifyCompWide).run
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtIn, ← stmtOut.getM, proof, taggedP ++ taggedV⟩

/-- CO25 §5.8. Execute a Section 5.8 line-4 trace map (e.g. D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`)
inside `ProbComp` by interpreting the auxiliary unit-sampling oracle uniformly. -/
def runSection58TraceMap
    [instSampleable : SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec)
    (fullTrace : TaggedQueryLog (oSpec + challengeSpec)) :
    ProbComp
      (Option (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))) :=
  simulateQ
    (d2sUnitSampleImpl (instSampleable := instSampleable) (U := U))
    ((traceMap fullTrace).run)

/-! ### Common eager-sample handler for `Hyb_1` / `Hyb_2` / `Hyb_3` / `Hyb_4` -/

/-- CO25 §5.8. Stateless 4-slot query handler for the §5.8 hybrid experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; challenge queries → `pure (k_chal q)` (paper
`𝒟_Σ` / `𝒟_e` / `𝒟_IP_salted`); auxiliary unit queries → `d2sUnitSampleImpl` (fresh per
call); auxiliary `unifSpec` queries → ambient `ProbComp` uniform sampling.  The deterministic table
carrier is read from the state but never mutated — sampled once at game initialization
and held fixed (CO25 Eq. 16 / Eq. 53 / Eq. 55).  The paper has no ambient distribution; we
take an arbitrary `QueryImpl oSpec ProbComp` instead, which the caller specializes (e.g. to
the empty spec for paper fidelity). -/
def hybChallengeImpl
    [instSampleable : SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT (QueryImpl challengeSpec Id) ProbComp) :=
      -- the sampled oracle function is embedded into StateT as `(QueryImpl challengeSpec Id)` type
  fun
    | .inl (qShared : ι) =>
        StateT.lift <| oSpecImpl qShared
    | .inr (.inl (qChal : κ)) => do -- `κ`
        let kC : (QueryImpl challengeSpec Id) ← get
        StateT.lift <| pure (kC qChal)
    | .inr (.inr (.inl (qUnit : Unit))) => -- (Unit →ₒ U) => alphabet sampling, e.g. in LookAhead
        StateT.lift <| d2sUnitSampleImpl (instSampleable := instSampleable) (U := U) qUnit
    | .inr (.inr (.inr (qUnif : ℕ))) => -- unifSpec => default from ProbComp, we adopt it for `ψ⁻¹`
        StateT.lift <|
          (show ProbComp (unifSpec.Range qUnif) from
            query (spec := unifSpec) qUnif)

/-! ### DSFS-side handler for `Hyb_0` -/

/-- CO25 §5.8 Hyb_0. Sampler for the DSFS-side experiment carrier: draws one realization of
`(h, p)` from the duplex-sponge oracle distribution `𝒟_𝔖` (CO25 Def. 4.2).  The carrier is
held fixed by `hyb0Impl` for the entire game run. -/
def hyb0Init :
    ProbComp (DuplexSpongeOracleFamily StmtIn U) :=
  D_𝔖.sample StmtIn U

/-- CO25 §5.8 Hyb_0. Stateless query handler for the DSFS-side experiment: ambient `oSpec`
queries → caller-supplied `oSpecImpl`; duplex-sponge queries (`h`, `p`, `p⁻¹`) →
`duplexSpongeOracleQueryImpl k_DS`.  `k_DS` is sampled once at game start by `hyb0Init` and held
fixed (CO25 Def. 4.2).  The paper has no ambient distribution; we take an arbitrary
`QueryImpl oSpec ProbComp` instead. -/
def hyb0Impl
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (DuplexSpongeOracleFamily StmtIn U) ProbComp) :=
  fun q =>
    match q with
    | .inl qShared => do
        let resp ← StateT.lift <| oSpecImpl qShared
        pure resp
    | .inr qDS => D_𝔖.answer qDS

/-! ### Common hybrid game skeleton (Figure 4 lines 2–3) -/

/-- CO25 §5.8. Common hybrid game skeleton (Figure 4 lines 2–3): run `𝒫̃^{D2SQuery^g}` and
`𝒱^{D2SQuery^g}` exposing only the chosen external challenge-oracle family, then project
away the auxiliary unit-sampling randomness. Polymorphic over the **inner state type `M`**
that `gImpl` carries beneath `D2SQuery`'s own `StateT (D2SQueryState …)` layer:

- `Hyb_1` / `Hyb_2`: trivial inner state `M := PUnit` (no memo — pass `StateT.lift ∘ oldGImpl`).
- `Hyb_3` (paper §5.4 D2SAlgo Item 3): `M := D2SAlgoMemo …`, the `tr_i` memo.

The prover and the verifier share one `D2SQuery` state (trace, `tr_∇`, `Cache_p`): the verifier
phase resumes the state the prover phase returns, as in `(𝒫̃ ‖ 𝒱)^{D2SQuery}`. The inner state
`M` is **not** shared. Each phase starts from `default`. The `tr_i` memo belongs to one run of
`D2SAlgo(𝒫̃)` (§5.4 D2SAlgo Item 1 initializes it), and the Hyb₃ verifier
`𝒱^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (Figure 4 line 3) is not part of that run. If the verifier resumed the
prover's memo, each of its boundary `gᵢ` calls would be a memo hit and would query no `fᵢ`, so
Hyb₃'s verifier segment of the trace would be empty, while Hyb₂ and Hyb₄ log one challenge query
per round. With a fresh memo, each verifier `gᵢ` call queries `fᵢ`. Its fresh `ψ⁻¹` preimage is
discarded by Item 4(e)ii, because the prover's `tr_∇.p` already holds the boundary pair.

For `M := PUnit` the inner state is vacuous; for `M := D2SAlgoMemo …` the prover phase is
`𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper Eq. 17 RHS), mirroring `D2FQueryProver` in
`ProverTransform.lean`.

If the prover phase aborts, the game continues with `default` statement and proof
`(default : StmtIn, (default : Vector U δ, default))`, which `hybridGameDist` reports as
`π = (SaltCodec.encode default, default)`. `basicFiatShamirGame` substitutes the same proof, so
Hyb₃ and Hyb₄ handle a prover abort identically.

The game returns `none` when the verifier rejects or its simulation aborts (`stmtOut?.getM`), so
`(𝕩, π, tr)` is discarded on rejection; see `BasicFiatShamirGameOutput`. -/
def hybridGame
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
        TaggedQueryLog (oSpec + challengeSpec)) := do
  -- Run the prover from fresh simulator states; retain its log even if simulation fails.
  let proverComp := d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default
  let ⟨proverTriple?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle proverComp.run).run
  -- Success preserves both states; failure selects defaults, not the partial failed state.
  -- The prover's separately collected query log remains available in either case.
  let ⟨stmtIn, proof, d2sState₁⟩ :=
    match proverTriple? with
    | some ⟨⟨⟨stmtIn, proof⟩, d2sState₁⟩, _⟩ => (stmtIn, proof, d2sState₁)
    | none => (default, default, default)
  -- Run the honest forward-only verifier using the selected statement and proof.
  let rawVerifierComp := runForwardVerifierWide δ V stmtIn proof
  -- Resume the prover's D2SQuery state (trace, tables, synthesis cache). The inner `gImpl`
  -- state (Hyb₃'s `tr_i` memo) starts fresh: `tr_i` is local to the prover's `D2SAlgo` run.
  let verifierComp := d2fRawFrom (T_H := T_H) (T_P := T_P)
    gImpl rawVerifierComp d2sState₁ default
  -- V has same simulated (h,p,p⁻¹) oracle access via `D2SQuery^{gImpl}` as P~.
  let ⟨verifierTriple?, verifyQueryLogRaw⟩ ← (simulateQ loggingOracle verifierComp.run).run
  -- Simulation failure and the verifier's own rejection both remain rejection.
  let stmtOut? :=
    match verifierTriple? with
    | some ⟨⟨stmtOut?, _⟩, _⟩ => stmtOut?
    | none => none
  let proveQueryLog :=
    filterD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) proveQueryLogRaw
  let verifyQueryLog :=
    filterD2SChallengePlusUnitQueryLog
      (oSpec := oSpec) (U := U) verifyQueryLogRaw
  let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
  let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
  return ⟨stmtIn, ← stmtOut?.getM, proof, taggedP ++ taggedV⟩

/-! ### Distribution wrappers (game → `ProbComp`) -/

/-- CO25 §5.8. Distribution of a Section 5.8 hybrid game after applying its line-4 trace map
(Figure 4 line 4: `tr := (φ⁻¹,ψ)(tr_𝒫̃ ‖ tr_𝒱)` or `φ⁻¹(…)` or identity).  Collapses the
hybrid game output to `BasicFiatShamirGameOutput`, enabling the TV-distance chain of
Claims 5.21–5.24. Polymorphic over the **inner state type `M`** that `gImpl` carries
(trivial `PUnit` for `Hyb_1` / `Hyb_2`; `D2SAlgoMemo …` for `Hyb_3`'s `tr_i` table —
see `hybridGame`). -/
def hybridGameDist -- apply traceMap into output of `hybridGame`
    [instSampleable : SampleableType U]
    [∀ i, DecidableEq (pSpec.Message i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {M : Type} [Inhabited M]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (StateT σ ProbComp))
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) challengeSpec) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := do
  let hybridOutput ←
    (simulateQ impl
      ((hybridGame
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U)
        gImpl V P).run)).run' (← init)
  match hybridOutput with
  | none => return none
  | some
      (⟨stmtIn, stmtOut, proof, projectedTrace⟩ :
        StmtIn × StmtOut × DSSaltedProof (pSpec := pSpec) (U := U) δ ×
          TaggedQueryLog (oSpec + challengeSpec)) => do
      -- Paper Items 4-6: bridge on-sponge `Vector U δ` salt → FS-std `Salt` via
      -- `SaltCodec.encode = bin` at the hybrid game boundary.
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)
          traceMap projectedTrace
      match outputFS? with
      | none => -- NOTE: this is for consistency with `mappedDSFSGameDist`, even though the
        -- line-4 maps of `Hyb₁`–`Hyb₃` (the only users of this wrapper) never abort
        return some (stmtIn, stmtOut, π, [])
      | some fullTraceFS =>
          return some (stmtIn, stmtOut, π, fullTraceFS)

/-- CO25 Lemma 5.1. Distribution of the basic-FS game (`Hyb_4` right-hand side) under a
concrete oracle implementation (oracle family `𝒟_IP`). Used for `hyb_4`. -/
def basicFiatShamirGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  (simulateQ impl (basicFiatShamirGame (V := V) (Salt := Salt) (δ := δ) P)).run' (← init)

/-- CO25 Lemma 5.1. Distribution of the DSFS game (`Hyb_0` left-hand side) under a concrete
oracle implementation (oracle family `𝒟_𝔖`). Used via `mappedDSFSGameDist`. -/
def dsfsGameDist
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) := do
  (simulateQ impl (dsfsGame (V := V) P)).run' (← init)

/-- CO25 Lemma 5.1. Left experiment of Lemma 5.1 (`Hyb_0`): run the DSFS game under
`𝒟_𝔖(λ,n)` and apply the line-4 trace map D2STrace = `(φ⁻¹, ψ) ∘ StdTrace` to produce a
basic-FS query log. This is the full output distribution of the left experiment of Lemma 5.1, not
only its acceptance probability `Pr[𝒱^{h,p}(𝕩, π) = 1]`. -/
def mappedDSFSGameDist
    [instSampleable : SampleableType U]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) := do
  let outputDS ← dsfsGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) init impl V P
  -- should run D2STrace directly in dsfsGameDist?
  match outputDS with
  | none => return none
  | some ⟨stmtIn, stmtOut, proof, fullTraceDS⟩ => do
      -- Paper Items 4-6: bridge on-sponge `Vector U δ` salt → FS-std `Salt` via
      -- `SaltCodec.encode = bin` at the DS→FS boundary on the LHS experiment.
      let π : FSSaltedProof pSpec Salt :=
        (SaltCodec.encode (Salt := Salt) proof.1, proof.2)
      let outputFS? ←
        runSection58TraceMap
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          traceMap fullTraceDS
      match outputFS? with
      -- Trace-synthesis abort (a sponge bad event) is a distinguished bad-trace value, NOT a
      -- suppressed acceptance: the verifier's `(𝕩, stmtOut)` decision survives. Matches CO25
      -- Hyb₀, where a `tr = ⊥` bad event keeps the acceptance bit `b`; the abort then lives only
      -- in the trace component, inside `Δ(Hyb₀, Hyb₄) ≤ η★` (Claims 5.21–5.24), rather than
      -- wrongly zeroing the soundness event.
      | none => return some (stmtIn, stmtOut, π, [])
      | some fullTraceFS => return some (stmtIn, stmtOut, π, fullTraceFS)

end SecurityGames

section KeyLemma

open scoped NNReal

/-! ### Numerical bounds: `θ★`, `CodecBias`, `η★`, per-claim bounds -/

/-- CO25 Lemma 5.1 / Eq. (6). `θ★(t) := t_p` — forward-permutation query budget of `𝒫̃`,
used as the query-bound multiplier in `η★` and as the challenge-query bound of `D2SAlgo(𝒫̃)`.

Eq. (6) also assumes `t_p ≥ max {L_P, L_V}`. The paper uses that condition only for the running
time of `D2SAlgo` (Eq. 18). The query-count and statistical-distance statements in this file do not
need it, and this file states no cost bound. Operation counts of `D2SAlgo` can be expressed with
VCVio's resource model (`CostModel`, `ResourceProfile`, `MeasuredProgram`) and ArkLib's
`MeasuredKnowledgeCertificate` / `StateRestorationBudget`; a bound on complete execution time
cannot be expressed yet. A cost statement for `D2SAlgo` must take `t_p ≥ max {L_P, L_V}` as a
hypothesis again. -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-- CO25 Definition 4.1. Per-round codec bias profile `i ↦ ε_{cdc,i}(λ,n)`.
Parameters `(λ, n)` are suppressed (assumed fixed by the ambient instantiation); `CodecBias`
carries only the per-round values `ε_{cdc,i}` used in Claims 5.22 and the `η★` formula. -/
abbrev CodecBias :=
  pSpec.ChallengeIdx → ℝ≥0

/-- CO25 Lemma 5.1 / Eq. (5). Additive error bound `η★(t_h, t_p, t_{p⁻¹})`:
```
η★ := numerator / (2 · |Σ|^c) + θ★ · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}
```
where `numerator = 7t² + 28(L+1)t + 14(L+1)² − 3t − 6(L+1)` with
`t = t_h + t_p + t_{p⁻¹}` and `L` an upper bound on the verifier's forward-permutation queries.
For the salted hybrids, callers instantiate `L` with
`L_totalRateBlocks δ pSpec = L_δ + L_P + L_V`. This is the sum of the four bounds from Claims
5.21 (Hyb_0 → Hyb_1), 5.22 (Hyb_1 → Hyb_2), 5.23 = 0 (Hyb_2 → Hyb_3), and 5.24
(Hyb_3 → Hyb_4); see `ηStar_eq_claimBounds`.

The printed Eq. (5) ends in `− 13(L+1)`. That value inherits the closed form printed in Claim
5.24, which is smaller than the claim's own sum (Eq. 56) by `7(L+1)/(2|Σ|^c)`; see
`claim5_24Bound`. With the closed form of the sum, the numerator ends in `− 6(L+1)`. -/
def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  let tTotalR : ℝ := tTotal
  let LplusOneR : ℝ := (L + 1)
  let firstTermNumerator : ℝ :=
    7 * tTotalR ^ 2
      + 28 * LplusOneR * tTotalR
      + 14 * LplusOneR ^ 2
      - 3 * tTotalR
      - 6 * LplusOneR
  let firstTermDenominator : ℝ := 2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  let secondTerm : ℝ := (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
  let thirdTerm : ℝ := ∑ i, (εcodec i : ℝ)
  firstTermNumerator / firstTermDenominator + secondTerm + thirdTerm

/-- CO25 Claim 5.21. Statistical-distance bound for `Hyb_0` vs `Hyb_1` (Eq. from the claim):
`(7·T² − 3·T) / (2·|Σ|^c)` where `T = t_h + 1 + t_p + L + t_{p⁻¹}`. -/
def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- CO25 Claim 5.22. Statistical-distance bound for `Hyb_1` vs `Hyb_2` (Eq. 54):
`θ★(t_h, t_p, t_{p⁻¹}) · max_i ε_{cdc,i} + ∑_i ε_{cdc,i}`. -/
def claim5_22Bound
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

/-- CO25 Claim 5.24. Statistical-distance bound for `Hyb_3` vs `Hyb_4`: the closed form of the
sum in Eq. (56),
```
(7·(L+1)·(2t + 1 + L) − 3·(L+1)) / (2·|Σ|^c),   t = t_h + t_p + t_{p⁻¹}.
```
`claim5_24Bound_eq_sum` proves that this equals the Eq. (56) sum
`∑_{j=t+1}^{t+1+L} (2(j−1) + (2j−1) + (2j−1) + (j−1)) / |Σ|^c`, and `claim5_24Bound_nonneg`
proves that it is nonnegative.

Paper discrepancy: the paper prints the closed form
`7(L+1)(2t + 1 + L)/(2|Σ|^c) − 5(L+1)/|Σ|^c`. It is smaller than the Eq. (56) sum by
`7(L+1)/(2|Σ|^c)` and is negative at `t = L = 0`. -/
def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let t : ℝ := (tₕ + tₚ + tₚᵢ : ℕ)
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  (7 * ((L : ℝ) + 1) * (2 * t + 1 + L) - 3 * ((L : ℝ) + 1)) / (2 * cardPow)

/-- The Claim 5.24 bound is the closed form of the Eq. (56) sum over
`j = t + 1, …, t + 1 + L`, where `t = t_h + t_p + t_{p⁻¹}`. The `j`-th summand is the
Lemma 5.8 bound `2(j−1) + (2j−1) + (2j−1) + (j−1) = 7j − 5` over `|Σ|^c`. -/
theorem claim5_24Bound_eq_sum (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) :
    claim5_24Bound U tₕ tₚ tₚᵢ L =
      ∑ j ∈ Finset.Icc (tₕ + tₚ + tₚᵢ + 1) (tₕ + tₚ + tₚᵢ + 1 + L),
        (2 * ((j : ℝ) - 1) + (2 * (j : ℝ) - 1) + (2 * (j : ℝ) - 1) + ((j : ℝ) - 1)) /
          ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C := by
  rw [← Finset.sum_div, claim5_24Bound]
  set c : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  set t := tₕ + tₚ + tₚᵢ
  have hsum : ∀ M : ℕ, ∑ j ∈ Finset.Icc (t + 1) (t + 1 + M),
      (2 * ((j : ℝ) - 1) + (2 * (j : ℝ) - 1) + (2 * (j : ℝ) - 1) + ((j : ℝ) - 1)) =
        (7 * ((M : ℝ) + 1) * (2 * (t : ℝ) + 1 + M) - 3 * ((M : ℝ) + 1)) / 2 := by
    intro M
    induction M with
    | zero => simp; ring
    | succ M ih =>
      rw [← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [hsum L, div_div]

/-- The Claim 5.24 bound is nonnegative for every query budget and every `L`. -/
theorem claim5_24Bound_nonneg (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : 0 ≤ claim5_24Bound U tₕ tₚ tₚᵢ L := by
  unfold claim5_24Bound
  apply div_nonneg
  · have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have ht : (0 : ℝ) ≤ ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · positivity

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- CO25 Eq. (5) is the sum of the per-claim bounds: Claims 5.21, 5.22, 5.23 (`= 0`) and 5.24. -/
theorem ηStar_eq_claimBounds (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) (εcodec : CodecBias (pSpec := pSpec)) :
    ηStar (pSpec := pSpec) U tₕ tₚ tₚᵢ L εcodec =
      claim5_21Bound U tₕ tₚ tₚᵢ L + claim5_22Bound tₕ tₚ tₚᵢ εcodec +
        claim5_24Bound U tₕ tₚ tₚᵢ L := by
  unfold ηStar claim5_21Bound claim5_22Bound claim5_24Bound
  push_cast
  ring

/-! ### Hybrid distributions `Hyb_0` … `Hyb_4` and per-step claims 5.21–5.24 (CO25 §5.8)

Each `Hyb_X` is defined immediately before the claim that bounds `Δ(Hyb_X, Hyb_{X+1})`,
mirroring the paper's narrative: introduce both endpoints, bound the gap, advance to the next
hybrid. -/

/-- CO25 §5.8 Hyb_0. `Hyb_0` left-experiment distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
duplex-sponge oracle `(h, p, p⁻¹) ← 𝒟_𝔖(λ,n)` (CO25 Def. 4.2) sampled eagerly via
`D_𝔖.sample`. Line-4 trace map = D2STrace = `(φ⁻¹, ψ) ∘ StdTrace`.
Samples `(h, p)` eagerly at game start rather than via a lazy random-oracle cache for `h`. -/
def hyb_0
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) -- (x, π)
    (traceMap : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) :=
  mappedDSFSGameDist (instSampleable := VCVCompatible.toSampleableType)
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (Salt := Salt)
    (init := hyb0Init (StmtIn := StmtIn) (U := U))
    (impl := hyb0Impl (oSpec := oSpec) (StmtIn := StmtIn) (U := U) oSpecImpl)
    V maliciousProver (traceMap := traceMap)

/-- CO25 §5.8 Hyb_1. `Hyb_1` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
encoded challenge oracle
`g := (g_i)_{i ∈ [k]} ← 𝒟_Σ(λ,n)` (CO25 Eq. 16) sampled eagerly via
`D_Sigma.sample`, auxiliary `(Unit →ₒ U)` and `unifSpec` slots handled
inline (fresh per call).

Line-4 trace map is `(φ⁻¹, ψ)(tr_𝒫̃ ‖ tr_𝒱)` (`hyb1Line4Trace`). -/
def hyb_1
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := gSpec (U := U) StmtIn pSpec δ -- implemented via using `g ← D_g`
  let sampleChallenge := D_Sigma.sample (instSampleable := instSampleableTypeEncodedChallengeOracle)
    (U := U) StmtIn pSpec δ
  -- `Hyb_1` `gᵢ`-realization: forward each `gSpec` query straight into the encoded challenge
  -- oracle exposed by `challengeSpec`.  No `ψᵢ⁻¹` step is needed since `challengeSpec`
  -- already returns the encoded `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`.  Trivial inner state `M := PUnit` —
  -- `StateT.lift` adds the vacuous `StateT PUnit` layer required by the unified
  -- `hybridGameDist` skeleton (paper's `tr_i` memo collapses to `()` here).
  let gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec PUnit :=
    fun q =>
      StateT.lift <|
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (Vector U (challengeSize (pSpec := pSpec) q.1)) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
              (.inl q))
  exact
    hybridGameDist (instSampleable := VCVCompatible.toSampleableType)
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := sampleChallenge)
      (impl := hybChallengeImpl (instSampleable := VCVCompatible.toSampleableType)
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl)
      (gImpl := gImpl) V maliciousProver
      (hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-! ### Malicious-prover query bounds -/

/-- DS hash queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1HashQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- DS forward-permutation queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1PermQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inl _)) => True
  | _ => False

/-- DS inverse-permutation queries in the combined Lemma 5.1 prover surface. -/
def isLemma5_1PermInvQuery :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- CO25 Lemma 5.1 query-bound predicate for the malicious prover `𝒫̃`.
`t_h`, `t_p`, and `t_{p⁻¹}` are aggregate bounds for the hash, forward-permutation, and
inverse-permutation oracle families. The ambient `oSpec` handler is unconstrained: CO25's
statement contains no ambient-oracle query budget. -/
abbrev IsLemma5_1QueryBound
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop := by
  classical
  exact OracleComp.IsQueryBoundP maliciousProver
      (isLemma5_1HashQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₕ ∧
    OracleComp.IsQueryBoundP maliciousProver
      (isLemma5_1PermQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚ ∧
    OracleComp.IsQueryBoundP maliciousProver
      (isLemma5_1PermInvQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚᵢ

/-- CO25 §5.8 Hyb_2. `Hyb_2` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
decoded challenge oracle
`e := (e_i)_{i ∈ [k]}` (CO25 Eq. 53) sampled eagerly via `D_e.sample`,
auxiliary slots inline. Line-4 trace map is `φ⁻¹(tr_𝒫̃ ‖ tr_𝒱)`
(`hyb2Line4Trace`). -/
def hyb_2
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := eSpec (U := U) StmtIn pSpec δ
  let sampleChallenge := D_e.sample (instSampleable := instSampleableTypeDecodedChallengeOracle)
    (U := U) StmtIn pSpec δ
  -- `Hyb_2` `gᵢ`-realization: query the decoded challenge oracle `eᵢ` for
  -- `ρᵢ ∈ ℳ_{V,i}`, then sample a uniform `ψᵢ⁻¹` preimage to recover the encoded
  -- `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` (CO25 §5.4 Item 4(e)i).  Trivial inner state `M := PUnit`
  -- (`StateT.lift` wraps the no-memo body for the unified `hybridGameDist`).
  let gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec PUnit :=
    fun q => do
      let challenge ← -- query to `e`
        StateT.lift <|
          OptionT.lift <|
            (show OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (pSpec.Challenge q.1) from
              query
                (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (.inl q))
      StateT.lift <|
        OptionT.lift <|  -- apply `ψᵢ⁻¹` on the response `pᵢ` to get `p̂ᵢ`
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := challengeSpec) challenge
  exact
    hybridGameDist (instSampleable := VCVCompatible.toSampleableType)
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := sampleChallenge)
      (impl := hybChallengeImpl (instSampleable := VCVCompatible.toSampleableType)
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl)
      gImpl V maliciousProver
      (hyb2Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_3. `Hyb_3` distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`,
salted Fiat–Shamir oracle
`f := (f_i)_{i ∈ [k]} ← 𝒟_IP(λ,n)` (CO25 Eq. 55) sampled eagerly via
`D_IP_salted.sample`, auxiliary slots inline. Line-4 trace map is identity
(`hyb3Line4Trace`). -/
def hyb_3
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let sampleChallenge :=
    D_IP_salted.sample (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  -- `Hyb_3` `gᵢ`-realization (CO25 Eq. 17): `φ⁻¹` parse encoded prefix → query salted
  -- `fᵢ` oracle (keyed at `StmtIn × Salt`, with the on-sponge `Vector U δ` salt
  -- bridged via `SaltCodec.encode = bin`) → `ψᵢ⁻¹` uniform preimage.  The `OptionT`
  -- abort layer carries `φ⁻¹` parse failure (⊥ on malformed encoded-message prefixes).
  -- CO25 §5.4 D2SAlgo Item 3 — paper's `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` threads a `tr_i` memo
  -- (`d2sCodecBridgeImplMemo`) so repeated encoded `gᵢ` keys reuse the cached `ρ̂_i`. The memo
  -- is local to each phase of `hybridGame`: the verifier phase starts with an empty memo, so
  -- each of its `gᵢ` calls queries `fᵢ` (see `hybridGame`).
  let gImpl := d2sCodecBridgeImplMemo (δ := δ) (Salt := Salt)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  exact
    hybridGameDist (instSampleable := VCVCompatible.toSampleableType)
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := sampleChallenge)
      (impl := hybChallengeImpl (instSampleable := VCVCompatible.toSampleableType)
        (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl)
      gImpl V maliciousProver
      (traceMap := hyb3Line4Trace (Salt := Salt) (oSpec := oSpec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- CO25 §5.8 Hyb_4. `Hyb_4` right-experiment distribution sampled via state-based evaluation
(`simulateQ` with `StateT`): ambient `oSpec` answered by caller-supplied `oSpecImpl`, salted
Fiat–Shamir oracle `f ← 𝒟_IP(λ,n)` (CO25 §5.8 Hyb₄, Figure 4 line 1) sampled eagerly via
`D_IP_salted.sample`, the same distribution as `Hyb_3`. Lemma 5.1 instantiates
`d2sAlgoTransform` with `ProverTransform.d2sAlgo` (see `Lemma5_1Statement`).

Differences from `Hyb_3` (`hybridGame` at `M := D2SAlgoMemo …`, `gImpl := d2sCodecBridgeImplMemo`):

- Prover. `Hyb_3` runs `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (`d2fRaw` with the memoized bridge) and keeps
  the on-sponge salt `Vector U δ`; `hybridGameDist` reports `π = (bin τ, messages)`. `Hyb_4`
  runs `d2sAlgo`, which is the same pipeline (`D2FQueryProver`) followed by `bin` on the salt
  (D2SAlgo Items 4-6), and returns `FSSaltedProof pSpec Salt` directly. The two prover phases make
  the same queries. On a prover abort both games continue with the proof
  `(default, (SaltCodec.encode default, default))`.
- Verifier. `Hyb_3` runs `𝒱^{h,p}` on the DSFS proof, with its `(h, p)` queries answered by
  `D2SQuery` from the prover's `D2SQuery` state and a fresh `tr_i` memo; it can abort inside
  `D2SQuery`. `Hyb_4` runs `𝒱_std^f` (`basicFSVerifierComp`) on the FS proof and queries `f` at
  `(𝕩, bin τ, messages)` directly.

CO25 Claim 5.24 bounds the distance by `Pr[E_𝒱]`, the probability that the verifier's `D2SQuery`
aborts while the prover's does not, and Eq. (57) states that the hybrids agree otherwise. Neither
step is formalized. The paper's argument compares the decision bits and the challenges `ρᵢ`;
the trace components `tr` must also agree for the full output distributions to agree. -/
def hyb_4
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Salt := Salt)) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  let challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec
  let sampleChallenge :=
    D_IP_salted.sample (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
  exact basicFiatShamirGameDist
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (Salt := Salt) (δ := δ)
    (init := sampleChallenge)
    (impl := hybChallengeImpl (instSampleable := VCVCompatible.toSampleableType)
      (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec) oSpecImpl)
    V (d2sAlgoTransform maliciousProver)

/-! ### Query-bound interfaces for a future Lemma 5.1 proof -/

/-- Basic-FS challenge queries made by `D2SAlgo`; ambient queries and its private sampling
oracles are deliberately excluded. -/
def isD2SAlgoChallengeQuery :
    (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- CO25 Lemma 5.1's `θ★` query bound for the transformed prover. This counts precisely the
basic-FS challenge-oracle calls; `oSpec` and D2SAlgo's private sampling oracles are not adversary
queries in the target FS security game. -/
abbrev IsD2SAlgoChallengeQueryBound
    (prover : AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) (StmtIn × FSSaltedProof pSpec Salt))
    (t : ℕ) : Prop := by
  classical
  exact OracleComp.IsQueryBoundP prover
    (isD2SAlgoChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (Salt := Salt) (pSpec := pSpec)) t

/-! ### `θ★` query bound of `D2SAlgo` -/

section ThetaStarBound

open DuplexSpongeFS.D2SAlgoQueryBound DuplexSpongeFS.ProverTransform

omit [VCVCompatible StmtIn] [VCVCompatible Salt] in
lemma d2fOuterImpl_queryBound
    {_ : DecidablePred (isLemma5_1PermQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U))}
    {_ : DecidablePred (isD2SAlgoChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (Salt := Salt) (pSpec := pSpec))}
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U)) :
    StateQueryBound (((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
      (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))) t).run s₁)
      (isD2SAlgoChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (Salt := Salt) (pSpec := pSpec))
      (if isLemma5_1PermQuery t then 1 else 0) := by
  intro s₂
  rcases t with oq | dq
  · refine IsQueryBoundP.mono (n := 0) ?_ (Nat.zero_le _)
    exact stateQueryBound_lift (x := liftM (OracleSpec.query
      (spec := oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)) (Sum.inl oq)))
        ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim) s₂
  · simp only [d2fOuterImpl, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply]
    have hk : (if isDSPermQuery dq then 1 else 0) =
        (if isLemma5_1PermQuery (oSpec := oSpec) (Sum.inr dq) then 1 else 0) := by
      rcases dq with _ | _ | _ <;> simp [isDSPermQuery, isLemma5_1PermQuery]
    rw [← hk]
    refine isQueryBoundP_simulateQ (p := isChallengeSlotQuery (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sQueryImpl_queryBound (T_H := T_H) (T_P := T_P) (fun aux s => ?_) dq s₁ s₂) fun t => ?_
    · exact stateQueryBound_lift (x := liftM (OracleSpec.query
        (spec := D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)) (Sum.inr aux)))
        ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim) s
    · refine isQueryBoundP_liftM_query t fun h => ?_
      rcases t with _ | _
      · exact Nat.one_pos
      · exact h.elim

omit [VCVCompatible StmtIn] [VCVCompatible Salt] in
theorem isD2SAlgoChallengeQueryBound_d2sAlgo
    (P : MaliciousProver oSpec pSpec StmtIn U δ) (tₕ tₚ tₚᵢ : ℕ)
    (h : IsLemma5_1QueryBound P tₕ tₚ tₚᵢ) :
    IsD2SAlgoChallengeQueryBound
      (ProverTransform.d2sAlgo (Salt := Salt) (T_H := T_H) (T_P := T_P) P)
      (θStar tₕ tₚ tₚᵢ) := by
  classical
  obtain ⟨-, hp, -⟩ := h
  have hraw := isQueryBoundP_simulateQ_StateT_StateT_OptionT hp
    (fun t s₁ => d2fOuterImpl_queryBound (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ)
      (Salt := Salt) (T_H := T_H) (T_P := T_P) t s₁) default default
  unfold IsD2SAlgoChallengeQueryBound θStar
  unfold d2sAlgo D2FQueryProver d2fRaw d2fRawFrom
  change IsQueryBoundP (OptionT.run _) _ _
  rw [OptionT.run_bind, Option.elimM]
  refine (isQueryBoundP_bind (n := tₚ) (m := 0) ?_ fun o _ => ?_).mono (by simp)
  · rw [OptionT.run_map, OptionT.run_map, isQueryBoundP_map_iff, isQueryBoundP_map_iff]
    exact hraw
  · rcases o with _ | ⟨_, _, _⟩ <;> exact trivial

end ThetaStarBound

/-! ### CO25 Lemma 5.1 as a proposition -/

/-- CO25 Lemma 5.1, stated as a proposition (its proof is deferred). For a nondegenerate round
schedule (`NondegenerateRounds`) and every `(t_h, t_p, t_{p⁻¹})`-query malicious prover `𝒫̃`
(`IsLemma5_1QueryBound`):
- the left experiment `Hyb_0` with the line-4 map `D2STrace` (`d2sTraceSalted`) and the right
  experiment `Hyb_4` with `D2SAlgo` (`ProverTransform.d2sAlgo`) are `η★`-close, with `L`
  instantiated by `L_totalRateBlocks δ pSpec` (see `ηStar`);
- `D2SAlgo(𝒫̃)` makes at most `θ★(t_h, t_p, t_{p⁻¹})` challenge queries (the "Moreover" clause).

The ambient handler `oSpecImpl` and the verifier `V` are parameters; the paper has no ambient
oracle (take `oSpec` empty). The games compare `Option` outputs that discard `(𝕩, π, tr)` on
rejection; see `BasicFiatShamirGameOutput`. -/
def Lemma5_1Statement
    [∀ i, DecidableEq (pSpec.Message i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  NondegenerateRounds pSpec →
    ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        discreteTVDist
            (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
              oSpecImpl V maliciousProver
              (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
                (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
            (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
              oSpecImpl V maliciousProver
              (ProverTransform.d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
                (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
          ≤ ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias
        ∧ IsD2SAlgoChallengeQueryBound
            (ProverTransform.d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) maliciousProver)
            (θStar tₕ tₚ tₚᵢ)


end KeyLemma

end DuplexSpongeFS.KeyLemma
