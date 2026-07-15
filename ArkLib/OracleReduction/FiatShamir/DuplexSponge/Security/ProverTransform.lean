/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SCacheHistory
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SSynthesis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

/-!
# Prover transformation

This file contains the prover transformation (via query simulation) for the analysis of duplex
sponge Fiat-Shamir, following Section 5.4 in the paper.

Note: The paper's §5.5.2 D2STrace Step 3 `bin(τ) ∈ {0,1}^{δ_*}` salt binarization is modeled
using the `SaltCodec` class from `Defs.lean`, decoupling the FS-standard `Salt` type from
the on-sponge `Vector U δ` type.
-/

open OracleComp OracleSpec ProtocolSpec
namespace DuplexSpongeFS.ProverTransform
open Backtrack Lookahead DSTraceStorage TraceTransform
variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : Nat}

local instance : Inhabited U := ⟨0⟩
noncomputable section

section D2SQueryHelpers
variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- Executable approximation of Item 4(d)/(e) tuple-image branching, tightened with
`BackTrack`-shape checks and challenge-block length sanity. -/
private def messageInSerializeImage
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) : Bool := by
  exact decide (∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = encoded)

/-- Executable check for the paper branch condition
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)` on one parsed `BackTrack` output. -/
def backtrackOutputMessagesInImage
    (inImage : (msgIdx : pSpec.MessageIdx) → Vector U (messageSize msgIdx) → Bool)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let before : List pSpec.MessageIdx := messageIdxListBefore (pSpec := pSpec) out.roundIdx
  before.attach.all fun ⟨j, hj⟩ =>
    let hlt : j.1 < out.roundIdx.1 := of_decide_eq_true (List.mem_filter.mp hj).2
    inImage j (out.encodedMessages ⟨j, hlt⟩)

/-- Executable Item-4(d)/(e) branch predicate, exposed so support proofs can name the
algorithmic case split rather than rely on anonymous `split` hypotheses.  It is CO25 §5.4's
predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)`, decided by `Serialize`-image checks on the encoded
messages recovered by `BackTrack`. -/
noncomputable def d2sInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  backtrackOutputMessagesInImage
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (inImage := messageInSerializeImage (pSpec := pSpec) (U := U))
    (out := out)

/-- CO25 §5.4 — `𝒰(Σ)` realization of `Unit →ₒ U` in `ProbComp`; used by §5.4 fresh-sample
branches (Items 2(b), 3(b), 4(c)iii, 4(e)iiiC). -/
def d2sUnitSampleImpl [SampleableType U] :
    QueryImpl (Unit →ₒ U) ProbComp :=
  fun
  | () => $ᵗ U

end D2SQueryHelpers

section D2SChallengePlusUnit

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]


/-- CO25 §5.8 — Finite preimage set of a verifier-message decoder `ψᵢ`.

`{α̂ ∈ Σ^{ℓ_V(i)} | ψᵢ(α̂) = α}` for a target challenge `α : ℳ_{V,i}`. Backs the uniform
preimage sampler `uniformDeserializePreimage`; surjectivity of `ψᵢ` (`Codec.decode_surjective`)
guarantees nonemptiness. -/
noncomputable def deserializePreimageFinset
    {i : pSpec.ChallengeIdx}
    [Fintype U] [DecidableEq U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (challenge : pSpec.Challenge i) :
    Finset (Vector U (challengeSize (pSpec := pSpec) i)) := by
  let _ : Fintype (Vector U (challengeSize (pSpec := pSpec) i)) :=
    Fintype.ofEquiv (Fin (challengeSize (pSpec := pSpec) i) → U) Equiv.rootVectorEquivFin.symm
  exact (Finset.univ : Finset (Vector U (challengeSize (pSpec := pSpec) i))).filter fun encoded =>
    Deserialize.deserialize encoded = challenge

/-- Sample a uniformly random element from a non-empty list using the `unifSpec` branch. -/
def sampleFromList {α κ : Type} {challengeSpec : OracleSpec κ} [SpongeUnit U]
    (l : List α) (hl : l ≠ []) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) α := do
  let idxRaw ← query
    (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
    (.inr (.inr (l.length - 1))) -- from unifSpec
  let idx : Fin l.length := ⟨idxRaw.1, by
    have hlen_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
    have hlen_eq : (l.length - 1) + 1 = l.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)
    simpa [hlen_eq] using idxRaw.2⟩
  pure (l.get idx)

/-- CO25 §5.4 / §5.8 — Uniform `ψᵢ⁻¹` preimage sampler: samples `α̂ ←$ ψᵢ⁻¹(α)` by toListing
`deserializePreimageFinset α` and indexing via `unifSpec` -/
noncomputable def uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U (challengeSize (pSpec := pSpec) i)) := do
  have hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty := by
    rcases codec.decode_surjective i challenge with ⟨encoded, hencoded⟩
    have hencoded' : Deserialize.deserialize encoded = challenge := hencoded
    exact ⟨encoded, by simp [deserializePreimageFinset, hencoded']⟩
  let preimages := (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).toList
  have hpreimages_ne : preimages ≠ [] := by
    simpa [preimages] using hpreimages_nonempty.toList_ne_nil
  sampleFromList preimages hpreimages_ne

end D2SChallengePlusUnit

/-! ## Oracle-first `D2SQuery` API

CO25 §5.4 — `D2SQuery` oracle spec and direct-query helpers.

`d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` where
`gSpec = gSpec StmtIn pSpec δ` is the `gᵢ`-family oracle.
All sampling (`𝒰(Σ^c)`, `𝒰(Σ^{r+c})`, etc.) goes through `Unit →ₒ U`;
the `gᵢ` query is a single `.inl` injection into the sum spec. -/
section D2SQuery

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]

/-- CO25 §5.4 — `D2SQuery` oracle spec: `gSpec + ((Unit →ₒ U) + unifSpec)`.

- `gSpec` = `gSpec` — the `gᵢ`-family (Item 4(e)i)
- `Unit →ₒ U` — `𝒰(Σ)` for sampling `s_{C,out}`, `s_in`, `s_out`, etc.
- `unifSpec` — `Fin`-sampling for `ψᵢ⁻¹` preimage selection -/
abbrev d2sQueryOracles :=
  D2SChallengePlusUnitOracle
    (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)

/-- CO25 §5.4 Item 4(e)i — Query `gᵢ(𝕩, τ̂, α̂₁, …, α̂ᵢ) → ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`.

Direct `.inl` injection into `d2sQueryOracles`. -/
def d2sQueryG
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U (challengeSize (pSpec := pSpec) i)) :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inl ⟨i, (stmt, salt, encodedMessages)⟩)

/-- CO25 §5.4 — Sample `u ← 𝒰(Σ)` via `Unit →ₒ U`. -/
private def d2sSampleUnit :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) U :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inr (.inl ()))

/-- Sample `m` consecutive units; helper for `d2sSampleVector`. -/
private def d2sSampleArrayExact :
    (m : Nat) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let ⟨xs, hxs⟩ ← d2sSampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

private def d2sSampleVector :
    (m : Nat) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (Vector U m)
  | 0 => pure #v[]
  | m + 1 => do
      let xs ← d2sSampleVector m
      let u ← d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      pure (xs.push u)

/-- CO25 §5.4 Item 2(b) — Sample `s_{C,out} ← 𝒰(Σ^c)`. -/
def d2sSampleCapacity :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U SpongeSize.C) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.C

/-- CO25 §5.4 Items 3(b)/4(d)ii — Sample `s ← 𝒰(Σ^{r+c})`. -/
def d2sSampleState :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (CanonicalSpongeState U) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.N

private lemma d2sSampleVector_simulateQ_probEvent_eq
    [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (m : ℕ) (P : Vector U m → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)]
      =
    Pr[ P | ($ᵗ (Vector U m)) ] := by
  classical
  have hdist : ∀ x : Vector U m,
      Pr[= x |
        simulateQ
          (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)]
        =
      Pr[= x | ($ᵗ (Vector U m)) ] := by
    intro x
    induction m with
    | zero =>
        have hx : x = #v[] := by
          apply Vector.ext
          intro i hi
          omega
        have hcard : Fintype.card (Vector U 0) = 1 := by
          apply Fintype.card_eq_one_iff.mpr
          refine ⟨#v[], ?_⟩
          intro y
          apply Vector.ext
          intro i hi
          omega
        subst x
        simp [d2sSampleVector, probOutput_uniformSample, hcard]
    | succ m ih =>
        have hpush : Function.Injective2 (Vector.push (α := U) (n := m)) := by
          intro xs ys x y hxy
          simp [Vector.push_eq_push.mp hxy]
        rw [show
          simulateQ
              (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
              (d2sSampleVector
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) (m + 1))
            =
          Vector.push <$>
            simulateQ
              (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
              (d2sSampleVector
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m) <*>
            ($ᵗ U) by
          simp [d2sSampleVector, d2sSampleUnit, d2sUnitSampleImpl, monad_norm]]
        rw [show ($ᵗ (Vector U (m + 1))) =
          Vector.push <$> ($ᵗ (Vector U m)) <*> ($ᵗ U) by
          rfl]
        let xp : Vector U m := Vector.cast (by omega : m + 1 - 1 = m) x.pop
        have hxpush : Vector.push xp x.back = x := by
          dsimp [xp]
          have h : m + 1 - 1 = m := by omega
          cases h
          exact Vector.push_pop_back x
        rw [← hxpush]
        erw [probOutput_seq_map_eq_mul_of_injective2 _ _ _ hpush xp x.back,
          probOutput_seq_map_eq_mul_of_injective2 _ _ _ hpush xp x.back,
          ih (fun _ => True) xp]
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro x
  rw [hdist x]

/-- Event-level distribution of CO25 §5.4 Item 2(b):
sampling `s_{C,out} ← 𝒰(Σ^c)` through the D2S unit sampler is uniform over capacities. -/
lemma d2sSampleCapacity_simulateQ_probEvent_eq
    [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (P : Vector U SpongeSize.C → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))]
      =
    Pr[ P | ($ᵗ (Vector U SpongeSize.C)) ] := by
  unfold d2sSampleCapacity
  exact d2sSampleVector_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl SpongeSize.C P

/-- Event-level distribution of CO25 §5.4 Items 3(b)/4(d)ii:
sampling `s ← 𝒰(Σ^{r+c})` through the D2S unit sampler is uniform over sponge states. -/
lemma d2sSampleState_simulateQ_probEvent_eq
    [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (P : CanonicalSpongeState U → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))]
      =
    Pr[ P | ($ᵗ (CanonicalSpongeState U)) ] := by
  unfold d2sSampleState CanonicalSpongeState
  exact d2sSampleVector_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl SpongeSize.N P

/-- `OptionT`-lifted form of `d2sSampleCapacity_simulateQ_probEvent_eq`.

The concrete sigma Lemma-5.8 experiment runs `D2SQuery` in `OptionT ProbComp`; when the underlying
query implementation is just a monad-lift of the `ProbComp` implementation, capacity sampling
still has the uniform distribution, wrapped in `some`. -/
lemma d2sSampleCapacity_simulateQ_liftTarget_probEvent_eq
    [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (P : Option (Vector U SpongeSize.C) → Prop) :
    Pr[ P |
      (simulateQ
        ((gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)).liftTarget
          (OptionT ProbComp))
        (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run]
      =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (Vector U SpongeSize.C)) ] := by
  rw [simulateQ_liftTarget]
  let impl := gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)
  let comp := simulateQ impl
    (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
  have hlift : (liftM comp : OptionT ProbComp (Vector U SpongeSize.C)).run = some <$> comp := rfl
  change Pr[ P | (liftM comp : OptionT ProbComp (Vector U SpongeSize.C)).run] =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (Vector U SpongeSize.C)) ]
  rw [hlift]
  rw [probEvent_map]
  dsimp [comp, impl]
  exact d2sSampleCapacity_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl (fun sampled => P (some sampled))

/-- `OptionT`-lifted form of `d2sSampleState_simulateQ_probEvent_eq`. -/
lemma d2sSampleState_simulateQ_liftTarget_probEvent_eq
    [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (P : Option (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      (simulateQ
        ((gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)).liftTarget
          (OptionT ProbComp))
        (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run]
      =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (CanonicalSpongeState U)) ] := by
  rw [simulateQ_liftTarget]
  let impl := gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)
  let comp := simulateQ impl
    (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
  have hlift : (liftM comp : OptionT ProbComp (CanonicalSpongeState U)).run = some <$> comp := rfl
  change Pr[ P | (liftM comp : OptionT ProbComp (CanonicalSpongeState U)).run] =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (CanonicalSpongeState U)) ]
  rw [hlift]
  rw [probEvent_map]
  dsimp [comp, impl]
  exact d2sSampleState_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl (fun sampled => P (some sampled))

/-- Concrete `D_Σ` form of the `OptionT`-lifted capacity sampler lemma. -/
lemma d2sSampleCapacity_simulateQ_sigma_probEvent_eq
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (P : Option (Vector U SpongeSize.C) → Prop) :
    Pr[ P |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run]
      =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (Vector U SpongeSize.C)) ] := by
  have himpl :
      ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        =
      (((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g +
        ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)).liftTarget
          (OptionT ProbComp)) := by
    funext q
    cases q <;> rfl
  rw [himpl]
  exact d2sSampleCapacity_simulateQ_liftTarget_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g) P

/-- Concrete `D_Σ` form of the `OptionT`-lifted state sampler lemma. -/
lemma d2sSampleState_simulateQ_sigma_probEvent_eq
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (P : Option (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run]
      =
    Pr[ fun sampled => P (some sampled) | ($ᵗ (CanonicalSpongeState U)) ] := by
  have himpl :
      ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        =
      (((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g +
        ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)).liftTarget
          (OptionT ProbComp)) := by
    funext q
    cases q <;> rfl
  rw [himpl]
  exact d2sSampleState_simulateQ_liftTarget_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g) P

/-- CO25 §5.4 Item 4(e)iiiC — Sample `s_C^{(0)}, …, s_C^{(k-1)} ← 𝒰(Σ^c)`. -/
def d2sSampleCapacityList :
    Nat →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (List (Vector U SpongeSize.C))
  | 0 => pure []
  | m + 1 => do
      let head ← d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let tail ← d2sSampleCapacityList m
      pure (head :: tail)

/-- CO25 §5.4 Item 4(e)iiiB — Split units into `m` rate blocks of size `r`,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
private def d2sRateBlocksFromUnitsM :
    (m : Nat) → List U →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        { blocks : List (Vector U SpongeSize.R) // blocks.length = m }
  | 0, _ => pure ⟨[], rfl⟩
  | m + 1, units => do
      let headUnits := units.take SpongeSize.R
      let restUnits := units.drop SpongeSize.R
      let block ←
        if hFull : headUnits.length = SpongeSize.R then
          pure <|
            Vector.ofFn (fun j => headUnits.get ⟨j.1, by
              rw [hFull]
              exact j.2⟩)
        else do
          -- MUST sample z units for the remainder where `|z| = r - (ℓᵥ(i) % r)`
          let padLen := SpongeSize.R - headUnits.length
          let pad ←
            d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) padLen
          let blockList := headUnits ++ pad.toList
          have hTake : headUnits.length ≤ SpongeSize.R := by
            dsimp [headUnits]
            exact List.length_take_le SpongeSize.R units
          have hLen : blockList.length = SpongeSize.R := by
            simp [blockList, padLen, Nat.add_sub_of_le hTake]
          pure <|
            Vector.ofFn (fun j => blockList.get ⟨j.1, by
              rw [hLen]
              exact j.2⟩)
      let ⟨tail, hTail⟩ ← d2sRateBlocksFromUnitsM m restUnits
      pure ⟨block :: tail, by simp [hTail]⟩

/-- CO25 §5.4 Item 4(e)iiiB — Reshape `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` into `L_V(i)` rate blocks,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
def d2sRateBlocksFromChallenge
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize (pSpec := pSpec) i)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ i)) := do
  let ⟨blocks, hBlocks⟩ ← d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn)
    (pSpec := pSpec) (δ := δ) (pSpec.Lᵥᵢ i) challenge.toList
  pure ⟨blocks.toArray, by simp [hBlocks]⟩

/-! ### `d2sQueryStep` / `d2sQueryImpl`

CO25 §5.4 — Wires the Items 2-4 branch tree to the `d2sQueryOracles` direct-query helpers.
Sampling goes through `Unit →ₒ U`; `gᵢ` evaluation goes through `d2sQueryG`. -/

section StepImpl

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- State update for CO25 §5.4 Item 2(b/c): after a hash-cache miss, add the sampled hash
answer to `tr_∇.h` and append the corresponding hash entry to the simulator trace. -/
def d2sHashMissState
    (stmt : StmtIn) (sampled : Vector U SpongeSize.C)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
  let trace' := st.trace ++ [⟨dsHashQuery stmt, sampled⟩]
  let trΔ' : TraceNabla T_H T_P StmtIn U :=
    { st.trΔ with h := TraceTableOps.add st.trΔ.h stmt sampled }
  let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
    TraceNabla.IsSubsetOfQueryLog_append_hash st.h_inv stmt sampled
  let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
    TraceNabla.MirrorsQueryLog_append_hash_add st.h_mirror stmt sampled
  { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }

/-- CO25 §5.4 Item 2 — hash-oracle (`h`) branch of `D2SQuery`.

Paper steps (lines 1039-1043): lookup `tr_∇.h.inlu(𝕩)`; on `⟂`, sample `s_{C,out} ← 𝒰(Σ^c)` and
call `tr_∇.h.add(𝕩, s_{C,out})`; always append `('h', 𝕩, s_{C,out})` to `tr`. -/
def d2sHandleHashQuery
    (stmt : StmtIn) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (Vector U SpongeSize.C) := do
  let st ← get
  match hLookup : TraceTableOps.inlu st.trΔ.h stmt with
  -- Item 2(a) — cache hit: `s_{C,out} := tr_∇.h.inlu(𝕩)`.
  | some capSeg =>
      let trace' := st.trace ++ [⟨dsHashQuery stmt, capSeg⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' := TraceNabla.IsSubsetOfQueryLog_append_any
        st.h_inv ⟨dsHashQuery stmt, capSeg⟩
      let h_mem : (stmt, capSeg) ∈ TraceTableOps.entries st.trΔ.h :=
        TraceTableOps.mem_entries_of_inlu_eq_some hLookup
      let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_hash_existing st.h_mirror stmt capSeg h_mem
      set { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
      return capSeg
  | none =>
      -- Item 2(b) — cache miss: `s_{C,out} ←$ 𝒰(Σ^c)`; then `tr_∇.h.add(𝕩, s_{C,out})`.
      let sampled ← StateT.lift <| OptionT.lift <| d2sSampleCapacity (U := U) (StmtIn := StmtIn)
        (pSpec := pSpec) (δ := δ)
      -- Item 2(c) — append `('h', 𝕩, s_{C,out})` to `tr`; return `s_{C,out}`.
      set (d2sHashMissState (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt sampled st)
      return sampled

/-- CO25 §5.4 Item 3 — inverse-permutation (`p⁻¹`) branch of `D2SQuery`.

Paper steps (lines 1044-1046): lookup `tr_∇.p.outlu(s_out)`; on `⟂`, sample `s_in ← 𝒰(Σ^{r+c})`
and call `tr_∇.p.add(s_in, s_out)`; always append `('p⁻¹', s_out, s_in)` to `tr`. -/
def d2sHandleInversePermQuery
    (stateOut : CanonicalSpongeState U) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match hLookup : TraceTableOps.outlu st.trΔ.p stateOut with
  -- Item 3(a) — reverse cache hit: `s_in := tr_∇.p.outlu(s_out)`.
  | some recovered =>
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, recovered⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermInvQuery stateOut, recovered⟩
      let h_mem : (recovered, stateOut) ∈ TraceTableOps.entries st.trΔ.p :=
        TraceTableOps.mem_entries_of_outlu_eq_some hLookup
      let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_inv_existing st.h_mirror recovered stateOut h_mem
      set { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
      return recovered
  | none =>
      -- Item 3(b) — miss: `s_in ←$ 𝒰(Σ^{r+c})`; then `tr_∇.p.add(s_in, s_out)`.
      let sampled ← StateT.lift <| OptionT.lift <|
        d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      -- Item 3(c) — append `('p⁻¹', s_out, s_in)` to `tr`; return `s_in`.
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, sampled⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.add st.trΔ.p sampled stateOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm_inv st.h_inv sampled stateOut
      let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_inv_add st.h_mirror sampled stateOut
      set { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
      return sampled

/-- CO25 §5.4 Item 4(c) — `BackTrack` returned `.noResult`.

Cache lookup (Item 4(c)i) → `tr_∇.p.inlu` (Item 4(c)ii) → fresh sampling fallback. -/
def d2sHandleBacktrackNoResult
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  -- find `s_out` for `s_in` from `Cache_p -> inlu -> sample`
  let st ← get
  match popCacheEntryByInput (U := U) st.cacheP stateIn with
  -- Item 4(c)i — cache pop: `(s_out, Cache_p') := pop(Cache_p, s_in)`.
  --
  -- `tr_∇` mirrors the forward pairs recorded in `tr` (with set semantics), so
  -- the consumed cache pair must be inserted here as well.  This does *not* change the
  -- cache-first priority: when a cached squeeze chunk conflicts with an existing `tr_∇` pair,
  -- this branch still returns the cached value and the forward `E_func` event accounts for it
  -- through the `Cache_p ∩ tr` term in CO25 Eqs. (31)--(33).
  -- It does ensure that a later `p⁻¹` lookup sees the pair just recorded, rather than sampling a
  -- fresh incompatible preimage.  This correction is needed by the Lemma 5.8 first-witness
  -- analysis.
  | some (cachedEntry, cacheTail) =>
      let cachedOut := cachedEntry.stateOut
      -- Item 4(f) — append `('p', s_in, s_out)` to `tr` (shared across 4(c)/(d)/(e)).
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, cachedOut⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn cachedOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_insert_perm st.h_inv stateIn cachedOut
      let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_insert st.h_mirror stateIn cachedOut
      let st' : D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
        ⟨trace', cacheTail,
          st.cacheHistory ++ [⟨cachedEntry, st.trace.length, st.trace⟩],
          trΔ', h_inv', h_mirror',
          st._phantom⟩
      set st'
      return cachedOut
  | none =>
      if hLookupNone : TraceTableOps.inlu st.trΔ.p stateIn = none then
          -- Item 4(c)iii — fresh sample: `s_out ←$ 𝒰(Σ^{r+c})`; `tr_∇.p.add(s_in, s_out)`.
          let sampledOut ← StateT.lift <| OptionT.lift <|
            d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          -- Item 4(f) — append `('p', s_in, s_out)` to `tr` (shared across 4(c)/(d)/(e)).
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, sampledOut⟩]
          let trΔ' : TraceNabla T_H T_P StmtIn U :=
            { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn sampledOut }
          let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
          let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
            TraceNabla.MirrorsQueryLog_append_perm_add st.h_mirror stateIn sampledOut
          set { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
          return sampledOut
      else
          -- Item 4(c)ii — forward cache hit: `s_out := tr_∇.p.inlu(s_in)`.
          let hExists :
              ∃ recovered : CanonicalSpongeState U,
                TraceTableOps.inlu st.trΔ.p stateIn = some recovered :=
            Option.ne_none_iff_exists'.mp hLookupNone
          let recovered := Classical.choose hExists
          have hLookup : TraceTableOps.inlu st.trΔ.p stateIn = some recovered :=
            Classical.choose_spec hExists
          -- Item 4(f) — append `('p', s_in, s_out)` to `tr` (shared across 4(c)/(d)/(e)).
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
          let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
          let h_mem : (stateIn, recovered) ∈ TraceTableOps.entries st.trΔ.p :=
            TraceTableOps.mem_entries_of_inlu_eq_some hLookup
          let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
            TraceNabla.MirrorsQueryLog_append_perm_existing st.h_mirror stateIn recovered h_mem
          set { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
          return recovered

/-- CO25 §5.4 Item 4(e)iii.B — synthesize `s_out` from the first rate block and chain the
remaining rate blocks into `Cache_p` extensions.

Parses `ρ̂_i ‖ z` as exactly `L_V(i)` rate segments: the first becomes the rate half of the
sampled `s_out`; the rest seed paired states that extend `Cache_p`. -/
def d2sSynthesizeStateFromRateBlocks
    (rateBlocks : List (Vector U SpongeSize.R)) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U × List (CacheEntry (StmtIn := StmtIn) (U := U))) := do
  let st ← get
  match rateBlocks with
  | [] => StateT.lift failure
  | _ =>
      -- Sample `s_C^{(k)} ←$ 𝒰(Σ^c)` for all `k = 0, …, L_V(i)-1` at once.
      let caps : List (Vector U SpongeSize.C) ← StateT.lift <| OptionT.lift <|
        d2sSampleCapacityList (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          rateBlocks.length
      let allStates :=
        d2sSynthesisStates (U := U) rateBlocks caps
      -- Since `rateBlocks` is not empty, `allStates` is not empty.
      match allStates with
      | [] => StateT.lift failure -- Unreachable if length > 0
      | synthesized_s_out :: extraStates =>
          -- Item 4(e)iii.E — extend `Cache_p` by chaining
          --   `(s_out, s^{(1)}), …, (s^{(L_V(i)-2)}, s^{(L_V(i)-1)})`.
          let birthRawTraceLength := st.trace.length
          let newEntries :=
            cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
              birthRawTraceLength st.trace (synthesized_s_out :: extraStates)
          pure (synthesized_s_out, st.cacheP ++ newEntries)

/-- CO25 §5.4 Items 4(d)/4(e) — `BackTrack` returned `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)`.

Splits on the codec-image predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` (Item 4(d) vs 4(e), lines
1056/1059) and dispatches in paper order.

Paper Item 4(e) (in-image branch):
- (e)i  : `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`  — issued **unconditionally**.
- (e)ii : `s_out := tr_∇.p.inlu(s_in)`, if any.
- (e)iii: else, sample `z`, reshape `ρ̂_i ‖ z` into `L_V(i)` rate blocks, synthesize `s_out`
  from the first block, chain the remainder into `Cache_p`, and `tr_∇.p.add(s_in, s_out)`.

The unconditional `g_i` query in (e)i is essential: `tr_i` (paper Item 3 of `D2SAlgo`, lived
externally to D2SQuery) makes the bridge `ψ⁻¹ ∘ f ∘ φ⁻¹` deterministic w.r.t. the encoded
query, so the cost of a repeat `gᵢ` call is a cache hit, not fresh randomness. -/
def d2sHandleBacktrackSome
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  if d2sInCodecImagePredicate -- all encoded-messages `α̂ᵢ` are in `Im(φᵢ)`
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut then
    -- Paper Item 4(e)i — **unconditional** `g_i` query: `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`.
    -- Determinism w.r.t. the encoded key is enforced by `D2SAlgo`'s `tr_i` memo at the
    -- bridge layer (`d2sCodecBridgeImplMemo` in §5.4 D2SAlgo); same key ⇒ same response.
    let sampledRhoHat ← StateT.lift <| OptionT.lift <|
      d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt
        backtrackOut.encodedMessages
    -- Paper Item 4(e)ii — `s_out := tr_∇.p.inlu(s_in)`, if any.
    match hLookup : TraceTableOps.inlu st.trΔ.p stateIn with
    | some recovered =>
        -- Paper Item 4(f) — append `('p', s_in, s_out)` to `tr`; Item 4(g) returns `s_out`.
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
        let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
        let h_mem : (stateIn, recovered) ∈ TraceTableOps.entries st.trΔ.p :=
          TraceTableOps.mem_entries_of_inlu_eq_some hLookup
        let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_existing st.h_mirror stateIn recovered h_mem
        set { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
        return recovered
    | none =>
        -- Paper Item 4(e)iii.A/B — sample `z`, concat `ρ̂_i ‖ z`, reshape into `L_V(i)`
        -- rate blocks.
        let rateBlocks ← StateT.lift <| OptionT.lift <|
          d2sRateBlocksFromChallenge
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (i := backtrackOut.roundIdx) sampledRhoHat
        -- Paper Item 4(e)iii.C/D/E — **sample capacities** for tail rate blocks, extend `Cache_p`,
        -- emit `s_out := (s_R^(0), s_C^(0))`.
        let (s_out, cache') ←
          d2sSynthesizeStateFromRateBlocks (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) rateBlocks.toList
        -- Paper Item 4(e)iii.F — `tr_∇.p.add(s_in, s_out)`
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, s_out⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn s_out }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn s_out
        let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_add st.h_mirror stateIn s_out
        set { st with trace := trace', cacheP := cache', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
        return s_out
  else
    -- Paper Item 4(d) — tuple not in image; `tr_∇.p.inlu(s_in)` else fresh sample
    match hLookup : TraceTableOps.inlu st.trΔ.p stateIn with
    | some recovered =>
        -- Item 4(d)i — cache hit
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
        let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
        let h_mem : (stateIn, recovered) ∈ TraceTableOps.entries st.trΔ.p :=
          TraceTableOps.mem_entries_of_inlu_eq_some hLookup
        let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_existing st.h_mirror stateIn recovered h_mem
        set { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
        return recovered
    | none =>
        -- Item 4(d)ii — fresh sample
        let sampledOut ← StateT.lift <| OptionT.lift <|
          d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, sampledOut⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn sampledOut }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
        let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_add st.h_mirror stateIn sampledOut
        set { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
        return sampledOut

/-- CO25 §5.4 Item 4 — forward-permutation (`p`) branch of `D2SQuery`.

Calls `BackTrack(tr, tr_∇, s_in)` (Item 4(a)) and dispatches:
- `.err` → abort (Item 4(b));
- `.noResult` → cache / `inlu` / sample fallback (Item 4(c));
- `.some backtrackOut` → codec-image dispatch (Items 4(d)/4(e)). -/
def d2sHandleForwardPermQuery
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match
      backTrack
        (δ := δ)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
  | .err =>
      -- Paper Item 4(b): `err` branch aborts.
      StateT.lift failure
  | .noResult =>
      d2sHandleBacktrackNoResult (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn
  | .some backtrackOut =>
      d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut

-- The support computation unfolds the nested `StateT` / `OptionT` simulator, which requires
-- more than the default elaboration budget but remains below the project-wide 400k cap.
set_option maxHeartbeats 400000 in
lemma d2sHandleBacktrackNoResult_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option (CanonicalSpongeState U ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sHandleBacktrackNoResult
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨dsPermQuery stateIn, a⟩] := by
  intro a st' hi_eq
  subst i
  unfold d2sHandleBacktrackNoResult at hi
  aesop

/-- Peel a successful support point through the common abortable pattern
`Option.elimM sample (pure none) body`.  The `none` branch cannot produce `some b`, so the output
must come from a successful sampled value followed by the body. -/
private lemma mem_support_option_elimM_some {α β : Type} {sample : ProbComp (Option α)}
    {body : α → ProbComp (Option β)} {b : β}
    (h : some b ∈ support (Option.elimM sample (pure none) body)) :
    ∃ a, some a ∈ support sample ∧ some b ∈ support (body a) := by
  simp only [Option.elimM] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨o, ho, hb⟩ := h
  cases o with
  | none =>
      simp at hb
  | some a =>
      exact ⟨a, ho, by simp at hb; exact hb⟩

/-- Peel a successful support point through a nested `Option.map` over a probabilistic
computation. -/
private lemma mem_support_map_nested_option_some {α β : Type}
    {sample : ProbComp (Option (Option α))} {f : α → β} {b : β}
    (h : some (some b) ∈ support (Option.map (Option.map f) <$> sample)) :
    ∃ a, some (some a) ∈ support sample ∧ f a = b := by
  rw [support_map] at h
  obtain ⟨ooa, hoo, hmap⟩ := h
  cases ooa with
  | none =>
      simp only [Option.map_none] at hmap
      cases hmap
  | some oa =>
      cases oa with
      | none =>
          simp only [Option.map_some, Option.map_none] at hmap
          cases hmap
      | some a =>
          simp only [Option.map_some, Option.some.injEq] at hmap
          subst hmap
          exact ⟨a, hoo, rfl⟩

set_option maxHeartbeats 400000 in
-- This support proof normalizes the large generated monadic term for BackTrack's codec-image
-- branch; the argument itself is just support peeling plus final-state projection.
/-- The `.some backtrackOut` sub-branch of the forward permutation handler appends exactly the
answered forward permutation query to the internal trace on every successful support point. -/
lemma d2sHandleBacktrackSome_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option (CanonicalSpongeState U ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sHandleBacktrackSome
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨dsPermQuery stateIn, a⟩] := by
  intro a st' hi_eq
  subst i
  unfold d2sHandleBacktrackSome at hi
  cases hpred : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      backtrackOut
  · simp [hpred] at hi
    split at hi <;>
      aesop
  · simp [hpred] at hi
    obtain ⟨rhoHat, _hrhoHat, hi⟩ := mem_support_option_elimM_some hi
    split at hi
    · aesop
    · simp at hi
      obtain ⟨rateBlocks, _hrateBlocks, hi⟩ := mem_support_option_elimM_some hi
      obtain ⟨synth, _hsynth, hsynth⟩ := mem_support_map_nested_option_some hi
      injection hsynth with ha hstEq
      rw [← hstEq]
      simp only
      rw [ha]

/-- CO25 §5.4 — `D2SQuery` one-step dispatcher over `d2sQueryOracles`: dispatches `h` (Item 2),
`p⁻¹` (Item 3), `p` (Item 4 with BackTrack branches 4(b)-4(g)). -/
def d2sQueryStep
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT
        (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) :=
  match q with
  | dsHashQuery stmt =>
      d2sHandleHashQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt
  | dsPermInvQuery stateOut =>
      d2sHandleInversePermQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut
  | dsPermQuery stateIn =>
      d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn

/-- The hash branch of `d2sQueryStep` appends exactly the answered hash query to the internal D2S
trace. -/
lemma d2sHandleHashQuery_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (stmt : StmtIn)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option (Vector U SpongeSize.C ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sHandleHashQuery
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨dsHashQuery stmt, a⟩] := by
  intro a st' hi_eq
  subst i
  unfold d2sHandleHashQuery at hi
  aesop

/-- The forward-permutation branch of `d2sQueryStep` appends exactly the answered `p`-query to the
internal D2S trace. -/
lemma d2sHandleForwardPermQuery_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option (CanonicalSpongeState U ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sHandleForwardPermQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨dsPermQuery stateIn, a⟩] := by
  intro a st' hi_eq
  subst i
  unfold d2sHandleForwardPermQuery at hi
  cases hbt : backTrack (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
  | err =>
      simp [hbt] at hi
  | noResult =>
      exact d2sHandleBacktrackNoResult_support_trace_append
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl stateIn st (by
          simp [hbt] at hi
          exact hi) a st' rfl
  | some backtrackOut =>
      exact d2sHandleBacktrackSome_support_trace_append
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl stateIn backtrackOut st (by
          simp [hbt] at hi
          exact hi) a st' rfl

/-- The inverse-permutation branch of `d2sQueryStep` appends exactly the answered `p⁻¹`-query to
the internal D2S trace. -/
lemma d2sHandleInversePermQuery_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (stateOut : CanonicalSpongeState U)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option (CanonicalSpongeState U ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sHandleInversePermQuery
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨dsPermInvQuery stateOut, a⟩] := by
  intro a st' hi_eq
  subst i
  unfold d2sHandleInversePermQuery at hi
  simp at hi
  aesop

/-- Any successful `d2sQueryStep` support point appends exactly the answered narrow query to the
internal D2S trace.  This is the local operational fact later used by the Lemma-5.8 trace-bridge
proofs. -/
lemma d2sQueryStep_support_trace_append
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((d2sQueryStep
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨q, a⟩] := by
  intro a st' hi_eq
  cases q with
  | inl stmt =>
      exact d2sHandleHashQuery_support_trace_append
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl stmt st hi a st' hi_eq
  | inr q' =>
      cases q' with
      | inl stateIn =>
          exact d2sHandleForwardPermQuery_support_trace_append
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            gImpl auxImpl stateIn st hi a st' hi_eq
      | inr stateOut =>
          exact d2sHandleInversePermQuery_support_trace_append
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            gImpl auxImpl stateOut st hi a st' hi_eq

end StepImpl

/-! ### `d2sQueryImpl` — generalization with a caller-supplied `gᵢ` realization

`d2sQueryImpl` parameterizes the D2SQuery simulator over an arbitrary
`challengeSpec`-targeted `gᵢ`-implementation `gImpl`.  The result lives in
`StateT _ (AbortComp (D2SChallengePlusUnitOracle challengeSpec))`, which is the
shape `KeyLemma.hybridGame` consumes.

The pipeline reuses `d2sQueryStep` for the §5.4 Items 2–4 branch tree and translates the
resulting `d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` queries through
`gImpl + auxImpl`, where `auxImpl` injects the `(Unit →ₒ U) + unifSpec` side into the
`D2SChallengePlusUnitOracle challengeSpec` target unchanged. -/

section WithOracle

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — `D2SQuery` simulator parameterized over a `gᵢ` realization `gImpl` and an
auxiliary `(Unit →ₒ U) + unifSpec` realization `auxImpl`, both landing in an arbitrary monad
`m` with `Alternative` (for the §5.4 Item 4(b) `err` abort branch); reuses `d2sQueryStep`
for Items 2-4.

Single interface used by:
- `d2sAlgo` (Phase 14): `m = StateT (D2SAlgoMemo …) (AbortComp …)`,
  `gImpl = d2sCodecBridgeImplMemo` — threads the paper Item 3 `tr_i` memo;
  `auxImpl` lifts `(Unit →ₒ U) + unifSpec` queries through to the outer
  `D2SChallengePlusUnitOracle`.
- §5.8 hybrid games (`hybridGame`): `m = OptionT (OracleComp _)`,
  `gImpl` varies per hybrid (`g`, `e`, `f`, …); `auxImpl` lifts to the same outer spec.
- `lemma5_8SigmaTraceDist` (BadEvents): `m = OptionT ProbComp`, `auxImpl` resolves
  `(Unit →ₒ U) + unifSpec` directly via `d2sUnitSampleImpl + QueryImpl.id' unifSpec`. The
  `OptionT`-abort halts the §5.8 experiment (paper line 1417); the partial trace at the moment
  of abort is preserved by `BadEvents.lemma5_8ProjectedTraceDistAbortable`. -/
def d2sQueryImpl
    {m : Type → Type} [Monad m] [Alternative m]
    (gImpl :
      QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        m) :=
  fun (q : (duplexSpongeChallengeOracle StmtIn U).Domain) st => do
    let combinedImpl :
        QueryImpl
          (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) m :=
      gImpl + auxImpl
    let pairOpt ←
      simulateQ combinedImpl
        (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
    match pairOpt with
    | none => failure
    | some ⟨query_answer, newState⟩ => pure ⟨query_answer, newState⟩

end WithOracle

end D2SQuery

/-! ## Codec bridge `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`

CO25 §5.4 Eq. 16 — Translates `d2sQueryOracles` into `fsChallengeOracle`-based queries:
- `.inl` (`gSpec`): `φ⁻¹` (decode prefix) → `f` (query FS oracle) → `ψ⁻¹` (uniform preimage)
- `.inr` (`(Unit →ₒ U) + unifSpec`): identity passthrough

The `OptionT` layer models `φ⁻¹` parse failure (⊥ on malformed encoded-message prefixes). -/

section CodecBridge

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 Eq. 16 — `gᵢ`-summand of the codec bridge: `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`.

Given a `gSpec` query `(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)`:
1. `φ⁻¹`: parse `α̂_{<i}` → `α_{<i}` via `hybEncodedMessagesBefore?` (⊥ on failure)
2. `f`: query `fᵢ(𝕩, bin(τ̂), α₁, …, αᵢ)` → `ρᵢ ∈ ℳ_{V,i}` via `fsChallengeOracle`
   keyed at the pre-encoded salt `Salt` (paper's `{0,1}^{δ⋆}`; bridge =
   `SaltCodec.encode = bin`)
3. `ψ⁻¹`: sample `ρ̂ᵢ ← 𝒰(ψᵢ⁻¹(ρᵢ))` via `uniformDeserializePreimage` -/
noncomputable def d2sCodecBridgeImpl :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    do
      -- Step 1 (`φ⁻¹`) — decode prover prefix: `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`;
      -- abort if any block lies outside `Im(φ_ι)`.
      let messagesBefore ←
        match hybEncodedMessagesBefore?
            (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | some messagesBefore => pure messagesBefore
        | none => failure
      -- Step 2 (`f`) — query the FS oracle at the binarized salt:
      --   `ρ_i := f_i(𝕩, bin(τ̂), α_1, …, α_{i-1}) ∈ ℳ_{V,i}`, with `bin = SaltCodec.encode`.
      let challenge ←
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec))
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec))
              (.inl ⟨roundIdx,
                ((stmt, SaltCodec.encode (Salt := Salt) salt), messagesBefore)⟩))
      -- Step 3 (`ψ⁻¹`) — uniform preimage: `ρ̂_i ←$ ψ_i⁻¹(ρ_i) ⊆ Σ^{ℓ_V(i)}`.
      OptionT.lift <|
        uniformDeserializePreimage
          (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
          challenge

end CodecBridge

/-! ## `D2SAlgoMemo` — `tr_i` memo for the codec bridge (CO25 §5.4 D2SAlgo Item 3)

The unconditional `gᵢ` query in `D2SQuery` Item 4(e)i (see `d2sHandleBacktrackSome`) means
that two adversary queries with the same `BacktrackOutput` produce two `gᵢ` queries with the
same encoded key in the resulting `OracleComp` tree. Without a memo at the bridge layer, the
randomness in `uniformDeserializePreimage` (the `ψ⁻¹` step) would give them different
responses, violating CO25 §5.4 D2SAlgo Item 3's determinism on repeat keys.

`D2SAlgoMemo` is the `tr_i : (i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i` table the paper threads through
the bridge as a `StateT` layer over `d2sCodecBridge`. On a cache hit, the stored `ρ̂_i` is
returned; on a miss, `d2sCodecBridgeImpl` is invoked and the resulting `ρ̂_i` is appended. -/

section D2SAlgoMemo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 D2SAlgo Item 3 — entry of the bridge-layer memo `tr_i`, keyed on the
encoded `gᵢ` query `(i, 𝕩, τ̂, α̂_1, …, α̂_i)` with **binarized** salt `τ̂ := bin(τ) ∈ Salt`
(paper `{0,1}^{δ⋆}`; see Item 3c/3f), carrying the sampled encoded response
`ρ̂_i ∈ Σ^{ℓ_V(i)}` (the `ψ⁻¹` preimage of the basic-FS challenge). -/
structure D2SAlgoMemoEntry
    (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Salt
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc
  response : Vector U (challengeSize (pSpec := pSpec) roundIdx)

/-- CO25 §5.4 D2SAlgo Item 3 — `tr_i` table, indexed by `gᵢ`-query keys with binarized salt. -/
abbrev D2SAlgoMemo (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :=
  List (D2SAlgoMemoEntry StmtIn U δ Salt pSpec)

instance [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    Inhabited (D2SAlgoMemo StmtIn U δ Salt pSpec) := ⟨[]⟩

open Classical in
/-- CO25 §5.4 D2SAlgo Item 3 — `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)]`, returning `some ρ̂_i` if the
encoded key was previously stored. Salt key is the **binarized** `τ̂ : Salt` (paper Item 3c). -/
noncomputable def lookupD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Salt)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    Option (Vector U (challengeSize (pSpec := pSpec) i)) :=
  memo.foldl (init := none) fun acc entry =>
    acc.orElse fun _ =>
      if hRound : entry.roundIdx = i then by
        subst hRound
        exact
          if entry.stmt = stmt ∧ entry.salt = salt ∧ entry.encodedMessages = encodedMessages
            then some entry.response
            else none
      else none

/-- CO25 §5.4 D2SAlgo Item 3 — append a fresh `(key, ρ̂_i)` entry to `tr_i`. -/
def insertD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (entry : D2SAlgoMemoEntry StmtIn U δ Salt pSpec) :
    D2SAlgoMemo StmtIn U δ Salt pSpec :=
  memo ++ [entry]

/-- CO25 §5.4 D2SAlgo Item 3 — memoized `gᵢ`-summand of the codec bridge.

Wraps `d2sCodecBridgeImpl` in a `StateT (D2SAlgoMemo …)` layer. On `lookupD2SAlgoMemo` hit,
returns the stored response without resampling `ψ⁻¹`; on miss, invokes the unmemoized bridge
and appends the result via `insertD2SAlgoMemo`. -/
noncomputable def d2sCodecBridgeImplMemo :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle (StmtIn × Salt) pSpec)
      (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    -- Paper Item 3c — binarize `τ̂ := bin(τ) ∈ Salt` once before memo lookup/insert.
    let encodedSalt : Salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) salt
    do
      let memo ← get
      match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
          memo roundIdx stmt encodedSalt encodedMessages with
      -- Item 3 cache hit: `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)] = some ρ̂_i` ⇒ return stored `ρ̂_i`.
      | some response => pure response
      | none =>
          -- Item 3 cache miss: invoke `ψ⁻¹∘f∘φ⁻¹` to sample `ρ̂_i`,
          --   then `tr_i := tr_i ∪ {(i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i}`.
          let response ←
            (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
              (Salt := Salt) q :
              OptionT (OracleComp _) _)
          modify (fun m =>
            insertD2SAlgoMemo
              (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec) m
              { roundIdx := roundIdx, stmt := stmt, salt := encodedSalt,
                encodedMessages := encodedMessages, response := response })
          pure response

end D2SAlgoMemo

/-! ## `d2fProverRaw` — shared `𝒜^{D2SQuery^{gImpl}}` inner pipeline

Raw post-`simulateQ` shape of the paper Eq. 16 RHS prover loop, keeping the two state layers
(`D2SQueryState`, inner `M`) so different call sites can project differently:
- `D2FQueryProver` projects via `Prod.fst ∘ Prod.fst` — drops both states, used by Hyb_4.
- `KeyLemma.hybridGame` keeps the triple — uses `D2SQueryState` for the verifier-half
  independent run and threads `M` (paper Item 3 `tr_i`) from prover to verifier, matching
  CO25 §5.4 D2SAlgo Item 3 ("`tr_i` is global to a single run").

Polymorphic over `M` (`PUnit` for Hyb_1 / Hyb_2's inline `g` / `e` realizations;
`D2SAlgoMemo …` for Hyb_3 / Hyb_4's memoized `gᵢ` bridge) and `challengeSpec` (`gSpec` /
`eSpec` / `fsChallengeOracle (StmtIn × Salt) pSpec` per-hybrid). Single source of truth for
the `outerImpl := QueryImpl.addLift (QueryImpl.id oSpec) (d2sQueryImpl gImpl auxImpl)`
construction. -/

section D2FProverRaw

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — Outer-spec `QueryImpl` for the paper Eq. 16 RHS simulator:
`id_oSpec ⊕ D2SQuery^{gImpl}`. Reused by `d2fProverRaw` and by `KeyLemma.hybridGame`'s
verifier-half (which re-runs the same `QueryImpl` against the honest verifier with the
shared `M` state threaded in — paper §5.4 D2SAlgo Item 3, `tr_i` global to a single run). -/
noncomputable def d2fOuterImpl
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT M
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := gImpl)
      (auxImpl := fun aux =>
        query
          (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
          (Sum.inr aux)))

/-- CO25 §5.4 Eq. 16 RHS — generic raw pipeline for `comp^{D2SQuery^{gImpl}}`, keeping the
post-run `D2SQueryState` and inner `M`.

Generalizes `d2fProverRaw` from prover-only to any wide-DSFS computation. Two call sites:
- **Prover**: `d2fProverRaw gImpl 𝒜 = d2fRaw gImpl 𝒜 default` (fresh inner state).
- **Verifier** (in `KeyLemma.hybridGame`): `d2fRaw gImpl verifyCompWide memo₁`
  (threads the prover's post-run `M` as the verifier's initial state, matching CO25 §5.4
  D2SAlgo Item 3 that `tr_i` is global to a single run). -/
noncomputable def d2fRaw
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
        ((α × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
          M) :=
  (((simulateQ (d2fOuterImpl (T_H := T_H) (T_P := T_P) gImpl) comp).run default).run initM)

end D2FProverRaw

/-! ## `D2FQueryProver` + `d2sAlgo` — paper Eq. 16 split

Paper §5.4 D2SAlgo (lines 1121-1138) decomposes into two structurally distinct pieces:

- **Items 1-3** = the inner prover loop running `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper Eq. 16
  RHS). Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`). Mirrored in Lean by
  `D2FQueryProver` returning `DSSaltedProof`.
- **Items 4-6** = parse `(τ, αᵢ)`, set `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`, repackage as
  `π̌ := (τ̌, αᵢ)`. This is a pure post-processing wrapper that re-encodes the salt to the
  FS-standard side. Mirrored in Lean by `d2sAlgo`, which applies `SaltCodec.encode = bin`
  to the salt-component of `D2FQueryProver`'s output, returning `FSSaltedProof`.

The split makes paper Figure 4 lines 2-3 explicit at the type level:
- Hyb_3 prover surface `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` outputs DS-form salt → `D2FQueryProver`.
- Hyb_4 prover surface `D2SAlgo^f(𝒫̃)` outputs FS-std-form salt → `d2sAlgo`.

Both share the same oracle-first pipeline:
1. `d2sQueryImpl` simulates the duplex-sponge challenge oracle into the encoded spec
   `d2sQueryOracles = gSpec + (Unit + unifSpec)`.
2. `d2sCodecBridgeImplMemo` translates `gSpec` queries into basic-FS `fsChallengeOracle` queries
   with `uniformDeserializePreimage`, threading the `tr_i` memo (CO25 §5.4 D2SAlgo Item 3) so
   that repeat encoded keys reuse the cached `ρ̂_i`; the `(Unit + unifSpec)` summand passes
   through unchanged.
3. The result lives in the basic-FS target spec
   `oSpec + D2SChallengePlusUnitOracle fsChallengeOracle`, matching `D2SAlgo`'s return monad.
   Both intermediate states (`D2SQueryState`, `D2SAlgoMemo`) are discarded. -/

section D2SAlgo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 Eq. 16 RHS — the inner prover surface `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper
D2SAlgo Items 1-3, lines 1121-1135). Runs `𝒜` with its duplex-sponge `(h, p, p⁻¹)` queries
answered by `D2SQuery` under the codec-bridged oracle `ψ⁻¹∘f∘φ⁻¹`, where `f` is the salted
FS challenge oracle keyed at `(StmtIn × Salt)`. Salt is bridged via `SaltCodec.encode = bin`
inside `d2sCodecBridgeImpl` at every `gᵢ`-query; the `tr_i` memo (Item 3) is threaded via
`d2sCodecBridgeImplMemo`.
**Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`)** — this is the paper-Hyb_3
prover surface, before the bin-repackaging of D2SAlgo Items 4-6. -/
noncomputable def D2FQueryProver
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) :=
  -- Shared raw pipeline: id_oSpec ⊕ D2SQuery^{tr_i-memoized ψ⁻¹∘f∘φ⁻¹}, single `simulateQ`,
  -- both states `default`-initialized. Strip `D2SQueryState` and `D2SAlgoMemo` at the
  -- boundary; `none` propagates as `OptionT` abort.
  Prod.fst <$> Prod.fst <$> -- DTOP the states (from the two nested StateT)
    (d2fRaw (T_H := T_H) (T_P := T_P)
      (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      𝒜 default)

/-- CO25 §5.4 Eq. 16 LHS — full `D2SAlgo^f(𝒜)` (paper Items 1-6, lines 1121-1138). Thin
wrapper over `D2FQueryProver` (Items 1-3) that applies the paper's Items 4-6 post-processing:
parse the inner output `(τ, αᵢ)` with `τ ∈ Σ^δ`, set `τ̌ := bin(τ) = SaltCodec.encode τ`,
and repackage as `(τ̌, αᵢ) : FSSaltedProof`.
**Output salt is the pre-encoded FS-std type `Salt` (paper `{0,1}^{δ⋆}`)** — this is the
paper-Hyb_4 prover surface, ready to be consumed by `𝒱_std^f` (`Verifier.singleSaltFiatShamir`)
without any further bin step. -/
noncomputable def d2sAlgo
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt) := do
  -- Items 1-3 — run inner prover to obtain `(𝕩, (τ, (α̂_1, …, α̂_n))) ∈ StmtIn × DSSaltedProof`.
  let ⟨stmt, ⟨τ, msgs⟩⟩ ← D2FQueryProver (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜
  -- Items 4-6 — re-encode salt: `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`; emit `(𝕩, (τ̌, α̂))`.
  return ⟨stmt, ⟨SaltCodec.encode (Salt := Salt) τ, msgs⟩⟩

end D2SAlgo

end

end DuplexSpongeFS.ProverTransform
