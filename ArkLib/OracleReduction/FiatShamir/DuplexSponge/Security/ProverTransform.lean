/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SCacheHistory
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRateOnlyCache
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SPermInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SSynthesis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries

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
  [codec : CodecCore pSpec U]
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

/-- Executable Item-4(d)/(e) branch predicate, exposed so support proofs can name the
algorithmic case split rather than rely on anonymous `split` hypotheses.  It is CO25 §5.4's
predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)`.  We decide it through the same total finite
`φ⁻¹` parser used by the codec bridge and the line-4 trace map: parser success is exactly
the witness that every encoded prefix block has a preimage.  Keeping this decision at the
parser boundary makes the successful branch carry the support fact needed by the Hyb₂/Hyb₃
oracle-key transport. -/
noncomputable def d2sInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  (hybEncodedMessagesBefore?
    (pSpec := pSpec) (U := U) out.roundIdx out.encodedMessages).isSome

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

/-- A challenge obtained by decoding an encoded rate string is in the decoder image.  This is
the small support fact used by the revised H₂ bridge: its partial `Lift_i` branch cannot fail on
answers produced from the encoded verifier table.  Unlike the legacy total sampler, this needs no
global surjectivity assumption. -/
lemma deserializePreimageFinset_nonempty_of_decode
    {i : pSpec.ChallengeIdx}
    [Fintype U] [DecidableEq U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (encoded : Vector U (challengeSize (pSpec := pSpec) i)) :
    (deserializePreimageFinset (pSpec := pSpec) (U := U) (codec.decode i encoded)).Nonempty := by
  refine ⟨encoded, ?_⟩
  simp only [deserializePreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  change codec.decode i encoded = codec.decode i encoded
  rfl

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

/-- Executing `sampleFromList` under a handler which forwards the `unifSpec` summand is exactly
uniform selection of an index of the supplied nonempty list.  The challenge and unit summands are
present only to give the simulator its full Section-5 target type: this computation never queries
either of them.  This is the computational form of the uniform-fibre sample used in Claim 5.22. -/
lemma simulateQ_sampleFromList
    {α κ : Type} {challengeSpec : OracleSpec κ} [SpongeUnit U] [SampleableType U]
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (l : List α) (hl : l ≠ []) :
    simulateQ
      (challengeImpl +
        ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (sampleFromList (U := U) (challengeSpec := challengeSpec) l hl) =
      (do
        let idxRaw ← ProbComp.uniformFin (l.length - 1)
        let idx : Fin l.length := ⟨idxRaw.1, by
          have hlen_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
          have hlen_eq : (l.length - 1) + 1 = l.length :=
            Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)
          simpa [hlen_eq] using idxRaw.2⟩
        pure (l.get idx)) := by
  unfold sampleFromList
  rw [simulateQ_bind]
  change (do
    let idxRaw ← ProbComp.uniformFin (l.length - 1)
    let idx : Fin l.length := ⟨idxRaw.1, by
      have hlen_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
      have hlen_eq : (l.length - 1) + 1 = l.length :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)
      simpa [hlen_eq] using idxRaw.2⟩
    pure (l.get idx)) = _
  rfl

/-- The nonempty-list sampler is the successful branch of the standard list uniform-selection
operator.  This exposes its exact probability law through `probOutput_uniformSelectList`. -/
lemma lift_simulateQ_sampleFromList_eq_uniformSelect
    {α κ : Type} {challengeSpec : OracleSpec κ} [SpongeUnit U] [SampleableType U]
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (l : List α) (hl : l ≠ []) :
    OptionT.lift
      (simulateQ
        (challengeImpl +
          ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (sampleFromList (U := U) (challengeSpec := challengeSpec) l hl)) =
      ($ l : OptionT ProbComp α) := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons x xs =>
      simp only [sampleFromList, List.length_cons, Nat.succ_sub_one]
      rfl

/-- Pointwise law of the simulated nonempty-list sampler. -/
lemma probOutput_simulateQ_sampleFromList
    {α κ : Type} [DecidableEq α] {challengeSpec : OracleSpec κ}
    [SpongeUnit U] [SampleableType U]
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (l : List α) (hl : l ≠ []) (x : α) :
    Pr[= x | (simulateQ
        (challengeImpl +
          ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (sampleFromList (U := U) (challengeSpec := challengeSpec) l hl))] =
      (l.count x : ENNReal) / l.length := by
  have h := congrArg (fun computation : OptionT ProbComp α => Pr[= x | computation])
    (lift_simulateQ_sampleFromList_eq_uniformSelect (U := U) challengeImpl l hl)
  change Pr[= x | OptionT.lift
    (simulateQ
      (challengeImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (sampleFromList (U := U) (challengeSpec := challengeSpec) l hl))] =
      Pr[= x | ($ l : OptionT ProbComp α)] at h
  rw [OptionT.probOutput_lift, ProbComp.probOutput_uniformSelectList] at h
  exact h

/-- Predicate selecting the challenge-oracle component from the combined D2S target. -/
def isD2SChallengePoint {κ : Type} {challengeSpec : OracleSpec κ} :
    (D2SChallengePlusUnitOracle (U := U) challengeSpec).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance {κ : Type} {challengeSpec : OracleSpec κ} :
    DecidablePred (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) :=
  fun point =>
    match point with
    | .inl _ => isTrue True.intro
    | .inr _ => isFalse (fun h => h)

/-- CO25 §5.4 / §5.8 — Uniform partial-fibre sampler.  It is available only after the caller
has established that the decoded value is in the image of `ψᵢ`; no decoder-surjectivity premise
is hidden in this operation. -/
noncomputable def uniformDeserializePreimageOfImage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i)
    (hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U (challengeSize (pSpec := pSpec) i)) := do
  let preimages := (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).toList
  have hpreimages_ne : preimages ≠ [] := by
    simpa [preimages] using hpreimages_nonempty.toList_ne_nil
  sampleFromList preimages hpreimages_ne

/-- Legacy total-fibre wrapper.  New revised Section 5 callers use
`uniformDeserializePreimageOfImage` after their explicit image test; this wrapper is retained
for pre-existing total-codec clients. -/
noncomputable def uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [CodecTotal pSpec U]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U (challengeSize (pSpec := pSpec) i)) :=
  uniformDeserializePreimageOfImage
    (pSpec := pSpec) (U := U) (challengeSpec := challengeSpec) challenge (by
      rcases CodecTotal.decode_surjective (pSpec := pSpec) (U := U) i challenge with
        ⟨encoded, hencoded⟩
      have hencoded' : Deserialize.deserialize encoded = challenge := hencoded
      exact ⟨encoded, by simp [deserializePreimageFinset, hencoded']⟩)

/-- Under the live Section-5 auxiliary handler, `uniformDeserializePreimage` has exactly the
uniform distribution on the decoder fibre.  This is the single-query probability identity behind
the H₁--H₂ reparameterization; the later adaptive proof must additionally establish that the
memoized bridge invokes this kernel only at the first occurrence of a key. -/
lemma probOutput_simulateQ_uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [CodecTotal pSpec U]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i)
    (encoded : Vector U (challengeSize (pSpec := pSpec) i)) :
    Pr[= encoded | (simulateQ
      (challengeImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge))] =
      Preliminaries.sampleUniformPreimage
        (codec.decode i) (CodecTotal.decode_surjective (pSpec := pSpec) (U := U) i)
        challenge encoded := by
  unfold uniformDeserializePreimage uniformDeserializePreimageOfImage
  rw [probOutput_simulateQ_sampleFromList]
  rw [Preliminaries.sampleUniformPreimage_apply]
  set s := deserializePreimageFinset (pSpec := pSpec) (U := U) challenge with hs
  have hmem : ∀ value, value ∈ s ↔ codec.decode i value = challenge := by
    intro value
    rw [hs]
    simp only [deserializePreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    change codec.decode i value = challenge ↔ codec.decode i value = challenge
    rfl
  have hcard : Fintype.card (Preliminaries.Preimage (codec.decode i) challenge) = s.card := by
    apply Fintype.card_of_subtype s
    intro value
    exact hmem value
  have hlength : s.toList.length = s.card := Finset.length_toList s
  letI : BEq (Vector U (challengeSize (pSpec := pSpec) i)) := instBEqOfDecidableEq
  change ((↑(s.toList.count encoded) : ENNReal) / (↑s.toList.length : ENNReal)) = _
  by_cases h : encoded ∈ s
  · have hcount : s.toList.count encoded = 1 :=
      List.count_eq_one_of_mem s.nodup_toList (by simpa using h)
    rw [hcount, hlength, if_pos (hmem encoded |>.mp h), hcard]
    simp
  · have hcount : s.toList.count encoded = 0 :=
      List.count_eq_zero_of_not_mem (by simpa using h)
    rw [hcount, if_neg (fun hdecode => h (hmem encoded |>.mpr hdecode))]
    simp

/-- Distributional form of the live uniform-fibre sampler.  The right-hand side is the PMF
kernel used in CO25 Lemma 3.2, embedded into the `SPMF` semantics of `ProbComp`. -/
lemma evalDist_simulateQ_uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [CodecTotal pSpec U]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i) :
    𝒟[simulateQ
      (challengeImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge)] =
      (liftM (Preliminaries.sampleUniformPreimage
        (codec.decode i) (CodecTotal.decode_surjective (pSpec := pSpec) (U := U) i)
        challenge) :
        SPMF (Vector U (challengeSize (pSpec := pSpec) i))) := by
  apply (evalDist_eq_liftM_iff _ _).mpr
  intro encoded
  exact probOutput_simulateQ_uniformDeserializePreimage
    (pSpec := pSpec) (U := U) challengeImpl challenge encoded

/-- Executing the partial `Lift` kernel at an explicitly in-image challenge has exactly the
uniform fibre law.  This is the executable one-cell form used by the revised Claim 5.22 route;
unlike the legacy lemma above, it has no `CodecTotal` requirement. -/
lemma probOutput_simulateQ_uniformDeserializePreimageOfImage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i)
    (hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty)
    (encoded : Vector U (challengeSize (pSpec := pSpec) i)) :
    Pr[= encoded | (simulateQ
      (challengeImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (uniformDeserializePreimageOfImage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge hpreimages_nonempty))] =
      Preliminaries.sampleUniformPreimageOfImage (codec.decode i) challenge (by
        rcases hpreimages_nonempty with ⟨preimage, hpreimage⟩
        refine ⟨preimage, ?_⟩
        simpa [deserializePreimageFinset] using hpreimage) encoded := by
  unfold uniformDeserializePreimageOfImage
  rw [probOutput_simulateQ_sampleFromList]
  rw [Preliminaries.sampleUniformPreimageOfImage_apply]
  set s := deserializePreimageFinset (pSpec := pSpec) (U := U) challenge with hs
  have hmem : ∀ value, value ∈ s ↔ codec.decode i value = challenge := by
    intro value
    rw [hs]
    simp only [deserializePreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcard : Fintype.card (Preliminaries.Preimage (codec.decode i) challenge) = s.card := by
    apply Fintype.card_of_subtype s
    intro value
    exact hmem value
  have hlength : s.toList.length = s.card := Finset.length_toList s
  letI : BEq (Vector U (challengeSize (pSpec := pSpec) i)) := instBEqOfDecidableEq
  change ((↑(s.toList.count encoded) : ENNReal) / (↑s.toList.length : ENNReal)) = _
  by_cases h : encoded ∈ s
  · have hcount : s.toList.count encoded = 1 :=
      List.count_eq_one_of_mem s.nodup_toList (by simpa using h)
    rw [hcount, hlength, if_pos (hmem encoded |>.mp h), hcard]
    simp
  · have hcount : s.toList.count encoded = 0 :=
      List.count_eq_zero_of_not_mem (by simpa using h)
    rw [hcount, if_neg (fun hdecode => h (hmem encoded |>.mpr hdecode))]
    simp

/-- Distributional form of the executable partial `Lift` identity. -/
lemma evalDist_simulateQ_uniformDeserializePreimageOfImage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challengeImpl : QueryImpl challengeSpec ProbComp)
    (challenge : pSpec.Challenge i)
    (hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty) :
    𝒟[simulateQ
      (challengeImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (uniformDeserializePreimageOfImage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge hpreimages_nonempty)] =
      (liftM
        (Preliminaries.sampleUniformPreimageOfImage (codec.decode i) challenge (by
          rcases hpreimages_nonempty with ⟨preimage, hpreimage⟩
          refine ⟨preimage, ?_⟩
          simpa [deserializePreimageFinset] using hpreimage) :
          PMF (Vector U (challengeSize (pSpec := pSpec) i))) :
        SPMF (Vector U (challengeSize (pSpec := pSpec) i))) := by
  apply (evalDist_eq_liftM_iff _ _).mpr
  intro encoded
  exact probOutput_simulateQ_uniformDeserializePreimageOfImage
    (pSpec := pSpec) (U := U) challengeImpl challenge hpreimages_nonempty encoded

/-- **Claim 5.23, one-cell partial-lift bound.**  The decoded-table distribution and the
standard uniform challenge distribution are processed by the same total `Lift` kernel: an
in-image challenge yields a uniform fibre representative, while an out-of-image challenge
yields `none`.  Consequently the explicit image stop costs no extra term beyond the decoder
bias, and no decoder-surjectivity assumption is needed. -/
theorem codec_partialLift_bias
    [Fintype U] [Nonempty U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Nonempty (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    (i : pSpec.ChallengeIdx) :
    PMF.tvDist
      ((codec.decode i <$> PMF.uniformOfFintype
        (Vector U (challengeSize (pSpec := pSpec) i))).bind
        (Preliminaries.sampleUniformPreimageOrNone (codec.decode i)))
      ((PMF.uniformOfFintype (pSpec.Challenge i)).bind
        (Preliminaries.sampleUniformPreimageOrNone (codec.decode i))) ≤
      (codec.decodingBias i : ℝ) := by
  calc
    PMF.tvDist
        ((codec.decode i <$> PMF.uniformOfFintype
          (Vector U (challengeSize (pSpec := pSpec) i))).bind
          (Preliminaries.sampleUniformPreimageOrNone (codec.decode i)))
        ((PMF.uniformOfFintype (pSpec.Challenge i)).bind
          (Preliminaries.sampleUniformPreimageOrNone (codec.decode i))) ≤
        PMF.tvDist
          (codec.decode i <$> PMF.uniformOfFintype
            (Vector U (challengeSize (pSpec := pSpec) i)))
          (PMF.uniformOfFintype (pSpec.Challenge i)) :=
      Preliminaries.tvDist_bind_sampleUniformPreimageOrNone_le (codec.decode i)
    _ ≤ @Dist.dist (PMF (pSpec.Challenge i)) instDistPMFOfFintype_arkLib
          (codec.decode i <$> PMF.uniformOfFintype
            (Vector U (challengeSize (pSpec := pSpec) i)))
          (PMF.uniformOfFintype (pSpec.Challenge i)) :=
      Preliminaries.pmf_tvDist_le_serdeDist _ _
    _ = @Dist.dist (PMF (pSpec.Challenge i)) instDistPMFOfFintype_arkLib
          (PMF.uniformOfFintype (pSpec.Challenge i))
          (codec.decode i <$> PMF.uniformOfFintype
            (Vector U (challengeSize (pSpec := pSpec) i))) :=
      by
        change
          (∑ challenge, |((codec.decode i <$> PMF.uniformOfFintype
            (Vector U (challengeSize (pSpec := pSpec) i))) challenge).toReal -
            ((PMF.uniformOfFintype (pSpec.Challenge i)) challenge).toReal|) =
          ∑ challenge, |((PMF.uniformOfFintype (pSpec.Challenge i)) challenge).toReal -
            ((codec.decode i <$> PMF.uniformOfFintype
              (Vector U (challengeSize (pSpec := pSpec) i))) challenge).toReal|
        apply Finset.sum_congr rfl
        intro challenge _
        exact abs_sub_comm _ _
    _ ≤ (codec.decodingBias i : ℝ) := codec.decode_isBiased i

/-- Sampling an in-image fiber representative uses only the auxiliary finite-index oracle, never
the standard challenge-table summand. -/
lemma uniformDeserializePreimageOfImage_isQueryBoundP_challenge_zero
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i)
    (hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty) :
    OracleComp.IsQueryBoundP
      (uniformDeserializePreimageOfImage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge hpreimages_nonempty)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) 0 := by
  unfold uniformDeserializePreimageOfImage
  unfold sampleFromList
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)
  apply (OracleComp.isQueryBoundP_query_iff _ _ 0).mpr
  intro h
  exact h.elim

/-- The legacy total-fibre wrapper has the same auxiliary-only query bound. -/
lemma uniformDeserializePreimage_isQueryBoundP_challenge_zero
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [CodecTotal pSpec U]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i) :
    OracleComp.IsQueryBoundP
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := challengeSpec) challenge)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) 0 := by
  unfold uniformDeserializePreimage
  apply uniformDeserializePreimageOfImage_isQueryBoundP_challenge_zero

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

/-- Predicate selecting the `gᵢ` summand of the internal `D2SQuery` oracle.  All sampling
helpers use the right-hand `Unit →ₒ U` / `unifSpec` summands, while Item 4(e)i is the sole
source of a query satisfying this predicate. -/
def isD2SQueryGPoint :
    (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred
    (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) :=
  fun
  | .inl _ => isTrue trivial
  | .inr _ => isFalse fun h => h

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

/-- The internal unit samplers used by revised `D2SQuery` never address the `gᵢ` summand.
This small accounting fact is the zero-cost half of the Lemma 5.1 query-budget transport. -/
lemma d2sSampleVector_isQueryBoundP_g_zero (m : Nat) :
    OracleComp.IsQueryBoundP
      (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  induction m with
  | zero => simp [d2sSampleVector]
  | succ m ih =>
      change (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m >>= fun xs =>
        d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun u =>
          pure (xs.push u)).IsQueryBoundP
        (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0
      simpa using OracleComp.isQueryBoundP_bind ih (fun xs _ => by
        unfold d2sSampleUnit
        apply (OracleComp.isQueryBoundP_query_iff _ _ 0).mpr
        intro h
        exact h.elim)

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

/-- The fresh capacity branch performs no `gᵢ` query. -/
lemma d2sSampleCapacity_isQueryBoundP_g_zero :
    OracleComp.IsQueryBoundP
      (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  exact d2sSampleVector_isQueryBoundP_g_zero SpongeSize.C

/-- The fresh full-state branch performs no `gᵢ` query. -/
lemma d2sSampleState_isQueryBoundP_g_zero :
    OracleComp.IsQueryBoundP
      (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  exact d2sSampleVector_isQueryBoundP_g_zero SpongeSize.N

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

/-- Padding an encoded verifier answer consumes only auxiliary unit samples, never `gᵢ`.
This is the other zero-cost branch needed by the per-forward-query D2S budget proof. -/
private lemma d2sRateBlocksFromUnitsM_isQueryBoundP_g_zero :
    ∀ (m : Nat) (units : List U),
      OracleComp.IsQueryBoundP
        (d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          m units)
        (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  intro m
  induction m with
  | zero =>
      intro units
      simp [d2sRateBlocksFromUnitsM]
  | succ m ih =>
      intro units
      unfold d2sRateBlocksFromUnitsM
      dsimp
      split
      · simpa using ih (List.drop SpongeSize.R units)
      · rename_i hFull
        simpa using OracleComp.isQueryBoundP_bind
          (d2sSampleVector_isQueryBoundP_g_zero
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) _)
          (fun _ _ => by simpa using ih (List.drop SpongeSize.R units))

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

/-- Reshaping/padding a verifier answer does not issue a `gᵢ` query. -/
lemma d2sRateBlocksFromChallenge_isQueryBoundP_g_zero
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize (pSpec := pSpec) i)) :
    OracleComp.IsQueryBoundP
      (d2sRateBlocksFromChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        challenge)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  unfold d2sRateBlocksFromChallenge
  simpa using d2sRateBlocksFromUnitsM_isQueryBoundP_g_zero
    (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
    (pSpec.Lᵥᵢ i) challenge.toList

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

/-- Install a forward permutation occurrence into the normalized table and append its actual
operation to the insertion trace.  A conflicting mapping has no successor state: the caller
aborts, while a present mapping leaves the table unchanged. -/
def d2sInstallPermForwardState
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U) :
    Option (D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match hStatus : permInstallStatus st.trΔ.p stateIn stateOut with
  | .conflict => none
  | .fresh =>
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn stateOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn stateOut
      let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_add st.h_mirror stateIn stateOut
      some { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
  | .present =>
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, stateOut⟩
      let h_mem : (stateIn, stateOut) ∈ TraceTableOps.entries st.trΔ.p :=
        permInstallStatus_present_mem st.trΔ.p stateIn stateOut hStatus
      let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_existing st.h_mirror stateIn stateOut h_mem
      some { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }

/-- Inverse-orientation counterpart of `d2sInstallPermForwardState`.  The normalized mapping is
still `stateIn ↦ stateOut`; only the inserted trace occurrence is `p⁻¹`. -/
def d2sInstallPermInverseState
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    Option (D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match hStatus : permInstallStatus st.trΔ.p stateIn stateOut with
  | .conflict => none
  | .fresh =>
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn stateOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm_inv st.h_inv stateIn stateOut
      let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_inv_add st.h_mirror stateIn stateOut
      some { st with trace := trace', trΔ := trΔ', h_inv := h_inv', h_mirror := h_mirror' }
  | .present =>
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermInvQuery stateOut, stateIn⟩
      let h_mem : (stateIn, stateOut) ∈ TraceTableOps.entries st.trΔ.p :=
        permInstallStatus_present_mem st.trΔ.p stateIn stateOut hStatus
      let h_mirror' : st.trΔ.MirrorsQueryLog trace' :=
        TraceNabla.MirrorsQueryLog_append_perm_inv_existing st.h_mirror stateIn stateOut h_mem
      some { st with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }

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
      -- Item 3(b) — miss: sample `s_in ← 𝒰(Σ^{r+c})`, then install the mapping.
      let sampled ← StateT.lift <| OptionT.lift <|
        d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
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
  -- Find `s_out` for `s_in` from `Cache_p -> inlu -> sample`.  In the revised `Cache_p` branch
  -- the cache stores only a rate tail, so this is the point at which its output capacity is drawn.
  let st ← get
  match popRateOnlyTailByInput (U := U) st.rateCacheP stateIn with
  -- Item 4(c)i — consume a rate-only cache tail.  This is deliberately the *first* time an
  -- output capacity is sampled for this pending squeeze block.
  | some (tail, cacheTail) =>
      let capacity ← StateT.lift <| OptionT.lift <|
        d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let materialized := materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity
      let cachedOut := materialized.1
      let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
        match materialized.2 with
        | none => cacheTail
        | some successor => successor :: cacheTail
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
        ⟨trace', rateCache', trΔ', h_inv', h_mirror', st._phantom⟩
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

/- CO25 §5.4 Item 4(e)ii--iii, after Item 4(e)i has obtained `ρ̂_i`.

Separating this state transition from the preceding `gᵢ` call makes the paper's accounting
explicit: this continuation uses only auxiliary samples.  It also keeps the dependent
`tr_∇.p.inlu` proof fields local to the transition that constructs them. -/
/-- Continuation of the nonempty codec-image Backtrack branch after the `g_i` reply.  This is
public because the Section 5 trace invariants must reason about its two table-update cases. -/
def d2sHandleBacktrackAfterG
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match hLookup : TraceTableOps.inlu st.trΔ.p stateIn with
  | some recovered =>
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
      let rateBlocks ← StateT.lift <| OptionT.lift <|
        d2sRateBlocksFromChallenge
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (i := backtrackOut.roundIdx) sampledRhoHat
      match rateBlocks.toList with
      | [] => StateT.lift failure
      | firstRate :: remainingRates =>
          -- Item 4(e)iii.B/C: materialize only the first rate block now.  The capacities of all
          -- later squeeze blocks remain unsampled inside the rate-only tail.
          let capacity ← StateT.lift <| OptionT.lift <|
            d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          let s_out := d2sSynthesisState (U := U) firstRate capacity
          let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
            match RateOnlyTail.ofBlocks? (U := U) remainingRates with
            | none => st.rateCacheP
            | some tail => st.rateCacheP ++ [⟨s_out, tail⟩]
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, s_out⟩]
          let trΔ' : TraceNabla T_H T_P StmtIn U :=
            { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn s_out }
          let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn s_out
          let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
            TraceNabla.MirrorsQueryLog_append_perm_add st.h_mirror stateIn s_out
          let st' : D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
            ⟨trace', rateCache', trΔ', h_inv', h_mirror', st._phantom⟩
          set st'
          return s_out

/-- CO25 §5.4 Items 4(d)/4(e) — `BackTrack` returned `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)`.

Splits on the codec-image predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` (Item 4(d) vs 4(e), lines
1056/1059) and dispatches in paper order.

Paper Item 4(e) (in-image branch):
- (e)i  : `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`  — issued for a nonempty
  verifier squeeze.
- (e)ii : `s_out := tr_∇.p.inlu(s_in)`, if any.
- (e)iii: else, sample `z`, reshape `ρ̂_i ‖ z` into `L_V(i)` rate blocks, synthesize `s_out`
  from the first block, chain the remainder into `Cache_p`, and `tr_∇.p.add(s_in, s_out)`.

For a nonempty squeeze, the `g_i` query in (e)i is essential: `tr_i` (paper Item 3 of
`D2SAlgo`, lived externally to D2SQuery) makes the bridge `ψ⁻¹ ∘ f ∘ φ⁻¹` deterministic
w.r.t. the encoded query, so the cost of a repeat `gᵢ` call is a cache hit, not fresh
randomness.  A zero-length squeeze has no corresponding `p` query and therefore takes the
ordinary no-result branch. -/
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
    if _hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx then
      -- Paper Item 4(e)i — `g_i` exists only for a nonempty verifier squeeze.
      -- Determinism w.r.t. the encoded key is enforced by `D2SAlgo`'s `tr_i` memo at the
      -- bridge layer (`d2sCodecBridgeImplMemo` in §5.4 D2SAlgo); same key ⇒ same response.
      let sampledRhoHat ← StateT.lift <| OptionT.lift <|
        d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt
          backtrackOut.encodedMessages
      d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        stateIn backtrackOut sampledRhoHat
    else
      -- Defensive totality guard.  The stateful parser cannot normally return
      -- such an output, but treating it as no-result keeps `D2SQuery` faithful
      -- if a future parser is weakened or called through an alternate path.
      d2sHandleBacktrackNoResult (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn
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
    by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
    · simp [hNonempty] at hi
      obtain ⟨rhoHat, _hrhoHat, hi⟩ := mem_support_option_elimM_some hi
      unfold d2sHandleBacktrackAfterG at hi
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_lift,
        OptionT.run_bind, OptionT.run_lift, OptionT.run_pure, Option.elimM,
        pure_bind, Option.elim_some] at hi
      split at hi
      · aesop
      · simp at hi
        obtain ⟨rateBlocks, _hrateBlocks, hi⟩ := mem_support_option_elimM_some hi
        cases hBlocks : rateBlocks.toList with
        | nil => simp [hBlocks] at hi
        | cons firstRate remainingRates =>
            simp [hBlocks] at hi
            obtain ⟨capacity, _hcapacity, ha, hstEq⟩ := hi
            rw [← hstEq]
            simp only
            rw [ha]
    · apply d2sHandleBacktrackNoResult_support_trace_append
          (T_H := T_H) (T_P := T_P) (δ := δ)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          gImpl auxImpl stateIn st
      simpa [hNonempty] using hi
      rfl

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

set_option maxHeartbeats 400000 in
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
- `d2sAlgo`: `m = StateT (D2SAlgoMemo …) (AbortComp …)`,
  `gImpl = d2sCodecBridgeImplMemo` — threads the paper Item 3 `tr_i` memo;
  `auxImpl` lifts `(Unit →ₒ U) + unifSpec` queries through to the outer
  `D2SChallengePlusUnitOracle`.
- §5.8 hybrid games (`hybridGame`): `m = OptionT (OracleComp _)`,
  `gImpl` varies per hybrid (`g`, `e`, `f`, …); `auxImpl` lifts to the same outer spec. -/
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

/-! ### Local `g`-query accounting -/

section LocalGQueryBounds

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- Predicate selecting forward permutation queries in the duplex-sponge query interface.
CO25 §5.4 uses precisely these queries as the possible source of an Item-4(e)i `gᵢ` call. -/
def isD2SForwardPermPoint :
    (duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | Sum.inr (Sum.inl _) => True
  | _ => False

instance : DecidablePred (isD2SForwardPermPoint (StmtIn := StmtIn) (U := U)) :=
  fun q =>
    match q with
    | Sum.inr (Sum.inl _) => isTrue True.intro
    | Sum.inl _ => isFalse (fun h => h)
    | Sum.inr (Sum.inr _) => isFalse (fun h => h)

end LocalGQueryBounds

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
  {T_H : Type} {T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The query-producing prefix of CO25 §5.4 Eq. 16.  Given a `gSpec` query
`(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)`, it parses the encoded prover prefix and performs the matching basic-FS
query `fᵢ`.  It deliberately does *not* sample a `ψᵢ⁻¹` preimage.  Keeping this prefix separate
lets `d2sCodecBridgeImplMemo` issue the required `fᵢ` occurrence even on a memo hit, while the
memo still fixes the encoded preimage returned to the adversary. -/
noncomputable def d2sCodecBridgeQuery
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    OptionT (OracleComp
      (D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec)))
      (pSpec.Challenge q.1) :=
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    do
      let messagesBefore ←
        match hybEncodedMessagesBefore?
            (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | some messagesBefore => pure messagesBefore
        | none => failure
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

/-- The codec bridge's query-producing prefix makes at most one standard challenge-table call.
If encoded messages fail to parse, it makes none; this is the exact local accounting fact needed
for D2SAlgo's `tₚ` budget and does not assume decoder surjectivity. -/
lemma d2sCodecBridgeQuery_isQueryBoundP_challenge_le_one
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    OracleComp.IsQueryBoundP
      (d2sCodecBridgeQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) q).run
      (isD2SChallengePoint (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) 1 := by
  unfold d2sCodecBridgeQuery
  dsimp
  split
  · apply (OracleComp.isQueryBoundP_query_iff _ _ 1).mpr
    exact fun _ => by simp [isD2SChallengePoint]
  · simp

/-- A lossless `Option.elimM` adds no target-oracle calls when each branch is target-query-free.
The helper keeps the `OptionT` short-circuit in the codec bridge visible to the accounting proof. -/
private lemma d2s_option_elimM_isQueryBoundP
    {κ α β : Type} {challengeSpec : OracleSpec κ}
    (oa : OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) (Option α))
    (onone : OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) β)
    (onsome : α → OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) β)
    (n m : ℕ)
    (h : OracleComp.IsQueryBoundP oa
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) n)
    (hnone : OracleComp.IsQueryBoundP onone
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) m)
    (hsome : ∀ a, OracleComp.IsQueryBoundP (onsome a)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) m) :
    OracleComp.IsQueryBoundP (Option.elimM oa onone onsome)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) (n + m) := by
  unfold Option.elimM
  simpa using OracleComp.isQueryBoundP_bind (n := n) (m := m) h (fun value _ => by
    cases value with
    | none => simpa using hnone
    | some a => simpa using hsome a)

/-- Generic predicate-query accounting for the `Option.elimM` normal form of `OptionT.run`. -/
private lemma isQueryBoundP_option_elimM
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p]
    (oa : OracleComp spec (Option α)) (onone : OracleComp spec β)
    (onsome : α → OracleComp spec β) (n m : ℕ)
    (h : OracleComp.IsQueryBoundP oa p n)
    (hnone : OracleComp.IsQueryBoundP onone p m)
    (hsome : ∀ a, OracleComp.IsQueryBoundP (onsome a) p m) :
    OracleComp.IsQueryBoundP (Option.elimM oa onone onsome) p (n + m) := by
  unfold Option.elimM
  simpa using OracleComp.isQueryBoundP_bind (n := n) (m := m) h (fun value _ => by
    cases value with
    | none => simpa using hnone
    | some a => simpa using hsome a)

/-- Public predicate-query accounting for a one-state aborting simulation.  One source request
costs at most one target request exactly at the selected source predicate. -/
theorem isQueryBoundP_simulateQ_run_StateT_OptionT_of_step
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α σ : Type} {p : ι₁ → Prop} [DecidablePred p] {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec₁ (StateT σ (OptionT (OracleComp spec₂)))}
    {oa : OracleComp spec₁ α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep : ∀ t s, OracleComp.IsQueryBoundP (((impl t).run s).run) q
      (if p t then 1 else 0))
    (s : σ) :
    OracleComp.IsQueryBoundP (((simulateQ impl oa).run s).run) q n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind, OptionT.run_bind]
      change OracleComp.IsQueryBoundP
        (Option.elimM (((impl t).run s).run) (pure none)
          (fun result => ((simulateQ impl (mx result.1)).run result.2).run)) q n
      refine (isQueryBoundP_option_elimM _ _ _
        (if p t then 1 else 0) (if p t then n - 1 else n)
        (hstep t s) (by simp) (fun result => ?_)).mono ?_
      · exact ih result.1 (h.2 result.1) result.2
      · by_cases hpt : p t
        · simp only [if_pos hpt]
          rcases h.1 with hnot | hpositive
          · exact False.elim (hnot hpt)
          · omega
        · simp only [if_neg hpt]
          omega

/-- Public two-state predicate-query transport for D2SAlgo.  Source-query simulation threads the
D2S normal state and memo independently while retaining the same predicate-query budget. -/
theorem isQueryBoundP_simulateQ_run_StateT_StateT_OptionT_of_step
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α σ τ : Type} {p : ι₁ → Prop} [DecidablePred p] {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec₁ (StateT σ (StateT τ (OptionT (OracleComp spec₂))))}
    {oa : OracleComp spec₁ α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep : ∀ t s u, OracleComp.IsQueryBoundP ((((impl t).run s).run u).run) q
      (if p t then 1 else 0))
    (s : σ) (u : τ) :
    OracleComp.IsQueryBoundP ((((simulateQ impl oa).run s).run u).run) q n := by
  induction oa using OracleComp.inductionOn generalizing n s u with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind, OptionT.run_bind]
      change OracleComp.IsQueryBoundP
        (Option.elimM ((((impl t).run s).run u).run) (pure none)
          (fun result =>
            (((simulateQ impl (mx result.1.1)).run result.1.2).run result.2).run))
        q n
      refine (isQueryBoundP_option_elimM _ _ _
        (if p t then 1 else 0) (if p t then n - 1 else n)
        (hstep t s u) (by simp) (fun result => ?_)).mono ?_
      · exact ih result.1.1 (h.2 result.1.1) result.1.2 result.2
      · by_cases hpt : p t
        · simp only [if_pos hpt]
          rcases h.1 with hnot | hpositive
          · exact False.elim (hnot hpt)
          · omega
        · simp only [if_neg hpt]
          omega

/-- CO25 §5.4 Eq. 16 — `gᵢ`-summand of the codec bridge: `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`.

Given a `gSpec` query `(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)`:
1. `φ⁻¹`: parse `α̂_{<i}` → `α_{<i}` via `hybEncodedMessagesBefore?` (⊥ on failure)
2. `f`: query `fᵢ(𝕩, bin(τ̂), α₁, …, αᵢ)` → `ρᵢ ∈ ℳ_{V,i}` via `fsChallengeOracle`
   keyed at the pre-encoded salt `Salt` (paper's `{0,1}^{δ⋆}`; bridge =
   `SaltCodec.encode = bin`)
3. `Lift`: if `ρᵢ ∉ Im(ψᵢ)`, stop; otherwise sample
   `ρ̂ᵢ ← 𝒰(ψᵢ⁻¹(ρᵢ))`.  This explicit image test is the paper's Claim 5.23
   codec stop, not a duplex bad event. -/
noncomputable def d2sCodecBridgeImpl :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))) :=
  fun q => do
    let challenge ←
      d2sCodecBridgeQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) q
    if hpreimages :
        (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
      -- The partial `Lift_i` kernel is called only on `Im(ψ_i)`.
      OptionT.lift <|
        uniformDeserializePreimageOfImage
          (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
          challenge hpreimages
    else
      -- This is the public codec-image stop of Claim 5.23.  It occurs after the `f_i`
      -- occurrence above and before a new duplex occurrence can be installed.
      failure

end CodecBridge

/-! ## Decoded-challenge bridge `gᵢ = ψᵢ⁻¹ ∘ eᵢ`

CO25 §5.8 Hyb₂ uses the decoded challenge oracle `eᵢ`, followed by the uniform
`ψᵢ⁻¹` preimage sampler. The composition is an oracle, not a fresh sampler at
each call: repeated encoded keys must return the same encoded challenge. -/

section DecodedBridgeMemo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

local instance : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _

structure D2SDecodedMemoEntry
    (StmtIn : Type) (U : Type) (δ : ℕ) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Vector U δ
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc
  response : Vector U (challengeSize (pSpec := pSpec) roundIdx)

abbrev D2SDecodedMemo (StmtIn : Type) (U : Type) (δ : ℕ)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :=
  List (D2SDecodedMemoEntry StmtIn U δ pSpec)

instance [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    Inhabited (D2SDecodedMemo StmtIn U δ pSpec) := ⟨[]⟩

open Classical in
noncomputable def lookupD2SDecodedMemo
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
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

def insertD2SDecodedMemo
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (entry : D2SDecodedMemoEntry StmtIn U δ pSpec) :
    D2SDecodedMemo StmtIn U δ pSpec :=
  memo ++ [entry]

/-- A newly inserted decoded-bridge entry is found at its exact encoded key, provided that key
was absent before insertion.  This is the memo invariant needed to lift the one-cell Claim 5.22
reparameterization to an adaptive sequence: the fresh fibre sample is made once and every later
occurrence observes that same representative. -/
lemma lookupD2SDecodedMemo_insert_same_of_none
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (entry : D2SDecodedMemoEntry StmtIn U δ pSpec)
    (hmiss : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo entry.roundIdx entry.stmt entry.salt entry.encodedMessages = none) :
    lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      (insertD2SDecodedMemo memo entry) entry.roundIdx entry.stmt entry.salt
      entry.encodedMessages = some entry.response := by
  unfold lookupD2SDecodedMemo at hmiss
  unfold insertD2SDecodedMemo lookupD2SDecodedMemo
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, hmiss]
  simp

/-- Extending the decoded-bridge memo cannot change an already-recorded response.  The lookup is
left-biased, so this is the stability invariant needed when an adaptive run later inserts a
different fresh key. -/
lemma lookupD2SDecodedMemo_insert_preserves_some
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (entry : D2SDecodedMemoEntry StmtIn U δ pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (response : Vector U (challengeSize (pSpec := pSpec) i))
    (hlookup : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo i stmt salt encodedMessages = some response) :
    lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      (insertD2SDecodedMemo memo entry) i stmt salt encodedMessages = some response := by
  unfold lookupD2SDecodedMemo at hlookup
  unfold insertD2SDecodedMemo lookupD2SDecodedMemo
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, hlookup]
  simp

/-- The non-aborting one-cell H₂ bridge computation.  It queries the decoded table and samples
one uniform representative of the returned decoder fibre. -/
noncomputable def d2sDecodedBridgeBaseRun [CodecTotal pSpec U] :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OracleComp (D2SChallengePlusUnitOracle (U := U)
        (eSpec (U := U) StmtIn pSpec δ))) :=
  fun q => do
    let challenge ←
      (show OracleComp
          (D2SChallengePlusUnitOracle (U := U)
            (eSpec (U := U) StmtIn pSpec δ))
          (pSpec.Challenge q.1) from
        query
          (spec := D2SChallengePlusUnitOracle (U := U)
            (eSpec (U := U) StmtIn pSpec δ))
          (.inl q))
    uniformDeserializePreimage
      (pSpec := pSpec) (U := U)
      (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge

/-- The uncached one-cell H₂ bridge, lifted into the common abort stack.  The underlying
`d2sDecodedBridgeBaseRun` has no failure branch; the cache wrapper below is therefore the
authoritative live implementation without adding a semantic abort possibility. -/
noncomputable def d2sDecodedBridgeBaseImpl [CodecTotal pSpec U] :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (AbortComp (D2SChallengePlusUnitOracle (U := U)
        (eSpec (U := U) StmtIn pSpec δ))) :=
  fun q => OptionT.lift <|
    d2sDecodedBridgeBaseRun (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) q

/-- The authoritative H₂ bridge implementation.  Every encoded `gᵢ` invocation first reissues
its corresponding decoded-table `eᵢ` query, so the translated trace retains the original
occurrence order and multiplicity.  The cache memoizes only the sampled encoded representative:
on a repeat it returns that same representative after the reissued `eᵢ` lookup. -/
noncomputable def d2sDecodedBridgeImplCache [CodecTotal pSpec U] :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (eSpec (U := U) StmtIn pSpec δ)
      ((gSpec (U := U) StmtIn pSpec δ).QueryCache) :=
  fun q => do
    let challenge ← StateT.lift <| OptionT.lift <|
      (show OracleComp
          (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (pSpec.Challenge q.1) from
        query
          (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl q))
    let cache ← get
    match cache q with
    | some response => pure response
    | none =>
        let response ← StateT.lift <| OptionT.lift <|
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge
        modify (fun current => current.cacheQuery q response)
        pure response

/-- Revised-paper H₂ bridge.  It has the same requery-and-memo behavior as the legacy cache
bridge, but invokes the decoder-fibre sampler only after an explicit image test.  Therefore it
implements the partial `Lift` convention of Claim 5.22 rather than relying on the global
surjectivity field of the legacy `Codec` interface.  For H₂'s actual `D_e` sampler this failure
branch is unreachable; retaining it here makes the oracle-level operation total only on the
decoder image, as the paper requires. -/
noncomputable def d2sDecodedBridgeImplCacheOfImage :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (eSpec (U := U) StmtIn pSpec δ)
      ((gSpec (U := U) StmtIn pSpec δ).QueryCache) :=
  fun q => do
    let challenge ← StateT.lift <| OptionT.lift <|
      (show OracleComp
          (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (pSpec.Challenge q.1) from
        query
          (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
          (.inl q))
    if hpreimages :
        (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
      let cache ← get
      match cache q with
      | some response => pure response
      | none =>
          let response ← StateT.lift <| OptionT.lift <|
            uniformDeserializePreimageOfImage
              (pSpec := pSpec) (U := U)
              (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge hpreimages
          modify (fun current => current.cacheQuery q response)
          pure response
    else
      failure

/-- The post-lookup hit residual of the partial H₂ bridge is deterministic.  This small
state-machine equality is separated from the outer decoded-table query so later coupling proofs
can retain the public occurrence while simplifying only the cache transition. -/
lemma d2sDecodedBridgeImplCacheOfImage_hit_residual
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (response : Vector U (challengeSize (pSpec := pSpec) q.1))
    (challenge : pSpec.Challenge q.1)
    (hcache : cache q = some response) :
    ((if hpreimages :
        (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
        do
          let current : (gSpec (U := U) StmtIn pSpec δ).QueryCache ← get
          match current q with
          | some response => pure response
          | none =>
              let fresh ← StateT.lift <| OptionT.lift <|
                uniformDeserializePreimageOfImage
                  (pSpec := pSpec) (U := U)
                  (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge hpreimages
              modify (fun (current : (gSpec (U := U) StmtIn pSpec δ).QueryCache) =>
                current.cacheQuery q fresh)
              pure fresh
      else
        failure).run cache) =
      (if hpreimages :
          (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
        pure (response, cache)
      else
        failure) := by
  split <;> simp [hcache] <;> rfl

/-- The post-lookup cache-miss residual of the partial H₂ bridge performs one partial-fibre
sample, installs it at the encoded key, and otherwise preserves the image-failure abort. -/
lemma d2sDecodedBridgeImplCacheOfImage_miss_residual
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (challenge : pSpec.Challenge q.1)
    (hcache : cache q = none) :
    ((if hpreimages :
        (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
        do
          let current : (gSpec (U := U) StmtIn pSpec δ).QueryCache ← get
          match current q with
          | some response => pure response
          | none =>
              let fresh ← StateT.lift <| OptionT.lift <|
                uniformDeserializePreimageOfImage
                  (pSpec := pSpec) (U := U)
                  (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge hpreimages
              modify (fun (current : (gSpec (U := U) StmtIn pSpec δ).QueryCache) =>
                current.cacheQuery q fresh)
              pure fresh
      else
        failure).run cache) =
      (if hpreimages :
          (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
        do
          let fresh ← OptionT.lift <|
            uniformDeserializePreimageOfImage
              (pSpec := pSpec) (U := U)
              (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge hpreimages
          pure (fresh, cache.cacheQuery q fresh)
      else
        failure) := by
  split <;> simp [hcache] <;> rfl

/-- On an H₂ cache hit, the bridge still reissues the corresponding decoded challenge query,
then returns the stored encoded representative without modifying the cache. -/
lemma d2sDecodedBridgeImplCache_run_of_hit
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (response : Vector U (challengeSize (pSpec := pSpec) q.1))
    (hcache : cache q = some response) :
    (d2sDecodedBridgeImplCache (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      q).run cache = (do
        let _ ← OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (pSpec.Challenge q.1) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U) (eSpec (U := U) StmtIn pSpec δ))
              (.inl q))
        pure (response, cache)) := by
  apply OptionT.ext
  simp [d2sDecodedBridgeImplCache, hcache]

/-- On an H₂ cache miss, the bridge executes one decoded-table/fibre step and installs its
result at the encoded key. -/
lemma d2sDecodedBridgeImplCache_run_of_miss
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (hcache : cache q = none) :
    (d2sDecodedBridgeImplCache (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      q).run cache =
      (fun response => (response, cache.cacheQuery q response)) <$>
        (d2sDecodedBridgeBaseImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          q) := by
  apply OptionT.ext
  simp [d2sDecodedBridgeImplCache, d2sDecodedBridgeBaseImpl,
    d2sDecodedBridgeBaseRun, hcache]
  rfl

/-- Memoized `ψ⁻¹ ∘ e`: the decoded oracle is queried only on a cache miss. -/
noncomputable def d2sDecodedBridgeImplMemo [CodecTotal pSpec U] :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (eSpec (U := U) StmtIn pSpec δ)
      (D2SDecodedMemo StmtIn U δ pSpec) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    do
      let memo ← get
      match lookupD2SDecodedMemo
          (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
          memo roundIdx stmt salt encodedMessages with
      | some response => pure response
      | none =>
          let challenge ← StateT.lift <| OptionT.lift <|
            (show OracleComp
                (D2SChallengePlusUnitOracle (U := U)
                  (eSpec (U := U) StmtIn pSpec δ))
                (pSpec.Challenge roundIdx) from
              query
                (spec := D2SChallengePlusUnitOracle (U := U)
                  (eSpec (U := U) StmtIn pSpec δ))
                (.inl q))
          let response ← StateT.lift <| OptionT.lift <|
            uniformDeserializePreimage
              (pSpec := pSpec) (U := U)
              (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge
          modify (fun m =>
            insertD2SDecodedMemo
              (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec) m
              { roundIdx := roundIdx, stmt := stmt, salt := salt,
                encodedMessages := encodedMessages, response := response })
          pure response

/-- On a decoded-bridge memo hit, the bridge is deterministic: it makes no `eᵢ` lookup and
returns the stored encoded representative without changing the memo.  This is the repeat-key
half of the adaptive Claim 5.22 coupling. -/
lemma d2sDecodedBridgeImplMemo_run_of_lookup_eq_some
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (response : Vector U (challengeSize (pSpec := pSpec) q.1))
    (hlookup : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo q.1 q.2.1 q.2.2.1 q.2.2.2 = some response) :
    (d2sDecodedBridgeImplMemo (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      q).run memo = pure (response, memo) := by
  apply OptionT.ext
  simp [d2sDecodedBridgeImplMemo, hlookup]
  rfl

/-- On a decoded-bridge memo miss, the operational bridge makes exactly its one decoded-table
query, uniformly lifts that decoded answer to an encoded representative, and records that
representative under the queried key.  This is the fresh-key half of the adaptive Claim 5.22
coupling; paired with the hit lemma above, it exposes the bridge as a genuine lazy table. -/
lemma d2sDecodedBridgeImplMemo_run_of_lookup_eq_none
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (hmiss : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo q.1 q.2.1 q.2.2.1 q.2.2.2 = none) :
    (d2sDecodedBridgeImplMemo (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      q).run memo =
      (do
        let challenge ← OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U)
                (eSpec (U := U) StmtIn pSpec δ))
              (pSpec.Challenge q.1) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U)
                (eSpec (U := U) StmtIn pSpec δ))
              (.inl q))
        let response ← OptionT.lift <|
          uniformDeserializePreimage
            (pSpec := pSpec) (U := U)
            (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge
        let entry : D2SDecodedMemoEntry StmtIn U δ pSpec :=
          { roundIdx := q.1, stmt := q.2.1, salt := q.2.2.1,
            encodedMessages := q.2.2.2, response := response }
        pure (response,
          insertD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
            memo entry)) := by
  simp [d2sDecodedBridgeImplMemo, hmiss]

/-- Immediately after a genuine miss inserts its entry, the next occurrence of that same encoded
key is a deterministic memo hit.  This packages the insertion and hit laws in the exact form
used by an induction over an adaptive query transcript. -/
lemma d2sDecodedBridgeImplMemo_run_after_insert_of_lookup_eq_none
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (response : Vector U (challengeSize (pSpec := pSpec) q.1))
    (hmiss : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo q.1 q.2.1 q.2.2.1 q.2.2.2 = none) :
    (d2sDecodedBridgeImplMemo (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      q).run
        (insertD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec) memo
          { roundIdx := q.1, stmt := q.2.1, salt := q.2.2.1,
            encodedMessages := q.2.2.2, response := response }) =
      pure (response,
        insertD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec) memo
          { roundIdx := q.1, stmt := q.2.1, salt := q.2.2.1,
            encodedMessages := q.2.2.2, response := response }) := by
  apply d2sDecodedBridgeImplMemo_run_of_lookup_eq_some
  exact lookupD2SDecodedMemo_insert_same_of_none
    (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec) _ _ hmiss

/-- A decoded-bridge memo hit incurs no decoded-challenge-table query.  Together with the
miss branch, this isolates the exact ``one fresh cell per distinct key'' accounting required by
the adaptive H₁--H₂ reparameterization. -/
lemma d2sDecodedBridgeImplMemo_run_of_lookup_eq_some_isQueryBoundP_challenge_zero
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SDecodedMemo StmtIn U δ pSpec)
    (response : Vector U (challengeSize (pSpec := pSpec) q.1))
    (hlookup : lookupD2SDecodedMemo (StmtIn := StmtIn) (U := U) (δ := δ) (pSpec := pSpec)
      memo q.1 q.2.1 q.2.2.1 q.2.2.2 = some response) :
    OracleComp.IsQueryBoundP
      (((d2sDecodedBridgeImplMemo (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        q).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := eSpec (U := U) StmtIn pSpec δ)) 0 := by
  rw [d2sDecodedBridgeImplMemo_run_of_lookup_eq_some (q := q) (memo := memo)
    (response := response) hlookup]
  change OracleComp.IsQueryBoundP (pure (some (response, memo))) _ 0
  simp

/-- Every decoded-bridge invocation consumes at most one `eᵢ` table cell; by the preceding
hit lemma that one cell can occur only on a memo miss. -/
lemma d2sDecodedBridgeImplMemo_run_isQueryBoundP_challenge_le_one
    [CodecTotal pSpec U]
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SDecodedMemo StmtIn U δ pSpec) :
    OracleComp.IsQueryBoundP
      (((d2sDecodedBridgeImplMemo (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        q).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := eSpec (U := U) StmtIn pSpec δ)) 1 := by
  simp [d2sDecodedBridgeImplMemo]
  split
  · simp
  · simp only [StateT.run_bind, StateT.run_lift, OptionT.run_bind, OptionT.run_lift, modify]
    apply isQueryBoundP_option_elimM (n := 1) (m := 0)
    · apply d2s_option_elimM_isQueryBoundP (n := 1) (m := 0)
      · change OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (Sum.inl q)) >>= fun x => pure (some x)) _ 1
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr (by omega), fun _ => by simp⟩
      · simp
      · intro _
        simp
    · simp
    · rintro ⟨challenge, memo'⟩
      apply isQueryBoundP_option_elimM (n := 0) (m := 0)
      · apply d2s_option_elimM_isQueryBoundP (n := 0) (m := 0)
        · simpa using uniformDeserializePreimage_isQueryBoundP_challenge_zero
            (pSpec := pSpec) (U := U)
            (challengeSpec := eSpec (U := U) StmtIn pSpec δ) challenge
        · simp
        · intro _
          simp
      · simp
      · intro _
        simp

end DecodedBridgeMemo

/-! ## `D2SAlgoMemo` — `tr_i` memo for the codec bridge (CO25 §5.4 D2SAlgo Item 3)

The unconditional `gᵢ` query in `D2SQuery` Item 4(e)i (see `d2sHandleBacktrackSome`) means
that two adversary queries with the same `BacktrackOutput` produce two `gᵢ` queries with the
same encoded key in the resulting `OracleComp` tree. Without a memo at the bridge layer, the
randomness in `uniformDeserializePreimage` (the `ψ⁻¹` step) would give them different
responses, violating CO25 §5.4 D2SAlgo Item 3's determinism on repeat keys.

`D2SAlgoMemo` is the `tr_i : (i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i` table the paper threads through
the bridge as a `StateT` layer over `d2sCodecBridge`. **Every invocation first issues the matching
basic-FS `f_i` query.** On a cache hit, its answer is discarded and the stored `ρ̂_i` is returned;
on a miss, that answer is used to sample and append the new `ρ̂_i`. Thus the memo fixes the
encoded preimage, never suppresses the standard-oracle occurrence. -/

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

Every invocation parses and queries the corresponding `f_i` table through `d2sCodecBridgeQuery`.
On a `D2SAlgoMemo` hit, it discards that already-recorded `f_i` answer and returns the stored
encoded preimage without resampling `ψ⁻¹`; on a miss, it samples the preimage from the queried
answer and stores it.  Consequently the memo preserves deterministic encoded answers while the
standard trace retains one `f_i` occurrence per `g_i` invocation. -/
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
      -- Paper Algorithm 5.4 Step 1: every `g_i` invocation issues this matching `f_i` query,
      -- including a memo hit.  Only the encoded `ψ_i⁻¹` preimage is memoized below.
      let challenge ← StateT.lift <|
        d2sCodecBridgeQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) q
      if hpreimages :
          (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty then
        let memo ← get
        match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
            (pSpec := pSpec) memo roundIdx stmt encodedSalt encodedMessages with
        -- Item 3 cache hit: retain the just-issued `f_i` occurrence, return the stored `ρ̂_i`.
        | some response => pure response
        | none =>
            -- Item 3 cache miss: use the queried `f_i` answer to sample `ρ̂_i`,
            --   then `tr_i := tr_i ∪ {(i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i}`.
            let response ← StateT.lift <|
              uniformDeserializePreimageOfImage
                (pSpec := pSpec) (U := U)
                (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
                challenge hpreimages
            modify (fun m =>
              insertD2SAlgoMemo
                (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec) m
                { roundIdx := roundIdx, stmt := stmt, salt := encodedSalt,
                  encodedMessages := encodedMessages, response := response })
            pure response
      else
        -- Paper Algorithm 5.4 Step 2: this outer stop is charged solely by Claim 5.23.
        failure

/-- Every invocation of the memoized codec bridge retains its corresponding standard `f_i`
occurrence.  A memo hit avoids only the auxiliary fiber sample; it never reduces the challenge
table trace multiplicity. -/
lemma d2sCodecBridgeImplMemo_run_isQueryBoundP_challenge_le_one
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    OracleComp.IsQueryBoundP
      ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) q).run memo).run
      (isD2SChallengePoint (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) 1 := by
  simp [d2sCodecBridgeImplMemo]
  apply d2s_option_elimM_isQueryBoundP (m := 0)
  · exact d2sCodecBridgeQuery_isQueryBoundP_challenge_le_one
      (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) (Salt := Salt) q
  · simp
  · intro challenge
    split
    · generalize hlookup : lookupD2SAlgoMemo
        (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo q.1 q.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1)
        q.2.2.2 = hit
      cases hit with
      | none =>
          simp [StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, modify, hlookup,
            uniformDeserializePreimageOfImage_isQueryBoundP_challenge_zero]
      | some response => simp [StateT.run_bind, hlookup]
    · simp

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
