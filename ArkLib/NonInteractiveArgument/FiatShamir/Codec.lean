/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Devon Tuma
-/
module

public import ArkLib.Data.Classes.CloseToUniform
public import ArkLib.OracleReduction.ProtocolSpec.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.DiscreteTVDistFintype

/-!
# Duplex-sponge Fiat–Shamir codecs

This module defines the message-length interfaces, the round-indexed codec, and the salt
encoding shared with the canonical Fiat–Shamir oracle.
-/

@[expose] public section

namespace ProtocolSpec

/-- **[CO25, Definition 4.1]** Type class for protocol specifications to specify the size of each
  message as a natural number (to be interpreted as a vector of units `U` of the given size for some
  sponge unit `U`).

  `U`-independent so that size-only helpers (e.g. `numPermQueriesProverMessage`) stay free of the
  unit parameter. `Codec pSpec U` extends this class. -/
class HasProverMessageSize {n : ℕ} (pSpec : ProtocolSpec n) where
  proverMessageSize : pSpec.MessageIdx → Nat

export HasProverMessageSize (proverMessageSize)

/-- Message indices in rounds strictly before `k`. -/
abbrev ProverMessageIdxBefore {n : ℕ} (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  {j : pSpec.MessageIdx // j.1.1 < k.1}

/-- **[CO25, §5.2]** Encoded prover prefix `(α̂₁, …, α̂ₘ)` before schedule boundary `k`:
`∏_{j ∈ P, j < k} Σ^{ℓ_P(j)}`, where `Σ = U`, `P` is the set of prover positions,
and `m` counts those before `k`.
The empty product is a singleton. Lean indexes the product by `ProverMessageIdxBefore k pSpec`. -/
abbrev EncodedProverMessagesBefore {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    [HasProverMessageSize pSpec]
    (k : Fin (n + 1)) : Type :=
  (j : ProverMessageIdxBefore k pSpec) → Vector U (proverMessageSize j.val)

/-- **[CO25, Definition 4.1]** Type class for protocol specifications to specify the size of each
  verifier message as a natural number (to be interpreted as a vector of units `U` of the given size
  for some sponge unit `U`).

  `U`-independent so that size-only helpers (e.g. `numPermQueriesVerifierMessage`) stay free of the
  unit parameter. `Codec pSpec U` extends this class. -/
class HasVerifierMessageSize {n : ℕ} (pSpec : ProtocolSpec n) where
  verifierMessageSize : pSpec.ChallengeIdx → Nat

export HasVerifierMessageSize (verifierMessageSize)

namespace EncodedProverMessagesBefore

/-- Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`. -/
noncomputable def toList {n : ℕ} {pSpec : ProtocolSpec n} {U : Type} [HasProverMessageSize pSpec]
    {k : Fin (n + 1)} (f : pSpec.EncodedProverMessagesBefore U k) :
    List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)) :=
  (Finset.univ : Finset (pSpec.MessageIdx)).toList.filterMap fun j =>
    if h : j.1.1 < k.1 then some ⟨j, f ⟨j, h⟩⟩ else none

end EncodedProverMessagesBefore

/-- **[CO25, Definition 4.1]** Per-round encoding and decoding for duplex-sponge Fiat–Shamir.

Each prover message has an injective fixed-length encoding, and each verifier-message decoder
is surjective with an explicit total-variation bias bound. The size classes record the lengths
independently of the sponge alphabet. The projection instances supply the corresponding
`Serialize` and `Deserialize` instances, and `Codec.mk'` assembles a codec from those
instances and the decoding hypotheses.
-/
class Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    extends HasProverMessageSize pSpec, HasVerifierMessageSize pSpec where
  /-- **[CO25, Definition 4.1]** `φᵢ : M_{P,i} → Σ^{ℓ_P(i)}` — prover message encoder. -/
  encode : (i : pSpec.MessageIdx) → pSpec.Message i → Vector U (proverMessageSize i)
  encode_injective : ∀ i, Function.Injective (encode i) -- `φᵢ` is injective
  /-- **[CO25, Definition 4.1]** `ψᵢ : Σ^{ℓ_V(i)} → M_{V,i}` — verifier message decoder. -/
  decode : (i : pSpec.ChallengeIdx) → Vector U (verifierMessageSize i) → pSpec.Challenge i
  /-- **[CO25, Definition 4.1]** The bias `ε_{cdc,i}` of the decoder `ψᵢ`. -/
  decodingBias : pSpec.ChallengeIdx → NNReal -- `ε_cdc`
  /-- **[CO25, Definition 4.1]** For every `i`, `decode i` is ε-biased in total variation:
    `discreteTVDist (𝒰 M_{V,i}) (decode_i <$> 𝒰 Σ^{ℓ_V(i)}) ≤ decodingBias i`
    ([CO25, Definition 4.1]). Every `SampleableType` instance samples uniformly, so the statement
    does not depend on the chosen samplers. -/
  decode_isBiased : ∀ (i : pSpec.ChallengeIdx)
      [SampleableType (Vector U (verifierMessageSize i))] [SampleableType (pSpec.Challenge i)],
      discreteTVDist ($ᵗ (pSpec.Challenge i)) (decode i <$> ($ᵗ (Vector U (verifierMessageSize i))))
        ≤ decodingBias i
  /-- **[CO25, Definition 4.1]** For every `i`, `decode i` is surjective: every verifier message has
    at least one encoded preimage. Required for the `ψ⁻¹` sampler in the Section 5.8 reduction. -/
  decode_surjective : ∀ i, Function.Surjective (decode i)

namespace Codec

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}

instance (priority := high) instSerializeMessage [c : Codec pSpec U] (i : pSpec.MessageIdx) :
    Serialize (pSpec.Message i) (Vector U (proverMessageSize i)) where
  serialize := c.encode i

instance (priority := high) instDeserializeChallenge [c : Codec pSpec U] (i : pSpec.ChallengeIdx) :
    Deserialize (pSpec.Challenge i) (Vector U (verifierMessageSize i)) where
  deserialize := c.decode i

section FromSerialization

open MeasureTheory ProbabilityTheory

-- Finite message alphabets and vectors use the discrete measurable space.
local instance (α : Type) : MeasurableSpace α := ⊤

/-- A `Deserialize.CloseToUniform` decoder is `ε / 2`-close to uniform in total variation.
The class bounds the L1 distance of the point masses, which is twice the total variation; this
is the normalization that CO25's codec bias `ε_cdc` (a total variation bound) needs. -/
private theorem discreteTVDist_uniform_deserialize_le {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] [Deserialize α β]
    [h : Deserialize.CloseToUniform α β] :
    discreteTVDist ($ᵗ α) (Deserialize.deserialize <$> ($ᵗ β)) ≤ (h.ε : ℝ) / 2 := by
  unfold discreteTVDist measureTVDist
  refine (Measure.statDist_eq_half_sum_abs _ _).le.trans
    (div_le_div_of_nonneg_right (le_of_eq_of_le ?_ h.ε_close) zero_le_two)
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample,
    SampleableType.evalDist_uniformSample]

/-- Assemble the codec in **[CO25, Definition 4.1]** from `Serialize` and `Deserialize`
instances and their laws. The deserializer's `CloseToUniform.ε` bounds the L1 distance
of the point masses, so the total-variation bias is `ε / 2`. -/
@[instance_reducible]
noncomputable def mk' {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    (mSize : pSpec.MessageIdx → Nat) (cSize : pSpec.ChallengeIdx → Nat)
    [∀ i, Fintype (Vector U (cSize i))] [∀ i, Nonempty (Vector U (cSize i))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Nonempty (pSpec.Challenge i)]
    [serMsg : ∀ i, Serialize (pSpec.Message i) (Vector U (mSize i))]
    [serMsgInj : ∀ i, Serialize.IsInjective (pSpec.Message i) (Vector U (mSize i))]
    [decVMsg : ∀ i, Deserialize (pSpec.Challenge i) (Vector U (cSize i))]
    [decVMsgUniform : ∀ i, Deserialize.CloseToUniform (pSpec.Challenge i) (Vector U (cSize i))]
    (decVMsgSurj : ∀ i, Function.Surjective ((decVMsg i).deserialize)) :
    Codec pSpec U where
  proverMessageSize := mSize
  verifierMessageSize := cSize
  encode := fun i => (serMsg i).serialize
  encode_injective := fun i => (serMsgInj i).serialize_inj
  decode := fun i => (decVMsg i).deserialize
  decodingBias := fun i => (decVMsgUniform i).ε / 2
  decode_isBiased := fun i => by
    refine (discreteTVDist_uniform_deserialize_le
      (h := decVMsgUniform i)).trans (le_of_eq ?_)
    simp
  decode_surjective := decVMsgSurj

end FromSerialization

end Codec

/-!
## Salt codec ([CO25, §5.4 and §5.8])

The paper distinguishes two views of a single salt:

- **On-sponge view** ([CO25, Construction 4.4]): the salt lives in `Σ^δ` and is absorbed into the
  duplex sponge directly. In Lean this is `Vector U δ`.
- **FS-standard view** ([CO25, Construction 3.17] + §5.8 hybrids `Hyb₃`, `Hyb₄`): the salt is a
  binary string in `{0,1}^{δ★}` (where `δ★ := δ · log₂|Σ|`) used as part of the FS-standard
  oracle key. We model this as an abstract type `Salt`.

The two views are bridged by an injective encoding `bin : Σ^δ → {0,1}^{δ★}` ([CO25, §5.4]:
`τ̌ := bin(τ) ∈ {0,1}^{δ★}`; [CO25, §5.8, `Hyb₃`] states `bin(·)` is injective). The encoding
contributes *no* bias to the §5 error analysis — only the time cost `t_bin = δ · log|Σ|`.

`SaltCodec U δ Salt` packages `bin` and its left inverse. The class is intentionally minimal:
`decode_encode` gives injectivity of `encode` automatically.
-/

/-- **[CO25, §5.4]** Bridge between on-sponge salts (`Σ^δ = Vector U δ`) and the pre-encoded
abstract salt type `Salt` (paper's `{0,1}^{δ★}`). `encode = bin` per [CO25, §5.4]. -/
class SaltCodec (U : Type) (δ : Nat) (Salt : Type) where
  /-- `bin : Σ^δ → {0,1}^{δ★}` — inject `Σ^δ` salt into the FS-standard pre-encoded salt type. -/
  encode : Vector U δ → Salt
  /-- Left inverse of `encode`. Exists because `encode = bin` is injective with a recoverable
    code ([CO25, §5.8, `Hyb₃`]). -/
  decode : Salt → Vector U δ
  /-- `decode ∘ encode = id`. Gives **injectivity** of `encode` (and matches
    [CO25, §5.8, `Hyb₃`]). -/
  decode_encode : ∀ τ, decode (encode τ) = τ

namespace SaltCodec

variable {U : Type} {δ : Nat} {Salt : Type}

/-- Supporting lemma for **[CO25, §5.4]**. `encode` is injective, derived from `decode_encode`.
Matches [CO25, §5.8, `Hyb₃`]. -/
theorem encode_injective [SaltCodec U δ Salt] :
    Function.Injective (encode (U := U) (δ := δ) (Salt := Salt)) := by
  intro a b h
  have := congrArg (decode (U := U) (δ := δ) (Salt := Salt)) h
  rw [decode_encode, decode_encode] at this
  exact this

end SaltCodec

end ProtocolSpec
