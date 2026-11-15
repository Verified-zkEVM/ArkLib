/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Devon Tuma
-/
module

public import ArkLib.Data.Hash.DuplexSponge
public import ArkLib.OracleReduction.FiatShamir.Basic
public import ArkLib.OracleReduction.FiatShamir.Canonical
public import VCVio.OracleComp.Constructions.UniformPreimage
public import ArkLib.Data.Classes.CloseToUniform
public import ArkLib.OracleReduction.Security.OracleSampling
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Duplex Sponge Fiat-Shamir

We define the (multi-round) Fiat-Shamir transformation using duplex sponges.

This file provides:
- one optimized compiler (`duplexSpongeFiatShamir`) parameterized by salt length,
  where one salt `τ ∈ Σ^δ` is sampled per NARG string and absorbed before any rounds.

Length zero is an instance of this same construction. Salt is separate NARG metadata; it does
not extend the application statement, witness, relation, or interactive message types. The
sampler uses only private ambient randomness. Uniformity is required by the ZK experiment.
An empty salt has no encoded symbols and requires no separate wire-format marker.
- Oracle distributions:
  + duplexSpongeHashOracleDistribution: `h`-oracle
  + duplexSpongePermutationOracleDistribution: `(p, p⁻¹)`-oracle
  + D_𝔖.sample / D_𝔖.answer: sample `(h, p)` once, then answer `(h, p, p⁻¹)` queries
  + D_Sigma.sample: for Hyb1
  + D_e.sample: for Hyb2
  + D_IP_salted.sample: single-salt FS random oracle
-/

@[expose] public section

/-- Explicitly distinguish Prover and Verifier queries within a single combined query log.
Used by the §5 Fiat-Shamir games to preserve boundary information after trace-concatenation,
allowing `ksFactKernel` to extract `tr_P` and `tr_V` securely. -/
inductive SourceTag | prover | verifier
  deriving Inhabited, DecidableEq, Repr

/-- A combined query log explicitly tagged with its source. -/
abbrev TaggedQueryLog {ι : Type} (spec : OracleSpec ι) := List (SourceTag × Sigma spec)

namespace TaggedQueryLog

def proverLog {ι : Type} {spec : OracleSpec ι}
    (log : TaggedQueryLog spec) : OracleSpec.QueryLog spec :=
  log.filterMap fun ⟨tag, entry⟩ => if tag = SourceTag.prover then some entry else none

def verifierLog {ι : Type} {spec : OracleSpec ι}
    (log : TaggedQueryLog spec) : OracleSpec.QueryLog spec :=
  log.filterMap fun ⟨tag, entry⟩ => if tag = SourceTag.verifier then some entry else none

def untagged {ι : Type} {spec : OracleSpec ι}
    (log : TaggedQueryLog spec) : OracleSpec.QueryLog spec :=
  log.map Prod.snd

/-- Tagging the prover/verifier logs then concatenating, then projecting the prover side, recovers
the original prover log exactly — regardless of how many entries (incl. `oSpec` queries) each side
made.  This is what makes `ksFactKernel`'s boundary recovery exact (replacing the old `len − k`
suffix split). -/
theorem proverLog_tagAppend {ι : Type} {spec : OracleSpec ι}
    (P V : OracleSpec.QueryLog spec) :
    proverLog (P.map (fun e => (SourceTag.prover, e)) ++ V.map (fun e => (SourceTag.verifier, e)))
      = P := by
  simp [proverLog, List.filterMap_append, List.filterMap_map, Function.comp]

/-- Verifier-side dual of `proverLog_tagAppend`. -/
theorem verifierLog_tagAppend {ι : Type} {spec : OracleSpec ι}
    (P V : OracleSpec.QueryLog spec) :
    verifierLog (P.map (fun e => (SourceTag.prover, e)) ++ V.map (fun e => (SourceTag.verifier, e)))
      = V := by
  simp [verifierLog, List.filterMap_append, List.filterMap_map, Function.comp]

end TaggedQueryLog

/-- Result type for three-valued algorithm outcomes: paper-`err`, paper-`none`, success.

Used for BackTrack (§5.2) and LookAhead (§5.3), which have two distinct failure modes at the type
level. Other Section 5 algorithms (D2SQuery, D2SAlgo, StdTrace, D2STrace) have only binary
abort/success and continue to use `OptionT`. -/
inductive ExperimentOutput.{u} (Out : Type u) : Type u where
  /-- Paper-`err`: e.g., multiple elements in `Outs` (BackTrack) or multiple chains (LookAhead). -/
  | err : ExperimentOutput Out
  /-- Paper-`none`: e.g., zero elements found, empty lookahead family. -/
  | noResult : ExperimentOutput Out
  /-- Success case: unique paper tuple recovered. -/
  | some : Out → ExperimentOutput Out
  deriving Repr

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

/-- **[CO25, Definition 4.1]** Codec class.

`Codec pSpec U` is the generic-parameter carrier for everything DSFS needs about a
protocol's per-round encoder/decoder: per-round vector sizes, the encoder, its injectivity proof,
the decoder, the per-round decoder bias `ε_cdc`, and the per-round preimage sampler.

It extends the `U`-independent size classes `HasProverMessageSize` / `HasVerifierMessageSize`, and
projects to per-index `Serialize` / `Deserialize` / `Serialize.IsInjective` instances via the
projection instances below — so generic alphabet-agnostic infrastructure (CompPoly's
`CompPoly.Data.Classes.Serialize`) remains the single landing zone for hax-extracted Rust trait
impls. Use `Codec.mk'` to assemble a `Codec` from external `Serialize`/`Deserialize` instances
plus the math-side metadata.

Downstream consumers should take a single `[Codec pSpec U]` instance. The projection instances
`instSerializeMessage` / `instSerializeMessageInjective` / `instDeserializeChallenge` (declared
`(priority := high)` below) discharge any incidental `[Serialize ...]` / `[Deserialize ...]`
requirement at use sites with a *named* `(i : ...Idx)`.

For function bodies that need to serialize/deserialize on an *anonymous* `⟨i, hDir⟩` subtype
constructor inside deeply nested elaboration contexts (`Fin.induction` step lambdas, `match`
arms with named hypothesis), Lean's TC search may fail to unify. The fix is to (a) name the
index and (b) bind the projection instance explicitly, then call its method directly:

```
let idx : pSpec.ChallengeIdx := ⟨i, hDir⟩
let inst : Deserialize (pSpec.Challenge idx) (Vector U (verifierMessageSize idx)) :=
  Codec.instDeserializeChallenge idx
let verifierMessage : pSpec.Challenge idx := inst.deserialize raw
```

See `deriveTranscriptDSFSAux` / `Prover.runToRoundDSFS` for the canonical pattern.

We account for this by explicitly tracking **decoding biases**. We say that a codec has bias
`ε_cdc` if, for every `i ∈ [k]`, `ψ_i : Σ^{ℓ_V(i)} → M_{V, i}` is a `ε_{cdc, i}`-biased map
(i.e., it maps the uniform distribution on `Σ^{ℓ_V(i)}` to a distribution that is
`ε_{cdc, i}`-close to the uniform distribution on `M_{V, i}`).
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

/-- Supporting definition for **[CO25, Definition 4.1]**. Hax-pipeline constructor: assemble a
    `Codec` from external `Serialize`/`Deserialize` instances supplied by Rust→hax extraction, plus
    the math-side metadata. `decodingBias` is derived from `[decVMsgUniform]`'s `ε` field:
    `Deserialize.CloseToUniform.ε` bounds the L1 distance of the point masses, which is twice the
    total variation distance, so the TV bias is `ε / 2`
    (`Deserialize.CloseToUniform.discreteTVDist_uniform_deserialize_le`). -/
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
    refine (Deserialize.CloseToUniform.discreteTVDist_uniform_deserialize_le
      (h := decVMsgUniform i)).trans (le_of_eq ?_)
    simp
  decode_surjective := decVMsgSurj

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

/-!
## Block-count notation ([CO25, Equations 7–8])

`L_δ`, `L_P(i)`, `L_V(i)`, `L_P`, `L_V`, `L` from the paper. -/
section BlockCountNotation

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasProverMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (proverMessageSize i))]
    [HasVerifierMessageSize pSpec]
    [∀ i, Deserialize (pSpec.Challenge i) (Vector U (verifierMessageSize i))]

/-- **[CO25, Eq. (7)]** `L_δ = ⌈δ / r⌉`: number of rate blocks needed for a salt of size `δ`. -/
def numSaltBlocks (δ : Nat) : Nat := Nat.ceil ((δ : ℚ) / SpongeSize.R)

/-- **[CO25, Eq. (7)]** Rate-block budget for absorbing the `i`-th encoded
  prover message: `L_P(i) = ⌈ℓ_P(i) / r⌉`, where `r` is the sponge rate. -/
def numPermQueriesProverMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((proverMessageSize i : ℚ) / SpongeSize.R)

alias Lₚᵢ := numPermQueriesProverMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for absorbing encoded
  prover messages: `L_P = ∑ᵢ ⌈ℓ_P(i) / r⌉`. -/
def totalNumPermQueriesProverMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ i

alias Lₚ := totalNumPermQueriesProverMessage

/-- **[CO25, Eq. (7)]** Rate-block budget for squeezing the `i`-th encoded verifier message:
  `L_V(i) = ⌈ℓ_V(i) / r⌉`, where `r` is the sponge rate. -/
def numPermQueriesVerifierMessage (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((verifierMessageSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesVerifierMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for squeezing encoded verifier messages:
  `L_V = ∑ᵢ ⌈ℓ_V(i) / r⌉`. -/
def totalNumPermQueriesVerifierMessage : Nat :=
  ∑ i, pSpec.Lᵥᵢ i

alias Lᵥ := totalNumPermQueriesVerifierMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for absorbing prover messages and squeezing
  verifier messages of the protocol specification. This is `L_P + L_V` in
  the paper's block-count notation and its `L` in Equation (8). The salt-inclusive budget
  used here is `L_totalRateBlocks = L_δ + L_P + L_V`. -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesProverMessage + pSpec.totalNumPermQueriesVerifierMessage

alias L := totalNumPermQueries

end BlockCountNotation

/-- Salt-inclusive upper bound on the verifier's permutation queries in Section 5:
`L_totalRateBlocks = L_δ + L_P + L_V = ⌈δ / r⌉ + L_P + L_V`. This includes salt absorption,
whereas the paper's Equation (8) defines `L = L_P + L_V`, the protocol-only sum
`totalNumPermQueries`. This sum is conservative: the salt and first prover message may share
a rate block. -/
def L_totalRateBlocks {n : ℕ} [SpongeSize] (δ : Nat) (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] : Nat :=
  numSaltBlocks δ + pSpec.totalNumPermQueries

/-- With no salt, the total block budget consists only of protocol message blocks. -/
@[simp] theorem L_totalRateBlocks_zero {n : ℕ} [SpongeSize] (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :
    L_totalRateBlocks 0 pSpec = pSpec.totalNumPermQueries := by
  simp [L_totalRateBlocks, numSaltBlocks]

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasProverMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (proverMessageSize i))]
    [HasVerifierMessageSize pSpec]
    [∀ i, Deserialize (pSpec.Challenge i) (Vector U (verifierMessageSize i))]

section HybridOracles

open OracleReduction

/-- Section 5.8 `Hyb₁` verifier message-oracle surface: encoded prover-prefix queries, encoded
verifier messages.

In the paper's alternating, prover-first schedule [CO25, Eq. (18)],
`dom_i = {0,1}^≤n × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)}` and
`gᵢ : dom_i → Σ^{ℓ_V(i)}`.

More generally, let `mᵢ` count the prover messages strictly before verifier position `i`. Then
`dom_i = StmtIn × Σ^δ × ∏_{j=1}^{mᵢ} Σ^{ℓ_P(j)}`, with `Σ = U`.
Lean represents this product by `pSpec.EncodedProverMessagesBefore U i.1.castSucc`; the empty
product at an initial verifier position is a singleton. The paper's `{0,1}^≤n` is generalized
to `StmtIn` (its instance-size bound is distinct from Lean's schedule length `n`).
Finite component types give a finite query space for the eager uniform function sampler. -/
@[inline, reducible]
def gSpecInterface
    {U : Type} [SpongeUnit U]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :
    ∀ i, OracleInterface (Vector U (verifierMessageSize (pSpec := pSpec) i)) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedProverMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => Vector U (verifierMessageSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def gSpec
    {U : Type} [SpongeUnit U]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [fun i => Vector U (verifierMessageSize (pSpec := pSpec) i)]ₒ'
    (gSpecInterface (U := U) StmtIn pSpec δ)

/-- Section 5.8 `Hyb₂` verifier message-oracle surface: encoded prover-prefix queries, decoded
verifier messages.

As in [CO25, Eq. (55)], `eᵢ : dom_i → ℳ_{V,i}`, where
`dom_i = StmtIn × Σ^δ × ∏_{j=1}^{mᵢ} Σ^{ℓ_P(j)}` and `mᵢ` counts preceding prover messages.
The domain is the same as `gSpecInterface`; the answer is a decoded verifier message
(`pSpec.Challenge i`) rather than an element of `Σ^{ℓ_V(i)}`. -/
@[inline, reducible]
def eSpecInterface
    {U : Type} [SpongeUnit U]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : Nat) [HasProverMessageSize pSpec] :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedProverMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def eSpec
    {U : Type} [SpongeUnit U]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) (δ : Nat) [HasProverMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (eSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [pSpec.Challenge]ₒ'
    (eSpecInterface (U := U) StmtIn pSpec δ)

/-- **[CO25, Eq. (18)]** Eager full-table distribution `𝒟_Σ` (symbol `g`) over the encoded
verifier message-oracle family for `Hyb₁`.

Samples a single full random table `g : (q : Domain) → Range q` once at game start; all subsequent
queries deterministically index into this fixed table. The `[SampleableType (QueryImpl _ Id)]`
hypothesis matches CO25: with a fixed-length round-indexed prefix (see
`EncodedProverMessagesBefore`), the oracle's domain is finite, and uniform sampling of the function
table is the canonical realization of `g ← 𝒰((dom_i → Σ^{ℓ_V(i)})_{i∈[k]})`. -/
def D_Sigma.sample
    {U : Type} [SpongeUnit U]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec]
    [instSampleable : SampleableType (QueryImpl (gSpec (U := U) StmtIn pSpec δ) Id)] :
    ProbComp (QueryImpl (gSpec (U := U) StmtIn pSpec δ) Id) :=
  OracleReduction.sampleRandomOracleTable (instSampleable := instSampleable)

/-- Uniform full-table sampling for `gSpec` (Hyb₁'s `g`), derived from finite nonempty
statement and alphabet types. Each round has domain
`StmtIn × U^δ × ∏_{j < i, P→V} U^{ℓ_P(j)}` and range `U^{ℓ_V(i)}`.
These hypotheses suffice for finite table sampling; they are not claimed necessary in
degenerate cases such as an empty round family or singleton answer spaces. -/
noncomputable instance instSampleableTypeEncodedVerifierMessageOracle
    {U : Type} [SpongeUnit U] {n : ℕ} {StmtIn : Type} {pSpec : ProtocolSpec n} {δ : Nat}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :
    SampleableType (QueryImpl (gSpec (U := U) StmtIn pSpec δ) Id) := by
  -- The `gSpec` domain is definitionally the sigma of a verifier message index and its query type;
  -- state the `Fintype`/`DecidableEq` instances on the unfolded form (default-transparency
  -- unification sees through `toOracleSpec`, which is not reducible for TC search).
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    (inferInstance : Fintype ((i : pSpec.ChallengeIdx) ×
      (StmtIn × Vector U δ × pSpec.EncodedProverMessagesBefore U i.1.castSucc)))
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    (inferInstance : DecidableEq ((i : pSpec.ChallengeIdx) ×
      (StmtIn × Vector U δ × pSpec.EncodedProverMessagesBefore U i.1.castSucc)))
  letI : ∀ q : (gSpec (U := U) StmtIn pSpec δ).Domain,
      Fintype ((gSpec (U := U) StmtIn pSpec δ).Range q) := fun q =>
    (inferInstance : Fintype (Vector U (verifierMessageSize (pSpec := pSpec) q.1)))
  letI : Fintype (QueryImpl (gSpec (U := U) StmtIn pSpec δ) Id) :=
    show Fintype ((q : (gSpec (U := U) StmtIn pSpec δ).Domain) →
      (gSpec (U := U) StmtIn pSpec δ).Range q) from inferInstance
  -- Every encoded answer type is inhabited (`U` has a default element).
  letI : Nonempty (QueryImpl (gSpec (U := U) StmtIn pSpec δ) Id) :=
    ⟨fun q => (default : Vector U (verifierMessageSize (pSpec := pSpec) q.1))⟩
  apply SampleableType.ofFintype

/-- **[CO25, Eq. (55)]** Eager full-table distribution `e` over the decoded verifier message-oracle
family for `Hyb₂`.

Same eager full-table semantics as `D_Sigma.sample`, with the
answer type swapped from `Σ^{ℓ_V(i)}` to the decoded `pSpec.Challenge i`. Realizes
`e ← 𝒰((dom_i → ℳ_{V,i})_{i∈[k]})`. -/
def D_e.sample
    {U : Type} [SpongeUnit U]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasProverMessageSize pSpec]
    [instSampleable : SampleableType (QueryImpl (eSpec (U := U) StmtIn pSpec δ) Id)] :
    ProbComp (QueryImpl (eSpec (U := U) StmtIn pSpec δ) Id) :=
    OracleReduction.sampleRandomOracleTable (instSampleable := instSampleable)

/-! ## Setup: oracle distributions and `SampleableType` bridges -/

/-- **[CO25, Eq. (57)]** Eager full-table distribution `𝒟_IP` (symbol `f`, salted) over the
salted Fiat–Shamir verifier message oracle for `Hyb₃` and `Hyb₄`.

Samples a single full random table `f : (q : Domain) → Range q` once at game start over the
salted domain `dom'_i = StmtIn × Salt × ∏_{j=1}^{mᵢ} ℳ_{P,j}`, with range `ℳ_{V,i}`.
Here `mᵢ` counts prover messages preceding verifier position `i`. In the paper's alternating,
prover-first schedule this specializes to
`dom'_i = {0,1}^≤n × {0,1}^{δ⋆} × ℳ_{P,1} × … × ℳ_{P,i}`.
Per [CO25, §5.8, `Hyb₄`], Hyb₃ and Hyb₄ both sample from this same distribution; the difference
between hybrids lies in the prover/verifier algorithm, not the oracle.

The salt slot of `dom'_i` is the pre-encoded `{0,1}^{δ⋆}`-side, modeled here by the abstract
type `Salt`. The on-sponge `Σ^δ` salt produced by Construction 4.4 is projected via
`SaltCodec.encode = bin` before being used as an oracle key. -/
noncomputable def D_IP_salted.sample
    {n : ℕ} {StmtIn Salt : Type} (pSpec : ProtocolSpec n)
    [VCVCompatible StmtIn] [VCVCompatible Salt]
    [∀ i, VCVCompatible (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ProbComp (QueryImpl (fsChallengeOracle (StmtIn × Salt) pSpec) Id) :=
  OracleReduction.sampleFiatShamirChallengeTable (Statement := StmtIn × Salt) pSpec

/-- Bridge: `SampleableType` for `eSpec` (Hyb₂ `e`) derived from
granular `VCVCompatible` base-type hypotheses. Eliminates verbose table-sampling hypotheses
at call sites in §5.8 hybrids. -/
noncomputable instance instSampleableTypeDecodedVerifierMessageOracle
    {U : Type} [SpongeUnit U] {n : ℕ} {StmtIn : Type} {pSpec : ProtocolSpec n} {δ : Nat}
    [VCVCompatible StmtIn] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [HasProverMessageSize pSpec] :
    SampleableType (QueryImpl (eSpec (U := U) StmtIn pSpec δ) Id) := by
  -- Same recipe as `instSampleableTypeEncodedVerifierMessageOracle`; only the answer type differs
  -- (decoded `pSpec.Challenge i` instead of encoded `Vector U (verifierMessageSize i)`).
  letI : Fintype (eSpec (U := U) StmtIn pSpec δ).Domain :=
    (inferInstance : Fintype ((i : pSpec.ChallengeIdx) ×
      (StmtIn × Vector U δ × pSpec.EncodedProverMessagesBefore U i.1.castSucc)))
  letI : DecidableEq (eSpec (U := U) StmtIn pSpec δ).Domain :=
    (inferInstance : DecidableEq ((i : pSpec.ChallengeIdx) ×
      (StmtIn × Vector U δ × pSpec.EncodedProverMessagesBefore U i.1.castSucc)))
  letI : ∀ q : (eSpec (U := U) StmtIn pSpec δ).Domain,
      Fintype ((eSpec (U := U) StmtIn pSpec δ).Range q) := fun q =>
    (inferInstance : Fintype (pSpec.Challenge q.1))
  letI : Fintype (QueryImpl (eSpec (U := U) StmtIn pSpec δ) Id) :=
    show Fintype ((q : (eSpec (U := U) StmtIn pSpec δ).Domain) →
      (eSpec (U := U) StmtIn pSpec δ).Range q) from inferInstance
  -- Every decoded answer type is inhabited via `VCVCompatible (pSpec.Challenge i)`.
  letI : Nonempty (QueryImpl (eSpec (U := U) StmtIn pSpec δ) Id) :=
    ⟨fun q => (default : pSpec.Challenge q.1)⟩
  apply SampleableType.ofFintype

end HybridOracles

end ProtocolSpec

namespace OracleSpec

/-- **[CO25, Definition 4.3]** The oracle specification for duplex sponge Fiat-Shamir
(Definition 4.3); its distribution is the paper's `𝒟_𝔖` (`D_𝔖`). The index consists of
`(h, p, p⁻¹)`, where:
- `h : ByteArray → Vector U SpongeSize.C`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the forward direction of the random permutation
- `p⁻¹ : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the backward direction of the random permutation
-/
@[reducible]
def duplexSpongeOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U SpongeSize.C) + permutationOracle (CanonicalSpongeState U)

/-- **[CO25, Definition 5.2]** The type of a single entry in a duplex sponge query trace -/
abbrev duplexSpongeTraceEntry {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize] :=
  Sigma (α := StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U)
    (β := duplexSpongeOracle StartType U)

/-! ### Smart constructors for the three `(h, p, p⁻¹)` `𝒟_𝔖` query flavors

[CO25, §5.4] notation `('h', 𝕩, …)` / `('p', s_in, …)` / `('p⁻¹', s_out, …)` corresponds
to three nested-`Sum` injections into

  `(duplexSpongeOracle StartType U).Domain
     = StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U`.

The wrappers below tag each injection with the paper query name, so trace constructions
(`⟨dsHashQuery 𝕩, capOut⟩`, `⟨dsPermInvQuery s_out, s_in⟩`) and pattern matches read directly
as paper notation rather than as nested-`Sum.inl/.inr` chains. `@[match_pattern]` keeps them
usable as match patterns; `@[reducible]` lets the elaborator unfold them where the bare
`Sum`-form is expected. -/

/-- **[CO25, §5.4]** Paper `h(𝕩)` — hash query index. -/
@[match_pattern, reducible]
def dsHashQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stmt : StartType) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inl stmt

/-- **[CO25, §5.4]** Paper `p(s_in)` — permutation query index. -/
@[match_pattern, reducible]
def dsPermQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateIn : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inl stateIn)

/-- **[CO25, §5.4]** Paper `p⁻¹(s_out)` — inverse permutation query index. -/
@[match_pattern, reducible]
def dsPermInvQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateOut : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inr stateOut)

/-- **[CO25, Definition 4.3]** Forward-only sub-spec of `duplexSpongeOracle`: only `h` and
the permutation slot `p` are exposed. The backward slot `p⁻¹` is omitted.

This is the type-level encoding of [CO25, Figure 4, line 3] — `𝒱^{h,p}` — the honest verifier in
the DSFS hybrid experiment has no syntactic access to `p⁻¹`. Used as the typing surface of the
verify helpers (`deriveTranscriptDSFS{,Salted}`) and a parallel narrow-typed verifier surface
`Verifier.duplexSpongeFiatShamirForward`. The wide reduction surface
`Reduction.duplexSpongeFiatShamir{,Salted}` keeps the full `duplexSpongeOracle` because
`NonInteractiveReduction` requires uniform spec across prover and verifier.
-/
@[reducible]
def duplexSpongeForwardOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U SpongeSize.C) + forwardPermutationOracle (CanonicalSpongeState U)

section OracleDistribution

/-- One sampled realization of the DSFS ideal oracle distribution `𝒟_𝔖`:
a random function `h : StartType → Σ^c` and a random permutation `p : Σ^{r+c} → Σ^{r+c}`.
The inverse oracle `p⁻¹` is *derived* as `p.symm`, not sampled — the bijection invariant
`p ∘ p⁻¹ = id` holds by construction since the carrier is `Equiv.Perm`. -/
abbrev DuplexSpongeOracleFamily (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :=
  (QueryImpl (StartType →ₒ Vector U SpongeSize.C) Id) ×
    Equiv.Perm (CanonicalSpongeState U)

/-- **[CO25, Definition 4.3]** Interpret one sampled `𝒟_𝔖` realization as the concrete `(h, p, p⁻¹)`
query implementation. -/
@[reducible]
def duplexSpongeOracleQueryImpl
    {StartType U : Type} [SpongeUnit U] [SpongeSize]
    (realization : DuplexSpongeOracleFamily StartType U) :
    QueryImpl (duplexSpongeOracle StartType U) ProbComp
  | Sum.inl qHash => pure (realization.1 qHash)
  | Sum.inr (Sum.inl state) => pure (realization.2 state)
  | Sum.inr (Sum.inr state) => pure (realization.2.symm state)

/-- **[CO25, Definition 4.3]** Answer using the initially sampled pair `(h, p) ← 𝒟_𝔖` throughout the
experiment. Hash queries use `h`, forward queries use `p`, and inverse queries use `p.symm`. The
pair is read but never modified: this handler does not sample a new oracle. -/
def D_𝔖.answer {StartType U : Type} [SpongeUnit U] [SpongeSize] :
    QueryImpl (duplexSpongeOracle StartType U)
      (StateT (DuplexSpongeOracleFamily StartType U) ProbComp) := fun q => do
  let realization ← get
  StateT.lift (duplexSpongeOracleQueryImpl realization q)

/-- **[CO25, Construction 4.4]** Oracle implementation with stateless ambient queries.
The sampled sponge realization is shared and unchanged throughout the execution. -/
def D_𝔖.withOracle {ι : Type} {oSpec : OracleSpec ι} {StartType U : Type}
    [SpongeUnit U] [SpongeSize] (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + duplexSpongeOracle StartType U)
      (StateT (DuplexSpongeOracleFamily StartType U) ProbComp) := fun q =>
  match q with
  | .inl q => do
    let response ← StateT.lift (oSpecImpl q)
    pure response
  | .inr q => D_𝔖.answer q

/-- **[CO25, Definition 4.3]** Fixed-oracle contract: every query returns the prescribed
deterministic answer together with the unchanged realization. In particular there is no per-query
resampling or failure. This equation applies to every realization, irrespective of the distribution
used to sample it. -/
@[simp]
theorem D_𝔖.answer_run {StartType U : Type} [SpongeUnit U] [SpongeSize]
    (realization : DuplexSpongeOracleFamily StartType U)
    (q : (duplexSpongeOracle StartType U).Domain) :
    (D_𝔖.answer q).run realization =
      match q with
      | Sum.inl x => pure (realization.1 x, realization)
      | Sum.inr (Sum.inl s) => pure (realization.2 s, realization)
      | Sum.inr (Sum.inr s) => pure (realization.2.symm s, realization) := by
  rcases q with x | s | s <;>
    simp [D_𝔖.answer, duplexSpongeOracleQueryImpl]

/-- `CanonicalSpongeState U = Vector U SpongeSize.N` is `VCVCompatible` whenever `U` is.
Needed so `VCVCompatible U` implies `SampleableType (Equiv.Perm (CanonicalSpongeState U))`. -/
instance instVCVCompatibleCanonicalSpongeState
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] :
    VCVCompatible (CanonicalSpongeState U) :=
  (inferInstance : VCVCompatible (Vector U SpongeSize.N))

/-- **[CO25, Definition 4.3]** Uniform random-function distribution for the `h` component of
`𝒟_𝔖`. -/
noncomputable def duplexSpongeHashOracleDistribution (StartType U : Type) [SpongeUnit U]
    [SpongeSize] [VCVCompatible StartType] [VCVCompatible U] :
    (ProbComp (QueryImpl (StartType →ₒ Vector U SpongeSize.C) Id)) :=
  OracleReduction.sampleRandomOracleTable (instSampleable := OracleReduction.sampleableTypePiVCV)

/-- **[CO25, Definition 4.3]** Uniform random-permutation distribution for the `(p, p⁻¹)` component
of `𝒟_𝔖`.

Only `p` is sampled; `p⁻¹` is derived as `p.symm`. -/
noncomputable def duplexSpongePermutationOracleDistribution (U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible U] :
    ProbComp (Equiv.Perm (CanonicalSpongeState U)) :=
  uniformSample _ (h := VCVCompatible.toSampleableTypePerm)

/-- **[CO25, Definition 4.3]** Ideal duplex-sponge oracle distribution `𝒟_𝔖`.

Samples `h` as a uniform random function and `p` as a uniform random permutation, then answers
inverse-permutation queries using `p.symm`. -/
noncomputable def D_𝔖.sample (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U] :
    ProbComp (DuplexSpongeOracleFamily StartType U) := do
  let h ← duplexSpongeHashOracleDistribution StartType U
  let p ← duplexSpongePermutationOracleDistribution U
  pure (h, p)

/-- Supporting lemma for **[CO25, Definition 4.3]**: `D_𝔖.sample` samples `h` and `p` uniformly. -/
@[simp]
lemma D_𝔖.sample_eq
    (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U] :
    (D_𝔖.sample StartType U) =
      (do
        let h ← uniformSample _ (h := OracleReduction.sampleableTypePiVCV)
        let p ← uniformSample _ (h := VCVCompatible.toSampleableTypePerm)
        pure (h, p)) := rfl

end OracleDistribution

end OracleSpec

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [Codec pSpec U]

/-! ## Salted interfaces

Salt sampling, NARG strings, and the prover/verifier types used by the salted security games.
The unsalted NARG string is simply `pSpec.Messages`.
-/

section SaltedInterfaces

/-- Public DSFS NARG strings are bytes, parsed by a canonical byte serializer. -/
abbrev DSFSNARGString := ByteArray

/-- Salt and typed prover messages before canonical byte serialization. -/
abbrev DSFSTypedNARGString (pSpec : ProtocolSpec n) (U : Type) (δ : Nat) :=
  FiatShamirNARGString pSpec U δ

/-- **[CO25, Lemma 5.1]** Paper-faithful type of the malicious DSFS prover `𝒫̃`
(`\tilde{\mathcal{P}}`), per [CO25, §5.4, `D2SAlgo` Step 4]: *"Let `𝒜`'s output be
`(x, π_𝒜)`, and parse `π_𝒜` as `(τ, α_1, ..., α_k)`"*.

`𝒫̃` queries `(h, p, p⁻¹) = duplexSpongeOracle` plus an ambient `oSpec` (for oracle-IP
generalization; `oSpec = []ₒ` recovers the paper's pure-IP case), and outputs a salted NARG string
`(x, (τ, messages))` with on-sponge salt `τ : Vector U δ`.

Used uniformly in §5.4 (`D2SAlgo` input), §5.8 hybrids `Hyb_0 .. Hyb_4`, and Lemma 5.1. -/
abbrev MaliciousProver {n : ℕ} {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (StmtIn U : Type) [SpongeUnit U] (δ : ℕ) :=
  OracleComp (oSpec + duplexSpongeOracle StmtIn U)
    (StmtIn × DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)

end SaltedInterfaces

/-! ## Shared transcript reconstruction -/

namespace ProtocolSpec.Messages

/-- **[CO25, Construction 4.4]** Auxiliary function for deriving the transcript up to round `k` from
  the (full) prover messages, via querying the permutation oracle for the verifier messages.

  This is used to define `deriveTranscriptDSFS`. The body uses only permutation queries
  (`squeeze`, `absorb`); the return type is the narrow `duplexSpongeForwardOracle`, encoding
  [CO25, Figure 4, line 3] (`𝒱^{h,p}`) at the type level. -/
def deriveTranscriptDSFSAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (i : Fin (n + 1)) :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
        (CanonicalDuplexSponge U × pSpec.Transcript i) :=
  Fin.induction
    (pure (sponge, fun i => i.elim0))
    (fun i ih => do
      let ⟨curSponge, prevTranscript⟩ ← ih
      match hDir : pSpec.dir i with
      | .V_to_P =>
        let idx : pSpec.ChallengeIdx := ⟨i, hDir⟩
        let inst : Deserialize (pSpec.Challenge idx) (Vector U (verifierMessageSize idx)) :=
          Codec.instDeserializeChallenge idx
        let ⟨verifierMessage, newSponge⟩ ← liftM (curSponge.squeeze (verifierMessageSize idx))
        let decodedVerifierMessage : pSpec.Challenge idx :=
          inst.deserialize verifierMessage
        return (newSponge, prevTranscript.concat decodedVerifierMessage)
      | .P_to_V =>
        let idx : pSpec.MessageIdx := ⟨i, hDir⟩
        let inst : Serialize (pSpec.Message idx) (Vector U (proverMessageSize idx)) :=
          Codec.instSerializeMessage idx
        let serializedMessage : Vector U (proverMessageSize idx) :=
          inst.serialize (messages idx)
        let newSponge ← liftM (DuplexSponge.absorb curSponge serializedMessage.toList)
        return (newSponge, prevTranscript.concat (messages idx)))
    i

end ProtocolSpec.Messages
section Execution

/-- Route honest sponge operations to the permutation, whose query signature is
identical to the inverse permutation's signature. -/
@[reducible]
def dsfsForwardPermutationLift : MonadLiftT
    (OracleQuery (forwardPermutationOracle (CanonicalSpongeState U)))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query := ⟨Sum.inr (Sum.inr (Sum.inl query.input)), query.cont⟩

namespace DuplexSpongeFS

/-- Infer honest sponge computation lifts to the forward slot, avoiding the identically typed
inverse slot. Enable locally with `open scoped DuplexSpongeFS`. -/
@[reducible] scoped instance forwardPermutationQueryLift : MonadLift
    (OracleQuery (forwardPermutationOracle (CanonicalSpongeState U)))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query := dsfsForwardPermutationLift.monadLift query

end DuplexSpongeFS

open scoped DuplexSpongeFS

/-- Pinned narrow→wide lift for whole `𝒱^{h,p}` computations: embeds
`oSpec + duplexSpongeForwardOracle` into `oSpec + duplexSpongeOracle`, sending
- ambient queries to the ambient slot (`.inl i ↦ .inl i`),
- hash queries to the hash slot (`.inr (.inl 𝕩) ↦ .inr (.inl 𝕩)`),
- permutation queries to the forward slot `p` (`.inr (.inr s) ↦ .inr (.inr (.inl s))`).

The generic narrow-to-wide lift routes permutation queries to the forward slot, so
verifier computations use inferred lifting. This pinned lift remains available for explicit
routing statements; `liftComp_dsfsForwardToFullLift` rewrites it away. -/
@[reducible]
def dsfsForwardToFullLift : MonadLiftT
    (OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query :=
    match query with
    | ⟨Sum.inl i, cont⟩ => ⟨Sum.inl i, cont⟩
    | ⟨Sum.inr (Sum.inl stmt), cont⟩ => ⟨Sum.inr (Sum.inl stmt), cont⟩
    | ⟨Sum.inr (Sum.inr stateIn), cont⟩ => ⟨Sum.inr (Sum.inr (Sum.inl stateIn)), cont⟩

omit [VCVCompatible StmtIn] in
/-- The pinned narrow→wide lift agrees with the generic `liftComp`: both send every
permutation query to the forward slot `p`. -/
theorem liftComp_dsfsForwardToFullLift {α : Type}
    (oa : OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) α) :
    liftComp oa (oSpec + duplexSpongeOracle StmtIn U) (h := dsfsForwardToFullLift) =
      liftComp oa (oSpec + duplexSpongeOracle StmtIn U) :=
  liftComp_inst_irrel (fun t => by rcases t with t | t | t <;> rfl) oa

/-! ## Shared proof execution

The canonical prover absorbs prover messages immediately when a later verifier message can affect a
subsequent prover message, and stops immediately after the last prover message. The runner takes
an initialized sponge; it neither samples nor requires a salt.
-/

section SharedProofExecution

namespace DuplexSpongeFS

/-- Absorb a prover message only if a later verifier message precedes another prover message. -/
def needsNARGAbsorption (pSpec : ProtocolSpec n) (j : Fin n) : Prop :=
  ∃ k : Fin n, j < k ∧ pSpec.dir k = .V_to_P ∧
    ∃ l : pSpec.MessageIdx, k < l.1

instance (pSpec : ProtocolSpec n) (j : Fin n) :
    Decidable (needsNARGAbsorption pSpec j) :=
  inferInstanceAs (Decidable (∃ k : Fin n, j < k ∧ pSpec.dir k = .V_to_P ∧
    ∃ l : pSpec.MessageIdx, k < l.1))

end DuplexSpongeFS

open DuplexSpongeFS in
/-- Execute one step of the prefix needed to produce the NARG string. Absorption is immediate
and occurs only when a later verifier message can affect a subsequent prover message. -/
def Prover.processRoundDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec) (j : Fin n)
    (previousRound : OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc × CanonicalDuplexSponge U × P.PrvState j.castSucc)) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.succ × CanonicalDuplexSponge U × P.PrvState j.succ) := do
  let (messages, sponge, prvState) ← previousRound
  match hd : pSpec.dir j with
  | .P_to_V => do
    let (message, nextPrvState) ← P.sendMessage ⟨j, hd⟩ prvState
    let sponge ← if needsNARGAbsorption pSpec j then do
        sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize message).toList
      else pure sponge
    return (messages.concat hd message, sponge, nextPrvState)
  | .V_to_P => do
    let receiveChallenge ← P.receiveChallenge ⟨j, hd⟩ prvState
    let (verifierMessage, sponge) ← sponge.squeeze (verifierMessageSize ⟨j, hd⟩)
    return (messages.extend hd, sponge,
      receiveChallenge ((Codec.instDeserializeChallenge ⟨j, hd⟩).deserialize verifierMessage))

/-- Execute a prover prefix in increasing round order, starting from an initialized sponge.
The prefix must end at or before the last prover message. Beyond that point, the optimized
sponge state can omit absorbed messages needed to reconstruct the verifier's transcript. -/
def Prover.runToRoundDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (i : Fin (n + 1)) (_hi : i ≤ proverMessageEnd pSpec)
    (sponge : CanonicalDuplexSponge U) (initialPrvState : P.PrvState 0) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo i × CanonicalDuplexSponge U × P.PrvState i) :=
  Fin.induction
    (zero := pure (default, sponge, initialPrvState))
    (succ := P.processRoundDSFS) i

/-- Generate all NARG messages from an initialized sponge. The stopping boundary and
conversion from a complete prefix are internal; no terminal verifier steps are executed. -/
def Prover.runDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (sponge : CanonicalDuplexSponge U) (initialPrvState : P.PrvState 0) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) pSpec.Messages := do
  let (messages, _sponge, _lastPrvState) ←
    P.runToRoundDSFS (proverMessageEnd pSpec) le_rfl sponge initialPrvState
  pure (MessagesUpTo.completeMessages (i := proverMessageEnd pSpec) messages
    (message_lt_proverMessageEnd pSpec))

end SharedProofExecution

/-! ## Salted construction

The prover initializes the sponge, samples and absorbs the salt, then runs the shared prefix.
The NARG string contains the salt and prover messages; the verifier reconstructs the full
transcript.
-/

section SaltedConstruction

/-- **[CO25, Construction 4.4]** Derive the full transcript from prover messages after explicitly
absorbing a public salt `τ`.

This is the transcript path for the salted Construction 4.4 surface.
-/
def ProtocolSpec.Messages.deriveTranscriptDSFS {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {δ : Nat}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge0 ← liftM (DuplexSponge.start stmtIn)
  let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
  ProtocolSpec.Messages.deriveTranscriptDSFSAux (pSpec := pSpec) (oSpec := oSpec) (U := U)
    sponge messages (Fin.last n)

/-- **[CO25, Construction 4.4]** Salted DSFS verifier surface (Construction 4.4-facing, wide-spec).

Wide-spec wrapper around the forward-only helper `deriveTranscriptDSFS`. Kept at the wide
`oSpec + duplexSpongeOracle StmtIn U` for compatibility with
`Reduction.duplexSpongeFiatShamir`. For the strict `𝒱^{h,p}` typing used inside §5.8
security games, see `Verifier.duplexSpongeFiatShamirForward`. -/
def Verifier.duplexSpongeFiatShamir (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn nargString => do
    let saltedNARGString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ := nargString 0
    let salt : Vector U δ := saltedNARGString.1
    let messages : pSpec.Messages := saltedNARGString.2
    let ⟨_, transcript⟩ ←
      messages.deriveTranscriptDSFS
        (pSpec := pSpec) (oSpec := oSpec) (U := U) stmtIn salt
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- **[CO25, Construction 4.4]** Narrow-typed salted DSFS verifier surface — [CO25, Figure 4,
line 3] (`𝒱^{h,p}`) for the salted Construction 4.4 path.

Lives at `oSpec + duplexSpongeForwardOracle StmtIn U`, omitting the inverse permutation slot
`p⁻¹` at the type level. Used by the §5.8 hybrid security games to invoke the honest verifier
without granting it syntactic access to `p⁻¹`. -/
def Verifier.duplexSpongeFiatShamirForward (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeForwardOracle StmtIn U) StmtIn StmtOut where
  verify := fun stmtIn nargString => do
    let saltedNARGString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ := nargString 0
    let salt : Vector U δ := saltedNARGString.1
    let messages : pSpec.Messages := saltedNARGString.2
    let ⟨_, transcript⟩ ←
      messages.deriveTranscriptDSFS
        (pSpec := pSpec) (oSpec := oSpec) (U := U) stmtIn salt
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- **[CO25, Construction 4.4]** — Argument prover for an interactive proof. The final output is an
accepting claim; only the verifier decides whether the NARG string is accepted. -/
def Prover.duplexSpongeFiatShamir (δ : ℕ)
    (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveProver (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U) StmtIn WitIn Bool Unit where
  PrvState
    | 0 => StmtIn × P.PrvState 0
    | 1 => Unit
  input := fun ctx => (ctx.1, P.input ctx)
  sendMessage
    | ⟨0, _⟩ => fun (stmt, initialPrvState) => do
      let initialSponge : CanonicalDuplexSponge U ← liftM (DuplexSponge.start stmt)
      let salt ← sampleSalt
      let sponge ← initialSponge.absorb salt.toList
      let messages ← P.runDSFS sponge initialPrvState
      pure ((salt, messages), ())
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun _lastPrvState => pure (true, ())

/-- **[CO25, Construction 4.4]** — Salted duplex-sponge transformation of an interactive proof.
The prover omits terminal work; the verifier reconstructs the full transcript. -/
def Reduction.duplexSpongeFiatShamir (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveReduction (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U) StmtIn WitIn Bool Unit where
  prover := P.prover.duplexSpongeFiatShamir δ sampleSalt
  verifier := P.verifier.duplexSpongeFiatShamir δ

namespace DuplexSpongeFS

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Changing the honest prover's stopping behavior does not change the compiled verifier.
The existing stateless soundness and knowledge-soundness theorems therefore apply to this
verifier directly, with the accepting output language `{true}`. -/
@[simp] theorem salted_proof_verifier_eq (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).verifier =
      P.verifier.duplexSpongeFiatShamir δ := rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The compiled prover claims acceptance independently of its terminal private state. -/
@[simp] theorem salted_proof_prover_output (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (lastPrvState : (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).prover.PrvState
      (Fin.last 1)) :
    (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).prover.output lastPrvState =
      pure (true, ()) := rfl

end DuplexSpongeFS

/-- **[CO25, Construction 4.4]** Run the narrow-spec salted forward verifier `𝒱^{h,p}`
(`V.duplexSpongeFiatShamirForward δ`) on
`(stmtIn, nargString : DSFSTypedNARGString pSpec U δ)`, then `liftComp` the resulting computation
up to the wide spec `oSpec + duplexSpongeOracle StmtIn U`.

Shared by:
- `dsfsGame` / `hybridGame` (KeyLemma.lean — `Hyb_0` through `Hyb_3` skeleton);
- `abortableTraceDist` (BadEvents.lean — §5.6).

Encodes [CO25, Figure 4, line 3] at the type level: the narrow input spec
`oSpec + duplexSpongeForwardOracle StmtIn U` exposes only `(h, p)`, while the wide output spec
`oSpec + duplexSpongeOracle StmtIn U` exposes `(h, p, p⁻¹)`. Because the body is just
`liftComp`-ed from the narrow surface, no `p⁻¹` query ever appears in the resulting query log. -/
def runForwardVerifierWide (δ : Nat) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) (Option StmtOut) :=
  let verifyCompNarrow :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((V.duplexSpongeFiatShamirForward δ).run stmtIn
      (fun i => match i with | ⟨0, _⟩ => nargString)).run
  liftComp verifyCompNarrow (oSpec + duplexSpongeOracle StmtIn U)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The canonical salted verifier executes the forward-only Section 5 verifier,
after widening its oracle interface. -/
theorem Verifier.duplexSpongeFiatShamir_verify (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmt : StmtIn)
    (tr : FullTranscript ⟨!v[.P_to_V], !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩) :
    (V.duplexSpongeFiatShamir δ).verify stmt tr =
      OptionT.mk (runForwardVerifierWide δ V stmt (tr 0)) := by
  symm
  unfold Verifier.duplexSpongeFiatShamir
  apply OptionT.ext
  simp only [runForwardVerifierWide, Verifier.duplexSpongeFiatShamirForward,
    Verifier.run, liftComp_bind, ← monadLift_liftM_OptionT,
    OptionT.run_monadLift, monadLift_self, bind_map_left, Option.elimM, Option.elim_some,
    OptionT.run_bind]
  apply bind_congr
  intro t
  simp only [← liftComp_eq_liftM]
  induction (V.verify stmt t.2).run using OracleComp.inductionOn with
  | pure x => cases x <;> simp [Option.getM]
  | query_bind q k ih =>
    simp only [liftComp_bind]
    simp only [bind_assoc]
    congr 1
    exact funext ih

end SaltedConstruction

end Execution

/-! ### Section 5 Transforms and Monads -/

/-- `OracleComp σ` paired with a paper-faithful abort layer (`OptionT`).

`OracleComp σ` queries `σ`; `OptionT` adds `none = abort` ([CO25, §5] `err` outcome). Section 5
procedures (`D2SQuery`, `LookAhead`, `BackTrack`, `StdTrace`, `D2STrace`) all live in this stack
with various choices of `σ`. -/
abbrev AbortComp {ι : Type} (σ : OracleSpec ι) := OptionT (OracleComp σ)

/-- Shared abort/randomness monad stack used by Section 5 algorithms.

`OptionT` provides paper-binary `abort`/`success`; the inner `OracleComp (Unit →ₒ U)` provides the
fresh `𝒰(Σ)` sampling oracle used by `D2SQuery`/`D2SAlgo`/`StdTrace`/`D2STrace`/`LookAhead`.

This is `AbortComp (Unit →ₒ U)` — specialized to the uniform-`U` sampling oracle. -/
abbrev UnitSampleM (U : Type) [SpongeUnit U] := AbortComp (Unit →ₒ U)

section TransformTypes

variable {ι : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn : Type} {U : Type} [SpongeUnit U]
  {δ : Nat}
  [codec : Codec pSpec U]

/-- **[CO25, §5.4]** External verifier message-oracle family augmented with the auxiliary sampling
oracles.

`D2SVerifierMessagePlusUnitOracle verifierMessageSpec` is
`verifierMessageSpec + (Unit →ₒ U) + unifSpec`:
the sum of the caller-supplied verifier message oracle `gᵢ`-family, the auxiliary unit-sampling
oracle `𝒰(Σ)` used by D2SQuery fresh-sample branches (§5.4 Items 2(b), 3(b), 4(c)iii, 4(e)iiiC),
and `unifSpec` for any additional uniform randomness. -/
abbrev D2SVerifierMessagePlusUnitOracle {κ : Type} (verifierMessageSpec : OracleSpec κ) :=
  verifierMessageSpec + ((Unit →ₒ U) + unifSpec)

/-- **[CO25, Eq. (19)]** Shorthand for the recurring `gᵢ`-realization shape: a `QueryImpl`
from the `gSpec` source into `StateT M (OptionT (OracleComp …))` over the basic-FS-style
outer spec `D2SVerifierMessagePlusUnitOracle verifierMessageSpec`.

Polymorphic over:
- inner state `M` — paper §5.4 D2SAlgo Item 3's `tr_i` table type (`D2SAlgoMemo …` for the
  memoized bridge `d2sCodecBridgeImplMemo`; `PUnit` for hybrids with inline `gᵢ`
  realizations such as `Hyb_1` / `Hyb_2`);
- basic-FS verifier message spec `verifierMessageSpec` (e.g. `gSpec` / `eSpec` /
  `fsChallengeOracle (StmtIn × Salt) pSpec` per-hybrid).

Used by `d2sCodecBridgeImplMemo`, `d2fOuterImpl`, `d2fProverRaw` (this file) and by
`KeyLemma.hybridGame` / `hybridGameDist` / inline `Hyb_i` `gImpl` realizations. -/
abbrev GImpl {κ : Type} (verifierMessageSpec : OracleSpec κ) (M : Type) :=
  QueryImpl (gSpec (U := U) StmtIn pSpec δ)
    (StateT M
      (OptionT (OracleComp (D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec))))

variable {Salt : Type}

/-- **[CO25, Eq. (19)]** Type of the full `D2SAlgo^f(𝒫̃)` prover transform (§5.4, Items 1-6).
- Inner prover `D2FQueryProver` runs `𝒫̃^{D2SQuery}` (outputs `τ ∈ Σ^δ`)
- Post-processing applies `τ̌ := bin(τ)` (outputs `τ̌ ∈ {0,1}^{δ⋆}`)
-/
abbrev D2SAlgoTransform :=
  MaliciousProver oSpec pSpec StmtIn U δ →
    AbortComp (oSpec +
      D2SVerifierMessagePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedNARGString pSpec Salt)

/-- **[CO25, Lemma 5.1]** Type of the §5.8 line-4 trace maps (e.g. `D2STrace`, `(φ⁻¹, ψ)(tr)`).
Transforms a left-hand game query log into a basic-FS query log using
auxiliary uniform sampling. -/
abbrev D2STraceTransform {κ : Type} (verifierMessageSpec : OracleSpec κ) :=
  TaggedQueryLog (oSpec + verifierMessageSpec) →
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))

end TransformTypes

namespace DuplexSpongeFS.ZeroKnowledge

section CodecBias

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}
  [SpongeUnit U] [codec : Codec pSpec U]

/-- The encoded verifier message at verifier message round `i`. -/
abbrev EncodedVerifierMessage (i : pSpec.ChallengeIdx) :=
  Vector U (verifierMessageSize (pSpec := pSpec) i)

/-! ## Codec bias -/

omit [SpongeUnit U] [SpongeSize] in
/-- The codec's per-round total-variation guarantee, for any uniform samplers of the encoded and
decoded verifier message spaces. -/
theorem codec_round_pmf_tvDist_le_bias
    (i : pSpec.ChallengeIdx)
    [SampleableType (EncodedVerifierMessage (pSpec := pSpec) (U := U) i)]
    [SampleableType (pSpec.Challenge i)] :
    discreteTVDist ($ᵗ (pSpec.Challenge i))
      (codec.decode i <$> ($ᵗ (EncodedVerifierMessage (pSpec := pSpec) (U := U) i)))
      ≤ (codec.decodingBias i : ℝ) :=
  @Codec.decode_isBiased _ _ _ codec i _ _

end CodecBias

end DuplexSpongeFS.ZeroKnowledge
