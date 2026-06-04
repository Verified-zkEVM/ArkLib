/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.SingleSalt
import ArkLib.OracleReduction.Security.OracleDistribution

/-!
# Duplex Sponge Fiat-Shamir

We define the (multi-round) Fiat-Shamir transformation using duplex sponges.

This file provides:
- an unsalted DSFS surface (`duplexSpongeFiatShamir`) used by existing Section 5 machinery, and
- an explicit salted surface (`duplexSpongeFiatShamirSalted`) matching Construction 4.3 shape,
  where a salt `τ ∈ Σ^δ` is absorbed before round processing and included in the proof string.
- Oracle distributions:
  + duplexSpongeHashOracleDistribution: `h`-oracle
  + duplexSpongePermutationOracleDistribution: `(p, p⁻¹)`-oracle
  + duplexSpongeOracleDistribution (D_𝔖): `(h, p, p⁻¹)`-oracle
  + D_g: for Hyb1
  + D_e: for Hyb2
  + D_IP_salted (D_f): single-salt FS random oracle
-/

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

/-- Type class for protocol specifications to specify the size of each message as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`).

  `U`-independent so that size-only helpers (e.g. `numPermQueriesMessage`) stay free of the unit
  parameter. `Codec pSpec U` extends this class. -/
class HasMessageSize {n : ℕ} (pSpec : ProtocolSpec n) where
  messageSize : pSpec.MessageIdx → Nat

export HasMessageSize (messageSize)

/-- Message indices in rounds strictly before `k`. -/
abbrev MessageIdxBefore {n : ℕ} (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  {j : pSpec.MessageIdx // j.1.1 < k.1}

/-- Challenge indices in rounds strictly before `k`. -/
abbrev ChallengeIdxBefore {n : ℕ} (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  {j : pSpec.ChallengeIdx // j.1.1 < k.1}

/-- CO25 §5.2 — Encoded prover messages `(α̂_1, …, α̂_i)` for message rounds strictly before `k`.
`f j h` gives the `U`-vector encoding of message `j` whenever the round of `j` is before `k`. -/
abbrev EncodedMessagesBefore {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) [HasMessageSize pSpec]
    (k : Fin (n + 1)) : Type :=
  (j : MessageIdxBefore k pSpec) → Vector U (messageSize j.val)

/-- Type class for protocol specifications to specify the size of each challenge as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`).

  `U`-independent so that size-only helpers (e.g. `numPermQueriesChallenge`) stay free of the unit
  parameter. `Codec pSpec U` extends this class. -/
class HasChallengeSize {n : ℕ} (pSpec : ProtocolSpec n) where
  challengeSize : pSpec.ChallengeIdx → Nat

export HasChallengeSize (challengeSize)

abbrev EncodedChallengesBefore {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) [HasChallengeSize pSpec]
    (k : Fin (n + 1)) : Type :=
  (j : ChallengeIdxBefore k pSpec) → Vector U (challengeSize j.val)

namespace EncodedMessagesBefore

/-- Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`. -/
noncomputable def toList {n : ℕ} {pSpec : ProtocolSpec n} {U : Type} [HasMessageSize pSpec]
    {k : Fin (n + 1)} (f : pSpec.EncodedMessagesBefore U k) :
    List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) :=
  (Finset.univ : Finset (pSpec.MessageIdx)).toList.filterMap fun j =>
    if h : j.1.1 < k.1 then some ⟨j, f ⟨j, h⟩⟩ else none

end EncodedMessagesBefore

/-- Codec class for CO25 Definition 4.1.

`Codec pSpec U` is the generic-parameter carrier for everything DSFS needs about a
protocol's per-round encoder/decoder: per-round vector sizes, the encoder, its injectivity proof,
the decoder, the per-round decoder bias `ε_cdc`, and the per-round preimage sampler.

It extends the `U`-independent size classes `HasMessageSize` / `HasChallengeSize`, and projects
to per-index `Serialize` / `Deserialize` / `Serialize.IsInjective` instances via the projection
instances below — so generic alphabet-agnostic infrastructure in `ArkLib/Data/Classes/Serde.lean`
remains the single landing zone for hax-extracted Rust trait impls. Use `Codec.mk'` to assemble a
`Codec` from external `Serialize`/`Deserialize` instances plus the math-side metadata.

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
let inst : Deserialize (pSpec.Challenge idx) (Vector U (challengeSize idx)) :=
  Codec.instDeserializeChallenge idx
let challenge : pSpec.Challenge idx := inst.deserialize raw
```

See `deriveTranscriptDSFSAux` / `Prover.processRoundDSFS` for the canonical pattern.

We account for this by explicitly tracking **decoding biases**. We say that a codec has bias
`ε_cdc` if, for every `i ∈ [k]`, `ψ_i : Σ^{ℓ_V(i)} → M_{V, i}` is a `ε_{cdc, i}`-biased map
(i.e., it maps the uniform distribution on `Σ^{ℓ_V(i)}` to a distribution that is
`ε_{cdc, i}`-close to the uniform distribution on `M_{V, i}`).
-/
class Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    extends HasMessageSize pSpec, HasChallengeSize pSpec where
  /-- `φᵢ : Message i → Σ^{ℓ_P(i)}` — message encoder (CO25 Def. 4.1). -/
  encode : (i : pSpec.MessageIdx) → pSpec.Message i → Vector U (messageSize i)
  encode_injective : ∀ i, Function.Injective (encode i) -- `φᵢ` is injective
  /-- `ψᵢ : Σ^{ℓ_V(i)} → Challenge i` — challenge decoder (CO25 Def. 4.1). -/
  decode : (i : pSpec.ChallengeIdx) → Vector U (challengeSize i) → pSpec.Challenge i
  decodingBias : pSpec.ChallengeIdx → NNReal -- `ε_cdc`
  /-- For every `i`, `decode i` is ε-biased: `dist (𝒰 Challenge_i) (decode_i <$> 𝒰 Domain_i)`
    ≤ `decodingBias i`. Matches `Deserialize.CloseToUniform.ε_close` (CO25 Definition 4.1). -/
  decode_isBiased : ∀ (i : pSpec.ChallengeIdx)
      [Fintype (Vector U (challengeSize i))] [Nonempty (Vector U (challengeSize i))]
      [Fintype (pSpec.Challenge i)] [Nonempty (pSpec.Challenge i)],
      dist (PMF.uniformOfFintype (pSpec.Challenge i))
        (decode i <$> PMF.uniformOfFintype (Vector U (challengeSize i))) ≤ decodingBias i
  /-- For every `i`, `decode i` is surjective: every challenge has at least one encoded preimage.
    Required for the `ψ⁻¹` sampler in the Section 5.8 reduction. -/
  decode_surjective : ∀ i, Function.Surjective (decode i)
  /-- `ψᵢ⁻¹ : Challenge i → ProbComp (Σ^{ℓ_V(i)})` — preimage sampler (CO25 Def. 4.1). -/
  sampleChallengePreimage :
    (i : pSpec.ChallengeIdx) → pSpec.Challenge i → ProbComp (Vector U (challengeSize i))

namespace Codec

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}

instance (priority := high) instSerializeMessage [c : Codec pSpec U] (i : pSpec.MessageIdx) :
    Serialize (pSpec.Message i) (Vector U (messageSize i)) where
  serialize := c.encode i

instance (priority := high) instSerializeMessageInjective [c : Codec pSpec U]
    (i : pSpec.MessageIdx) :
    Serialize.IsInjective (pSpec.Message i) (Vector U (messageSize i)) where
  serialize_inj := c.encode_injective i

instance (priority := high) instDeserializeChallenge [c : Codec pSpec U] (i : pSpec.ChallengeIdx) :
    Deserialize (pSpec.Challenge i) (Vector U (challengeSize i)) where
  deserialize := c.decode i

/-- hax-pipeline constructor: assemble a `Codec` from external `Serialize`/`Deserialize`
    instances supplied by Rust→hax extraction, plus the math-side metadata. `decodingBias` is
    derived from `[decChalUniform]`'s `ε` field; no separate bias parameter is needed. -/
def mk' {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    (mSize : pSpec.MessageIdx → Nat) (cSize : pSpec.ChallengeIdx → Nat)
    [∀ i, Fintype (Vector U (cSize i))] [∀ i, Nonempty (Vector U (cSize i))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Nonempty (pSpec.Challenge i)]
    [serMsg : ∀ i, Serialize (pSpec.Message i) (Vector U (mSize i))]
    [serMsgInj : ∀ i, Serialize.IsInjective (pSpec.Message i) (Vector U (mSize i))]
    [decChal : ∀ i, Deserialize (pSpec.Challenge i) (Vector U (cSize i))]
    [decChalUniform : ∀ i, Deserialize.CloseToUniform (pSpec.Challenge i) (Vector U (cSize i))]
    (dechalSurj : ∀ i, Function.Surjective ((decChal i).deserialize))
    (sampler : (i : pSpec.ChallengeIdx) → pSpec.Challenge i → ProbComp (Vector U (cSize i))) :
    Codec pSpec U where
  messageSize := mSize
  challengeSize := cSize
  encode := fun i => (serMsg i).serialize
  encode_injective := fun i => (serMsgInj i).serialize_inj
  decode := fun i => (decChal i).deserialize
  decodingBias := fun i => (decChalUniform i).ε
  decode_isBiased := fun i [_h1 : Fintype (Vector U (cSize i))]
      [_h2 : Nonempty (Vector U (cSize i))]
      [_h3 : Fintype (pSpec.Challenge i)]
      [_h4 : Nonempty (pSpec.Challenge i)] => by
    convert (decChalUniform i).ε_close using 4
  decode_surjective := dechalSurj
  sampleChallengePreimage := sampler

end Codec

/-!
## Salt codec (CO25 line 1188, line 1729)

The paper distinguishes two views of a single salt:

- **On-sponge view** (CO25 Construction 4.3): the salt lives in `Σ^δ` and is absorbed into the
  duplex sponge directly. In Lean this is `Vector U δ`.
- **FS-standard view** (CO25 Construction 3.17 + §5.8 hybrids `Hyb₃`, `Hyb₄`): the salt is a
  binary string in `{0,1}^{δ★}` (where `δ★ := δ · log₂|Σ|`) used as part of the FS-standard
  oracle key. We model this as an abstract type `Salt`.

The two views are bridged by an injective encoding `bin : Σ^δ → {0,1}^{δ★}` (paper line 1188:
`τ̌ := bin(τ) ∈ {0,1}^{δ★}`; line 1729 states `bin(·)` is injective). The encoding contributes
*no* bias to the §5 error analysis — only the time cost `t_bin = δ · log|Σ|`.

`SaltCodec U δ Salt` packages `bin` and its left inverse. The class is intentionally minimal:
`decode_encode` gives injectivity of `encode` automatically.
-/

/-- Bridge between on-sponge salts (`Σ^δ = Vector U δ`) and the pre-encoded abstract salt type
`Salt` (paper's `{0,1}^{δ★}`). `encode = bin` per CO25 line 1188. -/
class SaltCodec (U : Type) (δ : Nat) (Salt : Type) where
  /-- `bin : Σ^δ → {0,1}^{δ★}` — inject `Σ^δ` salt into the FS-standard pre-encoded salt type. -/
  encode : Vector U δ → Salt
  /-- Left inverse of `encode`. Exists because `encode = bin` is injective with a recoverable
    code (paper line 1729). -/
  decode : Salt → Vector U δ
  /-- `decode ∘ encode = id`. Gives **injectivity** of `encode` (and matches CO25 line 1729). -/
  decode_encode : ∀ τ, decode (encode τ) = τ

namespace SaltCodec

variable {U : Type} {δ : Nat} {Salt : Type}

/-- `encode` is injective, derived from `decode_encode`. Matches CO25 line 1729. -/
theorem encode_injective [SaltCodec U δ Salt] :
    Function.Injective (encode (U := U) (δ := δ) (Salt := Salt)) := by
  intro a b h
  have := congrArg (decode (U := U) (δ := δ) (Salt := Salt)) h
  rw [decode_encode, decode_encode] at this
  exact this

end SaltCodec

/-!
## Block-count notation (CO25 Equations 6–7)

`L_δ`, `L_P(i)`, `L_V(i)`, `L_P`, `L_V`, `L` from the paper. -/
section BlockCountNotation

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- CO25 Eq. 6 — `L_δ = ⌈δ / r⌉`: number of rate blocks needed for a salt of size `δ`. -/
def numSaltBlocks (δ : Nat) : Nat := Nat.ceil ((δ : ℚ) / SpongeSize.R)

alias Lδ := numSaltBlocks

/-- Number of queries to the permutation oracle needed to absorb the `i`-th message of the
  protocol specification. This is `Lₚ(i)` in the paper block-count notation (Equation 6). -/
def numPermQueriesMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((messageSize i : ℚ) / SpongeSize.R)

alias Lₚᵢ := numPermQueriesMessage

/-- Total number of queries to the permutation oracle needed to absorb all messages of the
  protocol specification. This is `Lₚ` in the paper block-count notation (Equation 7). -/
def totalNumPermQueriesMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ i

alias Lₚ := totalNumPermQueriesMessage

/-- Number of queries to the permutation oracle needed to absorb the `i`-th challenge of the
  protocol specification. This is `Lᵥ(i)` in the paper block-count notation (Equation 6). -/
def numPermQueriesChallenge (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((challengeSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all challenges of the
  protocol specification. This is `Lᵥ` in the paper block-count notation (Equation 7). -/
def totalNumPermQueriesChallenge : Nat :=
  ∑ i, pSpec.Lᵥᵢ i

alias Lᵥ := totalNumPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all messages and challenges
  of the protocol specification. This is `L` in the paper block-count notation (Equation 7). -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesMessage + pSpec.totalNumPermQueriesChallenge

alias L := totalNumPermQueries

end BlockCountNotation

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

section Section58Oracles

/-- Section 5.8 `Hyb₁` challenge-oracle surface: encoded prover-prefix queries, encoded verifier
responses.

Per CO25 Eq. 15: `dom_i = {0,1}^≤n × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)}` — the prover prefix is
*exactly* `i` encoded messages, not an unbounded list. We model this as
`pSpec.EncodedMessagesBefore U i.1.castSucc`, the dependent function indexed by message rounds
strictly before `i`. With `Fintype` instances for the components this Query is also `Fintype`,
which is required for the eager full-table `OracleDistribution.uniform _` realization. -/
@[inline, reducible]
def gSpecInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    ∀ i, OracleInterface (Vector U (challengeSize (pSpec := pSpec) i)) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => Vector U (challengeSize (pSpec := pSpec) i)
    toOC.impl := fun _ => read }

/-- Oracle family for the `gᵢ` queries in Section 5.8 `Hyb₁`. -/
@[inline, reducible]
def gSpec
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [fun i => Vector U (challengeSize (pSpec := pSpec) i)]ₒ'
    (gSpecInterface (U := U) StmtIn pSpec δ)

/-- Section 5.8 `Hyb₂` challenge-oracle surface: encoded prover-prefix queries, decoded verifier
responses.

Same CO25 Eq. 52 prefix shape as `gSpecInterface` (encoded messages
indexed by rounds `< i`); only the response type differs (decoded `pSpec.Challenge i`). -/
@[inline, reducible]
def eSpecInterface
    {U : Type} [SpongeUnit U] [SpongeSize]
    {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query :=
      StmtIn × Vector U δ ×
        pSpec.EncodedMessagesBefore U i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

/-- Oracle family for the `eᵢ` queries in Section 5.8 `Hyb₂`. -/
@[inline, reducible]
def eSpec
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) (δ : Nat) [HasMessageSize pSpec] :
    OracleSpec (((i : pSpec.ChallengeIdx) ×
      (eSpecInterface (U := U) StmtIn pSpec δ i).Query)) :=
  [pSpec.Challenge]ₒ'
    (eSpecInterface (U := U) StmtIn pSpec δ)

/-- CO25 Eq. 15 — eager full-table distribution `𝒟_Σ` (symbol `g`) over the encoded
challenge-oracle family for `Hyb₁`.

Samples a single full random table `g : (q : Domain) → Range q` once at game start; all subsequent
queries deterministically index into this fixed table. The `[SampleableType (OracleFamily _)]`
hypothesis matches CO25: with a fixed-length round-indexed prefix (see `EncodedMessagesBefore`), the
oracle's domain is finite, and uniform sampling of the function table is the canonical realization
of `g ← 𝒰((dom_i → Σ^{ℓ_V(i)})_{i∈[k]})`. -/
def D_Sigma
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec] [HasChallengeSize pSpec]
    [SampleableType
      (OracleReduction.OracleFamily
        (gSpec (U := U) StmtIn pSpec δ))] :
    OracleReduction.OracleDistribution
      (gSpec (U := U) StmtIn pSpec δ) :=
  OracleReduction.D_ROM _

/-- Bridge: `SampleableType` for `gSpec` (Hyb₁ `g`) derived from
granular `VCVCompatible` base-type hypotheses. Eliminates verbose `SampleableType (OracleFamily
(gSpec …))` at call sites in §5.8 hybrids and in `BadEvents.lemma_5_8`'s
eager `𝒟_Σ` sampling. -/
instance instSampleableTypeEncodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize] {n : ℕ} {StmtIn : Type} {pSpec : ProtocolSpec n} {δ : Nat}
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    SampleableType (OracleReduction.OracleFamily
      (gSpec (U := U) StmtIn pSpec δ)) := by
  sorry

/-- CO25 Eq. 52 — eager full-table distribution `e` over the decoded challenge-oracle family
for `Hyb₂`.

Same eager full-table semantics as `D_Sigma`, with the
response type swapped from `Σ^{ℓ_V(i)}` to the decoded `pSpec.Challenge i`. Realizes
`e ← 𝒰((dom_i → ℳ_{V,i})_{i∈[k]})`. -/
def D_e
    {U : Type} [SpongeUnit U] [SpongeSize]
    (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (δ : Nat)
    [HasMessageSize pSpec]
    [SampleableType
      (OracleReduction.OracleFamily
        (eSpec (U := U) StmtIn pSpec δ))] :
    OracleReduction.OracleDistribution
      (eSpec (U := U) StmtIn pSpec δ) :=
    OracleReduction.D_ROM _

/-! ## Setup: oracle distributions and `SampleableType` bridges -/

/-- CO25 Eq. 54 — eager full-table distribution `𝒟_IP` (symbol `f`, salted) over the
salted Fiat–Shamir challenge oracle for `Hyb₃` and `Hyb₄`.

Samples a single full random table `f : (q : Domain) → Range q` once at game start over the
salted domain `dom'_i = {0,1}^≤n × {0,1}^{δ⋆} × ℳ_{P,1} × … × ℳ_{P,i}` with range `ℳ_{V,i}`.
Per CO25 line 1784, Hyb₃ and Hyb₄ both sample from this same distribution; the difference
between hybrids lies in the prover/verifier algorithm, not the oracle.

The salt slot of `dom'_i` is the pre-encoded `{0,1}^{δ⋆}`-side, modeled here by the abstract
type `Salt`. The on-sponge `Σ^δ` salt produced by Construction 4.3 is projected via
`SaltCodec.encode = bin` before being used as an oracle key. -/
noncomputable def D_IP_salted
    {n : ℕ} {StmtIn Salt : Type} (pSpec : ProtocolSpec n)
    [VCVCompatible StmtIn] [VCVCompatible Salt]
    [∀ i, VCVCompatible (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleReduction.OracleDistribution (fsChallengeOracle (StmtIn × Salt) pSpec) :=
  OracleReduction.D_IP (Statement := StmtIn × Salt) pSpec

noncomputable def D_f
    {n : ℕ} {StmtIn Salt : Type} (pSpec : ProtocolSpec n)
    [VCVCompatible StmtIn] [VCVCompatible Salt]
    [∀ i, VCVCompatible (pSpec.Message i)] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleReduction.OracleDistribution (fsChallengeOracle (StmtIn × Salt) pSpec) :=
  D_IP_salted pSpec

/-- Bridge: `SampleableType` for `eSpec` (Hyb₂ `e`) derived from
granular `VCVCompatible` base-type hypotheses. Eliminates verbose `SampleableType (OracleFamily
(eSpec …))` at call sites in §5.8 hybrids. -/
instance instSampleableTypeDecodedChallengeOracle
    {U : Type} [SpongeUnit U] [SpongeSize] {n : ℕ} {StmtIn : Type} {pSpec : ProtocolSpec n} {δ : Nat}
    [VCVCompatible StmtIn] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [HasMessageSize pSpec] :
    SampleableType (OracleReduction.OracleFamily
      (eSpec (U := U) StmtIn pSpec δ)) := by
  sorry

end Section58Oracles

end ProtocolSpec

namespace OracleSpec

/-- The oracle specification for duplex sponge Fiat-Shamir (Definition 4.2, written as `𝒟_𝔖`).
The index consists of `(h, p, p⁻¹)`, where:
- `h : ByteArray → Vector U SpongeSize.C`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the forward direction of the random permutation
- `p⁻¹ : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the backward direction of the random permutation
-/
@[reducible]
def duplexSpongeChallengeOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U SpongeSize.C) + permutationOracle (CanonicalSpongeState U)

/-- The type of a single entry in a duplex sponge query trace -/
abbrev duplexSpongeTraceEntry {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  := Sigma (α := StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U)
      (β := duplexSpongeChallengeOracle StartType U)

alias «𝒟_𝔖» := duplexSpongeChallengeOracle

/-! ### Smart constructors for the three `(h, p, p⁻¹)` `𝒟_𝔖` query flavors

CO25 §5.4 paper notation `('h', 𝕩, …)` / `('p', s_in, …)` / `('p⁻¹', s_out, …)` corresponds
to three nested-`Sum` injections into

  `(duplexSpongeChallengeOracle StartType U).Domain
     = StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U`.

The wrappers below tag each injection with the paper query name, so trace constructions
(`⟨dsHashQuery 𝕩, capOut⟩`, `⟨dsPermInvQuery s_out, s_in⟩`) and pattern matches read directly
as paper notation rather than as nested-`Sum.inl/.inr` chains. `@[match_pattern]` keeps them
usable as match patterns; `@[reducible]` lets the elaborator unfold them where the bare
`Sum`-form is expected. -/

/-- CO25 §5.4 paper `h(𝕩)` — hash query index. -/
@[match_pattern, reducible]
def dsHashQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stmt : StartType) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inl stmt

/-- CO25 §5.4 paper `p(s_in)` — forward permutation query index. -/
@[match_pattern, reducible]
def dsPermQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateIn : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inl stateIn)

/-- CO25 §5.4 paper `p⁻¹(s_out)` — inverse permutation query index. -/
@[match_pattern, reducible]
def dsPermInvQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize]
    (stateOut : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inr stateOut)

/-- Forward-only sub-spec of `duplexSpongeChallengeOracle`: only `h` and the forward permutation
slot `p` are exposed. The backward slot `p⁻¹` is omitted.

This is the type-level encoding of CO25 Figure 4 line 3 — `𝒱^{h,p}` — the honest verifier in the
DSFS hybrid experiment has no syntactic access to `p⁻¹`. Used as the typing surface of the verify
helpers (`deriveTranscriptDSFS{,Salted}`) and a parallel narrow-typed verifier surface
`Verifier.duplexSpongeFiatShamirSaltedForward`. The wide reduction surface
`Reduction.duplexSpongeFiatShamir{,Salted}` keeps the full `duplexSpongeChallengeOracle` because
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
  OracleReduction.OracleFamily (StartType →ₒ Vector U SpongeSize.C) ×
    Equiv.Perm (CanonicalSpongeState U)

/-- Interpret one sampled `𝒟_𝔖` realization as the concrete `(h, p, p⁻¹)` query implementation. -/
@[reducible]
def duplexSpongeOracleQueryImpl
    {StartType U : Type} [SpongeUnit U] [SpongeSize]
    (duplexSpongeOracle : DuplexSpongeOracleFamily StartType U) :
    QueryImpl (duplexSpongeChallengeOracle StartType U) ProbComp
  | Sum.inl qHash => OracleReduction.tableQueryImpl (g := duplexSpongeOracle.1) qHash
  | Sum.inr (Sum.inl state) => pure (duplexSpongeOracle.2 state)
  | Sum.inr (Sum.inr state) => pure (duplexSpongeOracle.2.symm state)

/-- Interpret one sampled permutation as forward/backward permutation-oracle answers. -/
@[reducible]
def permutationOracleQueryImpl {α : Type} (p : Equiv.Perm α) :
    QueryImpl (permutationOracle α) ProbComp
  | Sum.inl state => pure (p state)
  | Sum.inr state => pure (p.symm state)

/-- `CanonicalSpongeState U = Vector U SpongeSize.N` is `VCVCompatible` whenever `U` is.
Needed so `VCVCompatible U` implies `SampleableType (Equiv.Perm (CanonicalSpongeState U))`. -/
instance instVCVCompatibleCanonicalSpongeState
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] :
    VCVCompatible (CanonicalSpongeState U) :=
  (inferInstance : VCVCompatible (Vector U SpongeSize.N))

/-- Uniform random-function distribution for the `h` component of `𝒟_𝔖`. -/
noncomputable def duplexSpongeHashOracleDistribution (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U] :
    OracleReduction.OracleDistribution (StartType →ₒ Vector U SpongeSize.C) :=
  OracleReduction.D_ROM _

/-- Uniform random-permutation distribution for the `(p, p⁻¹)` component of `𝒟_𝔖`.

Only `p` is sampled; `p⁻¹` is derived as `p.symm`. -/
noncomputable def duplexSpongePermutationOracleDistribution (U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible U] :
    OracleReduction.OracleDistribution (permutationOracle (CanonicalSpongeState U)) where
  Carrier := Equiv.Perm (CanonicalSpongeState U)
  sample := $ᵗ (Equiv.Perm (CanonicalSpongeState U))
  toImpl := permutationOracleQueryImpl

/-- CO25 Definition 4.2 — ideal duplex-sponge oracle distribution `𝒟_𝔖`.

Samples `h` as a uniform random function and `p` as a uniform random permutation, then answers
inverse-permutation queries using `p.symm`. -/
noncomputable def duplexSpongeOracleDistribution (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U] :
    OracleReduction.OracleDistribution
      (duplexSpongeChallengeOracle StartType U) :=
  OracleReduction.OracleDistribution.prod -- **prod**
    (duplexSpongeHashOracleDistribution StartType U)
    (duplexSpongePermutationOracleDistribution U)

alias D_𝔖 := duplexSpongeOracleDistribution

@[simp]
lemma duplexSpongeOracleDistribution_toImpl
    (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U]
    (realization : DuplexSpongeOracleFamily StartType U) :
    (duplexSpongeOracleDistribution StartType U).toImpl realization =
      duplexSpongeOracleQueryImpl realization := by
  funext q
  cases q with
  | inl qHash => rfl
  | inr qPerm =>
      cases qPerm <;> rfl

@[simp]
lemma duplexSpongeOracleDistribution_sample
    (StartType U : Type) [SpongeUnit U] [SpongeSize]
    [VCVCompatible StartType] [VCVCompatible U] :
    (duplexSpongeOracleDistribution StartType U).sample =
      (do
        let h ← $ᵗ (OracleReduction.OracleFamily
          (StartType →ₒ Vector U SpongeSize.C))
        let p ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
        pure (h, p)) := rfl

end OracleDistribution

end OracleSpec

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [Codec pSpec U]

namespace OracleSpec

/-- Per-index query budget for the DS oracle alone: `tₕ` for hash, `tₚ` for forward permutation,
    `tₚᵢ` for inverse permutation. Used directly for DS-only provers (e.g. Lemma 5.8). -/
def duplexSpongeQueryBudget (tₕ tₚ tₚᵢ : ℕ) :
    (duplexSpongeChallengeOracle StmtIn U).Domain → ℕ
  | .inl _ => tₕ
  | .inr (.inl _) => tₚ
  | .inr (.inr _) => tₚᵢ

/-- Extends `duplexSpongeQueryBudget` to a prover that also queries an ambient oracle `oSpec`.
    `tShared` bounds the `oSpec` slice; DS queries delegate to `duplexSpongeQueryBudget`.
    Used for provers against `oSpec + duplexSpongeChallengeOracle` (e.g. Lemma 5.1). -/
def duplexSpongeQueryBudgetWithShared (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ) :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → ℕ
  | .inl q => tShared q
  | .inr q => duplexSpongeQueryBudget tₕ tₚ tₚᵢ q

end OracleSpec

/-- Proof-string format for the salted DSFS surface (`τ` plus prover messages). -/
abbrev DSSaltedProof (pSpec : ProtocolSpec n) (U : Type) (δ : Nat) :=
  Vector U δ × pSpec.Messages

/-- Paper-faithful type of the malicious DSFS prover `𝒫̃` (`\tilde{\mathcal{P}}`), per
CO25 §5.4 line 1136 (paper Step 4 of `D2SAlgo`):
*"Let `𝒜`'s output be `(x, π_𝒜)`, and parse `π_𝒜` as `(τ, α_1, ..., α_k)`"*.

`𝒫̃` queries `(h, p, p⁻¹) = duplexSpongeChallengeOracle` plus an ambient `oSpec` (for oracle-IP
generalization; `oSpec = []ₒ` recovers the paper's pure-IP case), and outputs a salted proof
`(x, (τ, messages))` with on-sponge salt `τ : Vector U δ`.

Used uniformly in §5.4 (`D2SAlgo` input), §5.6 (`BadEvents.lemma_5_8` — LHS matches `Hyb_0`,
RHS matches `Hyb_1`), §5.8 hybrids `Hyb_0 .. Hyb_4`, and Lemma 5.1. -/
abbrev MaliciousProver {n : ℕ} {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (StmtIn U : Type) [SpongeUnit U] [SpongeSize] (δ : ℕ) :=
  OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)

/-- Paper-faithful type of the narrow DSFS honest verifier `𝒱^{h,p}` (`\mathcal{V}^{h,p}`),
per CO25 Figure 4 line 3 and §5.8 hybrid security games.

`𝒱^{h,p}` consumes salted proofs `(τ, π) : DSSaltedProof pSpec U δ` and queries `(h, p)` only —
the inverse permutation `p⁻¹` is **not** exposed at the type level (`duplexSpongeForwardOracle`,
not `duplexSpongeChallengeOracle`). This narrow typing is what makes the §5.6 / §5.8 trace
analysis go through: the honest verifier provably cannot witness `p⁻¹`-collisions.

Constructed from a base interactive `Verifier` via `Verifier.duplexSpongeFiatShamirSaltedForward`.
Used in `dsfsGame`, `hybridGame`, `hyb_0 .. hyb_4` (`KeyLemma.lean`), and the conclusion of
Lemma 5.1. For the wide-spec variant kept for `Reduction.duplexSpongeFiatShamirSalted` API
compatibility (with `p⁻¹` in the spec but unused), see
`Verifier.duplexSpongeFiatShamirSalted`. -/
abbrev DSFSSaltedVerifier {n : ℕ} {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (StmtIn StmtOut U : Type) [SpongeUnit U] [SpongeSize] (δ : ℕ) :=
  NonInteractiveVerifier (DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (oSpec + duplexSpongeForwardOracle StmtIn U)
    StmtIn StmtOut

namespace ProtocolSpec.Messages

/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the permutation oracle for the challenges.

  This is used to define `deriveTranscriptDSFS`. The body uses only forward permutation queries
  (`squeeze`, `absorb`); the return type is the narrow `duplexSpongeForwardOracle`, encoding
  CO25 Figure 4 line 3 (`𝒱^{h,p}`) at the type level. -/
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
        let inst : Deserialize (pSpec.Challenge idx) (Vector U (challengeSize idx)) :=
          Codec.instDeserializeChallenge idx
        let ⟨challenge, newSponge⟩ ← liftM (curSponge.squeeze (challengeSize idx))
        let deserializedChallenge : pSpec.Challenge idx :=
          inst.deserialize challenge
        return (newSponge, prevTranscript.concat deserializedChallenge)
      | .P_to_V =>
        let idx : pSpec.MessageIdx := ⟨i, hDir⟩
        let inst : Serialize (pSpec.Message idx) (Vector U (messageSize idx)) :=
          Codec.instSerializeMessage idx
        let serializedMessage : Vector U (messageSize idx) :=
          inst.serialize (messages idx)
        let newSponge ← liftM (DuplexSponge.absorb curSponge serializedMessage.toList)
        return (newSponge, prevTranscript.concat (messages idx)))
    i

/-- Derive the full transcript from the (full) messages, via doing absorb / squeeze operations on
    the duplex sponge.

  Returns the final state of the duplex sponge and the full transcript. Lives at the narrow
  forward-only spec (CO25 Figure 4 line 3, `𝒱^{h,p}`). -/
def deriveTranscriptDSFS {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmtIn : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge ← liftM (DuplexSponge.start stmtIn)
  deriveTranscriptDSFSAux sponge messages (Fin.last n)

end ProtocolSpec.Messages
section Execution

/--
Prover's function for processing the next round, given the current result of the previous round.

This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)]
     (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc ×
        CanonicalDuplexSponge U × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (pSpec.MessagesUpTo j.succ ×
          CanonicalDuplexSponge U × prover.PrvState j.succ) := do
  let ⟨messages, sponge, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let idx : pSpec.ChallengeIdx := ⟨j, hDir⟩
    let inst : Deserialize (pSpec.Challenge idx) (Vector U (challengeSize idx)) :=
      Codec.instDeserializeChallenge idx
    let f ← prover.receiveChallenge idx state
    let (challenge, newSponge) ←
      liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (DuplexSponge.squeeze sponge (challengeSize idx))
    -- Deserialize the challenge
    let deserializedChallenge : pSpec.Challenge idx := inst.deserialize challenge
    return ⟨messages.extend hDir, newSponge, f deserializedChallenge⟩
  | .P_to_V => do
    let idx : pSpec.MessageIdx := ⟨j, hDir⟩
    let inst : Serialize (pSpec.Message idx) (Vector U (messageSize idx)) :=
      Codec.instSerializeMessage idx
    let ⟨msg, newState⟩ ← prover.sendMessage idx state
    let serializedMessage : Vector U (messageSize idx) := inst.serialize msg
    let newSponge ← liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (DuplexSponge.absorb sponge serializedMessage.toList)
    return ⟨messages.concat hDir msg, newSponge, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      -- Initialize the sponge with the input statement
      let sponge ← liftM (DuplexSponge.start stmt)
      return ⟨default, sponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- The duplex sponge Fiat-Shamir transformation for the prover. -/
def Prover.duplexSpongeFiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundDSFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The duplex sponge Fiat-Shamir transformation for the verifier (wide-spec surface).

The verify body itself only uses forward operations (`start`, `absorb`, `squeeze`) via the narrow
helper `deriveTranscriptDSFS`; the surface is kept at the wide
`oSpec + duplexSpongeChallengeOracle StmtIn U` so it lines up with
`Reduction.duplexSpongeFiatShamir` (which requires the prover and verifier to share a single
oracle spec). The helper is `liftComp`-ed into the wide spec at the call site.
For the strict CO25 Figure 4 line 3 typing
(`𝒱^{h,p}` — no `p⁻¹`) used inside security games, see
`Verifier.duplexSpongeFiatShamirForward`. -/
def Verifier.duplexSpongeFiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    -- Get the messages from the non-interactive proof
    let messages : pSpec.Messages := proof 0
    -- Derive the full transcript based on the messages and the sponge (forward-only helper),
    -- then lift into the wide spec required by this surface.
    let ⟨_, transcript⟩ ←
      liftComp (messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn)
        (oSpec + duplexSpongeChallengeOracle StmtIn U)
    let v ← (V.verify stmtIn transcript).run
    v.getM
    -- Option.getM (← (V.verify stmtIn transcript).run)

/-- Narrow-typed verifier surface matching CO25 Figure 4 line 3 (`𝒱^{h,p}`).

Lives at `oSpec + duplexSpongeForwardOracle StmtIn U`, omitting the inverse permutation slot
`p⁻¹` at the type level. This is the surface the security game in §5.8 uses for the honest
verifier; the wider surface `Verifier.duplexSpongeFiatShamir` is preserved for compatibility
with `Reduction.duplexSpongeFiatShamir` (whose `NonInteractiveReduction` requires uniform spec). -/
def Verifier.duplexSpongeFiatShamirForward (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + duplexSpongeForwardOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let ⟨_, transcript⟩ ← messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- The duplex sponge Fiat-Shamir transformation for an (interactive) reduction, which consists of
  applying the duplex sponge Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.duplexSpongeFiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamir
  verifier := R.verifier.duplexSpongeFiatShamir

/--
Derive the full transcript from prover messages after explicitly absorbing a public salt `τ`.

This is the transcript path for the salted Construction 4.3 surface.
-/
def ProtocolSpec.Messages.deriveTranscriptDSFSSalted {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {δ : Nat}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge0 ← liftM (DuplexSponge.start stmtIn)
  let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
  ProtocolSpec.Messages.deriveTranscriptDSFSAux (pSpec := pSpec) (oSpec := oSpec) (U := U)
    sponge messages (Fin.last n)

/--
Run the prover up to round `i` after first absorbing an explicit salt `τ`.
-/
@[inline, specialize]
def Prover.runToRoundDSFSSalted [∀ i, VCVCompatible (pSpec.Challenge i)] {δ : Nat}
    (salt : Vector U δ) (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      let sponge0 ← liftM (DuplexSponge.start stmt)
      let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
      return ⟨default, sponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- Salted DSFS prover surface (Construction 4.3-facing). -/
def Prover.duplexSpongeFiatShamirSalted [∀ i, VCVCompatible (pSpec.Challenge i)] (δ : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → P.PrvState 0 →
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Vector U δ)) :
    NonInteractiveProver (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let salt ← sampleSalt stmtIn state
    let ⟨messages, _, state⟩ ← P.runToRoundDSFSSalted (salt := salt) (Fin.last n) stmtIn state
    return ⟨(salt, messages), state⟩
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- Salted DSFS verifier surface (Construction 4.3-facing, wide-spec).

Wide-spec wrapper around the forward-only helper `deriveTranscriptDSFSSalted`. Kept at the wide
`oSpec + duplexSpongeChallengeOracle StmtIn U` for compatibility with
`Reduction.duplexSpongeFiatShamirSalted`. For the strict `𝒱^{h,p}` typing used inside §5.8
security games, see `Verifier.duplexSpongeFiatShamirSaltedForward`. -/
def Verifier.duplexSpongeFiatShamirSalted (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := proof 0
    let salt : Vector U δ := saltedProof.1
    let messages : pSpec.Messages := saltedProof.2
    let ⟨_, transcript⟩ ←
      liftComp
        (messages.deriveTranscriptDSFSSalted
          (pSpec := pSpec) (oSpec := oSpec) (U := U) stmtIn salt)
        (oSpec + duplexSpongeChallengeOracle StmtIn U)
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- Narrow-typed salted DSFS verifier surface — CO25 Figure 4 line 3 (`𝒱^{h,p}`) for the salted
Construction 4.3 path.

Lives at `oSpec + duplexSpongeForwardOracle StmtIn U`, omitting the inverse permutation slot
`p⁻¹` at the type level. Used by the §5.8 hybrid security games to invoke the honest verifier
without granting it syntactic access to `p⁻¹`. -/
def Verifier.duplexSpongeFiatShamirSaltedForward (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    DSFSSaltedVerifier oSpec pSpec StmtIn StmtOut U δ where
  verify := fun stmtIn proof => do
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := proof 0
    let salt : Vector U δ := saltedProof.1
    let messages : pSpec.Messages := saltedProof.2
    let ⟨_, transcript⟩ ←
      messages.deriveTranscriptDSFSSalted
        (pSpec := pSpec) (oSpec := oSpec) (U := U) stmtIn salt
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- Salted DSFS reduction surface (Construction 4.3-facing). -/
def Reduction.duplexSpongeFiatShamirSalted [∀ i, VCVCompatible (pSpec.Challenge i)] (δ : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → R.prover.PrvState 0 →
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Vector U δ)) :
    NonInteractiveReduction (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamirSalted (δ := δ) sampleSalt
  verifier := R.verifier.duplexSpongeFiatShamirSalted (δ := δ)

/-- Short alias for `Verifier.duplexSpongeFiatShamirSaltedForward` — lift an interactive
`Verifier` to the paper-faithful narrow DSFS NARG verifier `𝒱^{h,p}`
(`DSFSSaltedVerifier`).

This is the canonical §5.8 surface: salted (consumes `(τ, π) : DSSaltedProof`) and forward-only
(`oSpec + duplexSpongeForwardOracle StmtIn U` — no `p⁻¹`). -/
@[inline, reducible]
def Verifier.toDSFS (δ : Nat) (V : Verifier oSpec StmtIn StmtOut pSpec) :
    DSFSSaltedVerifier oSpec pSpec StmtIn StmtOut U δ :=
  V.duplexSpongeFiatShamirSaltedForward δ

/-- Run the narrow-spec salted forward verifier `𝒱^{h,p}` (`V.toDSFS δ`) on
`(stmtIn, proof : DSSaltedProof pSpec U δ)`, then `liftComp` the resulting computation up to the
wide spec `oSpec + duplexSpongeChallengeOracle StmtIn U`.

Shared by:
- `dsfsGame` / `hybridGame` (KeyLemma.lean — `Hyb_0` through `Hyb_3` skeleton);
- `lemma5_8ProjectedTraceDistAbortable` / `lemma5_8TraceExperiment` (BadEvents.lean — §5.6).

Encodes CO25 Figure 4 line 3 at the type level: the narrow input spec
`oSpec + duplexSpongeForwardOracle StmtIn U` exposes only `(h, p)`, while the wide output spec
`oSpec + duplexSpongeChallengeOracle StmtIn U` exposes `(h, p, p⁻¹)`. Because the body is just
`liftComp`-ed from the narrow surface, no `p⁻¹` query ever appears in the resulting query log. -/
def runForwardVerifierWide (δ : Nat) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
  let verifyCompNarrow :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((V.toDSFS δ).run stmtIn (fun i => match i with | ⟨0, _⟩ => proof)).run
  liftComp verifyCompNarrow (oSpec + duplexSpongeChallengeOracle StmtIn U)

/-- Short alias for `Verifier.singleSaltFiatShamir` — lift an interactive `Verifier` to the
paper-faithful FS-standard salted NARG verifier `𝒱_std^f` (`FSStdSaltedVerifier`).

Consumes `(τ, π) : FSSaltedProof pSpec Salt` and queries a single FS challenge oracle
`fsChallengeOracle (StmtIn × Salt) pSpec` keyed at the augmented statement `(stmtIn, τ)`. -/
@[inline, reducible]
def Verifier.toSaltedFS {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    FSStdSaltedVerifier oSpec pSpec StmtIn StmtOut Salt :=
  V.singleSaltFiatShamir

end Execution

/-! ### Section 5 Transforms and Monads -/

/-- `OracleComp σ` paired with a paper-faithful abort layer (`OptionT`).

`OracleComp σ` queries `σ`; `OptionT` adds `none = abort` (CO25 §5 `err` outcome). Section 5
simulators (`D2SQuery`, `LookAhead`, `BackTrack`, `StdTrace`, `D2STrace`) all live in this stack
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
  {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  {δ : Nat}
  [codec : Codec pSpec U]

/-- CO25 §5.4 — External challenge-oracle family augmented with the auxiliary sampling oracles.

`D2SChallengePlusUnitOracle challengeSpec` is `challengeSpec + (Unit →ₒ U) + unifSpec`:
the sum of the caller-supplied challenge oracle `gᵢ`-family, the auxiliary unit-sampling
oracle `𝒰(Σ)` used by D2SQuery fresh-sample branches (§5.4 Items 2(b), 3(b), 4(c)iii, 4(e)iiiC),
and `unifSpec` for any additional uniform randomness. -/
abbrev D2SChallengePlusUnitOracle {κ : Type} (challengeSpec : OracleSpec κ) :=
  challengeSpec + ((Unit →ₒ U) + unifSpec)

/-- CO25 §5.4 Eq. 16 — Shorthand for the recurring `gᵢ`-realization shape: a `QueryImpl`
from the `gSpec` source into `StateT M (OptionT (OracleComp …))` over the basic-FS-style
outer spec `D2SChallengePlusUnitOracle challengeSpec`.

Polymorphic over:
- inner state `M` — paper §5.4 D2SAlgo Item 3's `tr_i` table type (`D2SAlgoMemo …` for the
  memoized bridge `d2sCodecBridgeImplMemo`; `PUnit` for hybrids with inline `gᵢ`
  realizations such as `Hyb_1` / `Hyb_2`);
- basic-FS challenge spec `challengeSpec` (e.g. `gSpec` / `eSpec` /
  `fsChallengeOracle (StmtIn × Salt) pSpec` per-hybrid).

Used by `d2sCodecBridgeImplMemo`, `d2fOuterImpl`, `d2fProverRaw` (this file) and by
`KeyLemma.hybridGame` / `hybridGameDist` / inline `Hyb_i` `gImpl` realizations. -/
abbrev GImpl {κ : Type} (challengeSpec : OracleSpec κ) (M : Type) :=
  QueryImpl (gSpec (U := U) StmtIn pSpec δ)
    (StateT M
      (OptionT (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))))

variable {Salt : Type}

/-- CO25 §5.4 Eq. 16 LHS — type for the full `D2SAlgo^f(𝒫̃)` prover transform (Items 1-6).
- Inner prover `D2FQueryProver` runs `𝒫̃^{D2SQuery}` (outputs `τ ∈ Σ^δ`)
- Post-processing applies `τ̌ := bin(τ)` (outputs `τ̌ ∈ {0,1}^{δ⋆}`)
-/
abbrev D2SAlgoTransform :=
  MaliciousProver oSpec pSpec StmtIn U δ →
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt)

/-- Type for CO25 §5.8 line-4 trace maps (e.g. `D2STrace`, `(φ⁻¹, ψ)(tr)`).
Transforms a left-hand game query log into a basic-FS query log using
auxiliary uniform sampling. -/
abbrev D2STraceTransform {κ : Type} (challengeSpec : OracleSpec κ) :=
  QueryLog (oSpec + challengeSpec) →
    UnitSampleM U
      (QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))

end TransformTypes
