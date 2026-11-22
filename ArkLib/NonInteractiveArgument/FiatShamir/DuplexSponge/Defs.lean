/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Devon Tuma
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Codec
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Sponge
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Construction
public import VCVio.OracleComp.Constructions.UniformPreimage
public import ArkLib.OracleReduction.Security.OracleSampling
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Duplex-sponge Fiat–Shamir oracle and payload interfaces

This module describes the ideal hash and permutation oracles, the NARG payload, and
the oracle interfaces used by the DSFS security reductions. The prover and verifier
are defined in `Construction.lean`.
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

/-!
## Block-count notation ([CO25, Equations 7–8])

`L_δ`, `L_P(i)`, `L_V(i)`, `L_P`, `L_V`, `L` from the paper. -/
section BlockCountNotation

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize U]
    [HasProverMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (proverMessageSize i))]
    [HasVerifierMessageSize pSpec]
    [∀ i, Deserialize (pSpec.Challenge i) (Vector U (verifierMessageSize i))]

/-- **[CO25, Eq. (7)]** `L_δ = ⌈δ / r⌉`: number of rate blocks needed for a salt of size `δ`. -/
def numSaltBlocks (δ : Nat) : Nat := Nat.ceil ((δ : ℚ) / SpongeSize.R U)

/-- **[CO25, Eq. (7)]** Rate-block budget for absorbing the `i`-th encoded
  prover message: `L_P(i) = ⌈ℓ_P(i) / r⌉`, where `r` is the sponge rate. -/
def numPermQueriesProverMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((proverMessageSize i : ℚ) / SpongeSize.R U)

alias Lₚᵢ := numPermQueriesProverMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for absorbing encoded
  prover messages: `L_P = ∑ᵢ ⌈ℓ_P(i) / r⌉`. -/
def totalNumPermQueriesProverMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ (U := U) i

alias Lₚ := totalNumPermQueriesProverMessage

/-- **[CO25, Eq. (7)]** Rate-block budget for squeezing the `i`-th encoded verifier message:
  `L_V(i) = ⌈ℓ_V(i) / r⌉`, where `r` is the sponge rate. -/
def numPermQueriesVerifierMessage (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((verifierMessageSize i : ℚ) / SpongeSize.R U)

alias Lᵥᵢ := numPermQueriesVerifierMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for squeezing encoded verifier messages:
  `L_V = ∑ᵢ ⌈ℓ_V(i) / r⌉`. -/
def totalNumPermQueriesVerifierMessage : Nat :=
  ∑ i, pSpec.Lᵥᵢ (U := U) i

alias Lᵥ := totalNumPermQueriesVerifierMessage

/-- **[CO25, Eq. (8)]** Total rate-block budget for absorbing prover messages and squeezing
  verifier messages of the protocol specification. This is `L_P + L_V` in
  the paper's block-count notation and its `L` in Equation (8). The salt-inclusive budget
  used here is `L_totalRateBlocks = L_δ + L_P + L_V`. -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesProverMessage (U := U) +
    pSpec.totalNumPermQueriesVerifierMessage (U := U)

alias L := totalNumPermQueries

end BlockCountNotation

/-- Salt-inclusive upper bound on the verifier's permutation queries in Section 5:
`L_totalRateBlocks = L_δ + L_P + L_V = ⌈δ / r⌉ + L_P + L_V`. This includes salt absorption,
whereas the paper's Equation (8) defines `L = L_P + L_V`, the protocol-only sum
`totalNumPermQueries`. This sum is conservative: the salt and first prover message may share
a rate block. -/
def L_totalRateBlocks {n : ℕ} {U : Type} [SpongeSize U] (δ : Nat) (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] : Nat :=
  numSaltBlocks (U := U) δ + pSpec.totalNumPermQueries (U := U)

/-- With no salt, the total block budget consists only of protocol message blocks. -/
@[simp] theorem L_totalRateBlocks_zero {n : ℕ} {U : Type} [SpongeSize U] (pSpec : ProtocolSpec n)
    [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec] :
    L_totalRateBlocks (U := U) 0 pSpec = pSpec.totalNumPermQueries (U := U) := by
  simp [L_totalRateBlocks, numSaltBlocks]

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize U]
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
    ProbComp (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id) :=
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
- `h : ByteArray → Vector U (SpongeSize.C U)`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U (SpongeSize.N U) → Vector U (SpongeSize.N U)`
is the forward direction of the random permutation
- `p⁻¹ : Vector U (SpongeSize.N U) → Vector U (SpongeSize.N U)`
is the backward direction of the random permutation
-/
@[reducible]
def duplexSpongeOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize U] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U (SpongeSize.C U)) + permutationOracle (CanonicalSpongeState U)

/-- **[CO25, Definition 5.2]** The type of a single entry in a duplex sponge query trace -/
abbrev duplexSpongeTraceEntry {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize U] :=
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
def dsHashQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize U]
    (stmt : StartType) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inl stmt

/-- **[CO25, §5.4]** Paper `p(s_in)` — permutation query index. -/
@[match_pattern, reducible]
def dsPermQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize U]
    (stateIn : CanonicalSpongeState U) :
    StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U :=
  Sum.inr (Sum.inl stateIn)

/-- **[CO25, §5.4]** Paper `p⁻¹(s_out)` — inverse permutation query index. -/
@[match_pattern, reducible]
def dsPermInvQuery {StartType : Type} {U : Type} [SpongeUnit U] [SpongeSize U]
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
def duplexSpongeForwardOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize U] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U (SpongeSize.C U)) + forwardPermutationOracle (CanonicalSpongeState U)

section OracleDistribution

/-- One sampled realization of the DSFS ideal oracle distribution `𝒟_𝔖`:
a random function `h : StartType → Σ^c` and a random permutation `p : Σ^{r+c} → Σ^{r+c}`.
The inverse oracle `p⁻¹` is *derived* as `p.symm`, not sampled — the bijection invariant
`p ∘ p⁻¹ = id` holds by construction since the carrier is `Equiv.Perm`. -/
abbrev DuplexSpongeOracleFamily (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize U] :=
  (QueryImpl (StartType →ₒ Vector U (SpongeSize.C U)) Id) ×
    Equiv.Perm (CanonicalSpongeState U)

/-- **[CO25, Definition 4.3]** Interpret one sampled `𝒟_𝔖` realization as the concrete `(h, p, p⁻¹)`
query implementation. -/
@[reducible]
def duplexSpongeOracleQueryImpl
    {StartType U : Type} [SpongeUnit U] [SpongeSize U]
    (realization : DuplexSpongeOracleFamily StartType U) :
    QueryImpl (duplexSpongeOracle StartType U) ProbComp
  | Sum.inl qHash => pure (realization.1 qHash)
  | Sum.inr (Sum.inl state) => pure (realization.2 state)
  | Sum.inr (Sum.inr state) => pure (realization.2.symm state)

/-- **[CO25, Definition 4.3]** Answer using the initially sampled pair `(h, p) ← 𝒟_𝔖` throughout the
experiment. Hash queries use `h`, forward queries use `p`, and inverse queries use `p.symm`. The
pair is read but never modified: this handler does not sample a new oracle. -/
def D_𝔖.answer {StartType U : Type} [SpongeUnit U] [SpongeSize U] :
    QueryImpl (duplexSpongeOracle StartType U)
      (StateT (DuplexSpongeOracleFamily StartType U) ProbComp) := fun q => do
  let realization ← get
  StateT.lift (duplexSpongeOracleQueryImpl realization q)

/-- **[CO25, Construction 4.4]** Oracle implementation with stateless ambient queries.
The sampled sponge realization is shared and unchanged throughout the execution. -/
def D_𝔖.withOracle {ι : Type} {oSpec : OracleSpec ι} {StartType U : Type}
    [SpongeUnit U] [SpongeSize U] (oSpecImpl : QueryImpl oSpec ProbComp) :
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
theorem D_𝔖.answer_run {StartType U : Type} [SpongeUnit U] [SpongeSize U]
    (realization : DuplexSpongeOracleFamily StartType U)
    (q : (duplexSpongeOracle StartType U).Domain) :
    (D_𝔖.answer q).run realization =
      match q with
      | Sum.inl x => pure (realization.1 x, realization)
      | Sum.inr (Sum.inl s) => pure (realization.2 s, realization)
      | Sum.inr (Sum.inr s) => pure (realization.2.symm s, realization) := by
  rcases q with x | s | s <;>
    simp [D_𝔖.answer, duplexSpongeOracleQueryImpl]

/-- `CanonicalSpongeState U = Vector U (SpongeSize.N U)` is `VCVCompatible` whenever `U` is.
Needed so `VCVCompatible U` implies `SampleableType (Equiv.Perm (CanonicalSpongeState U))`. -/
instance instVCVCompatibleCanonicalSpongeState
    {U : Type} [SpongeUnit U] [SpongeSize U] [VCVCompatible U] :
    VCVCompatible (CanonicalSpongeState U) :=
  (inferInstance : VCVCompatible (Vector U (SpongeSize.N U)))

/-- **[CO25, Definition 4.3]** Uniform random-function distribution for the `h` component of
`𝒟_𝔖`. -/
noncomputable def duplexSpongeHashOracleDistribution (StartType U : Type) [SpongeUnit U]
    [SpongeSize U] [VCVCompatible StartType] [VCVCompatible U] :
    (ProbComp (QueryImpl (StartType →ₒ Vector U (SpongeSize.C U)) Id)) :=
  OracleReduction.sampleRandomOracleTable (instSampleable := OracleReduction.sampleableTypePiVCV)

/-- **[CO25, Definition 4.3]** Uniform random-permutation distribution for the `(p, p⁻¹)` component
of `𝒟_𝔖`.

Only `p` is sampled; `p⁻¹` is derived as `p.symm`. -/
noncomputable def duplexSpongePermutationOracleDistribution (U : Type) [SpongeUnit U] [SpongeSize U]
    [VCVCompatible U] :
    ProbComp (Equiv.Perm (CanonicalSpongeState U)) :=
  uniformSample _ (h := VCVCompatible.toSampleableTypePerm)

/-- **[CO25, Definition 4.3]** Ideal duplex-sponge oracle distribution `𝒟_𝔖`.

Samples `h` as a uniform random function and `p` as a uniform random permutation, then answers
inverse-permutation queries using `p.symm`. -/
noncomputable def D_𝔖.sample (StartType U : Type) [SpongeUnit U] [SpongeSize U]
    [VCVCompatible StartType] [VCVCompatible U] :
    ProbComp (DuplexSpongeOracleFamily StartType U) := do
  let h ← duplexSpongeHashOracleDistribution StartType U
  let p ← duplexSpongePermutationOracleDistribution U
  pure (h, p)

/-- Supporting lemma for **[CO25, Definition 4.3]**: `D_𝔖.sample` samples `h` and `p` uniformly. -/
@[simp]
lemma D_𝔖.sample_eq
    (StartType U : Type) [SpongeUnit U] [SpongeSize U]
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
  {U : Type} [SpongeUnit U] [SpongeSize U]
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
    (StmtIn U : Type) [SpongeUnit U] [SpongeSize U] (δ : ℕ) :=
  OracleComp (oSpec + duplexSpongeOracle StmtIn U)
    (StmtIn × DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)

end SaltedInterfaces

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
  {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize U]
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
  `fsVerifierMessageOracle (StmtIn × Salt) pSpec` per-hybrid).

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
      D2SVerifierMessagePlusUnitOracle (U := U) (fsVerifierMessageOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedNARGString pSpec Salt)

/-- **[CO25, Lemma 5.1]** Type of the §5.8 line-4 trace maps (e.g. `D2STrace`, `(φ⁻¹, ψ)(tr)`).
Transforms a left-hand game query log into a basic-FS query log using
auxiliary uniform sampling. -/
abbrev D2STraceTransform {κ : Type} (verifierMessageSpec : OracleSpec κ) :=
  TaggedQueryLog (oSpec + verifierMessageSpec) →
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec))

end TransformTypes
