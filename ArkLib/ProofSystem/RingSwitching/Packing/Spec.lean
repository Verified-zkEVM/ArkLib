/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.Spec

Definitions and results for this component of ArkLib.
-/

namespace RingSwitching

/-!
# Wire formats of the interactive packing reduction

The transcript shape of the interactive `Packing` reduction, phase by phase, together
with the `OracleInterface`/`SampleableType` instances the oracle-reduction framework needs:

* `pSpecBatching` — the batching round: one carrier message, one batching-vector challenge
  (the family-shared message-then-scalar-challenge wire at `Msg := P.A`, `C := Fin κ → L`);
* `pSpecSumcheckLoop` — `ℓ'` copies of the structured single sumcheck round (degree-generic
  in `WithDegree` form; the reduction pins degree 2);
* `pSpecFinalSumcheck` — the closing round: one constant from the prover, no challenge (the
  family-shared one-message wire `pSpecMessage` at `Msg := L`);
* their sequential compositions, up to `fullPspec` — the whole reduction followed by the
  downstream opening protocol's own wire.
-/

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
open scoped NNReal
open Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

section Pspec

/-- The batching-phase wire format: the prover sends the carrier element `ŝ ∈ P.A`, the
verifier replies with the batching scalars `r'' ∈ L^κ`. This is the generic
message-then-scalar-challenge round `CoordinateWise.ScalarRound.pSpecScalar` at
`Msg := P.A`, `C := Fin κ → L` — the same wire format the committed-scalar seam
(`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`) and the
Hachi `Lift` instance use at `Msg := TCom`, `C := F`. The verifier of this
round is an instance of the family-shared check-then-update shape on this wire
(`RingSwitching.scalarRoundOracleVerifier`, `../RoundVerifiers.lean`). -/
@[reducible]
def pSpecBatching : ProtocolSpec 2 :=
  CoordinateWise.ScalarRound.pSpecScalar P.A (Fin κ → L)

-- `pSpecSumcheckRound` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` as a
-- degree-neutral spec. The `WithDegree` names expose the reusable protocol shape; the historical
-- Binius ring-switching names below pin `d := 2`.
abbrev pSpecSumcheckRoundWithDegree (L : Type) [Semiring L] (d : ℕ) : ProtocolSpec 2 :=
  Sumcheck.Structured.pSpecSumcheckRound L d

abbrev pSpecSumcheckRound (L : Type) [Semiring L] : ProtocolSpec 2 :=
  pSpecSumcheckRoundWithDegree L 2

@[reducible]
def pSpecSumcheckLoopWithDegree (d : ℕ) :=
  ProtocolSpec.seqCompose (fun (_: Fin ℓ') => pSpecSumcheckRoundWithDegree L d)

@[reducible]
def pSpecSumcheckLoop := pSpecSumcheckLoopWithDegree L ℓ' 2

/-- Final-step wire: one constant `c ∈ L` from the prover, no challenge — the family-shared
one-message wire `RingSwitching.pSpecMessage` at `Msg := L` (`RoundVerifiers.lean`). -/
@[reducible]
def pSpecFinalSumcheck : ProtocolSpec 1 := pSpecMessage L

@[reducible]
def pSpecCoreInteractionWithDegree (d : ℕ) :=
  (pSpecSumcheckLoopWithDegree L ℓ' d) ++ₚ (pSpecFinalSumcheck L)

@[reducible]
def pSpecCoreInteraction := pSpecCoreInteractionWithDegree L ℓ' 2

@[reducible]
def pSpecLargeFieldReduction :=
  (pSpecBatching κ L K P) ++ₚ (pSpecCoreInteraction (L:=L) (ℓ':=ℓ'))

@[reducible]
def fullPspec := (pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')) ++ₚ (mlIOPCS.pSpec)

/-! ## Oracle Interface instances for Messages-/

instance : OracleInterface P.A := OracleInterface.instDefault
instance : OracleInterface (Fin κ → L) := OracleInterface.instDefault

-- The message interface of `pSpecBatching` is the generic `pSpecScalar` instance from
-- `CoordinateWise.ScalarRound`, fed by `OracleInterface P.A` above. Keeping the generic
-- instance (rather than a hand-written per-index one) lets the batching verifier be stated
-- through the family-shared `scalarRoundOracleVerifier` without instance mismatches.

-- The `OracleInterface` instance for `pSpecSumcheckRound.Message` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` along with the spec itself.
-- Anonymous instances are looked up globally regardless of namespace, so no shim is needed.

instance {d : ℕ} : ∀ j,
    OracleInterface ((pSpecSumcheckLoopWithDegree (L := L) ℓ' d).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface ((pSpecSumcheckLoop (L := L) ℓ').Message j) :=
  instOracleInterfaceMessageSeqCompose

-- The message interface of `pSpecFinalSumcheck` is the canonical in-the-clear instance of
-- the one-message wire `pSpecMessage` (`RingSwitching/RoundVerifiers.lean`).

instance {d : ℕ} : ∀ i,
    OracleInterface ((pSpecCoreInteractionWithDegree (L:=L) (ℓ':=ℓ') d).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface (mlIOPCS.pSpec.Message i) := fun i => mlIOPCS.Oₘ i

instance : ∀ i, OracleInterface ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Message i) :=
  instOracleInterfaceMessageAppend

/-! ## SampleableType instances -/

-- The challenge sampler of `pSpecBatching` is the generic `pSpecScalar` instance from
-- `CoordinateWise.ScalarRound`, fed by `SampleableType (Fin κ → L)` (`instSampleableTypeFinFunc`).

-- The `SampleableType` instance for `pSpecSumcheckRound.Challenge` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`. Anonymous instances are looked up
-- globally, so no shim is needed.

instance {d : ℕ} : ∀ j,
    SampleableType ((pSpecSumcheckLoopWithDegree (L := L) ℓ' d).Challenge j) :=
  instSampleableTypeChallengeSeqCompose

instance : ∀ j, SampleableType ((pSpecSumcheckLoop (L := L) ℓ').Challenge j) :=
  instSampleableTypeChallengeSeqCompose

-- `pSpecFinalSumcheck` has no challenges; the empty `SampleableType` instance comes with
-- `pSpecMessage` (`RingSwitching/RoundVerifiers.lean`).

instance {d : ℕ} : ∀ i,
    SampleableType ((pSpecCoreInteractionWithDegree (L:=L) (ℓ':=ℓ') d).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

instance : ∀ i, SampleableType ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Challenge i) :=
  instSampleableTypeChallengeAppend

end Pspec

end
end RingSwitching
