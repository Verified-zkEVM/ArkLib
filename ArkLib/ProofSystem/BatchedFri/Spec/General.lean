/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General

/-!
# ArkLib.ProofSystem.BatchedFri.Spec.General

Definitions and results for this component of ArkLib.
-/


namespace BatchedFri

namespace Spec

open OracleSpec OracleComp ProtocolSpec NNReal BatchingRound Domain

/- Batched FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
  - `m`, number of batched polynomials.
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l m : ℕ)
variable {ω : SmoothCosetFftDomain n F}

-- /- Input/Output relations for the Batched FRI protocol. -/
def inputRelation (δ : ℝ≥0) :
    Set
      (
        Unit × (∀ j, OracleStatement m ω j) × (Witness F s d m)
      ) := sorry


instance instBatchFRIreductionMessageOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Message j) := fun j ↦ by
      apply instOracleInterfaceMessageAppend

instance instBatchFRIreductionChallengeOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/- Oracle reduction of the batched FRI protocol. -/
@[reducible]
def batchedFRIreduction :=
  OracleReduction.append
    (BatchingRound.batchOracleReduction s d m)
    (Fri.Spec.reduction (ω := ω) k s d dom_size_cond l)

end Spec

end BatchedFri
