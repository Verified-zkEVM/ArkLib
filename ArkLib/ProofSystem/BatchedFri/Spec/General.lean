/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
public import ArkLib.ProofSystem.Fri.Spec.General

/-!
# ArkLib.ProofSystem.BatchedFri.Spec.General

The batching round parameterized by a proximity generator `G`, followed by the FRI reduction.
Independent coefficients, powers, and multilinear monomials differ only in their generator
and correlated-agreement error; the relations and FRI stage are shared.

## Status

`BatchedFri.Spec.batchedFRI_soundness` in `BatchedFri/EndToEnd.lean` proves the
composite ordinary soundness bound by sequential composition, and
`BatchedFri.Spec.batchedFRI_perfectCompleteness` proves perfect completeness at radius zero.
Composite knowledge soundness is out of scope
because the batching round has no extractor.
-/

@[expose] public section


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
  - `m`, one less than the number of batched input polynomials.
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l m : ℕ)
variable {S : Type} [Fintype S] [Nonempty S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable {ω : SmoothCosetFftDomain n F}

/-- The composite protocol starts with the batching round's correlated-agreement relation. -/
abbrev inputRelation (δ : ℝ≥0) :=
  BatchingRound.inputRelation (ω := ω) s d m δ


instance instBatchFRIreductionMessageOI : ∀ j,
  OracleInterface
    ((batchSpec S ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Message j) := fun j ↦ by
      apply instOracleInterfaceMessageAppend

instance instBatchFRIreductionChallengeOI : ∀ j,
  OracleInterface
    ((batchSpec S ++ₚ
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
    (BatchingRound.batchOracleReduction s d m G)
    (Fri.Spec.reduction (ω := ω) k s d dom_size_cond l)

end Spec

end BatchedFri
