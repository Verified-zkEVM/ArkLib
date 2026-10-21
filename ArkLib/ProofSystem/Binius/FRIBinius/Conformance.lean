/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Binius.FRIBinius.General
public import ArkLib.ProofSystem.RingSwitching.Packing.Conformance

/-!
# Binius batching conformance

The Binius batching phase specializes the shared DP24 conformance theorem at its tensor profile
and first-oracle compatibility relation. This does not identify Binius's separate sumcheck and
final verifiers with the shared DP24 verifiers.
-/

@[expose] public section

open Module MvPolynomial RingSwitching Sumcheck.Structured RingSwitching.Packing.Conformance

noncomputable section

namespace Binius.FRIBinius.Conformance

section Binius

open Binius.FRIBinius Binius.FRIBinius.FullFRIBinius

variable (κ : ℕ) [NeZero κ]
  (L : Type) [Field L] [Fintype L] [DecidableEq L]
  (K : Type) [Field K] [Fintype K]
  [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)] [Algebra K L]
  (β : Basis (Fin (2 ^ κ)) K L) {ℓ ℓ' 𝓡 ϑ : ℕ} [NeZero ℓ'] [NeZero ϑ]
  (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ) (h_l : ℓ = ℓ' + κ) [Fact (ϑ ∣ ℓ')]

omit [NeZero κ] in
/-- Batching acceptance at the tensor profile is equivalent to first-codeword compatibility,
the multiplier identity, the batched sum-check claim, and column reconstruction. -/
theorem binius_batching_conforms (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j)
    (z : (biniusProfile κ L K β).A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    (performCheckOriginalEvaluation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l stmt.original_claim
          stmt.t_eval_point z = true ∧
        ((acceptedStatement (biniusProfile κ L K β) stmt z c, oStmt), wit) ∈
          sumcheckRoundRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
            (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) 0) ↔
      Binius.BinaryBasefold.firstOracleWitnessConsistencyProp K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t'
          (Binius.BinaryBasefold.getFirstOracle K β oStmt) ∧
        wit.H.val = ((Packing.PackingData.ofBasis (biniusProfile κ L K β).basis).multiplier
          ((prefixLayout (biniusProfile κ L K β) ℓ').point
            (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point))
            (batchingWeight c)).val * wit.t'.val ∧
        (∑ u, batchingWeight c u * (biniusProfile κ L K β).decomposeRows z u, wit.t') ∈
          (Packing.PackingData.ofBasis (biniusProfile κ L K β).basis).sumcheckClaimRel ℓ'
            ((prefixLayout (biniusProfile κ L K β) ℓ').point
              (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point)) (batchingWeight c) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout (biniusProfile κ L K β) ℓ').weight
            (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point) v *
            (biniusProfile κ L K β).decomposeColumns z v :=
  batching_conforms (biniusProfile κ L K β) h_l
    (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) stmt oStmt z c wit

end Binius

end Binius.FRIBinius.Conformance

end
