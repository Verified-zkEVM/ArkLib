/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General


namespace BatchedFri

namespace Spec

open OracleSpec OracleComp ProtocolSpec NNReal BatchingRound

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
variable {ω : ReedSolomon.SmoothCosetFftDomain n F}

-- /- Input/Output relations for the Batched FRI protocol. -/
def inputRelation [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        Unit × (∀ j, OracleStatement m ω j) × (Witness F s d m)
      ) := sorry


/- Lifting FRI to include using `liftingLens`:
    - RLC in statement
    - Simulate batched polynomial oracle using oracles of
      batched polynomials
-/
def liftingLens :
  OracleContext.Lens
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (OracleStatement m ω) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.OracleStatement s ω 0) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1))) where
  stmt := Witness.InvLens.ofOutputOnly <| fun ⟨⟨cs, stmt⟩, ostmt⟩ =>
    ⟨
      stmt,
      fun j v =>
          have : v.1 ∈ ω.toFinset := by {
            rw [ReedSolomon.CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] 
            rcases j with ⟨j, h⟩
            have : j = 0 := by simpa using h
            simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceAdd,
              Fin.ofNat_eq_cast, Fin.val_natCast] at v
            rcases v with ⟨v, h'⟩
            simp only
            subst this
            simp only [finRangeTo.eq_1, List.take_zero, List.toFinset_nil, Finset.sum_empty,
              Nat.sub_zero, ReedSolomon.CosetFftDomain.subdomainNatReversed,
              ReedSolomon.CosetFftDomain.subdomainNat, Nat.succ_eq_add_one, Fin.ofNat_eq_cast] at h'
            rw [ReedSolomon.CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at h'            
            rw [←ReedSolomon.CosetFftDomain.subdomain_n']
            exact (ReedSolomon.CosetFftDomain.mem_subdomain_of_eq_vals (by simp)).1 h'
          }
          (ostmt 0) ⟨v.1, this⟩ + ∑ j, cs j * ostmt j.succ ⟨v.1, this⟩
    ⟩
  wit  := Witness.Lens.id

noncomputable def liftedFRI [DecidableEq F] :
  OracleReduction []ₒ
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
      (OracleStatement m ω) (Fri.Spec.Witness F s d 0)
    (Fri.Spec.FinalStatement F k)
      (Fri.Spec.FinalOracleStatement s ω) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (
      Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
      Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
      Fri.Spec.QueryRound.pSpec (ω := ω) l
    ) :=
    OracleReduction.liftContext
      (liftingLens k s d m)
      (Fri.Spec.reduction k s d dom_size_cond l)

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
noncomputable def batchedFRIreduction [DecidableEq F]
 :=
  OracleReduction.append
    (BatchingRound.batchOracleReduction s d m)
    (liftedFRI (ω := ω) k s d dom_size_cond l m)

end Spec

end BatchedFri
