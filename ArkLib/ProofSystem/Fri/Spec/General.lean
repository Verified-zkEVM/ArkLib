/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound

namespace Fri

open OracleSpec OracleComp ProtocolSpec Domain NNReal

namespace Spec

/- FRI parameters:
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
-/
variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ)

/- Input/Output relations for the FRI protocol. -/
def inputRelation [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement (k := k) F 0 × (∀ j, OracleStatement (k := k) D x s 0 j)) ×
        Witness F s d (0 : Fin (k + 2))
      ) :=
  match k with
  | 0 => FinalFoldPhase.inputRelation D x s d (round_bound dom_size_cond) δ
  | .succ _ => FoldPhase.inputRelation D x s d 0 (round_bound dom_size_cond) δ

def outputRelation [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := QueryRound.outputRelation D x s d (round_bound dom_size_cond) δ

/- Protocol spec for the combined non-final folding rounds of the FRI protocol. -/
@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec D x s i)

/- `OracleInterface` instance for `pSpecFold` and with the final folding round
   protocol specification appended to it. -/
instance : ∀ j, OracleInterface ((pSpecFold D x k s).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface (((pSpecFold D x k s ++ₚ FinalFoldPhase.pSpec F)).Message j) :=
  instOracleInterfaceMessageAppend

instance :
    ∀ i, OracleInterface
          ((pSpecFold D x k s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec D x l).Message i) :=
  instOracleInterfaceMessageAppend

/- Oracle reduction for all folding rounds of the FRI protocol -/
@[reducible]
noncomputable def reductionFold :
  OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement D x s (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement D x s)
      (Witness F s d (Fin.last (k + 1)))
    (pSpecFold D x k s ++ₚ FinalFoldPhase.pSpec F)
 := OracleReduction.append
      (OracleReduction.seqCompose _ _ (fun (i : Fin (k + 1)) => Witness F s d i.castSucc)
        (FoldPhase.foldOracleReduction D x s d))
      (FinalFoldPhase.finalFoldOracleReduction D x (k := k) s d)

/- Oracle reduction of the FRI protocol. -/
@[reducible]
noncomputable def reduction [DecidableEq F] :
  OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement D x s (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement D x s) (Witness F s d (Fin.last (k + 1)))
    (pSpecFold D x k s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec D x l) :=
  OracleReduction.append (reductionFold D x k s d)
    (QueryRound.queryOracleReduction (k := k) D x s d dom_size_cond l)

end Spec

end Fri
