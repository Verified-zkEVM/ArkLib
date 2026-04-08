/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal

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
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ)
variable {ω : ReedSolomon.SmoothCosetFftDomain n F}

/- Input/Output relations for the FRI protocol. -/
def inputRelation [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement (k := k) F 0 × (∀ j, OracleStatement (k := k) s ω 0 j)) ×
        Witness F s d (0 : Fin (k + 2))
      ) :=
  match k with
  | 0 => FinalFoldPhase.inputRelation s (ω := ω) d (round_bound dom_size_cond) δ
  | .succ _ => FoldPhase.inputRelation s (ω := ω) d 0 (round_bound dom_size_cond) δ

def outputRelation [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ

/- Protocol spec for the combined non-final folding rounds of the FRI protocol. -/
@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec (ω := ω) s i)

/- `OracleInterface` instance for `pSpecFold` and with the final folding round
   protocol specification appended to it. -/
instance : ∀ j, OracleInterface ((pSpecFold (ω := ω) k s).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Message j) :=
  instOracleInterfaceMessageAppend

instance : ∀ j, OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance :
    ∀ i, OracleInterface
          ((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec (ω := ω) l).Message i) :=
  instOracleInterfaceMessageAppend

instance :
    ∀ j,
      OracleInterface
        (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec (ω := ω) l)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/- Oracle reduction for all folding rounds of the FRI protocol -/
@[reducible]
noncomputable def reductionFold :
  OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement s ω)
      (Witness F s d (Fin.last (k + 1)))
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)
 := OracleReduction.append
      (OracleReduction.seqCompose _ _ (fun (i : Fin (k + 1)) => Witness F s d i.castSucc)
        (FoldPhase.foldOracleReduction s (ω := ω) d))
      (FinalFoldPhase.finalFoldOracleReduction (k := k) s d)

/- Oracle reduction of the FRI protocol. -/
@[reducible]
noncomputable def reduction [DecidableEq F] :
  OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec l (ω := ω)) :=
  OracleReduction.append (reductionFold k s d)
    (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)

end Spec

end Fri
