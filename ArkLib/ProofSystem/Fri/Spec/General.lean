/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.ProofSystem.Fri.Spec.SingleRound

/-!
# Composition of the FRI oracle reduction

`pSpec` appends `k` non-final folding rounds, one final folding round, and a query round.
`reductionFold` retains the committed words and checks the final polynomial's degree;
`reduction` then checks folding consistency along the sampled query paths.

The input relation is the closed relative-Hamming ball of radius `δ` around evaluations
of the initial degree-bounded witness. The output relation compares the final polynomial
with the final witness. The corresponding soundness theorems are in
`ArkLib.ProofSystem.Fri.Spec.Soundness`.
-/

@[expose] public section

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ)
variable {ω : SmoothCosetFftDomain n F}

/-- The initial word is within relative Hamming distance `δ` of its polynomial witness. -/
def inputRelation (δ : ℝ≥0) :
    Set ((Statement (k := k) F 0 × (∀ j, OracleStatement (k := k) s ω 0 j)) ×
      Witness F s d (0 : Fin (k + 2))) :=
  match k with
  | 0 => FinalFoldPhase.inputRelation s (ω := ω) d (round_bound dom_size_cond) δ
  | .succ _ => FoldPhase.inputRelation s (ω := ω) d 0 (round_bound dom_size_cond) δ

/-- The final polynomial's evaluations are within distance `δ` of the final witness. -/
def outputRelation (δ : ℝ≥0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1))) :=
  QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ

/-- The sequence of non-final folding rounds. -/
@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec (ω := ω) s i)

/-- The complete FRI schedule: folding commitments, final polynomial, and query vector. -/
@[reducible]
def pSpec : ProtocolSpec ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) :=
  pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec (ω := ω) l

/- `OracleInterface` instance for `pSpecFold` and with the final folding round
   protocol specification appended to it. -/
instance : ∀ j, OracleInterface ((pSpecFold (ω := ω) k s).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Message j) :=
  instOracleInterfaceMessageAppend

instance : ∀ j, OracleInterface
    (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance :
    ∀ i, OracleInterface
          ((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ
            QueryRound.pSpec (ω := ω) l).Message i) :=
  instOracleInterfaceMessageAppend

instance :
    ∀ j,
      OracleInterface
        (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ
          QueryRound.pSpec (ω := ω) l)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- Commit all folded words and the final polynomial, checking the final degree bound. -/
@[reducible]
def reductionFold :
    OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement s ω)
      (Witness F s d (Fin.last (k + 1)))
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F) := OracleReduction.append
      (OracleReduction.seqCompose _ _ (fun (i : Fin (k + 1)) => Witness F s d i.castSucc)
        (FoldPhase.foldOracleReduction s (ω := ω) d))
      (FinalFoldPhase.finalFoldOracleReduction (k := k) s d)

/-- The complete FRI reduction, including the final query checks. -/
@[reducible]
def reduction :
    OracleReduction []ₒ
      (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
        (Witness F s d (0 : Fin (k + 2)))
      (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
      (pSpec k (ω := ω) s l) :=
  OracleReduction.append (reductionFold k s d)
    (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)

end Spec

end Fri
