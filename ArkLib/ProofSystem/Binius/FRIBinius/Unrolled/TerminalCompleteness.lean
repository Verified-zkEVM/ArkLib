/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Terminal
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic

/-!
# Honest fused terminal check

At the end of the folding loop the honest word is constant. The residual product-sumcheck
equation implies the fused guard directly, including when its multiplier evaluates to zero.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Terminal

open Binius.BinaryBasefold MvPolynomial AdditiveNTT
open OracleComp ProtocolSpec

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R : ℕ} [NeZero ℓ] [NeZero R] {h_rate : ℓ + R < r}
variable {Context : Type}
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)

omit [NeZero ℓ] in
/-- The honest last-round scalar passes the fused guard for any public multiplier. -/
theorem check_honest (𝓑 : Fin 2 ↪ L)
    (s : Statement (L := L) Context (Fin.last ℓ))
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (hsum : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) s.sumcheck_target w.H)
    (hstruct : WitnessStructuralInvariant K β (h_ℓ_add_R_rate := h_rate)
      (multpoly := multiplier.polynomial) s w) :
    check multiplier.evaluate s (w.f ⟨0, by simp only [zero_mem]⟩) := by
  classical
  unfold sumcheckConsistencyProp at hsum
  simp only [Fin.val_last] at hsum
  rw [Finset.sum_eq_single_of_mem (a := fun _ => 0)
    (by
      simp only [SumcheckDomain.mem_cube]
      intro i
      have hi := i.isLt
      omega)
    (fun b _ hb => (hb (by funext i; have hi := i.isLt; omega)).elim)] at hsum
  have hc : w.f ⟨0, by simp only [zero_mem]⟩ = w.t.val.eval s.challenges := by
    rw [hstruct.2]
    exact congr_fun (iteratedFold_to_level_ℓ_eval K β (h_ℓ_add_R_rate := h_rate)
      (t := w.t) (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last]) (challenges := s.challenges))
      ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [hstruct.1, Sumcheck.Structured.eval_projectToMidSumcheckPoly_last] at hsum
  unfold check
  rw [multiplier.evaluate_eq, hc]
  exact hsum

variable {ϑ : ℕ} [NeZero ϑ] [Fact (ϑ ∣ ℓ)]
variable (outputContext : Context → SumcheckBaseContext L ℓ)

/-- The honest prover sends the value of its fully folded word at zero. -/
def prover : OracleProver ([]ₒ)
    (Statement (L := L) Context (Fin.last ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    Unit (pSpecFinalSumcheckStep (L := L)) where
  PrvState _ :=
    (Statement (L := L) Context (Fin.last ℓ) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)) ×
      Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ)
  input := id
  sendMessage
  | ⟨0, _⟩ => fun s => pure (s.2.f ⟨0, by simp only [zero_mem]⟩, s)
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  output s := pure ((output outputContext s.1.1 (s.2.f ⟨0, by simp only [zero_mem]⟩), s.1.2), ())

/-- The fused terminal reduction, with an executable scalar-message prover. -/
def reduction [DecidableEq K] := OracleReduction.mk
  (prover K β outputContext (ϑ := ϑ) (h_rate := h_rate))
  (verifier K β multiplier.evaluate outputContext)

/-- Strict last-round consistency implies the strict output folding relation consumed by
the query phase. This property is independent of the public multiplier. -/
theorem strict_output_of_honest
    (s : Statement (L := L) Context (Fin.last ℓ))
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (hw : w.f = getMidCodewords K β w.t s.challenges)
    (ho : StrictOracleFoldingConsistent K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (i := Fin.last ℓ) (t := w.t) (challenges := s.challenges) (oStmt := ost)) :
    ((output outputContext s (w.f ⟨0, by simp only [zero_mem]⟩), ost), ()) ∈
      strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) := by
  refine ⟨w.t, ho, ?_⟩
  funext y
  exact iteratedFold_lastOracle_eq_finalConstant K β s w ost hw ho y

/-- Perfect completeness of the fused terminal reduction from the strict last-round relation. -/
theorem perfectCompleteness [DecidableEq K] [SampleableType L] (𝓑 : Fin 2 ↪ L)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (reduction K β multiplier outputContext (ϑ := ϑ) (h_rate := h_rate)).perfectCompleteness
      init impl
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) := by
  classical
  apply Reduction.perfectCompleteness_of_guarded_prover_support _
    (guardedForm K β multiplier.evaluate outputContext)
  intro ⟨s, ost⟩ w hin q hq
  let c : L := w.f ⟨0, by simp only [zero_mem]⟩
  have hp : (prover K β outputContext (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) w =
      pure (((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c),
        ((output outputContext s c, ost), ())) := rfl
  change q ∈ support ((prover K β outputContext).run (s, ost) w) at hq
  rw [hp] at hq
  have heq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  obtain ⟨hsum, hstruct, horacles⟩ := hin
  refine ⟨?_, ?_, rfl⟩
  · change decide (s.sumcheck_target = multiplier.evaluate s.ctx s.challenges * c) = true
    exact decide_eq_true (check_honest K β multiplier 𝓑 s w hsum hstruct)
  · exact strict_output_of_honest K β outputContext s w ost hstruct.2 horacles

end Binius.FRIBinius.Unrolled.Terminal
