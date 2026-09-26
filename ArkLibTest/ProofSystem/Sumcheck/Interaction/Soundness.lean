/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Elias Judin
-/
import Mathlib.Algebra.Field.ZMod
import ArkLib.ProofSystem.Sumcheck.Interaction.Soundness
import ArkLibTest.ProofSystem.Sumcheck.Interaction.SingleRound

/-! # Adversarial closed-output regression tests

The false claim for `X` on `[0]` is supported by the cheating constant message `1`.
It passes the sum check, but produces a true closed output only at challenge `1`.
-/

namespace Sumcheck.Interaction.SingleRound.Test

open OracleComp Polynomial

noncomputable section

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A cheating message whose sum equals the false target. -/
def cheating : Message (ZMod 17) 1 :=
  ⟨1, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- The input behavior, rather than the sent message, decides the closed relation. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 1 0).closed.map
    (closedOutputRelation (ZMod 17) 1) ≠ some True := by
  rw [ne_eq, committedRun_true_iff]
  simp [polynomial, cheating]

/-- Collision at one challenge really does fool this round. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 1 1).closed.map
    (closedOutputRelation (ZMod 17) 1) = some True := by
  rw [committedRun_true_iff]
  simp [polynomial, cheating]

/-- The actual executor, with a false input claim, obeys the nonvacuous field bound. -/
example : Pr{let run ←
    executeCommitted (ZMod 17) 1 ($ᵗ (ZMod 17)) polynomial cheating [0] 1}[
      run.closed.map (closedOutputRelation (ZMod 17) 1) = some True] ≤
      (1 : ENNReal) / 17 := by
  simpa using executeCommitted_soundness (ZMod 17) 1 polynomial cheating [0] 1
    (by simp [polynomial])

/-- A rejected message produces no output even at a collision challenge. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 2 1).closed = none := by
  apply committedRun_rejects
  simpa [cheating] using (show (1 : ZMod 17) ≠ 2 by decide)

namespace BooleanControls

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The fixed true polynomial in the false-target controls. -/
def zeroPolynomial (deg : ℕ) : Message (ZMod 5) deg :=
  ⟨0, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- This message passes the Boolean endpoint check for the false target one. -/
def linearPolynomial : Message (ZMod 5) 1 :=
  ⟨X, Polynomial.mem_degreeLE.mpr Polynomial.degree_X_le⟩

/-- A failed endpoint check is an actual rejection with probability one. -/
theorem rejection_probability :
    Pr{let run ←
      executeCommitted (ZMod 5) 1 ($ᵗ (ZMod 5))
        (zeroPolynomial 1) (zeroPolynomial 1) [0, 1] 1}[run.closed = none] = 1 := by
  rw [executeCommitted_eq, prEvent_map]
  have h (r : ZMod 5) :
      (committedRun (ZMod 5) 1 (zeroPolynomial 1) (zeroPolynomial 1) [0, 1] 1 r).closed =
        none := committedRun_rejects _ _ _ _ _ _ _ (by simp [zeroPolynomial])
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr h

/-- Exactly the challenge zero repairs this false Boolean-domain claim. -/
theorem exact_repair_probability :
    Pr{let run ←
      executeCommitted (ZMod 5) 1 ($ᵗ (ZMod 5))
        (zeroPolynomial 1) linearPolynomial [0, 1] 1}[
        run.closed.map (closedOutputRelation (ZMod 5) 1) = some True] = (1 : ENNReal) / 5 := by
  rw [executeCommitted_eq, prEvent_map]
  have hevent (r : ZMod 5) :
      (committedRun (ZMod 5) 1 (zeroPolynomial 1) linearPolynomial [0, 1] 1 r).closed.map
        (closedOutputRelation (ZMod 5) 1) = some True ↔ 0 = r := by
    rw [committedRun_true_iff]
    simp [zeroPolynomial, linearPolynomial]
  rw [prEvent_congr ($ᵗ (ZMod 5)) _ _ hevent, SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun r : ZMod 5 => 0 = r)).card = 1 := by decide
  simp [hcard]

/-- The message carrier excludes a quadratic from a degree-one round. -/
theorem excludes_quadratic (q : Message (ZMod 5) 1) : q.val ≠ X ^ 2 := by
  intro h
  have hdegree := Polynomial.natDegree_le_of_degree_le (message_degree (ZMod 5) 1 q)
  rw [h] at hdegree
  norm_num at hdegree

/-- A message selected after seeing the challenge can pass and hit zero at that challenge. -/
def adaptivePolynomial (r : ZMod 5) : Message (ZMod 5) 2 :=
  if r = 1 then ⟨1 - X, Polynomial.mem_degreeLE.mpr (by
    apply Polynomial.degree_le_of_natDegree_le
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp))⟩
  else ⟨C (1 - r)⁻¹ * (X * (X - C r)), Polynomial.mem_degreeLE.mpr (by
    apply Polynomial.degree_le_of_natDegree_le
    apply (Polynomial.natDegree_mul_le).trans
    simp only [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_mul_le).trans
    simp)⟩

/-- Every adaptive message passes the same false endpoint claim. -/
theorem adaptive_endpoints (r : ZMod 5) :
    (adaptivePolynomial r).val.eval 0 + (adaptivePolynomial r).val.eval 1 = 1 := by
  by_cases h : r = 1
  · simp [adaptivePolynomial, h]
  · simp [adaptivePolynomial, h, sub_ne_zero.mpr (Ne.symm h)]

/-- Every adaptive message agrees with the true polynomial at the known challenge. -/
theorem adaptive_hits (r : ZMod 5) : (adaptivePolynomial r).val.eval r = 0 := by
  by_cases h : r = 1 <;> simp [adaptivePolynomial, h]

/-- Reversing the sampling order yields success one through the actual executor. -/
theorem challenge_first_probability :
    Pr{let run ←
      ($ᵗ (ZMod 5)) >>= fun r => executeCommitted (ZMod 5) 2 (pure r)
        (zeroPolynomial 2) (adaptivePolynomial r) [0, 1] 1}[
        run.closed.map (closedOutputRelation (ZMod 5) 2) = some True] = 1 := by
  have hprogram :
      (($ᵗ (ZMod 5)) >>= fun r => executeCommitted (ZMod 5) 2 (pure r)
        (zeroPolynomial 2) (adaptivePolynomial r) [0, 1] 1) =
      (fun r => committedRun (ZMod 5) 2 (zeroPolynomial 2) (adaptivePolynomial r)
        [0, 1] 1 r) <$> ($ᵗ (ZMod 5)) := by
    simp only [executeCommitted_eq, map_pure, bind_pure_comp]
  rw [hprogram, prEvent_map]
  have hevent (r : ZMod 5) :
      (committedRun (ZMod 5) 2 (zeroPolynomial 2) (adaptivePolynomial r)
        [0, 1] 1 r).closed.map (closedOutputRelation (ZMod 5) 2) = some True := by
    rw [committedRun_true_iff]
    simp [zeroPolynomial, adaptive_endpoints, adaptive_hits]
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr hevent

/-- The challenge-first success strictly exceeds the fresh-challenge bound. -/
theorem fresh_bound_lt_one : (2 : ENNReal) / 5 < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

/-- An empty domain has sum zero, so every message rejects a nonzero target. -/
theorem empty_domain_rejection (p q : Message (ZMod 5) 1) :
    Pr{let run ← executeCommitted (ZMod 5) 1 ($ᵗ (ZMod 5)) p q [] 1}[run.closed = none] = 1 := by
  rw [executeCommitted_eq, prEvent_map]
  have h (r : ZMod 5) : (committedRun (ZMod 5) 1 p q [] 1 r).closed = none :=
    committedRun_rejects _ _ _ _ _ _ _ (by simp)
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr h

#print axioms zeroPolynomial
#print axioms linearPolynomial
#print axioms rejection_probability
#print axioms exact_repair_probability
#print axioms excludes_quadratic
#print axioms adaptivePolynomial
#print axioms adaptive_endpoints
#print axioms adaptive_hits
#print axioms challenge_first_probability
#print axioms fresh_bound_lt_one
#print axioms empty_domain_rejection

end BooleanControls

#print axioms executeCommitted_eq
#print axioms executeCommitted_soundness
#print axioms executeRandomCommitment_soundness
#print axioms executeCommitted_measureSoundness
#print axioms executeRandomCommitment_measureSoundness

end
end Sumcheck.Interaction.SingleRound.Test
