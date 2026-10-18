/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The fixed-message Sumcheck collision bound

The round message is fixed before the challenge. Soundness uses an integral domain;
the execution definitions themselves only require a commutative semiring.
-/

@[expose] public section

open Polynomial OracleComp
open scoped Polynomial

namespace Sumcheck.Spec.SingleRound.Simple

/-- Distinct bounded-degree polynomials agree at at most `deg` field points. -/
theorem collision_card_le {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] {deg : ℕ} (p q : R⦃≤ deg⦄[X]) (hne : p ≠ q) :
    (Finset.univ.filter (fun r => p.val.eval r = q.val.eval r)).card ≤ deg := by
  have hsub : p.val - q.val ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.mp h))
  apply (Polynomial.card_le_degree_of_subset_roots (p := p.val - q.val) ?_).trans
  · exact natDegree_le_of_degree_le
      ((degree_sub_le _ _).trans (max_le (mem_degreeLE.mp p.property)
        (mem_degreeLE.mp q.property)))
  · intro r hr
    apply (mem_roots hsub).mpr
    simpa only [IsRoot, eval_sub, sub_eq_zero] using (Finset.mem_filter.mp hr).2

/-- A false sum and a message passing the sum check can yield a true next claim only
with the usual degree-over-field-size probability. -/
theorem fixed_message_collision_bound {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [SampleableType R] {deg m : ℕ} (D : Fin m ↪ R)
    (p q : R⦃≤ deg⦄[X]) (target : R)
    (hfalse : ∑ x ∈ Finset.univ.map D, p.val.eval x ≠ target)
    (hcheck : ∑ x ∈ Finset.univ.map D, q.val.eval x = target) :
    Pr{let r ← $ᵗ R}[p.val.eval r = q.val.eval r] ≤
      (deg : ENNReal) / Fintype.card R := by
  classical
  have hne : p ≠ q := by
    intro h
    exact hfalse (h ▸ hcheck)
  rw [SampleableType.prEvent_uniformSample]
  have hcard := collision_card_le p q hne
  gcongr

/-- The corrected verifier's accepting, related output has the fixed-prefix collision bound.
The sum check may reject; no assumption that it passes is required here. -/
theorem guarded_output_bound {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] [SampleableType R] {deg m : ℕ} (D : Fin m ↪ R)
    {ι : Type} (oSpec : OracleSpec ι)
    (input : StmtIn R × ∀ i, OStmtIn R deg i) (q : R⦃≤ deg⦄[X])
    (hfalse : (input, ()) ∉ inputRelation R deg D) :
    Pr{let r ← $ᵗ R}[
      (verifierGuardedForm R deg D oSpec).check input
        (ProtocolSpec.FullTranscript.mk2 (pSpec := pSpec R deg) q r) = true ∧
      ((verifierGuardedForm R deg D oSpec).out input
        (ProtocolSpec.FullTranscript.mk2 (pSpec := pSpec R deg) q r), ()) ∈ outputRelation R deg] ≤
      (deg : ENNReal) / Fintype.card R := by
  by_cases hcheck : ∑ x ∈ Finset.univ.map D, q.val.eval x = input.1
  · simp only [verifierGuardedForm, ProtocolSpec.FullTranscript.mk2, outputRelation]
    simp only [hcheck, decide_true, true_and, Set.mem_ofPred_eq]
    exact fixed_message_collision_bound D (input.2 ()) q input.1 hfalse
      hcheck
  · simp [verifierGuardedForm, ProtocolSpec.FullTranscript.mk2, -Finset.sum_map, hcheck]

end Sumcheck.Spec.SingleRound.Simple
