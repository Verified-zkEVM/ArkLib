/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveStages
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageSum
/-!
# Composing the regular stages of a finite curve certificate

The geometric argument handles one regular equation at a time. This module combines those
stage theorems with the actual separant chain and the interpolation certificate. One union
of exceptional challenges then works for every close candidate, and the cap-sensitive stage
sum gives exactly the finite curve envelope.

The predicate `conclusion z P` names the conclusion supplied by the geometric stage theorem;
for MCA it is exact agreement with a correlated polynomial tuple. The stage hypothesis is
explicit: this composition lemma does not replace the required regular-stage geometry.
-/

@[expose] public section

noncomputable section

open PolynomialDifferential Polynomial MvPolynomial

namespace ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate

open SymbolicSeparantChain SymbolicReceivedInterpolation

universe u

variable {F E : Type u} [Field F] [Field E] {D A m M μ k h n N : ℕ}
  {domain : Fin n ↪ F} {w : Fin n → F[X]} {columns : Fin N → SourceColumn 1}

/-- Assemble uniform regular-stage conclusions with the exact finite curve budget at a common
Taylor denominator exponent. -/
theorem exists_exceptional_of_regular_stage_bounds_of_factors
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns)
    {stages : List (Stage F[X] 1)} {terminal : DifferentialPolynomial F[X] 1}
    (hc : Chain cert.Q stages terminal) (ι : F →+* E)
    (K L ell τ : ℕ) (η : ℚ) (hη : 1 ≤ η)
    (hK : 2 ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (conclusion : E → E[X] → Prop)
    (hregular : ∀ stage ∈ stages, ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveStageCharge n K k L A ell h stage (τ := τ) (η := η) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 →
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1)
              stage.2) P ≠ 0 → conclusion z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) → conclusion z P := by
  classical
  obtain ⟨base, hbase, hcover⟩ := cert.exists_exceptional_stage_coverage hc ι
  let ex : Stage F[X] 1 → Finset E := fun stage ↦
    if hs : stage ∈ stages then (hregular stage hs).choose else ∅
  have hex (stage : Stage F[X] 1) (hs : stage ∈ stages) := (hregular stage hs).choose_spec
  have hex_eq (stage : Stage F[X] 1) (hs : stage ∈ stages) :
      ex stage = (hregular stage hs).choose := by simp [ex, hs]
  have hnodup : stages.Nodup := by
    exact hc.ordered_stage_metadata.imp (fun hab heq ↦ by
      cases heq
      exact (lt_irrefl _ hab.1))
  refine ⟨base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ (h : ℚ) + ∑ stage ∈ stages.toFinset, ((ex stage).card : ℚ) := by
        apply add_le_add
        · exact_mod_cast hbase
        · exact_mod_cast Finset.card_biUnion_le
      _ ≤ (h : ℚ) + ∑ stage ∈ stages.toFinset,
          firstOrderCurveStageCharge n K k L A ell h stage (τ := τ) (η := η) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro stage hs
        rw [hex_eq stage (List.mem_toFinset.mp hs)]
        exact (hex stage (List.mem_toFinset.mp hs)).1
      _ = (h : ℚ) + (stages.map (fun stage ↦
          firstOrderCurveStageCharge n K k L A ell h stage
            (τ := τ) (η := η))).sum := by
        rw [List.sum_toFinset _ hnodup]
      _ ≤ _ := hc.sum_firstOrderCurveStageCharge_add_height_le_of_factors τ η hη
        cert.jetWeight_le cert.jetDegree_one_le hK hk hkL hLA hAn
  · intro z hz indices P hdegree hagree hvalues
    have hzbase : z ∉ base := fun hm ↦ hz (Finset.mem_union_left _ hm)
    obtain ⟨stage, hs, hsol, hsep⟩ := hcover z hzbase indices P hdegree hagree hvalues
    apply (hex stage hs).2 z ?_ indices P hdegree hagree hvalues hsol hsep
    intro hm
    apply hz (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨stage, List.mem_toFinset.mpr hs, ?_⟩))
    rwa [hex_eq stage hs]

/-- Dimension-sensitive specialization using the direct `k`-to-`A` joint factor at order one. -/
theorem exists_exceptional_of_regular_stage_bounds_of_exponent
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns)
    {stages : List (Stage F[X] 1)} {terminal : DifferentialPolynomial F[X] 1}
    (hc : Chain cert.Q stages terminal) (ι : F →+* E)
    (K L ell τ : ℕ) (hK : 2 ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (conclusion : E → E[X] → Prop)
    (hregular : ∀ stage ∈ stages, ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveStageCharge n K k L A ell h stage
          (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 →
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1)
              stage.2) P ≠ 0 → conclusion z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A μ M ell h
          (τ := τ) (η := firstOrderCurveDirectRatio n k A) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) → conclusion z P :=
  cert.exists_exceptional_of_regular_stage_bounds_of_factors hc ι K L ell τ
    (firstOrderCurveDirectRatio n k A)
    (firstOrderCurveDirectRatio_one_le (hkL.trans hLA) hAn)
    hK hk hkL hLA hAn conclusion hregular

end ReedSolomon.HiddenDerivative.FirstOrderCurveCertificate
