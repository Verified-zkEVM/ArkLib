/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Agreement
/-!
# Simultaneous specialization of polynomial tuples

Distinct tuples collide at only finitely many challenges. Over an infinite extension field,
a finite family therefore specializes injectively at one challenge, simultaneously avoiding
the zeros of finitely many nonzero auxiliary polynomials. This is the specialization step
used to count retained graphs by a generic fiber.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] {ℓ : ℕ}

/-- The coefficient vector of a power-batching coordinate is recoverable from its polynomial. -/
theorem powerBatchedCoordinate_injective :
    Function.Injective (powerBatchedCoordinate (F := F) (ℓ := ℓ)) := by
  intro u v h
  funext t
  have hc := congrArg (fun p : F[X] ↦ p.coeff t.val) h
  simpa [powerBatchedCoordinate, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Fin.val_inj] using hc

/-- Agreement of two tuple specializations at infinitely many challenges identifies every
constituent. The argument is coefficientwise and permits arbitrary batching degree. -/
theorem polynomialTuple_eq_of_infinite_specializations (ι : F →+* E)
    (P Q : Fin (ℓ + 1) → F[X])
    (h : Set.Infinite {z : E | powerBatchedPolynomial (fun t ↦ (P t).map ι) z =
      powerBatchedPolynomial (fun t ↦ (Q t).map ι) z}) : P = Q := by
  funext t
  apply Polynomial.ext
  intro j
  let a := powerBatchedCoordinate (fun t ↦ ι ((P t).coeff j))
  let b := powerBatchedCoordinate (fun t ↦ ι ((Q t).coeff j))
  have hab : a = b := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply h.mono
    intro z hz
    have hc := congrArg (fun p : E[X] ↦ p.coeff j) hz
    simpa only [Set.mem_ofPred_eq, a, b, powerBatchedCoordinate_eval, powerBatchedPolynomial,
      Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
      Polynomial.coeff_map] using hc
  have heq := powerBatchedCoordinate_injective hab
  exact ι.injective (congrFun heq t)

/-- Distinct polynomial tuples have only finitely many collision challenges. -/
theorem finite_polynomialTuple_collisions (ι : F →+* E)
    {P Q : Fin (ℓ + 1) → F[X]} (hne : P ≠ Q) :
    {z : E | powerBatchedPolynomial (fun t ↦ (P t).map ι) z =
      powerBatchedPolynomial (fun t ↦ (Q t).map ι) z}.Finite := by
  by_contra hinfinite
  exact hne (polynomialTuple_eq_of_infinite_specializations ι P Q hinfinite)

/-- A finite family fails to specialize injectively at only finitely many challenges. -/
theorem finite_polynomialTuple_noninjective_challenges (ι : F →+* E)
    (family : Finset (Fin (ℓ + 1) → F[X])) :
    {z : E | ¬ Set.InjOn (fun P : Fin (ℓ + 1) → F[X] ↦
      powerBatchedPolynomial (fun t ↦ (P t).map ι) z)
      (↑family)}.Finite := by
  classical
  have hfinite : (⋃ P ∈ (↑family : Set (Fin (ℓ + 1) → F[X])),
      ⋃ Q ∈ (↑family : Set (Fin (ℓ + 1) → F[X])),
      {z : E | P ≠ Q ∧ powerBatchedPolynomial (fun t ↦ (P t).map ι) z =
        powerBatchedPolynomial (fun t ↦ (Q t).map ι) z}).Finite := by
    apply family.finite_toSet.biUnion
    intro P _
    apply family.finite_toSet.biUnion
    intro Q _
    by_cases heq : P = Q
    · simp [heq]
    · exact (finite_polynomialTuple_collisions ι heq).subset (fun _ hz ↦ hz.2)
  apply hfinite.subset
  intro z hz
  simp only [Set.InjOn, not_forall] at hz
  obtain ⟨P, hP, Q, hQ, heq, hne⟩ := hz
  exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP,
    Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hQ, hne, heq⟩⟩⟩⟩

/-- One extension-field challenge separates an entire finite tuple family and avoids every
specified exceptional value and every zero of the auxiliary polynomials. -/
theorem exists_polynomialTuple_specialization_injective_avoiding_roots [Infinite E]
    (ι : F →+* E) (family : Finset (Fin (ℓ + 1) → F[X])) (avoid : Finset E)
    (auxiliary : Finset E[X]) (hne : ∀ R ∈ auxiliary, R ≠ 0) :
    ∃ z : E, z ∉ avoid ∧
      Set.InjOn (fun P : Fin (ℓ + 1) → F[X] ↦
        powerBatchedPolynomial (fun t ↦ (P t).map ι) z) (↑family) ∧
      ∀ R ∈ auxiliary, R.eval z ≠ 0 := by
  classical
  let roots := auxiliary.biUnion fun R ↦ R.roots.toFinset
  have hfinite := (finite_polynomialTuple_noninjective_challenges ι family).union
    (avoid ∪ roots).finite_toSet
  obtain ⟨z, hz⟩ := hfinite.exists_notMem
  have hboth := not_or.mp hz
  have hzavoid : z ∉ avoid ∧ z ∉ roots := by
    simpa only [Finset.mem_coe, Finset.mem_union, not_or] using hboth.2
  refine ⟨z, hzavoid.1, not_not.mp hboth.1, ?_⟩
  intro R hR heval
  apply hzavoid.2
  exact Finset.mem_biUnion.mpr ⟨R, hR,
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne R hR)).mpr heval)⟩

end ReedSolomon
