/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Injective specialization of polynomial tuples

A tuple `P : Fin (ℓ + 1) → F[X]` specializes at a challenge `z` in a field `E`, along
`φ : F →+* E`, to the batched polynomial `∑ t, z ^ t • (P t).map φ`. Two distinct tuples have the
same specialization at only finitely many challenges: comparing the coefficient of `X ^ j` gives
two polynomials of degree at most `ℓ` in `z`, and a polynomial with infinitely many roots is zero.
No bound on `ℓ` or on the characteristic is needed.

Consequently a finite family of tuples specializes injectively at all but finitely many
challenges. Over an infinite field `E` one challenge therefore separates the whole family while
avoiding a finite set of values and the roots of finitely many nonzero polynomials.

## Main statements

* `ReedSolomon.polynomialTuple_eq_of_infinite_specializations`: tuples whose specializations
  agree at infinitely many challenges are equal.
* `ReedSolomon.finite_polynomialTuple_collisions`: distinct tuples collide at finitely many
  challenges.
* `ReedSolomon.finite_polynomialTuple_noninjective_challenges`: a finite family specializes
  injectively at all but finitely many challenges.
* `ReedSolomon.exists_polynomialTuple_specialization_injective_avoiding_roots`: over an infinite
  field, one challenge separates a finite family and avoids finitely many values and roots.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] {ℓ : ℕ}

/-- If the specializations of two tuples along `φ` agree at infinitely many challenges, the tuples
are equal. -/
theorem polynomialTuple_eq_of_infinite_specializations (φ : F →+* E)
    (P Q : Fin (ℓ + 1) → F[X])
    (h : {z : E | powerBatchedPolynomial (fun t ↦ (P t).map φ) z =
      powerBatchedPolynomial (fun t ↦ (Q t).map φ) z}.Infinite) : P = Q := by
  funext t
  ext j
  have hab : powerBatchedCoordinate (fun t ↦ φ ((P t).coeff j)) =
      powerBatchedCoordinate (fun t ↦ φ ((Q t).coeff j)) := by
    refine eq_of_infinite_eval_eq _ _ (h.mono fun z hz ↦ ?_)
    have hc := congrArg (fun p : E[X] ↦ p.coeff j) hz
    simpa only [Set.mem_ofPred_eq, powerBatchedCoordinate_eval, powerBatchedPolynomial,
      finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_map] using hc
  exact φ.injective (congrFun (powerBatchedCoordinate_injective hab) t)

/-- Two distinct tuples have the same specialization along `φ` at only finitely many
challenges. -/
theorem finite_polynomialTuple_collisions (φ : F →+* E) {P Q : Fin (ℓ + 1) → F[X]}
    (hne : P ≠ Q) :
    {z : E | powerBatchedPolynomial (fun t ↦ (P t).map φ) z =
      powerBatchedPolynomial (fun t ↦ (Q t).map φ) z}.Finite :=
  Set.not_infinite.mp fun h ↦ hne (polynomialTuple_eq_of_infinite_specializations φ P Q h)

/-- A finite family of tuples fails to specialize injectively along `φ` at only finitely many
challenges. -/
theorem finite_polynomialTuple_noninjective_challenges (φ : F →+* E)
    (family : Finset (Fin (ℓ + 1) → F[X])) :
    {z : E | ¬ Set.InjOn (fun P : Fin (ℓ + 1) → F[X] ↦
      powerBatchedPolynomial (fun t ↦ (P t).map φ) z) family}.Finite := by
  have hfinite : (⋃ P ∈ (family : Set (Fin (ℓ + 1) → F[X])),
      ⋃ Q ∈ (family : Set (Fin (ℓ + 1) → F[X])),
      {z : E | P ≠ Q ∧ powerBatchedPolynomial (fun t ↦ (P t).map φ) z =
        powerBatchedPolynomial (fun t ↦ (Q t).map φ) z}).Finite := by
    refine family.finite_toSet.biUnion fun P _ ↦ family.finite_toSet.biUnion fun Q _ ↦ ?_
    by_cases heq : P = Q
    · simp [heq]
    · exact (finite_polynomialTuple_collisions φ heq).subset fun _ hz ↦ hz.2
  refine hfinite.subset fun z hz ↦ ?_
  simp only [Set.InjOn, not_forall, Set.mem_ofPred_eq] at hz
  obtain ⟨P, hP, Q, hQ, heq, hne⟩ := hz
  simp only [Set.mem_iUnion]
  exact ⟨P, hP, Q, hQ, hne, heq⟩

/-- **Simultaneous injective specialization.** Over an infinite field `E`, some challenge `z`
lies outside a given finite set `avoid`, specializes the finite family `family` injectively along
`φ`, and is not a root of any polynomial in a finite set `auxiliary` of nonzero polynomials. -/
theorem exists_polynomialTuple_specialization_injective_avoiding_roots [Infinite E]
    (φ : F →+* E) (family : Finset (Fin (ℓ + 1) → F[X])) (avoid : Finset E)
    (auxiliary : Finset E[X]) (hne : ∀ R ∈ auxiliary, R ≠ 0) :
    ∃ z : E, z ∉ avoid ∧
      Set.InjOn (fun P : Fin (ℓ + 1) → F[X] ↦
        powerBatchedPolynomial (fun t ↦ (P t).map φ) z) family ∧
      ∀ R ∈ auxiliary, R.eval z ≠ 0 := by
  classical
  let roots := auxiliary.biUnion fun R ↦ R.roots.toFinset
  obtain ⟨z, hz⟩ := ((finite_polynomialTuple_noninjective_challenges φ family).union
    (avoid ∪ roots).finite_toSet).exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.coe_union, Finset.mem_coe,
    not_or, not_not] at hz
  obtain ⟨hinj, havoid, hroots⟩ := hz
  refine ⟨z, havoid, hinj, fun R hR heval ↦ hroots ?_⟩
  exact Finset.mem_biUnion.mpr ⟨R, hR,
    Multiset.mem_toFinset.mpr ((mem_roots (hne R hR)).mpr heval)⟩

end ReedSolomon
