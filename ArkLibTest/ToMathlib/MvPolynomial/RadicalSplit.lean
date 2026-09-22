/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Acceptance tests for the variable split of distinct factors

For `Q = X 1 * X 0 ^ 2` over `ℚ` and the variable `0`, the distinct factor classes are those of
`X 1` and `X 0`. Only `X 0` has positive degree in `X 0`, and the content radical is associated to
`X 1`. The degree bound of `sum_degreeOf_positiveDegreeFactorClasses_le` is strict: the factor
degrees sum to `1`, while `degreeOf 0 Q = 2`. The zero polynomial shows that
`exists_exceptional_of_factor_exceptional` needs `Q ≠ 0`. The special cases over
`MvPolynomial (Option σ) F` with root variable `none` are derived at the end.
-/

open MvPolynomial UniqueFactorizationMonoid

namespace RadicalSplitTest

/-- `degreeOf j` is additive on nonzero products. -/
theorem degreeOf_additive {σ : Type*} (j : σ) : ∀ x y : MvPolynomial σ ℚ, x ≠ 0 → y ≠ 0 →
    degreeOf j (x * y) = degreeOf j x + degreeOf j y :=
  fun _ _ hx hy ↦ degreeOf_mul_eq hx hy

/-- The sample polynomial `X 1 * X 0 ^ 2`. -/
noncomputable abbrev Q : MvPolynomial (Fin 2) ℚ := X 1 * X 0 ^ 2

theorem Q_ne_zero : Q ≠ 0 := mul_ne_zero (X_ne_zero 1) (pow_ne_zero 2 (X_ne_zero 0))

theorem degreeOf_rep_mk_X (i j : Fin 2) :
    degreeOf i (Associates.mk (X j : MvPolynomial (Fin 2) ℚ)).rep = if j = i then 1 else 0 := by
  rw [map_eq_of_associated (degreeOf_additive i) (X_ne_zero j)
    (Associates.mk_eq_mk_iff_associated.mp (Associates.mk_rep _)), degreeOf_X]
  split_ifs <;> simp_all [eq_comm]

theorem mem_primeFactors_Q {c : Associates (MvPolynomial (Fin 2) ℚ)} :
    c ∈ primeFactors (Associates.mk Q) ↔ c = Associates.mk (X 1) ∨ c = Associates.mk (X 0) := by
  classical
  rw [← Associates.mk_mul_mk, primeFactors_mul_eq_union (by simp [X_ne_zero])
    (by simp [X_ne_zero]), ← pow_one (X 1), primeFactors_mk_pow_of_prime X_prime one_ne_zero,
    primeFactors_mk_pow_of_prime X_prime two_ne_zero, pow_one]
  simp

/-- Only the class of `X 0` has positive degree in `X 0`. -/
theorem positiveDegreeFactorClasses_Q :
    positiveDegreeFactorClasses 0 Q = {Associates.mk (X 0)} := by
  ext c
  simp only [mem_positiveDegreeFactorClasses, mem_primeFactors_Q, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · simp [degreeOf_rep_mk_X] at h
    · rfl
  · rintro rfl
    simp [degreeOf_rep_mk_X]

/-- The positive-degree factor degrees sum to `1`, strictly below `degreeOf 0 Q = 2`. -/
example : ∑ c ∈ positiveDegreeFactorClasses 0 Q, degreeOf 0 c.rep = 1 := by
  simp [positiveDegreeFactorClasses_Q, degreeOf_rep_mk_X]

example : degreeOf 0 Q = 2 := by
  rw [Q, degreeOf_mul_eq (X_ne_zero 1) (pow_ne_zero 2 (X_ne_zero 0)), degreeOf_pow_eq _ _ _
    (X_ne_zero 0)]
  simp [degreeOf_X]

/-- The content radical of `Q` is associated to `X 1`. -/
example : Associated (radicalContent 0 Q) (X 1) := by
  have hfilter : (primeFactors (Associates.mk Q)).filter
      (fun c ↦ degreeOf 0 (Associates.rep c) = 0) = {Associates.mk (X 1)} := by
    ext c
    simp only [Finset.mem_filter, mem_primeFactors_Q, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · simp [degreeOf_rep_mk_X] at h
    · rintro rfl
      simp [degreeOf_rep_mk_X]
  rw [← Associates.mk_eq_mk_iff_associated, radicalContent, hfilter, Finset.prod_singleton,
    Associates.mk_rep]

/-! ### Zeros -/

/-- Setting every variable to `0` kills `Q`, and the split locates the zero in the content radical
or in a positive-degree factor. -/
example : constantCoeff (radicalContent 0 Q) = 0 ∨
    ∃ c ∈ positiveDegreeFactorClasses 0 Q, constantCoeff c.rep = 0 :=
  (map_eq_zero_iff_radicalContent_or_exists constantCoeff 0 Q_ne_zero).mp (by simp [Q])

/-! ### `Q ≠ 0` is needed in the combination of exceptional sets -/

/-- For `Q = 0` the hypotheses of `exists_exceptional_of_factor_exceptional` hold with every bound
`0`: the content radical is `1`, and there are no factor classes. -/
example : (∃ ex : Finset Unit, (ex.card : ℚ) ≤ 0 ∧ ∀ w ∉ ex, ∀ _v : Unit,
      constantCoeff (radicalContent 0 (0 : MvPolynomial (Fin 2) ℚ)) ≠ 0) ∧
    ∀ c ∈ positiveDegreeFactorClasses 0 (0 : MvPolynomial (Fin 2) ℚ), ∃ ex : Finset Unit,
      (ex.card : ℚ) ≤ 0 ∧ ∀ w ∉ ex, ∀ _v : Unit, constantCoeff c.rep = 0 → False :=
  ⟨⟨∅, by simp, by simp⟩, by simp⟩

/-- For `Q = 0` the conclusion fails: the only set of size `0` is empty, and `0` is a zero. -/
example : ¬ ∃ ex : Finset Unit, (ex.card : ℚ) ≤
      0 + ∑ _c ∈ positiveDegreeFactorClasses 0 (0 : MvPolynomial (Fin 2) ℚ), (0 : ℚ) ∧
    ∀ w ∉ ex, ∀ _v : Unit, constantCoeff (0 : MvPolynomial (Fin 2) ℚ) = 0 → False := by
  rintro ⟨ex, hcard, hgood⟩
  have hex : ex = ∅ := by simpa using hcard
  exact hgood () (by simp [hex]) () (map_zero _)

/-! ### Root variable `none` over a field -/

section OptionRoot

variable {F τ D : Type*} [Field F] [CommRing D] [IsDomain D]

/-- The split product and `Q` have the same zeros under a ring homomorphism into a domain. -/
example (Q : MvPolynomial (Option τ) F) (hQ : Q ≠ 0) (f : MvPolynomial (Option τ) F →+* D) :
    f (radicalContent none Q * radicalPrimPart none Q) = 0 ↔ f Q = 0 :=
  map_radicalContent_mul_radicalPrimPart_eq_zero_iff f none hQ

/-- The coordinate-degree budget for the split at `none`. -/
example (Q : MvPolynomial (Option τ) F) (j : Option τ) :
    degreeOf j (radicalContent none Q) +
        ∑ a ∈ positiveDegreeFactorClasses none Q, degreeOf j a.rep ≤ degreeOf j Q :=
  add_sum_degreeOf_positiveDegreeFactorClasses_le none j Q

/-- The root-degree budget for the split at `none`. -/
example (Q : MvPolynomial (Option τ) F) :
    ∑ a ∈ positiveDegreeFactorClasses none Q, degreeOf none a.rep ≤ degreeOf none Q :=
  sum_degreeOf_positiveDegreeFactorClasses_le none Q

/-- Each positive-degree factor class at `none` has an irreducible representative of positive
degree in `X none`. -/
example (Q : MvPolynomial (Option τ) F) {a : Associates (MvPolynomial (Option τ) F)}
    (ha : a ∈ positiveDegreeFactorClasses none Q) :
    Irreducible a.rep ∧ 0 < degreeOf none a.rep :=
  ⟨irreducible_rep_of_mem_positiveDegreeFactorClasses ha,
    (mem_positiveDegreeFactorClasses.mp ha).2⟩

end OptionRoot

end RadicalSplitTest
