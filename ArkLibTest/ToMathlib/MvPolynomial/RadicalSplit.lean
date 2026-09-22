/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.JetDegree
import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Acceptance tests for the variable split of distinct factors

For `Q = X 1 * X 0 ^ 2` over `ℚ` and the variable `0`, the distinct factor classes are those of
`X 1` and `X 0`. Only `X 0` has positive degree in `X 0`, and the content radical is associated to
`X 1`. The degree bound of `sum_degreeOf_positiveDegreeFactorClasses_le` is strict: the factor
degrees sum to `1`, while `degreeOf 0 Q = 2`. The zero polynomial shows that
`exists_exceptional_of_factor_exceptional` needs `Q ≠ 0`. The primitive-part radical of `Q` has
total degree `1`, strictly below `totalDegree Q = 3`, and for `X 0 ^ 2` a degree function that is
not additive on products exceeds its value on the polynomial at the primitive-part radical. The
special cases over `MvPolynomial (Option σ) F` with root variable `none`, and over first-order jet
polynomials with root variable `Y₁`, are derived at the end.
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

/-- The primitive-part radical of `Q` is the representative of the class of `X 0`. -/
theorem radicalPrimPart_Q :
    radicalPrimPart 0 Q = (Associates.mk (X 0 : MvPolynomial (Fin 2) ℚ)).rep := by
  rw [radicalPrimPart, positiveDegreeFactorClasses_Q, Finset.prod_singleton]

/-- `totalDegree` is additive on nonzero products over `ℚ`. -/
theorem totalDegree_additive {σ : Type*} : ∀ x y : MvPolynomial σ ℚ, x ≠ 0 → y ≠ 0 →
    totalDegree (x * y) = totalDegree x + totalDegree y :=
  fun _ _ hx hy ↦ totalDegree_mul_of_isDomain hx hy

theorem totalDegree_rep_mk_X (j : Fin 2) :
    totalDegree (Associates.mk (X j : MvPolynomial (Fin 2) ℚ)).rep = 1 := by
  rw [map_eq_of_associated totalDegree_additive (X_ne_zero j)
    (Associates.mk_eq_mk_iff_associated.mp (Associates.mk_rep _)), totalDegree_X]

/-- The primitive-part radical has total degree `1`, strictly below `totalDegree Q = 3`: the
repeated factor `X 0` is counted once. -/
example : totalDegree (radicalPrimPart 0 Q) = 1 := by
  rw [radicalPrimPart_Q, totalDegree_rep_mk_X]

example : totalDegree Q = 3 := by
  rw [Q, totalDegree_mul_of_isDomain (X_ne_zero 1) (pow_ne_zero 2 (X_ne_zero 0)),
    totalDegree_X_pow, totalDegree_X]

example : radicalPrimPart 0 Q ∣ Q := radicalPrimPart_dvd_self 0 Q

/-! ### Additivity is needed in `map_radicalPrimPart_le` -/

/-- The indicator of total degree `1`, which is not additive on products. -/
noncomputable def isLinear (p : MvPolynomial (Fin 2) ℚ) : ℕ :=
  if totalDegree p = 1 then 1 else 0

/-- For `X 0 ^ 2` the primitive-part radical is the representative of the class of `X 0`. -/
theorem radicalPrimPart_X_sq :
    radicalPrimPart 0 (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      (Associates.mk (X 0 : MvPolynomial (Fin 2) ℚ)).rep := by
  have hclasses : positiveDegreeFactorClasses 0 (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      {Associates.mk (X 0)} := by
    rw [positiveDegreeFactorClasses, primeFactors_mk_pow_of_prime X_prime two_ne_zero]
    simp [degreeOf_rep_mk_X]
  rw [radicalPrimPart, hclasses, Finset.prod_singleton]

/-- `isLinear` takes the value `1` at the primitive-part radical of `X 0 ^ 2` and `0` at
`X 0 ^ 2`, so the conclusion of `map_radicalPrimPart_le` fails without additivity. -/
example : isLinear (X 0 ^ 2) < isLinear (radicalPrimPart 0 (X 0 ^ 2)) := by
  simp [isLinear, radicalPrimPart_X_sq, totalDegree_rep_mk_X, totalDegree_X_pow]

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


/-- The total degree of the primitive-part radical at `none` is at most that of `Q`, with no
hypothesis `Q ≠ 0`. -/
example (Q : MvPolynomial (Option τ) F) :
    totalDegree (radicalPrimPart none Q) ≤ totalDegree Q :=
  totalDegree_radicalPrimPart_le none Q

/-- The total-degree budget for the split at `none`, with no hypothesis `Q ≠ 0`. -/
example (Q : MvPolynomial (Option τ) F) :
    totalDegree (radicalContent none Q) +
        ∑ a ∈ positiveDegreeFactorClasses none Q, totalDegree a.rep ≤ totalDegree Q :=
  add_sum_totalDegree_positiveDegreeFactorClasses_le none Q

/-- `radicalRep Q` divides `Q`, with no hypothesis `Q ≠ 0`. -/
example (Q : MvPolynomial (Option τ) F) : radicalRep Q ∣ Q := radicalRep_dvd_self Q

end OptionRoot

/-! ### First-order jet polynomials with root variable `Y₁`

The split is taken directly at the variable `some 1`, which is `Y₁` in `DifferentialPolynomial F 1`;
no change of coordinates is needed. -/

section FirstOrder

open PolynomialDifferential

variable {F : Type*} [Field F]

/-- The content radical does not involve `Y₁`. -/
example (Q : DifferentialPolynomial F 1) : jetDegree (radicalContent (some 1) Q) 1 = 0 :=
  degreeOf_radicalContent (some 1) Q

/-- The content radical and the distinct factors of positive `Y₁`-degree share the total-degree
budget of `Q`. -/
example (Q : DifferentialPolynomial F 1) :
    totalDegree (radicalContent (some 1) Q) +
        ∑ a ∈ positiveDegreeFactorClasses (some 1) Q, totalDegree a.rep ≤ totalDegree Q :=
  add_sum_totalDegree_positiveDegreeFactorClasses_le (some 1) Q

/-- The primitive-part radical in `Y₁` has total degree at most that of `Q`. -/
example (Q : DifferentialPolynomial F 1) :
    totalDegree (radicalPrimPart (some 1) Q) ≤ totalDegree Q :=
  totalDegree_radicalPrimPart_le (some 1) Q

/-- The distinct factors of positive `Y₁`-degree have `Y₁`-degrees summing to at most that of
`Q`. -/
example (Q : DifferentialPolynomial F 1) :
    ∑ a ∈ positiveDegreeFactorClasses (some 1) Q, degreeOf (some 1) a.rep ≤ jetDegree Q 1 :=
  sum_degreeOf_positiveDegreeFactorClasses_le (some 1) Q

/-- The primitive-part radical in `Y₁` has `Y₁`-degree at most that of `Q`. -/
example (Q : DifferentialPolynomial F 1) :
    jetDegree (radicalPrimPart (some 1) Q) 1 ≤ jetDegree Q 1 :=
  degreeOf_radicalPrimPart_le (some 1) (some 1) Q

/-- The content radical times the primitive-part radical in `Y₁` divides `Q`. -/
example (Q : DifferentialPolynomial F 1) :
    radicalContent (some 1) Q * radicalPrimPart (some 1) Q ∣ Q :=
  radicalContent_mul_radicalPrimPart_dvd_self (some 1) Q

/-- Every differential root of a nonzero `Q` is a root of its content radical or of its
primitive-part radical in `Y₁`. -/
example (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (P : Polynomial F)
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization (radicalContent (some 1) Q) P = 0 ∨
      differentialSpecialization (radicalPrimPart (some 1) Q) P = 0 := by
  have h := (map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (differentialSpecializationHom P) (some 1) hQ).mpr hroot
  rwa [map_mul, mul_eq_zero] at h

end FirstOrder

end RadicalSplitTest
