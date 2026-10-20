/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Translation
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SourceMonomial
public import ArkLib.Data.MvPolynomial.WeightedHomogeneous

/-!
# The jet-degree grading of the local constraint map

Give the global jet variables `Y₀, ..., Y_d` weight one and `X` weight zero (`jetDegreeWeight`),
and give the local error `E` and the visible jets `Y₁, ..., Y_d` weight one and the displacement
`T` weight zero (`localJetDegreeWeight`). When the received value is zero, the unscaled local
substitution sends each generator to a homogeneous polynomial of the generator's weight:

```text
X  ↦ center + T                                    (degree 0),
Y₀ ↦ ∑_{j<d} (-1)^j T^(j+1) Y_(j+1) + T E          (degree 1),
Y_(j+1) ↦ Y_(j+1)                                  (degree 1).
```

So the substitution, and the local constraint map after the low-contact projection, send a
polynomial homogeneous of jet degree `t` to one homogeneous of local jet degree `t`. The local
constraint map therefore restricts to linear maps `gradedLocalConstraintAt` between the grade-`t`
pieces, which is the row profile used by shifted symbolic interpolation. A source-monomial
coefficient of the constraint map vanishes outside its own grade.

A nonzero received value breaks the grading, since `Y₀ ↦ received + ⋯` has a constant term of
degree zero; a nonzero center does not, since `X` and `T` both have weight zero. Translation in
`X` and `Y₀` can lower the total jet degree of a monomial but cannot raise it.

## Main statements

* `unscaledLocalSubstitution_isWeightedHomogeneous`,
  `localConstraintAt_isWeightedHomogeneous`: the grading at received value zero.
* `gradedLocalConstraintAt`: the restriction to one grade.
* `coeff_localConstraintAt_eq_zero_of_weight_ne` and its source-monomial case
  `coeff_localConstraintAt_zero_sourceMonomial_eq_zero`.
* `totalJetDegree_le_of_mem_globalPointTranslation_support`.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d m : ℕ}

/-- Every monomial `(-1)^j T^(j+1) Y_(j+1)` of the local correction has local jet degree one. -/
theorem localCorrection_isWeightedHomogeneous (d : ℕ) :
    (localCorrection (R := R) d).IsWeightedHomogeneous (localJetDegreeWeight d) 1 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hC := isWeightedHomogeneous_C (localJetDegreeWeight d) ((-1 : R) ^ j.val)
  have hT := (isWeightedHomogeneous_X R (localJetDegreeWeight d) (localT d)).pow (j.val + 1)
  have hY := isWeightedHomogeneous_X R (localJetDegreeWeight d) (localY j)
  simpa [localJetDegreeWeight, localT, localY] using (hC.mul hT).mul hY

/-- With received value zero, the local substitution sends each global generator to a
homogeneous polynomial whose local jet degree is the generator's jet degree: `X ↦ center + T`
has degree zero, and `Y₀` and `Y_(j+1)` go to degree one. The center is arbitrary because `X` and
`T` both have weight zero. -/
theorem unscaledLocalImage_isWeightedHomogeneous (center : R) (v : JetVariable d) :
    (unscaledLocalImage d center 0 v).IsWeightedHomogeneous (localJetDegreeWeight d)
      (jetDegreeWeight v) := by
  have hX := isWeightedHomogeneous_X R (localJetDegreeWeight d)
  rcases v with _ | j
  · simpa [unscaledLocalImage, localJetDegreeWeight, localT] using
      (isWeightedHomogeneous_C (localJetDegreeWeight d) center).add (hX (localT d))
  · refine Fin.cases ?_ (fun i => ?_) j
    · have hTE : (X (localT d) * X (localE d) : LocalPolynomial R d).IsWeightedHomogeneous
          (localJetDegreeWeight d) 1 := (hX (localT d)).mul (hX (localE d))
      simpa [unscaledLocalImage] using (localCorrection_isWeightedHomogeneous d).add hTE
    · simpa [unscaledLocalImage, localJetDegreeWeight, localY] using hX (localY i)

/-- With received value zero, the unscaled local substitution sends a polynomial homogeneous of
jet degree `t` to one homogeneous of local jet degree `t`. -/
theorem unscaledLocalSubstitution_isWeightedHomogeneous (center : R)
    {Q : DifferentialPolynomial R d} {t : ℕ} (hQ : Q.IsWeightedHomogeneous jetDegreeWeight t) :
    (unscaledLocalSubstitution d center 0 Q).IsWeightedHomogeneous (localJetDegreeWeight d) t :=
  hQ.bind₁ (unscaledLocalImage_isWeightedHomogeneous center)

/-- With received value zero, the local constraint map sends a polynomial homogeneous of jet
degree `t` to one homogeneous of local jet degree `t`: the low-contact projection only deletes
monomials. -/
theorem localConstraintAt_isWeightedHomogeneous (center : R)
    {Q : DifferentialPolynomial R d} {t : ℕ} (hQ : Q.IsWeightedHomogeneous jetDegreeWeight t) :
    (localConstraintAt m center 0 Q).IsWeightedHomogeneous (localJetDegreeWeight d) t :=
  (unscaledLocalSubstitution_isWeightedHomogeneous center hQ).weightedTruncation _ m

/-- The source block of total jet degree `t`: polynomials all of whose monomials have jet degree
`t`, with `X` of degree zero. -/
def sourceJetGrade (R : Type*) [CommRing R] (d t : ℕ) :
    Submodule R (DifferentialPolynomial R d) :=
  weightedHomogeneousSubmodule R jetDegreeWeight t

/-- The local block of local jet degree `t`, with `E` and every visible jet of degree one and `T`
of degree zero. -/
def localJetGrade (R : Type*) [CommRing R] (d t : ℕ) :
    Submodule R (LocalPolynomial R d) :=
  weightedHomogeneousSubmodule R (localJetDegreeWeight d) t

/-- The local constraint map at `(center, 0)` restricted to the source block and the local block
of degree `t`. -/
def gradedLocalConstraintAt (m : ℕ) (center : R) (t : ℕ) :
    sourceJetGrade R d t →ₗ[R] localJetGrade R d t :=
  (localConstraintAt m center 0).restrict fun _ hQ =>
    localConstraintAt_isWeightedHomogeneous center hQ

/-- `gradedLocalConstraintAt m center t` acts as `localConstraintAt m center 0` on underlying
polynomials. -/
@[simp]
theorem coe_gradedLocalConstraintAt_apply (m : ℕ) (center : R) (t : ℕ)
    (Q : sourceJetGrade R d t) :
    (gradedLocalConstraintAt m center t Q : LocalPolynomial R d) =
      localConstraintAt m center 0 (Q : DifferentialPolynomial R d) :=
  rfl

/-- With received value zero, a coefficient of the constraint image of a polynomial of jet degree
`t` vanishes at every local exponent whose local jet degree is not `t`. -/
theorem coeff_localConstraintAt_eq_zero_of_weight_ne (center : R)
    {Q : DifferentialPolynomial R d} {t : ℕ} (hQ : Q.IsWeightedHomogeneous jetDegreeWeight t)
    (e : LocalVariable d →₀ ℕ) (he : e.weight (localJetDegreeWeight d) ≠ t) :
    (localConstraintAt m center 0 Q).coeff e = 0 :=
  (localConstraintAt_isWeightedHomogeneous center hQ).coeff_eq_zero e he

/-- At the origin, the constraint coefficient of `X^x Y₀^b ∏ Y_(j+1)^(higher j)`
vanishes unless the local jet degree of the row is `b + ∑_j higher j`. -/
theorem coeff_localConstraintAt_zero_sourceMonomial_eq_zero
    (x b : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ)
    (hgrade : e.weight (localJetDegreeWeight d) ≠ b + ∑ j, higher j) :
    (localConstraintAt (R := R) m 0 0 (sourceMonomial x b higher)).coeff e = 0 :=
  coeff_localConstraintAt_eq_zero_of_weight_ne 0
    (sourceMonomial_isWeightedHomogeneous_jetDegreeWeight x b higher) e hgrade

/-- Translation of `X` and `Y₀` by constants cannot raise the total jet degree of any support
monomial: the translate of `Y₀` is `received + Y₀`, which only adds lower-degree terms. -/
theorem totalJetDegree_le_of_mem_globalPointTranslation_support
    (center received : R) {Q : DifferentialPolynomial R d} {t : ℕ}
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ t)
    {e : JetVariable d →₀ ℕ} (he : e ∈ (globalPointTranslation center received Q).support) :
    totalJetDegree e ≤ t :=
  mem_restrictWeightAtMost.mp
    (globalPointTranslation_mem_restrictWeightAtMost (w := jetDegreeWeight) (by simp) (by simp)
      center received (mem_restrictWeightAtMost.mpr hQ)) e he

end ReedSolomon.HiddenDerivative
