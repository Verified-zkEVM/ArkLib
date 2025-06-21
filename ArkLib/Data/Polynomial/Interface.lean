import ArkLib.Data.Fin.Lift
import Mathlib.RingTheory.Polynomial.Basic

section PolynomialInterface

open Polynomial

variable {F : Type*} [Semiring F] {deg : ℕ} {coeffs : Fin deg → F}

lemma natDegree_lt_of_lbounded_zero_coeff {p : F[X]} [NeZero deg]
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

def coeffsOfPolynomial (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x

variable [DecidableEq F]

def polynomialOfCoeffs (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi ⟨a, w⟩))
  ⟩

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
  [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg :
  (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT [NeZero deg] :
  polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs :
  Fin.liftF' (polynomialOfCoeffs coeffs).coeff = coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

lemma coeff_polynomialOfCoeffs_eq_coeffs' :
  (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs'' :
  (polynomialOfCoeffs coeffs).coeff = Fin.liftF coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

@[simp]
lemma polynomialOfCoeffs_eq_zero :
  polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffs, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffs_coeffsOfPolynomial {p : F[X]}
  (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))

@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs :
  coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs : (polynomialOfCoeffs coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

@[simp]
lemma eval_polynomialsOfCoeffs [NeZero deg] {α : F} :
  (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, coeff_polynomialOfCoeffs_eq_coeffs', Fin.liftF]

@[simp]
lemma isRoot_polynomialsOfCoeffs {x : F} :
  IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl

end PolynomialInterface
