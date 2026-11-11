/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
public import ArkLib.Data.MvPolynomial.JointDegree

/-!
# Challenge degree of substituted source columns

Over a polynomial ring `R[X]`, whose variable is a symbolic challenge, the received value at a
point may be a polynomial `received` of degree at most `ℓ` in the challenge. The unscaled local
substitution then introduces challenge degree through `Y₀ ↦ received + ⋯`. This file bounds the
challenge degree of the substituted polynomial jointly with a weight on its local monomials,
using `MvPolynomial.restrictJointDegree`.

* `unscaledLocalSubstitution_mem_restrictJointDegree`: if a source weight `v` and a local weight
  `u` satisfy `center.natDegree ≤ v X`, `received.natDegree ≤ v Y₀` and the weight inequalities
  of the local image, then the substitution maps the joint bound `B` for `v` to the joint bound
  `B` for `u`.

For a source column with `Y₀` exponent `y₀` and higher exponents `higher`, a constant center
and `received.natDegree ≤ ℓ`, two weight choices give the bounds used by symbolic interpolation:

* the local jet-degree weight scaled by `ℓ`: a local monomial `e` of jet degree `t` has challenge
  degree at most `ℓ * (y₀ + ∑_j higher j - t)`, and none with `t > y₀ + ∑_j higher j` occurs;
* the zero weight: every coefficient has challenge degree at most `ℓ * y₀`.

## Main statements

* `unscaledLocalSubstitution_mem_restrictJointDegree` and
  `localConstraintAt_mem_restrictJointDegree`: the joint-bound transport.
* `SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le`: the bound `ℓ * y₀`.
* `SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le_sub`: the bound
  `ℓ * (y₀ + ∑_j higher j - t)`.
* `SourceColumn.coeff_unscaledLocalSubstitution_eq_zero_of_lt`: no monomial above the source
  jet degree.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

open PolynomialDifferential
open scoped Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ### Transport through the substitution -/

section Transport

variable {v : JetVariable d → ℕ} {u : LocalVariable d → ℕ}

/-- The correction `∑_j (-1)^j T^(j+1) Y_(j+1)` satisfies the joint bound `B` for `u` when every
term `T^(j+1) Y_(j+1)` has `u`-weight at most `B`. Its coefficients are constants. -/
theorem localCorrection_mem_restrictJointDegree {B : ℕ}
    (hcorr : ∀ j : Fin d, (j.val + 1) * u (localT d) + u (localY j) ≤ B) :
    localCorrection (R := R[X]) d ∈ restrictJointDegree (R := R) u B := by
  refine Submodule.sum_mem _ fun j _ => ?_
  refine restrictJointDegree_mono u (by simpa using hcorr j)
    (mul_mem_restrictJointDegree (mul_mem_restrictJointDegree
      (C_mem_restrictJointDegree u (B := 0) ?_)
      (pow_mem_restrictJointDegree (X_mem_restrictJointDegree u (localT d) le_rfl) _))
      (X_mem_restrictJointDegree u (localY j) le_rfl))
  rw [show (-1 : R[X]) ^ j.val = Polynomial.C ((-1 : R) ^ j.val) by simp,
    Polynomial.natDegree_C]

/-- Each generator image of the unscaled substitution satisfies the joint bound given by the
source weight of its variable. -/
theorem unscaledLocalImage_mem_restrictJointDegree {center received : R[X]}
    (hcenter : center.natDegree ≤ v none) (hX : u (localT d) ≤ v none)
    (hreceived : received.natDegree ≤ v (some 0))
    (hE : u (localT d) + u (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) * u (localT d) + u (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, u (localY j) ≤ v (some j.succ)) (x : JetVariable d) :
    unscaledLocalImage d center received x ∈ restrictJointDegree (R := R) u (v x) := by
  rcases x with _ | j
  · exact add_mem (C_mem_restrictJointDegree u hcenter) (X_mem_restrictJointDegree u _ hX)
  induction j using Fin.cases with
  | zero =>
    exact add_mem (add_mem (C_mem_restrictJointDegree u hreceived)
      (localCorrection_mem_restrictJointDegree hcorr))
      (restrictJointDegree_mono u hE (mul_mem_restrictJointDegree
        (X_mem_restrictJointDegree u _ le_rfl) (X_mem_restrictJointDegree u _ le_rfl)))
  | succ j =>
    simpa [unscaledLocalImage] using X_mem_restrictJointDegree (R := R) u _ (hjet j)

/-- The unscaled substitution at `(center, received)` maps the joint bound `B` for the source
weight `v` to the joint bound `B` for the local weight `u`, provided `center` has degree at most
`v X`, `received` has degree at most `v Y₀`, and the local image of each variable has `u`-weight
at most its `v`-weight. -/
theorem unscaledLocalSubstitution_mem_restrictJointDegree {center received : R[X]}
    (hcenter : center.natDegree ≤ v none) (hX : u (localT d) ≤ v none)
    (hreceived : received.natDegree ≤ v (some 0))
    (hE : u (localT d) + u (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) * u (localT d) + u (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, u (localY j) ≤ v (some j.succ)) {B : ℕ}
    {Q : DifferentialPolynomial R[X] d} (hQ : Q ∈ restrictJointDegree (R := R) v B) :
    unscaledLocalSubstitution d center received Q ∈ restrictJointDegree (R := R) u B :=
  bind₁_mem_restrictJointDegree
    (unscaledLocalImage_mem_restrictJointDegree hcenter hX hreceived hE hcorr hjet) hQ

/-- The low-contact projection keeps some coefficients and zeroes the others, so it preserves
every joint bound. -/
theorem projectLowContact_mem_restrictJointDegree (m : ℕ) {B : ℕ}
    {P : LocalPolynomial R[X] d} (hP : P ∈ restrictJointDegree (R := R) u B) :
    projectLowContact m P ∈ restrictJointDegree (R := R) u B := by
  rw [mem_restrictJointDegree_iff_coeff] at hP ⊢
  intro e n hne
  rw [coeff_projectLowContact] at hne
  split_ifs at hne
  · exact hP e n hne
  · simp at hne

/-- The local constraint map at `(center, received)` satisfies the joint-bound transport of
`unscaledLocalSubstitution_mem_restrictJointDegree`. -/
theorem localConstraintAt_mem_restrictJointDegree (m : ℕ) {center received : R[X]}
    (hcenter : center.natDegree ≤ v none) (hX : u (localT d) ≤ v none)
    (hreceived : received.natDegree ≤ v (some 0))
    (hE : u (localT d) + u (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) * u (localT d) + u (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, u (localY j) ≤ v (some j.succ)) {B : ℕ}
    {Q : DifferentialPolynomial R[X] d} (hQ : Q ∈ restrictJointDegree (R := R) v B) :
    localConstraintAt m center received Q ∈ restrictJointDegree (R := R) u B :=
  projectLowContact_mem_restrictJointDegree m
    (unscaledLocalSubstitution_mem_restrictJointDegree hcenter hX hreceived hE hcorr hjet hQ)

end Transport

/-! ### Source columns at a constant center -/

namespace SourceColumn

/-- With a constant center and a received value of challenge degree at most `ℓ`, the substituted
column satisfies the joint bound `ℓ * (y₀ + ∑_j higher j)` for the local jet-degree weight scaled
by `ℓ`. -/
theorem unscaledLocalSubstitution_mem_restrictJointDegree_localJetDegree (ℓ : ℕ) (a : R)
    {received : R[X]} (hreceived : received.natDegree ≤ ℓ) (c : SourceColumn d) :
    unscaledLocalSubstitution d (Polynomial.C a) received c.polynomial ∈
      restrictJointDegree (R := R) (fun x => ℓ * localJetDegreeWeight d x)
        (ℓ * (c.y₀ + ∑ j, c.higher j)) := by
  refine unscaledLocalSubstitution_mem_restrictJointDegree (v := fun x => ℓ * jetDegreeWeight x)
    (by simp) (by simp [localJetDegreeWeight, localT])
    (by simpa using hreceived) (by simp [localJetDegreeWeight, localT, localE, localAux])
    (fun _ => by simp [localJetDegreeWeight, localT, localY])
    (fun _ => by simp [localJetDegreeWeight, localY])
    (monomial_mem_restrictJointDegree _ ?_)
  simp [weight_exponent, Finset.mul_sum, mul_add, mul_comm]

/-- With a constant center and a received value of challenge degree at most `ℓ`, every
coefficient of the substituted column has challenge degree at most `ℓ * y₀`. -/
theorem natDegree_coeff_unscaledLocalSubstitution_le (ℓ : ℕ) (a : R) {received : R[X]}
    (hreceived : received.natDegree ≤ ℓ) (c : SourceColumn d) (e : LocalVariable d →₀ ℕ) :
    ((unscaledLocalSubstitution d (Polynomial.C a) received c.polynomial).coeff e).natDegree ≤
      ℓ * c.y₀ := by
  have h : unscaledLocalSubstitution d (Polynomial.C a) received c.polynomial ∈
      restrictJointDegree (R := R) (0 : LocalVariable d → ℕ) (ℓ * c.y₀) := by
    classical
    refine unscaledLocalSubstitution_mem_restrictJointDegree (v := Pi.single (some 0) ℓ)
      (by simp) (by simp) (by simpa using hreceived) (by simp) (fun _ => by simp)
      (fun _ => by simp) (monomial_mem_restrictJointDegree _ ?_)
    simp [Finsupp.weight_single_index, mul_comm]
  exact mem_restrictJointDegree_zero_iff.mp h e

/-- With a constant center and a received value of challenge degree at most `ℓ`, the coefficient
of the substituted column at a local monomial `e` of jet degree `t` has challenge degree at most
`ℓ * (y₀ + ∑_j higher j - t)`. -/
theorem natDegree_coeff_unscaledLocalSubstitution_le_sub (ℓ : ℕ) (a : R) {received : R[X]}
    (hreceived : received.natDegree ≤ ℓ) (c : SourceColumn d) (e : LocalVariable d →₀ ℕ) :
    ((unscaledLocalSubstitution d (Polynomial.C a) received c.polynomial).coeff e).natDegree ≤
      ℓ * (c.y₀ + ∑ j, c.higher j - e.weight (localJetDegreeWeight d)) := by
  have h := natDegree_coeff_le_of_mem_restrictJointDegree
    (unscaledLocalSubstitution_mem_restrictJointDegree_localJetDegree ℓ a hreceived c) e
  have hw : e.weight (fun x => ℓ * localJetDegreeWeight d x) =
      ℓ * e.weight (localJetDegreeWeight d) := by
    simp only [Finsupp.weight_eq_sum, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
  rwa [hw, ← Nat.mul_sub] at h

/-- The substituted column has no local monomial of jet degree above the column's total jet
degree `y₀ + ∑_j higher j`. This holds at every center and received value. -/
theorem coeff_unscaledLocalSubstitution_eq_zero_of_lt (center received : R)
    (c : SourceColumn d) {e : LocalVariable d →₀ ℕ}
    (he : c.y₀ + ∑ j, c.higher j < e.weight (localJetDegreeWeight d)) :
    (unscaledLocalSubstitution d center received c.polynomial).coeff e = 0 := by
  classical
  by_contra hne
  have hsupport : ∀ x ∈ (c.polynomial : DifferentialPolynomial R d).support,
      totalJetDegree x ≤ c.y₀ + ∑ j, c.higher j := by
    intro x hx
    rw [polynomial, support_monomial] at hx
    split_ifs at hx
    · simp at hx
    · rw [Finset.mem_singleton.mp hx, totalJetDegree_exponent]
  have := localJetDegree_le_of_mem_support center received hsupport (mem_support_iff.mpr hne)
  omega

end SourceColumn

end ReedSolomon.HiddenDerivative
