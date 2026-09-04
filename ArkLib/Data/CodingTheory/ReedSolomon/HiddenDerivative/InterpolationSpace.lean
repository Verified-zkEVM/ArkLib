/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng
-/

import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The finite hidden-derivative interpolation space

This file encodes the corrected support-first interpolation space. The variables are `X` and the
formal jets `Y₀, ..., Y_d`. The high-jet weight gives weight zero to `X`, `Y₀`, and `Y₁`, so
finiteness is proved from the complete support predicate, including separate bounds on the
`X` exponent and total jet degree. It does not misuse a positive-weight finrank theorem at zero
weights.

The definitions and proofs are adapted, with permission, from Kai Zhe Zheng's `rs-ld-mca`
formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. The coefficient ring is made
generic here; the donor stated the space over `ZMod q`.

## Variable convention

`JetVariable d` is definitionally `Option (Fin (d + 1))`. The constructor `none` denotes `X`,
and `some j` denotes `Y_j`. Downstream differential-polynomial code should reuse this type.
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

/-- Variables `X, Y₀, ..., Y_d`. `none` denotes `X`; `some j` denotes `Y_j`. -/
abbrev JetVariable (d : ℕ) := Option (Fin (d + 1))

/-- A polynomial in `X, Y₀, ..., Y_d` over `F`. -/
abbrev DifferentialPolynomial (F : Type*) [CommSemiring F] (d : ℕ) :=
  MvPolynomial (JetVariable d) F

/-- Exponent vectors for `Y₂, ..., Y_d`.

Coordinate `i : Fin (d - 1)` represents `Y_(i+2)`. -/
abbrev HigherJetExponent (d : ℕ) := Fin (d - 1) →₀ ℕ

/-- Anisotropic weight `omega(c) = sum_i (i+1)c_i` of a higher-jet exponent. -/
def higherJetWeight {d : ℕ} (c : HigherJetExponent d) : ℕ :=
  Finsupp.weight (fun i : Fin (d - 1) ↦ i.val + 1) c

/-- Ordinary degree `|c|` of a higher-jet exponent. -/
def higherJetDegree {d : ℕ} (c : HigherJetExponent d) : ℕ :=
  Finsupp.degree c

/-- Simultaneous anisotropic-weight and ordinary-degree eligibility. -/
def GoodHigherExponent (d W C : ℕ) (c : HigherJetExponent d) : Prop :=
  higherJetWeight c ≤ W ∧ higherJetDegree c ≤ C

/-- The set of eligible higher-jet exponents. -/
def goodHigherExponentSet (d W C : ℕ) : Set (HigherJetExponent d) :=
  {c | GoodHigherExponent d W C c}

/-- The eligible higher-jet exponent set is finite. -/
theorem goodHigherExponentSet_finite (d W C : ℕ) :
    (goodHigherExponentSet d W C).Finite := by
  apply (Finsupp.finite_of_nat_weight_le
    (fun i : Fin (d - 1) ↦ i.val + 1) (by omega) W).subset
  intro c hc
  exact hc.1

/-- The finite anisotropic exponent set for `Y₂, ..., Y_d`. -/
def goodHigherExponents (d W C : ℕ) : Finset (HigherJetExponent d) :=
  (goodHigherExponentSet_finite d W C).toFinset

@[simp]
theorem mem_goodHigherExponents {d W C : ℕ} {c : HigherJetExponent d} :
    c ∈ goodHigherExponents d W C ↔ GoodHigherExponent d W C c := by
  simp [goodHigherExponents, goodHigherExponentSet]

/-- The exponent of `Y₁`; this remains total when `d = 0`. -/
def firstJetExponent {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) ↦ if j.val = 1 then 1 else 0) u.some

/-- Total exponent of `Y₀, ..., Y_d`. -/
def totalJetDegree {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.degree u.some

/-- High-jet weight on a full exponent: `Y_j` has weight `j - 1`. -/
def fullHigherJetWeight {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) ↦ j.val - 1) u.some

/-- Ordinary degree in `Y₂, ..., Y_d`, expressed on a full exponent. -/
def fullHigherJetDegree {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) ↦ if 2 ≤ j.val then 1 else 0) u.some

/-- Complete support predicate for the global interpolation space.

The clauses bound the `Y₁` exponent, total jet degree, global weighted degree, anisotropic
higher-jet weight, and ordinary higher-jet degree, in that order. -/
def GlobalEligibleExponent (d m A K B W C : ℕ) (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ m ∧
    totalJetDegree u ≤ B ∧
    u none + (K - 1) * totalJetDegree u < m * A ∧
    fullHigherJetWeight u ≤ W ∧
    fullHigherJetDegree u ≤ C

/-- The set underlying `globalEligibleExponents`. -/
def globalEligibleExponentSet (d m A K B W C : ℕ) : Set (JetVariable d →₀ ℕ) :=
  {u | GlobalEligibleExponent d m A K B W C u}

/-- Splitting an exponent on `Option` separates `X` from the total jet degree. -/
theorem exponentDegree_eq_x_add_totalJetDegree {d : ℕ} (u : JetVariable d →₀ ℕ) :
    Finsupp.degree u = u none + totalJetDegree u := by
  classical
  simp [Finsupp.degree_eq_sum, totalJetDegree, Fintype.sum_option]

/-- The complete eligible-exponent set is finite, including when some semantic weights vanish. -/
theorem globalEligibleExponentSet_finite (d m A K B W C : ℕ) :
    (globalEligibleExponentSet d m A K B W C).Finite := by
  apply (Finsupp.finite_of_degree_le (m * A + B)).subset
  intro u hu
  have hx : u none < m * A :=
    lt_of_le_of_lt (Nat.le_add_right (u none) ((K - 1) * totalJetDegree u)) hu.2.2.1
  change Finsupp.degree u ≤ m * A + B
  rw [exponentDegree_eq_x_add_totalJetDegree]
  exact Nat.add_le_add (Nat.le_of_lt hx) hu.2.1

/-- The finite set of globally eligible exponent vectors. -/
def globalEligibleExponents (d m A K B W C : ℕ) : Finset (JetVariable d →₀ ℕ) :=
  (globalEligibleExponentSet_finite d m A K B W C).toFinset

@[simp]
theorem mem_globalEligibleExponents {d m A K B W C : ℕ} {u : JetVariable d →₀ ℕ} :
    u ∈ globalEligibleExponents d m A K B W C ↔
      GlobalEligibleExponent d m A K B W C u := by
  simp [globalEligibleExponents, globalEligibleExponentSet]

/-- Polynomials supported on eligible global monomials. -/
def interpolationSpace (F : Type*) [CommSemiring F] (d m A K B W C : ℕ) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))

/-- Membership is pointwise eligibility of every support exponent. -/
theorem mem_interpolationSpace_iff {F : Type*} [CommSemiring F] {d m A K B W C : ℕ}
    {Q : DifferentialPolynomial F d} :
    Q ∈ interpolationSpace F d m A K B W C ↔
      ∀ u ∈ Q.support, GlobalEligibleExponent d m A K B W C u := by
  rw [interpolationSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_globalEligibleExponents]

/-- A monomial is in the space exactly when its exponent is eligible, unless its coefficient is
zero. -/
@[simp]
theorem monomial_mem_interpolationSpace {F : Type*} [CommSemiring F]
    {d m A K B W C : ℕ} {u : JetVariable d →₀ ℕ} {a : F} :
    MvPolynomial.monomial u a ∈ interpolationSpace F d m A K B W C ↔
      GlobalEligibleExponent d m A K B W C u ∨ a = 0 := by
  simp [interpolationSpace]

/-- Canonical monomial basis of the global interpolation space. -/
def interpolationSpaceBasis (F : Type*) [CommSemiring F] (d m A K B W C : ℕ) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))

end
end HiddenDerivative
end ReedSolomon
