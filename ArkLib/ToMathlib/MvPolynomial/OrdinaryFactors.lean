/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Distinct irreducible factors of an ordinary multivariate polynomial

This file extracts one representative of every irreducible associate class of a nonzero
multivariate polynomial. Factors involving the distinguished `none` variable are separated from
the remaining content. Their squarefree product has the same zero locus as the original
polynomial after every map to a domain, and its coordinate degrees are bounded by those of the
original polynomial.

This is only factor extraction. It makes no characteristic, separability, or incidence claim.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open UniqueFactorizationMonoid

variable {F : Type*} {σ : Type*} [Field F]

local instance : DecidableEq (Associates (MvPolynomial (Option σ) F)) := Classical.decEq _

/-- A fixed polynomial representative of an associate class. -/
def ordinaryFactorRepresentative {M : Type*} [CommMonoid M]
    (a : Associates M) : M :=
  Quotient.out a

theorem mk_ordinaryFactorRepresentative {M : Type*} [CommMonoid M]
    (a : Associates M) :
    Associates.mk (ordinaryFactorRepresentative a) = a :=
  Quotient.out_eq a

theorem ordinaryFactorRepresentative_injective {M : Type*} [CommMonoid M] :
    Function.Injective (@ordinaryFactorRepresentative M _) := by
  intro a b hab
  rw [← mk_ordinaryFactorRepresentative a, ← mk_ordinaryFactorRepresentative b, hab]

private theorem ordinaryFactorRepresentative_ne_zero
    {M : Type*} [CommMonoidWithZero M] {a : Associates M} (ha : a ≠ 0) :
    ordinaryFactorRepresentative a ≠ 0 := by
  intro h
  apply ha
  rw [← mk_ordinaryFactorRepresentative a, h]
  exact Associates.mk_zero

private theorem ordinaryFactorRepresentative_irreducible
    {M : Type*} [CommMonoidWithZero M] {a : Associates M} (ha : Irreducible a) :
    Irreducible (ordinaryFactorRepresentative a) := by
  rw [← Associates.irreducible_mk, mk_ordinaryFactorRepresentative]
  exact ha

private theorem mk_multiset_prod_ordinaryFactorRepresentative
    {M : Type*} [CommMonoid M] (s : Multiset (Associates M)) :
    Associates.mk ((s.map ordinaryFactorRepresentative).prod) = s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [← Associates.mk_mul_mk, mk_ordinaryFactorRepresentative, ih]

private theorem mk_finset_prod_ordinaryFactorRepresentative
    {M : Type*} [CommMonoid M] (s : Finset (Associates M)) :
    Associates.mk (∏ a ∈ s, ordinaryFactorRepresentative a) = ∏ a ∈ s, a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      rw [← Associates.mk_mul_mk, mk_ordinaryFactorRepresentative, ih]

/-- The finite set of irreducible associate classes occurring in `Q`, without multiplicity. -/
def ordinaryFactorClasses (Q : MvPolynomial (Option σ) F) :
    Finset (Associates (MvPolynomial (Option σ) F)) :=
  (normalizedFactors (Associates.mk Q)).toFinset

/-- The factors of `Q` having positive degree in the distinguished root variable. -/
def ordinaryRootFactorClasses (Q : MvPolynomial (Option σ) F) :
    Finset (Associates (MvPolynomial (Option σ) F)) :=
  (ordinaryFactorClasses Q).filter fun a =>
    0 < degreeOf none (ordinaryFactorRepresentative a)

/-- The squarefree product of factors of `Q` independent of the distinguished root variable. -/
def ordinaryContent (Q : MvPolynomial (Option σ) F) : MvPolynomial (Option σ) F :=
  ∏ a ∈ (ordinaryFactorClasses Q).filter fun a =>
    degreeOf none (ordinaryFactorRepresentative a) = 0,
    ordinaryFactorRepresentative a

/-- The squarefree product of factors of `Q` having positive root-variable degree. -/
def ordinaryRootProduct (Q : MvPolynomial (Option σ) F) : MvPolynomial (Option σ) F :=
  ∏ a ∈ ordinaryRootFactorClasses Q, ordinaryFactorRepresentative a

/-- The squarefree product of all irreducible factors of `Q`. -/
def ordinarySquarefreeProduct (Q : MvPolynomial (Option σ) F) : MvPolynomial (Option σ) F :=
  ∏ a ∈ ordinaryFactorClasses Q, ordinaryFactorRepresentative a

theorem ordinaryFactorClasses_representatives_injective
    (Q : MvPolynomial (Option σ) F)
    {a b : Associates (MvPolynomial (Option σ) F)}
    (_ha : a ∈ ordinaryFactorClasses Q) (_hb : b ∈ ordinaryFactorClasses Q)
    (h : ordinaryFactorRepresentative a = ordinaryFactorRepresentative b) : a = b :=
  ordinaryFactorRepresentative_injective h

theorem ordinaryFactorClasses_irreducible
    (Q : MvPolynomial (Option σ) F) {a : Associates (MvPolynomial (Option σ) F)}
    (ha : a ∈ ordinaryFactorClasses Q) :
    Irreducible (ordinaryFactorRepresentative a) := by
  apply ordinaryFactorRepresentative_irreducible
  exact irreducible_of_normalized_factor a (by simpa [ordinaryFactorClasses] using ha)

theorem ordinaryRootFactorClasses_spec
    (Q : MvPolynomial (Option σ) F) {a : Associates (MvPolynomial (Option σ) F)}
    (ha : a ∈ ordinaryRootFactorClasses Q) :
    Irreducible (ordinaryFactorRepresentative a) ∧
      0 < degreeOf none (ordinaryFactorRepresentative a) := by
  rw [ordinaryRootFactorClasses, Finset.mem_filter] at ha
  exact ⟨ordinaryFactorClasses_irreducible Q ha.1, ha.2⟩

theorem ordinary_split_product (Q : MvPolynomial (Option σ) F) :
    ordinaryContent Q * ordinaryRootProduct Q = ordinarySquarefreeProduct Q := by
  rw [ordinaryContent, ordinaryRootProduct, ordinarySquarefreeProduct,
    ordinaryRootFactorClasses]
  rw [← Finset.prod_union]
  · congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨ha, hz⟩ | ⟨ha, hp⟩)
      · exact ha
      · exact ha
    · intro ha
      by_cases hz : degreeOf none (ordinaryFactorRepresentative a) = 0
      · exact Or.inl ⟨ha, hz⟩
      · exact Or.inr ⟨ha, by omega⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    omega

theorem ordinaryContent_ne_zero (Q : MvPolynomial (Option σ) F) : ordinaryContent Q ≠ 0 := by
  rw [ordinaryContent]
  exact Finset.prod_ne_zero_iff.mpr fun a ha => by
    rw [Finset.mem_filter] at ha
    apply ordinaryFactorRepresentative_ne_zero
    apply ne_zero_of_mem_normalizedFactors
    simpa [ordinaryFactorClasses] using ha.1

theorem ordinaryRootProduct_ne_zero (Q : MvPolynomial (Option σ) F) :
    ordinaryRootProduct Q ≠ 0 := by
  rw [ordinaryRootProduct]
  exact Finset.prod_ne_zero_iff.mpr fun a ha => by
    exact (ordinaryRootFactorClasses_spec Q ha).1.ne_zero

theorem degreeOf_ordinaryContent_none (Q : MvPolynomial (Option σ) F) :
    degreeOf none (ordinaryContent Q) = 0 := by
  rw [ordinaryContent, degreeOf_prod_eq]
  · simp
  · intro a ha
    rw [Finset.mem_filter] at ha
    apply ordinaryFactorRepresentative_ne_zero
    apply ne_zero_of_mem_normalizedFactors
    simpa [ordinaryFactorClasses] using ha.1

theorem ordinarySquarefreeProduct_ne_zero (Q : MvPolynomial (Option σ) F) :
    ordinarySquarefreeProduct Q ≠ 0 := by
  rw [← ordinary_split_product]
  exact mul_ne_zero (ordinaryContent_ne_zero Q) (ordinaryRootProduct_ne_zero Q)

private theorem ordinarySquarefreeProduct_dvd
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) :
    ordinarySquarefreeProduct Q ∣ Q := by
  apply Associates.mk_dvd_mk.mp
  rw [ordinarySquarefreeProduct, mk_finset_prod_ordinaryFactorRepresentative]
  apply (Multiset.toFinset_prod_dvd_prod
    (normalizedFactors (Associates.mk Q))).trans
  exact (prod_normalizedFactors (by simpa using hQ)).dvd

private theorem degreeOf_le_of_dvd
    {P Q : MvPolynomial (Option σ) F} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P ∣ Q)
    (j : Option σ) : degreeOf j P ≤ degreeOf j Q := by
  obtain ⟨H, rfl⟩ := h
  have hH : H ≠ 0 := (mul_ne_zero_iff.mp hQ).2
  rw [degreeOf_mul_eq hP hH]
  exact le_add_of_nonneg_right zero_le

theorem ordinarySquarefreeProduct_zero_iff
    {D : Type*} [CommRing D] [IsDomain D]
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0)
    (f : MvPolynomial (Option σ) F →+* D) :
    f (ordinarySquarefreeProduct Q) = 0 ↔ f Q = 0 := by
  constructor
  · intro hsquare
    obtain ⟨H, hQeq⟩ := ordinarySquarefreeProduct_dvd Q hQ
    rw [hQeq, map_mul, hsquare, zero_mul]
  · intro hQzero
    let s := normalizedFactors (Associates.mk Q)
    have hmkQ : Associates.mk Q ≠ 0 := by simpa using hQ
    have hfullassoc : Associated ((s.map ordinaryFactorRepresentative).prod) Q := by
      rw [← Associates.mk_eq_mk_iff_associated,
        mk_multiset_prod_ordinaryFactorRepresentative]
      exact associated_iff_eq.mp (prod_normalizedFactors hmkQ)
    have hfullzero : f ((s.map ordinaryFactorRepresentative).prod) = 0 := by
      exact (hfullassoc.map f).eq_zero_iff.mpr hQzero
    rw [map_multiset_prod] at hfullzero
    have hmem : 0 ∈ (s.map ordinaryFactorRepresentative).map f :=
      Multiset.prod_eq_zero_iff.mp hfullzero
    rw [Multiset.mem_map] at hmem
    obtain ⟨P, hP, hPzero⟩ := hmem
    rw [Multiset.mem_map] at hP
    obtain ⟨a, ha, rfl⟩ := hP
    rw [ordinarySquarefreeProduct, map_prod]
    apply Finset.prod_eq_zero (i := a)
    · simpa [ordinaryFactorClasses, s] using ha
    · exact hPzero

theorem ordinary_split_zero_iff
    {D : Type*} [CommRing D] [IsDomain D]
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0)
    (f : MvPolynomial (Option σ) F →+* D) :
    f (ordinaryContent Q * ordinaryRootProduct Q) = 0 ↔ f Q = 0 := by
  rw [ordinary_split_product]
  exact ordinarySquarefreeProduct_zero_iff Q hQ f

theorem ordinary_degree_sum_le
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) (j : Option σ) :
    degreeOf j (ordinaryContent Q) +
        ∑ a ∈ ordinaryRootFactorClasses Q,
          degreeOf j (ordinaryFactorRepresentative a) ≤
      degreeOf j Q := by
  have hcontent := ordinaryContent_ne_zero Q
  have hroot := ordinaryRootProduct_ne_zero Q
  calc
    degreeOf j (ordinaryContent Q) +
          ∑ a ∈ ordinaryRootFactorClasses Q,
            degreeOf j (ordinaryFactorRepresentative a) =
        degreeOf j (ordinaryContent Q * ordinaryRootProduct Q) := by
          rw [degreeOf_mul_eq hcontent hroot, ordinaryRootProduct, degreeOf_prod_eq]
          intro a ha
          exact (ordinaryRootFactorClasses_spec Q ha).1.ne_zero
    _ = degreeOf j (ordinarySquarefreeProduct Q) := by rw [ordinary_split_product]
    _ ≤ degreeOf j Q := degreeOf_le_of_dvd
      (by rw [← ordinary_split_product]; exact mul_ne_zero hcontent hroot)
      hQ (ordinarySquarefreeProduct_dvd Q hQ) j

theorem ordinary_root_degree_sum_le (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) :
    ∑ a ∈ ordinaryRootFactorClasses Q,
        degreeOf none (ordinaryFactorRepresentative a) ≤ degreeOf none Q := by
  have h := ordinary_degree_sum_le Q hQ none
  rw [degreeOf_ordinaryContent_none, zero_add] at h
  exact h

section Canary

variable (a : F) (ha : a ≠ 0) (j : σ)

def ordinaryFactorsCanary : MvPolynomial (Option σ) F :=
  X (some j) * (C a * X none + 1) ^ 2

private theorem ordinaryFactorsCanary_linear_ne_zero (ha : a ≠ 0) :
    (C a * X none + 1 : MvPolynomial (Option σ) F) ≠ 0 := by
  intro h
  have hp := congrArg (pderiv none) h
  exact ha (by simpa using hp)

private theorem ordinaryFactorsCanary_ne_zero (ha : a ≠ 0) :
    ordinaryFactorsCanary a j ≠ 0 := by
  rw [ordinaryFactorsCanary]
  exact mul_ne_zero (X_ne_zero (some j))
    (pow_ne_zero 2 (ordinaryFactorsCanary_linear_ne_zero (σ := σ) a ha))

theorem ordinaryFactorsCanary_root_degree (ha : a ≠ 0) :
    degreeOf none (ordinaryFactorsCanary a j) = 2 := by
  have hterm : degreeOf none (C a * X none : MvPolynomial (Option σ) F) = 1 := by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) (X_ne_zero none)]
    simp
  have hlinear : degreeOf none (C a * X none + 1 : MvPolynomial (Option σ) F) = 1 := by
    rw [degreeOf_add_eq_of_degreeOf_lt]
    · exact hterm
    · rw [hterm]
      simp
  rw [ordinaryFactorsCanary,
    degreeOf_mul_eq (X_ne_zero (some j))
      (pow_ne_zero 2 (ordinaryFactorsCanary_linear_ne_zero (σ := σ) a ha)),
    degreeOf_X_of_ne (Ne.symm (Option.some_ne_none j)),
    degreeOf_pow_eq none (C a * X none + 1) 2
      (ordinaryFactorsCanary_linear_ne_zero (σ := σ) a ha), hlinear]

theorem ordinaryFactorsCanary_content_degree (ha : a ≠ 0) :
    degreeOf (some j) (ordinaryFactorsCanary a j) = 1 := by
  have hterm :
      degreeOf (some j) (C a * X none : MvPolynomial (Option σ) F) = 0 := by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) (X_ne_zero none),
      degreeOf_X_of_ne (Option.some_ne_none j)]
    simp
  have hlinear :
      degreeOf (some j) (C a * X none + 1 : MvPolynomial (Option σ) F) = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      degreeOf (some j) (C a * X none + 1 : MvPolynomial (Option σ) F) ≤
          max (degreeOf (some j) (C a * X none : MvPolynomial (Option σ) F))
            (degreeOf (some j) (1 : MvPolynomial (Option σ) F)) :=
        degreeOf_add_le _ _ _
      _ = 0 := by rw [hterm, degreeOf_one]; simp
  rw [ordinaryFactorsCanary,
    degreeOf_mul_eq (X_ne_zero (some j))
      (pow_ne_zero 2 (ordinaryFactorsCanary_linear_ne_zero (σ := σ) a ha)),
    degreeOf_X_self,
    degreeOf_pow_eq (some j) (C a * X none + 1) 2
      (ordinaryFactorsCanary_linear_ne_zero (σ := σ) a ha), hlinear]

theorem ordinaryFactorsCanary_zero_iff
    {D : Type*} [CommRing D] [IsDomain D]
    (ha : a ≠ 0)
    (f : MvPolynomial (Option σ) F →+* D) :
    f (ordinaryContent (ordinaryFactorsCanary a j) *
        ordinaryRootProduct (ordinaryFactorsCanary a j)) = 0 ↔
      f (ordinaryFactorsCanary a j) = 0 :=
  ordinary_split_zero_iff (ordinaryFactorsCanary a j)
    (ordinaryFactorsCanary_ne_zero a j ha) f

end Canary

end

end MvPolynomial
