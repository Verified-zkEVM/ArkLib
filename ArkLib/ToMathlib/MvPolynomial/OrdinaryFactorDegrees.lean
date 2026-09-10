/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.OrdinaryFactors

/-!
# Total-degree budgets for distinct ordinary factors

The ordinary-factor split separates the factors involving one distinguished root variable from
the root-independent content.  This file adds the total-degree budget needed when all remaining
variables participate in a reconstruction map.  Over a domain, total degree is additive on
nonzero products, so the content degree plus the sum of the distinct positive-root factor degrees
is bounded by the original polynomial's total degree.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open UniqueFactorizationMonoid

variable {F σ : Type*} [Field F]

local instance : DecidableEq (Associates (MvPolynomial (Option σ) F)) :=
  instDecidableEqAssociatesOption_arkLib

private theorem mk_finset_prod_ordinaryFactorRepresentative'
    {M : Type*} [CommMonoid M] (s : Finset (Associates M)) :
    Associates.mk (∏ a ∈ s, ordinaryFactorRepresentative a) = ∏ a ∈ s, a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      rw [← Associates.mk_mul_mk, mk_ordinaryFactorRepresentative, ih]

/-- The product of all distinct factor representatives divides the original polynomial. -/
theorem ordinarySquarefreeProduct_dvd
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) :
    ordinarySquarefreeProduct Q ∣ Q := by
  apply Associates.mk_dvd_mk.mp
  rw [ordinarySquarefreeProduct, mk_finset_prod_ordinaryFactorRepresentative']
  rw [ordinaryFactorClasses]
  apply (Multiset.toFinset_prod_dvd_prod
    (normalizedFactors (Associates.mk Q))).trans
  exact (prod_normalizedFactors (by simpa using hQ)).dvd

private theorem totalDegree_finset_prod_eq_sum
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Option σ) F)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        totalDegree_mul_of_isDomain (hf i (Finset.mem_insert_self i s))
          (Finset.prod_ne_zero_iff.mpr fun j hj =>
            hf j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The retained root-independent content and all distinct positive-root factors share the
original total-degree budget.  Repeated factors of the source are intentionally counted once. -/
theorem ordinary_totalDegree_sum_le
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) :
    (ordinaryContent Q).totalDegree +
        ∑ a ∈ ordinaryRootFactorClasses Q,
          (ordinaryFactorRepresentative a).totalDegree ≤ Q.totalDegree := by
  have hcontent := ordinaryContent_ne_zero Q
  have hroot := ordinaryRootProduct_ne_zero Q
  have hsquare : ordinarySquarefreeProduct Q ≠ 0 := ordinarySquarefreeProduct_ne_zero Q
  calc
    (ordinaryContent Q).totalDegree +
          ∑ a ∈ ordinaryRootFactorClasses Q,
            (ordinaryFactorRepresentative a).totalDegree =
        (ordinaryContent Q * ordinaryRootProduct Q).totalDegree := by
      rw [totalDegree_mul_of_isDomain hcontent hroot, ordinaryRootProduct,
        totalDegree_finset_prod_eq_sum]
      intro a ha
      exact (ordinaryRootFactorClasses_spec Q ha).1.ne_zero
    _ = (ordinarySquarefreeProduct Q).totalDegree := by rw [ordinary_split_product]
    _ ≤ Q.totalDegree := totalDegree_le_of_dvd_of_isDomain
      (ordinarySquarefreeProduct_dvd Q hQ) hQ

/-- The total degree of the positive-root squarefree product alone is bounded by the source. -/
theorem totalDegree_ordinaryRootProduct_le
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0) :
    (ordinaryRootProduct Q).totalDegree ≤ Q.totalDegree := by
  have h := ordinary_totalDegree_sum_le Q hQ
  rw [ordinaryRootProduct,
    totalDegree_finset_prod_eq_sum (hf := fun a ha =>
      (ordinaryRootFactorClasses_spec Q ha).1.ne_zero)]
  exact (Nat.le_add_left _ _).trans h

end

end MvPolynomial
