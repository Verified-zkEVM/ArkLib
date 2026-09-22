/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Radical.Representative
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Splitting the distinct factors of a multivariate polynomial by one variable

Let `R` be a unique factorization domain, so that `MvPolynomial σ R` is a unique factorization
domain, and fix a variable `i : σ`. The distinct irreducible factors of a nonzero polynomial `Q`,
one representative per associate class, split into those of degree `0` in `X i` and those of
positive degree in `X i`. The product of the first group, `radicalContent i Q`, is the radical of
the content of `Q` with respect to `X i`; the product of the second group,
`radicalPrimPart i Q`, is the radical of its primitive part. Their product is
`UniqueFactorizationMonoid.radicalRep Q`.

Both products divide `Q`. Under a monoid-with-zero homomorphism into a target without zero
divisors, `Q` vanishes exactly when the content radical or one of the positive-degree factors
vanishes. Every degree function that is additive on nonzero products, such as `degreeOf j` and
`totalDegree`, gives the content radical and the positive-degree factors together at most the
degree of `Q`, and so gives the primitive-part radical alone at most the degree of `Q`.

These facts combine exceptional sets. If each positive-degree factor `c` fails a property only on
a set of challenges of size at most `bound c`, and the content radical vanishes only on a set of
size at most `contentBound`, then the zeros of `Q` fail the property only on a set of size at most
`contentBound + ∑ c, bound c` (`MvPolynomial.exists_exceptional_of_factor_exceptional`).

The zero-locus statements and the combination of exceptional sets need only
`UniqueFactorizationMonoid R`; the nonvanishing and degree statements also assume `IsDomain R`.
This file makes no characteristic, separability or incidence claim.

## Main statements

* `MvPolynomial.radicalContent_mul_radicalPrimPart`: the two products multiply to `radicalRep Q`.
* `MvPolynomial.radicalContent_mul_radicalPrimPart_dvd_self`, `radicalContent_dvd_self`,
  `radicalPrimPart_dvd_self`: the two products and their product divide `Q`.
* `MvPolynomial.degreeOf_radicalContent`: the content radical does not involve `X i`.
* `MvPolynomial.map_eq_zero_iff_radicalContent_or_exists`,
  `MvPolynomial.map_radicalContent_mul_radicalPrimPart_eq_zero_iff`: the zeros of `Q`.
* `MvPolynomial.add_sum_positiveDegreeFactorClasses_le` and its specializations
  `add_sum_degreeOf_positiveDegreeFactorClasses_le`,
  `add_sum_totalDegree_positiveDegreeFactorClasses_le` and
  `sum_degreeOf_positiveDegreeFactorClasses_le`: the degree budgets.
* `MvPolynomial.map_radicalContent_add_map_radicalPrimPart_le`, `map_radicalPrimPart_le` and
  their specializations `totalDegree_radicalPrimPart_le` and `degreeOf_radicalPrimPart_le`: the
  degree budgets for the two products.
* `MvPolynomial.exists_exceptional_of_factor_exceptional`: the combination of exceptional sets.
-/

@[expose] public section

open scoped BigOperators
open UniqueFactorizationMonoid

namespace MvPolynomial

noncomputable section

variable {R σ : Type*} [CommRing R] [UniqueFactorizationMonoid R]

/-- The distinct irreducible factor classes of `Q` of positive degree in `X i`. For `Q = 0` there
are none. -/
def positiveDegreeFactorClasses (i : σ) (Q : MvPolynomial σ R) :
    Finset (Associates (MvPolynomial σ R)) :=
  (primeFactors (Associates.mk Q)).filter fun c ↦ 0 < degreeOf i c.rep

/-- The product of one representative of every distinct irreducible factor class of `Q` of degree
`0` in `X i`: the radical of the content of `Q` with respect to `X i`, up to a unit. -/
def radicalContent (i : σ) (Q : MvPolynomial σ R) : MvPolynomial σ R :=
  ∏ c ∈ (primeFactors (Associates.mk Q)).filter (fun c ↦ degreeOf i c.rep = 0), c.rep

/-- The product of one representative of every distinct irreducible factor class of `Q` of
positive degree in `X i`: the radical of the primitive part of `Q` with respect to `X i`, up to a
unit. -/
def radicalPrimPart (i : σ) (Q : MvPolynomial σ R) : MvPolynomial σ R :=
  ∏ c ∈ positiveDegreeFactorClasses i Q, c.rep

/-- The zero polynomial has no factor classes. -/
@[simp]
theorem positiveDegreeFactorClasses_zero (i : σ) :
    positiveDegreeFactorClasses i (0 : MvPolynomial σ R) = ∅ := by
  simp [positiveDegreeFactorClasses, primeFactors_zero]

/-- The zero polynomial has no factor classes, so its content radical is `1`. -/
@[simp]
theorem radicalContent_zero (i : σ) : radicalContent i (0 : MvPolynomial σ R) = 1 := by
  simp [radicalContent, primeFactors_zero]

/-- `c` is a positive-degree factor class of `Q` exactly when it is a prime factor class of `Q`
whose representative has positive degree in `X i`. -/
@[simp]
theorem mem_positiveDegreeFactorClasses {i : σ} {Q : MvPolynomial σ R}
    {c : Associates (MvPolynomial σ R)} :
    c ∈ positiveDegreeFactorClasses i Q ↔
      c ∈ primeFactors (Associates.mk Q) ∧ 0 < degreeOf i c.rep :=
  Finset.mem_filter

/-- Each positive-degree factor class has an irreducible representative of positive degree in
`X i`. -/
theorem irreducible_rep_of_mem_positiveDegreeFactorClasses {i : σ} {Q : MvPolynomial σ R}
    {c : Associates (MvPolynomial σ R)} (hc : c ∈ positiveDegreeFactorClasses i Q) :
    Irreducible c.rep :=
  irreducible_rep_of_mem_primeFactors (mem_positiveDegreeFactorClasses.mp hc).1

/-- The content radical times the primitive-part radical is `radicalRep Q`. -/
theorem radicalContent_mul_radicalPrimPart (i : σ) (Q : MvPolynomial σ R) :
    radicalContent i Q * radicalPrimPart i Q = radicalRep Q := by
  rw [radicalContent, radicalPrimPart, positiveDegreeFactorClasses, radicalRep]
  have hfilter : (primeFactors (Associates.mk Q)).filter (fun c ↦ 0 < degreeOf i c.rep) =
      (primeFactors (Associates.mk Q)).filter (fun c ↦ ¬degreeOf i c.rep = 0) := by
    simp only [Nat.pos_iff_ne_zero]
  rw [hfilter, Finset.prod_filter_mul_prod_filter_not]

/-- The content radical times the primitive-part radical divides `Q`. -/
theorem radicalContent_mul_radicalPrimPart_dvd_self (i : σ) (Q : MvPolynomial σ R) :
    radicalContent i Q * radicalPrimPart i Q ∣ Q :=
  radicalContent_mul_radicalPrimPart i Q ▸ radicalRep_dvd_self Q

/-- The content radical divides `Q`. -/
theorem radicalContent_dvd_self (i : σ) (Q : MvPolynomial σ R) : radicalContent i Q ∣ Q :=
  (dvd_mul_right _ _).trans (radicalContent_mul_radicalPrimPart_dvd_self i Q)

/-- The primitive-part radical divides `Q`. -/
theorem radicalPrimPart_dvd_self (i : σ) (Q : MvPolynomial σ R) : radicalPrimPart i Q ∣ Q :=
  (dvd_mul_left _ _).trans (radicalContent_mul_radicalPrimPart_dvd_self i Q)

/-- A monoid-with-zero homomorphism into a nontrivial commutative monoid with zero without zero
divisors kills a nonzero `Q` exactly when it kills the content radical or the representative of a
positive-degree factor class.

The hypothesis `Q ≠ 0` is needed: `radicalContent i 0 = 1` and there are no positive-degree factor
classes of `0`, while every homomorphism kills `0`. -/
theorem map_eq_zero_iff_radicalContent_or_exists {K Fn : Type*} [CommMonoidWithZero K]
    [NoZeroDivisors K] [Nontrivial K] [FunLike Fn (MvPolynomial σ R) K]
    [MonoidWithZeroHomClass Fn (MvPolynomial σ R) K] (f : Fn) (i : σ)
    {Q : MvPolynomial σ R} (hQ : Q ≠ 0) :
    f Q = 0 ↔ f (radicalContent i Q) = 0 ∨
      ∃ c ∈ positiveDegreeFactorClasses i Q, f c.rep = 0 := by
  rw [map_eq_zero_iff_exists_primeFactors f hQ, radicalContent, map_prod,
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_filter, mem_positiveDegreeFactorClasses]
  constructor
  · rintro ⟨c, hc, hzero⟩
    by_cases hdeg : degreeOf i c.rep = 0
    · exact Or.inl ⟨c, ⟨hc, hdeg⟩, hzero⟩
    · exact Or.inr ⟨c, ⟨hc, Nat.pos_of_ne_zero hdeg⟩, hzero⟩
  · rintro (⟨c, ⟨hc, _⟩, hzero⟩ | ⟨c, ⟨hc, _⟩, hzero⟩) <;> exact ⟨c, hc, hzero⟩

/-- A nonzero `Q` and the product of its content and primitive-part radicals have the same zeros
under every monoid-with-zero homomorphism into a commutative monoid with zero without zero
divisors. The hypothesis `Q ≠ 0` is needed as in `map_radicalRep_eq_zero_iff`. -/
theorem map_radicalContent_mul_radicalPrimPart_eq_zero_iff {K Fn : Type*} [CommMonoidWithZero K]
    [NoZeroDivisors K] [FunLike Fn (MvPolynomial σ R) K]
    [MonoidWithZeroHomClass Fn (MvPolynomial σ R) K] (f : Fn) (i : σ)
    {Q : MvPolynomial σ R} (hQ : Q ≠ 0) :
    f (radicalContent i Q * radicalPrimPart i Q) = 0 ↔ f Q = 0 := by
  rw [radicalContent_mul_radicalPrimPart]
  exact map_radicalRep_eq_zero_iff f hQ

/-- Combining exceptional sets along the factor split. Let `ev w v` be monoid-with-zero
homomorphisms into a commutative monoid with zero without zero divisors, indexed by a challenge
`w` and a point `v`. Suppose the content radical of `Q` is killed by no `ev w v` for `w` outside a
set of size at most `contentBound`, and for each positive-degree factor class `c` there is a set of
size at most `bound c` outside which every zero `ev w v c.rep = 0` satisfies `Good w v`. Then
outside a set of size at most `contentBound + ∑ c, bound c`, every zero of `Q` satisfies
`Good w v`.

The hypothesis `Q ≠ 0` is needed: the zero polynomial has no positive-degree factor classes and
content radical `1`, so the hypotheses can hold with every bound `0` while `ev w v 0 = 0` for all
`w` and `v`. -/
theorem exists_exceptional_of_factor_exceptional {W V K Fn α : Type*} [CommMonoidWithZero K]
    [NoZeroDivisors K] [FunLike Fn (MvPolynomial σ R) K]
    [MonoidWithZeroHomClass Fn (MvPolynomial σ R) K]
    [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (i : σ) {Q : MvPolynomial σ R} (hQ : Q ≠ 0) (ev : W → V → Fn) (Good : W → V → Prop)
    (contentBound : α) (bound : Associates (MvPolynomial σ R) → α)
    (hcontent : ∃ ex : Finset W, (ex.card : α) ≤ contentBound ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent i Q) ≠ 0)
    (hfactors : ∀ c ∈ positiveDegreeFactorClasses i Q, ∃ ex : Finset W,
      (ex.card : α) ≤ bound c ∧ ∀ w ∉ ex, ∀ v, ev w v c.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : α) ≤ contentBound + ∑ c ∈ positiveDegreeFactorClasses i Q, bound c ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  classical
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  set S := positiveDegreeFactorClasses i Q
  choose factorEx hfCard hf using hfactors
  refine ⟨contentEx ∪ S.attach.biUnion fun c ↦ factorEx c.1 c.2, ?_, ?_⟩
  · have hcard : (contentEx ∪ S.attach.biUnion fun c ↦ factorEx c.1 c.2).card ≤
        contentEx.card + ∑ c ∈ S.attach, (factorEx c.1 c.2).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    calc ((contentEx ∪ S.attach.biUnion fun c ↦ factorEx c.1 c.2).card : α)
        ≤ contentEx.card + ∑ c ∈ S.attach, ((factorEx c.1 c.2).card : α) := by
          exact_mod_cast Nat.mono_cast (α := α) hcard
      _ ≤ contentBound + ∑ c ∈ S.attach, bound c.1 :=
          add_le_add hcCard (Finset.sum_le_sum fun c _ ↦ hfCard c.1 c.2)
      _ = contentBound + ∑ c ∈ S, bound c := by rw [Finset.sum_attach S bound]
  · intro w hw v hzero
    have hwc : w ∉ contentEx := fun hm ↦ hw (Finset.mem_union_left _ hm)
    have : Nontrivial K := ⟨⟨_, 0, hc w hwc v⟩⟩
    rcases (map_eq_zero_iff_radicalContent_or_exists (ev w v) i hQ).mp hzero with
      hcontent | ⟨c, hcS, hczero⟩
    · exact absurd hcontent (hc w hwc v)
    · refine hf c hcS w (fun hm ↦ hw (Finset.mem_union_right _ ?_)) v hczero
      exact Finset.mem_biUnion.mpr ⟨⟨c, hcS⟩, Finset.mem_attach _ _, hm⟩

variable [IsDomain R]

/-- The content radical is nonzero: it is a factor of `radicalRep Q`
(`radicalContent_mul_radicalPrimPart`), which is nonzero over a domain, also for `Q = 0`. -/
theorem radicalContent_ne_zero (i : σ) (Q : MvPolynomial σ R) : radicalContent i Q ≠ 0 :=
  left_ne_zero_of_mul (radicalContent_mul_radicalPrimPart i Q ▸ radicalRep_ne_zero Q)

/-- The primitive-part radical is nonzero: it is a factor of `radicalRep Q`
(`radicalContent_mul_radicalPrimPart`), which is nonzero over a domain, also for `Q = 0`. -/
theorem radicalPrimPart_ne_zero (i : σ) (Q : MvPolynomial σ R) : radicalPrimPart i Q ≠ 0 :=
  right_ne_zero_of_mul (radicalContent_mul_radicalPrimPart i Q ▸ radicalRep_ne_zero Q)

/-- The content radical does not involve `X i`. -/
theorem degreeOf_radicalContent (i : σ) (Q : MvPolynomial σ R) :
    degreeOf i (radicalContent i Q) = 0 := by
  rw [radicalContent, degreeOf_prod_eq _ _ fun c hc ↦
    rep_ne_zero_of_mem_primeFactors (Finset.mem_filter.mp hc).1]
  exact Finset.sum_eq_zero fun c hc ↦ (Finset.mem_filter.mp hc).2

/-- For `d` additive on products of nonzero polynomials, `d` of the content radical plus the
`d`-values of the positive-degree factors is at most `d Q`. -/
theorem add_sum_positiveDegreeFactorClasses_le {d : MvPolynomial σ R → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) (i : σ) (Q : MvPolynomial σ R) :
    d (radicalContent i Q) + ∑ c ∈ positiveDegreeFactorClasses i Q, d c.rep ≤ d Q := by
  have hprim : d (radicalPrimPart i Q) = ∑ c ∈ positiveDegreeFactorClasses i Q, d c.rep :=
    map_prod_rep_eq_sum hd (Finset.filter_subset _ _)
  rw [← hprim, ← hd _ _ (radicalContent_ne_zero i Q) (radicalPrimPart_ne_zero i Q),
    radicalContent_mul_radicalPrimPart, map_radicalRep_eq_sum hd]
  exact sum_primeFactors_le hd Q

/-- For `d` additive on products of nonzero polynomials, `d` of the content radical plus `d` of the
primitive-part radical is at most `d Q`. -/
theorem map_radicalContent_add_map_radicalPrimPart_le {d : MvPolynomial σ R → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) (i : σ) (Q : MvPolynomial σ R) :
    d (radicalContent i Q) + d (radicalPrimPart i Q) ≤ d Q := by
  rw [radicalPrimPart,
    map_prod_rep_eq_sum (s := positiveDegreeFactorClasses i Q) hd (Finset.filter_subset _ _)]
  exact add_sum_positiveDegreeFactorClasses_le hd i Q

/-- For `d` additive on products of nonzero polynomials, `d` of the primitive-part radical is at
most `d Q`. -/
theorem map_radicalPrimPart_le {d : MvPolynomial σ R → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) (i : σ) (Q : MvPolynomial σ R) :
    d (radicalPrimPart i Q) ≤ d Q :=
  (Nat.le_add_left _ _).trans (map_radicalContent_add_map_radicalPrimPart_le hd i Q)

/-- The degree in `X j` of the content radical plus the degrees in `X j` of the positive-degree
factors is at most the degree of `Q` in `X j`. -/
theorem add_sum_degreeOf_positiveDegreeFactorClasses_le (i j : σ) (Q : MvPolynomial σ R) :
    degreeOf j (radicalContent i Q) +
        ∑ c ∈ positiveDegreeFactorClasses i Q, degreeOf j c.rep ≤ degreeOf j Q :=
  add_sum_positiveDegreeFactorClasses_le (fun _ _ hx hy ↦ degreeOf_mul_eq hx hy) i Q

/-- The total degree of the content radical plus the total degrees of the positive-degree factors
is at most the total degree of `Q`. -/
theorem add_sum_totalDegree_positiveDegreeFactorClasses_le (i : σ) (Q : MvPolynomial σ R) :
    totalDegree (radicalContent i Q) +
        ∑ c ∈ positiveDegreeFactorClasses i Q, totalDegree c.rep ≤ totalDegree Q :=
  add_sum_positiveDegreeFactorClasses_le (fun _ _ hx hy ↦ totalDegree_mul_of_isDomain hx hy) i Q

/-- The total degree of the primitive-part radical is at most the total degree of `Q`. -/
theorem totalDegree_radicalPrimPart_le (i : σ) (Q : MvPolynomial σ R) :
    totalDegree (radicalPrimPart i Q) ≤ totalDegree Q :=
  map_radicalPrimPart_le (fun _ _ hx hy ↦ totalDegree_mul_of_isDomain hx hy) i Q

/-- The degree in `X j` of the primitive-part radical is at most the degree of `Q` in `X j`. -/
theorem degreeOf_radicalPrimPart_le (i j : σ) (Q : MvPolynomial σ R) :
    degreeOf j (radicalPrimPart i Q) ≤ degreeOf j Q :=
  map_radicalPrimPart_le (fun _ _ hx hy ↦ degreeOf_mul_eq hx hy) i Q

/-- The degrees in `X i` of the positive-degree factors sum to at most the degree of `Q` in
`X i`. -/
theorem sum_degreeOf_positiveDegreeFactorClasses_le (i : σ) (Q : MvPolynomial σ R) :
    ∑ c ∈ positiveDegreeFactorClasses i Q, degreeOf i c.rep ≤ degreeOf i Q := by
  have h := add_sum_degreeOf_positiveDegreeFactorClasses_le i i Q
  rwa [degreeOf_radicalContent, zero_add] at h

end

end MvPolynomial
