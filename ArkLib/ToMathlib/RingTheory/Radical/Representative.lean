/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Radical.Basic

/-!
# A representative of the radical without a normalization

Mathlib's `UniqueFactorizationMonoid.radical` needs a `NormalizationMonoid`, which pinned Mathlib
does not provide for rings such as `MvPolynomial σ F`. The monoid of associates always has one, so
`radical (Associates.mk a)` is defined for every element `a` of a unique factorization monoid.
This file lifts it back: `UniqueFactorizationMonoid.radicalRep a` multiplies one chosen
representative `c.rep` of every prime factor class `c` of `Associates.mk a`. It is the
product of the distinct irreducible factors of `a`, each taken once, up to units.

The main facts are that `radicalRep a` divides `a`, that a nonzero `a` and `radicalRep a` have the
same zeros under every monoid-with-zero homomorphism into a commutative monoid with zero without
zero divisors, and that a degree function which is additive on nonzero products assigns the
distinct factors a total of at most the degree of `a`.

## Main statements

* `Associates.mk_prod_rep`: `Associates.mk` of a product of representatives is the product
  of the classes.
* `UniqueFactorizationMonoid.mk_radicalRep`: `radicalRep a` represents `radical (Associates.mk a)`.
* `UniqueFactorizationMonoid.radicalRep_dvd_self`, `radicalRep_ne_zero`,
  `radicalRep_eq_of_associated`, `radicalRep_zero`.
* `UniqueFactorizationMonoid.irreducible_rep_of_mem_primeFactors`: each representative is
  irreducible.
* `UniqueFactorizationMonoid.primeFactors_mk_pow_of_prime`,
  `associated_radicalRep_pow_of_prime`: the radical of a prime power.
* `UniqueFactorizationMonoid.map_eq_zero_iff_exists_primeFactors`: a homomorphism kills a nonzero
  `a` exactly when it kills the representative of one of its prime factor classes.
* `UniqueFactorizationMonoid.map_radicalRep_eq_zero_iff`: `a` and `radicalRep a` have the same
  zeros.
* `UniqueFactorizationMonoid.map_le_of_dvd`, `map_eq_of_associated`,
  `map_prod_rep_eq_sum`, `sum_primeFactors_le`: a degree function additive on nonzero products is
  monotone under divisibility and constant on associate classes, its value on a product of
  distinct factors is the sum of their values, and the sum over all distinct factors of `a` is at
  most its value on `a`.
-/

@[expose] public section

open scoped BigOperators

namespace Associates

/-- A fixed representative of an associate class, chosen by `Quot.out`. Mathlib's
`Associates.out` needs a `NormalizationMonoid`; this choice does not. -/
noncomputable def rep {M : Type*} [Monoid M] (c : Associates M) : M :=
  Quot.out c

/-- The representative of `c` lies in `c`. -/
@[simp]
theorem mk_rep {M : Type*} [Monoid M] (c : Associates M) : Associates.mk c.rep = c :=
  quot_out c

/-- Distinct classes have distinct representatives. -/
theorem rep_injective {M : Type*} [Monoid M] : Function.Injective (@rep M _) := fun c d h ↦ by
  rw [← mk_rep c, ← mk_rep d, h]

/-- `Associates.mk` of a finite product of representatives `(f i).rep` is the product of the
classes `f i`. -/
theorem mk_prod_rep {M ι : Type*} [CommMonoid M] (s : Finset ι) (f : ι → Associates M) :
    Associates.mk (∏ i ∈ s, (f i).rep) = ∏ i ∈ s, f i := by
  rw [← mkMonoidHom_apply, map_prod]
  simp only [mkMonoidHom_apply, mk_rep]

end Associates

namespace UniqueFactorizationMonoid

noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] {a b : M}

/-- A representative of the radical of `a`: the product of one chosen representative
`c.rep` of every prime factor class `c` of `Associates.mk a`. Each distinct irreducible
factor of `a` occurs once, up to a unit. This needs no `NormalizationMonoid` on `M`. For `a = 0`
there are no prime factor classes and `radicalRep 0 = 1`. -/
def radicalRep (a : M) : M :=
  ∏ c ∈ primeFactors (Associates.mk a), c.rep

/-- `0` has no prime factor classes, so its radical representative is `1`. -/
@[simp]
theorem radicalRep_zero : radicalRep (0 : M) = 1 := by
  simp [radicalRep, primeFactors_zero]

/-- `radicalRep a` represents the radical of `Associates.mk a`. -/
theorem mk_radicalRep (a : M) : Associates.mk (radicalRep a) = radical (Associates.mk a) :=
  Associates.mk_prod_rep _ _

/-- Associated elements have the same prime factor classes, so the same `radicalRep`. -/
theorem radicalRep_eq_of_associated (h : Associated a b) : radicalRep a = radicalRep b := by
  rw [radicalRep, radicalRep, Associates.mk_eq_mk_iff_associated.mpr h]

/-- `radicalRep a` divides `a`. For `a = 0` this is `1 ∣ 0`. -/
theorem radicalRep_dvd_self (a : M) : radicalRep a ∣ a := by
  rw [← Associates.mk_dvd_mk, mk_radicalRep]
  exact radical_dvd_self

/-- `radicalRep a` is never zero in a nontrivial monoid. -/
theorem radicalRep_ne_zero [Nontrivial M] (a : M) : radicalRep a ≠ 0 := by
  rw [← Associates.mk_ne_zero, mk_radicalRep]
  exact radical_ne_zero

/-- The representative of each prime factor class of `a` is irreducible. -/
theorem irreducible_rep_of_mem_primeFactors {c : Associates M}
    (hc : c ∈ primeFactors (Associates.mk a)) : Irreducible (c.rep) := by
  rw [← Associates.irreducible_mk, Associates.mk_rep]
  exact irreducible_of_normalized_factor c (mem_primeFactors.mp hc)

/-- The representative of each prime factor class of `a` is nonzero. -/
theorem rep_ne_zero_of_mem_primeFactors {c : Associates M}
    (hc : c ∈ primeFactors (Associates.mk a)) : c.rep ≠ 0 :=
  (irreducible_rep_of_mem_primeFactors hc).ne_zero

/-- For a prime `p` and `n ≠ 0`, the only prime factor class of `p ^ n` is that of `p`. The
hypothesis `n ≠ 0` is needed: `p ^ 0 = 1` has no prime factor classes. -/
theorem primeFactors_mk_pow_of_prime {p : M} (hp : Prime p) {n : ℕ} (hn : n ≠ 0) :
    primeFactors (Associates.mk (p ^ n)) = {Associates.mk p} := by
  classical
  rw [Associates.mk_pow, primeFactors_pow _ hn, ← toFinset_normalizedFactors,
    normalizedFactors_irreducible (Associates.prime_mk.mpr hp).irreducible, normalize_eq,
    Multiset.toFinset_singleton]

/-- For a prime `p` and `n ≠ 0`, `radicalRep (p ^ n)` is associated to `p`. -/
theorem associated_radicalRep_pow_of_prime {p : M} (hp : Prime p) {n : ℕ} (hn : n ≠ 0) :
    Associated (radicalRep (p ^ n)) p := by
  rw [← Associates.mk_eq_mk_iff_associated, radicalRep, primeFactors_mk_pow_of_prime hp hn,
    Finset.prod_singleton, Associates.mk_rep]

/-- A monoid-with-zero homomorphism `f` into a nontrivial commutative monoid with zero without
zero divisors kills a nonzero `a` exactly when it kills the representative of one of the prime
factor classes of `a`.

The hypothesis `a ≠ 0` is needed: `0` has no prime factor classes, while `f 0 = 0`. Nontriviality
is needed: in the zero ring `f a = 0` for a unit `a`, which again has no prime factor classes. -/
theorem map_eq_zero_iff_exists_primeFactors {D F : Type*} [CommMonoidWithZero D]
    [NoZeroDivisors D] [Nontrivial D] [FunLike F M D] [MonoidWithZeroHomClass F M D]
    (f : F) (ha : a ≠ 0) :
    f a = 0 ↔ ∃ c ∈ primeFactors (Associates.mk a), f (c.rep) = 0 := by
  set s := normalizedFactors (Associates.mk a)
  have hprod : Associates.mk (s.map Associates.rep).prod = Associates.mk a := by
    rw [← Associates.prod_mk, Multiset.map_map]
    simp only [Function.comp_def, Associates.mk_rep, Multiset.map_id']
    exact associated_iff_eq.mp (prod_normalizedFactors (Associates.mk_ne_zero.mpr ha))
  have hassoc : Associated (s.map Associates.rep).prod a :=
    Associates.mk_eq_mk_iff_associated.mp hprod
  rw [← (hassoc.map f).eq_zero_iff, map_multiset_prod, Multiset.prod_eq_zero_iff,
    Multiset.map_map, Multiset.mem_map]
  simp only [Function.comp_apply, mem_primeFactors, s]

/-- A nonzero `a` and `radicalRep a` have the same zeros under every monoid-with-zero homomorphism
into a commutative monoid with zero without zero divisors.

The hypothesis `a ≠ 0` is needed: `radicalRep 0 = 1`, which a homomorphism into a nontrivial
target does not kill. -/
theorem map_radicalRep_eq_zero_iff {D F : Type*} [CommMonoidWithZero D] [NoZeroDivisors D]
    [FunLike F M D] [MonoidWithZeroHomClass F M D] (f : F) (ha : a ≠ 0) :
    f (radicalRep a) = 0 ↔ f a = 0 := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · exact ⟨fun _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩
  rw [map_eq_zero_iff_exists_primeFactors f ha, radicalRep, map_prod, Finset.prod_eq_zero_iff]

/-- Let `d` be additive on products of nonzero elements, as `MvPolynomial.degreeOf` and
`MvPolynomial.totalDegree` are over a domain. Then `d` of a product of representatives of a set
of prime factor classes of `a` is the sum of their `d`-values.

The value `d 1 = 0` follows from additivity at `1 * 1`, which uses `1 ≠ 0`; this is why `M` is
assumed nontrivial. -/
theorem map_prod_rep_eq_sum [Nontrivial M] {d : M → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y)
    {s : Finset (Associates M)} (hs : s ⊆ primeFactors (Associates.mk a)) :
    d (∏ c ∈ s, c.rep) = ∑ c ∈ s, d (c.rep) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h1 := hd 1 1 one_ne_zero one_ne_zero
      rw [one_mul] at h1
      rw [Finset.prod_empty, Finset.sum_empty]
      omega
  | @insert c s hc ih =>
      have hs' : s ⊆ primeFactors (Associates.mk a) := (Finset.subset_insert c s).trans hs
      have hc0 := rep_ne_zero_of_mem_primeFactors (hs (Finset.mem_insert_self c s))
      have hprod : ∏ c ∈ s, c.rep ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun c' hc' ↦ rep_ne_zero_of_mem_primeFactors (hs' hc')
      rw [Finset.prod_insert hc, Finset.sum_insert hc, hd _ _ hc0 hprod, ih hs']

/-- For `d` additive on products of nonzero elements, `d (radicalRep a)` is the sum of the
`d`-values of the representatives of the prime factor classes of `a`. -/
theorem map_radicalRep_eq_sum [Nontrivial M] {d : M → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) (a : M) :
    d (radicalRep a) = ∑ c ∈ primeFactors (Associates.mk a), d (c.rep) :=
  map_prod_rep_eq_sum hd subset_rfl

/-- For `d` additive on products of nonzero elements, `d` of a divisor of a nonzero element is at
most `d` of that element. -/
theorem map_le_of_dvd {N : Type*} [MonoidWithZero N] {d : N → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) {x y : N}
    (hy : y ≠ 0) (hxy : x ∣ y) : d x ≤ d y := by
  obtain ⟨e, rfl⟩ := hxy
  rw [hd _ _ (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)]
  exact Nat.le_add_right _ _

/-- For `d` additive on products of nonzero elements, associated nonzero elements have the same
`d`-value. The hypothesis `y ≠ 0` is needed because additivity says nothing about `d 0`. -/
theorem map_eq_of_associated {N : Type*} [MonoidWithZero N] {d : N → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) {x y : N}
    (hy : y ≠ 0) (hxy : Associated x y) : d x = d y :=
  le_antisymm (map_le_of_dvd hd hy hxy.dvd)
    (map_le_of_dvd hd (hxy.ne_zero_iff.mpr hy) hxy.symm.dvd)

/-- For `d` additive on products of nonzero elements, the `d`-values of the distinct irreducible
factors of `a`, each counted once, sum to at most `d a`. The inequality is strict when a factor of
positive degree is repeated: for `a = X ^ 2` and `d = degreeOf`, the sum is `1`. For `a = 0` there
are no prime factor classes and the sum is `0`. -/
theorem sum_primeFactors_le [Nontrivial M] {d : M → ℕ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) (a : M) :
    ∑ c ∈ primeFactors (Associates.mk a), d (c.rep) ≤ d a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [Associates.mk_zero, primeFactors_zero]
  rw [← map_radicalRep_eq_sum hd]
  exact map_le_of_dvd hd ha (radicalRep_dvd_self a)

end

end UniqueFactorizationMonoid
