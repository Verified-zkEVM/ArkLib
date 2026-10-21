/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.ToMathlib.LinearAlgebra.LineInjectivity
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite families of commonly agreeing pairs and injective specialization

Fix an evaluation domain `domain : ι ↪ F` over a field `F` and two received words
`f g : ι → F`. A pair `(P, Q)` of polynomials of degree below `k` whose common agreement set
with `(f, g)` has at least `k` elements is determined by any `k` of its common agreements: `P` and
`Q` are the Lagrange interpolants of `f` and `g` on those coordinates. So all such pairs lie in
the explicit family `correlatedPairFamily domain f g k` of interpolant pairs over the `k`-element
subsets of `ι`, which has at most `(Fintype.card ι).choose k` members. No finiteness of `F` is
needed.

For a field homomorphism `φ : F →+* E` and a challenge `z : E`, the specialization of a pair is
`P.map φ + C z * Q.map φ`. Two distinct pairs have equal specializations for at most one
challenge. Hence a finite family of distinct pairs is specialized injectively at all but finitely
many challenges, and over an infinite field `E` some challenge does so while avoiding any finite
set and any finite set of roots of nonzero auxiliary polynomials. These specialization statements
are those of `ArkLib.ToMathlib.LinearAlgebra.LineInjectivity` in the `E`-module `E[X]`, with
`C z * R = z • R`.

## Main definitions

* `ReedSolomon.correlatedPairFamily`: the interpolant pairs over all `k`-element samples.
* `ReedSolomon.correlatedPairSpecialization`: `P.map φ + C z * Q.map φ`.

## Main statements

* `ReedSolomon.mem_correlatedPairFamily_iff`: the family is exactly the set of pairs of degree
  below `k` with at least `k` common agreements.
* `ReedSolomon.correlatedPairFamily_card_le`, `ReedSolomon.finite_commonAgreement_pairs`.
* `ReedSolomon.pair_eq_of_correlatedPairSpecialization_eq_at_two`,
  `ReedSolomon.subsingleton_correlatedPair_collisions`,
  `ReedSolomon.finite_correlatedPair_collision_challenges`: two challenges determine a pair.
* `ReedSolomon.exists_correlatedPairSpecialization_injOn_avoiding`,
  `ReedSolomon.exists_correlatedPairSpecialization_injOn_avoiding_roots`: an injective challenge
  over an infinite field.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

section Family

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- **The interpolant pairs on `k`-element samples.** For every `k`-element set `sample` of
coordinates, the pair of Lagrange interpolants of `f` and `g` on `sample`. -/
def correlatedPairFamily (domain : ι ↪ F) (f g : ι → F) (k : ℕ) : Finset (F[X] × F[X]) :=
  (Finset.univ.powersetCard k).image fun sample ↦
    (Lagrange.interpolate sample domain f, Lagrange.interpolate sample domain g)

/-- **Membership in the interpolant family.** A pair belongs to `correlatedPairFamily domain f g k`
exactly when both polynomials have degree below `k` and their common agreement set with `(f, g)`
has at least `k` elements.

From right to left, any `k` common agreements form a sample on which both polynomials are the
interpolants, by uniqueness of interpolation in degree below `k`. -/
theorem mem_correlatedPairFamily_iff (domain : ι ↪ F) (f g : ι → F) {k : ℕ}
    (pair : F[X] × F[X]) :
    pair ∈ correlatedPairFamily domain f g k ↔
      pair.1.degree < k ∧ pair.2.degree < k ∧
        k ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card := by
  classical
  have hinj (s : Finset ι) : Set.InjOn domain s := domain.injective.injOn
  constructor
  · intro hpair
    obtain ⟨sample, hsample, rfl⟩ := Finset.mem_image.mp hpair
    have hcard := (Finset.mem_powersetCard.mp hsample).2
    refine ⟨hcard ▸ Lagrange.degree_interpolate_lt f (hinj sample),
      hcard ▸ Lagrange.degree_interpolate_lt g (hinj sample), ?_⟩
    rw [← hcard]
    exact Finset.card_le_card fun i hi ↦ (mem_commonPolynomialAgreementSet ..).mpr
      ⟨Lagrange.eval_interpolate_at_node f (hinj sample) hi,
        Lagrange.eval_interpolate_at_node g (hinj sample) hi⟩
  · rintro ⟨hP, hQ, hcommon⟩
    obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcommon
    have hmem (i : ι) (hi : i ∈ sample) := (mem_commonPolynomialAgreementSet ..).mp (hsub hi)
    refine Finset.mem_image.mpr ⟨sample,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, Prod.ext ?_ ?_⟩
    · exact (Lagrange.eq_interpolate_of_eval_eq f (hinj sample) (hcard ▸ hP)
        fun i hi ↦ (hmem i hi).1).symm
    · exact (Lagrange.eq_interpolate_of_eval_eq g (hinj sample) (hcard ▸ hQ)
        fun i hi ↦ (hmem i hi).2).symm

/-- **A commonly agreeing pair is in the family.** A pair `(P, Q)` of degree below `k` with at
least `k` common agreements with `(f, g)` belongs to `correlatedPairFamily domain f g k`. This is
the reverse direction of `mem_correlatedPairFamily_iff`. -/
theorem mem_correlatedPairFamily_of_commonAgreement {k : ℕ} (domain : ι ↪ F) (f g : ι → F)
    (P Q : F[X]) (hP : P.degree < k) (hQ : Q.degree < k)
    (hcommon : k ≤ (commonPolynomialAgreementSet domain f g P Q).card) :
    (P, Q) ∈ correlatedPairFamily domain f g k :=
  (mem_correlatedPairFamily_iff domain f g (P, Q)).mpr ⟨hP, hQ, hcommon⟩

/-- **Size of the family.** There are at most `(Fintype.card ι).choose k` interpolant pairs, one
for each `k`-element sample. Distinct samples can give the same pair, so the bound need not be
attained. -/
theorem correlatedPairFamily_card_le (domain : ι ↪ F) (f g : ι → F) (k : ℕ) :
    (correlatedPairFamily domain f g k).card ≤ (Fintype.card ι).choose k := by
  classical
  exact Finset.card_image_le.trans_eq (by simp)

omit [DecidableEq ι] in
/-- **Finitely many commonly agreeing pairs.** The pairs of polynomials of degree below `k` with
at least `k` common agreements with `(f, g)` form a finite set, even when `F` is infinite. -/
theorem finite_commonAgreement_pairs {k : ℕ} (domain : ι ↪ F) (f g : ι → F) :
    {pair : F[X] × F[X] | pair.1.degree < k ∧ pair.2.degree < k ∧
      k ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card}.Finite := by
  classical
  exact (correlatedPairFamily domain f g k).finite_toSet.subset fun pair hpair ↦
    (mem_correlatedPairFamily_iff domain f g pair).mpr hpair

end Family

section Specialization

variable {F E : Type*} [Field F] [Field E]

/-- **Specialization of a pair.** The polynomial `P.map φ + C z * Q.map φ` over `E` obtained from
the pair `(P, Q)` over `F` at the challenge `z : E`. -/
def correlatedPairSpecialization (φ : F →+* E) (z : E) (pair : F[X] × F[X]) : E[X] :=
  pair.1.map φ + C z * pair.2.map φ

/-- The specialization is the `E[X]`-line `z ↦ P.map φ + z • Q.map φ`. -/
theorem correlatedPairSpecialization_eq_add_smul (φ : F →+* E) (z : E) (pair : F[X] × F[X]) :
    correlatedPairSpecialization φ z pair = pair.1.map φ + z • pair.2.map φ := by
  rw [correlatedPairSpecialization, smul_eq_C_mul]

/-- The mapped pairs `(P.map φ, Q.map φ)` of distinct pairs are distinct, since `Polynomial.map φ`
is injective for a field homomorphism `φ`. -/
theorem injective_map_pair (φ : F →+* E) :
    Function.Injective fun pair : F[X] × F[X] ↦ (pair.1.map φ, pair.2.map φ) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (map_injective φ φ.injective h.1) (map_injective φ φ.injective h.2)

/-- **Two challenges determine a pair.** If two pairs have equal specializations at two distinct
challenges `x ≠ y`, the pairs are equal. -/
theorem pair_eq_of_correlatedPairSpecialization_eq_at_two (φ : F →+* E)
    {p q : F[X] × F[X]} {x y : E} (hxy : x ≠ y)
    (hx : correlatedPairSpecialization φ x p = correlatedPairSpecialization φ x q)
    (hy : correlatedPairSpecialization φ y p = correlatedPairSpecialization φ y q) :
    p = q := by
  simp only [correlatedPairSpecialization_eq_add_smul] at hx hy
  obtain ⟨h1, h2⟩ := eq_and_eq_of_add_smul_eq_add_smul_of_ne hxy hx hy
  exact injective_map_pair φ (Prod.ext h1 h2)

/-- **Distinct pairs collide at most once.** Two distinct pairs have equal specializations for at
most one challenge. -/
theorem subsingleton_correlatedPair_collisions (φ : F →+* E) {p q : F[X] × F[X]}
    (hpq : p ≠ q) :
    {z : E | correlatedPairSpecialization φ z p =
      correlatedPairSpecialization φ z q}.Subsingleton :=
  fun _ hx _ hy ↦ by_contra fun hxy ↦
    hpq (pair_eq_of_correlatedPairSpecialization_eq_at_two φ hxy hx hy)

/-- **Finitely many non-injective challenges.** For a finite family `pairs`, the challenges at
which specialization is not injective on `pairs` form a finite set. -/
theorem finite_correlatedPair_collision_challenges (φ : F →+* E)
    (pairs : Finset (F[X] × F[X])) :
    {z : E | ¬ Set.InjOn (correlatedPairSpecialization φ z) (↑pairs)}.Finite := by
  simpa only [funext (correlatedPairSpecialization_eq_add_smul φ _)] using
    pairs.finite_toSet.finite_setOf_not_injOn_add_smul (K := E)
      (fun pair ↦ pair.1.map φ) (fun pair ↦ pair.2.map φ) (injective_map_pair φ).injOn

/-- **An injective challenge avoiding a finite set.** Over an infinite field `E`, some challenge
outside `avoid` specializes the finite family `pairs` injectively.

`Infinite E` is needed: over a finite field, `avoid` can be all of `E`. -/
theorem exists_correlatedPairSpecialization_injOn_avoiding [Infinite E] (φ : F →+* E)
    (pairs : Finset (F[X] × F[X])) (avoid : Finset E) :
    ∃ z : E, z ∉ avoid ∧ Set.InjOn (correlatedPairSpecialization φ z) (↑pairs) := by
  obtain ⟨z, hz, hinj⟩ := pairs.finite_toSet.exists_notMem_injOn_add_smul
    (fun pair ↦ pair.1.map φ) (fun pair ↦ pair.2.map φ) (injective_map_pair φ).injOn
    avoid.finite_toSet
  exact ⟨z, hz, by simpa only [funext (correlatedPairSpecialization_eq_add_smul φ z)] using hinj⟩

/-- **An injective challenge that is not a root of given polynomials.** Over an infinite field
`E`, some challenge outside `avoid` specializes `pairs` injectively and is a root of none of the
finitely many polynomials in `auxiliary`.

Each `R ∈ auxiliary` must be nonzero: the zero polynomial vanishes at every challenge. -/
theorem exists_correlatedPairSpecialization_injOn_avoiding_roots [Infinite E]
    (φ : F →+* E) (pairs : Finset (F[X] × F[X])) (avoid : Finset E) (auxiliary : Finset E[X])
    (hne : ∀ R ∈ auxiliary, R ≠ 0) :
    ∃ z : E, z ∉ avoid ∧ Set.InjOn (correlatedPairSpecialization φ z) (↑pairs) ∧
      ∀ R ∈ auxiliary, R.eval z ≠ 0 := by
  classical
  obtain ⟨z, hz, hinj⟩ := exists_correlatedPairSpecialization_injOn_avoiding φ pairs
    (avoid ∪ auxiliary.biUnion fun R ↦ R.roots.toFinset)
  simp only [Finset.mem_union, not_or, Finset.mem_biUnion, not_exists, not_and,
    Multiset.mem_toFinset] at hz
  exact ⟨z, hz.1, hinj, fun R hR heval ↦ hz.2 R hR ((mem_roots (hne R hR)).mpr heval)⟩

end Specialization

end

end ReedSolomon
