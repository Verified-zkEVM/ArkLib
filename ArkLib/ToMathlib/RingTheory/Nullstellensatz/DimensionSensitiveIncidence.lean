/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
public import ArkLib.ToMathlib.Set.Finite

/-!
# Dimension-sensitive agreement incidence

Let `k` be a field, `σ` a finite type, `P` a prime ideal of `MvPolynomial σ k` and `s` a
polynomial. Write `H(I)` for `affineHilbertPolynomial I`, `d = natDegree H(P)` for the dimension
of `P`, and `U(Q) = {x ∈ V(Q) | s(x) ≠ 0}` for the principal open subset of the zero locus of an
ideal `Q`, with points in a field extension `K` of `k`. Fix cuts `cuts : ι → MvPolynomial σ k`
of total degree at most `b` and write `n = Fintype.card ι`.

The incidence bound `card_le_incidenceProduct_of_agreement_off_excluded` charges a component of
dimension `t + 1` the factor `((n - T t + 1) * b) / (A - T t + 1)`, where fewer than `T t` cuts
lie in such a component. This file specializes it to two budgets on the number of cuts in a
component.

* A dimension-sensitive budget: every positive-dimensional prime `Q ⊇ P` with `s ∉ Q` satisfies
  `natDegree H(Q) + #{i | cuts i ∈ Q} ≤ m`. This holds in the coefficient space of polynomials
  of degree less than `m` for the evaluation equations at distinct points, where a component of
  dimension `e` lies in at most `m - e` of them. The threshold is `T t = m - t`, and the product
  is `dimensionSensitiveIncidenceProduct n A m b d`.
* A hybrid budget: components of dimension one containing at least `L` cuts are excluded, and
  components of dimension `e ≥ 2` satisfy `e + #{i | cuts i ∈ Q} ≤ m + 1`. The product is
  `hybridDimensionSensitiveIncidenceProduct n A L m b d`.

The hybrid bound extends to points on the iterated retained cut family of a family of primes by
a list of fixed cuts of degree at most `B`, where the fixed cuts contribute `B ^ d`.

## Main statements

All declarations are in the namespace `MvPolynomial`.

* `card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded` and
  `card_le_dimensionSensitiveIncidenceProduct_of_agreement`: the dimension-sensitive incidence
  bound, outside an excluded set and without one.
* `card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`: the hybrid
  incidence bound.
* `card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily` and
  `card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily`: the
  hybrid bound after a list of fixed cuts, in any dimension and in dimension at most two.
* `finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation`: in
  the coefficient space of polynomials of degree less than `m`, the polynomials agreeing with
  received values at `A ≥ m` of `n` distinct points form a finite set on each principal open
  subset of a prime, bounded by the dimension-sensitive product.

Each bound on a finite set also has a form for the set of all such points.
-/

@[expose] public section

open scoped Finset

namespace MvPolynomial

variable {k K σ ι : Type*} [Field k] [Field K] [Algebra k K]

/-- **Dimension-sensitive agreement incidence outside an excluded set.** Let `P` be a prime of
dimension `d`, `cuts : ι → MvPolynomial σ k` of total degree at most `b`, and `m ≤ A`. Suppose
that every positive-dimensional prime `Q ⊇ P` with `s ∉ Q` either satisfies
`natDegree H(Q) + #{i | cuts i ∈ Q} ≤ m` or has `U(Q)` inside `excluded`. Then every finite set
`S` of points of `U(P)` outside `excluded`, each agreeing with at least `A` cuts, satisfies

  `#S ≤ affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b d`.

This is `card_le_incidenceProduct_of_agreement_off_excluded` with threshold `m - t` at
dimension `t + 1`. If `S` is nonempty, the hypothesis applied to `P` gives `d ≤ m`, and a point
of `S` gives `A ≤ Fintype.card ι`, so the two products agree.

The hypothesis `m ≤ A` is needed: for `P = ⊥` in one variable, no cuts, `m = 1` and `A = 0`, the
budget holds, but the bound is `0` while `S` can be any finite set. -/
theorem card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded [Finite σ]
    [Fintype ι] {P : Ideal (MvPolynomial σ k)} [hP : P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A) (excluded : Set (σ → K))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m ∨
        {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K)) (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b
      (affineHilbertPolynomial P).natDegree := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simpa using mul_nonneg (affineDegree_nonneg P)
      (dimensionSensitiveIncidenceProduct_nonneg _ A m b _)
  have hsP : s ∉ P := fun h ↦ (hS x₀ hx₀).2.1 ((hS x₀ hx₀).1 s h)
  have hAn : A ≤ Fintype.card ι := by
    have := (hA x₀ hx₀).trans (Set.ncard_le_ncard (Set.subset_univ _))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hdm : (affineHilbertPolynomial P).natDegree ≤ m := by
    rcases Nat.eq_zero_or_pos (affineHilbertPolynomial P).natDegree with hd | hd
    · omega
    rcases hcomponent P le_rfl hP hsP hd with h | h
    · omega
    · exact absurd (h ⟨(hS x₀ hx₀).1, (hS x₀ hx₀).2.1⟩) (hS x₀ hx₀).2.2
  rw [dimensionSensitiveIncidenceProduct_eq_incidenceProduct (by omega) hmA hAn]
  exact card_le_incidenceProduct_of_agreement_off_excluded s cuts hdeg (fun t ↦ m - t)
    (fun t _ ↦ by omega) excluded
    (fun Q hPQ hQ hsQ hdQ hTQ ↦ (hcomponent Q hPQ hQ hsQ hdQ).resolve_left (by omega)) S hS hA

/-- **Dimension-sensitive agreement incidence.** Let `P` be a prime of dimension `d`,
`cuts : ι → MvPolynomial σ k` of total degree at most `b`, and `m ≤ A`. Suppose that every
positive-dimensional prime `Q ⊇ P` with `s ∉ Q` satisfies `natDegree H(Q) + #{i | cuts i ∈ Q} ≤ m`.
Then every finite set `S ⊆ U(P)` of points agreeing with at least `A` cuts satisfies

  `#S ≤ affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b d`. -/
theorem card_le_dimensionSensitiveIncidenceProduct_of_agreement [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m)
    (S : Finset (σ → K)) (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b
      (affineHilbertPolynomial P).natDegree :=
  card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts hdeg hmA ∅
    (fun Q hPQ hQ hsQ hdQ ↦ Or.inl (hcomponent Q hPQ hQ hsQ hdQ)) S
    (fun x hx ↦ ⟨(hS x hx).1, (hS x hx).2, Set.notMem_empty x⟩) hA

/-- **Dimension-sensitive agreement incidence outside an excluded set, for the set of all
points.** Under the hypotheses of
`card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded`, the set of all points of
`U(P)` outside `excluded` agreeing with at least `A` cuts is finite, with at most
`affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b d` elements. -/
theorem finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded
    [Finite σ] [Fintype ι] {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A) (excluded : Set (σ → K))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m ∨
        {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded) :
    {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b
        (affineHilbertPolynomial P).natDegree := by
  have hbound (S : Finset (σ → K)) (hS : (S : Set (σ → K)) ⊆
      {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}) :=
    card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts hdeg hmA
      excluded hcomponent S (fun _x hx ↦ ⟨(hS hx).1, (hS hx).2.1, (hS hx).2.2.1⟩)
      fun _x hx ↦ (hS hx).2.2.2
  have hfin := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ fun _x hx ↦ hfin.mem_toFinset.mp hx

/-- **Dimension-sensitive agreement incidence, for the set of all points.** Under the hypotheses
of `card_le_dimensionSensitiveIncidenceProduct_of_agreement`, the set of all points of `U(P)`
agreeing with at least `A` cuts is finite, with at most
`affineDegree P * dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b d` elements. -/
theorem finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement [Finite σ]
    [Fintype ι] {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m) :
    {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct (Fintype.card ι) A m b
        (affineHilbertPolynomial P).natDegree := by
  have hbound (S : Finset (σ → K)) (hS : (S : Set (σ → K)) ⊆
      {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}) :=
    card_le_dimensionSensitiveIncidenceProduct_of_agreement s cuts hdeg hmA hcomponent S
      (fun _x hx ↦ ⟨(hS hx).1, (hS hx).2.1⟩) fun _x hx ↦ (hS hx).2.2
  have hfin := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ fun _x hx ↦ hfin.mem_toFinset.mp hx

/-- The hybrid budget gives the hypothesis of `card_le_incidenceProduct_of_agreement_off_excluded`
with threshold `L` at dimension one and `m + 1 - t` at dimension `t + 1` for `t ≥ 1`. -/
private theorem hybrid_terminal [Finite σ] {Q : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    {cuts : ι → MvPolynomial σ k} {L m : ℕ} {excluded : Set (σ → K)}
    (hdimension : 1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : L ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (hd : 0 < (affineHilbertPolynomial Q).natDegree)
    (hT : (fun t ↦ if t = 0 then L else m + 1 - t) ((affineHilbertPolynomial Q).natDegree - 1) ≤
      {i | cuts i ∈ Q}.ncard) :
    {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded := by
  by_cases h1 : (affineHilbertPolynomial Q).natDegree = 1
  · rw [h1] at hT
    exact hterminal (by simpa using hT)
  · have := hdimension (by omega)
    have h0 : (affineHilbertPolynomial Q).natDegree - 1 ≠ 0 := by omega
    simp only [h0, ↓reduceIte] at hT
    omega

/-- **Hybrid agreement incidence outside an excluded set.** Let `P` be a prime of dimension `d`,
`cuts : ι → MvPolynomial σ k` of total degree at most `b`, `L ≤ A` and `m ≤ A`. Suppose that for
every prime `Q ⊇ P` with `s ∉ Q`, if `Q` has dimension `e ≥ 2` then
`e + #{i | cuts i ∈ Q} ≤ m + 1`, and if `Q` has positive dimension and contains at least `L`
cuts then `U(Q)` lies in `excluded`. Then every finite set `S` of points of `U(P)` outside
`excluded`, each agreeing with at least `A` cuts, satisfies

  `#S ≤ affineDegree P * hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b d`.

This is `card_le_incidenceProduct_of_agreement_off_excluded` with threshold `L` at dimension one
and `m + 1 - t` at dimension `t + 1` for `t ≥ 1`. -/
theorem card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded [Finite σ]
    [Fintype ι] {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A L m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hmA : m ≤ A) (excluded : Set (σ → K))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree → L ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K)) (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P * hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b
      (affineHilbertPolynomial P).natDegree := by
  rw [hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct]
  exact card_le_incidenceProduct_of_agreement_off_excluded s cuts hdeg _
    (fun t _ ↦ by split_ifs <;> omega) excluded
    (fun Q hPQ hQ hsQ hdQ hTQ ↦ hybrid_terminal (hdimension Q hPQ hQ hsQ)
      (hterminal Q hPQ hQ hsQ hdQ) hdQ hTQ) S hS hA

/-- **Hybrid agreement incidence outside an excluded set, for the set of all points.** Under the
hypotheses of `card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`, the
set of all points of `U(P)` outside `excluded` agreeing with at least `A` cuts is finite, with at
most `affineDegree P * hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b d`
elements. -/
theorem finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded
    [Finite σ] [Fintype ι] {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A L m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hmA : m ≤ A) (excluded : Set (σ → K))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree → L ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded) :
    {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b
        (affineHilbertPolynomial P).natDegree := by
  have hbound (S : Finset (σ → K)) (hS : (S : Set (σ → K)) ⊆
      {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}) :=
    card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts hdeg hLA
      hmA excluded hdimension hterminal S
      (fun _x hx ↦ ⟨(hS hx).1, (hS hx).2.1, (hS hx).2.2.1⟩) fun _x hx ↦ (hS hx).2.2.2
  have hfin := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ fun _x hx ↦ hfin.mem_toFinset.mp hx

/-- **Hybrid agreement incidence after a list of fixed cuts.** Let `Ps` be a finite family of
primes of dimension at most `d` whose affine degrees sum to at most `V`, let `highCuts` be a list
of polynomials of total degree at most `B > 0`, let `cuts : ι → MvPolynomial σ k` have total
degree at most `b > 0`, and let `L ≤ A` and `m ≤ A`. Suppose that the hybrid budget of
`card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded` holds for every
prime `Q` above a member of `Ps` with `s ∉ Q` containing every element of `highCuts`. Then every
finite set `S` of points of the zero loci of members of `Ps` with `s ≠ 0`, all of `highCuts`
vanishing, outside `excluded`, and agreeing with at least `A` cuts satisfies

  `#S ≤ V * B ^ d *
    hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b (min d (m + 1))`.

This is `card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily`: the
budget bounds the dimension of each prime `Q` above a member of `Ps` by `m + 1`. -/
theorem card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily [Finite σ]
    [Fintype ι] (Ps : Finset (Ideal (MvPolynomial σ k))) (hprime : ∀ P ∈ Ps, P.IsPrime)
    (s : MvPolynomial σ k) {d : ℕ} (hdim : ∀ P ∈ Ps, (affineHilbertPolynomial P).natDegree ≤ d)
    {V : ℚ} (hV : ∑ P ∈ Ps, affineDegree P ≤ V) (highCuts : List (MvPolynomial σ k)) {B : ℕ}
    (hB : 0 < B) (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B) (cuts : ι → MvPolynomial σ k)
    {b A L m : ℕ} (hb : 0 < b) (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (hLA : L ≤ A)
    (hmA : m ≤ A) (excluded : Set (σ → K))
    (hdimension : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ {i | cuts i ∈ Q}.ncard → {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K))
    (hS : ∀ x ∈ S, (∃ P ∈ Ps, x ∈ zeroLocus K P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ V * (B : ℚ) ^ d *
      hybridDimensionSensitiveIncidenceProduct (Fintype.card ι) A L m b (min d (m + 1)) := by
  rw [hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct]
  refine card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily Ps hprime
    s hdim hV highCuts hB hhigh cuts hb hdeg _ (fun t _ ↦ by split_ifs <;> omega) excluded
    (fun P hP Q hPQ hQ hsQ hhighQ ↦ ?_)
    (fun P hP Q hPQ hQ hsQ hhighQ hdQ hTQ ↦ hybrid_terminal
      (hdimension P hP Q hPQ hQ hsQ hhighQ) (hterminal P hP Q hPQ hQ hsQ hhighQ hdQ) hdQ hTQ)
    S hS hA
  have hdQ := (natDegree_affineHilbertPolynomial_le_of_le hPQ).trans (hdim P hP)
  by_cases h1 : (affineHilbertPolynomial Q).natDegree ≤ 1
  · omega
  · have := hdimension P hP Q hPQ hQ hsQ hhighQ (by omega)
    omega

/-- **Hybrid agreement incidence after a list of fixed cuts, in dimension at most two.** Under
the hypotheses of `card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily`
with `d = 2`,

  `#S ≤ V * B ^ 2 * ((Fintype.card ι - L + 1) * b / (A - L + 1)) *
    ((Fintype.card ι - m + 1) * b / (A - m + 1))`. -/
theorem card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily
    [Finite σ] [Fintype ι] (Ps : Finset (Ideal (MvPolynomial σ k)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) (s : MvPolynomial σ k)
    (hdim : ∀ P ∈ Ps, (affineHilbertPolynomial P).natDegree ≤ 2) {V : ℚ}
    (hV : ∑ P ∈ Ps, affineDegree P ≤ V) (highCuts : List (MvPolynomial σ k)) {B : ℕ}
    (hB : 0 < B) (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B) (cuts : ι → MvPolynomial σ k)
    {b A L m : ℕ} (hb : 0 < b) (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (hLA : L ≤ A)
    (hmA : m ≤ A) (excluded : Set (σ → K))
    (hdimension : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ {i | cuts i ∈ Q}.ncard → {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K))
    (hS : ∀ x ∈ S, (∃ P ∈ Ps, x ∈ zeroLocus K P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ V * (B : ℚ) ^ 2 *
      ((((Fintype.card ι - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((Fintype.card ι - m + 1) * b : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hV0 : 0 ≤ V := (Finset.sum_nonneg fun P _ ↦ affineDegree_nonneg P).trans hV
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hAn : A ≤ Fintype.card ι := by
    have := (hA x₀ hx₀).trans (Set.ncard_le_ncard (Set.subset_univ _))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun P _ ↦ affineDegree_nonneg P).trans hV
  refine (card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily Ps hprime
    s hdim hV highCuts hB hhigh cuts hb hdeg hLA hmA excluded hdimension hterminal S hS
    hA).trans ?_
  rw [mul_assoc (V * (B : ℚ) ^ 2)]
  exact mul_le_mul_of_nonneg_left
    (hybridDimensionSensitiveIncidenceProduct_le_two (min_le_left _ _) hAn hb)
    (by positivity)

/-- **Agreement incidence in coefficient space.** Let `α : Fin n ↪ k` be distinct points,
`y : Fin n → k` received values, `P` a prime of `MvPolynomial (Fin m) k` of dimension `d`, and
`m ≤ A`. The coefficient vectors `x` of polynomials of degree less than `m` in `U(P)` whose
evaluation `∑ l, α i ^ l * x l` equals `y i` for at least `A` indices `i` form a finite set with
at most `affineDegree P * dimensionSensitiveIncidenceProduct n A m 1 d` elements.

This is `finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement`, whose budget holds
by `natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation`. -/
theorem finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation
    {n m A : ℕ} (α : Fin n ↪ k) (y : Fin n → k) {P : Ideal (MvPolynomial (Fin m) k)}
    [P.IsPrime] (s : MvPolynomial (Fin m) k) (hmA : m ≤ A) :
    {x : Fin m → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (fixedCoefficientEvaluation m (α i) (y i)) = 0}.ncard}.Finite ∧
      ({x : Fin m → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (fixedCoefficientEvaluation m (α i) (y i)) = 0}.ncard}.ncard : ℚ) ≤
        affineDegree P * dimensionSensitiveIncidenceProduct n A m 1
          (affineHilbertPolynomial P).natDegree := by
  simpa only [Fintype.card_fin] using
    finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement (K := K) s
      (fun i ↦ fixedCoefficientEvaluation m (α i) (y i))
      (fun i ↦ totalDegree_fixedCoefficientEvaluation_le m (α i) (y i)) hmA
      fun _Q _ _ _ hd ↦ natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation
        α y hd

end MvPolynomial
