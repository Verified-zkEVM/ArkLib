/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting
public import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCutFamily
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CutFamily
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen

/-!
# Agreement incidence on principal open subsets of affine primes

Let `k` be a field, `σ` a finite type, `P` a prime ideal of `MvPolynomial σ k` and `s` a
polynomial. Write `H(I)` for `affineHilbertPolynomial I`, `d = natDegree H(P)` for the dimension
of `P`, and `U(Q) = {x ∈ V(Q) | s(x) ≠ 0}` for the principal open subset of the zero locus of an
ideal `Q` cut out by `s`, with points in a field extension `K` of `k`.

Fix a finite family of equations `cuts : ι → MvPolynomial σ k` of total degree at most `b`, and
write `n = Fintype.card ι`. Say a point `x` *agrees* with the cut `i` if `cuts i` vanishes at `x`.
The main theorem bounds the number of points of `U(P)` that agree with at least `A` cuts by

  `affineDegree P * (n * b / (A - L + 1)) ^ d`,

provided that every positive-dimensional prime `Q ⊇ P` with `s ∉ Q` containing at least `L` of
the cuts has `U(Q)` inside a set `excluded` that the counted points avoid. The set `excluded` is
arbitrary and adds no degree factor.

More generally, a threshold may depend on the dimension: if every such `Q` of dimension `e + 1`
containing at least `T e` cuts has `U(Q)` inside `excluded`, the bound is
`affineDegree P * incidenceProduct n A b T d`, the product over `t < d` of the factors
`((n - T t + 1) * b) / (A - T t + 1)`. The constant threshold `L` gives the bound above.

The proof is an induction on `d`. In dimension zero the whole zero locus has at most
`affineDegree P` points. In positive dimension `e + 1`, the hypothesis applied to `P` itself
shows that fewer than `T e` cuts lie in `P`; say `u` of them do. Each counted point agrees with at
least `A - u` of the remaining `n - u` cuts, so double counting gives
`#S * (A - u) ≤ ∑_{cuts i ∉ P} #{x ∈ S | cuts i (x) = 0}`. For a cut `f ∉ P`, the points on
`f = 0` lie on the minimal primes of `P ⊔ span {f}` not containing `s`; these have dimension `e`
by purity, the induction hypothesis bounds the points on each, and the Bézout bound sums their
degrees to at most `b * affineDegree P`. Summing over the `n - u` cuts, dividing by `A - u`, and
bounding `(n - u) / (A - u)` by `(n - T e + 1) / (A - T e + 1)` closes the induction.

If `k` is algebraically closed and any `m` cuts determine a point of `U(P)`, then a
positive-dimensional `U(Q)` can contain at most one point agreeing with `m` cuts, so it is finite,
which contradicts positive dimension; hence fewer than `m` cuts lie in `Q`, and the hypothesis
above holds with `excluded = ∅` and `L = m`.

## Main statements

* `MvPolynomial.ncard_inter_cut_le_sum_retainedMinimalPrimes`: the points of a finite subset of
  `U(I)` on a hypersurface are covered by the retained components of the cut.
* `MvPolynomial.ncard_inter_cut_le_of_retained_le`: one inductive step, bounding the points on a
  cut `f ∉ P` from bounds on each retained component.
* `MvPolynomial.card_le_incidenceProduct_of_agreement_off_excluded` and
  `MvPolynomial.finite_and_ncard_le_incidenceProduct_of_agreement_off_excluded`: the incidence
  bound with a dimension-dependent threshold.
* `MvPolynomial.card_le_of_agreement_off_excluded` and
  `MvPolynomial.finite_and_ncard_le_of_agreement_off_excluded`: the incidence bound outside an
  excluded set, for a finite set of points and for the set of all such points.
* `MvPolynomial.ncard_setOf_mem_lt_of_subsingleton`: over an algebraically closed field, fewer
  than `m` cuts vanish on a positive-dimensional prime whose principal open subset is determined
  by any `m` cuts.
* `MvPolynomial.card_le_of_agreement_of_subsingleton` and
  `MvPolynomial.finite_and_ncard_le_of_agreement_of_subsingleton`: the incidence bound under
  uniqueness.
* `MvPolynomial.card_le_sum_of_agreement_off_excluded`: the incidence bound for points covered by
  a finite family of primes, as a sum over the family.
* `MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface`: the incidence bound for points
  on a hypersurface `g = 0` cut by further equations, with the factor `deg g` in place of the
  affine degree and exponent `Nat.card σ - 1`.
* `MvPolynomial.card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily`:
  the incidence bound with a dimension-dependent threshold for points on the iterated retained
  cut family of a family of primes by a list of fixed cuts.
-/

@[expose] public section

open scoped Finset

namespace MvPolynomial

variable {k K σ ι : Type*} [Field k] [Field K] [Algebra k K]

/-- The number of points of a finite set satisfying `p`, written with `Set.ncard`, is the
cardinality of the corresponding filter. -/
private theorem ncard_coe_inter_setOf {α : Type*} (S : Finset α) (p : α → Prop)
    [DecidablePred p] : ((S : Set α) ∩ {x | p x}).ncard = #(S.filter p) := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

/-- The points of a finite set `S ⊆ U(I)` lying on the hypersurface `f = 0` are covered by the
zero loci of the minimal primes of `I ⊔ span {f}` that do not contain `s`, so their number is at
most the sum of the numbers of points of `S` on each of these components.

This is the union bound for `MvPolynomial.mem_zeroLocus_and_cut_iff_retained`. No hypothesis
relates `f`, `s` and `I`, and `K` need not be algebraically closed. The hypothesis that `s` does
not vanish on `S` is needed: for `I = ⊥` in one variable, `s = f = X 0` and `S = {0}`, the left
side is `1`, while `span {X 0}` contains `s`, so no component is retained. -/
theorem ncard_inter_cut_le_sum_retainedMinimalPrimes [Finite σ] (I : Ideal (MvPolynomial σ k))
    (s f : MvPolynomial σ k) (S : Finset (σ → K))
    (hS : ∀ x ∈ S, x ∈ zeroLocus K I ∧ aeval x s ≠ 0) :
    ((S : Set (σ → K)) ∩ {x | aeval x f = 0}).ncard ≤
      ∑ Q ∈ (I ⊔ Ideal.span {f}).retainedMinimalPrimes s,
        ((S : Set (σ → K)) ∩ zeroLocus K Q).ncard := by
  classical
  rw [ncard_coe_inter_setOf]
  simp_rw [show ∀ Q : Ideal (MvPolynomial σ k), (S : Set (σ → K)) ∩ zeroLocus K Q =
      (S : Set (σ → K)) ∩ {x | x ∈ zeroLocus K Q} from fun _ ↦ rfl, ncard_coe_inter_setOf]
  refine (Finset.card_le_card fun x hx ↦ ?_).trans Finset.card_biUnion_le
  rw [Finset.mem_filter] at hx
  obtain ⟨Q, hQ, hxQ, -⟩ := (mem_zeroLocus_and_cut_iff_retained I s f x).mp
    ⟨(hS x hx.1).1, hx.2, (hS x hx.1).2⟩
  exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_filter.mpr ⟨hx.1, hxQ⟩⟩

/-- One step of the incidence induction. Let `P` be prime, `f ∉ P` with `totalDegree f ≤ b`, and
`S ⊆ U(P)` finite. If every minimal prime `Q` of `P ⊔ span {f}` not containing `s` carries at most
`affineDegree Q * c` points of `S`, then at most `b * affineDegree P * c` points of `S` lie on
`f = 0`.

The points are covered by the retained components
(`ncard_inter_cut_le_sum_retainedMinimalPrimes`), and their affine degrees sum to at most
`b * affineDegree P` (`principalCut_sum_affineDegree_retainedMinimalPrimes_le`). The factor `c`
must be nonnegative for the last step. The hypothesis `f ∉ P` is needed: for `P = ⊥`, `f = 0`,
`b = 0` and `c = 1`, the only retained component of `P ⊔ span {0} = ⊥` is `⊥`, which has affine
degree `1`, so a one-point `S` satisfies the hypothesis while the conclusion bounds it by `0`. -/
theorem ncard_inter_cut_le_of_retained_le [Finite σ] {P : Ideal (MvPolynomial σ k)} [P.IsPrime]
    (s : MvPolynomial σ k) {f : MvPolynomial σ k} (hf : f ∉ P) {b : ℕ}
    (hfdeg : f.totalDegree ≤ b) (S : Finset (σ → K))
    (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0) {c : ℚ} (hc : 0 ≤ c)
    (hchild : ∀ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s,
      (((S : Set (σ → K)) ∩ zeroLocus K Q).ncard : ℚ) ≤ affineDegree Q * c) :
    (((S : Set (σ → K)) ∩ {x | aeval x f = 0}).ncard : ℚ) ≤ b * affineDegree P * c := by
  calc (((S : Set (σ → K)) ∩ {x | aeval x f = 0}).ncard : ℚ)
      ≤ ∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s,
          (((S : Set (σ → K)) ∩ zeroLocus K Q).ncard : ℚ) := by
        exact_mod_cast ncard_inter_cut_le_sum_retainedMinimalPrimes P s f S hS
    _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s, affineDegree Q * c :=
        Finset.sum_le_sum hchild
    _ = (∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s, affineDegree Q) * c :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ b * affineDegree P * c :=
        mul_le_mul_of_nonneg_right
          (principalCut_sum_affineDegree_retainedMinimalPrimes_le s hf hfdeg) hc

/-- A number of cuts vanishing at a point is at most the number of cuts. -/
private theorem le_fintypeCard_of_le_ncard [Fintype ι] {p : ι → Prop} {A : ℕ}
    (hA : A ≤ {i | p i}.ncard) : A ≤ Fintype.card ι := by
  have := hA.trans (Set.ncard_le_ncard (Set.subset_univ {i | p i}))
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this

/-- **Agreement incidence with a dimension-dependent threshold.** Let `P` be a prime of
`MvPolynomial σ k` of dimension `d = natDegree H(P)`, let `cuts : ι → MvPolynomial σ k` be a
finite family of total degree at most `b`, and let `T : ℕ → ℕ` with `T t ≤ A` for `t < d`.
Suppose that for every prime `Q ⊇ P` with `s ∉ Q` and positive dimension `e + 1`, if at least
`T e` cuts lie in `Q`, then `U(Q)` lies in `excluded`. Then every finite set `S` of points of
`U(P)` outside `excluded`, each agreeing with at least `A` cuts, satisfies

  `#S ≤ affineDegree P * incidenceProduct (Fintype.card ι) A b T d`,

where `incidenceProduct` multiplies the factors `((Fintype.card ι - T t + 1) * b) / (A - T t + 1)`
over `t < d`.

In the step from dimension `e + 1`, fewer than `T e` cuts lie in `P`. If `u` of them do, each
point agrees with at least `A - u` of the other `Fintype.card ι - u` cuts, and the ratio
`(Fintype.card ι - u) / (A - u)` is at most `(Fintype.card ι - T e + 1) / (A - T e + 1)`
(`natCast_sub_div_natCast_sub_le`). No hypothesis `A ≤ Fintype.card ι` is needed, since a point
agreeing with `A` cuts forces it.

The hypothesis on `T` is needed: for `P = ⊥` in one variable, no cuts, `A = 0` and `T 0 = 1`,
the hypothesis on `excluded = ∅` is vacuous, but the bound is `0` while `S` can be any finite
set. -/
theorem card_le_incidenceProduct_of_agreement_off_excluded [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [hP : P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (T : ℕ → ℕ) (hTA : ∀ t < (affineHilbertPolynomial P).natDegree, T t ≤ A)
    (excluded : Set (σ → K))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      T ((affineHilbertPolynomial Q).natDegree - 1) ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K)) (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P *
      incidenceProduct (Fintype.card ι) A b T (affineHilbertPolynomial P).natDegree := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, (affineHilbertPolynomial P).natDegree = d := ⟨_, rfl⟩
  rw [hd]
  induction d using Nat.strong_induction_on generalizing P S with
  | _ d ih =>
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simpa using mul_nonneg (affineDegree_nonneg P) (incidenceProduct_nonneg _ A b T d)
  rcases d with _ | e
  · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := K) P hd
    have hcard : (#S : ℚ) ≤ (zeroLocus K P).ncard := by
      have := Set.ncard_le_ncard (fun x (hx : x ∈ (S : Set (σ → K))) ↦ (hS x hx).1) hfin.1
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    simpa using hcard.trans hfin.2
  have hsP : s ∉ P := fun h ↦ (hS x₀ hx₀).2.1 ((hS x₀ hx₀).1 s h)
  have hAn : A ≤ Fintype.card ι := le_fintypeCard_of_le_ncard (hA x₀ hx₀)
  let r : (σ → K) → ι → Prop := fun x i ↦ aeval x (cuts i) = 0
  let u : Finset ι := Finset.univ.filter fun i ↦ cuts i ∈ P
  have hu : #u < T e := by
    have hu_eq : #u = {i | cuts i ∈ P}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [u]
    rw [hu_eq]
    by_contra h
    exact (hS x₀ hx₀).2.2 (hterminal P le_rfl hP hsP (by omega)
      (by rw [hd, Nat.add_sub_cancel]; exact not_lt.mp h) ⟨(hS x₀ hx₀).1, (hS x₀ hx₀).2.1⟩)
  have hTe : T e ≤ A := hTA e (by omega)
  set c : ℚ := ((A - #u : ℕ) : ℚ) with hc_def
  set R : ℚ := incidenceProduct (Fintype.card ι) A b T e with hR_def
  have hcpos : 0 < c := by rw [hc_def]; exact_mod_cast (by omega : 0 < A - #u)
  have hR : 0 ≤ R := incidenceProduct_nonneg _ A b T e
  have hlowerNat : #S * (A - #u) ≤ ∑ i ∈ uᶜ, #(S.bipartiteBelow r i) := by
    refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow r u fun x hx ↦ ?_
    rw [← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
    simpa [r] using hA x hx
  have hlower : (#S : ℚ) * c ≤ ∑ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) := by
    have := (Nat.cast_le (α := ℚ)).mpr hlowerNat
    rwa [Nat.cast_mul, Nat.cast_sum] at this
  have hcut : ∀ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) ≤ b * affineDegree P * R := by
    intro i hi
    have hiP : cuts i ∉ P := by simpa [u] using hi
    rw [← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
    refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) S
      (fun x hx ↦ ⟨(hS x hx).1, (hS x hx).2.1⟩) hR fun Q hQ ↦ ?_
    have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
    have : Q.IsPrime := hQmin.isPrime
    have hPQ : P ≤ Q := le_sup_left.trans hQmin.le
    have hQdeg : (affineHilbertPolynomial Q).natDegree = e := by
      have := principalCut_natDegree_affineHilbertPolynomial_add_one hiP hQmin
      omega
    have := ih e (by omega) (P := Q) (S := S.filter (· ∈ zeroLocus K Q))
      (fun t ht ↦ hTA t (by omega))
      (fun J hQJ hJ hsJ hdJ hTJ ↦ hterminal J (hPQ.trans hQJ) hJ hsJ hdJ hTJ)
      (fun x hx ↦ by
        rw [Finset.mem_filter] at hx
        exact ⟨hx.2, (hS x hx.1).2.1, (hS x hx.1).2.2⟩)
      (fun x hx ↦ hA x (Finset.mem_filter.mp hx).1) hQdeg
    rwa [show (S : Set (σ → K)) ∩ zeroLocus K Q = (S : Set (σ → K)) ∩ {x | x ∈ zeroLocus K Q}
      from rfl, ncard_coe_inter_setOf]
  have hupper : ∑ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) ≤
      ((Fintype.card ι - #u : ℕ) : ℚ) * (b * affineDegree P * R) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
    rw [nsmul_eq_mul, Finset.card_compl]
  have hratio : ((Fintype.card ι - #u : ℕ) : ℚ) / c ≤
      ((Fintype.card ι - T e + 1 : ℕ) : ℚ) / ((A - T e + 1 : ℕ) : ℚ) := by
    have := natCast_sub_div_natCast_sub_le (K := ℚ) (n := Fintype.card ι) (A := A) (m := #u)
      (m' := T e - 1) (by omega) (by omega) hAn
    rwa [show Fintype.card ι - (T e - 1) = Fintype.card ι - T e + 1 by omega,
      show A - (T e - 1) = A - T e + 1 by omega] at this
  have hS' : (#S : ℚ) ≤ ((Fintype.card ι - #u : ℕ) : ℚ) / c * (b * affineDegree P * R) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
    exact hlower.trans hupper
  refine hS'.trans ?_
  rw [incidenceProduct_succ, ← hR_def]
  calc ((Fintype.card ι - #u : ℕ) : ℚ) / c * (b * affineDegree P * R)
      ≤ ((Fintype.card ι - T e + 1 : ℕ) : ℚ) / ((A - T e + 1 : ℕ) : ℚ) *
          (b * affineDegree P * R) :=
        mul_le_mul_of_nonneg_right hratio
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P)) hR)
    _ = affineDegree P * (R * ((((Fintype.card ι - T e + 1) * b : ℕ) : ℚ) /
          ((A - T e + 1 : ℕ) : ℚ))) := by
        push_cast
        ring

/-- **Agreement incidence outside an excluded set.** Let `P` be a prime of `MvPolynomial σ k` of
dimension `d = natDegree H(P)`, let `cuts : ι → MvPolynomial σ k` be a finite family of total
degree at most `b`, and let `L ≤ A`. Suppose that for every prime `Q ⊇ P` with `s ∉ Q`, positive
dimension, and at least `L` cuts in `Q`, the principal open subset `U(Q)` lies in `excluded`.
Then every finite set `S` of points of `U(P)` outside `excluded`, each agreeing with at least `A`
cuts, satisfies

  `#S ≤ affineDegree P * (Fintype.card ι * b / (A - L + 1)) ^ d`.

The hypothesis on `excluded` is imposed on every prime above `P`, so that it passes to the
components met by the induction; `excluded` need not be algebraic. Points may lie in any field
extension `K` of `k`, which need not be algebraically closed. This is the constant threshold
`L` in `card_le_incidenceProduct_of_agreement_off_excluded`, with the factor
`(Fintype.card ι - L + 1) * b` bounded by `Fintype.card ι * b` when `L ≥ 1`.

The hypothesis `L ≤ A` is needed: for `P = ⊥` in one variable, no cuts, `A = 0` and `L = 1`, the
hypothesis on `excluded = ∅` is vacuous, but the bound is `0` while `S` can be any finite set.
Primality of `P` is needed for purity of principal cuts; see
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity`. -/
theorem card_le_of_agreement_off_excluded [Finite σ] [Fintype ι] {P : Ideal (MvPolynomial σ k)}
    [hP : P.IsPrime] (s : MvPolynomial σ k) (cuts : ι → MvPolynomial σ k) {b A L : ℕ}
    (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (hLA : L ≤ A) (excluded : Set (σ → K))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree → L ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K)) (hS : ∀ x ∈ S, x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P *
      (((Fintype.card ι * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg (by positivity) _)
  have hcore := card_le_incidenceProduct_of_agreement_off_excluded s cuts hdeg (fun _ ↦ L)
    (fun _ _ ↦ hLA) excluded (fun Q hPQ hQ hsQ hdQ hLQ ↦ hterminal Q hPQ hQ hsQ hdQ hLQ) S hS hA
  rw [incidenceProduct_const] at hcore
  refine hcore.trans (mul_le_mul_of_nonneg_left ?_ (affineDegree_nonneg P))
  rcases Nat.eq_zero_or_pos L with hL | hL
  · rcases Nat.eq_zero_or_pos (affineHilbertPolynomial P).natDegree with hd | hd
    · simp [hd]
    · have hsP : s ∉ P := fun h ↦ (hS x₀ hx₀).2.1 ((hS x₀ hx₀).1 s h)
      exact absurd (hterminal P le_rfl hP hsP hd (by omega) ⟨(hS x₀ hx₀).1, (hS x₀ hx₀).2.1⟩)
        (hS x₀ hx₀).2.2
  · have hAn : A ≤ Fintype.card ι := le_fintypeCard_of_le_ncard (hA x₀ hx₀)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.mul_le_mul_right b (by omega : Fintype.card ι - L + 1 ≤ _))
      (by positivity)) _

/-- If every finite subset of `S` has at most `B` elements, then `S` is finite with at most `B`
elements. -/
private theorem finite_and_ncard_le_of_forall_finset {α : Type*} {S : Set α} {B : ℚ}
    (h : ∀ T : Finset α, (T : Set α) ⊆ S → (#T : ℚ) ≤ B) : S.Finite ∧ (S.ncard : ℚ) ≤ B := by
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hTS, hT⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊B⌋₊ + 1)
    have hB := h T hTS
    rw [hT] at hB
    have hB0 : 0 ≤ B := le_trans (by positivity) hB
    push_cast at hB
    linarith [Nat.lt_floor_add_one B]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact h _ (by simp)

/-- **Agreement incidence outside an excluded set, for the set of all points.** Under the
hypotheses of `card_le_of_agreement_off_excluded`, the set of all points of `U(P)` outside
`excluded` agreeing with at least `A` cuts is finite, with at most
`affineDegree P * (Fintype.card ι * b / (A - L + 1)) ^ d` elements. Every finite subset obeys the
bound, and a set whose finite subsets are uniformly bounded is finite. -/
theorem finite_and_ncard_le_of_agreement_off_excluded [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A L : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (excluded : Set (σ → K))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree → L ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded) :
    {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      (((Fintype.card ι * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree :=
  finite_and_ncard_le_of_forall_finset fun T hT ↦
    card_le_of_agreement_off_excluded s cuts hdeg hLA excluded hterminal T
      (fun _x hx ↦ ⟨(hT hx).1, (hT hx).2.1, (hT hx).2.2.1⟩) fun _x hx ↦ (hT hx).2.2.2

/-- **Agreement incidence with a dimension-dependent threshold, for the set of all points.**
Under the hypotheses of `card_le_incidenceProduct_of_agreement_off_excluded`, the set of all
points of `U(P)` outside `excluded` agreeing with at least `A` cuts is finite, with at most
`affineDegree P * incidenceProduct (Fintype.card ι) A b T d` elements. -/
theorem finite_and_ncard_le_incidenceProduct_of_agreement_off_excluded [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (T : ℕ → ℕ) (hTA : ∀ t < (affineHilbertPolynomial P).natDegree, T t ≤ A)
    (excluded : Set (σ → K))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      T ((affineHilbertPolynomial Q).natDegree - 1) ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded) :
    {x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → K | x ∈ zeroLocus K P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      incidenceProduct (Fintype.card ι) A b T (affineHilbertPolynomial P).natDegree :=
  finite_and_ncard_le_of_forall_finset fun S hS ↦
    card_le_incidenceProduct_of_agreement_off_excluded s cuts hdeg T hTA excluded hterminal S
      (fun _x hx ↦ ⟨(hS hx).1, (hS hx).2.1, (hS hx).2.2.1⟩) fun _x hx ↦ (hS hx).2.2.2

/-- Over an algebraically closed field `k`, let `Q` be a prime of positive dimension with `s ∉ Q`,
and suppose that for every set `T` of `m` cuts, at most one point of `U(Q)` agrees with all cuts
in `T`. Then fewer than `m` cuts lie in `Q`.

Otherwise choose `m` cuts in `Q`; they vanish on all of `U(Q)`, which is then a subsingleton,
hence finite. Since `Q` is prime and `s ∉ Q`, a finite `U(Q)` forces
`natDegree H(Q) = 0` (`finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`).
Algebraic closedness is needed for this last step: over `ℚ`, the prime `span {X 0 ^ 2 + 1}` of
`ℚ[X 0, X 1]` has no rational points and dimension `1`, and contains the cut `X 0 ^ 2 + 1`, so the
uniqueness hypothesis holds for `m = 1` while one cut lies in the prime. -/
theorem ncard_setOf_mem_lt_of_subsingleton [IsAlgClosed k] [Finite σ] [Finite ι]
    {Q : Ideal (MvPolynomial σ k)} [Q.IsPrime] {s : MvPolynomial σ k} (hs : s ∉ Q)
    (cuts : ι → MvPolynomial σ k) {m : ℕ} (hd : 0 < (affineHilbertPolynomial Q).natDegree)
    (hunique : ∀ T : Finset ι, #T = m → Set.Subsingleton
      {x : σ → k | x ∈ zeroLocus k Q ∧ aeval x s ≠ 0 ∧ ∀ i ∈ T, aeval x (cuts i) = 0}) :
    {i | cuts i ∈ Q}.ncard < m := by
  by_contra hm
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_card_eq (not_lt.mp hm)
  have hreg : IsLeftRegular (Ideal.Quotient.mk Q s) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hfin : {x : σ → k | x ∈ zeroLocus k Q ∧ aeval x s ≠ 0}.Finite :=
    ((hunique T.toFinite.toFinset (by rw [← Set.ncard_eq_toFinset_card]; exact hTcard)).anti
      fun x hx ↦ ⟨hx.1, hx.2, fun i hi ↦ hx.1 _ (hTsub (by simpa using hi))⟩).finite
  have := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hreg).mp hfin
  omega

/-- Under uniqueness, the hypothesis of `card_le_of_agreement_off_excluded` holds with
`excluded = ∅` and `L = m`: a prime `Q ⊇ P` inherits uniqueness from `P`, so by
`ncard_setOf_mem_lt_of_subsingleton` it cannot be positive-dimensional with `m` cuts. -/
private theorem subset_empty_of_subsingleton [IsAlgClosed k] [Finite σ] [Finite ι]
    {P : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k} {cuts : ι → MvPolynomial σ k} {m : ℕ}
    (hunique : ∀ T : Finset ι, #T = m → Set.Subsingleton
      {x : σ → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧ ∀ i ∈ T, aeval x (cuts i) = 0})
    (Q : Ideal (MvPolynomial σ k)) (hPQ : P ≤ Q) (hQ : Q.IsPrime) (hsQ : s ∉ Q)
    (hd : 0 < (affineHilbertPolynomial Q).natDegree) (hm : m ≤ {i | cuts i ∈ Q}.ncard) :
    {x : σ → k | x ∈ zeroLocus k Q ∧ aeval x s ≠ 0} ⊆ ∅ := by
  refine absurd hm (not_le.mpr (ncard_setOf_mem_lt_of_subsingleton hsQ cuts hd fun T hT ↦ ?_))
  exact (hunique T hT).anti fun x hx ↦ ⟨zeroLocus_anti_mono hPQ hx.1, hx.2⟩

/-- **Agreement incidence under uniqueness.** Over an algebraically closed field `k`, let `P` be
prime of dimension `d`, `cuts : ι → MvPolynomial σ k` of total degree at most `b`, and `m ≤ A`.
Suppose that for every set `T` of `m` cuts, at most one point of `U(P)` agrees with all cuts in
`T`. Then every finite set `S ⊆ U(P)` of points agreeing with at least `A` cuts satisfies

  `#S ≤ affineDegree P * (Fintype.card ι * b / (A - m + 1)) ^ d`.

This is `card_le_of_agreement_off_excluded` with `excluded = ∅` and `L = m`, whose hypothesis
holds by `ncard_setOf_mem_lt_of_subsingleton`. The hypothesis `m ≤ A` is needed: for `P = ⊥` in
one variable, no cuts, `m = 1` and `A = 0`, there is no set of `m` cuts, so uniqueness holds
vacuously, but the bound is `0` while `S` can be any finite set. -/
theorem card_le_of_agreement_of_subsingleton [IsAlgClosed k] [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A)
    (hunique : ∀ T : Finset ι, #T = m → Set.Subsingleton
      {x : σ → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧ ∀ i ∈ T, aeval x (cuts i) = 0})
    (S : Finset (σ → k)) (hS : ∀ x ∈ S, x ∈ zeroLocus k P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ affineDegree P *
      (((Fintype.card ι * b : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree :=
  card_le_of_agreement_off_excluded s cuts hdeg hmA ∅ (subset_empty_of_subsingleton hunique) S
    (fun x hx ↦ ⟨(hS x hx).1, (hS x hx).2, Set.notMem_empty x⟩) hA

/-- **Agreement incidence under uniqueness, for the set of all points.** Under the hypotheses of
`card_le_of_agreement_of_subsingleton`, the set of all points of `U(P)` agreeing with at least `A`
cuts is finite, with at most `affineDegree P * (Fintype.card ι * b / (A - m + 1)) ^ d`
elements. -/
theorem finite_and_ncard_le_of_agreement_of_subsingleton [IsAlgClosed k] [Finite σ] [Fintype ι]
    {P : Ideal (MvPolynomial σ k)} [P.IsPrime] (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A m : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A)
    (hunique : ∀ T : Finset ι, #T = m → Set.Subsingleton
      {x : σ → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧ ∀ i ∈ T, aeval x (cuts i) = 0}) :
    {x : σ → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.Finite ∧
      ({x : σ → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧
        A ≤ {i | aeval x (cuts i) = 0}.ncard}.ncard : ℚ) ≤ affineDegree P *
      (((Fintype.card ι * b : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree :=
  finite_and_ncard_le_of_forall_finset fun T hT ↦
    card_le_of_agreement_of_subsingleton s cuts hdeg hmA hunique T
      (fun _x hx ↦ ⟨(hT hx).1, (hT hx).2.1⟩) fun _x hx ↦ (hT hx).2.2

/-- **Agreement incidence over a finite family of primes.** Let `T` be a finite family of primes
and let every finite set `S` of points be covered by the principal open subsets `U(Q)`, `Q ∈ T`.
Under the hypotheses of `card_le_of_agreement_off_excluded` for each member of `T`,

  `#S ≤ ∑ Q ∈ T, affineDegree Q * (Fintype.card ι * b / (A - L + 1)) ^ natDegree H(Q)`.

Each point is counted on one member containing it, and `card_le_of_agreement_off_excluded`
bounds the points on each member. Members may share points; the bound counts them once per
member. -/
theorem card_le_sum_of_agreement_off_excluded [Finite σ] [Fintype ι]
    (T : Finset (Ideal (MvPolynomial σ k))) (hT : ∀ Q ∈ T, Q.IsPrime) (s : MvPolynomial σ k)
    (cuts : ι → MvPolynomial σ k) {b A L : ℕ} (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (excluded : Set (σ → K))
    (hterminal : ∀ Q ∈ T, ∀ J : Ideal (MvPolynomial σ k), Q ≤ J → J.IsPrime → s ∉ J →
      0 < (affineHilbertPolynomial J).natDegree → L ≤ {i | cuts i ∈ J}.ncard →
      {x : σ → K | x ∈ zeroLocus K J ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K))
    (hS : ∀ x ∈ S, (∃ Q ∈ T, x ∈ zeroLocus K Q) ∧ aeval x s ≠ 0 ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ ∑ Q ∈ T, affineDegree Q *
      (((Fintype.card ι * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial Q).natDegree := by
  classical
  have hcover : #S ≤ ∑ Q ∈ T, #(S.filter (· ∈ zeroLocus K Q)) := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans Finset.card_biUnion_le
    obtain ⟨Q, hQ, hxQ⟩ := (hS x hx).1
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_filter.mpr ⟨hx, hxQ⟩⟩
  refine (Nat.cast_le.mpr hcover).trans ?_
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun Q hQ ↦ ?_
  have := hT Q hQ
  exact card_le_of_agreement_off_excluded s cuts hdeg hLA excluded (hterminal Q hQ) _
    (fun x hx ↦ by
      rw [Finset.mem_filter] at hx
      exact ⟨hx.2, (hS x hx.1).2.1, (hS x hx.1).2.2⟩)
    fun x hx ↦ hA x (Finset.mem_filter.mp hx).1

/-- **Agreement incidence on a cut hypersurface.** Let `g ≠ 0` have total degree at most `v`, let
`highCuts` be a list of polynomials and `cuts : ι → MvPolynomial σ k` a finite family, all of total
degree at most `b`, and let `L ≤ A` with `A - L + 1 ≤ Fintype.card ι`. Suppose that every prime
`J` with `s ∉ J`, containing `g` and every element of `highCuts`, of positive dimension, and
containing at least `L` cuts, has `U(J)` inside `excluded`. Then every finite set `S` of points
over `K` with `g = 0`, `s ≠ 0`, all of `highCuts` vanishing, outside `excluded`, and agreeing with
at least `A` cuts satisfies

  `#S ≤ v * (Fintype.card ι * b / (A - L + 1)) ^ (Nat.card σ - 1)`.

The points lie on the iterated retained cut family of the components of `g = 0` by `highCuts`
(`exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`); `card_le_sum_of_agreement_off_excluded`
bounds them by a sum over this family; each member has dimension at most `Nat.card σ - 1`
(`natDegree_affineHilbertPolynomial_le_of_mem`), and the potential of the family is at most
`v * b ^ (Nat.card σ - 1)` (`sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le`).

The hypothesis `A - L + 1 ≤ Fintype.card ι` makes the ratio `Fintype.card ι / (A - L + 1)` at
least `1`, so that raising it to a member's dimension is bounded by raising it to
`Nat.card σ - 1`. It is needed: in two variables, take `g = X 0`, `highCuts = [X 1]`, `s = 1`, no
cuts and `A = L = 0`. The only prime containing `X 0` and `X 1` is maximal, so the hypothesis on
`excluded = ∅` is vacuous, and the origin is a point of `S`, while the bound is `0`. -/
theorem card_le_of_agreement_off_excluded_of_hypersurface [Finite σ] [Fintype ι]
    {g : MvPolynomial σ k} (hg : g ≠ 0) (s : MvPolynomial σ k) {v b A L : ℕ}
    (hv : g.totalDegree ≤ v) (highCuts : List (MvPolynomial σ k))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ b) (cuts : ι → MvPolynomial σ k)
    (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (hLA : L ≤ A) (hAn : A - L + 1 ≤ Fintype.card ι)
    (excluded : Set (σ → K))
    (hterminal : ∀ J : Ideal (MvPolynomial σ k), J.IsPrime → s ∉ J → g ∈ J →
      (∀ f ∈ highCuts, f ∈ J) → 0 < (affineHilbertPolynomial J).natDegree →
      L ≤ {i | cuts i ∈ J}.ncard → {x : σ → K | x ∈ zeroLocus K J ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧ (∀ f ∈ highCuts, aeval x f = 0) ∧
      x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ v * (((Fintype.card ι * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
      (Nat.card σ - 1) := by
  set T := Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s highCuts
  set c : ℚ := ((A - L + 1 : ℕ) : ℚ) with hc_def
  set t : ℚ := (Fintype.card ι : ℚ) / c with ht_def
  have hcpos : 0 < c := by positivity
  have ht : 1 ≤ t := (one_le_div hcpos).mpr (by rw [hc_def]; exact_mod_cast hAn)
  have hratio : ((Fintype.card ι * b : ℕ) : ℚ) / c = b * t := by
    rw [ht_def, Nat.cast_mul]
    ring
  have hmem : ∀ Q ∈ T, g ∈ Q ∧ ∀ f ∈ highCuts, f ∈ Q := fun Q hQ ↦ by
    obtain ⟨P, hP, hPQ, hcuts⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hQ
    exact ⟨hPQ ((Ideal.mem_retainedMinimalPrimes.mp hP).1.le (Ideal.mem_span_singleton_self g)),
      hcuts⟩
  have hbound := card_le_sum_of_agreement_off_excluded T
    (fun _ ↦ Ideal.isPrime_of_mem_iteratedRetainedCutFamily
      (fun _ hP ↦ (Ideal.mem_retainedMinimalPrimes.mp hP).1.isPrime) s highCuts)
    s cuts hdeg hLA excluded
    (fun Q hQ J hQJ hJ hsJ hdJ hLJ ↦ hterminal J hJ hsJ (hQJ (hmem Q hQ).1)
      (fun f hf ↦ hQJ ((hmem Q hQ).2 f hf)) hdJ hLJ) S
    (fun x hx ↦ by
      obtain ⟨hgx, hsx, hhx, hex⟩ := hS x hx
      have hxg : x ∈ zeroLocus K (Ideal.span {g}) := mem_zeroLocus_iff_le_ker_aeval.mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hgx))
      obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ s x hxg hsx
      obtain ⟨Q, hQ, -, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus hP hxP hsx hhx
      exact ⟨⟨Q, hQ, hxQ⟩, hsx, hex⟩) hA
  refine hbound.trans ?_
  rw [hratio]
  calc ∑ Q ∈ T, affineDegree Q * ((b : ℚ) * t) ^ (affineHilbertPolynomial Q).natDegree
      ≤ ∑ Q ∈ T, affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree *
          t ^ (Nat.card σ - 1) := by
        refine Finset.sum_le_sum fun Q hQ ↦ ?_
        rw [mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ht (natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ).1))
          (mul_nonneg (affineDegree_nonneg Q) (by positivity))
    _ = (∑ Q ∈ T, affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree) *
          t ^ (Nat.card σ - 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ (v * (b : ℚ) ^ (Nat.card σ - 1)) * t ^ (Nat.card σ - 1) :=
        mul_le_mul_of_nonneg_right
          (sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le hg s hv hhigh)
          (by positivity)
    _ = v * ((b : ℚ) * t) ^ (Nat.card σ - 1) := by ring

/-- **Agreement incidence after a list of fixed cuts.** Let `Ps` be a finite family of primes of
dimension at most `d` whose affine degrees sum to at most `V`, let `highCuts` be a list of
polynomials of total degree at most `B > 0`, and let `cuts : ι → MvPolynomial σ k` have total
degree at most `b > 0`. Let `T : ℕ → ℕ` with `T t ≤ A` for `t < D`. Suppose that every prime
`Q` above a member of `Ps` with `s ∉ Q` containing every element of `highCuts` has dimension at
most `D`, and that such a `Q` of positive dimension `e + 1` containing at least `T e` cuts has
`U(Q)` inside `excluded`. Then every finite set `S` of points of the zero loci of members of
`Ps` with `s ≠ 0`, all of `highCuts` vanishing, outside `excluded`, and agreeing with at least
`A` cuts satisfies

  `#S ≤ V * B ^ d * incidenceProduct (Fintype.card ι) A b T D`.

The points lie on the members of the iterated retained cut family of `Ps` by `highCuts`
(`exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`), whose affine degrees sum to at most
`V * B ^ d` (`sum_affineDegree_iteratedRetainedCutFamily_le`).
`card_le_incidenceProduct_of_agreement_off_excluded` bounds the points on each member, and the
product is monotone in the dimension (`incidenceProduct_mono_dimension`). -/
theorem card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily
    [Finite σ] [Fintype ι] (Ps : Finset (Ideal (MvPolynomial σ k)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) (s : MvPolynomial σ k) {d : ℕ}
    (hdim : ∀ P ∈ Ps, (affineHilbertPolynomial P).natDegree ≤ d) {V : ℚ}
    (hV : ∑ P ∈ Ps, affineDegree P ≤ V) (highCuts : List (MvPolynomial σ k)) {B : ℕ}
    (hB : 0 < B) (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B) (cuts : ι → MvPolynomial σ k)
    {b A D : ℕ} (hb : 0 < b) (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (T : ℕ → ℕ)
    (hTA : ∀ t < D, T t ≤ A) (excluded : Set (σ → K))
    (hD : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → (affineHilbertPolynomial Q).natDegree ≤ D)
    (hterminal : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ k), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      T ((affineHilbertPolynomial Q).natDegree - 1) ≤ {i | cuts i ∈ Q}.ncard →
      {x : σ → K | x ∈ zeroLocus K Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → K))
    (hS : ∀ x ∈ S, (∃ P ∈ Ps, x ∈ zeroLocus K P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (#S : ℚ) ≤ V * (B : ℚ) ^ d * incidenceProduct (Fintype.card ι) A b T D := by
  classical
  set F := Ideal.iteratedRetainedCutFamily Ps s highCuts
  set R : ℚ := incidenceProduct (Fintype.card ι) A b T D with hR_def
  have hR : 0 ≤ R := incidenceProduct_nonneg _ A b T D
  have hcover : #S ≤ ∑ Q ∈ F, #(S.filter (· ∈ zeroLocus K Q)) := by
    refine (Finset.card_le_card fun x hx ↦ ?_).trans Finset.card_biUnion_le
    obtain ⟨P, hP, hxP⟩ := (hS x hx).1
    obtain ⟨Q, hQ, -, hxQ⟩ :=
      exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus hP hxP (hS x hx).2.1 (hS x hx).2.2.1
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_filter.mpr ⟨hx, hxQ⟩⟩
  have hmember : ∀ Q ∈ F, (#(S.filter (· ∈ zeroLocus K Q)) : ℚ) ≤ affineDegree Q * R := by
    intro Q hQ
    rcases (S.filter (· ∈ zeroLocus K Q)).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (affineDegree_nonneg Q) hR
    rw [Finset.mem_filter] at hx₀
    have := Ideal.isPrime_of_mem_iteratedRetainedCutFamily hprime s highCuts hQ
    obtain ⟨P, hP, hPQ, hhighQ⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hQ
    have hsQ : s ∉ Q := fun h ↦ (hS x₀ hx₀.1).2.1 (hx₀.2 s h)
    have hQD := hD P hP Q hPQ this hsQ hhighQ
    have hAn : A ≤ Fintype.card ι := le_fintypeCard_of_le_ncard (hA x₀ hx₀.1)
    refine (card_le_incidenceProduct_of_agreement_off_excluded s cuts hdeg T
      (fun t ht ↦ hTA t (by omega)) excluded
      (fun J hQJ hJ hsJ hdJ hTJ ↦ hterminal P hP J (hPQ.trans hQJ) hJ hsJ
        (fun f hf ↦ hQJ (hhighQ f hf)) hdJ hTJ) _
      (fun x hx ↦ by
        rw [Finset.mem_filter] at hx
        exact ⟨hx.2, (hS x hx.1).2.1, (hS x hx.1).2.2.2⟩)
      fun x hx ↦ hA x (Finset.mem_filter.mp hx).1).trans ?_
    exact mul_le_mul_of_nonneg_left (incidenceProduct_mono_dimension T hAn hb hQD)
      (affineDegree_nonneg Q)
  have hpotential : ∑ Q ∈ F, affineDegree Q ≤ V * (B : ℚ) ^ d := by
    refine (sum_affineDegree_iteratedRetainedCutFamily_le hprime s hB hhigh).trans ?_
    calc ∑ P ∈ Ps, affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree
        ≤ ∑ P ∈ Ps, affineDegree P * (B : ℚ) ^ d :=
          Finset.sum_le_sum fun P hP ↦ mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by exact_mod_cast hB) (hdim P hP)) (affineDegree_nonneg P)
      _ = (∑ P ∈ Ps, affineDegree P) * (B : ℚ) ^ d := (Finset.sum_mul _ _ _).symm
      _ ≤ V * (B : ℚ) ^ d := mul_le_mul_of_nonneg_right hV (by positivity)
  calc (#S : ℚ) ≤ ∑ Q ∈ F, (#(S.filter (· ∈ zeroLocus K Q)) : ℚ) := by exact_mod_cast hcover
    _ ≤ ∑ Q ∈ F, affineDegree Q * R := Finset.sum_le_sum hmember
    _ = (∑ Q ∈ F, affineDegree Q) * R := (Finset.sum_mul _ _ _).symm
    _ ≤ V * (B : ℚ) ^ d * R := mul_le_mul_of_nonneg_right hpotential hR

end MvPolynomial
