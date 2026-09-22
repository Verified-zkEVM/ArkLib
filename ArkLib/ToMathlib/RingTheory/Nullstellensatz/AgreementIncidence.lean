/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial
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

The proof is an induction on `d`. In dimension zero the whole zero locus has at most
`affineDegree P` points. In positive dimension, the hypothesis applied to `P` itself shows that
fewer than `L` cuts lie in `P`. Each counted point agrees with at least `A - L + 1` of the
remaining cuts, so double counting gives
`#S * (A - L + 1) ≤ ∑_{cuts i ∉ P} #{x ∈ S | cuts i (x) = 0}`. For a cut `f ∉ P`, the points on
`f = 0` lie on the minimal primes of `P ⊔ span {f}` not containing `s`; these have dimension
`d - 1` by purity, the induction hypothesis bounds the points on each, and the Bézout bound sums
their degrees to at most `b * affineDegree P`. Summing over at most `n` cuts and dividing by
`A - L + 1` closes the induction.

If `k` is algebraically closed and any `m` cuts determine a point of `U(P)`, then a
positive-dimensional `U(Q)` can contain at most one point agreeing with `m` cuts, so it is finite,
which contradicts positive dimension; hence fewer than `m` cuts lie in `Q`, and the hypothesis
above holds with `excluded = ∅` and `L = m`.

## Main statements

* `MvPolynomial.ncard_inter_cut_le_sum_retainedMinimalPrimes`: the points of a finite subset of
  `U(I)` on a hypersurface are covered by the retained components of the cut.
* `MvPolynomial.ncard_inter_cut_le_of_retained_le`: one inductive step, bounding the points on a
  cut `f ∉ P` from bounds on each retained component.
* `MvPolynomial.card_le_of_agreement_off_excluded` and
  `MvPolynomial.finite_and_ncard_le_of_agreement_off_excluded`: the incidence bound outside an
  excluded set, for a finite set of points and for the set of all such points.
* `MvPolynomial.ncard_setOf_mem_lt_of_subsingleton`: over an algebraically closed field, fewer
  than `m` cuts vanish on a positive-dimensional prime whose principal open subset is determined
  by any `m` cuts.
* `MvPolynomial.card_le_of_agreement_of_subsingleton` and
  `MvPolynomial.finite_and_ncard_le_of_agreement_of_subsingleton`: the incidence bound under
  uniqueness.
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

/-- **Agreement incidence outside an excluded set.** Let `P` be a prime of `MvPolynomial σ k` of
dimension `d = natDegree H(P)`, let `cuts : ι → MvPolynomial σ k` be a finite family of total
degree at most `b`, and let `L ≤ A`. Suppose that for every prime `Q ⊇ P` with `s ∉ Q`, positive
dimension, and at least `L` cuts in `Q`, the principal open subset `U(Q)` lies in `excluded`.
Then every finite set `S` of points of `U(P)` outside `excluded`, each agreeing with at least `A`
cuts, satisfies

  `#S ≤ affineDegree P * (Fintype.card ι * b / (A - L + 1)) ^ d`.

The hypothesis on `excluded` is imposed on every prime above `P`, so that it passes to the
components met by the induction; `excluded` need not be algebraic. Points may lie in any field
extension `K` of `k`, which need not be algebraically closed.

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
  classical
  set c : ℚ := ((A - L + 1 : ℕ) : ℚ) with hc_def
  set R : ℚ := ((Fintype.card ι * b : ℕ) : ℚ) / c with hR_def
  have hcpos : 0 < c := by positivity
  have hR : 0 ≤ R := by positivity
  obtain ⟨d, hd⟩ : ∃ d, (affineHilbertPolynomial P).natDegree = d := ⟨_, rfl⟩
  rw [hd]
  induction d using Nat.strong_induction_on generalizing P S with
  | _ d ih =>
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg hR d)
  rcases d with _ | e
  · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := K) P hd
    have hcard : (#S : ℚ) ≤ (zeroLocus K P).ncard := by
      have := Set.ncard_le_ncard (fun x (hx : x ∈ (S : Set (σ → K))) ↦ (hS x hx).1) hfin.1
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    simpa using hcard.trans hfin.2
  have hsP : s ∉ P := fun h ↦ (hS x₀ hx₀).2.1 ((hS x₀ hx₀).1 s h)
  let r : (σ → K) → ι → Prop := fun x i ↦ aeval x (cuts i) = 0
  let u : Finset ι := Finset.univ.filter fun i ↦ cuts i ∈ P
  have hu : #u < L := by
    have hu_eq : #u = {i | cuts i ∈ P}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [u]
    rw [hu_eq]
    by_contra h
    exact (hS x₀ hx₀).2.2 (hterminal P le_rfl hP hsP (by omega) (not_lt.mp h)
      ⟨(hS x₀ hx₀).1, (hS x₀ hx₀).2.1⟩)
  have hlowerNat : #S * (A - L + 1) ≤ ∑ i ∈ uᶜ, #(S.bipartiteBelow r i) := by
    refine Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow r u hLA hu
      fun x hx ↦ ?_
    rw [← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
    simpa [r] using hA x hx
  have hlower : (#S : ℚ) * c ≤ ∑ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) := by
    have := (Nat.cast_le (α := ℚ)).mpr hlowerNat
    rwa [Nat.cast_mul, Nat.cast_sum] at this
  have hcut : ∀ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) ≤ b * affineDegree P * R ^ e := by
    intro i hi
    have hiP : cuts i ∉ P := by simpa [u] using hi
    rw [← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
    refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) S
      (fun x hx ↦ ⟨(hS x hx).1, (hS x hx).2.1⟩) (pow_nonneg hR e) fun Q hQ ↦ ?_
    have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
    have hsQ := (Ideal.mem_retainedMinimalPrimes.mp hQ).2
    have : Q.IsPrime := hQmin.isPrime
    have hPQ : P ≤ Q := le_sup_left.trans hQmin.le
    have hQdeg : (affineHilbertPolynomial Q).natDegree = e := by
      have := principalCut_natDegree_affineHilbertPolynomial_add_one hiP hQmin
      omega
    have := ih e (by omega) (P := Q) (S := S.filter (· ∈ zeroLocus K Q))
      (fun J hQJ hJ hsJ hdJ hLJ ↦ hterminal J (hPQ.trans hQJ) hJ hsJ hdJ hLJ)
      (fun x hx ↦ by
        rw [Finset.mem_filter] at hx
        exact ⟨hx.2, (hS x hx.1).2.1, (hS x hx.1).2.2⟩)
      (fun x hx ↦ hA x (Finset.mem_filter.mp hx).1) hQdeg
    rwa [show (S : Set (σ → K)) ∩ zeroLocus K Q = (S : Set (σ → K)) ∩ {x | x ∈ zeroLocus K Q}
      from rfl, ncard_coe_inter_setOf]
  have hupper : ∑ i ∈ uᶜ, (#(S.bipartiteBelow r i) : ℚ) ≤
      Fintype.card ι * (b * affineDegree P * R ^ e) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P)) (pow_nonneg hR e))
  have hRc : R * c = Fintype.card ι * b := by
    rw [hR_def, div_mul_cancel₀ _ hcpos.ne']
    push_cast
    ring
  refine le_of_mul_le_mul_right (hlower.trans (hupper.trans (le_of_eq ?_))) hcpos
  calc (Fintype.card ι : ℚ) * (b * affineDegree P * R ^ e)
      = affineDegree P * R ^ e * (Fintype.card ι * b) := by ring
    _ = affineDegree P * R ^ (e + 1) * c := by rw [← hRc, pow_succ]; ring

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

end MvPolynomial
