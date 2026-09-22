/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance tests for agreement incidence on principal open subsets

These examples use the public API through an ordinary import. On the affine line over the
algebraic closure `K` of `ℚ`, the four cuts `x, x, x - 1, x - 1` determine a point by any one of
them, so at most `1 * (4 * 1 / (2 - 1 + 1)) ^ 1 = 2` points agree with two cuts; the points `0`
and `1` do. With rational cuts `x` and `x - 1` and points in `K`, no prime contains both cuts, so
the excluded-set theorem applies with `excluded = ∅` over the non-closed field `ℚ`; the product
over the threshold `2` bounds the same points by `1`. The boundary examples show that `L ≤ A` is
needed in the main theorem and that `s` must not vanish on the points in the cover lemma.

On the line `x = 0` of the plane, the iterated-family bound with threshold `1` and dimension `1`
is `2`, attained by `(0, 0)` and `(0, 1)` for the cuts `y` and `y - 1`. Further boundary examples
show that `T t ≤ A` is needed in the product bound, and `0 < b` and `0 < B` in the iterated-family
bound. The last examples restate the main results for cuts indexed by `Fin n`, with the counts
written as filters of `Finset.univ`.
-/

open MvPolynomial

namespace AgreementIncidenceTest

local notation "K" => AlgebraicClosure ℚ

/-- A linear cut `x - a` on the line has total degree at most `1`. -/
theorem totalDegree_X_sub_C_le {k : Type*} [Field k] (a : k) :
    (X 0 - C a : MvPolynomial (Fin 1) k).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (by simp)

/-- On the line, a point agreeing with one linear cut `x - c i` is the point `c i`, so the points
agreeing with any single cut form a subsingleton. -/
theorem subsingleton_linearCuts {k : Type*} [Field k] {n : ℕ} (c : Fin n → k)
    (P : Ideal (MvPolynomial (Fin 1) k)) (s : MvPolynomial (Fin 1) k) (T : Finset (Fin n))
    (hT : T.card = 1) :
    Set.Subsingleton {x : Fin 1 → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧
      ∀ i ∈ T, aeval x (X 0 - C (c i) : MvPolynomial (Fin 1) k) = 0} := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hT
  intro x hx y hy
  have hx' := hx.2.2 i (Finset.mem_singleton_self i)
  have hy' := hy.2.2 i (Finset.mem_singleton_self i)
  simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hx' hy'
  funext j
  rw [Subsingleton.elim j 0, hx', hy']

/-- A prime of `ℚ[x]` does not contain both cuts `x` and `x - 1`, since it would contain their
difference `1`. -/
theorem not_two_le_ncard_linearCuts {Q : Ideal (MvPolynomial (Fin 1) ℚ)} (hQ : Q.IsPrime) :
    ¬ 2 ≤ {i | (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ) ∈ Q}.ncard := by
  intro hL
  have huniv : {i | (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ) ∈ Q} = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using hL)
  have hone := Q.sub_mem (Set.eq_univ_iff_forall.mp huniv 0) (Set.eq_univ_iff_forall.mp huniv 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, sub_zero,
    sub_sub_cancel, map_one] at hone
  exact absurd ((Ideal.eq_top_iff_one Q).mpr hone) hQ.ne_top

/-- At most two points of the line over `K` agree with two of the cuts `x, x, x - 1, x - 1`.
Any one cut determines a point, so `m = 1`, and the bound is
`affineDegree ⊥ * (4 * 1 / (2 - 1 + 1)) ^ 1 = 2`. -/
example :
    let S := {x : Fin 1 → K | x ∈ zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) K)) ∧
      aeval x (1 : MvPolynomial (Fin 1) K) ≠ 0 ∧
      2 ≤ {i | aeval x (X 0 - C (![0, 0, 1, 1] i) : MvPolynomial (Fin 1) K) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 2 := by
  intro S
  have h := finite_and_ncard_le_of_agreement_of_subsingleton (P := ⊥) 1
    (fun i : Fin 4 ↦ (X 0 - C (![0, 0, 1, 1] i) : MvPolynomial (Fin 1) K)) (b := 1) (A := 2)
    (m := 1) (fun _ ↦ totalDegree_X_sub_C_le _) (by norm_num)
    (fun T hT ↦ subsingleton_linearCuts _ _ _ T hT)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp
  norm_num

/-- The excluded-set theorem over the non-closed field `ℚ`, with points in `K`. For the cuts
`x` and `x - 1`, a prime containing both contains their difference `1`, so the hypothesis holds
with `L = 2` and `excluded = ∅`, and at most `1 * (2 * 1 / (2 - 2 + 1)) ^ 1 = 2` points of the
line over `K` agree with both cuts. -/
example :
    let S := {x : Fin 1 → K | x ∈ zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧ x ∉ (∅ : Set (Fin 1 → K)) ∧
      2 ≤ {i | aeval x (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 2 := by
  intro S
  have h := finite_and_ncard_le_of_agreement_off_excluded (P := ⊥) 1
    (fun i : Fin 2 ↦ (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ)) (b := 1) (A := 2) (L := 2)
    (fun _ ↦ totalDegree_X_sub_C_le _) le_rfl (∅ : Set (Fin 1 → K))
    fun Q _ hQ _ _ hL ↦ absurd hL (not_two_le_ncard_linearCuts hQ)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp

/-- With the threshold `2` in every dimension, the product bound for the same data is
`1 * ((2 - 2 + 1) * 1 / (2 - 2 + 1)) = 1`: at most one point of the line agrees with both cuts
`x` and `x - 1`. -/
example :
    let S := {x : Fin 1 → K | x ∈ zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧ x ∉ (∅ : Set (Fin 1 → K)) ∧
      2 ≤ {i | aeval x (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 1 := by
  intro S
  have h := finite_and_ncard_le_incidenceProduct_of_agreement_off_excluded (P := ⊥) 1
    (fun i : Fin 2 ↦ (X 0 - C (![0, 1] i) : MvPolynomial (Fin 1) ℚ)) (b := 1) (A := 2)
    (fun _ ↦ totalDegree_X_sub_C_le _) (fun _ ↦ 2) (fun _ _ ↦ le_rfl) (∅ : Set (Fin 1 → K))
    fun Q _ hQ _ _ hL ↦ absurd hL (not_two_le_ncard_linearCuts hQ)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [incidenceProduct_const]

/-- The hypothesis `L ≤ A` is needed in `card_le_of_agreement_off_excluded`. For `P = ⊥` on the
line over `ℚ`, no cuts, `A = 0`, `L = 1`, `s = 1` and `excluded = ∅`, no prime contains one of
the cuts, so the excluded-set hypothesis holds, and every point agrees with at least `0` cuts. The
bound `1 * (0 * 1 / (0 - 1 + 1)) ^ 1` is `0`, but the one-point set `{0}` has one element. -/
example :
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ), ⊥ ≤ Q → Q.IsPrime →
      (1 : MvPolynomial (Fin 1) ℚ) ∉ Q → 0 < (affineHilbertPolynomial Q).natDegree →
      1 ≤ {i : Fin 0 | (Fin.elim0 i : MvPolynomial (Fin 1) ℚ) ∈ Q}.ncard →
      {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ Q ∧ aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0} ⊆ ∅) ∧
    ¬ ((({0} : Finset (Fin 1 → ℚ)).card : ℚ) ≤
      affineDegree (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) *
        (((Fintype.card (Fin 0) * 1 : ℕ) : ℚ) / ((0 - 1 + 1 : ℕ) : ℚ)) ^
          (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree) := by
  refine ⟨fun Q _ _ _ _ h ↦ absurd h (by simp [Set.eq_empty_of_isEmpty]), by simp⟩

/-- The hypothesis that `s` does not vanish on the points is needed in
`ncard_inter_cut_le_sum_retainedMinimalPrimes`. For `I = ⊥` on the line, `s = f = x` and
`S = {0}`, the point `0` lies on `f = 0`, but the only minimal prime `(x)` of the cut contains
`s`, so no component is retained. -/
example : ¬ ((({0} : Finset (Fin 1 → ℚ)) : Set (Fin 1 → ℚ)) ∩
      {x | aeval x (X 0 : MvPolynomial (Fin 1) ℚ) = 0}).ncard ≤
    ∑ Q ∈ ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ⊔ Ideal.span {X 0}).retainedMinimalPrimes (X 0),
      ((({0} : Finset (Fin 1 → ℚ)) : Set (Fin 1 → ℚ)) ∩ zeroLocus ℚ Q).ncard := by
  have : (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  have hempty : ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ⊔ Ideal.span {X 0}).retainedMinimalPrimes
      (X 0) = ∅ := by
    ext Q
    simp only [Ideal.mem_retainedMinimalPrimes, bot_sup_eq,
      Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff, Finset.notMem_empty,
      iff_false, not_and, not_not]
    rintro rfl
    exact Ideal.subset_span rfl
  rw [hempty, Finset.sum_empty, Nat.le_zero,
    Set.ncard_eq_zero ((Finset.finite_toSet _).subset Set.inter_subset_left)]
  exact Set.nonempty_iff_ne_empty.mp ⟨0, by simp⟩

/-! ### Agreement incidence on a hypersurface -/

/-- The cut `y - a` of the plane has total degree at most `1`. -/
theorem totalDegree_X1_sub_C_le {k : Type*} [Field k] (a : k) :
    (X 1 - C a : MvPolynomial (Fin 2) k).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (by simp)

/-- On the hypersurface `x = 0` of the plane over `ℚ`, with points in `K`, at most two points
agree with both cuts `y` and `y - 1`. A prime containing both cuts contains `1`, so the hypothesis
of `card_le_of_agreement_off_excluded_of_hypersurface` holds with `L = 2` and `excluded = ∅`, and
the bound is `1 * (2 * 1 / (2 - 2 + 1)) ^ (2 - 1) = 2`. -/
example (S : Finset (Fin 2 → K))
    (hS : ∀ x ∈ S, aeval x (X 0 : MvPolynomial (Fin 2) ℚ) = 0)
    (hA : ∀ x ∈ S, 2 ≤ {i | aeval x (X 1 - C (![0, 1] i) : MvPolynomial (Fin 2) ℚ) = 0}.ncard) :
    (S.card : ℚ) ≤ 2 := by
  have h := card_le_of_agreement_off_excluded_of_hypersurface (X_ne_zero 0) 1 (v := 1)
    (b := 1) (A := 2) (L := 2) (by rw [totalDegree_X]) [] (by simp)
    (fun i : Fin 2 ↦ (X 1 - C (![0, 1] i) : MvPolynomial (Fin 2) ℚ))
    (fun _ ↦ totalDegree_X1_sub_C_le _) le_rfl (by simp) (∅ : Set (Fin 2 → K))
    (fun J hJ hsJ _ _ _ hL ↦ by
      have huniv : {i | (X 1 - C (![0, 1] i) : MvPolynomial (Fin 2) ℚ) ∈ J} = Set.univ :=
        Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using hL)
      have hone := J.sub_mem (Set.eq_univ_iff_forall.mp huniv 0)
        (Set.eq_univ_iff_forall.mp huniv 1)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, sub_zero,
        sub_sub_cancel, map_one] at hone
      exact absurd ((Ideal.eq_top_iff_one J).mpr hone) hJ.ne_top)
    S (fun x hx ↦ ⟨hS x hx, by simp, by simp, id⟩) hA
  refine h.trans_eq ?_
  simp

/-- An ideal of `ℚ[x, y]` containing `x` and `y` has dimension `0`: its zero locus over `K` is
at most the origin, the image of the empty parametrization. -/
theorem natDegree_affineHilbertPolynomial_eq_zero_of_X_mem {J : Ideal (MvPolynomial (Fin 2) ℚ)}
    (h0 : X 0 ∈ J) (h1 : X 1 ∈ J) : (affineHilbertPolynomial J).natDegree = 0 := by
  have hreg : IsLeftRegular (Ideal.Quotient.mk J 1) := by
    rw [map_one]
    exact isRegular_one.left
  have h := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range (τ := Empty) hreg
    (fun _ ↦ 0) fun (x : Fin 2 → K) hx _ ↦ ⟨isEmptyElim, ?_⟩
  · simpa using h
  funext i
  have hi : aeval x (X i : MvPolynomial (Fin 2) ℚ) = 0 :=
    (mem_zeroLocus_iff.mp hx) _ (by fin_cases i <;> assumption)
  simpa using hi

/-- The hypothesis `A - L + 1 ≤ Fintype.card ι` is needed in
`card_le_of_agreement_off_excluded_of_hypersurface`. Take `g = x`, `highCuts = [y]`, `s = 1`, no
cuts and `A = L = 0`, so `A - L + 1 = 1 > 0`. A prime containing `x` and `y` has dimension `0`, so
the hypothesis on `excluded = ∅` holds, and the origin satisfies every condition on the points,
but the bound `1 * (0 * 1 / 1) ^ (2 - 1)` is `0`. -/
example :
    (∀ J : Ideal (MvPolynomial (Fin 2) ℚ), J.IsPrime → (1 : MvPolynomial (Fin 2) ℚ) ∉ J →
      X 0 ∈ J → (∀ f ∈ [(X 1 : MvPolynomial (Fin 2) ℚ)], f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      0 ≤ {i : Fin 0 | (Fin.elim0 i : MvPolynomial (Fin 2) ℚ) ∈ J}.ncard →
      {x : Fin 2 → ℚ | x ∈ zeroLocus ℚ J ∧ aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0} ⊆ ∅) ∧
    (∀ x ∈ ({0} : Finset (Fin 2 → ℚ)), aeval x (X 0 : MvPolynomial (Fin 2) ℚ) = 0 ∧
      aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      (∀ f ∈ [(X 1 : MvPolynomial (Fin 2) ℚ)], aeval x f = 0) ∧ x ∉ (∅ : Set (Fin 2 → ℚ))) ∧
    ¬ ((({0} : Finset (Fin 2 → ℚ)).card : ℚ) ≤ (1 : ℕ) *
      (((Fintype.card (Fin 0) * 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) ^ (Nat.card (Fin 2) - 1)) := by
  refine ⟨fun J _ _ h0 hhigh hd _ ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have := natDegree_affineHilbertPolynomial_eq_zero_of_X_mem h0
      (hhigh _ (List.mem_singleton_self _))
    omega
  · rw [Finset.mem_singleton.mp hx]
    simp
  · simp

/-! ### Thresholds depending on the dimension -/

/-- The hypothesis `T t ≤ A` below the dimension is needed in
`card_le_incidenceProduct_of_agreement_off_excluded`. For `P = ⊥` on the line over `ℚ`, no cuts,
`A = 0`, `T = 1`, `s = 1` and `excluded = ∅`, no prime contains one of the cuts, so the
excluded-set hypothesis holds, and every point agrees with at least `0` cuts. The bound
`1 * ((0 - 1 + 1) * 1 / (0 - 1 + 1))` is `1`, but `{0, 1}` has two elements. -/
example :
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ), ⊥ ≤ Q → Q.IsPrime →
      (1 : MvPolynomial (Fin 1) ℚ) ∉ Q → 0 < (affineHilbertPolynomial Q).natDegree →
      (fun _ ↦ 1 : ℕ → ℕ) ((affineHilbertPolynomial Q).natDegree - 1) ≤
        {i : Fin 0 | (Fin.elim0 i : MvPolynomial (Fin 1) ℚ) ∈ Q}.ncard →
      {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ Q ∧ aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0} ⊆ ∅) ∧
    ¬ ((({0, 1} : Finset (Fin 1 → ℚ)).card : ℚ) ≤
      affineDegree (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) *
        incidenceProduct (Fintype.card (Fin 0)) 0 1 (fun _ ↦ 1)
          (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree) := by
  refine ⟨fun Q _ _ _ _ h ↦ absurd h (by simp [Set.eq_empty_of_isEmpty]), ?_⟩
  have h01 : (0 : Fin 1 → ℚ) ≠ 1 := fun h ↦ zero_ne_one (congrFun h 0)
  rw [Finset.card_pair h01]
  simp [incidenceProduct_const]

/-- An ideal of `ℚ[x]` containing `x - a` has dimension `0`: its zero locus over `K` is at most
the point `a`, the image of the empty parametrization. -/
theorem natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem_line
    {J : Ideal (MvPolynomial (Fin 1) ℚ)} (a : ℚ) (h : X 0 - C a ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  have hreg : IsLeftRegular (Ideal.Quotient.mk J 1) := by
    rw [map_one]
    exact isRegular_one.left
  have hle := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range (τ := Empty) hreg
    (fun _ ↦ C a) fun (x : Fin 1 → K) hx _ ↦ ⟨isEmptyElim, ?_⟩
  · simpa using hle
  funext i
  rw [Subsingleton.elim i 0]
  simpa [sub_eq_zero] using (mem_zeroLocus_iff.mp hx) _ h

/-- An ideal of `ℚ[x, y]` containing `x - a` and `y - c` has dimension `0`. -/
theorem natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem
    {J : Ideal (MvPolynomial (Fin 2) ℚ)} (a c : ℚ) (h0 : X 0 - C a ∈ J) (h1 : X 1 - C c ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  have hreg : IsLeftRegular (Ideal.Quotient.mk J 1) := by
    rw [map_one]
    exact isRegular_one.left
  have hle := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range (τ := Empty) hreg
    (fun i ↦ C (![a, c] i)) fun (x : Fin 2 → K) hx _ ↦ ⟨isEmptyElim, ?_⟩
  · simpa using hle
  funext i
  fin_cases i
  · simpa [sub_eq_zero] using (mem_zeroLocus_iff.mp hx) _ h0
  · simpa [sub_eq_zero] using (mem_zeroLocus_iff.mp hx) _ h1

/-- An ideal of `ℚ[x, y]` containing `x` has dimension at most `1`: its zero locus over `K` lies
in the image of `t ↦ (0, t)`. -/
theorem natDegree_affineHilbertPolynomial_le_one_of_X_mem {J : Ideal (MvPolynomial (Fin 2) ℚ)}
    (h : X 0 ∈ J) : (affineHilbertPolynomial J).natDegree ≤ 1 := by
  have hreg : IsLeftRegular (Ideal.Quotient.mk J 1) := by
    rw [map_one]
    exact isRegular_one.left
  have hle := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range (τ := Fin 1)
    hreg ![0, X 0] fun (x : Fin 2 → K) hx _ ↦ ⟨fun _ ↦ x 1, ?_⟩
  · simpa using hle
  funext i
  fin_cases i
  · simpa using (mem_zeroLocus_iff.mp hx) _ h
  · simp

/-- On the line `x = 0` of the plane over `ℚ`, with points in `K`, at most two points agree with
one of the cuts `y` and `y - 1`. Take `Ps = {⊥}`, `highCuts = [x]`, `T = 1` and `D = 1`: a prime
containing `x` has dimension at most `1`, and a prime containing `x` and one cut has dimension
`0`. The bound is `1 * 1 ^ 2 * ((2 - 1 + 1) * 1 / (1 - 1 + 1)) = 2`, attained by the points
`(0, 0)` and `(0, 1)`. -/
example (S : Finset (Fin 2 → K))
    (hS : ∀ x ∈ S, aeval x (X 0 : MvPolynomial (Fin 2) ℚ) = 0)
    (hA : ∀ x ∈ S, 1 ≤ {i | aeval x (X 1 - C (![0, 1] i) : MvPolynomial (Fin 2) ℚ) = 0}.ncard) :
    (S.card : ℚ) ≤ 2 := by
  have h := card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily
    {⊥} (fun P hP ↦ by rw [Finset.mem_singleton.mp hP]; exact Ideal.isPrime_bot) 1 (d := 2)
    (fun P hP ↦ by rw [Finset.mem_singleton.mp hP, natDegree_affineHilbertPolynomial_bot]; simp)
    (V := 1) (by simp [affineDegree_bot]) [X 0] (B := 1) one_pos (by simp [totalDegree_X])
    (fun i : Fin 2 ↦ (X 1 - C (![0, 1] i) : MvPolynomial (Fin 2) ℚ)) (b := 1) (A := 1) (D := 1)
    one_pos (fun _ ↦ totalDegree_X1_sub_C_le _) (fun _ ↦ 1) (fun _ _ ↦ le_rfl)
    (∅ : Set (Fin 2 → K))
    (fun _ _ Q _ _ _ hhigh ↦
      natDegree_affineHilbertPolynomial_le_one_of_X_mem (hhigh _ (List.mem_singleton_self _)))
    (fun _ _ Q _ _ _ hhigh hd hT ↦ ?_) S
    (fun x hx ↦ ⟨⟨⊥, by simp, by simp⟩, by simp, by simpa using hS x hx, by simp⟩) hA
  · refine h.trans_eq ?_
    simp [incidenceProduct_const]
  · obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (Nat.one_le_iff_ne_zero.mp hT)
    have := natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem 0 (![0, 1] i)
      (by simpa using hhigh _ (List.mem_singleton_self _)) hi
    omega

/-- The hypothesis `0 < b` is needed in
`card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily`, where the
product is taken in a dimension `D` that may exceed the dimensions of the members. Take
`Ps = {(x)}` on the line over `ℚ`, no high-degree cuts, no cuts, `b = 0`, `A = 0`, `T = 0`,
`d = 0` and `D = 1`. The prime `(x)` and every ideal above it have dimension `0`, so the
dimension hypotheses hold and the excluded-set hypothesis is vacuous, and the point `0` lies on
`(x)`. The bound `affineDegree (x) * 1 ^ 0 * ((0 - 0 + 1) * 0 / (0 - 0 + 1))` is `0`. -/
example :
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}).IsPrime ∧
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ), Ideal.span {X 0} ≤ Q →
      (affineHilbertPolynomial Q).natDegree = 0) ∧
    (0 : Fin 1 → ℚ) ∈ zeroLocus ℚ (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) ∧
    ¬ ((({0} : Finset (Fin 1 → ℚ)).card : ℚ) ≤
      affineDegree (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) * ((1 : ℕ) : ℚ) ^ 0 *
        incidenceProduct (Fintype.card (Fin 0)) 0 0 (fun _ ↦ 0) 1) := by
  refine ⟨(Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime, fun Q hQ ↦
    natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem_line 0
      (by simpa using hQ (Ideal.subset_span rfl)), ?_, by simp [incidenceProduct]⟩
  rw [mem_zeroLocus_iff]
  intro f hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  simp

/-- The hypothesis `0 < B` is needed in
`card_le_incidenceProduct_of_agreement_off_excluded_of_iteratedRetainedCutFamily`. Take
`Ps = {⊥}` on the line over `ℚ`, of dimension `d = 1`, no high-degree cuts, `B = 0`, the single
cut `x` with `b = 1`, `A = 1`, `T = 1` and `D = 1`. A prime containing `x` has dimension `0`, so
the excluded-set hypothesis holds with `excluded = ∅`, and the point `0` agrees with the cut. The
bound `1 * 0 ^ 1 * ((1 - 1 + 1) * 1 / (1 - 1 + 1))` is `0`. -/
example :
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ), X 0 ∈ Q → (affineHilbertPolynomial Q).natDegree = 0) ∧
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree ≤ 1 ∧
    ¬ ((({0} : Finset (Fin 1 → ℚ)).card : ℚ) ≤
      affineDegree (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) * ((0 : ℕ) : ℚ) ^ 1 *
        incidenceProduct (Fintype.card (Fin 1)) 1 1 (fun _ ↦ 1) 1) := by
  refine ⟨fun Q hQ ↦ natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem_line 0
    (by simpa using hQ), by simp [natDegree_affineHilbertPolynomial_bot], by simp⟩

/-! ### Cuts indexed by `Fin n` -/

/-- The cardinality of a filter of `Finset.univ` is the `Set.ncard` of the corresponding set. -/
theorem card_filter_univ_eq_ncard {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = {i | p i}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext
  simp

open Classical in
/-- Fewer than `k` of the cuts lie in a positive-dimensional prime `P` with `s ∉ P` when any `k`
cuts determine a point of `V(P)` off `s = 0`, with the count written as a filter. -/
theorem card_filter_mem_lt_of_unique {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]
    {n k : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F)
    (hd : 0 < (affineHilbertPolynomial P).natDegree)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (Finset.univ.filter fun i ↦ cuts i ∈ P).card < k := by
  have := hP
  rw [card_filter_univ_eq_ncard]
  exact ncard_setOf_mem_lt_of_subsingleton hs cuts hd fun T hT x hx y hy ↦
    hunique T hT x y hx.1 hx.2.1 hy.1 hy.2.1 fun i hi ↦ ⟨hx.2.2 i hi, hy.2.2 i hi⟩

open Classical in
/-- The points of a finite subset of `V(P)` off `s = 0` that lie on `f = 0` are covered by the
retained components of the cut, with the counts written as filters. -/
theorem card_filter_cut_le_sum_retainedMinimalPrimes {F σ : Type*} [Field F] [Finite σ]
    (P : Ideal (MvPolynomial σ F)) (s f : MvPolynomial σ F) (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0) :
    (S.filter fun x ↦ aeval x f = 0).card ≤
      ∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s,
        (S.filter fun x ↦ x ∈ zeroLocus F Q).card := by
  have h := ncard_inter_cut_le_sum_retainedMinimalPrimes P s f S hS
  simp only [← Set.ncard_coe_finset, Finset.coe_filter]
  exact h

open Classical in
/-- The incidence bound under uniqueness for cuts indexed by `Fin n`, with the agreement counts
written as filters. The hypotheses `0 < b`, `0 < k`, `A ≤ n` and `s ∉ P` are not used. -/
theorem card_le_of_agreement_of_unique_fin {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (_hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (_hb : 0 < b) (_hk : 0 < k) (hkA : k ≤ A) (_hAn : A ≤ n)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter fun i ↦ aeval x (cuts i) = 0).card)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ affineDegree P *
      (((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree := by
  have := hP
  have h := card_le_of_agreement_of_subsingleton s cuts hdeg hkA
    (fun T hT x hx y hy ↦
      hunique T hT x y hx.1 hx.2.1 hy.1 hy.2.1 fun i hi ↦ ⟨hx.2.2 i hi, hy.2.2 i hi⟩)
    S hS fun x hx ↦ by rw [← card_filter_univ_eq_ncard]; exact hA x hx
  rwa [Fintype.card_fin] at h

open Classical in
/-- The incidence bound outside an excluded set for cuts indexed by `Fin n`, with the principal
open subsets and the counts written out. The hypotheses `0 < b` and `s ∉ P` are not used. -/
theorem card_le_of_agreement_off_excluded_fin {F σ : Type*} [Field F] [Finite σ]
    {n A L b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (_hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (_hb : 0 < b) (hLA : L ≤ A)
    (excluded : Set (σ → F))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ (Finset.univ.filter fun i ↦ cuts i ∈ Q).card →
      {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, (x ∈ zeroLocus F P ∧ aeval x s ≠ 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter fun i ↦ aeval x (cuts i) = 0).card) :
    (S.card : ℚ) ≤ affineDegree P *
      (((n * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial P).natDegree := by
  have := hP
  have h := card_le_of_agreement_off_excluded s cuts hdeg hLA excluded
    (fun Q hPQ hQ hsQ hd hL ↦ hterminal Q hPQ hQ hsQ hd (by rwa [card_filter_univ_eq_ncard]))
    S (fun x hx ↦ ⟨(hS x hx).1.1, (hS x hx).1.2, (hS x hx).2⟩)
    fun x hx ↦ by rw [← card_filter_univ_eq_ncard]; exact hA x hx
  rwa [Fintype.card_fin] at h

open Classical in
/-- The incidence bound on a cut hypersurface for cuts indexed by `Fin n`, with the principal open
subsets and the counts written out. The hypotheses `0 < L` and `A ≤ n` give `A - L + 1 ≤ n`; the
hypothesis `0 < B` is not used. -/
theorem card_le_of_agreement_off_excluded_of_hypersurface_fin {F σ : Type*} [Field F] [Finite σ]
    (g s : MvPolynomial σ F) (hg : g ≠ 0) {v B n A L : ℕ}
    (hv : g.totalDegree ≤ v) (_hB : 0 < B)
    (highCuts : List (MvPolynomial σ F))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B)
    (cuts : Fin n → MvPolynomial σ F) (hcuts : ∀ i, (cuts i).totalDegree ≤ B)
    (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hterminal : ∀ P : Ideal (MvPolynomial σ F),
      P.IsPrime → s ∉ P → g ∈ P → (∀ f ∈ highCuts, f ∈ P) →
      0 < (affineHilbertPolynomial P).natDegree →
      L ≤ (Finset.univ.filter fun i ↦ cuts i ∈ P).card →
      {x | x ∈ zeroLocus F P ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter fun i ↦ aeval x (cuts i) = 0).card) :
    (S.card : ℚ) ≤ (v : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (Nat.card σ - 1) := by
  have h := card_le_of_agreement_off_excluded_of_hypersurface hg s hv highCuts hhigh cuts hcuts
    hLA (by rw [Fintype.card_fin]; omega) excluded
    (fun J hJ hsJ hgJ hhJ hd hLJ ↦
      hterminal J hJ hsJ hgJ hhJ hd (by rwa [card_filter_univ_eq_ncard]))
    S hS fun x hx ↦ by rw [← card_filter_univ_eq_ncard]; exact hA x hx
  rwa [Fintype.card_fin] at h

end AgreementIncidenceTest
