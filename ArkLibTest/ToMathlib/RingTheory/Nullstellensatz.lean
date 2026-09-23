/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedBidegreeIncidence
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation

/-!
# Acceptance client for retained minimal primes of a zero locus

The examples work in `MvPolynomial (Fin 2) ℚ` with the ideal `I = (X 0 * X 1)`, whose zero locus is
the union of the two coordinate axes. For `s = X 0` the retained family is computed exactly: it is
the single prime `lineIdeal`, the kernel of the substitution `X 1 ↦ 0`, which is the ideal of the
axis `X 1 = 0`. The other axis lies inside `{X 0 = 0}` and is discarded.

The cover theorem is then applied with rational points, over the field `ℚ` itself, which is not
algebraically closed. The zero `(0, 1)` of `I` shows that the hypothesis `aeval x s ≠ 0` cannot be
dropped, and the point `(1, 0)` with the cut `f = X 0 - 2` shows that a regular point off the cut
lies on no retained component of the cut.
-/

open MvPolynomial

namespace RetainedMinimalPrimesCanary

/-- Substitution of `0` for the second variable. -/
private noncomputable abbrev killSecond : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  aeval ![X 0, 0]

/-- The ideal of the axis `X 1 = 0`, presented as the kernel of `killSecond`. -/
private noncomputable abbrev lineIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  RingHom.ker killSecond

/-- The ideal of the union of the two coordinate axes. -/
private noncomputable abbrev axesIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {X 0 * X 1}

private instance : lineIdeal.IsPrime := RingHom.ker_isPrime _

/-- Every polynomial agrees with its substitution `X 1 ↦ 0` modulo `X 1`. -/
private theorem sub_killSecond_mem (p : MvPolynomial (Fin 2) ℚ) :
    p - killSecond p ∈ Ideal.span {(X 1 : MvPolynomial (Fin 2) ℚ)} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    have hX : X n - killSecond (X n) ∈ Ideal.span {(X 1 : MvPolynomial (Fin 2) ℚ)} := by
      fin_cases n
      · simp
      · simp
    have hsplit : p * X n - killSecond (p * X n) =
        (p - killSecond p) * X n + killSecond p * (X n - killSecond (X n)) := by
      rw [map_mul]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hX)

private theorem X0_notMem_lineIdeal : (X 0 : MvPolynomial (Fin 2) ℚ) ∉ lineIdeal := by
  simp [RingHom.mem_ker]

private theorem X1_mem_lineIdeal : (X 1 : MvPolynomial (Fin 2) ℚ) ∈ lineIdeal := by
  simp [RingHom.mem_ker]

/-- A prime containing `X 0 * X 1` but not `X 0` contains all of `lineIdeal`. -/
private theorem lineIdeal_le {Q : Ideal (MvPolynomial (Fin 2) ℚ)} [Q.IsPrime]
    (hIQ : axesIdeal ≤ Q) (hX0 : (X 0 : MvPolynomial (Fin 2) ℚ) ∉ Q) : lineIdeal ≤ Q := by
  have hX1 : (X 1 : MvPolynomial (Fin 2) ℚ) ∈ Q :=
    ((‹Q.IsPrime›.mem_or_mem (hIQ (Ideal.subset_span (Set.mem_singleton _)))).resolve_left hX0)
  intro p hp
  have hdiff := sub_killSecond_mem p
  rw [RingHom.mem_ker.mp hp, sub_zero] at hdiff
  exact (Ideal.span_singleton_le_iff_mem Q).mpr hX1 hdiff

/-- The minimal primes of the two axes retained by `s = X 0` are exactly the ideal of the axis
`X 1 = 0`. -/
private theorem retainedMinimalPrimes_axes_X0 :
    axesIdeal.retainedMinimalPrimes (X 0) = {lineIdeal} := by
  have hIline : axesIdeal ≤ lineIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (by simp [RingHom.mem_ker])
  ext P
  rw [Ideal.mem_retainedMinimalPrimes, Finset.mem_singleton]
  constructor
  · rintro ⟨hP, hX0⟩
    have : P.IsPrime := hP.isPrime
    have hle := lineIdeal_le hP.le hX0
    exact le_antisymm (hP.2 ⟨inferInstance, hIline⟩ hle) hle
  · rintro rfl
    refine ⟨⟨⟨inferInstance, hIline⟩, fun Q hQ hQle ↦ ?_⟩, X0_notMem_lineIdeal⟩
    have : Q.IsPrime := hQ.1
    exact lineIdeal_le hQ.2 fun hX0 ↦ X0_notMem_lineIdeal (hQle hX0)

/-- The cover theorem with a rational point: `(1, 0)` is a zero of `X 0 * X 1` where `X 0` does not
vanish, so it lies on the retained component `lineIdeal`. The field `ℚ` is not algebraically
closed. -/
example : ![(1 : ℚ), 0] ∈ zeroLocus ℚ lineIdeal := by
  have hx : ![(1 : ℚ), 0] ∈ zeroLocus ℚ axesIdeal := by
    simp [axesIdeal, zeroLocus_span]
  obtain ⟨P, hP, hxP⟩ :=
    exists_retainedMinimalPrime_of_mem_zeroLocus axesIdeal (X 0) ![(1 : ℚ), 0] hx (by simp)
  rw [retainedMinimalPrimes_axes_X0, Finset.mem_singleton] at hP
  exact hP ▸ hxP

/-- The regularity hypothesis cannot be dropped: `(0, 1)` is a zero of `X 0 * X 1`, but it lies on
no minimal prime retained by `X 0`. -/
example :
    ![(0 : ℚ), 1] ∈ zeroLocus ℚ axesIdeal ∧
      ¬∃ P ∈ axesIdeal.retainedMinimalPrimes (X 0), ![(0 : ℚ), 1] ∈ zeroLocus ℚ P := by
  refine ⟨by simp [axesIdeal, zeroLocus_span], ?_⟩
  rintro ⟨P, hP, hxP⟩
  rw [retainedMinimalPrimes_axes_X0, Finset.mem_singleton] at hP
  subst hP
  simpa using hxP _ X1_mem_lineIdeal

/-- A point off the cut: `(1, 0)` is a regular zero of `X 0 * X 1`, but `X 0 - 2` does not vanish
there, so no retained component of the cut `(X 0 * X 1, X 0 - 2)` contains it. -/
example :
    ¬∃ P ∈ (axesIdeal ⊔ Ideal.span {X 0 - C 2}).retainedMinimalPrimes (X 0),
      ![(1 : ℚ), 0] ∈ zeroLocus ℚ P ∧ aeval ![(1 : ℚ), 0] (X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  rw [← mem_zeroLocus_and_cut_iff_retained]
  rintro ⟨-, hf, -⟩
  norm_num at hf

/-- A point on the cut: `(2, 0)` satisfies `X 0 * X 1 = 0`, `X 0 - 2 = 0` and `X 0 ≠ 0`, so a
retained component of the cut contains it. -/
example :
    ∃ P ∈ (axesIdeal ⊔ Ideal.span {X 0 - C 2}).retainedMinimalPrimes (X 0),
      ![(2 : ℚ), 0] ∈ zeroLocus ℚ P ∧ aeval ![(2 : ℚ), 0] (X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  rw [← mem_zeroLocus_and_cut_iff_retained]
  refine ⟨by simp [axesIdeal, zeroLocus_span], by simp, by simp⟩

/-- The retained family is empty when `s` lies in the radical: `X 0 * X 1` retains nothing. -/
example : axesIdeal.retainedMinimalPrimes (X 0 * X 1) = ∅ :=
  Ideal.retainedMinimalPrimes_eq_empty_iff.mpr
    (Ideal.le_radical (Ideal.subset_span (Set.mem_singleton _)))

end RetainedMinimalPrimesCanary

namespace CappedBidegreeIncidenceCanary

open MvPolynomial

private theorem X_none_mem_restrictCappedBidegree :
    (X none : MvPolynomial (Option (Fin 2)) ℚ) ∈
      restrictCappedBidegree (Fin 2) ℚ 1 1 1 1 := by
  rw [mem_restrictCappedBidegree, support_X]
  simp [Finsupp.some_single_none]

private theorem span_X_none_ne_top :
    Ideal.span {(X none : MvPolynomial (Option (Fin 2)) ℚ)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro h
  simpa using h.map constantCoeff

private theorem natDegree_zero_of_all_variables_mem
    {J : Ideal (MvPolynomial (Option (Fin 2)) ℚ)}
    (hvars : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  let v : Option (Fin 2) ↪ Option (Fin 2) := ⟨id, fun _ _ h ↦ h⟩
  have h := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (I := J) v (1 : Matrix (Option (Fin 2)) (Option (Fin 2)) ℚ)
    (by simp)
    (fun i ↦ X i) hvars (fun i ↦ by simp [v, Matrix.one_apply])
  exact Nat.le_zero.mp (by simpa using h)

private theorem X_mem_restrictCappedBidegree (i : Option (Fin 2)) :
    (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈
    restrictCappedBidegree (Fin 2) ℚ 1 1 1 1 := by
  rw [mem_restrictCappedBidegree, support_X]
  cases i with
  | none => simp [Finsupp.some_single_none]
  | some i => fin_cases i <;> simp [Finsupp.some_single_some]

/-- A rational point on `X none = 0` satisfies the hybrid bound under three coordinate cuts. -/
example :
    (({fun _ : Option (Fin 2) => (0 : ℚ)} : Finset (Option (Fin 2) → ℚ)).card : ℚ) ≤
      (cappedBidegreeMixedVolume 1 1 1 1 1 1 : ℕ) *
        (((3 - 3 + 1 : ℕ) : ℚ) / ((3 - 3 + 1 : ℕ) : ℚ)) *
          (((3 - 0 + 1 : ℕ) : ℚ) / ((3 - 0 + 1 : ℕ) : ℚ)) := by
  have h := MvPolynomial.cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two
    (a := 1) (b := 1) (c := 1) (h := 1) (j := 1) (r := 1) (n := 3)
    (A := 3) (L := 3) (k := 0)
    (ha := by norm_num) (hb := by norm_num) (hc := by norm_num)
    (hLA := by norm_num) (hkA := by norm_num)
    (g := X none) (s := 1)
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_restrictCappedBidegree)
    (hgAB := X_none_mem_restrictCappedBidegree)
    (hs := by
      rw [mem_restrictCappedBidegree]
      simp)
    (highCuts := [X none, X (some 0), X (some 1)])
    (hhigh := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> exact X_mem_restrictCappedBidegree _)
    (cuts := ![X none, X (some 0), X (some 1)])
    (hcuts := by
      intro i
      fin_cases i <;> exact X_mem_restrictCappedBidegree _)
    (excluded := ∅)
    (hdimension := by
      intro J hJ hsJ hX hhigh hd
      have hvars : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J := by
        intro i
        cases i with
        | none => exact hhigh _ (by simp)
        | some i => fin_cases i <;> exact hhigh _ (by simp)
      rw [natDegree_zero_of_all_variables_mem hvars] at hd
      omega)
    (hterminal := by
      intro J hJ hsJ hX hhigh hd hL
      have hvars : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J := by
        intro i
        cases i with
        | none => exact hhigh _ (by simp)
        | some i => fin_cases i <;> exact hhigh _ (by simp)
      rw [natDegree_zero_of_all_variables_mem hvars] at hd
      omega)
    (S := {fun _ : Option (Fin 2) => (0 : ℚ)})
    (hS := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      simp)
    (hA := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      have hcuts : {i : Fin 3 | aeval (fun _ : Option (Fin 2) ↦ (0 : ℚ))
          ((![X none, X (some 0), X (some 1)] : Fin 3 →
            MvPolynomial (Option (Fin 2)) ℚ) i) = 0} = Set.univ := by
        ext i
        fin_cases i <;> simp
      rw [hcuts]
      simp)
  have hvolume : cappedBidegreeMixedVolume 1 1 1 1 1 1 = 3 := by
    rw [cappedBidegreeMixedVolume_eq (by norm_num)]
  norm_num [hvolume] at h ⊢

end CappedBidegreeIncidenceCanary
