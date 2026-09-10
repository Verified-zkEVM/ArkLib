/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.ZeroLocus.Finite
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Presentation
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthRescaling

/-! # Finite principal opens in affine prime varieties -/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]

/-- The rational points of the principal open of `V(P)` cut out by `s`. -/
def principalOpenZeroLocus (P : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) :
    Set (σ → F) := {x | x ∈ zeroLocus F P ∧ aeval x s ≠ 0}

omit [IsAlgClosed F] [Finite σ] in
private theorem awayPresentationIdeal_isPrime
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P) :
    (awayPresentationIdeal P s).IsPrime := by
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain (Localization.Away (Ideal.Quotient.mk P s)) :=
    Localization.Away.isDomain hs0
  exact RingHom.ker_isPrime (awayPresentationHom P s).toRingHom

private def restrictAwayPoint (z : Option σ → F) : σ → F := fun i ↦ z (some i)

omit [IsAlgClosed F] [Finite σ] in
private theorem awayRelation_mem (P : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) :
    MvPolynomial.X none * MvPolynomial.rename some s - 1 ∈ awayPresentationIdeal P s := by
  change awayPresentationHom P s
    (MvPolynomial.X none * MvPolynomial.rename some s - 1) = 0
  rw [map_sub, map_mul, awayPresentationHom_rename_some]
  simp only [awayPresentationHom, MvPolynomial.eval₂AlgHom_X, map_one]
  rw [mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

omit [IsAlgClosed F] [Finite σ] in
private theorem restrictAwayPoint_mem_zeroLocus
    (P : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F)
    (z : zeroLocus F (awayPresentationIdeal P s)) :
    restrictAwayPoint z.val ∈ zeroLocus F P := by
  intro p hp
  have hk : MvPolynomial.rename some p ∈ awayPresentationIdeal P s := by
    change awayPresentationHom P s (MvPolynomial.rename some p) = 0
    rw [awayPresentationHom_rename_some]
    rw [show Ideal.Quotient.mk P p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hz := z.property (MvPolynomial.rename some p) hk
  rw [MvPolynomial.aeval_rename] at hz
  change aeval (z.val ∘ some) p = 0
  exact hz

omit [IsAlgClosed F] [Finite σ] in
private theorem restrictAwayPoint_eval_ne_zero
    (P : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F)
    (z : zeroLocus F (awayPresentationIdeal P s)) :
    aeval (restrictAwayPoint z.val) s ≠ 0 := by
  have hz := z.property
    (MvPolynomial.X none * MvPolynomial.rename some s - 1) (awayRelation_mem P s)
  simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_rename,
    map_one] at hz
  change z.val none * aeval (restrictAwayPoint z.val) s - 1 = 0 at hz
  intro hs0
  rw [hs0, mul_zero, zero_sub] at hz
  exact one_ne_zero (neg_eq_zero.mp hz)

omit [IsAlgClosed F] [Finite σ] in
private theorem restrictAwayPoint_injective (P : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) :
    Function.Injective (fun z : zeroLocus F (awayPresentationIdeal P s) ↦
      restrictAwayPoint z.val) := by
  intro z w hzw
  apply Subtype.ext
  funext i
  cases i with
  | some i => exact congrFun hzw i
  | none =>
      have hz := z.property
        (MvPolynomial.X none * MvPolynomial.rename some s - 1) (awayRelation_mem P s)
      have hw := w.property
        (MvPolynomial.X none * MvPolynomial.rename some s - 1) (awayRelation_mem P s)
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_rename,
        map_one] at hz hw
      change z.val none * aeval (restrictAwayPoint z.val) s - 1 = 0 at hz
      change w.val none * aeval (restrictAwayPoint w.val) s - 1 = 0 at hw
      have heval : aeval (restrictAwayPoint z.val) s =
          aeval (restrictAwayPoint w.val) s := congrArg (fun x ↦ aeval x s) hzw
      rw [heval] at hz
      exact mul_right_cancel₀ (restrictAwayPoint_eval_ne_zero P s w)
        ((sub_eq_zero.mp hz).trans (sub_eq_zero.mp hw).symm)

/-- If a principal open in an affine prime variety has only finitely many rational
points over an algebraically closed field, the prime quotient has Hilbert-polynomial
degree zero. -/
theorem hilbertPolynomial_natDegree_zero_of_finite_principalOpen
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (hfinite : (principalOpenZeroLocus P s).Finite) :
    (hilbertPolynomial P).natDegree = 0 := by
  let K := awayPresentationIdeal P s
  have hKprime : K.IsPrime := awayPresentationIdeal_isPrime hP hs
  let φ : zeroLocus F K → principalOpenZeroLocus P s := fun z ↦
    ⟨restrictAwayPoint z.val,
      restrictAwayPoint_mem_zeroLocus P s z, restrictAwayPoint_eval_ne_zero P s z⟩
  have hφ : Function.Injective φ := by
    intro z w hzw
    apply restrictAwayPoint_injective P s
    exact congrArg Subtype.val hzw
  have hKfinite : (zeroLocus F K).Finite := by
    let _ : Fintype (principalOpenZeroLocus P s) := hfinite.fintype
    let _ : Finite (zeroLocus F K) := Finite.of_injective φ hφ
    exact Set.toFinite _
  have hKdeg : (hilbertPolynomial K).natDegree = 0 :=
    (finite_zeroLocus_iff_hilbertPolynomial_natDegree_zero K hKprime.isRadical).mp hKfinite
  have hdeg : (hilbertPolynomial P).natDegree ≤ (hilbertPolynomial K).natDegree := by
    apply natDegree_le_of_eventually_eval_nat_le_rescaled
      (hilbertPolynomial_ne_zero hP.ne_top) (c := 2) (by omega)
    · filter_upwards [hilbertPolynomial_eventually_eval P] with N hN
      rw [hN]
      positivity
    · obtain ⟨TP, hPev⟩ := hilbertPolynomial_eventually P
      obtain ⟨TK, hKev⟩ := hilbertPolynomial_eventually K
      filter_upwards [Filter.eventually_ge_atTop (max TP TK)] with N hN
      rw [hPev N ((le_max_left TP TK).trans hN),
        hKev (2 * N) ((le_max_right TP TK).trans hN |>.trans (by omega))]
      exact_mod_cast hilbertFunction_le_awayPresentation_hilbertFunction_two_mul hP hs N
  rw [hKdeg] at hdeg
  exact Nat.eq_zero_of_le_zero hdeg

end AffineHilbert
