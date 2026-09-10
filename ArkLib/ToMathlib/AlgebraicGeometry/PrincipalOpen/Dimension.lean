/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteAlgebraGrowth
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Presentation

/-!
# Dimension comparison for principal localizations

This module records the algebra direction needed when source coordinates are reconstructed only
after inverting a separant.  A surjection from a polynomial algebra onto the localized coordinate
ring bounds the dimension of the original prime by the number of source variables.  The inverse
of the localized element is accounted for by the explicit away presentation; it is not counted as
a freely adjoined generator.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]

/-- Passing from a prime affine coordinate ring to a nonempty principal localization preserves
enough Hilbert growth to bound the original dimension by that of the explicit away presentation.
-/
theorem hilbertPolynomial_natDegree_le_awayPresentation
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P) :
    (hilbertPolynomial P).natDegree ≤
      (hilbertPolynomial (awayPresentationIdeal P s)).natDegree := by
  apply natDegree_le_of_eventually_eval_nat_le_rescaled
    (hilbertPolynomial_ne_zero hP.ne_top) (c := 2) (by omega)
  · filter_upwards [hilbertPolynomial_eventually_eval P] with N hN
    rw [hN]
    positivity
  · obtain ⟨TP, hPev⟩ := hilbertPolynomial_eventually P
    obtain ⟨TK, hKev⟩ := hilbertPolynomial_eventually (awayPresentationIdeal P s)
    filter_upwards [Filter.eventually_ge_atTop (max TP TK)] with N hN
    rw [hPev N ((le_max_left TP TK).trans hN),
      hKev (2 * N) ((le_max_right TP TK).trans hN |>.trans (by omega))]
    exact_mod_cast hilbertFunction_le_awayPresentation_hilbertFunction_two_mul hP hs N

/-- The explicit away presentation has dimension at most the original prime quotient.  Its extra
inverse variable is constrained by the localization relation and therefore contributes no free
dimension. -/
theorem awayPresentation_hilbertPolynomial_natDegree_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P) :
    (hilbertPolynomial (awayPresentationIdeal P s)).natDegree ≤
      (hilbertPolynomial P).natDegree := by
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain (Localization.Away (Ideal.Quotient.mk P s)) :=
    Localization.Away.isDomain hs0
  have haway : awayPresentationIdeal P s ≠ ⊤ :=
    RingHom.ker_ne_top (awayPresentationHom P s).toRingHom
  let c := 1 + s.totalDegree
  have hc : 0 < c := by simp [c]
  apply natDegree_le_of_eventually_eval_nat_le_rescaled
    (hilbertPolynomial_ne_zero haway) hc
  · filter_upwards [hilbertPolynomial_eventually_eval (awayPresentationIdeal P s)] with N hN
    rw [hN]
    positivity
  · obtain ⟨TA, hAev⟩ := hilbertPolynomial_eventually (awayPresentationIdeal P s)
    obtain ⟨TP, hPev⟩ := hilbertPolynomial_eventually P
    filter_upwards [Filter.eventually_ge_atTop (max TA TP)] with N hN
    rw [hAev N ((le_max_left TA TP).trans hN),
      hPev (c * N) ((le_max_right TA TP).trans hN |>.trans
        (Nat.le_mul_of_pos_left N hc))]
    have hcN : c * N = N + N * s.totalDegree := by
      dsimp only [c]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm s.totalDegree N]
    rw [hcN]
    exact_mod_cast awayPresentation_hilbertFunction_le_hilbertFunction_rescaled hP hs N

/-- A surjection from one nonempty principal localization to another cannot increase the
dimension of the underlying prime.  Both inverse elements are represented explicitly before
applying the affine-algebra surjection comparison. -/
theorem hilbertPolynomial_natDegree_le_of_surjective_away_algHom
    {J : Ideal (MvPolynomial τ F)} (hJ : J.IsPrime)
    {t : MvPolynomial τ F} (ht : t ∉ J)
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (g : Localization.Away (Ideal.Quotient.mk J t) →ₐ[F]
      Localization.Away (Ideal.Quotient.mk P s))
    (hg : Function.Surjective g) :
    (hilbertPolynomial P).natDegree ≤ (hilbertPolynomial J).natDegree := by
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain (Localization.Away (Ideal.Quotient.mk P s)) :=
    Localization.Away.isDomain hs0
  let qg :
      (MvPolynomial (Option τ) F ⧸ awayPresentationIdeal J t) →ₐ[F]
        (MvPolynomial (Option σ) F ⧸ awayPresentationIdeal P s) :=
    (awayPresentationEquiv P s).symm.toAlgHom.comp
      (g.comp (awayPresentationEquiv J t).toAlgHom)
  have hqg : Function.Surjective qg :=
    (awayPresentationEquiv P s).symm.surjective.comp
      (hg.comp (awayPresentationEquiv J t).surjective)
  have hawayP : awayPresentationIdeal P s ≠ ⊤ :=
    RingHom.ker_ne_top (awayPresentationHom P s).toRingHom
  have hlocal :
      (hilbertPolynomial (awayPresentationIdeal P s)).natDegree ≤
        (hilbertPolynomial (awayPresentationIdeal J t)).natDegree :=
    hilbertPolynomial_natDegree_le_of_surjective_algHom qg hqg hawayP
  exact (hilbertPolynomial_natDegree_le_awayPresentation hP hs).trans
    (hlocal.trans (awayPresentation_hilbertPolynomial_natDegree_le hJ ht))

/-- If a polynomial algebra on `τ` surjects onto the localization of a prime affine coordinate
ring, then the original prime has dimension at most `|τ|`.

The quotient by the kernel of `g` is isomorphic to the localized ring.  Comparing that quotient
with the explicit away presentation gives the correct direction: the away-presentation dimension,
and hence the original dimension, is at most the dimension of the polynomial source. -/
theorem hilbertPolynomial_natDegree_le_of_surjective_algHom_to_away
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (g : MvPolynomial τ F →ₐ[F] Localization.Away (Ideal.Quotient.mk P s))
    (hg : Function.Surjective g) :
    (hilbertPolynomial P).natDegree ≤ Nat.card τ := by
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain (Localization.Away (Ideal.Quotient.mk P s)) :=
    Localization.Away.isDomain hs0
  let e :
      (MvPolynomial (Option σ) F ⧸ awayPresentationIdeal P s) ≃ₐ[F]
        (MvPolynomial τ F ⧸ RingHom.ker g) :=
    (awayPresentationEquiv P s).trans (Ideal.quotientKerAlgEquivOfSurjective hg).symm
  have hpresentation :
      (hilbertPolynomial (awayPresentationIdeal P s)).natDegree ≤
        (hilbertPolynomial (RingHom.ker g)).natDegree :=
    hilbertPolynomial_natDegree_le_of_injective_algHom e.toAlgHom e.injective
      (RingHom.ker_ne_top (awayPresentationHom P s).toRingHom)
  exact (hilbertPolynomial_natDegree_le_awayPresentation hP hs).trans
    (hpresentation.trans (hilbertPolynomial_natDegree_le (RingHom.ker g)))

/-- Generator form of `hilbertPolynomial_natDegree_le_of_surjective_algHom_to_away`.
It is often easier for an application to show directly that the challenge and the surviving
coefficient coordinates generate the localized source algebra. -/
theorem hilbertPolynomial_natDegree_le_of_adjoin_eq_top_away
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (x : τ → Localization.Away (Ideal.Quotient.mk P s))
    (hx : Algebra.adjoin F (Set.range x) = ⊤) :
    (hilbertPolynomial P).natDegree ≤ Nat.card τ := by
  apply hilbertPolynomial_natDegree_le_of_surjective_algHom_to_away hP hs
    (MvPolynomial.aeval x)
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hx

end AffineHilbert
