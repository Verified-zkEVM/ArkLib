/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finite prime covers of principal-open affine cuts

Minimal primes give a finite cover of an affine zero locus. Discarding primes containing
the denominator preserves every point of its principal open. Proper cuts strictly contain
the parent prime and decrease the actual quotient Krull dimension by at least one.
No multiplicity or geometric degree law is assumed here.
-/

@[expose] public section

noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Minimal primes that meet the principal open defined by `s`. -/
def retainedMinimalPrimes (I : Ideal R) (s : R) : Finset (Ideal R) := by
  classical
  exact (I.finite_minimalPrimes_of_isNoetherianRing R).toFinset.filter (fun P ↦ s ∉ P)

/-- Retaining a minimal prime records precisely its minimality and denominator condition. -/
theorem mem_retainedMinimalPrimes (I P : Ideal R) (s : R) :
    P ∈ I.retainedMinimalPrimes s ↔ P ∈ I.minimalPrimes ∧ s ∉ P := by
  classical
  simp [retainedMinimalPrimes]

omit [IsNoetherianRing R] in
/-- A prime below a strictly larger ideal loses at least one quotient dimension. -/
theorem ringKrullDim_quotient_succ_le_of_lt {P J : Ideal R} [P.IsPrime] (hPJ : P < J) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) := by
  obtain ⟨f, hfJ, hfP⟩ := SetLike.exists_of_lt hPJ
  apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPJ.le)
    (Ideal.Quotient.factor_surjective hPJ.le) (r := Ideal.Quotient.mk P f)
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hf ↦ hfP (Ideal.Quotient.eq_zero_iff_mem.mp hf)
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr hfJ

omit [IsNoetherianRing R] in
/-- Every minimal-prime child of a proper principal cut strictly contains its parent. -/
theorem lt_of_mem_minimalPrimes_sup_span {P J : Ideal R} {f : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : P < J := by
  apply lt_of_le_of_ne (le_sup_left.trans hJ.le)
  intro heq
  apply hf
  rw [heq]
  exact hJ.le ((show Ideal.span {f} ≤ P ⊔ Ideal.span {f} from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton f)))

/-- Every retained child of a proper prime cut has strictly smaller actual quotient dimension. -/
theorem retained_cut_krullDim_succ_le {P J : Ideal R} [P.IsPrime] {f s : R}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ P) := by
  exact ringKrullDim_quotient_succ_le_of_lt
    (lt_of_mem_minimalPrimes_sup_span hf ((mem_retainedMinimalPrimes _ _ _).mp hJ).1)

end Ideal

namespace MvPolynomial

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E] [Finite σ]

/-- Every regular zero lies over a retained minimal prime, over any coefficient-field extension. -/
theorem exists_retainedMinimalPrime_of_mem_zeroLocus
    (I : Ideal (MvPolynomial σ F)) (S : MvPolynomial σ F) (x : σ → E)
    (hx : x ∈ zeroLocus E I) (hS : aeval x S ≠ 0) :
    ∃ P ∈ I.retainedMinimalPrimes S, x ∈ zeroLocus E P := by
  let K : Ideal (MvPolynomial σ F) := RingHom.ker (aeval x).toRingHom
  have : K.IsPrime := RingHom.ker_isPrime (aeval x).toRingHom
  have hIK : I ≤ K := fun p hp ↦ hx p hp
  obtain ⟨P, hP, hPK⟩ := I.exists_minimalPrimes_le hIK
  refine ⟨P, (Ideal.mem_retainedMinimalPrimes _ _ _).mpr ⟨hP, ?_⟩, ?_⟩
  · intro hSP
    exact hS (hPK hSP)
  · intro p hp
    exact hPK hp

/-- Finite retained minimal primes cover exactly the regular part of an affine zero locus. -/
theorem mem_zeroLocus_and_eval_ne_zero_iff_retained
    (I : Ideal (MvPolynomial σ F)) (S : MvPolynomial σ F) (x : σ → E) :
    (x ∈ zeroLocus E I ∧ aeval x S ≠ 0) ↔
      ∃ P ∈ I.retainedMinimalPrimes S, x ∈ zeroLocus E P ∧ aeval x S ≠ 0 := by
  constructor
  · rintro ⟨hx, hS⟩
    obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus I S x hx hS
    exact ⟨P, hP, hxP, hS⟩
  · rintro ⟨P, hP, hx, hS⟩
    exact ⟨zeroLocus_anti_mono ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.le hx, hS⟩

/-- At a regular point, adding a polynomial equation is exactly the retained-child cover
of the actual ideal sum. Components on the denominator boundary contribute no points. -/
theorem mem_zeroLocus_and_cut_iff_retained
    (I : Ideal (MvPolynomial σ F)) (S f : MvPolynomial σ F) (x : σ → E) :
    (x ∈ zeroLocus E I ∧ aeval x f = 0 ∧ aeval x S ≠ 0) ↔
      ∃ P ∈ (I ⊔ Ideal.span {f}).retainedMinimalPrimes S,
        x ∈ zeroLocus E P ∧ aeval x S ≠ 0 := by
  rw [← mem_zeroLocus_and_eval_ne_zero_iff_retained]
  have heq : x ∈ zeroLocus E (I ⊔ Ideal.span {f}) ↔
      x ∈ zeroLocus E I ∧ aeval x f = 0 := by
    change I ⊔ Ideal.span {f} ≤ RingHom.ker (aeval x).toRingHom ↔ _
    rw [sup_le_iff, Ideal.span_singleton_le_iff_mem]
    rfl
  rw [heq]
  tauto

end MvPolynomial

end
