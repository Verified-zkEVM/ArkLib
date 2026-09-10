/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Cuts
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Relative codimension of principal-cut components

Krull's principal ideal theorem applies after quotienting by the parent prime.  Thus every
minimal-prime component of a proper principal cut has relative height exactly one.  This is the
unconditional codimension-one statement available without a catenary or equidimensional
dimension formula.
-/

@[expose] public section

noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- A strict child of a prime maps to a nonzero ideal in the parent quotient. -/
theorem map_quotient_ne_bot_of_lt {P J : Ideal R} (hP : P.IsPrime) (hPJ : P < J) :
    J.map (Ideal.Quotient.mk P) ≠ ⊥ := by
  let _ : P.IsPrime := hP
  intro hmap
  apply hPJ.2
  intro x hx
  have hxmap : Ideal.Quotient.mk P x ∈ J.map (Ideal.Quotient.mk P) :=
    Ideal.mem_map_of_mem _ hx
  rw [hmap] at hxmap
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hxmap)

/-- Every minimal-prime component of a proper principal cut has relative height exactly one
inside the parent domain quotient. -/
theorem map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span
    {P J : Ideal R} (hP : P.IsPrime) {f : R} (hf : f ∉ P)
    (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (J.map (Ideal.Quotient.mk P)).height = 1 := by
  let _ : P.IsPrime := hP
  let _ : J.IsPrime := hJ.isPrime
  let _ : (J.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact (le_sup_left.trans hJ.le))
  apply le_antisymm
  · exact Ideal.map_height_le_one_of_mem_minimalPrimes hJ
  · rw [Order.one_le_iff_ne_zero]
    intro hheight
    apply map_quotient_ne_bot_of_lt hP
      (Ideal.lt_of_mem_minimalPrimes_sup_span hf hJ)
    exact Ideal.height_eq_zero_iff_eq_bot.mp hheight

/-- Relative codimension-one purity, packaged with primality and strict containment of the
component in the original ring. -/
theorem principalCut_minimalPrime_relative_codimension_one
    {P J : Ideal R} (hP : P.IsPrime) {f : R} (hf : f ∉ P)
    (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    J.IsPrime ∧ P < J ∧ (J.map (Ideal.Quotient.mk P)).height = 1 := by
  exact ⟨hJ.isPrime, Ideal.lt_of_mem_minimalPrimes_sup_span hf hJ,
    map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span hP hf hJ⟩

/-- If the principal cut is proper, it has a minimal-prime component of relative codimension
exactly one. -/
theorem exists_principalCut_component_relative_codimension_one
    {P : Ideal R} (hP : P.IsPrime) {f : R} (hf : f ∉ P)
    (hcut : P ⊔ Ideal.span {f} ≠ ⊤) :
    ∃ J : Ideal R, J ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
      J.IsPrime ∧ P < J ∧ (J.map (Ideal.Quotient.mk P)).height = 1 := by
  obtain ⟨J, hJ⟩ := (P ⊔ Ideal.span {f}).nonempty_minimalPrimes hcut
  exact ⟨J, hJ, principalCut_minimalPrime_relative_codimension_one hP hf hJ⟩

end Ideal
