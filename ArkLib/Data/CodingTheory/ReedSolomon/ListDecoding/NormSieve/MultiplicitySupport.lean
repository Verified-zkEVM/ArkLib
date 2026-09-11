/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SquarefreeSupport
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Characteristic-safe retained multiplicity support

The norm sieve keeps the full multiplicity threshold polynomial rather than replacing it by its
ordinary derivative quotient.  In positive characteristic, ordinary derivatives alone lose
factors whose multiplicity is divisible by the characteristic.  This module instead intersects
the zero sets of all Hasse derivatives below the requested threshold and then applies the
executable characteristic-safe squarefree-support routine.

For every nonzero input and positive threshold `T`, the resulting monic squarefree polynomial has
exactly the geometric roots whose original integer root multiplicity is at least `T`.  The
construction is executable for the finite coefficient fields supported by `CPolynomial`; it does
not assert the quasi-linear complexity of the manuscript's separate Yun/residue decomposition.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.NormSieve

open Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Executable `j`-th Hasse derivative of a `CPolynomial`. -/
def cHasseDerivative (j : ℕ) (f : CompPoly.CPolynomial F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.ofArray <| Array.ofFn fun i : Fin (f.natDegree + 1) ↦
    ((i + j).choose j : F) * f.coeff (i + j)

@[simp] theorem coeff_cHasseDerivative (j : ℕ) (f : CompPoly.CPolynomial F) (i : ℕ) :
    (cHasseDerivative j f).coeff i =
      if i < f.natDegree + 1 then ((i + j).choose j : F) * f.coeff (i + j) else 0 := by
  rw [cHasseDerivative, CompPoly.CPolynomial.coeff_ofArray]
  simp only [Array.getD, Array.size_ofFn]
  split <;> simp_all

/-- The executable coefficient-array operation agrees exactly with Mathlib's Hasse derivative. -/
theorem cHasseDerivative_toPoly (j : ℕ) (f : CompPoly.CPolynomial F) :
    (cHasseDerivative j f).toPoly = hasseDeriv j f.toPoly := by
  ext i
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_cHasseDerivative, hasseDeriv_coeff,
    ← CompPoly.CPolynomial.coeff_toPoly]
  split_ifs with hi
  · rfl
  · have hdegree : f.toPoly.natDegree < i + j := by
      rw [← CompPoly.CPolynomial.natDegree_toPoly]
      omega
    have hz := f.toPoly.coeff_eq_zero_of_natDegree_lt hdegree
    rw [← CompPoly.CPolynomial.coeff_toPoly] at hz
    rw [hz, mul_zero]

/-- Successively gcd the input with every Hasse derivative of order below `T`. -/
def multiplicityGCD : ℕ → CompPoly.CPolynomial F → CompPoly.CPolynomial F
  | 0, f => f
  | T + 1, f => CompPoly.CPolynomial.gcdFactor (multiplicityGCD T f)
      (cHasseDerivative T f)

/-- The iterated gcd remains nonzero whenever the input is nonzero. -/
theorem multiplicityGCD_ne_zero {f : CompPoly.CPolynomial F} (hf : f ≠ 0) (T : ℕ) :
    multiplicityGCD T f ≠ 0 := by
  induction T with
  | zero => exact hf
  | succ T ih =>
      exact (CompPoly.CPolynomial.toPoly_eq_zero_iff _).not.mp
        ((CompPoly.CPolynomial.monic_toPoly_iff _).mp
          (CompPoly.CPolynomial.gcdFactor_monic ih)).ne_zero

/-- Intersecting with more Hasse equations never increases the degree. -/
theorem natDegree_multiplicityGCD_le {f : CompPoly.CPolynomial F} (hf : f ≠ 0) (T : ℕ) :
    (multiplicityGCD T f).natDegree ≤ f.natDegree := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
      rw [multiplicityGCD, CompPoly.CPolynomial.natDegree_toPoly]
      exact (Polynomial.natDegree_le_of_dvd
        (CompPoly.CPolynomial.gcdFactor_dvd_left (multiplicityGCD T f)
          (cHasseDerivative T f))
        ((CompPoly.CPolynomial.toPoly_eq_zero_iff _).not.mpr
          (multiplicityGCD_ne_zero hf T))).trans (by
            simpa only [← CompPoly.CPolynomial.natDegree_toPoly] using ih)

/-- The iterated gcd cuts out precisely the common Hasse-derivative zero set. -/
theorem eval₂_multiplicityGCD_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (f : CompPoly.CPolynomial F) (T : ℕ) :
    (multiplicityGCD T f).toPoly.eval₂ phi x = 0 ↔
      f.toPoly.eval₂ phi x = 0 ∧
        ∀ j < T, (cHasseDerivative j f).toPoly.eval₂ phi x = 0 := by
  induction T with
  | zero => simp [multiplicityGCD]
  | succ T ih =>
      rw [multiplicityGCD,
        CompPoly.CPolynomial.eval₂_gcdFactor_eq_zero_iff_left_right, ih]
      constructor
      · rintro ⟨⟨hf, hall⟩, hlast⟩
        exact ⟨hf, fun j hj ↦ by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hall j hj
          · exact hlast⟩
      · rintro ⟨hf, hall⟩
        exact ⟨⟨hf, fun j hj ↦ hall j (hj.trans_le (Nat.le_succ T))⟩,
          hall T (Nat.lt_succ_self T)⟩

variable [Fintype F]

/-- Monic squarefree support of the roots whose multiplicity is at least `T`. -/
def retainedMultiplicitySupport (p T : ℕ) [Fact p.Prime] [CharP F p]
    (f : CompPoly.CPolynomial F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.squarefreeSupport p (multiplicityGCD T f)

/-- Retained multiplicity support is nonzero for every nonzero input, including when no root
meets the threshold (the result is then the constant polynomial `1`). -/
theorem retainedMultiplicitySupport_ne_zero
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) :
    retainedMultiplicitySupport p T f ≠ 0 :=
  CompPoly.CPolynomial.squarefreeSupport_ne_zero p (multiplicityGCD_ne_zero hf T)

/-- Retained multiplicity support is monic. -/
theorem retainedMultiplicitySupport_monic
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) :
    (retainedMultiplicitySupport p T f).monic :=
  CompPoly.CPolynomial.squarefreeSupport_monic p (multiplicityGCD_ne_zero hf T)

/-- Retained multiplicity support is squarefree in every characteristic. -/
theorem retainedMultiplicitySupport_squarefree
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) :
    Squarefree (retainedMultiplicitySupport p T f).toPoly :=
  CompPoly.CPolynomial.squarefreeSupport_squarefree p (multiplicityGCD_ne_zero hf T)

/-- The retained support does not increase degree. -/
theorem natDegree_retainedMultiplicitySupport_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) :
    (retainedMultiplicitySupport p T f).natDegree ≤ f.natDegree := by
  exact (CompPoly.CPolynomial.natDegree_squarefreeSupport_le p
    (multiplicityGCD_ne_zero hf T)).trans (natDegree_multiplicityGCD_le hf T)

/-- Exact geometric semantics: for positive `T`, the output roots are exactly the roots of the
input whose original integer multiplicity is at least `T`.  The statement is stable under every
coefficient-field extension. -/
theorem eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) (hT : 0 < T) :
    (retainedMultiplicitySupport p T f).toPoly.eval₂ phi x = 0 ↔
      T ≤ (f.toPoly.map phi).rootMultiplicity x := by
  rw [retainedMultiplicitySupport,
    CompPoly.CPolynomial.eval₂_squarefreeSupport_eq_zero_iff p phi x
      (multiplicityGCD_ne_zero hf T),
    eval₂_multiplicityGCD_eq_zero_iff]
  have hfpoly : f.toPoly ≠ 0 := (CompPoly.CPolynomial.toPoly_eq_zero_iff f).not.mpr hf
  have hmap : f.toPoly.map phi ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff phi.injective).2 hfpoly
  rw [← Polynomial.hasseDeriv_eval_eq_zero_iff_le_rootMultiplicity hmap x T]
  constructor
  · rintro ⟨_, hall⟩ j hj
    simpa only [cHasseDerivative_toPoly, ← Polynomial.eval_map phi x,
      Polynomial.map_hasseDeriv] using hall j hj
  · intro hall
    refine ⟨?_, fun j hj ↦ ?_⟩
    · have hzero := hall 0 hT
      rw [← Polynomial.eval_map phi x]
      simpa only [hasseDeriv_zero, LinearMap.id_coe, id_eq] using hzero
    · simpa only [cHasseDerivative_toPoly, ← Polynomial.eval_map phi x,
        Polynomial.map_hasseDeriv] using hall j hj

/-- The retained squarefree support pays `T` units of input degree for every unit of output
degree.  This is the exact degree compression used by the norm sieve. -/
theorem threshold_mul_natDegree_retainedMultiplicitySupport_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {f : CompPoly.CPolynomial F} (hf : f ≠ 0) (hT : 0 < T) :
    T * (retainedMultiplicitySupport p T f).natDegree ≤ f.natDegree := by
  classical
  let K := AlgebraicClosure F
  let phi : F →+* K := algebraMap F K
  let G := (retainedMultiplicitySupport p T f).toPoly.map phi
  let P := f.toPoly.map phi
  have hphi : Function.Injective phi := FaithfulSMul.algebraMap_injective F K
  have hG0 : G ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hphi).2
      ((CompPoly.CPolynomial.toPoly_eq_zero_iff _).not.mpr
        (retainedMultiplicitySupport_ne_zero p T hf))
  have hP0 : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hphi).2
      ((CompPoly.CPolynomial.toPoly_eq_zero_iff _).not.mpr hf)
  have hGfree : G.Separable := by
    exact ((PerfectField.separable_iff_squarefree).2
      (retainedMultiplicitySupport_squarefree p T hf)).map
  have hGnodup : G.roots.Nodup := Polynomial.nodup_roots hGfree
  have hrootsG : G.roots.card = (retainedMultiplicitySupport p T f).natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
    exact (CompPoly.CPolynomial.natDegree_toPoly _).symm
  have hrootsP : P.roots.card = f.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
    exact (CompPoly.CPolynomial.natDegree_toPoly _).symm
  have hsubset : G.roots.toFinset ⊆ P.roots.toFinset := by
    intro x hx
    have hGroot : G.eval x = 0 := by
      exact (Polynomial.mem_roots hG0).mp (Multiset.mem_toFinset.mp hx)
    have hmult : T ≤ P.rootMultiplicity x := by
      exact (eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
        p T phi x hf hT).mp (by simpa [G, Polynomial.eval_map] using hGroot)
    have hProot : P.IsRoot x :=
      (Polynomial.rootMultiplicity_pos hP0).mp (hT.trans_le hmult)
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP0).mpr hProot)
  calc
    T * (retainedMultiplicitySupport p T f).natDegree = T * G.roots.card := by
      rw [hrootsG]
    _ = T * G.roots.toFinset.card := by
      rw [Multiset.toFinset_card_of_nodup hGnodup]
    _ = ∑ _x ∈ G.roots.toFinset, T := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ G.roots.toFinset, P.rootMultiplicity x := by
      exact Finset.sum_le_sum fun x hx ↦ by
        have hGroot : G.eval x = 0 :=
          (Polynomial.mem_roots hG0).mp (Multiset.mem_toFinset.mp hx)
        exact (eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
          p T phi x hf hT).mp (by simpa [G, P, Polynomial.eval_map] using hGroot)
    _ ≤ ∑ x ∈ P.roots.toFinset, P.rootMultiplicity x := by
      exact Finset.sum_le_sum_of_subset hsubset
    _ = P.roots.card := by
      simpa only [Polynomial.count_roots] using Multiset.toFinset_sum_count_eq P.roots
    _ = f.natDegree := hrootsP

end ReedSolomon.ListDecoding.NormSieve
