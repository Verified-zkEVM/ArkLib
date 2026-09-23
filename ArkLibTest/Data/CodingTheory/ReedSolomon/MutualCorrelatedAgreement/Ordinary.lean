/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget

open ReedSolomon

open scoped BigOperators

private abbrev assemblyPoly := MvPolynomial (Fin 1) ℚ

private noncomputable def assemblyQ : assemblyPoly := MvPolynomial.X 0

private theorem assemblyAssociatePrime : Prime (Associates.mk assemblyQ) := by
  have hXprime : Prime (MvPolynomial.X (0 : Fin 1) : assemblyPoly) := MvPolynomial.X_prime
  refine ⟨Associates.mk_ne_zero.mpr (MvPolynomial.X_ne_zero _), ?_, ?_⟩
  · rw [Associates.isUnit_mk]
    exact hXprime.not_isUnit
  · intro a b hab
    have hab' := hab
    rw [← Associates.mk_rep a, ← Associates.mk_rep b, Associates.mk_mul_mk] at hab'
    have hdiv : (MvPolynomial.X (0 : Fin 1) : assemblyPoly) ∣ a.rep * b.rep :=
      Associates.mk_dvd_mk.mp hab'
    rcases hXprime.2.2 _ _ hdiv with h | h
    · exact Or.inl (by rw [← Associates.mk_rep a]; exact Associates.mk_dvd_mk.mpr h)
    · exact Or.inr (by rw [← Associates.mk_rep b]; exact Associates.mk_dvd_mk.mpr h)

private theorem assemblyFactorDegree :
    MvPolynomial.degreeOf (0 : Fin 1) (Associates.mk assemblyQ).rep = 1 := by
  have hassoc : Associated ((Associates.mk assemblyQ).rep) assemblyQ :=
    (Associates.mk_eq_mk_iff_associated).mp (Associates.mk_rep (Associates.mk assemblyQ))
  rcases hassoc with ⟨u, hu⟩
  have hrep0 : (Associates.mk assemblyQ).rep ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
    exact (MvPolynomial.X_ne_zero (0 : Fin 1)) hu.symm
  have hu0 : MvPolynomial.degreeOf (0 : Fin 1) (u : assemblyPoly) = 0 := by
    have huinv : ((u⁻¹ : Units assemblyPoly) : assemblyPoly) ≠ 0 := (u⁻¹).ne_zero
    have hmul := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 1)) u.ne_zero huinv
    simp at hmul
    omega
  have hdeg := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 1)) hrep0 u.ne_zero
  rw [hu] at hdeg
  simp [assemblyQ, hu0] at hdeg
  simpa [assemblyQ] using hdeg.symm

private theorem assemblyFactorMem :
    Associates.mk assemblyQ ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ := by
  have hmem : Associates.mk assemblyQ ∈
      UniqueFactorizationMonoid.normalizedFactors (Associates.mk assemblyQ) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (Associates.mk_ne_zero.mpr (MvPolynomial.X_ne_zero _))).2
      ⟨assemblyAssociatePrime, dvd_rfl⟩
  rw [MvPolynomial.mem_positiveDegreeFactorClasses]
  constructor
  · exact UniqueFactorizationMonoid.mem_primeFactors.mpr hmem
  · have hdeg := assemblyFactorDegree
    change 0 < MvPolynomial.degreeOf (0 : Fin 1) (Associates.mk assemblyQ).rep
    rw [hdeg]
    norm_num

private theorem assemblyFactorDvd {c : Associates assemblyPoly}
    (hc : c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ) :
    c.rep ∣ assemblyQ := by
  have hc' := (MvPolynomial.mem_positiveDegreeFactorClasses.mp hc).1
  have hclass : c ∣ Associates.mk assemblyQ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (UniqueFactorizationMonoid.mem_primeFactors.mp hc')
  have hrep : Associates.mk c.rep ∣ Associates.mk assemblyQ := by
    rw [Associates.mk_rep]
    exact hclass
  exact Associates.mk_dvd_mk.mp hrep

private noncomputable def assemblyEval : Unit → ℚ → (assemblyPoly →+* ℚ) :=
  fun _ y ↦ MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ ↦ y)

private theorem assemblyFactorRoot {c : Associates assemblyPoly}
    (hc : c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ) (y : ℚ)
    (hy : assemblyEval () y c.rep = 0) : y = 0 := by
  obtain ⟨r, hr⟩ := assemblyFactorDvd hc
  have h := congrArg (assemblyEval () y) hr
  have hrep : MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ ↦ y) c.rep = 0 := by
    simpa [assemblyEval] using hy
  have h' : y = MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ ↦ y) c.rep *
      MvPolynomial.eval₂ (RingHom.id ℚ) (fun _ ↦ y) r := by
    simpa [assemblyEval, assemblyQ] using h
  rw [hrep, zero_mul] at h'
  exact h'.trans (by simp)

private theorem assemblyPrimeFactors :
    UniqueFactorizationMonoid.primeFactors (Associates.mk assemblyQ) =
      {Associates.mk (MvPolynomial.X (0 : Fin 1) : assemblyPoly)} := by
  rw [UniqueFactorizationMonoid.primeFactors,
    UniqueFactorizationMonoid.normalizedFactors_irreducible assemblyAssociatePrime.irreducible]
  simp [assemblyQ]

private theorem assemblyContent : MvPolynomial.radicalContent (0 : Fin 1) assemblyQ = 1 := by
  rw [MvPolynomial.radicalContent, assemblyPrimeFactors]
  have hdeg : MvPolynomial.degreeOf (0 : Fin 1)
      (Associates.mk (MvPolynomial.X (0 : Fin 1) : assemblyPoly)).rep = 1 := by
    simpa [assemblyQ] using assemblyFactorDegree
  have hfilter :
      ({Associates.mk (MvPolynomial.X (0 : Fin 1) : assemblyPoly)} :
        Finset (Associates assemblyPoly)).filter
          (fun c ↦ MvPolynomial.degreeOf (0 : Fin 1) c.rep = 0) = ∅ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, hc⟩
      rw [hdeg] at hc
      norm_num at hc
    · simp
  rw [hfilter]
  simp

private def assemblyHeight : assemblyPoly → ℕ := fun _ ↦ 0

private theorem assemblyContentGood : ∃ ex : Finset Unit,
    ex.card ≤ assemblyHeight (MvPolynomial.radicalContent (0 : Fin 1) assemblyQ) ∧
    ∀ w ∉ ex, ∀ y, assemblyEval w y (MvPolynomial.radicalContent (0 : Fin 1) assemblyQ) ≠ 0 := by
  refine ⟨∅, by simp [assemblyHeight], ?_⟩
  intro w _ y
  rw [assemblyContent]
  simp [assemblyEval]

private theorem assemblyFactorGood :
    ∀ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
      ∃ ex : Finset Unit,
        (ex.card : ℚ) ≤ ordinaryFactorRaw 0 1 0
          (MvPolynomial.degreeOf (0 : Fin 1) c.rep) (assemblyHeight c.rep) ∧
        ∀ w ∉ ex, ∀ y, assemblyEval w y c.rep = 0 → y = 0 := by
  intro c hc
  refine ⟨∅, ?_, ?_⟩
  · simp [ordinaryFactorRaw, assemblyHeight]
  · intro w _ y hy
    exact assemblyFactorRoot hc y hy

private theorem assemblyUnifiedFactorGood :
    ∀ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
      ∃ ex : Finset Unit,
        (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt 0 1 0 1
          (MvPolynomial.degreeOf (0 : Fin 1) c.rep) (assemblyHeight c.rep) 1 ∧
        ∀ w ∉ ex, ∀ y, assemblyEval w y c.rep = 0 → y = 0 := by
  intro c hc
  refine ⟨∅, ?_, ?_⟩
  · simp [ordinaryUnifiedPowerFactorRawAt, assemblyHeight]
  · intro w _ y hy
    exact assemblyFactorRoot hc y hy

private theorem assemblyRootBudget : MvPolynomial.degreeOf (0 : Fin 1) assemblyQ ≤ 1 := by
  simp [assemblyQ]

private theorem assemblyHeightBudget :
    assemblyHeight (MvPolynomial.radicalContent (0 : Fin 1) assemblyQ) +
      ∑ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
        assemblyHeight c.rep ≤ 0 := by
  simp [assemblyHeight]

example : (MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ).Nonempty ∧
    (∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryFactorRaw 0 1 0 1 0 ∧
      ∀ w ∉ ex, ∀ y, assemblyEval w y assemblyQ = 0 → y = 0) ∧
    assemblyEval () 0 assemblyQ = 0 := by
  have hresult := exists_exceptional_ordinaryFactorAssembly (i := 0) (Q := assemblyQ)
    (by exact MvPolynomial.X_ne_zero _) assemblyEval (fun _ y ↦ y = 0) assemblyHeight
    0 1 0 1 0 (by norm_num) (by norm_num) assemblyRootBudget assemblyHeightBudget
    assemblyContentGood assemblyFactorGood
  have hzero : assemblyEval () 0 assemblyQ = 0 := by
    simp [assemblyEval, assemblyQ]
  exact ⟨⟨Associates.mk assemblyQ, assemblyFactorMem⟩, hresult, hzero⟩

example : ∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt 0 1 0 1 1 0 1 ∧
    (∀ w ∉ ex, ∀ y, assemblyEval w y assemblyQ = 0 → y = 0) ∧
    assemblyEval () 0 assemblyQ = 0 := by
  have hresult := exists_exceptional_ordinaryUnifiedPowerFactorAssembly
    (i := 0) (Q := assemblyQ) (by exact MvPolynomial.X_ne_zero _) assemblyEval
    (fun _ y ↦ y = 0) assemblyHeight 0 1 0 1 1 0 1 (by norm_num) (by norm_num)
    assemblyRootBudget assemblyHeightBudget assemblyContentGood assemblyUnifiedFactorGood
  have hzero : assemblyEval () 0 assemblyQ = 0 := by
    simp [assemblyEval, assemblyQ]
  rcases hresult with ⟨ex, hcard, hgood⟩
  exact ⟨ex, hcard, hgood, hzero⟩

example : ordinaryFrobeniusMixedDegree 1 1 2 2 ≤ 2 * 2 + ordinaryPsi 1 4 := by
  norm_num [ordinaryFrobeniusMixedDegree, ordinaryPsi]
