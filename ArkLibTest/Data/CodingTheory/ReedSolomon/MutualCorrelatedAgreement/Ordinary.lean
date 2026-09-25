/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.BaseEquation
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.IrreducibleEquation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Acceptance cases for ordinary factor bounds and equations -/

open ReedSolomon
open Polynomial PolynomialDifferential MvPolynomial

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

private theorem assemblyFactorExceptionalRoot {c : Associates assemblyPoly}
    (hc : c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ) :
    ∃ ex : Finset Unit, (ex.card : ℚ) = 0 ∧
      ∀ w ∉ ex, ∀ y, assemblyEval w y c.rep = 0 → y = 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro w _ y hy
  exact assemblyFactorRoot hc y hy

private theorem assemblyRootAtZero : assemblyEval () 0 assemblyQ = 0 := by
  simp [assemblyEval, assemblyQ]

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
  obtain ⟨ex, hcard, hroot⟩ := assemblyFactorExceptionalRoot hc
  refine ⟨ex, ?_, hroot⟩
  rw [hcard]
  simp [ordinaryFactorRaw, assemblyHeight]

private theorem assemblyUnifiedFactorGood :
    ∀ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
      ∃ ex : Finset Unit,
        (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt 0 1 0 1
          (MvPolynomial.degreeOf (0 : Fin 1) c.rep) (assemblyHeight c.rep) 1 ∧
        ∀ w ∉ ex, ∀ y, assemblyEval w y c.rep = 0 → y = 0 := by
  intro c hc
  obtain ⟨ex, hcard, hroot⟩ := assemblyFactorExceptionalRoot hc
  refine ⟨ex, ?_, hroot⟩
  rw [hcard]
  simp [ordinaryUnifiedPowerFactorRawAt, assemblyHeight]

private theorem assemblyCurveFactorGood :
    ∀ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
      ∃ ex : Finset Unit,
        (ex.card : ℚ) ≤ ordinaryCurveFactorRaw 0 1 0 1
          (MvPolynomial.degreeOf (0 : Fin 1) c.rep) (assemblyHeight c.rep) ∧
        ∀ w ∉ ex, ∀ y, assemblyEval w y c.rep = 0 → y = 0 := by
  intro c hc
  refine ⟨∅, ?_, ?_⟩
  · simp [ordinaryCurveFactorRaw, assemblyHeight]
  · intro w hw y hy
    exact assemblyFactorRoot hc y hy

private theorem assemblyRootBudget : MvPolynomial.degreeOf (0 : Fin 1) assemblyQ ≤ 1 := by
  simp [assemblyQ]

private theorem assemblyHeightBudget :
    assemblyHeight (MvPolynomial.radicalContent (0 : Fin 1) assemblyQ) +
      ∑ c ∈ MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ,
        assemblyHeight c.rep ≤ 0 := by
  simp [assemblyHeight]

private def ordinaryEquationDomain : Fin 2 ↪ ℂ where
  toFun i := (i.val : ℂ)
  inj' := by
    intro i j hij
    change (i.val : ℂ) = (j.val : ℂ) at hij
    apply Fin.ext
    exact_mod_cast hij

private noncomputable abbrev ordinaryEquation : DifferentialPolynomial ℂ[X] 0 :=
  MvPolynomial.X (some (0 : Fin 1))

example : ∃ exceptional : Finset ℂ, (exceptional.card : ℚ) ≤ 1 ∧
    ∃ z ∉ exceptional,
      HasExactCorrelatedPair ordinaryEquationDomain (fun _ ↦ 0) (fun _ ↦ 0)
        (RingHom.id ℂ) 2 z 0 := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryEquation
    ordinaryEquationDomain (fun _ ↦ 0) (fun _ ↦ 0) (RingHom.id ℂ) ordinaryEquation
    1 0 2 (by norm_num) (by norm_num) (by norm_num)
    (coeffNatDegreeLE_X (some (0 : Fin 1))) MvPolynomial.X_prime.irreducible (by simp)
  have hcard' : (exceptional.card : ℚ) ≤ 1 := by
    simpa [ordinaryEquation, ordinaryFactorRaw] using hcard
  have hcardNat : exceptional.card ≤ 1 := by exact_mod_cast hcard'
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := exceptional) (t := ({0, 1} : Finset ℂ))
    (Nat.lt_of_le_of_lt hcardNat (by norm_num))
  have hpair := hgood z hz 0 (by simp) (by simp [ordinaryEquation, challengeSpecialization]) (by
    norm_num [polynomialAgreementSet, ordinaryEquationDomain])
  exact ⟨exceptional, hcard', z, hz, hpair⟩

example : ∃ exceptional : Finset ℂ, (exceptional.card : ℚ) ≤ 2 ∧
    ∃ z ∉ exceptional,
      HasExactCorrelatedPair ordinaryEquationDomain (fun _ ↦ 0) (fun _ ↦ 0)
        (RingHom.id ℂ) 2 z 0 := by
  classical
  let squareEquation : DifferentialPolynomial ℂ[X] 0 := ordinaryEquation ^ 2
  have hQ : squareEquation ≠ 0 := by
    dsimp [squareEquation, ordinaryEquation]
    exact pow_ne_zero 2 (MvPolynomial.X_ne_zero _)
  have hheight : CoeffNatDegreeLE squareEquation 0 := by
    simpa [squareEquation, ordinaryEquation] using
      (CoeffNatDegreeLE.pow (coeffNatDegreeLE_X (some (0 : Fin 1))) 2)
  have hdegree : squareEquation.degreeOf (some 0) ≤ 2 := by
    simp [squareEquation, ordinaryEquation]
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryEquation
    ordinaryEquationDomain (fun _ ↦ 0) (fun _ ↦ 0) (RingHom.id ℂ) squareEquation
    1 0 2 2 hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hheight hdegree
  have hcard' : (exceptional.card : ℚ) ≤ 2 := by
    simpa [ordinaryFactorRaw] using hcard
  have hcardNat : exceptional.card ≤ 2 := by exact_mod_cast hcard'
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := exceptional) (t := ({0, 1, 2} : Finset ℂ))
    (Nat.lt_of_le_of_lt hcardNat (by norm_num))
  have hpair := hgood z hz 0 (by simp)
    (by simp [squareEquation, ordinaryEquation, challengeSpecialization,
      differentialSpecialization, differentialSpecializationHom]) (by
      norm_num [polynomialAgreementSet, ordinaryEquationDomain])
  exact ⟨exceptional, hcard', z, hz, hpair⟩
example : ∃ exceptional : Finset ℂ, (exceptional.card : ℚ) ≤ 1 ∧
    ∃ z ∉ exceptional, HasExactPowerAgreement (ℓ := 1) ordinaryEquationDomain
      (fun _ _ ↦ 0) (RingHom.id ℂ) 2 z 0 := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryPowerEquation
    (ℓ := 1) ordinaryEquationDomain (fun _ _ ↦ 0) (RingHom.id ℂ) ordinaryEquation
    1 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coeffNatDegreeLE_X (some (0 : Fin 1))) MvPolynomial.X_prime.irreducible (by simp)
  have hcard' : (exceptional.card : ℚ) ≤ 1 := by
    simpa [ordinaryEquation, ordinaryCurveFactorRaw] using hcard
  have hcardNat : exceptional.card ≤ 1 := by exact_mod_cast hcard'
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := exceptional) (t := ({0, 1} : Finset ℂ))
    (Nat.lt_of_le_of_lt hcardNat (by norm_num))
  have hpower := hgood z hz 0 (by simp)
    (by simp [ordinaryEquation, challengeSpecialization]) (by
      norm_num [polynomialAgreementSet, powerBatchedWord])
  exact ⟨exceptional, hcard', z, hz, hpower⟩

example : (MvPolynomial.positiveDegreeFactorClasses (0 : Fin 1) assemblyQ).Nonempty ∧
    (∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryFactorRaw 0 1 0 1 0 ∧
      ∀ w ∉ ex, ∀ y, assemblyEval w y assemblyQ = 0 → y = 0) ∧
    assemblyEval () 0 assemblyQ = 0 := by
  have hresult := exists_exceptional_ordinaryFactorAssembly (i := 0) (Q := assemblyQ)
    (by exact MvPolynomial.X_ne_zero _) assemblyEval (fun _ y ↦ y = 0) assemblyHeight
    0 1 0 1 0 (by norm_num) (by norm_num) assemblyRootBudget assemblyHeightBudget
    assemblyContentGood assemblyFactorGood
  exact ⟨⟨Associates.mk assemblyQ, assemblyFactorMem⟩, hresult, assemblyRootAtZero⟩

example : ∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt 0 1 0 1 1 0 1 ∧
    (∀ w ∉ ex, ∀ y, assemblyEval w y assemblyQ = 0 → y = 0) ∧
    assemblyEval () 0 assemblyQ = 0 := by
  have hresult := exists_exceptional_ordinaryUnifiedPowerFactorAssembly
    (i := 0) (Q := assemblyQ) (by exact MvPolynomial.X_ne_zero _) assemblyEval
    (fun _ y ↦ y = 0) assemblyHeight 0 1 0 1 1 0 1 (by norm_num) (by norm_num)
    assemblyRootBudget assemblyHeightBudget assemblyContentGood assemblyUnifiedFactorGood
  rcases hresult with ⟨ex, hcard, hgood⟩
  exact ⟨ex, hcard, hgood, assemblyRootAtZero⟩

example : (∑ _i ∈ (Finset.univ : Finset (Fin 2)),
    ordinaryFactorRaw 0 4 1 1 1) ≤ ordinaryFactorRaw 0 4 1 2 2 := by
  have h := ordinaryFactorRaw_sum_le (S := (Finset.univ : Finset (Fin 2)))
    (a := fun _ : Fin 2 ↦ 1) (height := fun _ : Fin 2 ↦ 1)
    (theta := 0) (n := 4) (D := 1) (mu := 2) (H := 2) (contentHeight := 0)
    (by norm_num) (by norm_num) (by simp) (by simp)
  simpa using h

example : ordinaryFrobeniusCurveMixedDegree 1 2 3 2 1 = 16 := by
  calc
    ordinaryFrobeniusCurveMixedDegree 1 2 3 2 1 =
        3 + 2 * (2 * 1) + (2 * 1 * 2 - 1) * 3 * (2 * 1 - 1) :=
      ordinaryFrobeniusCurveMixedDegree_eq 1 2 3 2 1
    _ = 16 := by norm_num

example : ordinaryFrobeniusCurveMixedDegree 1 2 3 2 1 ≤ 31 := by
  calc
    ordinaryFrobeniusCurveMixedDegree 1 2 3 2 1 ≤
        3 + 2 * (2 * 1) + 4 * 1 * 3 * (2 * 1) :=
      ordinaryFrobeniusCurveMixedDegree_le 1 2 3 2 1
    _ = 31 := by norm_num

example : (25 : ℚ) ≤ ordinaryCurveFactorRaw 1 5 1 2 2 3 := by
  have h := ordinaryFrobeniusCurve_charge_le 1 5 1 2 3 2 1
    (by norm_num) (by norm_num)
  norm_num [ordinaryFrobeniusCurveMixedDegree] at h
  exact h

example : ordinaryCurveFactorRaw 1 5 1 2 2 3 ≤ 2 * ordinaryFactorRaw 1 5 1 2 2 := by
  exact ordinaryCurveFactorRaw_le_line_mul 1 5 1 2 2 3 2 (by norm_num) (by norm_num)

example : ordinaryCurveFactorRaw 1 5 1 2 1 3 ≤ 44 := by
  calc
    ordinaryCurveFactorRaw 1 5 1 2 1 3 ≤
        ((2 * 2 - 1 : ℕ) + 1 * (1 + 4 * 1 * 2)) * 3 +
        (1 * 2 + (2 * (5 - 1 - 1) : ℕ)) * 1 :=
      ordinaryCurveFactorRaw_le_linear (theta := 1) (n := 5) (D := 1) (ell := 2)
        (a := 1) (mu := 2) 3 (by norm_num)
        (Nat.le_of_lt (by norm_num : (1 : ℕ) < 2))
    _ = 44 := by norm_num

example : ordinaryCurveFactorRaw 1 5 1 2 2 3 = 52 := by
  calc
    ordinaryCurveFactorRaw 1 5 1 2 2 3 =
        ((2 * 2 - 1 : ℕ) + 1 * (1 + 4 * 1 * 2)) * 3 +
        (1 * 2 + (2 * (5 - 1 - 1) : ℕ)) * 2 :=
      ordinaryCurveFactorRaw_eq_linear 1 5 1 2 2 3
    _ = 52 := by norm_num

example : (∑ _i ∈ (Finset.univ : Finset (Fin 2)),
    ordinaryCurveFactorRaw 0 4 1 2 1 1) ≤ ordinaryCurveFactorRaw 0 4 1 2 2 2 := by
  have h := ordinaryCurveFactorRaw_sum_le (S := (Finset.univ : Finset (Fin 2)))
    (a := fun _ : Fin 2 ↦ 1) (height := fun _ : Fin 2 ↦ 1)
    (theta := 0) (n := 4) (D := 1) (ell := 2) (mu := 2) (H := 2) (contentHeight := 0)
    (by norm_num) (by norm_num) (by simp) (by simp)
  simpa using h

example : ∃ ex : Finset Unit, (ex.card : ℚ) ≤ ordinaryCurveFactorRaw 0 1 0 1 1 0 ∧
    (∀ w ∉ ex, ∀ y, assemblyEval w y assemblyQ = 0 → y = 0) ∧
    assemblyEval () 0 assemblyQ = 0 := by
  have hresult := exists_exceptional_ordinaryCurveFactorAssembly
    (i := 0) (Q := assemblyQ) (by exact MvPolynomial.X_ne_zero _) assemblyEval
    (fun _ y ↦ y = 0) assemblyHeight 0 1 0 1 1 0 (by norm_num) (by norm_num)
    assemblyRootBudget assemblyHeightBudget assemblyContentGood assemblyCurveFactorGood
  rcases hresult with ⟨ex, hcard, hgood⟩
  exact ⟨ex, hcard, hgood, assemblyRootAtZero⟩

private def baseEquationDomain : Fin 2 ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    change (i.val : ℚ) = (j.val : ℚ) at hij
    apply Fin.ext
    exact_mod_cast hij

/-- Over `ℚ`, the reducible equation `Y₀²` has an exceptional set of size at most `2` outside
which the zero root of the zero curve has exact power agreement. -/
example : ∃ exceptional : Finset ℚ, (exceptional.card : ℚ) ≤ 2 ∧ ∃ z ∉ exceptional,
    HasExactPowerAgreement (ℓ := 1) baseEquationDomain (fun _ _ ↦ 0) (RingHom.id ℚ) 2 z 0 := by
  classical
  let squareEquation : DifferentialPolynomial ℚ[X] 0 := MvPolynomial.X (some 0) ^ 2
  have hheight : CoeffNatDegreeLE squareEquation 0 := by
    simpa [squareEquation] using
      (CoeffNatDegreeLE.pow (coeffNatDegreeLE_X (some (0 : Fin 1))) 2)
  obtain ⟨exceptional, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation
    (ℓ := 1) baseEquationDomain (fun _ _ ↦ 0) squareEquation 1 0 2 2 2
    (pow_ne_zero 2 (MvPolynomial.X_ne_zero _)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hheight (by simp [squareEquation])
  have hcard' : (exceptional.card : ℚ) ≤ 2 := by
    simpa [ordinaryUnifiedPowerFactorAtOrHeight, ordinaryUnifiedPowerFactorAt,
      ordinaryUnifiedPowerFactorRawAt] using hcard
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hcard', z, hz, hgood z hz 0 (by simp) ?_ ?_⟩
  · simp [squareEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  · norm_num [polynomialAgreementSet, powerBatchedWord]

private def rationalEquationDomain : Fin 2 ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    change (i.val : ℚ) = (j.val : ℚ) at hij
    apply Fin.ext
    exact_mod_cast hij

example : ∃ exceptional : Finset ℚ, (exceptional.card : ℚ) ≤ 2 ∧
    ∃ z ∉ exceptional,
      HasExactCorrelatedPair rationalEquationDomain (fun _ ↦ 0) (fun _ ↦ 0)
        (RingHom.id ℚ) 2 z 0 := by
  classical
  let squareEquation : DifferentialPolynomial ℚ[X] 0 := MvPolynomial.X (some 0) ^ 2
  have hQ : squareEquation ≠ 0 := pow_ne_zero 2 (MvPolynomial.X_ne_zero _)
  have hheight : CoeffNatDegreeLE squareEquation 0 := by
    simpa [squareEquation] using
      (CoeffNatDegreeLE.pow (coeffNatDegreeLE_X (R := ℚ) (some (0 : Fin 1))) 2)
  have hdegree : squareEquation.degreeOf (some 0) ≤ 2 := by
    simp [squareEquation]
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryEquation_base
    rationalEquationDomain (fun _ ↦ 0) (fun _ ↦ 0) squareEquation
    1 0 2 2 hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hheight hdegree
  have hcard' : (exceptional.card : ℚ) ≤ 2 := by
    simpa [ordinaryFactorRaw] using hcard
  have hcardNat : exceptional.card ≤ 2 := by exact_mod_cast hcard'
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := exceptional) (t := ({0, 1, 2} : Finset ℚ))
    (Nat.lt_of_le_of_lt hcardNat (by norm_num))
  have hpair := hgood z hz 0 (by simp)
    (by simp [squareEquation, challengeSpecialization,
      differentialSpecialization, differentialSpecializationHom]) (by
      norm_num [polynomialAgreementSet, rationalEquationDomain])
  exact ⟨exceptional, hcard', z, hz, hpair⟩
