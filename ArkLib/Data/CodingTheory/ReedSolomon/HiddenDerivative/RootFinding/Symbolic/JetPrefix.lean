/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.JetPrefix


/-!
# Actual-order presentations of symbolic differential equations

Restricting an equation to its highest active jet is valid over polynomial coefficient
rings, before the challenge is evaluated. Injective renaming preserves coefficients,
total jet degree, and every retained individual jet degree. After any coefficient
specialization to a field, the presentation preserves differential equations and separants.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative.SymbolicJetPrefix

noncomputable section

open Polynomial MvPolynomial
open SymbolicSeparantChain (jetWeight)

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- A semantic presentation at the actual order `s.val`; no executable representation
or extra higher jet coordinates are retained. -/
structure Presentation (Q : DifferentialPolynomial R d) (s : Fin (d + 1)) where
  equation : DifferentialPolynomial R s.val
  ambient_eq : MvPolynomial.rename (jetPrefixEmbedding s) equation = Q

/-- The existing highest-active-jet argument works over arbitrary coefficient semirings. -/
theorem vars_subset_prefix (Q : DifferentialPolynomial R d) (s : Fin (d + 1))
    (hs : IsHighestActiveJet Q s) :
    (Q.vars : Set (JetVariable d)) ⊆ Set.range (jetPrefixEmbedding s) := by
  intro v hv
  rcases v with _ | j
  · exact ⟨none, rfl⟩
  · have hdegree : jetDegree Q j ≠ 0 := mem_vars_iff_degreeOf_ne_zero.mp hv
    have hactive : DependsOnJet Q j := Nat.pos_of_ne_zero hdegree
    have hle : j ≤ s := le_of_not_gt fun hsj ↦ hs.2 j hsj hactive
    let j' : Fin (s.val + 1) := ⟨j.val, Nat.lt_succ_iff.mpr hle⟩
    refine ⟨some j', congrArg some (Fin.ext rfl)⟩

/-- Construct an actual-order presentation before specializing any coefficient parameter. -/
theorem exists_presentation (Q : DifferentialPolynomial R d) (s : Fin (d + 1))
    (hs : highestActiveJet Q = some s) : Nonempty (Presentation Q s) := by
  obtain ⟨Q', hQ'⟩ := exists_rename_eq_of_vars_subset_range Q (jetPrefixEmbedding s)
    (jetPrefixEmbedding s).injective
    (vars_subset_prefix Q s (isHighestActiveJet_of_highestActiveJet_eq_some hs))
  exact ⟨⟨Q', hQ'⟩⟩

/-- Injective renaming makes the actual-order equation unique. -/
theorem Presentation.equation_eq {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A B : Presentation Q s) : A.equation = B.equation := by
  apply rename_injective (jetPrefixEmbedding s) (jetPrefixEmbedding s).injective
  rw [A.ambient_eq, B.ambient_eq]

/-- Prefix restriction cannot turn a nonzero equation into zero. -/
theorem Presentation.nonzero {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) (hQ : Q ≠ 0) : A.equation ≠ 0 := by
  intro hz
  apply hQ
  rw [← A.ambient_eq, hz, map_zero]

/-- Every retained coefficient agrees exactly with its ambient coefficient. -/
theorem Presentation.coeff {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) (u : JetVariable s.val →₀ ℕ) :
    MvPolynomial.coeff u A.equation =
      MvPolynomial.coeff (u.mapDomain (jetPrefixEmbedding s)) Q := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, coeff_rename_mapDomain _ (jetPrefixEmbedding s).injective]

/-- Every retained individual jet degree is unchanged by restriction. -/
theorem Presentation.jetDegree {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) (j : Fin (s.val + 1)) :
    PolynomialDifferential.jetDegree A.equation j =
      PolynomialDifferential.jetDegree Q
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) s.isLt⟩ := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he]
  exact (degreeOf_rename_of_injective (jetPrefixEmbedding s).injective (some j)).symm

/-- In particular the literal top jet has exactly the selected ambient exponent. -/
theorem Presentation.top_jetDegree {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) :
    PolynomialDifferential.jetDegree A.equation (Fin.last s.val) =
      PolynomialDifferential.jetDegree Q s := by
  simpa using A.jetDegree (Fin.last s.val)

/-- An actually highest ambient jet becomes the active literal top coordinate. -/
theorem Presentation.highest {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) (hs : highestActiveJet Q = some s) :
    IsHighestActiveJet A.equation (Fin.last s.val) := by
  constructor
  · change 0 < PolynomialDifferential.jetDegree A.equation (Fin.last s.val)
    rw [A.top_jetDegree]
    exact (isHighestActiveJet_of_highestActiveJet_eq_some hs).1
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- Total jet weight is invariant under prefix embedding over any coefficient semiring. -/
theorem jetWeight_rename (s : Fin (d + 1)) (Q : DifferentialPolynomial R s.val) :
    jetWeight (MvPolynomial.rename (jetPrefixEmbedding s) Q) = jetWeight Q := by
  classical
  unfold jetWeight MvPolynomial.weightedTotalDegree
  rw [support_rename_of_injective (jetPrefixEmbedding s).injective, Finset.sup_image]
  congr 1
  funext u
  simp only [Function.comp_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (by intro v; simp) (by intro v a b; simp [add_mul])]
  congr 1
  funext v n
  cases v <;> rfl

/-- Actual-order restriction preserves the total-degree parameter charged at this stage. -/
theorem Presentation.jetWeight {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) : jetWeight A.equation = jetWeight Q := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, jetWeight_rename]

/-- The selected separant is literally the renamed top-coordinate separant. -/
theorem Presentation.separant {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}
    (A : Presentation Q s) :
    MvPolynomial.rename (jetPrefixEmbedding s)
        (PolynomialDifferential.separant A.equation (Fin.last s.val)) =
      PolynomialDifferential.separant Q s := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, PolynomialDifferential.separant, PolynomialDifferential.separant,
    ← pderiv_rename (jetPrefixEmbedding s).injective]
  simp

/-- A coefficient homomorphism maps an exact presentation to an exact presentation.
No assumption that specialization preserves the highest active order is needed. -/
def Presentation.map {S : Type*} [CommSemiring S] (φ : R →+* S)
    {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : Presentation Q s) :
    Presentation (MvPolynomial.map φ Q) s where
  equation := MvPolynomial.map φ A.equation
  ambient_eq := by rw [← map_rename, A.ambient_eq]

/-- After coefficient evaluation, all candidate differential specializations agree. -/
theorem Presentation.specialization {E : Type*} [Field E] (φ : R →+* E)
    {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : Presentation Q s) (P : E[X]) :
    differentialSpecialization (MvPolynomial.map φ A.equation) P =
      differentialSpecialization (MvPolynomial.map φ Q) P := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, map_rename, differentialSpecialization_rename_jetPrefixEmbedding]

/-- Scalar evaluation of arbitrary ambient jets uses only their actual-order prefix. -/
theorem Presentation.jetEvaluation {E : Type*} [Field E] (φ : R →+* E)
    {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : Presentation Q s)
    (center : E) (jet : Fin (d + 1) → E) :
    PolynomialDifferential.jetEvaluation (MvPolynomial.map φ A.equation) center
      (restrictJet s jet) =
      PolynomialDifferential.jetEvaluation (MvPolynomial.map φ Q) center jet := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, map_rename, jetEvaluation_rename_jetPrefixEmbedding]

/-- Coefficient evaluation and actual-order restriction preserve the selected separant
equation on every candidate polynomial. -/
theorem Presentation.separant_specialization {E : Type*} [Field E] (φ : R →+* E)
    {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : Presentation Q s) (P : E[X]) :
    differentialSpecialization
        (PolynomialDifferential.separant (MvPolynomial.map φ A.equation) (Fin.last s.val)) P =
      differentialSpecialization (PolynomialDifferential.separant (MvPolynomial.map φ Q) s) P := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, map_rename, separant_rename_jetPrefixEmbedding,
    differentialSpecialization_rename_jetPrefixEmbedding]

/-- Regular scalar jets of polynomial candidates are unchanged at the actual order. -/
theorem Presentation.regular_iff {E : Type*} [Field E] (φ : R →+* E)
    {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : Presentation Q s)
    (center : E) (P : E[X]) :
    IsRegularJet (MvPolynomial.map φ A.equation) (Fin.last s.val) center
        (polynomialJet center P) ↔
      IsRegularJet (MvPolynomial.map φ Q) s center (polynomialJet center P) := by
  rcases A with ⟨equation, he⟩
  dsimp only
  rw [← he, map_rename, isRegularJet_rename_jetPrefixEmbedding_iff]

/-- Restriction preserves challenge height because the prefix embedding is injective. -/
theorem Presentation.challengeHeight_le {F : Type*} [Field F]
    {Q : DifferentialPolynomial F[X] d} {s : Fin (d + 1)} (A : Presentation Q s)
    {h : ℕ} (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    ∀ u, (MvPolynomial.coeff u A.equation).natDegree ≤ h := by
  intro u
  rw [A.coeff]
  exact hQ _

/-- Every genuine symbolic chain stage has an actual-order presentation preserving
its height, total jet weight, and selected derivative cap. -/
theorem exists_stage_presentation {F : Type*} [Field F]
    {Q terminal : DifferentialPolynomial F[X] d}
    {stages : List (SymbolicSeparantChain.Stage F[X] d)}
    (hc : SymbolicSeparantChain.Chain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    (stage : SymbolicSeparantChain.Stage F[X] d) (hstage : stage ∈ stages) :
    ∃ A : Presentation stage.1 stage.2,
      A.equation ≠ 0 ∧ jetWeight A.equation = jetWeight stage.1 ∧
      PolynomialDifferential.jetDegree A.equation (Fin.last stage.2.val) ≤
        PolynomialDifferential.jetDegree Q stage.2 ∧
      ∀ u, (MvPolynomial.coeff u A.equation).natDegree ≤ h := by
  obtain ⟨hne, hhighest, _, hcaps⟩ := hc.stage_contract stage hstage
  obtain ⟨A⟩ := exists_presentation stage.1 stage.2 hhighest
  refine ⟨A, A.nonzero hne, A.jetWeight, ?_, ?_⟩
  · rw [A.top_jetDegree]
    exact hcaps stage.2
  · exact A.challengeHeight_le ((hc.challengeHeight_le hQ).1 stage hstage)

end

end ReedSolomon.HiddenDerivative.SymbolicJetPrefix
