/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentAgreement
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PairCounting
public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Hypersurface
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCutDegree
/-!
# Incidence away from admissible source-chart pairs

The excluded locus is the union of actual admissible pair graphs. Component recognition
discharges the terminal condition of hypersurface incidence for every prime containing the
initial and high-coefficient equations. Degree bounds here refer to literal joint source
polynomials, so the exponent counts the challenge coordinate as well as the initial jets.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

/-- The finite list of actual high-coefficient equations in joint source coordinates. -/
def sourceChartHighCuts (center : E) (Q : DifferentialPolynomial E[X] r) (K k : ℕ) :
    List (MvPolynomial (Option (Fin (r + 1))) E) :=
  ((Finset.univ : Finset {l : Fin K // k ≤ l.val}).toList.map
    fun l ↦ symbolicSourceNumerator center Q K l.val)

/-- Every high source numerator occurs in the finite high-cut list. -/
theorem symbolicSourceNumerator_mem_sourceChartHighCuts
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k : ℕ)
    (l : Fin K) (hl : k ≤ l.val) :
    symbolicSourceNumerator center Q K l ∈ sourceChartHighCuts center Q K k := by
  classical
  simp only [sourceChartHighCuts, List.mem_map, Finset.mem_toList]
  exact ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

/-- Source points on graphs of pairs satisfying the actual chart identities. -/
def sourceChartPairLocus [DecidableEq F] (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r) (K k L : ℕ) :
    Set (Option (Fin (r + 1)) → E) :=
  {x | ∃ pair : F[X] × F[X], IsAdmissibleChartPair domain f g iota center Q K k L pair ∧
    x = affineGraphPoint (polynomialJet (d := r) center (pair.1.map iota))
      (polynomialJet (d := r) center (pair.2.map iota)) (x none)}

/-- A positive-dimensional prime containing at least `L` agreement cuts has all its
regular points on actual admissible pair graphs. -/
theorem principalOpen_subset_sourceChartPairLocus
    [IsAlgClosed E] [DecidableEq F] {K k L : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (hK : r < K) (hkL : k ≤ L)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ q ∈ sourceChartHighCuts center Q K k, q ∈ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hcuts : L ≤ (cutsInIdeal P (fun i ↦
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)))).card) :
    principalOpenZeroLocus P (symbolicSourceSeparant center Q) ⊆
      sourceChartPairLocus domain f g iota center Q K k L := by
  classical
  obtain ⟨indices, hsub, hcard⟩ := Finset.exists_subset_card_eq hcuts
  obtain ⟨P₀, P₁, hP₀, hP₁, hcommon, hgraph, _hvanish, hinitPair, hhighPair,
      hregularPair, hreconstruction⟩ :=
    exists_graphLine_pair_of_symbolic_prime_agreements domain f g indices hcard hkL
      iota center Q hK P hP hs hd hinit
      (fun l hl ↦ hhigh _ (symbolicSourceNumerator_mem_sourceChartHighCuts center Q K k l hl))
      (fun i hi ↦ (mem_cutsInIdeal.mp (hsub hi)))
  intro x hx
  refine ⟨(P₀, P₁), ?_, hgraph x hx⟩
  exact ⟨hP₀, hP₁, hcommon, hinitPair, hhighPair, hregularPair, hreconstruction⟩

/-- Finite regular source points outside admissible pair graphs satisfy hypersurface
incidence with the joint-space exponent `r + 1`. The input bounds are the actual total
degrees of the initial, high, and agreement polynomials. -/
theorem finite_sourceChart_points_off_pairs_card_le
    [IsAlgClosed E] [DecidableEq F] {K k L A sourceDegree B : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hsourceDegree : (symbolicSourceInitialEquation center Q).totalDegree ≤ sourceDegree)
    (hB : 0 < B)
    (hhighDegree : ∀ l : Fin K, k ≤ l.val →
      (symbolicSourceNumerator center Q K l).totalDegree ≤ B)
    (hagreementDegree : ∀ i,
      (symbolicSourceAgreement center Q K (iota (domain i))
        (iota (f i)) (iota (g i))).totalDegree ≤ B)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceChartPairLocus domain f g iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i))) x).card) :
    (S.card : ℚ) ≤ (sourceDegree : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  have hbound := hypersurfaceCutFamily_incidence_off_excluded
    (symbolicSourceInitialEquation center Q) (symbolicSourceSeparant center Q)
    hinit hsourceDegree hB (sourceChartHighCuts center Q K k)
    (by
      intro q hq
      simp only [sourceChartHighCuts, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      exact hhighDegree l.val l.property)
    (fun i ↦ symbolicSourceAgreement center Q K
      (iota (domain i)) (iota (f i)) (iota (g i))) hagreementDegree hL hLA hAn
    (sourceChartPairLocus domain f g iota center Q K k L)
    (fun P hp hs hi hh hd hc ↦ principalOpen_subset_sourceChartPairLocus
      domain f g iota center Q hK hkL P hp hs hi hh hd hc) S
    (by
      intro x hx
      refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
      intro q hq
      simp only [sourceChartHighCuts, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      exact (hS x hx).2.2.1 l.val l.property) hA
  simpa using hbound

/-- Source jet degree and challenge height discharge all literal joint-degree hypotheses. -/
theorem finite_sourceChart_points_off_pairs_card_le_of_source
    [IsAlgClosed E] [DecidableEq F] {K k L A v h : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceChartPairLocus domain f g iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i))) x).card) :
    (S.card : ℚ) ≤ ((v + h : ℕ) : ℚ) *
      (((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  apply finite_sourceChart_points_off_pairs_card_le domain f g iota center Q hK hkL hL hLA
    hAn hinit (jointTotalDegree_initialJetEquationOver_le_of_source center Q v h hjet hheight)
    (by omega) (fun l _ ↦
      jointTotalDegree_commonTaylorNumeratorOver_le_of_source center Q v h K hv hjet hheight l)
    (fun i ↦ jointTotalDegree_taylorAgreementEquationOver_le_of_source center
      (iota (domain i)) (iota (f i)) (iota (g i)) Q v h K hv hjet hheight) S hS hA

end ReedSolomon
