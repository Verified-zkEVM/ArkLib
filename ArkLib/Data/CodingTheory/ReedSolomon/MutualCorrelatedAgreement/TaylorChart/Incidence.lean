/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PairCounting
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
/-!
# Incidence outside admissible Taylor-pair graphs

The high Taylor equations define a finite list in the joint challenge and jet coordinates.
Positive-dimensional regular components containing these equations and enough agreement cuts
are parametrized by admissible polynomial-pair graphs. The generic hypersurface incidence bound
then bounds every finite set of regular chart points outside those graphs.

## Main statements

* `jointTaylorHighCutList` and `jointCommonTaylorNumerator_mem_jointTaylorHighCutList` describe
  the high Taylor equations in joint coordinates.
* `admissibleChartPairGraphLocus` is the union of graphs of admissible polynomial pairs.
* `principalOpen_subset_admissibleChartPairGraphLocus` identifies regular points on positive-
  dimensional prime components with admissible pair graphs.
* `finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le` gives the incidence
  bound from total-degree hypotheses; its jet-degree specialization uses coefficient height.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

/-- The common Taylor numerators with indices `k ≤ l < K`, using exponent `2 * K`. -/
def jointTaylorHighCutList (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k : ℕ) : List (MvPolynomial (Option (Fin (r + 1))) E) :=
  ((Finset.univ : Finset {l : Fin K // k ≤ l.val}).toList.map
    fun l ↦ jointCommonTaylorNumerator center Q (2 * K) l.val)

/-- Every joint common numerator with index at least `k` occurs in the high-cut list. -/
theorem jointCommonTaylorNumerator_mem_jointTaylorHighCutList
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k : ℕ)
    (l : Fin K) (hl : k ≤ l.val) :
    jointCommonTaylorNumerator center Q (2 * K) l ∈ jointTaylorHighCutList center Q K k := by
  classical
  simp only [jointTaylorHighCutList, List.mem_map, Finset.mem_toList]
  exact ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

/-- Joint chart points on graphs of admissible polynomial pairs. -/
def admissibleChartPairGraphLocus [DecidableEq F] (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r) (K k L : ℕ) :
    Set (Option (Fin (r + 1)) → E) :=
  {x | ∃ pair : F[X] × F[X],
    IsAdmissibleChartPair domain f g iota center Q K k L pair ∧
      ∃ z : E,
        x = fun j ↦ (affinePairCurve center (pair.1.map iota) (pair.2.map iota) j).eval z}

/-- A positive-dimensional prime containing the initial and high Taylor equations has its regular
points on graphs of admissible pairs when it contains enough agreement equations. -/
theorem principalOpen_subset_admissibleChartPairGraphLocus
    [IsAlgClosed E] [DecidableEq F] {K k L : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (hK : r < K) (hkL : k ≤ L)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hinit : jointInitialJetEquation center Q ∈ P)
    (hhigh : ∀ q ∈ jointTaylorHighCutList center Q K k, q ∈ P)
    (hd : 0 < (affineHilbertPolynomial P).natDegree)
    (hcuts : L ≤ {i | jointTaylorAgreementEquation center Q K (2 * K)
      (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) ∈ P}.ncard) :
    {x | x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
      admissibleChartPairGraphLocus domain f g iota center Q K k L := by
  classical
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    jointTaylorAgreementEquation center Q K (2 * K) (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
  let cutIndices : Finset (Fin n) := Finset.univ.filter fun i ↦ cuts i ∈ P
  have hindicesCard : L ≤ cutIndices.card := by
    have hset : (cutIndices : Set (Fin n)) = {i | cuts i ∈ P} := by
      ext i
      simp [cutIndices]
    calc
      L ≤ {i | cuts i ∈ P}.ncard := hcuts
      _ = (cutIndices : Set (Fin n)).ncard := by rw [hset]
      _ = cutIndices.card := Set.ncard_coe_finset _
  obtain ⟨indices, hsub, hcard⟩ := Finset.exists_subset_card_eq hindicesCard
  have hcuts' : ∀ i ∈ indices, cuts i ∈ P := by
    intro i hi
    have hi' : i ∈ cutIndices := hsub hi
    simpa [cutIndices] using hi'
  obtain ⟨P₀, P₁, hP₀, hP₁, hcommon, hgraph, -, hinitPair, hhighPair,
      hregularPair, hreconstruction⟩ :=
    @exists_graphLine_pair_of_regular_component_agreements (E := E) (r := r) (F := F)
      (n := n) (k := k) (K := K) inferInstance inferInstance inferInstance inferInstance
      (L := L) domain f g indices hcard hkL iota center Q hK
      (2 * K) (taylorExponentSufficient_two_mul r K) P hP hs hd hinit
      (fun l hl ↦ hhigh _
        (jointCommonTaylorNumerator_mem_jointTaylorHighCutList center Q K k l hl)) hcuts'
  intro x hx
  obtain ⟨z, hx⟩ := hgraph x hx
  refine ⟨(P₀, P₁), ?_, z, hx⟩
  refine ⟨hP₀, hP₁, hcommon, ?_, ?_, ?_, ?_⟩
  · simpa [chartPairPullback] using hinitPair
  · intro l hl
    simpa [chartPairPullback] using hhighPair l hl
  · simpa [chartPairPullback] using hregularPair
  · intro l
    simpa [chartPairPullback] using hreconstruction l

/-- A finite set of regular joint Taylor-chart points outside admissible pair graphs satisfies
the hypersurface incidence bound with exponent `r + 1`. -/
theorem finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le
    [IsAlgClosed E] [DecidableEq F] {K k L A initialDegree cutDegree : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A - L + 1 ≤ n)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hinitialDegree : (jointInitialJetEquation center Q).totalDegree ≤ initialDegree)
    (hhighDegree : ∀ l : Fin K, k ≤ l.val →
      (jointCommonTaylorNumerator center Q (2 * K) l).totalDegree ≤ cutDegree)
    (hagreementDegree : ∀ i,
      (jointTaylorAgreementEquation center Q K (2 * K) (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
          ).totalDegree ≤ cutDegree)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q (2 * K) l) = 0) ∧
      x ∉ admissibleChartPairGraphLocus domain f g iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤
      {i | aeval x (jointTaylorAgreementEquation center Q K (2 * K)
        (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ (initialDegree : ℚ) *
      (((n * cutDegree : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  have hbound := MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface
    (g := jointInitialJetEquation center Q) hinit (jointInitialJetSeparant center Q)
    hinitialDegree (jointTaylorHighCutList center Q K k)
    (by
      intro q hq
      simp only [jointTaylorHighCutList, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      exact hhighDegree l.val l.property)
    (fun i ↦ jointTaylorAgreementEquation center Q K (2 * K)
      (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))))
    hagreementDegree hLA (by simpa using hAn)
    (admissibleChartPairGraphLocus domain f g iota center Q K k L)
    (fun P hP hs hinitial hhigh hd hc ↦ principalOpen_subset_admissibleChartPairGraphLocus
      domain f g iota center Q hK hkL P hP hs hinitial
      (by
        intro q hq
        exact hhigh q hq) hd hc) S
    (by
      intro x hx
      refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
      intro q hq
      simp only [jointTaylorHighCutList, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      exact (hS x hx).2.2.1 l.val l.property) hA
  have hexponent : Nat.card (Option (Fin (r + 1))) - 1 = r + 1 := by
    simp [Nat.card_eq_fintype_card]
  simpa only [hexponent, Fintype.card_fin] using hbound

/-- Jet degree and coefficient height give the literal total-degree bounds for the incidence
estimate. -/
theorem finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le_of_jetDegree
    [IsAlgClosed E] [DecidableEq F] {K k L A v h : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A - L + 1 ≤ n)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q (2 * K) l) = 0) ∧
      x ∉ admissibleChartPairGraphLocus domain f g iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤
      {i | aeval x (jointTaylorAgreementEquation center Q K (2 * K)
        (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ ((v + h : ℕ) : ℚ) *
      (((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  apply finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le
    (initialDegree := v + h) (cutDegree := 1 + 2 * K * (v - 1 + h))
    domain f g iota center Q hK hkL hLA hAn hinit
    (by
      simpa [jointInitialJetEquation, jointTotalDegree] using
        jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE center Q v h hjet hheight)
    (fun l hl ↦ by
      have hlK : l.val < K := l.isLt
      have hlτ : 2 * (l.val - r) - 1 ≤ 2 * K := by omega
      simpa [jointCommonTaylorNumerator, jointTotalDegree] using
        jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE center Q v h
          (2 * K) l.val hlτ hjet hheight)
    (fun i ↦ by
      simpa [jointTaylorAgreementEquation, jointTotalDegree] using
        jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent
          center (iota (domain i)) (iota (f i)) (iota (g i)) Q v h K (2 * K)
          (taylorExponentSufficient_two_mul r K) hjet hheight)
    S hS hA

end

end ReedSolomon
