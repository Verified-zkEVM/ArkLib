/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedAdmissibility
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
public import
  ArkLib.ToMathlib.MvPolynomial.PowerMomentGeometry
public import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
public import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Incidence away from admissible power-batched graphs

The graph locus records the points covered by admissible polynomial tuples. Positive-dimensional
regular prime components with sufficiently many agreement cuts lie in this locus. The power-moment
lift then bounds the points on the initial equation and high Taylor cuts that lie outside it.

## Main statements

* `admissibleChartTupleGraphLocus` and
  `principalOpen_subset_admissibleChartTupleGraphLocus`: the graph locus and its component
  coverage property.
* `finite_admissibleChartTupleIncidence_off_graphs`: a finite incidence bound away from the graph
  locus.
* `finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent`: the dimension-sensitive
  product bound for finite sets of regular jets satisfying high cuts.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- Points on regular admissible polynomial tuple graphs at exponent `τ`. -/
def admissibleChartTupleGraphLocus [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) : Set (Option (Fin (r + 1)) → E) :=
  {x | ∃ P : Fin (ℓ + 1) → F[X],
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P ∧
      x = fun j ↦ (powerBatchedJetGraphMap (r := r) center
        (fun t ↦ (P t).map iota) j).eval (x none)}

/-- A positive-dimensional regular prime component with enough agreement cuts lies on an
admissible polynomial tuple graph. -/
theorem principalOpen_subset_admissibleChartTupleGraphLocus
    [decF : DecidableEq F] [IsAlgClosed E] (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E) (center : E)
    (Q : DifferentialPolynomial E[X] r) (K k L τ : ℕ)
    (hK : r < K) (hkL : k ≤ L) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hinit : jointInitialJetEquation center Q ∈ I)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : L ≤ {i : Fin n | jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate fun t ↦ iota (w t i)) ∈ I}.ncard) :
    {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
      admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
  let cutIndices : Set (Fin n) := {i | jointTaylorAgreementEquation center Q K τ
    (Polynomial.C (iota (domain i)))
    (powerBatchedCoordinate fun t ↦ iota (w t i)) ∈ I}
  have hfinite : cutIndices.Finite := Set.toFinite _
  have hcutsCard : L ≤ cutIndices.toFinset.card := by
    rw [Set.ncard_eq_toFinset_card cutIndices hfinite] at hcuts
    exact hcuts
  obtain ⟨indices, hsubset, hcard⟩ := Finset.exists_subset_card_eq hcutsCard
  obtain ⟨P, hP, hgraph⟩ := exists_admissibleChartTuple_of_primeTaylorComponent_agreements
    (K := K) (k := k) (L := L) domain w indices hcard hkL iota center Q hK τ
    hτ I hI hs hd hinit hhigh
    (fun i hi ↦ by
      have hi' : i ∈ cutIndices.toFinset := hsubset hi
      simpa only [cutIndices, Set.mem_toFinset, Set.mem_ofPred_eq] using hi')
  intro x hx
  have hP' : IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P := by
    have hinst : decF = Classical.decEq F := Subsingleton.elim _ _
    cases hinst
    exact hP
  exact ⟨P, hP', hgraph x hx⟩

private theorem coeffNatDegreeLE_taylorAgreementEquationOver
    (center x : E) (y : E[X]) (Q : DifferentialPolynomial E[X] r)
    (K τ h ell : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hheight : CoeffNatDegreeLE Q h) (hy : y.natDegree ≤ ell) :
    CoeffNatDegreeLE (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C x) y (τ := τ)) (ell + τ * h) := by
  unfold taylorAgreementEquationOver
  rw [sub_eq_add_neg]
  apply CoeffNatDegreeLE.add
  · apply coeffNatDegreeLE_sum
    intro l _
    exact ((coeffNatDegreeLE_C (h := 0) (by simp)).mul
      (coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val (hτ l) hheight)).mono
        (by omega)
  · have hsecond : CoeffNatDegreeLE
        (MvPolynomial.C y * initialJetSeparant (Polynomial.C center) Q ^ τ)
        (ell + τ * h) := by
      have hy' : CoeffNatDegreeLE (MvPolynomial.C y : MvPolynomial (Fin (r + 1)) E[X])
          ell := coeffNatDegreeLE_C hy
      have hsep := coeffNatDegreeLE_initialJetSeparant Q center hheight
      simpa only [Polynomial.algebraMap_eq, zero_add, add_mul, one_mul] using
        (hy'.mul (hsep.pow τ))
    intro m
    simpa only [MvPolynomial.coeff_neg, Polynomial.natDegree_neg] using hsecond m

private theorem totalDegree_of_restrictBidegree {P : MvPolynomial (Fin (r + 1)) E[X]}
    {h v : ℕ} (hP : (optionEquivRight E (Fin (r + 1))).symm P ∈
      restrictBidegree (Fin (r + 1)) E h v) : P.totalDegree ≤ v := by
  have hrect := (mem_restrictBidegree_iff_weightedTotalDegree_le.mp hP).2
  have hdegree := totalDegree_optionEquivRight
    ((optionEquivRight E (Fin (r + 1))).symm P)
  rw [AlgEquiv.apply_symm_apply] at hdegree
  exact hdegree.trans_le hrect

/-- A finite family of regular points on the initial equation and high Taylor cuts, outside the
admissible tuple graphs, has a bound linear in the batching degree. -/
theorem finite_admissibleChartTupleIncidence_off_graphs
    [IsAlgClosed E] [DecidableEq F] {K k L A v h : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hsep : jointInitialJetSeparant center Q ≠ 0)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S,
      aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q (2 * K) l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L (2 * K))
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K (2 * K)
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
      (((n * (2 + 2 * K * v) : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  let D := ℓ + h
  let M := 2 * K
  let B := 2 + 2 * K * v
  let g : MvPolynomial (Fin (r + 1)) E[X] :=
    initialJetEquation (Polynomial.C center) Q
  let s : MvPolynomial (Fin (r + 1)) E[X] :=
    initialJetSeparant (Polynomial.C center) Q
  let high : {l : Fin K // k ≤ l.val} → MvPolynomial (Fin (r + 1)) E[X] :=
    fun l ↦ commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q M l.val
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) E[X] := fun i ↦
    taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate fun t ↦ iota (w t i)) (τ := M)
  have hτ : TaylorExponentSufficient r K M := taylorExponentSufficient_two_mul r K
  have hEllD : ℓ ≤ D := by dsimp only [D]; omega
  have hHeightD : h ≤ D := by dsimp only [D]; omega
  have hgHeight : CoeffNatDegreeLE g D := by
    have hh := coeffNatDegreeLE_initialJetEquation center Q hheight
    exact hh.mono hHeightD
  have hsHeight : CoeffNatDegreeLE s D := by
    have hh := coeffNatDegreeLE_initialJetSeparant Q center hheight
    exact hh.mono hHeightD
  have hhighHeight : ∀ l, CoeffNatDegreeLE (high l) (M * D) := by
    intro l
    exact (coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h M l.val (hτ l)
      hheight).mono (Nat.mul_le_mul_left M hHeightD)
  have hcutsHeight : ∀ i, CoeffNatDegreeLE (cuts i) (M * D) := by
    intro i
    have hy : (powerBatchedCoordinate fun t ↦ iota (w t i)).natDegree ≤ ℓ :=
      powerBatchedCoordinate_natDegree_le _
    have hh := coeffNatDegreeLE_taylorAgreementEquationOver center (iota (domain i))
      (powerBatchedCoordinate fun t ↦ iota (w t i)) Q K M h ℓ hτ hheight hy
    apply hh.mono
    have hM : 1 ≤ M := by dsimp only [M]; omega
    calc
      ℓ + M * h ≤ M * ℓ + M * h := Nat.add_le_add_right
        (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right ℓ hM) _
      _ = M * D := by dsimp only [D]; ring
  have hgDegree : g.totalDegree + 1 ≤ v + 1 := by
    have hdeg := (totalDegree_initialJetEquation_le (Polynomial.C center) Q).trans hjet
    exact Nat.add_le_add_right hdeg 1
  have bidegree_to_totalDegree_bound
      {p : MvPolynomial (Fin (r + 1)) E[X]}
      (hp : p.totalDegree ≤ 1 + M * (v - 1)) : p.totalDegree + M + 1 ≤ B := by
    have hmv : M * (v - 1) + M = M * v := by
      calc
        _ = M * (v - 1) + M * 1 := by rw [Nat.mul_one]
        _ = M * ((v - 1) + 1) := by rw [Nat.mul_add]
        _ = M * v := by rw [Nat.sub_add_cancel (by omega)]
    calc
      _ ≤ (1 + M * (v - 1)) + M + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hp M) 1
      _ = 2 + (M * (v - 1) + M) := by omega
      _ = 2 + M * v := by rw [hmv]
      _ = B := by dsimp only [B, M]
  have hhighDegree : ∀ l, (high l).totalDegree + M + 1 ≤ B := by
    intro l
    have hrect := commonTaylorNumeratorOver_mem_restrictBidegree center Q h v K M hτ
      hheight hv hjet l.val
    have hdegree : (high l).totalDegree ≤ 1 + M * (v - 1) := by
      simpa only [high] using totalDegree_of_restrictBidegree hrect
    exact bidegree_to_totalDegree_bound hdegree
  have hcutsDegree : ∀ i, (cuts i).totalDegree + M + 1 ≤ B := by
    intro i
    have hy : (powerBatchedCoordinate fun t ↦ iota (w t i)).natDegree ≤ ℓ :=
      powerBatchedCoordinate_natDegree_le _
    have hrect := taylorAgreementEquationOver_mem_restrictBidegree
      (F := E) center (iota (domain i))
      (powerBatchedCoordinate fun t ↦ iota (w t i)) Q ℓ h v K M hτ hy hheight hv hjet
    have hdegree : (cuts i).totalDegree ≤ 1 + M * (v - 1) := by
      simpa only [cuts] using totalDegree_of_restrictBidegree hrect
    exact bidegree_to_totalDegree_bound hdegree
  have hgSource : (optionEquivRight E (Fin (r + 1))).symm g ≠ 0 := by
    simpa only [g, jointInitialJetEquation] using hinit
  have hsSource : (optionEquivRight E (Fin (r + 1))).symm s ≠ 0 := by
    simpa only [s, jointInitialJetSeparant] using hsep
  apply powerMomentMap_incidence_off_excluded
    (D := D) (M := M) (d := r + 1) (initialDegree := v + 1) (B := B)
    (A := A) (L := L) (g := g) (s := s) (high := high) (cuts := cuts)
    (excluded := admissibleChartTupleGraphLocus domain w iota center Q K k L M)
    (S := S) (ι := {l : Fin K // k ≤ l.val}) hD hgHeight hsHeight hgSource hsSource
  · exact hgDegree
  · exact hhighHeight
  · exact hhighDegree
  · exact hcutsHeight
  · exact hcutsDegree
  · simp
  · dsimp only [B]
    omega
  · exact hL
  · exact hLA
  · exact hAn
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    have hhigh' : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q M l ∈ J := by
      intro l hl
      have := hhighJ ⟨l, hl⟩
      simpa only [high, jointCommonTaylorNumerator] using this
    have hcuts' : L ≤ {i : Fin n | jointTaylorAgreementEquation center Q K M
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate fun t ↦ iota (w t i)) ∈ J}.ncard := by
      simpa only [cuts, jointTaylorAgreementEquation] using hcutsJ
    have hprincipal := principalOpen_subset_admissibleChartTupleGraphLocus
      domain w iota center Q K k L M hK hkL hτ J hJ hsJ hdJ hgJ hhigh' hcuts'
    intro x hx
    exact hprincipal hx
  · intro x hx
    refine ⟨?_, ?_, ?_, (hS x hx).2.2.2⟩
    · simpa only [g, jointInitialJetEquation] using (hS x hx).1
    · simpa only [s, jointInitialJetSeparant] using (hS x hx).2.1
    · intro l
      simpa only [high, jointCommonTaylorNumerator] using
        (hS x hx).2.2.1 l.val l.property
  · intro x hx
    simpa only [cuts, jointTaylorAgreementEquation] using hA x hx

/-- A finite family of regular jets satisfying all high Taylor cuts and enough agreement cuts is
bounded by the dimension-sensitive evaluation product. -/
theorem finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent [IsAlgClosed E]
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ E) (received : Fin n → E)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → E))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q τ l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤
      {i | aeval jet (taylorAgreementEquation center Q K τ (domain i) (received i)) = 0}.ncard) :
    (S.card : ℚ) ≤ (jetTotalDegree Q : ℚ) *
      (rationalTaylorCutDegreeBound Q τ : ℚ) ^ r *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  let B := rationalTaylorCutDegreeBound Q τ
  let T := highTaylorPrimeFamily center Q K k τ
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) E := fun i ↦
    taylorAgreementEquation center Q K τ (domain i) (received i)
  have hcoverNat : S.card ≤ ∑ P ∈ T, (S.filter fun jet ↦ jet ∈ zeroLocus E P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ S.filter fun jet ↦ jet ∈ zeroLocus E P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := exists_mem_highTaylorPrimeFamily_of_regular
          center Q jet (hS jet hjet).1 (hS jet hjet).2.1
          (fun l hkl hlK ↦ (hS jet hjet).2.2 ⟨⟨l, hlK⟩, hkl⟩)
        exact Finset.mem_biUnion.mpr ⟨P, hPT, Finset.mem_filter.mpr ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (S.filter fun jet ↦ jet ∈ zeroLocus E P).card :=
        Finset.card_biUnion_le
  have hcomponent : ∀ P ∈ T,
      ((S.filter fun jet ↦ jet ∈ zeroLocus E P).card : ℚ) ≤
        affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r := by
    intro P hPT
    have hPprime : P.IsPrime := isPrime_of_mem_highTaylorPrimeFamily hPT
    have hhigh : highTaylorCutsIdeal center Q K k τ ≤ P :=
      highTaylorCutsIdeal_le_of_mem_highTaylorPrimeFamily hPT
    have hbound := @MvPolynomial.card_le_dimensionSensitiveIncidenceProduct_of_agreement
      E E (Fin (r + 1)) (Fin n) _ _ _ _ _ P hPprime (initialJetSeparant center Q) cuts B A k
      (fun i ↦ totalDegree_taylorAgreementEquation_le center Q hτ (domain i) (received i))
      hkA (fun J hPJ hJ hsJ hdJ ↦ by
        have hhighJ : highTaylorCutsIdeal center Q K k τ ≤ J := hhigh.trans hPJ
        exact chart_dimensionSensitive_component_of_exponent center Q K k n τ hτ hK hkK
          J hJ hsJ (by
            intro l hkl
            exact hhighJ
              (commonTaylorNumerator_mem_highTaylorCutsIdeal center Q hkl l.isLt))
          domain received hdJ)
      (S.filter fun jet ↦ jet ∈ zeroLocus E P)
      (fun jet hjet ↦ by
        rw [Finset.mem_filter] at hjet
        exact ⟨hjet.2, (hS jet hjet.1).2.1⟩)
      (fun jet hjet ↦ hA jet (Finset.mem_filter.mp hjet).1)
    have hbound' :
        ((S.filter fun jet ↦ jet ∈ zeroLocus E P).card : ℚ) ≤
          affineDegree P *
            dimensionSensitiveIncidenceProduct n A k B (affineHilbertPolynomial P).natDegree := by
      simpa only [Fintype.card_fin] using hbound
    refine hbound'.trans ?_
    rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
    have hmono := dimensionSensitiveIncidenceProduct_mono_dimension
      (n := n) (A := A) (k := k) (b := 1) hAn Nat.zero_lt_one
    calc
      affineDegree P * ((B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 (affineHilbertPolynomial P).natDegree) =
        (affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 (affineHilbertPolynomial P).natDegree := by
        ring
      _ ≤ (affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 r :=
        mul_le_mul_of_nonneg_left
          (hmono (natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily hPT))
          (mul_nonneg (affineDegree_nonneg P) (by positivity))
      _ = affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r := rfl
  have hpotential := sum_affineDegree_mul_pow_highTaylorPrimeFamily_le
    (K := K) (k := k) (τ := τ) center Q hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((S.filter fun jet ↦ jet ∈ zeroLocus E P).card : ℚ) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
        dimensionSensitiveIncidenceProduct n A k 1 r := Finset.sum_le_sum hcomponent
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by rw [Finset.sum_mul]
    _ ≤ (jetTotalDegree Q * (B : ℚ) ^ r) * dimensionSensitiveIncidenceProduct n A k 1 r :=
      mul_le_mul_of_nonneg_right hpotential
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
    _ = _ := rfl

end ReedSolomon

end
