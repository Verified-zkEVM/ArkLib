/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedRegularEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGraphCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedIncidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension
public import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence
public import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
/-!
# Sharp regular power-batched agreement bounds

For an order-`r` differential equation over a polynomial ring, put

```text
a = ell + tau*h,
b = 1 + tau*(v-1),
J = h*b^(r+1) + (r+1)*v*a*b^r.
```

The arbitrary-order dimension-sensitive bound is

```text
J * ((n-L+1)/(A-L+1)) * P_r(A)
  + ell*(n-L)*v*b^r*P_r(L),
```

where `P_r(T) = prod_{j<r} (n-k+j+1)/(T-k+j+1)`. The incidence estimate applies away from
admissible tuple graphs. Sharp tuple counting bounds the retained graphs, and each graph
contributes at most `ell * (n-L)` accidental roots. A common regular Taylor center lifts the
fixed-center estimate to every finite family of bad challenges, yielding one finite exceptional
set. At order one, the estimates specialize to Section 5.6, Theorem 5.14 and Corollary 5.15
of [DKTZ26].

## Main statements

* The Taylor numerators, including high cuts, and agreement equations fit one common bidegree
  rectangle. The initial equation uses `initialJetEquation_mem_restrictBidegree` in its tighter
  `(h, v)` rectangle.
* The joint-evaluation theorems specialize Taylor equations and numerators at a challenge point,
  and `regularPowerBatchedHighCuts` collects the retained high numerators.
* `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition`
  accepts terminal graph recognition and only requires `k ≤ A`;
  `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent` derives
  recognition internally when `k ≤ L`.
* `finite_powerBatchedBadChallenges_card_le_of_tuple_bound_of_exponent` combines supplied
  tuple and off-graph estimates.
* `finite_powerBatchedBadChallenges_card_le_sharp_of_exponent` combines incidence and tuple
  counting; `exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent` gives one
  exceptional set for all regular bad challenges.

## References

* [DKTZ26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Evaluating a joint initial-jet equation specializes its polynomial coefficients. -/
theorem aeval_jointInitialJetEquation_specialize {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointInitialJetEquation center Q) =
      aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  simpa [Polynomial.evalRingHom] using
    aeval_jointInitialJetEquation center Q (fun i ↦ i.elim z jet)

/-- Evaluating a joint initial-jet separant specializes its polynomial coefficients. -/
theorem aeval_jointInitialJetSeparant_specialize {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointInitialJetSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  simpa [Polynomial.evalRingHom] using
    aeval_jointInitialJetSeparant center Q (fun i ↦ i.elim z jet)

/-- Evaluating a joint Taylor numerator specializes its polynomial coefficients. -/
theorem aeval_jointCommonTaylorNumerator_specialize {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (τ K : ℕ) (l : Fin K)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointCommonTaylorNumerator center Q τ l) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) τ l.val) := by
  simpa [Polynomial.evalRingHom] using
    aeval_jointCommonTaylorNumerator center Q τ l (fun i ↦ i.elim z jet)

/-- Evaluating a joint Taylor agreement equation specializes its polynomial coefficients. -/
theorem aeval_jointTaylorAgreementEquation_specialize {r : ℕ} (center z alpha : E)
    (values : Fin (ℓ + 1) → E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        (jointTaylorAgreementEquation center Q K τ (Polynomial.C alpha)
          (powerBatchedCoordinate values)) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K τ alpha
        (∑ t, z ^ t.val * values t)) := by
  simpa [Polynomial.eval_C, Polynomial.evalRingHom, powerBatchedCoordinate_eval] using
    aeval_jointTaylorAgreementEquation center Q K τ (Polynomial.C alpha)
      (powerBatchedCoordinate values) (fun i ↦ i.elim z jet)

/-- Common Taylor numerator cuts whose Taylor index is at least `k`. -/
def regularPowerBatchedHighCuts {r : ℕ} (center : E)
    (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ) :
    List (MvPolynomial (Option (Fin (r + 1))) E) :=
  ((Finset.univ.filter fun l : Fin K => k ≤ l.val).toList).map
    (fun l ↦ jointCommonTaylorNumerator center Q τ l)

/-- Challenge-degree bound of the common Taylor rectangle at exponent `τ`. -/
def regularPowerBatchedCutChallengeDegree (ℓ K h : ℕ) (τ : ℕ := 2 * K) : ℕ := ℓ + τ * h

/-- Total-jet-degree bound of the common Taylor rectangle at exponent `τ`. -/
def regularPowerBatchedCutJetDegree (K v : ℕ) (τ : ℕ := 2 * K) : ℕ := 1 + τ * (v - 1)

/-- Mixed affine degree of the pulled-back first-order initial hypersurface. -/
def regularPowerBatchedInitialMixedDegreeTwo (ℓ K v h : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  h * regularPowerBatchedCutJetDegree K v (τ := τ) ^ 2 +
    2 * v * regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) *
      regularPowerBatchedCutJetDegree K v (τ := τ)

/-- Sharp regular first-order agreement budget from incidence and exact tuple roots. -/
def regularPowerBatchedAgreementSharpBoundTwo
    (n ℓ K k L A v h : ℕ) (τ : ℕ := 2 * K)
    (η : ℚ) : ℚ :=
  (regularPowerBatchedInitialMixedDegreeTwo ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) * η +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      ((((n - k + 1) * regularPowerBatchedCutJetDegree K v (τ := τ) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))

/-- Mixed affine degree of the pulled-back order-`r` initial hypersurface. -/
def regularPowerBatchedInitialMixedDegree (r ℓ K v h : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  h * regularPowerBatchedCutJetDegree K v (τ := τ) ^ (r + 1) +
    (r + 1) * v * regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) *
      regularPowerBatchedCutJetDegree K v (τ := τ) ^ r

/-- Sharp dimension-sensitive regular agreement budget at derivative order `r`. -/
def regularPowerBatchedAgreementSharpBound
    (r n ℓ K k L A v h : ℕ) (τ : ℕ := 2 * K) : ℚ :=
  (regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      dimensionSensitiveIncidenceProduct n A k 1 r +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      (regularPowerBatchedCutJetDegree K v (τ := τ) : ℚ) ^ r *
      dimensionSensitiveIncidenceProduct n L k 1 r

/-- A joint common Taylor numerator fits the common cut rectangle at exponent `τ`. -/
theorem jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r)
    (ℓ K h v τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (hv : 0 < v)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v)
    (l : Fin K) :
    jointCommonTaylorNumerator center Q τ l ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
  have hrect := commonTaylorNumeratorOver_mem_restrictBidegree center Q h v K τ
    hτ hheight hv hjet l
  simpa only [jointCommonTaylorNumerator, regularPowerBatchedCutChallengeDegree,
    regularPowerBatchedCutJetDegree] using
      mem_restrictBidegree_mono hrect (Nat.le_add_left _ _) le_rfl

/-- A joint agreement equation with a received polynomial of degree at most `ℓ` fits the
common Taylor cut rectangle at exponent `τ`. -/
theorem jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
    {r : ℕ} (center x : E) (y : E[X]) (Q : DifferentialPolynomial E[X] r)
    (ℓ K h v τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hy : y.natDegree ≤ ℓ) (hv : 0 < v) (hheight : CoeffNatDegreeLE Q h)
    (hjet : jetTotalDegree Q ≤ v) :
    jointTaylorAgreementEquation center Q K τ (Polynomial.C x) y ∈
      restrictBidegree (Fin (r + 1)) E
        (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
        (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
  simpa only [jointTaylorAgreementEquation, regularPowerBatchedCutChallengeDegree,
    regularPowerBatchedCutJetDegree] using
      taylorAgreementEquationOver_mem_restrictBidegree center x y Q ℓ h v K τ
        hτ hy hheight hv hjet

/-- Regular points outside admissible tuple graphs satisfy the sharp bidegree incidence bound at
arbitrary derivative order and every positive sufficient Taylor exponent, given terminal
recognition of the retained components. -/
theorem
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition
    {r : ℕ} [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hkA : k ≤ A) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → jointInitialJetSeparant center Q ∉ J →
      jointInitialJetEquation center Q ∈ J →
      (∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ {i : Fin n | jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate fun t ↦ iota (w t i)) ∈ J}.ncard →
      {x | x ∈ zeroLocus E J ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
        admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := jointInitialJetEquation center Q
  let s := jointInitialJetSeparant center Q
  let high := regularPowerBatchedHighCuts center Q K k τ
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))
  have ha : 0 < regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) := by
    unfold regularPowerBatchedCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      exact Nat.add_pos_right ℓ (Nat.mul_pos hτpos hh)
  have hb : 0 < regularPowerBatchedCutJetDegree K v (τ := τ) := by
    simp only [regularPowerBatchedCutJetDegree]
    omega
  have hnotunit : ¬ IsUnit g := by
    intro hg
    have heval : IsUnit (aeval x₀ g) := hg.map (MvPolynomial.aeval x₀)
    rw [(hS x₀ hx₀).1] at heval
    exact not_isUnit_zero heval
  have hproper :
      Ideal.span ({g} : Set (MvPolynomial (Option (Fin (r + 1))) E)) ≠ ⊤ :=
    Ideal.span_singleton_ne_top hnotunit
  have hinit' : g ≠ 0 := by
    simpa only [g] using hinit
  have hinitRect : g ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
    have hrect := initialJetEquation_mem_restrictBidegree center Q h v hheight hjet
    have hchall : h ≤ regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) := by
      unfold regularPowerBatchedCutChallengeDegree
      exact (Nat.le_mul_of_pos_left h hτpos).trans (Nat.le_add_left _ _)
    have hjet' : v ≤ regularPowerBatchedCutJetDegree K v (τ := τ) := by
      unfold regularPowerBatchedCutJetDegree
      calc
        v = (v - 1) + 1 := by omega
        _ ≤ τ * (v - 1) + 1 := Nat.add_le_add_right
          (Nat.le_mul_of_pos_left _ hτpos) _
        _ = 1 + τ * (v - 1) := by omega
    change jointInitialJetEquation center Q ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ))
    exact mem_restrictBidegree_mono hrect hchall hjet'
  have hsepRect : s ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
    have hrect := initialJetSeparant_mem_restrictBidegree center Q h v hheight hjet
    have hchall : h ≤ regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) := by
      unfold regularPowerBatchedCutChallengeDegree
      exact (Nat.le_mul_of_pos_left h hτpos).trans (Nat.le_add_left _ _)
    change jointInitialJetSeparant center Q ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ))
    have hjet' : v - 1 ≤ regularPowerBatchedCutJetDegree K v (τ := τ) := by
      unfold regularPowerBatchedCutJetDegree
      calc
        v - 1 ≤ τ * (v - 1) := Nat.le_mul_of_pos_left _ hτpos
        _ ≤ 1 + τ * (v - 1) := Nat.le_add_left _ _
    exact mem_restrictBidegree_mono hrect hchall hjet'
  have hhighRect : ∀ f ∈ high, f ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
    intro f hf
    simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨l, hl, rfl⟩ := hf
    exact jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
      center Q ℓ K h v τ hτ hv hheight hjet l
  have hcutsRect : ∀ i, cuts i ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
    intro i
    exact jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
      center (iota (domain i)) (powerBatchedCoordinate (fun t ↦ iota (w t i)))
      Q ℓ K h v τ hτ (powerBatchedCoordinate_natDegree_le _) hv hheight hjet
  have hdim : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ high, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      (affineHilbertPolynomial J).natDegree ≤ k + 1 ∧
        (1 < (affineHilbertPolynomial J).natDegree →
          ({i | cuts i ∈ J}.ncard) ≤ k + 1 - (affineHilbertPolynomial J).natDegree) := by
    intro J hJ hsJ hgJ hhighJ hdJ
    have hhigh' : ∀ l : Fin K, k ≤ l.val →
        jointCommonTaylorNumerator center Q τ l ∈ J := by
      intro l hl
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hl, rfl⟩
    have hcomponent := symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK J hJ hsJ hhigh' (domain.trans ⟨iota, iota.injective⟩)
      (fun i ↦ powerBatchedCoordinate (fun t ↦ iota (w t i)))
    simpa only [cuts, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk] using hcomponent
  have hterminal' : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ high, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ ({i | cuts i ∈ J}.ncard) →
        {x | x ∈ zeroLocus E J ∧ aeval x s ≠ 0} ⊆
          admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
    intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply hterminal J hJ
    · simpa only [s] using hsJ
    · simpa only [g] using hgJ
    · intro l hl
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hl, rfl⟩
    · exact hdJ
    · simpa only [cuts] using hcutsJ
  have hbound : (S.card : ℚ) ≤
      affineDegree ((Ideal.span {g}).comap
        (bidegreeMap (Fin (r + 1)) E
          (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
          (regularPowerBatchedCutJetDegree K v (τ := τ)))) *
        hybridDimensionSensitiveIncidenceProduct n A L k 1
          (min ((affineHilbertPolynomial (Ideal.span {g})).natDegree - 1) k + 1) := by
    apply bidegreeHypersurface_incidence_off_excluded_hybrid
      ha hb hLA hkA hAn g s hinit hproper hinitRect hsepRect high hhighRect
      cuts hcutsRect (admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
      hdim hterminal' S ?_ ?_
    · intro x hx
      refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
      intro f hf
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨l, hl, rfl⟩ := hf
      exact (hS x hx).2.2.1 l hl
    · simpa only [cuts] using hA
  have hdegree : affineDegree ((Ideal.span {g}).comap
      (bidegreeMap (Fin (r + 1)) E
        (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
        (regularPowerBatchedCutJetDegree K v (τ := τ)))) ≤
      regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) := by
    have hrect := initialJetEquation_mem_restrictBidegree center Q h v hheight hjet
    have hdegree := affineDegree_comap_bidegreeMap_span_singleton_le ha hb hinit' hrect
    have hr : r + 1 - 1 = r := by omega
    simpa only [g, regularPowerBatchedInitialMixedDegree,
      regularPowerBatchedCutChallengeDegree, regularPowerBatchedCutJetDegree, hr,
      Nat.card_eq_fintype_card, Fintype.card_fin] using hdegree
  have hd : (affineHilbertPolynomial (Ideal.span {g})).natDegree = r + 1 := by
    have hd := natDegree_affineHilbertPolynomial_span_singleton_add_one hinit' hproper
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
    omega
  rw [hd] at hbound
  have hbound' : (S.card : ℚ) ≤ affineDegree ((Ideal.span {g}).comap
      (bidegreeMap (Fin (r + 1)) E
        (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
        (regularPowerBatchedCutJetDegree K v (τ := τ)))) *
        hybridDimensionSensitiveIncidenceProduct n A L k 1 (min r k + 1) := by
    simpa only [Nat.add_sub_cancel] using hbound
  calc
    (S.card : ℚ) ≤ affineDegree ((Ideal.span {g}).comap
        (bidegreeMap (Fin (r + 1)) E
          (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
          (regularPowerBatchedCutJetDegree K v (τ := τ)))) *
        hybridDimensionSensitiveIncidenceProduct n A L k 1 (min r k + 1) := hbound'
    _ ≤ (regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
        hybridDimensionSensitiveIncidenceProduct n A L k 1 (min r k + 1) :=
      mul_le_mul_of_nonneg_right hdegree (by
        rw [hybridDimensionSensitiveIncidenceProduct_eq_factor_mul n A L k 1
          (min r k) hkA hAn (by omega)]
        exact mul_nonneg (div_nonneg (by positivity) (by positivity))
          (dimensionSensitiveIncidenceProduct_nonneg n A k 1 (min r k)))
    _ ≤ (regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
        ((((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          dimensionSensitiveIncidenceProduct n A k 1 r) :=
      mul_le_mul_of_nonneg_left
        (by
          simpa only [Nat.mul_one, Nat.cast_one, Nat.cast_mul] using
            hybridDimensionSensitiveIncidenceProduct_min_le n A L k 1 r
              hkA hAn one_pos) (by positivity)
    _ = _ := by ring

/-- Regular points outside admissible tuple graphs satisfy the sharp bidegree incidence bound at
arbitrary derivative order and every positive sufficient Taylor exponent. The terminal graph
recognition premise is discharged internally when `k ≤ L`. -/
theorem finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent
    {r : ℕ} [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
  have hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → jointInitialJetSeparant center Q ∉ J →
      jointInitialJetEquation center Q ∈ J →
      (∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ {i : Fin n | jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate fun t ↦ iota (w t i)) ∈ J}.ncard →
      {x | x ∈ zeroLocus E J ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
        admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
    intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_admissibleChartTupleGraphLocus
      domain w iota center Q K k L τ hK hkL hτ J hJ
    · exact hsJ
    · exact hdJ
    · exact hgJ
    · exact hhighJ
    · exact hcutsJ
  exact
    finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition
    domain w iota center Q K k L A v h τ hτ hτpos hK hkK (hkL.trans hLA) hLA hAn hD hv
    hinit hjet hheight hterminal S hS hA

/-- Regular points outside admissible tuple graphs satisfy the first-order bidegree incidence
bound at every sufficient Taylor exponent. -/
theorem finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ)
    (ha : 0 < regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A)
    (hv : 0 < v)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hjet : jetTotalDegree Q ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (S : Finset (Option (Fin 2) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ regularPowerBatchedInitialMixedDegreeTwo ℓ K v h (τ := τ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := jointInitialJetEquation center Q
  let s := jointInitialJetSeparant center Q
  let high := regularPowerBatchedHighCuts center Q K k τ
  let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))
  have hb : 0 < regularPowerBatchedCutJetDegree K v (τ := τ) := by
    simp only [regularPowerBatchedCutJetDegree]
    omega
  have hnotunit : ¬ IsUnit g := by
    intro hg
    have hevalunit : IsUnit (aeval x₀ g) := hg.map (MvPolynomial.aeval x₀)
    rw [(hS x₀ hx₀).1] at hevalunit
    exact not_isUnit_zero hevalunit
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) E)) ≠ ⊤ :=
    Ideal.span_singleton_ne_top hnotunit
  change (S.card : ℚ) ≤ (h * regularPowerBatchedCutJetDegree K v (τ := τ) ^ 2 +
    2 * v * regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) *
      regularPowerBatchedCutJetDegree K v (τ := τ) : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
  apply bidegreeHypersurface_incidence_off_excluded_hybrid_two
    (h := h) (v := v)
    ha hb hLA (hkL.trans hLA) g s hinit hproper
      (by simpa only [g, jointInitialJetEquation] using
        initialJetEquation_mem_restrictBidegree center Q h v hheight hjet)
      high ?_ cuts ?_
      (admissibleChartTupleGraphLocus domain w iota center Q K k L τ) ?_ ?_ S ?_ ?_
  · intro f hf
    simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨l, hl, rfl⟩ := hf
    exact jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
      center Q ℓ K h v τ hτ hv hheight hjet l
  · intro i
    exact jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
      center (iota (domain i)) (powerBatchedCoordinate (fun t ↦ iota (w t i)))
      Q ℓ K h v τ hτ (powerBatchedCoordinate_natDegree_le _) hv hheight hjet
  · intro J hJ hsJ hgJ hhighJ _hdJ
    have hhigh' : ∀ l : Fin K, k ≤ l.val →
        jointCommonTaylorNumerator center Q τ l ∈ J := by
      intro l hl
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hl, rfl⟩
    have hdim := symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK J hJ hsJ hhigh' ((domain.trans ⟨iota, iota.injective⟩))
        (fun i ↦ powerBatchedCoordinate (fun t ↦ iota (w t i)))
    simpa only [cuts, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk] using hdim
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_admissibleChartTupleGraphLocus
      domain w iota center Q K k L τ hK hkL hτ J hJ
    · simpa only [s] using hsJ
    · exact hdJ
    · simpa only [g] using hgJ
    · intro q hq
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨q, hq, rfl⟩
    · simpa only [cuts] using hcutsJ
  · intro x hx
    refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
    intro f hf
    simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨l, hl, rfl⟩ := hf
    exact (hS x hx).2.2.1 l hl
  · simpa only [cuts] using hA

open Classical in
/-- The finite bad-challenge count follows from supplied tuple and off-graph bounds. -/
theorem finite_powerBatchedBadChallenges_card_le_of_tuple_bound_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K) (hkL : k ≤ L)
    (tupleBound : ℚ)
    (htupleBound : ∀ T : Finset (Fin (ℓ + 1) → F[X]),
      (∀ P ∈ T, IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) →
      (T.card : ℚ) ≤ tupleBound)
    (offBound : ℚ)
    (hsourceBound : ∀ S : Finset (Option (Fin (r + 1)) → E),
      (∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
        x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ) →
      (∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) →
      (S.card : ℚ) ≤ offBound)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) * tupleBound := by
  let tuples := (polynomialTupleFamily domain w k).filter
    (IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ)
  have htuple (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (Finset.mem_filter.mp hP).2
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_exactPowerAgreement_family
    (k := k) (L := L) domain w iota tuples
      (fun P hP ↦ (htuple P hP).degree) (fun P hP ↦ (htuple P hP).common)
  let remaining := challenges \ exceptional
  let point : E → Option (Fin (r + 1)) → E := fun z i ↦ i.elim z (jet z)
  have hpointinj : Function.Injective point := by
    intro z z' heq
    exact congrFun heq none
  let S := remaining.image point
  have hcard : S.card = remaining.card := Finset.card_image_of_injective _ hpointinj
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    rintro ⟨P, hP, heq⟩
    have hjetEq : jet z = chartTupleJet iota center z P := by
      funext j
      exact congrFun heq (some j)
    have hs := (hchart z hzc).2.2.1
    have hregular :
        (chartTuplePullback iota center P (jointInitialJetSeparant center Q)).eval z ≠ 0 := by
      rw [eval_chartTuplePullback]
      rw [aeval_jointInitialJetSeparant_specialize]
      simpa [hjetEq] using hs
    have hrec := (hP.specialize hτ hkK z hregular).2.2.2
    have hw : witness z = powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hrec
    have hPmem : P ∈ tuples := by
      apply Finset.mem_filter.mpr
      exact ⟨mem_polynomialTupleFamily_of_commonAgreement domain w P k hP.degree
        (hkL.trans hP.common), hP⟩
    apply hbad z hzc
    rw [hw]
    exact hexact P hPmem z hze
  have hoffbound : (remaining.card : ℚ) ≤ offBound := by
    rw [← hcard]
    apply hsourceBound S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      refine ⟨?_, ?_, ?_, hoff z hz⟩
      · exact
          (aeval_jointInitialJetEquation_specialize center z Q (jet z)).trans
            (hchart z hzc).2.1
      · rw [aeval_jointInitialJetSeparant_specialize]
        exact (hchart z hzc).2.2.1
      · intro l hl
        rw [aeval_jointCommonTaylorNumerator_specialize]
        exact (hchart z hzc).2.2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      let domainE := domain.trans ⟨iota, iota.injective⟩
      let received := powerBatchedWord (fun t i ↦ iota (w t i)) z
      have hsubset :
          (polynomialAgreementSet domainE received (witness z) : Set (Fin n)) ⊆
            {i | aeval (point z) (jointTaylorAgreementEquation center Q K τ
              (Polynomial.C (iota (domain i)))
              (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0} := by
        intro i hi
        have hi' := (mem_polynomialAgreementSet domainE received (witness z) i).mp hi
        change aeval (point z) (jointTaylorAgreementEquation center Q K τ
          (Polynomial.C (iota (domain i)))
          (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0
        have heval : aeval (point z) (jointTaylorAgreementEquation center Q K τ
            (Polynomial.C (iota (domain i)))
            (powerBatchedCoordinate (fun t ↦ iota (w t i)))) =
          aeval (jet z) (taylorAgreementEquation center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) K τ (iota (domain i))
            (received i)) := by
          simpa only [point, received, powerBatchedWord] using
            aeval_jointTaylorAgreementEquation_specialize center z (iota (domain i))
              (fun t ↦ iota (w t i)) Q K τ (jet z)
        rw [heval, taylorAgreementEquation_eq_zero_iff center _ hτ (jet z)
            (hchart z hzc).2.2.1 (iota (domain i)) (received i),
          (hchart z hzc).2.2.2.2]
        exact hi'
      calc
        A ≤ (polynomialAgreementSet domainE received (witness z)).card := hagree z hzc
        _ = (polynomialAgreementSet domainE received (witness z) : Set (Fin n)).ncard :=
          (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hsubset
  have htuplebound := htupleBound tuples htuple
  have hexcbound : (exceptional.card : ℚ) ≤
      ((ℓ * (n - L) : ℕ) : ℚ) * tupleBound := by
    have he : (exceptional.card : ℚ) ≤
        (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
      have hexc' : exceptional.card ≤ tuples.card * (ℓ * (n - L)) := by
        simpa only [Fintype.card_fin] using hexc
      exact_mod_cast hexc'
    have hm := mul_le_mul_of_nonneg_right htuplebound
      (show (0 : ℚ) ≤ ((ℓ * (n - L) : ℕ) : ℚ) by positivity)
    calc
      (exceptional.card : ℚ) ≤ (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := he
      _ ≤ tupleBound * ((ℓ * (n - L) : ℕ) : ℚ) := hm
      _ = ((ℓ * (n - L) : ℕ) : ℚ) * tupleBound := by ring
  have hcover : challenges.card ≤ remaining.card + exceptional.card := by
    have he := Finset.card_sdiff_add_card_inter challenges exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      challenges ∩ exceptional ⊆ exceptional)
    dsimp only [remaining]
    omega
  have hcoverQ : (challenges.card : ℚ) ≤
      (remaining.card : ℚ) + (exceptional.card : ℚ) := by
    exact_mod_cast hcover
  exact hcoverQ.trans (add_le_add hoffbound hexcbound)


open Classical in
/-- The finite bad-challenge count combines an off-graph estimate with sharp tuple counting. -/
theorem finite_powerBatchedBadChallenges_card_le_of_off_graph_bound_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : jetTotalDegree Q ≤ v)
    (offBound : ℚ)
    (hsourceBound : ∀ S : Finset (Option (Fin (r + 1)) → E),
      (∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
        x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ) →
      (∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) →
      (S.card : ℚ) ≤ offBound)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
        (regularPowerBatchedCutJetDegree K v (τ := τ) : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n L k 1 r := by
  have htupleBound : ∀ T : Finset (Fin (ℓ + 1) → F[X]),
      (∀ P ∈ T, IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) →
      (T.card : ℚ) ≤
        (v : ℚ) * (regularPowerBatchedCutJetDegree K v (τ := τ) : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n L k 1 r := by
    intro T hT
    exact admissibleChartTuples_card_le_dimensionSensitive_of_exponent
      domain w iota center Q K k L v τ hτ hK hkK hkL (hLA.trans hAn) hjet T hT
  have hbound := finite_powerBatchedBadChallenges_card_le_of_tuple_bound_of_exponent
    domain w iota center Q K k L A τ hτ hkK hkL
    ((v : ℚ) * (regularPowerBatchedCutJetDegree K v (τ := τ) : ℚ) ^ r *
      dimensionSensitiveIncidenceProduct n L k 1 r) htupleBound offBound hsourceBound
    challenges witness jet hchart hagree hbad
  simpa only [mul_assoc] using hbound

open Classical in
/-- The exact fixed-center sharp agreement bound at arbitrary derivative order and a positive
sufficient Taylor exponent. -/
theorem finite_powerBatchedBadChallenges_card_le_sharp_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤
      regularPowerBatchedAgreementSharpBound r n ℓ K k L A v h (τ := τ) := by
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularPowerBatchedAgreementSharpBound
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r))
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
        (dimensionSensitiveIncidenceProduct_nonneg n L k 1 r))
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := jointInitialJetEquation_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  have hbound := finite_powerBatchedBadChallenges_card_le_of_off_graph_bound_of_exponent
    domain w iota center Q K k L A v τ hτ hK hkK hkL hLA hAn hjet
    ((regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k 1 r)
    (fun S hS hA ↦ by
      calc
        (S.card : ℚ) ≤ regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) *
            (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
              dimensionSensitiveIncidenceProduct n A k 1 r :=
          finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent
            domain w iota center Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
            hinit hjet hheight S hS hA
        _ = (regularPowerBatchedInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
            (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
              dimensionSensitiveIncidenceProduct n A k 1 r := rfl)
    challenges witness jet hchart hagree hbad
  simpa only [regularPowerBatchedAgreementSharpBound] using hbound

open Classical in
/-- Exact fixed-center first-order bad-challenge bound at a sufficient Taylor exponent.  The
joint term uses the direct dimension-sensitive factor, while the persistent-tuple term uses the
fixed-challenge coefficient-space factor. -/
theorem finite_powerBatchedBadChallenges_card_le_firstOrder_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ regularPowerBatchedAgreementSharpBoundTwo
      n ℓ K k L A v h (τ := τ)
        (η := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularPowerBatchedAgreementSharpBoundTwo
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := jointInitialJetEquation_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  have ha : 0 < regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ) := by
    unfold regularPowerBatchedCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      exact Nat.add_pos_right ℓ (Nat.mul_pos hτpos hh)
  unfold regularPowerBatchedAgreementSharpBoundTwo
  convert (finite_powerBatchedBadChallenges_card_le_of_off_graph_bound_of_exponent
      domain w iota center Q K k L A v τ hτ hK hkK hkL hLA hAn hjet
      ((regularPowerBatchedInitialMixedDegreeTwo ℓ K v h (τ := τ) : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)))
      (fun S hS hA ↦
        finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent
        domain w iota center Q K k L A v h τ hτ ha hK hkK hkL hLA hv
          hinit hjet hheight S hS hA)
      challenges witness jet hchart hagree hbad) using 1
  simp only [dimensionSensitiveIncidenceProduct, Nat.mul_one]
  push_cast
  ring

open Classical in
/-- Every finite subset of regular bad challenges satisfies the supplied fixed-center bound. -/
theorem finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k A τ : ℕ)
    (hkK : k ≤ K)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (bound : ℚ)
    (hfixedCenter : ∀ (center : E) (challenges : Finset E)
      (witness : E → E[X]) (jet : E → Fin (r + 1) → E),
      (∀ z ∈ challenges,
        let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
        (witness z).degree < k ∧
          aeval (jet z) (initialJetEquation center Qz) = 0 ∧
          aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
          (∀ l : Fin K, k ≤ l.val →
            aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
          rationalTaylorPolynomial center Qz K (jet z) = witness z) →
      (∀ z ∈ challenges,
        A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card) →
      (∀ z ∈ challenges,
        ¬ HasExactPowerAgreement domain w iota k z (witness z)) →
      (challenges.card : ℚ) ≤ bound)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ bound := by
  let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
  have hw (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
  have hdeg (z : E) (hz : z ∈ S) : (witness z).degree < k := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).1
  have hsol (z : E) (hz : z ∈ S) :
      differentialSpecialization (challengeSpecialization Q z) (witness z) = 0 := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.2.1
  have hsep (z : E) (hz : z ∈ S) : differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last r)) (witness z) ≠ 0 := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.2.2.1
  obtain ⟨center, hc⟩ := exists_forall_jetEvaluation_ne_zero_of_family S
    (fun z ↦ separant (challengeSpecialization Q z) (Fin.last r)) witness hsep
  apply hfixedCenter center S witness (fun z ↦ polynomialJet center (witness z))
  · intro z hz
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    have hQz : challengeSpecialization Q z = Qz := by
      simp [Qz, challengeSpecialization, Polynomial.evalRingHom]
    have hs := hc z hz
    have hsolz : differentialSpecialization Qz (witness z) = 0 := by
      rw [← hQz]
      exact hsol z hz
    have hsepz : jetEvaluation (separant Qz (Fin.last r)) center
        (polynomialJet center (witness z)) ≠ 0 := by
      rw [← hQz]
      exact hs
    have hd : (witness z).degree < K := (hdeg z hz).trans_le (Nat.cast_le.mpr hkK)
    refine ⟨hdeg z hz,
      aeval_initialJetEquation_polynomialJet center Qz (witness z) hsolz, ?_, ?_, ?_⟩
    · simpa only [aeval_initialJetSeparant] using hsepz
    · intro l hl
      change aeval (polynomialJet center (witness z))
        (commonTaylorNumerator center Qz τ l.val) = 0
      have hcoeff : (Polynomial.taylor center (witness z)).coeff l.val = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simpa only [Polynomial.degree_taylor] using
          (hdeg z hz).trans_le (Nat.cast_le.mpr hl)
      have hcoeffRat : rationalTaylorCoefficient center Qz
          (polynomialJet center (witness z)) l.val = 0 := by
        rw [rationalTaylorCoefficient_eq_solution center Qz
          (witness z) hsolz hsepz l.val]
        · exact hcoeff
        · intro i hir hil
          exact hbin i hir (lt_of_le_of_lt hil l.isLt)
      have hs' : aeval (polynomialJet center (witness z))
          (initialJetSeparant center Qz) ≠ 0 := by
        simpa only [aeval_initialJetSeparant] using hsepz
      exact aeval_commonTaylorNumerator_eq_zero center Qz
        (polynomialJet center (witness z)) τ hs' hcoeffRat
    · exact rationalTaylorPolynomial_polynomialJet center Qz
        (witness z) hsolz hsepz hd hbin
  · intro z hz
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.2.2.2

open Classical in
/-- Every finite set of regular bad challenges satisfies the sharp dimension-sensitive bound at
arbitrary derivative order and a positive sufficient Taylor exponent. -/
theorem finite_regularPowerBatchedBadChallenges_card_le_sharp_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularPowerBatchedAgreementSharpBound r n ℓ K k L A v h (τ := τ) := by
  apply finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent
    domain w iota Q K k A τ hkK hbin
      (regularPowerBatchedAgreementSharpBound r n ℓ K k L A v h (τ := τ)) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_powerBatchedBadChallenges_card_le_sharp_of_exponent
    domain w iota center Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
      hjet hheight challenges witness jet hchart hagree hbad

open Classical in
/-- A single sharply bounded exceptional set works for every regular order-`r` solution at a
positive sufficient Taylor exponent. -/
theorem exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent
    {r : ℕ} [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        regularPowerBatchedAgreementSharpBound r n ℓ K k L A v h (τ := τ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  have hfinite :
      (regularPowerBatchedBadChallenges domain w iota Q k A).Finite := by
    apply Set.finite_of_forall_finset_card_le (R := ℚ) fun S hS ↦
      finite_regularPowerBatchedBadChallenges_card_le_sharp_of_exponent
        domain w iota Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
        hjet hheight hbin S hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularPowerBatchedBadChallenges_card_le_sharp_of_exponent
      domain w iota Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
      hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

open Classical in
/-- Every finite set of regular first-order bad challenges satisfies the exact
dimension-sensitive bound at the supplied Taylor exponent. -/
theorem finite_regularPowerBatchedBadChallenges_card_le_firstOrder_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularPowerBatchedAgreementSharpBoundTwo
      n ℓ K k L A v h (τ := τ)
        (η := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  apply finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent
    domain w iota Q K k A τ hkK hbin
      (regularPowerBatchedAgreementSharpBoundTwo n ℓ K k L A v h (τ := τ)
        (η := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_powerBatchedBadChallenges_card_le_firstOrder_of_exponent
    domain w iota center Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
      hjet hheight challenges witness jet hchart hagree hbad

open Classical in
/-- A single dimension-sensitively bounded exceptional set works for every regular first-order
solution at the supplied Taylor exponent.  The conclusion retains the exact full agreement-set
equality through `HasExactPowerAgreement`. -/
theorem exists_exceptional_regularPowerBatchedAgreement_firstOrder_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularPowerBatchedAgreementSharpBoundTwo
        n ℓ K k L A v h (τ := τ)
          (η := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet ((domain.trans ⟨iota, iota.injective⟩))
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  have hfinite :
      (regularPowerBatchedBadChallenges domain w iota Q k A).Finite := by
    apply Set.finite_of_forall_finset_card_le (R := ℚ) fun S hS ↦
      finite_regularPowerBatchedBadChallenges_card_le_firstOrder_of_exponent
      domain w iota Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
        hjet hheight hbin S hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularPowerBatchedBadChallenges_card_le_firstOrder_of_exponent
      domain w iota Q K k L A v h τ hτ hτpos hK hkK hkL hLA hAn hD hv
        hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
