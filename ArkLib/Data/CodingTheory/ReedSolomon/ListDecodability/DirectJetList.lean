/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.Polynomial.Differential.SeparantChain
public import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
public import ArkLib.Data.Polynomial.Differential.WitnessCount
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension
public import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Direct jet-list bounds along separant chains

For a differential equation, the agreement solutions split into regular roots at each stage and
roots of the next separant. A regular stage of jet weight `j` and order `r` contributes at most
`dimensionSensitiveIncidenceProduct n A k 1 r * j * (1 + 2 * K * (j - 1)) ^ r`. Strict descent
of the jet weight then bounds the sum of actual charges by a common-order sum.

## Main statements

* `finite_actualStage_regularSolutions_card_le_dimensionSensitive` bounds a regular family at
  its actual separant stage.
* `finset_card_le_directJetStageCharge_sum` and
  `directJetAgreementSolutions_finite_and_ncard_le_chain` sum those bounds along a chain.
* `directJetStageCharge_sum_le_commonOrderSum` and `directJetCommonOrderSum_le_coarse` compare
  the actual-stage sum with a uniform charge and the resulting coarse bound.
* `exists_directJetList_actualStages_and_bounds` supplies a chain and all three bounds under a
  characteristic hypothesis.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {d : ℕ}

private theorem regularHighTaylorJets_card_le_dimensionSensitive
    [IsAlgClosed F] {r : ℕ} (center : F) (Q : DifferentialPolynomial F r)
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (hsep : initialJetSeparant center Q ≠ 0)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l, k ≤ l → l < K →
        aeval jet (commonTaylorNumerator center Q τ l) = 0)
    (hA : ∀ jet ∈ S, A ≤
      {i | aeval jet (taylorAgreementEquation center Q K τ
        (domain i) (received i)) = 0}.ncard) :
    (S.card : ℚ) ≤ (jetTotalDegree Q : ℚ) *
      (rationalTaylorCutDegreeBound Q τ : ℚ) ^ r *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  let B := rationalTaylorCutDegreeBound Q τ
  let T := highTaylorPrimeFamily center Q K k τ
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) F := fun i ↦
    taylorAgreementEquation center Q K τ (domain i) (received i)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center Q hsep
  have hcoverNat : S.card ≤ ∑ P ∈ T,
      (S.filter fun jet ↦ jet ∈ zeroLocus F P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ S.filter fun jet ↦ jet ∈ zeroLocus F P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := exists_mem_highTaylorPrimeFamily_of_regular
          center Q (K := K) (k := k) (τ := τ) jet
          (hS jet hjet).1 (hS jet hjet).2.1
          (fun l hkl hlK ↦ hS jet hjet |>.2.2 l hkl hlK)
        exact Finset.mem_biUnion.mpr ⟨P, hPT,
          Finset.mem_filter.mpr ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (S.filter fun jet ↦ jet ∈ zeroLocus F P).card :=
        Finset.card_biUnion_le
  have hcomponent : ∀ P ∈ T,
      ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) ≤
        affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r := by
    intro P hPT
    have hPprime : P.IsPrime := isPrime_of_mem_highTaylorPrimeFamily hPT
    have hhigh : highTaylorCutsIdeal center Q K k τ ≤ P :=
      highTaylorCutsIdeal_le_of_mem_highTaylorPrimeFamily hPT
    have hbound := MvPolynomial.card_le_dimensionSensitiveIncidenceProduct_of_agreement
      (P := P) (initialJetSeparant center Q) cuts
      (fun i ↦ totalDegree_taylorAgreementEquation_le center Q hτ _ _)
      hkA (fun J hPJ hJ hsJ hdJ ↦
        have hhighJ := hhigh.trans hPJ
        ReedSolomon.chart_dimensionSensitive_component_of_exponent
          center Q K k n τ hτ hK hkK J hJ hsJ
          (fun l hl ↦ hhighJ <| by
            rw [highTaylorCutsIdeal]
            exact Ideal.subset_span
              ⟨l.val, ⟨hl, l.isLt⟩, rfl⟩)
          domain received hdJ)
      (S.filter fun jet ↦ jet ∈ zeroLocus F P)
      (fun jet hj ↦ by
        rw [Finset.mem_filter] at hj
        exact ⟨hj.2, (hS jet hj.1).2.1⟩)
      (fun jet hj ↦ hA jet (Finset.mem_filter.mp hj).1)
    have hdim : (affineHilbertPolynomial P).natDegree ≤ r :=
      natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily hPT
    have hproductMono := dimensionSensitiveIncidenceProduct_mono_dimension
      (n := n) (A := A) (k := k) (b := 1) hAn Nat.zero_lt_one
    have hproduct := hproductMono hdim
    have hbound' :
        ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) ≤
          affineDegree P * dimensionSensitiveIncidenceProduct n A k B
            (affineHilbertPolynomial P).natDegree := by
      simpa [B] using hbound
    calc
      ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) ≤
          affineDegree P * dimensionSensitiveIncidenceProduct n A k B
            (affineHilbertPolynomial P).natDegree := hbound'
      _ = affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 (affineHilbertPolynomial P).natDegree := by
        rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
        ring
      _ ≤ affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r :=
        mul_le_mul_of_nonneg_left hproduct
          (mul_nonneg (affineDegree_nonneg P) (by positivity))
      _ = _ := by ring
  have hpotential := sum_affineDegree_mul_pow_highTaylorPrimeFamily_le
    (k := k) center Q hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T,
        ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^
          (affineHilbertPolynomial P).natDegree *
            dimensionSensitiveIncidenceProduct n A k 1 r :=
      Finset.sum_le_sum hcomponent
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^
          (affineHilbertPolynomial P).natDegree) *
            dimensionSensitiveIncidenceProduct n A k 1 r := by
      rw [Finset.sum_mul]
    _ ≤ ((jetTotalDegree Q : ℚ) * (B : ℚ) ^ r) *
          dimensionSensitiveIncidenceProduct n A k 1 r :=
      mul_le_mul_of_nonneg_right hpotential
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
    _ = _ := by ring

/-- The degree-`< k` agreement polynomials that solve one differential equation. -/
def directJetAgreementSolutions {n : ℕ} (Q : DifferentialPolynomial F d)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Set F[X] := by
  classical
  exact {P | differentialSpecialization Q P = 0 ∧ P ∈ ReedSolomon.closePolynomialSet
    domain received k A}

/-- The charge of one actual stage of the separant chain. -/
def directJetStageCharge (domainSize A k K : ℕ)
    (stage : SeparantStage F d) : ℚ :=
  dimensionSensitiveIncidenceProduct domainSize A k 1 stage.2.val *
    (jetTotalDegree stage.1 : ℚ) *
      (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ stage.2.val

/-- The common-order sum charges each possible positive jet weight up to `B`. -/
def directJetCommonOrderSum (n A k K B d : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (B + 1),
    dimensionSensitiveIncidenceProduct n A k 1 d * (j : ℚ) *
      (1 + 2 * K * (j - 1) : ℕ) ^ d

/-- A regular family at an actual stage is bounded using its current jet weight and order. -/
theorem finite_actualStage_regularSolutions_card_le_dimensionSensitive
    (current : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hhighest : highestActiveJet current = some s)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant current s) P ≠ 0)
    (hagree : ∀ P ∈ S,
      P ∈ directJetAgreementSolutions current domain received k A) :
    (S.card : ℚ) ≤ directJetStageCharge n A k K (current, s) := by
  classical
  have hdegree : ∀ P ∈ S, P.degree < k := by
    intro P hP
    exact ((hagree P hP).2).1
  have hsol : ∀ P ∈ S, differentialSpecialization current P = 0 := by
    intro P hP
    exact (hagree P hP).1
  obtain ⟨presentation⟩ := nonempty_jetPrefixPresentation current
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let Q' := presentation.equation
  have hsle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
  have hweight : jetTotalDegree Q' = jetTotalDegree current :=
    presentation.jetTotalDegree_equation
  have hactive : 0 < jetDegree Q' (Fin.last s.val) := by
    rw [presentation.jetDegree_equation_last]
    exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
  have hv : 0 < jetTotalDegree Q' := hactive.trans_le (jetDegree_le_total Q' _)
  let E := AlgebraicClosure F
  let f : F →+* E := algebraMap F E
  let QE := MvPolynomial.map f Q'
  have hbinE : ∀ i, s.val < i → i < K → (i.choose s.val : E) ≠ 0 := by
    intro i hir hiK hz
    apply hbin s.val hsle i hir hiK
    exact f.injective (by simpa using hz)
  have hagreement (P : F[X]) (hP : P ∈ S) :
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
    have hclose := (hagree P hP).2
    simpa [ReedSolomon.closePolynomialSet, ReedSolomon.polynomialAgreementSet] using
      hclose.2
  have hfilter (P : F[X]) :
      Finset.univ.filter (fun i : Fin n ↦ P.eval (domain i) = received i) =
        @Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
          (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ := by
    exact (Finset.filter_congr_decidable Finset.univ
      (fun i : Fin n ↦ P.eval (domain i) = received i)
      (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i))).symm
  have hagree' : ∀ P ∈ S,
      A ≤ (@Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
        (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ).card := by
    intro P hP
    rw [← hfilter P]
    exact hagreement P hP
  obtain ⟨center, J, hcard, hJ⟩ :=
    exists_regular_solution_jet_family_of_exponent
      (f := f) (Q := Q') (K := K) (k := k) (τ := 2 * K)
      (hτ := taylorExponentSufficient_two_mul s.val K) (hkK := hkK) (S := S)
      (A := A) (ι := Fin n) (domain := domain) (received := received)
      (hdegree := hdegree)
      (hsol := fun P hP ↦ by
      simpa only [← presentation.differentialSpecialization_equation] using hsol P hP)
      (hsep := fun P hP ↦ by
      have heq := presentation.differentialSpecialization_separant_equation P
      exact heq.symm ▸ hsep P hP)
      (hbin := hbinE) (hagree := hagree')
  by_cases hJempty : J = ∅
  · have hScard : S.card = 0 := by simpa [hJempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 s.val)
        (Nat.cast_nonneg _)) (by positivity)
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjet⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    intro hz
    exact (hJ jet hjet).2.1 (by rw [hz, map_zero])
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := regularHighTaylorJets_card_le_dimensionSensitive
    center QE K k (2 * K) (taylorExponentSufficient_two_mul s.val K) (by omega) hkK hsepE
    domainE (fun i ↦ f (received i)) hkA hAn J
    (fun jet hjet ↦ ⟨(hJ jet hjet).1, (hJ jet hjet).2.1,
      fun l hkl hlK ↦ (hJ jet hjet).2.2.1 ⟨l, hlK⟩ hkl⟩)
    (fun jet hjet ↦ by
      let agreementSet := Finset.univ.filter (fun i ↦
        aeval jet (taylorAgreementEquation center ((MvPolynomial.map f) Q') K (2 * K)
          (f (domain i)) (f (received i))) = 0)
      have hset : ({i | aeval jet (taylorAgreementEquation center QE K (2 * K)
          (domainE i) (f (received i))) = 0} : Set (Fin n)) =
          (agreementSet : Set (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, agreementSet, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_univ, true_and]
        change (aeval jet (taylorAgreementEquation center QE K (2 * K)
          (f (domain i)) (f (received i))) = 0) ↔ _
        rfl
      rw [hset, Set.ncard_coe_finset]
      exact (hJ jet hjet).2.2.2)
  rw [hcard] at hcount
  have hregular : (S.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) *
      (rationalTaylorCutDegreeBound Q' (2 * K) : ℚ) ^ s.val *
        dimensionSensitiveIncidenceProduct n A k 1 s.val := by
    simpa only [QE, rationalTaylorCutDegreeBound, jetTotalDegree_map_eq f.injective] using hcount
  have hB : rationalTaylorCutDegreeBound Q' (2 * K) =
      1 + 2 * K * (jetTotalDegree current - 1) := by
    simp [rationalTaylorCutDegreeBound, hweight]
  calc
    (S.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) *
        (rationalTaylorCutDegreeBound Q' (2 * K) : ℚ) ^ s.val *
          dimensionSensitiveIncidenceProduct n A k 1 s.val := hregular
    _ = directJetStageCharge n A k K (current, s) := by
      simp [directJetStageCharge, hweight, hB]
      ring

/-- Every finite family of accepted roots is bounded by the sum of its actual-stage charges. -/
theorem finset_card_le_directJetStageCharge_sum
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SeparantStage F d)}
    (hchain : SeparantChain Q stages terminal)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received k A) :
    (S.card : ℚ) ≤ (stages.map (directJetStageCharge n A k K)).sum := by
  classical
  induction hchain generalizing S with
  | @terminal equation hne hterminal =>
      have hEmpty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro P hP
        obtain ⟨q, hqne, hq⟩ :=
          (SeparantChain.terminal hne hterminal).exists_toMvPolynomial_eq_terminal
        have hqzero : q ≠ 0 := by
          intro hz
          apply hne
          rw [← hq, hz]
          simp
        apply hqzero
        rw [← differentialSpecialization_toMvPolynomial (d := d) q P, hq]
        exact (hS P hP).1
      subst S
      simp
  | @active current tail terminal s hne hhighest next ih =>
      let regular := S.filter fun P ↦
        differentialSpecialization (separant current s) P ≠ 0
      let singular := S.filter fun P ↦
        ¬ differentialSpecialization (separant current s) P ≠ 0
      have hregular := finite_actualStage_regularSolutions_card_le_dimensionSensitive
        current s hhighest K k hK hkK domain received hkA hAn hbin regular
        (fun P hP ↦ (Finset.mem_filter.mp hP).2)
        (fun P hP ↦ hS P (Finset.mem_filter.mp hP).1)
      have hsingularAccept :
          ∀ P ∈ singular, P ∈ directJetAgreementSolutions (separant current s)
            domain received k A := by
        intro P hP
        have hm := Finset.mem_filter.mp hP
        exact ⟨not_ne_iff.mp hm.2, (hS P hm.1).2⟩
      have hsingular := ih singular hsingularAccept
      have hpartition : regular.card + singular.card = S.card := by
        exact Finset.card_filter_add_card_filter_not
          (s := S) (p := fun P ↦ differentialSpecialization (separant current s) P ≠ 0)
      simp only [List.map_cons, List.sum_cons]
      calc
        (S.card : ℚ) = (regular.card : ℚ) + (singular.card : ℚ) := by
          exact_mod_cast hpartition.symm
        _ ≤ directJetStageCharge n A k K (current, s) +
            (tail.map (directJetStageCharge n A k K)).sum :=
          add_le_add hregular hsingular

/-- The complete agreement solution set is finite and satisfies its actual-chain bound. -/
theorem directJetAgreementSolutions_finite_and_ncard_le_chain
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SeparantStage F d)}
    (hchain : SeparantChain Q stages terminal)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum := by
  classical
  let T := directJetAgreementSolutions Q domain received k A
  have hbound (S : Finset F[X]) (hST : (S : Set F[X]) ⊆ T) :
      (S.card : ℚ) ≤ (stages.map (directJetStageCharge n A k K)).sum :=
    finset_card_le_directJetStageCharge_sum hchain K k hK hkK domain received
      hkA hAn hbin S (fun P hP ↦ hST hP)
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ h ↦ hfinite.mem_toFinset.mp h)

/-- The actual-stage charge is bounded by the common-order sum over all possible weights. -/
theorem directJetStageCharge_sum_le_commonOrderSum
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SeparantStage F d)}
    (hchain : SeparantChain Q stages terminal)
    (n A k K B : ℕ) (hAn : A ≤ n) (hweight : jetTotalDegree Q ≤ B) :
    (stages.map (directJetStageCharge n A k K)).sum ≤
      directJetCommonOrderSum n A k K B d := by
  classical
  let f : ℕ → ℚ := fun j ↦
    dimensionSensitiveIncidenceProduct n A k 1 d * (j : ℚ) *
      (1 + 2 * K * (j - 1) : ℕ) ^ d
  have hpoint : ∀ stage ∈ stages,
      directJetStageCharge n A k K stage ≤ f (jetTotalDegree stage.1) := by
    intro stage hstage
    have htotal := hchain.jetTotalDegree_le_of_mem hstage
    have hr : stage.2.val ≤ d := Nat.le_of_lt_succ stage.2.isLt
    have hpMono := dimensionSensitiveIncidenceProduct_mono_dimension
      (n := n) (A := A) (k := k) (b := 1) hAn Nat.zero_lt_one
    have hp := hpMono hr
    have hb : (1 : ℚ) ≤
        (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) := by
      exact_mod_cast (Nat.le_add_right 1 _)
    dsimp only [directJetStageCharge, f]
    calc
      dimensionSensitiveIncidenceProduct n A k 1 stage.2.val *
          (jetTotalDegree stage.1 : ℚ) *
            (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ stage.2.val ≤
        dimensionSensitiveIncidenceProduct n A k 1 d *
          (jetTotalDegree stage.1 : ℚ) *
            (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ stage.2.val := by
          gcongr
      _ ≤ dimensionSensitiveIncidenceProduct n A k 1 d *
          (jetTotalDegree stage.1 : ℚ) *
            (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ d := by
          gcongr
          exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
            (Nat.cast_nonneg _)
  have hstageSum : (stages.map (directJetStageCharge n A k K)).sum ≤
      (stages.map fun stage ↦ f (jetTotalDegree stage.1)).sum :=
    List.sum_le_sum hpoint
  let weights := stages.map fun stage ↦ jetTotalDegree stage.1
  have hweightsPairwise : weights.Pairwise (· > ·) := by
    dsimp only [weights]
    rw [List.pairwise_map]
    exact hchain.pairwise_stages.imp fun h ↦ h.1
  have hweightsNodup : weights.Nodup := hweightsPairwise.nodup
  have hweightsSubset : weights.toFinset ⊆ Finset.range (B + 1) := by
    intro j hj
    rw [List.mem_toFinset] at hj
    obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hchain.jetTotalDegree_le_of_mem hstage).trans hweight)
  calc
    (stages.map (directJetStageCharge n A k K)).sum ≤
        (stages.map fun stage ↦ f (jetTotalDegree stage.1)).sum := hstageSum
    _ = (weights.map f).sum := by simp [weights, List.map_map, Function.comp_def]
    _ = ∑ j ∈ weights.toFinset, f j := (List.sum_toFinset f hweightsNodup).symm
    _ ≤ ∑ j ∈ Finset.range (B + 1), f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hweightsSubset (fun _ _ _ ↦ by
        dsimp only [f]
        exact mul_nonneg
          (mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
            (Nat.cast_nonneg _)) (by positivity))
    _ = directJetCommonOrderSum n A k K B d := by
      simp only [directJetCommonOrderSum, f]

/-- The common-order sum satisfies the square-weight coarse estimate. -/
theorem directJetCommonOrderSum_le_coarse
    (n A k K B d : ℕ) (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n) :
    directJetCommonOrderSum n A k K B d ≤
      (B : ℚ) ^ 2 *
        ((((n * (1 + 2 * K * (B - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  let P := dimensionSensitiveIncidenceProduct n A k 1 d
  let b := 1 + 2 * K * (B - 1)
  let R : ℚ := ((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hterm : ∀ i ∈ Finset.range B,
      P * ((i + 1 : ℕ) : ℚ) * (1 + 2 * K * ((i + 1) - 1) : ℕ) ^ d ≤
        P * (B : ℚ) * (b : ℚ) ^ d := by
    intro i hi
    have hiB : i + 1 ≤ B := Nat.succ_le_iff.mpr (by
      simpa only [Finset.mem_range] using hi)
    have hiPred : i ≤ B - 1 := by omega
    have hbase : 1 + 2 * K * ((i + 1) - 1) ≤ b := by
      dsimp only [b]
      rw [show (i + 1 : ℕ) - 1 = i by omega]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K) hiPred) 1
    dsimp only [P]
    gcongr
    · exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
        (Nat.cast_nonneg _)
    · exact dimensionSensitiveIncidenceProduct_nonneg n A k 1 d
  have hproduct := dimensionSensitiveIncidenceProduct_le_first_pow n A k d hkA hAn
  have hratio : ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) ≤
      (n : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
    gcongr
    exact_mod_cast (show n - k + 1 ≤ n by omega)
  have hproductN : P ≤ (((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d) :=
    hproduct.trans (pow_le_pow_left₀ (by positivity) hratio d)
  have hR : R = (b : ℚ) * ((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
    dsimp only [R]
    push_cast
    ring
  calc
    directJetCommonOrderSum n A k K B d =
        ∑ i ∈ Finset.range B,
          P * ((i + 1 : ℕ) : ℚ) *
            (1 + 2 * K * ((i + 1) - 1) : ℕ) ^ d := by
      rw [directJetCommonOrderSum, Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, P]
    _ ≤ ∑ _i ∈ Finset.range B, P * (B : ℚ) * (b : ℚ) ^ d :=
      Finset.sum_le_sum hterm
    _ = (B : ℚ) * (P * (B : ℚ) * (b : ℚ) ^ d) := by simp
    _ = (B : ℚ) ^ 2 * (b : ℚ) ^ d * P := by ring
    _ ≤ (B : ℚ) ^ 2 * (b : ℚ) ^ d *
        (((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
      exact mul_le_mul_of_nonneg_left hproductN
        (mul_nonneg (by positivity) (by positivity))
    _ = (B : ℚ) ^ 2 * R ^ d := by
      rw [hR, mul_pow]
      ring
    _ = _ := by rfl

/-- Characteristic bounds produce a separant chain and its direct finite-list estimate. -/
theorem exists_chain_directJetAgreementSolutions_finite_and_ncard_le
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) (jetTotalDegree Q) < ringChar F) :
    ∃ stages terminal, SeparantChain Q stages terminal ∧
      (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum := by
  obtain ⟨hchainChar, hcutChar⟩ := characteristic_bounds_of_max hchar
  have hchain := exists_separantChain_of_ringChar hQ hchainChar
  have hcutChar' : ringChar F = 0 ∨ K - 1 < ringChar F := hcutChar.imp_right (by omega)
  have hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hir hiK
    have hchoose := natCast_choose_ne_zero_of_ringChar
      (D := K - 1) (s := r) hcutChar' (i - r) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hir)] using hchoose
  obtain ⟨stages, terminal, hchain⟩ := hchain
  obtain ⟨hfinite, hbound⟩ := directJetAgreementSolutions_finite_and_ncard_le_chain
    hchain K k hK hkK domain received hkA hAn hbin
  exact ⟨stages, terminal, hchain, hfinite, hbound⟩

/-- A chain witnesses the exact-stage, common-order, and coarse agreement-list bounds. -/
theorem exists_directJetList_actualStages_and_bounds
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k B : ℕ) (hK : d < K) (hk : 0 < k) (hkK : k ≤ K)
    (hweight : jetTotalDegree Q ≤ B)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) B < ringChar F) :
    ∃ stages terminal, SeparantChain Q stages terminal ∧
      (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum ∧
      (stages.map (directJetStageCharge n A k K)).sum ≤
        directJetCommonOrderSum n A k K B d ∧
      directJetCommonOrderSum n A k K B d ≤
        (B : ℚ) ^ 2 *
          ((((n * (1 + 2 * K * (B - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (jetTotalDegree Q) < ringChar F := by
    apply hchar.imp_right
    intro hc
    exact max_lt
      ((Nat.le_max_left (K - 1) B).trans_lt hc)
      (hweight.trans_lt ((Nat.le_max_right (K - 1) B).trans_lt hc))
  obtain ⟨stages, terminal, hchain, hfinite, hactual⟩ :=
    exists_chain_directJetAgreementSolutions_finite_and_ncard_le
      Q hQ K k hK hkK domain received hkA hAn hchar'
  have hcommon := directJetStageCharge_sum_le_commonOrderSum
    hchain n A k K B hAn hweight
  have hcoarse := directJetCommonOrderSum_le_coarse n A k K B d hk hkA hAn
  exact ⟨stages, terminal, hchain, hfinite, hactual, hcommon, hcoarse⟩

end

end ReedSolomon.HiddenDerivative
