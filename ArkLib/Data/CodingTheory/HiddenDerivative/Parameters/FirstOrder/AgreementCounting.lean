/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.DerivativeCappedCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import ArkLib.Data.Polynomial.Differential.FirstOrderStageSum
public import ArkLib.Data.Polynomial.Differential.RecursiveCount
public import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
public import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Cap-sensitive first-order agreement list bounds

For a first-order differential equation, regular branches headed by `Y₀` cost their total jet
degree, while branches headed by `Y₁` cost the derivative-capped Taylor incidence degree times
the sharp agreement ratio. Summing these charges along a separant chain gives a bound sensitive
to the total jet degree and the degree in `Y₁`. The exact-exponent bound specializes to the
uniform cap-sensitive bound at exponent `2 * K`.

## Main statements

* `firstOrderListWeight` and `firstOrderTightListWeight`: uniform and exact stage-charge sums.
* `firstOrderTightListWeight_nonneg`: nonnegativity of the exact charge.
* `finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent`: the regular-solution
  derivative-capped count.
* `finite_regular_agreement_solutions_card_le_identityPair`: the degree-one identity-pair count.
* `finite_regular_agreement_solutions_card_le_regularTaylor`: the regular Taylor count.
* `finite_firstOrder_agreement_solutions_card_le_tight_of_exponent`: the exact-exponent count.
* `firstOrderTightListWeight_two_mul_le` and
  `finite_firstOrder_agreement_solutions_card_le_sharp`: the uniform comparison and count.

## References

* [DKTZ26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial PolynomialDifferential
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The uniform first-order list charge: order-zero stages contribute their degree, and the
highest `min M μ` stages use the full Taylor degree factor `1 + 2 * K * (j - 1)`. -/
def firstOrderListWeight (K : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1) + firstOrderListWeight K μ 0
  | μ + 1, M + 1 =>
      (μ + 1) * (1 + 2 * K * μ) + firstOrderListWeight K μ M

/-- The exact first-order list charge. Order-zero stages contribute their degree, while each
order-one stage uses its derivative-capped Taylor incidence degree and agreement ratio. -/
def firstOrderTightListWeight (n A k K τ : ℕ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1 : ℚ) + firstOrderTightListWeight n A k K τ μ 0
  | μ + 1, M + 1 =>
      (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1)) τ : ℚ) *
          ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) +
        firstOrderTightListWeight n A k K τ μ M

private theorem firstOrderTightListWeight_eq_stageCap (n A k K τ μ M : ℕ) :
    firstOrderTightListWeight n A k K τ μ M =
      firstOrderStageCap (fun j ↦ (j : ℚ))
        (fun j r ↦ (firstOrderCurveFiberStageOne K j r τ : ℚ) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))) μ M := by
  induction μ generalizing M with
  | zero => simp [firstOrderTightListWeight, firstOrderStageCap]
  | succ μ ih =>
      cases M with
      | zero =>
          rw [firstOrderTightListWeight, firstOrderStageCap_succ_zero]
          simpa only [Nat.cast_add, Nat.cast_one] using congrArg
            (fun x : ℚ ↦ (μ + 1 : ℚ) + x) (ih 0)
      | succ M =>
          rw [firstOrderTightListWeight, firstOrderStageCap_succ_succ]
          rw [ih M]
          ring

/-- The exact first-order list charge is nonnegative. -/
theorem firstOrderTightListWeight_nonneg (n A k K τ μ M : ℕ) :
    0 ≤ firstOrderTightListWeight n A k K τ μ M := by
  rw [firstOrderTightListWeight_eq_stageCap]
  exact firstOrderStageCap_nonneg (fun _ ↦ by positivity) (fun _ _ ↦ by positivity) μ M

private theorem agreement_ncard_eq_filter_card {n : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (P : F[X]) :
    ({i : Fin n | P.eval (domain i) = received i}).ncard =
      (@Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
        (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ).card := by
  classical
  have hset : ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)) =
      (@Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
        (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ :
          Finset (Fin n)) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset]

private theorem regularSolutions_card_le_of_agreement_orderZero
    (current : DifferentialPolynomial F 1) (hhighest : highestActiveJet current = some 0)
    (K k τ ν : ℕ) (hτ : TaylorExponentSufficient 0 K τ) (hk : 0 < k) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n) (hdegree : jetTotalDegree current ≤ ν)
    {D : ℕ} (regular : Finset (BoundedSolution current D))
    (haccept : ∀ solution ∈ regular,
      solution.polynomial.degree < k ∧
        A ≤ ({i : Fin n | solution.polynomial.eval (domain i) = received i}).ncard)
    (hseparant : ∀ solution ∈ regular,
      differentialSpecialization (separant current 0) solution.polynomial ≠ 0) :
    (regular.card : ℚ) ≤ ν := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective
      (fun solution : BoundedSolution current D ↦ solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card :=
    Finset.card_image_of_injective regular hinjective
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding (0 : Fin 2) Q', hQ']
    exact hdegree
  have hstage := card_le_of_regular_solutions_agreement (E := AlgebraicClosure F)
    Q' K k τ hτ (lt_of_lt_of_le hk hkK) hkK domain received hkA hAn polys
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccept solution hsolution).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      have heqsep :
          differentialSpecialization (separant current (0 : Fin 2)) solution.polynomial =
            differentialSpecialization (separant Q' (Fin.last (0 : Fin 2).val))
              solution.polynomial := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2))
                (separant Q' (Fin.last (0 : Fin 2).val))) solution.polynomial := by
              rw [← separant_rename_jetPrefixEmbedding, hQ']
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hs (heqsep.trans hz))
    (fun i hi hiK ↦ by simp)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have h := (haccept solution hsolution).2
      rw [agreement_ncard_eq_filter_card domain received] at h
      exact h)
  rw [hcard] at hstage
  have hstage' : (regular.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) := by
    simpa using hstage
  exact hstage'.trans (by exact_mod_cast hQ'Degree)

open Classical in
/-- A finite regular family of accepted first-order solutions is bounded by its derivative-capped
Taylor incidence charge. -/
theorem finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
    (Q : DifferentialPolynomial F 1) (K k j r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ) (hK : 1 < K)
    (hkK : k ≤ K) (hr : 0 < r) (hrj : r ≤ j)
    (hjet : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 1 ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (regular : Finset (Polynomial F))
    (hdegree : ∀ P ∈ regular, P.degree < k)
    (hsol : ∀ P ∈ regular, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ regular, differentialSpecialization (separant Q 1) P ≠ 0)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0)
    (hagree : ∀ P ∈ regular,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (regular.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := AlgebraicClosure F
  let f := algebraMap F E
  let QE := MvPolynomial.map f Q
  have hbinE : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiK hz
    apply hbin i hi hiK
    exact f.injective (by simpa using hz)
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family_of_exponent
    f Q K k τ hτ hkK regular domain received hdegree hsol hsep hbinE hagree
  by_cases hJempty : J = ∅
  · have hScard : regular.card = 0 := by simpa [hJempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
      center QE K k j r τ hτ hτpos hK hr hrj
      (by
        have hjetMapped : jetTotalDegree QE ≤ j := by
          simpa only [QE, jetTotalDegree_map_eq f.injective] using hjet
        have hw : (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) = jetDegreeWeight := by
          funext i
          cases i <;> rfl
        rw [hw]
        exact hjetMapped)
      (by
        change jetDegree QE 1 ≤ r
        simpa only [QE, jetDegree_map_eq f.injective Q 1] using hderiv)
      domainE (fun i ↦ f (received i)) hkA hAn J
      (fun jet hjetmem ↦ ⟨(hJ jet hjetmem).1, (hJ jet hjetmem).2.1,
        fun l ↦ (hJ jet hjetmem).2.2.1 l.val l.property⟩)
      (fun jet hjetmem ↦ by
        let agreementSet : Finset (Fin n) := Finset.univ.filter fun i ↦
          MvPolynomial.aeval (jet : Fin 2 → E) (taylorAgreementEquation center QE K τ
            (domainE i) (f (received i))) = 0
        have hset :
            ({i : Fin n | MvPolynomial.aeval (jet : Fin 2 → E)
              (taylorAgreementEquation center QE K τ
              (domainE i) (f (received i))) = 0} : Set (Fin n)) =
              (agreementSet : Set (Fin n)) := by
          ext i
          simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
            Finset.mem_univ, true_and, agreementSet]
        rw [hset, Set.ncard_coe_finset]
        exact (hJ jet hjetmem).2.2.2)
  rw [hcard] at hcount
  exact hcount

open Classical in
/-- A degree-one message equation is bounded by the identity-pair Taylor incidence count. -/
theorem finite_regular_agreement_solutions_card_le_identityPair
    (Q : DifferentialPolynomial F 1) (j r : ℕ)
    (hjet : jetTotalDegree Q ≤ j)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hA : 2 ≤ A) (hAn : A ≤ n)
    (S : Finset F[X])
    (hdegree : ∀ P ∈ S, P.degree < 2)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q 1) P ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne 2 j r 0 *
      (((n - 1 : ℕ) : ℚ) / ((A - 1 : ℕ) : ℚ)) := by
  classical
  let E := AlgebraicClosure F
  let scalar : F →+* E := algebraMap F E
  let QE := MvPolynomial.map scalar Q
  have htau : TaylorExponentSufficient 1 2 0 := by
    simpa using taylorExponentSufficient_firstOrder_tight 1
  obtain ⟨center, jets, hcard, hjets⟩ := exists_regular_solution_jet_family_of_exponent
    (A := A) scalar Q 2 2 0 htau le_rfl S domain received hdegree hsol hsep (by omega) hagree
  by_cases hempty : jets = ∅
  · have hScard : S.card = 0 := by simpa [hempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjetmem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    intro hz
    exact (hjets jet hjetmem).2.1 (by rw [hz, map_zero])
  have hdegreeE : jetTotalDegree QE ≤ j := by
    rw [jetTotalDegree_map_eq scalar.injective Q]
    exact hjet
  have hcount := card_le_of_highTaylorCuts_of_agreement_sharp center QE htau (by omega)
    (fun i ↦ scalar (domain i)) (fun i ↦ scalar (received i))
    (fun i j hij ↦ domain.injective (scalar.injective hij)) hA (by simpa using hAn) jets
    (fun jet hjetmem ↦ ⟨(hjets jet hjetmem).1, (hjets jet hjetmem).2.1,
      fun l hl hlK ↦ by omega⟩)
    (fun jet hjetmem ↦ by
      let agreementSet := Finset.univ.filter fun i : Fin n ↦
        MvPolynomial.aeval jet (taylorAgreementEquation center QE 2 0
          (scalar (domain i)) (scalar (received i))) = 0
      have hset : {i | MvPolynomial.aeval jet (taylorAgreementEquation center QE 2 0
          (scalar (domain i)) (scalar (received i))) = 0} =
            (agreementSet : Set (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and, agreementSet]
      rw [hset, Set.ncard_coe_finset]
      exact (hjets jet hjetmem).2.2.2)
  rw [hcard] at hcount
  have hdegreeCast :
      (jetTotalDegree QE : ℚ) ≤ (j : ℚ) := by
    exact_mod_cast hdegreeE
  have hratio : (0 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) / (A - 1 : ℕ) :=
    div_nonneg (by positivity) (by positivity)
  have hn : n - 2 + 1 = n - 1 := by omega
  have hA' : A - 2 + 1 = A - 1 := by omega
  rw [Fintype.card_fin] at hcount
  simp only [rationalTaylorCutDegreeBound, zero_mul, Nat.add_zero, hn, hA', pow_one, mul_one]
    at hcount
  calc
    (S.card : ℚ) ≤
        jetTotalDegree QE *
          (((n - 1 : ℕ) : ℚ) / (A - 1 : ℕ)) := hcount
    _ ≤ j * (((n - 1 : ℕ) : ℚ) / (A - 1 : ℕ)) :=
      mul_le_mul_of_nonneg_right hdegreeCast hratio
    _ = firstOrderCurveFiberStageOne 2 j r 0 *
        (((n - 1 : ℕ) : ℚ) / (A - 1 : ℕ)) := by
      simp [firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
        firstOrderTaylorDerivativeCap, MvPolynomial.cappedDegreeMixedVolume]

open Classical in
/-- A regular first-order solution family is bounded by its regular Taylor incidence charge
times the sharp agreement ratio. -/
theorem finite_regular_agreement_solutions_card_le_regularTaylor
    (Q : DifferentialPolynomial F 1) (D j r : ℕ)
    (hregime : D = 1 ∨ 1 < D ∧ 0 < r)
    (hjet : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 1 ≤ r) (hrj : r ≤ j)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (S : Finset F[X])
    (hdegree : ∀ P ∈ S, P.degree < D + 1)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q 1) P ≠ 0)
    (hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne (D + 1) j r (regularTaylorExponent D) *
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) := by
  rcases hregime with hDone | ⟨hD, hr⟩
  · subst D
    simpa [regularTaylorExponent] using
      finite_regular_agreement_solutions_card_le_identityPair Q j r hjet domain received
        (by omega) hAn S hdegree hsol hsep hagree
  · have hτ : TaylorExponentSufficient 1 (D + 1) (regularTaylorExponent D) := by
      simpa [regularTaylorExponent] using taylorExponentSufficient_firstOrder_tight D
    have hτpos : 0 < regularTaylorExponent D := by
      unfold regularTaylorExponent
      omega
    have hcount := finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
      Q (D + 1) (D + 1) j r (regularTaylorExponent D)
      hτ hτpos (by omega) le_rfl hr hrj hjet hderiv domain received (by omega) hAn S
      hdegree hsol hsep hbin hagree
    have hn : n - (D + 1) + 1 = n - D := by omega
    have hA' : A - (D + 1) + 1 = A - D := by omega
    simpa only [hn, hA'] using hcount

/-- Every finite family of accepted polynomial solutions of a first-order equation is bounded by
the exact sum of its order-zero and derivative-capped order-one stage charges. -/
theorem finite_firstOrder_agreement_solutions_card_le_tight_of_exponent
    (Q : DifferentialPolynomial F 1) (K k μ M τ : ℕ)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ μ)
    (hfirst : jetDegree Q (1 : Fin 2) ≤ M)
    (hτ : ∀ r ≤ 1, TaylorExponentSufficient r K τ)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S,
      P.degree < k ∧
        A ≤ ({i : Fin n | P.eval (domain i) = received i}).ncard) :
    (S.card : ℚ) ≤ firstOrderTightListWeight n A k K τ μ M := by
  classical
  have hτpos : 0 < τ := by
    have ht := hτ 0 (by omega) (⟨1, hK⟩ : Fin K)
    norm_num [TaylorExponentSufficient] at ht
    omega
  have hchainChar : ringChar F = 0 ∨ jetTotalDegree Q < ringChar F :=
    hchar.imp_right fun h ↦
      hdegree.trans_lt ((Nat.le_max_right (K - 1) μ).trans_lt h)
  obtain ⟨stages, terminal, hchain⟩ :=
    exists_separantChain_of_ringChar hQ hchainChar
  have hcutChar : ringChar F = 0 ∨ K - 1 < ringChar F :=
    hchar.imp_right fun h ↦ (Nat.le_max_left (K - 1) μ).trans_lt h
  have hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    have hpivot := natCast_choose_ne_zero_of_ringChar (D := K - 1) (s := 1) hcutChar
      (i - 1) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hpivot
  let accepts : F[X] → Prop := fun P ↦
    P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i}).ncard
  let toRoot : {P // P ∈ S} → BoundedSolution Q (k - 1) := fun P ↦
    ⟨⟨P.1, by
      rw [Polynomial.mem_degreeLT]
      simpa [Nat.sub_add_cancel hk] using (haccept P.1 P.2).1⟩, hsol P.1 P.2⟩
  let roots : Finset (BoundedSolution Q (k - 1)) := S.attach.image toRoot
  have htoRoot : Function.Injective toRoot := by
    intro left right heq
    apply Subtype.ext
    exact congrArg BoundedSolution.polynomial heq
  have hcard : roots.card = S.card := by
    change (S.attach.image toRoot).card = S.card
    rw [Finset.card_image_of_injective _ htoRoot, Finset.card_attach]
  have hroots : ∀ solution ∈ roots, accepts solution.polynomial := by
    intro solution hsolution
    change solution ∈ S.attach.image toRoot at hsolution
    rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, rfl⟩
    exact haccept source.1 source.2
  let ratio : ℚ := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let c₀ : ℕ → ℚ := fun j ↦ j
  let c₁ : ℕ → ℕ → ℚ := fun j r ↦
    (firstOrderCurveFiberStageOne K j r τ : ℚ) * ratio
  let stageCost : SeparantStage F 1 → ℚ := firstOrderStageCharge c₀ c₁
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hregular : ∀ stage ∈ stages,
      ∀ regular : Finset (BoundedSolution stage.1 (k - 1)),
        (∀ solution ∈ regular, accepts solution.polynomial) →
        (∀ solution ∈ regular,
          differentialSpecialization (separant stage.1 stage.2) solution.polynomial ≠ 0) →
        (regular.card : ℚ) ≤ stageCost stage := by
    intro stage hstage regular hregularAccepts hregularSeparant
    have hhighest := hchain.highestActiveJet_eq_of_mem hstage
    have hs : stage.2 = 0 ∨ stage.2 = 1 := by
      rcases Fin.eq_zero_or_eq_succ stage.2 with hzero | ⟨i, hi⟩
      · exact Or.inl hzero
      · have : i = 0 := Subsingleton.elim _ _
        subst i
        exact Or.inr (by simpa using hi)
    rcases hs with hs | hs
    · have hcount := regularSolutions_card_le_of_agreement_orderZero stage.1
        (by simpa [hs] using hhighest) K k τ (jetTotalDegree stage.1) (hτ 0 (by omega))
        hk hkK domain received hkA hAn le_rfl regular
        (fun solution hsolution ↦ hregularAccepts solution hsolution)
        (fun solution hsolution ↦ by
          simpa [hs] using hregularSeparant solution hsolution)
      simpa [stageCost, firstOrderStageCharge, c₀, hs] using hcount
    · have hhighest' : highestActiveJet stage.1 = some (1 : Fin 2) := by
        simpa [hs] using hhighest
      have hactive : 0 < jetDegree stage.1 (1 : Fin 2) :=
        (isHighestActiveJet_of_highestActiveJet_eq_some hhighest').1
      let polynomials : Finset F[X] := regular.image fun solution ↦ solution.polynomial
      have hinjective : Function.Injective
          (fun solution : BoundedSolution stage.1 (k - 1) ↦ solution.polynomial) := by
        intro left right heq
        exact Subtype.ext (Subtype.ext heq)
      have hpolynomialCard : polynomials.card = regular.card :=
        Finset.card_image_of_injective regular hinjective
      have hcount := finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
        stage.1 K k (jetTotalDegree stage.1) (jetDegree stage.1 (1 : Fin 2)) τ
        (hτ 1 (by omega)) hτpos hK hkK
        hactive
        (jetDegree_le_total stage.1 1) le_rfl le_rfl
        domain received hkA hAn polynomials
        (fun P hP ↦ by
          rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
          exact (hregularAccepts solution hsolution).1)
        (fun P hP ↦ by
          rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
          exact solution.equation)
        (fun P hP ↦ by
          rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
          simpa [hs] using hregularSeparant solution hsolution)
        hbin
        (fun P hP ↦ by
          rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
          rw [← agreement_ncard_eq_filter_card domain received solution.polynomial]
          exact (hregularAccepts solution hsolution).2)
      rw [hpolynomialCard] at hcount
      simpa [stageCost, firstOrderStageCharge, c₁, ratio, hs] using hcount
  have hcount := boundedSolution_card_le_separantChainStageSum
    hchain (k - 1) accepts roots hroots stageCost hregular
  rw [hcard] at hcount
  have hcharge0 : ∀ j, 0 ≤ c₀ j := by intro j; positivity
  have hcharge1 : ∀ j r, 0 ≤ c₁ j r := by intro j r; positivity
  have hmono0 : Monotone c₀ := by
    intro j w hjw
    change (j : ℚ) ≤ (w : ℚ)
    exact_mod_cast hjw
  have hmono1Total : ∀ {j w r}, r ≤ j → j ≤ w → c₁ j r ≤ c₁ w r := by
    intro j w r _ hjw
    dsimp [c₁]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast firstOrderCurveFiberStageOne_mono_total hjw) hratio_nonneg
  have hmono1Degree : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q := by
    intro j r q hrq hqj
    dsimp [c₁]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast firstOrderCurveFiberStageOne_mono_derivative hrq hqj)
      hratio_nonneg
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp [ratio]
    rw [le_div_iff₀ (by exact_mod_cast (show 0 < A - k + 1 by omega))]
    norm_cast
    omega
  have hcharge01 : ∀ j, c₀ j ≤ c₁ j 1 := by
    intro j
    dsimp [c₀, c₁]
    have hj : (j : ℚ) ≤ firstOrderCurveFiberStageOne K j 1 τ := by
      exact_mod_cast le_firstOrderCurveFiberStageOne (by omega)
    calc
      (j : ℚ) = (j : ℚ) * 1 := by ring
      _ ≤ (firstOrderCurveFiberStageOne K j 1 τ : ℚ) * ratio :=
        mul_le_mul hj hratio_ge_one (by positivity) (by norm_num)
  have hcharges := hchain.sum_firstOrderStageCharge_le
    (c₀ := c₀) (c₁ := c₁) hdegree hfirst hcharge0 hcharge1 hmono0
    hmono1Total hmono1Degree hcharge01
  calc
    (S.card : ℚ) ≤ (stages.map stageCost).sum := hcount
    _ = (stages.map (firstOrderStageCharge c₀ c₁)).sum := rfl
    _ ≤ firstOrderStageCap c₀ c₁ μ M := hcharges
    _ = firstOrderTightListWeight n A k K τ μ M :=
      (firstOrderTightListWeight_eq_stageCap n A k K τ μ M).symm

/-- At exponent `2 * K`, the exact first-order charge is bounded by the uniform list charge. -/
theorem firstOrderTightListWeight_two_mul_le (n A k K μ M : ℕ)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n) :
    firstOrderTightListWeight n A k K (2 * K) μ M ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hdenNat : 0 < A - k + 1 := by omega
  have hden : (0 : ℚ) < (A - k + 1 : ℕ) := by exact_mod_cast hdenNat
  have hone : (1 : ℚ) ≤ (n : ℚ) / (A - k + 1 : ℕ) := by
    rw [le_div_iff₀ hden]
    norm_cast
    omega
  induction μ generalizing M with
  | zero => simp [firstOrderTightListWeight, firstOrderListWeight]
  | succ μ ih =>
      cases M with
      | zero =>
          simp only [firstOrderTightListWeight, firstOrderListWeight]
          have hhead : (μ : ℚ) + 1 ≤
              ((μ : ℚ) + 1) * ((n : ℚ) / (A - k + 1 : ℕ)) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℚ) ≤ μ + 1))
          calc
            (μ : ℚ) + 1 + firstOrderTightListWeight n A k K (2 * K) μ 0 ≤
                ((μ : ℚ) + 1) * ((n : ℚ) / (A - k + 1 : ℕ)) +
                  ((n * firstOrderListWeight K μ 0 : ℕ) : ℚ) /
                    ((A - k + 1 : ℕ) : ℚ) := add_le_add hhead (ih 0)
            _ = ((n * ((μ + 1) + firstOrderListWeight K μ 0) : ℕ) : ℚ) /
                  ((A - k + 1 : ℕ) : ℚ) := by
              push_cast
              field_simp
      | succ M =>
          simp only [firstOrderTightListWeight, firstOrderListWeight]
          have hstageNat := firstOrderCurveFiberStageOne_le_mul_totalCap
            (K := K) (j := μ + 1) (r := min (M + 1) (μ + 1)) (τ := 2 * K)
            (min_le_right _ _)
          have hstage :
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) ≤
                ((μ + 1) * (1 + 2 * K * μ) : ℕ) := by
            simpa [firstOrderTaylorTotalCap] using (show
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) ≤
                  ((μ + 1) * firstOrderTaylorTotalCap (μ + 1) (2 * K) : ℕ) by
                    exact_mod_cast hstageNat)
          push_cast at hstage
          have hhead :
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) *
                  ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ) ≤
                ((μ : ℚ) + 1) * (1 + 2 * (K : ℚ) * μ) *
                  (n : ℚ) / (A - k + 1 : ℕ) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul hstage (by exact_mod_cast (show n - k + 1 ≤ n by omega))
                (by positivity) (by positivity)
            · exact hden.le
          calc
            (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                  (2 * K) : ℚ) *
                  ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ) +
                firstOrderTightListWeight n A k K (2 * K) μ M ≤
              ((μ : ℚ) + 1) * (1 + 2 * (K : ℚ) * μ) *
                  (n : ℚ) / (A - k + 1 : ℕ) +
                ((n * firstOrderListWeight K μ M : ℕ) : ℚ) /
                  ((A - k + 1 : ℕ) : ℚ) := add_le_add hhead (ih M)
            _ = ((n * ((μ + 1) * (1 + 2 * K * μ) +
                  firstOrderListWeight K μ M) : ℕ) : ℚ) /
                    ((A - k + 1 : ℕ) : ℚ) := by
              push_cast
              field_simp

/-- Every finite family of accepted first-order equation solutions is bounded by the uniform
cap-sensitive sum divided by the agreement slack. -/
theorem finite_firstOrder_agreement_solutions_card_le_sharp
    (Q : DifferentialPolynomial F 1) (K k μ M : ℕ)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ μ)
    (hfirst : jetDegree Q (1 : Fin 2) ≤ M)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S,
      P.degree < k ∧ A ≤ ({i : Fin n | P.eval (domain i) = received i}).ncard) :
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  exact (finite_firstOrder_agreement_solutions_card_le_tight_of_exponent
    Q K k μ M (2 * K) hQ hdegree hfirst
      (fun r _ ↦ taylorExponentSufficient_two_mul r K) domain received
      hK hkK hk hkA hAn hchar S hsol haccept).trans
        (firstOrderTightListWeight_two_mul_le n A k K μ M hk hkA hAn)

end

end ReedSolomon.HiddenDerivative
