/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.RecursiveCount
public import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
import ArkLib.Data.Polynomial.Differential.WitnessCount
import ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Coefficient extension of rational Taylor charts

An injective coefficient map preserves nonzero separant specializations. Over an infinite target
domain, finite families of regular solutions share a center after mapping coefficients. Over an
infinite extension field, their polynomial jets form a cardinality-preserving family satisfying the
initial equation, high Taylor cuts, and received-word agreement bounds.

## Main statements

* `exists_forall_jetEvaluation_ne_zero_map`: mapped nonzero separants share a center over an
  infinite target domain.
* `exists_regular_solution_jet_family_of_exponent`: regular solution families embed into a chart
  with any sufficient common Taylor exponent.
* `card_le_of_regular_solutions_agreement`: regular polynomial solutions obey the sharp agreement
  bound after passage to an algebraically closed extension.
* `regularBranchRatBudget_of_agreement`: every regular stage in the singular recursion has a
  rational agreement-count budget.
* `finite_solutions_card_le_sq_totalJetDegree_of_agreement`: finite differential-equation
  solutions with agreement constraints satisfy the square-total-degree bound.
* `finite_solutions_card_le_sq_totalJetDegree_of_agreementGap`: a positive agreement gap gives
  the corresponding geometric bound.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open MvPolynomial
open Polynomial

open Classical in
/-- A finite family with nonzero separant specialization has a common regular center after an
injective coefficient map into an infinite domain. The jet coordinate may be any `j`. -/
theorem exists_forall_jetEvaluation_ne_zero_map {F E : Type*} [CommSemiring F] [CommRing E]
    [IsDomain E] [Infinite E] {r : ℕ} (f : F →+* E) (hf : Function.Injective f)
    (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F)) (j : Fin (r + 1))
    (hregular : ∀ P ∈ S, differentialSpecialization (separant Q j) P ≠ 0) :
    ∃ center : E, ∀ P ∈ S,
      jetEvaluation (separant (MvPolynomial.map f Q) j) center
        (polynomialJet center (P.map f)) ≠ 0 := by
  classical
  have hregularMap : ∀ P ∈ S.image (Polynomial.map f),
      differentialSpecialization (separant (MvPolynomial.map f Q) j) P ≠ 0 := by
    intro P hP
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hP
    rw [← map_separant]
    exact (map_differentialSpecialization_ne_zero_iff hf (separant Q j) P).2
      (hregular P hPS)
  obtain ⟨center, hc⟩ :=
    exists_forall_jetEvaluation_ne_zero (separant (MvPolynomial.map f Q) j)
      (S.image (Polynomial.map f)) hregularMap
  exact ⟨center, fun P hP ↦ hc _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩)⟩

open Classical in
/-- A finite family of regular polynomial solutions embeds into a rational Taylor chart over an
infinite extension field. Each jet satisfies the initial equation, all high cuts for degree below
`k`, and the agreement equations at the mapped evaluation points. The chart exponent `τ` may be
any exponent sufficient for all coefficients before `K`. The pivot nonvanishing conditions are
required over the chart field `E`. -/
theorem exists_regular_solution_jet_family_of_exponent
    {F E : Type*} [Field F] [Field E] [Infinite E] {r : ℕ}
    (f : F →+* E) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K)
    (S : Finset (Polynomial F)) {A : ℕ} {ι : Type*} [Fintype ι]
    (domain received : ι → F)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter (fun i ↦ P.eval (domain i) = received i)).card) :
    ∃ (center : E) (J : Finset (Fin (r + 1) → E)), J.card = S.card ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center (MvPolynomial.map f Q)) = 0 ∧
        aeval jet (initialJetSeparant center (MvPolynomial.map f Q)) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (commonTaylorNumerator center (MvPolynomial.map f Q) τ l.val) = 0) ∧
        A ≤ (Finset.univ.filter (fun i ↦
          aeval jet (taylorAgreementEquation center (MvPolynomial.map f Q) K τ
            (f (domain i)) (f (received i))) = 0)).card := by
  classical
  let QE := MvPolynomial.map f Q
  let SE := S.image (Polynomial.map f)
  have hSE := map_regularSolutionFamily (f := f) f.injective Q S (j := Fin.last r) k
    hdegree hsol hsep
  obtain ⟨center, hcenter⟩ :=
    exists_forall_jetEvaluation_ne_zero_map f f.injective Q S (Fin.last r) hsep
  have hcenterMapped : ∀ P ∈ SE,
      jetEvaluation (separant QE (Fin.last r)) center (polynomialJet center P) ≠ 0 := by
    intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    exact hcenter P₀ hP₀
  refine ⟨center, SE.image (polynomialJet (d := r) center), ?_, ?_⟩
  · rw [card_image_polynomialJet center QE K hbin SE
      (fun P hP ↦ (hSE P hP).1.trans_le (Nat.cast_le.mpr hkK))
      (fun P hP ↦ (hSE P hP).2.1)
      (fun P hP ↦ hcenterMapped P hP)]
    exact Finset.card_image_of_injective _ (Polynomial.map_injective f f.injective)
  · intro jet hjet
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjet
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    have hp := hSE (Polynomial.map f P₀) (Finset.mem_image.mpr ⟨P₀, hP₀, rfl⟩)
    have hs := hcenter P₀ hP₀
    refine ⟨aeval_initialJetEquation_polynomialJet center QE (Polynomial.map f P₀) hp.2.1,
      ?_, ?_, ?_⟩
    · rwa [aeval_initialJetSeparant]
    · intro l hl
      exact (mem_zeroLocus_highTaylorCutsIdeal_iff center QE).mp
        (polynomialJet_mem_zeroLocus_highTaylorCutsIdeal center QE (Polynomial.map f P₀)
          hp.2.1 hs τ hp.1 hbin) l.val hl l.isLt
    · have hcut :
          (Finset.univ.filter (fun i ↦
            aeval (polynomialJet center (Polynomial.map f P₀))
              (taylorAgreementEquation center QE K τ (f (domain i)) (f (received i))) = 0)) =
          Finset.univ.filter (fun i ↦
            (Polynomial.map f P₀).eval (f (domain i)) = f (received i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [taylorAgreementEquation_eq_zero_iff center QE hτ
          (polynomialJet center (Polynomial.map f P₀))
          (by rwa [aeval_initialJetSeparant]) (f (domain i)) (f (received i))]
        rw [rationalTaylorPolynomial_polynomialJet center QE (Polynomial.map f P₀)
          hp.2.1 hs (hp.1.trans_le (Nat.cast_le.mpr hkK)) hbin]
      calc
        A ≤ (Finset.univ.filter (fun i ↦ P₀.eval (domain i) = received i)).card :=
          hagree P₀ hP₀
        _ = (Finset.univ.filter (fun i ↦
            (Polynomial.map f P₀).eval (f (domain i)) = f (received i))).card :=
          by simp only [Polynomial.eval_map_apply, f.injective.eq_iff]
        _ = (Finset.univ.filter (fun i ↦
            aeval (polynomialJet center (Polynomial.map f P₀))
              (taylorAgreementEquation center QE K τ (f (domain i)) (f (received i))) = 0)).card :=
          by rw [hcut]

open Classical in
/-- A finite family of regular polynomial solutions over `F` with degree below `k` and at least
`A` agreements on distinct evaluation points has size at most
`jetTotalDegree Q * (((n - k + 1) * B) / (A - k + 1)) ^ r` over any algebraically closed field
extension, where `B = rationalTaylorCutDegreeBound Q τ` for a sufficient exponent `τ`. -/
theorem card_le_of_regular_solutions_agreement
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] [Algebra F E] {r : ℕ}
    (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ jetTotalDegree Q *
      (((((n - k + 1) * rationalTaylorCutDegreeBound Q τ : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ))) ^ r := by
  classical
  let f : F →+* E := algebraMap F E
  let QE := MvPolynomial.map f Q
  have hbinE : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0 := by
    intro i hir hiK hz
    apply hbin i hir hiK
    exact f.injective (by simpa using hz)
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family_of_exponent
    f Q K k τ hτ hkK S domain received hdegree hsol hsep hbinE hagree
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := card_le_of_highTaylorCuts_of_agreement_sharp center QE hτ hK
    domainE (fun i ↦ f (received i)) domainE.injective hkA (by simpa using hAn) J
    (fun jet hjet ↦ by
      obtain ⟨hinit, hsep, hcuts, -⟩ := hJ jet hjet
      refine ⟨hinit, hsep, ?_⟩
      intro l hkl hlK
      exact hcuts ⟨l, hlK⟩ hkl)
    (fun jet hjet ↦ by
      obtain ⟨-, -, -, hagreeJet⟩ := hJ jet hjet
      have hfilter : ({i | aeval jet
          (taylorAgreementEquation center QE K τ (domainE i) (f (received i))) = 0} :
          Set (Fin n)) =
          (Finset.univ.filter (fun i ↦ aeval jet
            (taylorAgreementEquation center QE K τ (domainE i) (f (received i))) = 0) :
            Finset (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and]
      rw [hfilter, Set.ncard_coe_finset]
      exact hagreeJet)
  rw [hcard] at hcount
  simpa [QE, rationalTaylorCutDegreeBound, jetTotalDegree_map_eq f.injective] using hcount

/-- Agreement constraints give a rational cardinality budget for every regular branch in the
singular recursion. -/
theorem regularBranchRatBudget_of_agreement
    {F : Type*} [Field F] [DecidableEq F] {d D K k ν : ℕ}
    (Q : DifferentialPolynomial F d)
    (hK : d < K) (hkK : k ≤ K) {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (accepts : F[X] → Prop)
    (hagreement : ∀ P, accepts P ↔
      P.degree < k ∧ A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    RegularBranchRatBudget Q D accepts
      ((ν : ℚ) *
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ d)) := by
  classical
  intro current s hreachable hhighest _hcast regular haccepted hseparant
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let presentation : JetPrefixPresentation current s := ⟨Q', hQ'⟩
  let polynomials : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective
      (fun solution : BoundedSolution current D ↦ solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polynomials.card = regular.card := by
    exact Finset.card_image_of_injective regular hinjective
  have hsle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
  have hcurrentDegree : jetTotalDegree current ≤ ν :=
    (jetTotalDegree_le_of_reflTransGen_singularStep hreachable).trans hdegree
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [presentation.jetTotalDegree_equation]
    exact hcurrentDegree
  have hactive : 0 < jetDegree current s :=
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
  have hactive' : 0 < jetDegree Q' (Fin.last s.val) := by
    rw [presentation.jetDegree_equation_last]
    exact hactive
  have hpositive : 0 < jetTotalDegree Q' := hactive'.trans_le (jetDegree_le_total Q' _)
  have hν : 0 < ν := hpositive.trans_le hQ'Degree
  have hfilter (P : F[X]) :
      Finset.univ.filter (fun i : Fin n ↦ P.eval (domain i) = received i) =
        @Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
          (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ := by
    exact (Finset.filter_congr_decidable Finset.univ
      (fun i : Fin n ↦ P.eval (domain i) = received i)
      (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i))).symm
  have hstage := card_le_of_regular_solutions_agreement (E := AlgebraicClosure F)
    Q' K k (2 * K) (taylorExponentSufficient_two_mul s.val K) (by omega) hkK
    domain received hkA hAn polynomials
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact ((hagreement solution.polynomial).mp (haccepted solution hsolution)).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (presentation.differentialSpecialization_equation solution.polynomial).trans
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      rw [← presentation.differentialSpecialization_separant_equation] at hs
      exact hs)
    (fun i hi hiK ↦ hbin s.val hsle i hi hiK)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have h := ((hagreement solution.polynomial).mp
        (haccepted solution hsolution)).2
      rw [hfilter solution.polynomial] at h
      exact h)
  rw [hcard] at hstage
  have hB : rationalTaylorCutDegreeBound Q' (2 * K) ≤ 1 + 2 * K * (ν - 1) := by
    unfold rationalTaylorCutDegreeBound
    gcongr
  have hden : 0 < (A - k + 1 : ℕ) := by omega
  have hbase :
      (((((n - k + 1) * rationalTaylorCutDegreeBound Q' (2 * K) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ≤
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) := by
    gcongr
    omega
  have hglobalBaseOne :
      1 ≤ ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ))) := by
    rw [le_div_iff₀ (by exact_mod_cast hden)]
    norm_cast
    have hdenle : A - k + 1 ≤ n := by omega
    calc
      1 * (A - k + 1) = A - k + 1 := one_mul _
      _ ≤ n := hdenle
      _ = n * 1 := by omega
      _ ≤ n * (1 + 2 * K * (ν - 1)) :=
        Nat.mul_le_mul_left n (by omega)
  calc
    (regular.card : ℚ) ≤
        (jetTotalDegree Q' : ℚ) *
          (((((n - k + 1) * rationalTaylorCutDegreeBound Q' (2 * K) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := hstage
    _ ≤ (ν : ℚ) *
          ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := by
      gcongr
    _ ≤ (ν : ℚ) *
          ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
      gcongr

/-- Finite polynomial solutions of a differential equation with degree and agreement constraints
have cardinality bounded by the square of the total jet degree times the agreement factor. -/
theorem finite_solutions_card_le_sq_totalJetDegree_of_agreement
    {F : Type*} [Field F] [DecidableEq F] {d : ℕ}
    (Q : DifferentialPolynomial F d) (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    (hdegree : jetTotalDegree Q ≤ ν) {n A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hk : 0 < k) (hkA : k ≤ A)
    (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (accepts : F[X] → Prop)
    (hagreement : ∀ P, accepts P ↔
      P.degree < k ∧ A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card)
    (S : Finset F[X]) (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccepts : ∀ P ∈ S, accepts P) :
    (S.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  classical
  let toRoot : {P // P ∈ S} → BoundedSolution Q (k - 1) := fun P ↦
    ⟨⟨P.1, by
      rw [Polynomial.mem_degreeLT]
      simpa [Nat.sub_add_cancel hk] using
        ((hagreement P.1).mp (haccepts P.1 P.2)).1⟩, hsol P.1 P.2⟩
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
    exact haccepts source.1 source.2
  let R : ℚ :=
    ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hR : 0 ≤ R := by unfold R; positivity
  have hRegular : RegularBranchRatBudget Q (k - 1) accepts ((ν : ℚ) * R ^ d) := by
    simpa only [R] using regularBranchRatBudget_of_agreement (D := k - 1) Q hK hkK
      domain received hk hkA hAn accepts hagreement hdegree hbin
  have hcount := boundedSolution_card_le_sq_totalJetDegree Q hQ hcast accepts ν R hR
    roots hroots hdegree hRegular
  rw [hcard] at hcount
  exact hcount

/-- A positive agreement gap bounds a finite family of differential-equation solutions by
`ν² (2ν / δ)^d n^d`. -/
theorem finite_solutions_card_le_sq_totalJetDegree_of_agreementGap
    {F : Type*} [Field F] [DecidableEq F] {d : ℕ}
    (Q : DifferentialPolynomial F d) (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ ν) {n A : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hk : 0 < k) (hkA : k ≤ A)
    (hAn : A ≤ n) (hKn : K ≤ n) (hν : 0 < ν)
    (hgap : (k : ℝ) + δ * n ≤ A) (hδ : 0 < δ)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F)
    (accepts : F[X] → Prop)
    (hagreement : ∀ P, accepts P ↔
      P.degree < k ∧ A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card)
    (S : Finset F[X]) (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccepts : ∀ P ∈ S, accepts P) :
    (S.card : ℝ) ≤ (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  have htotalChar : ringChar F = 0 ∨ ν < ringChar F :=
    hchar.imp_right (Nat.le_max_right _ _ |>.trans_lt)
  have hcast := jetDegreeCastsNeZero_of_jetTotalDegree_charGuard hdegree htotalChar
  have hcutChar : ringChar F = 0 ∨ K - 1 < ringChar F :=
    hchar.imp_right (Nat.le_max_left _ _ |>.trans_lt)
  have hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hir hiK
    have hchoose := natCast_choose_ne_zero_of_ringChar (D := K - 1) (s := r)
      hcutChar (i - r) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hir)] using hchoose
  have hn : 0 < n := hk.trans_le (hkA.trans hAn)
  have hcount := finite_solutions_card_le_sq_totalJetDegree_of_agreement Q K k ν hK hkK
    hQ hcast hdegree domain received hk hkA hAn hbin accepts hagreement S hsol haccepts
  have hcountR : (S.card : ℝ) ≤ (ν : ℝ) ^ 2 *
      (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / (A - k + 1 : ℕ)) ^ d := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hcount
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hc
  have hratio := agreementGap_geometricRatio_le (F := ℝ) hn hν hδ hKn hkA hgap
  calc
    (S.card : ℝ) ≤ (ν : ℝ) ^ 2 *
        (((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) / (A - k + 1 : ℕ)) ^ d := hcountR
    _ ≤ (ν : ℝ) ^ 2 * ((2 * ν / δ) * n) ^ d := by
      gcongr
    _ = (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by rw [mul_pow, mul_assoc]

end PolynomialDifferential
