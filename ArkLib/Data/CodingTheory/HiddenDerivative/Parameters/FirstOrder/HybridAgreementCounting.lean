/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AgreementCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AutomaticParameters
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
public import ArkLib.ToMathlib.MvPolynomial.OptionRoots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Ring

/-!
# Actual-degree first-order hybrid agreement counting

For a first-order equation over a field, repeated differentiation in `Y₁` reaches a nonzero
equation independent of `Y₁`. A symbolic equation over `F[X]` carries one such descent through
every coefficient evaluation. The polynomial root bound controls the order-zero tail, while
derivative-capped Taylor incidence bounds control the earlier regular stages. Together these give
finite agreement-list bounds in terms of the actual `Y₁` degree, its optimized maximum, and the
closed first-order list constant.

## Main statements

* `FirstOrderFieldDescent` and `exists_firstOrderFieldDescent`: actual-degree descent for a
  ground-field equation.
* `FirstOrderHybridDescent`, `exists_firstOrderHybridDescent`, and
  `FirstOrderHybridDescent.root_coverage`: symbolic actual-degree descent and its specialization
  coverage.
* `finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail` and
  `finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_tail`: list bounds for a
  symbolic equation with a supplied order-zero tail bound.
* `finite_firstOrder_field_hybrid_agreement_solutions_card_le_raw`: the actual-degree list bound.
* `finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized`: the optimized, ceiling,
  and closed bounds.
* `finite_automaticFirstOrder_hybrid_agreement_solutions_card_le`: the automatic parameter bound.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

local instance : Unique (Fin (0 + 1)) where
  default := 0
  uniq i := Fin.ext (by omega)

open Classical in
/-- A finite family of accepted polynomials annihilated by an order-zero equation has size at most
`b`. The acceptance condition asks for degree below `D + 1` and at least `A` agreements. -/
def HasOrderZeroTailListBound {F : Type*} [Field F] {n D A b : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (Q₀ : DifferentialPolynomial F 0) : Prop :=
  ∀ S : Finset F[X],
    (∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) →
    (∀ P ∈ S, differentialSpecialization Q₀ P = 0) → (S.card : ℝ) ≤ b

open Classical in
/-- A nonzero order-zero equation has at most its total jet degree many polynomial roots. -/
theorem hasOrderZeroTailListBound_of_nonzero
    {F : Type*} [Field F] {n D A b : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) {Q₀ : DifferentialPolynomial F 0} (hQ₀ : Q₀ ≠ 0)
    (hweight : jetTotalDegree Q₀ ≤ b) :
    HasOrderZeroTailListBound (D := D) (A := A) (b := b) domain received Q₀ := by
  intro S _ hsol
  have hroot : ∀ P ∈ S,
      MvPolynomial.aeval (fun o : Option (Fin 1) ↦ o.elim (Polynomial.X : F[X])
        (fun _ ↦ P)) Q₀ = 0 := by
    intro P hP
    let lhs : DifferentialPolynomial F 0 →ₐ[F] F[X] :=
      MvPolynomial.aeval fun v : Option (Fin 1) ↦ v.elim (Polynomial.X : F[X])
        (fun _ ↦ P)
    have hhom : lhs = differentialSpecializationHom P := by
      apply MvPolynomial.algHom_ext
      intro v
      cases v with
      | none =>
          simp [lhs, differentialSpecializationHom, MvPolynomial.aeval_X]
      | some j =>
          fin_cases j
          simp [lhs, differentialSpecializationHom, MvPolynomial.aeval_X,
            Polynomial.hasseDeriv_zero]
    change lhs Q₀ = 0
    rw [hhom]
    exact hsol P hP
  have hroots := MvPolynomial.card_le_degreeOf_some_of_aeval_eq_zero
    hQ₀ S hroot
  let idx : Fin (0 + 1) := (inferInstance : Unique (Fin (0 + 1))).default
  have hdegree : Q₀.degreeOf (some idx) ≤ jetTotalDegree Q₀ := by
    simpa [jetDegree] using jetDegree_le_total Q₀ idx
  exact_mod_cast hroots.trans (hdegree.trans hweight)

/-- A first-order equation with `Y₁` degree zero has a presentation using only `X` and `Y₀`. -/
theorem exists_firstOrderTailPresentation {R : Type*} [CommSemiring R]
    (Q : DifferentialPolynomial R 1) (hdegree : jetDegree Q (1 : Fin 2) = 0) :
    Nonempty (JetPrefixPresentation Q (0 : Fin 2)) := by
  classical
  have hvars : (Q.vars : Set (JetVariable 1)) ⊆
      Set.range (jetPrefixEmbedding (0 : Fin 2)) := by
    intro v hv
    rcases v with _ | j
    · exact ⟨none, rfl⟩
    · fin_cases j
      · exact ⟨some 0, rfl⟩
      · have hne : jetDegree Q (1 : Fin 2) ≠ 0 :=
          MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv
        exact (hne hdegree).elim
  exact exists_jetPrefixPresentation_of_vars_subset_range Q (0 : Fin 2) hvars

/-- The successive partial derivatives of a first-order equation through its actual `Y₁` degree,
with a nonzero presentation of the terminal equation in `X` and `Y₀`. -/
structure FirstOrderFieldDescent {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (μ M : ℕ) where
  /-- The actual degree of the equation in `Y₁`. -/
  actualDegree : ℕ
  /-- The actual degree is the computed degree in `Y₁`. -/
  actualDegree_eq : actualDegree = jetDegree Q (1 : Fin 2)
  /-- The actual degree is at most the supplied derivative cap. -/
  actualDegree_le : actualDegree ≤ M
  /-- Every derivative through the actual degree is nonzero. -/
  stage_nonzero : ∀ j ≤ actualDegree, jetDerivative Q 1 j ≠ 0
  /-- The `j`-th derivative has `Y₁` degree `actualDegree - j`. -/
  stage_degree : ∀ j ≤ actualDegree,
    jetDegree (jetDerivative Q 1 j) 1 = actualDegree - j
  /-- The `j`-th derivative has total jet degree at most `μ - j`. -/
  stage_jetTotalDegree_le : ∀ j ≤ actualDegree,
    jetTotalDegree (jetDerivative Q 1 j) ≤ μ - j
  /-- The terminal derivative is presented using only `X` and `Y₀`. -/
  tail : JetPrefixPresentation (jetDerivative Q 1 actualDegree) (0 : Fin 2)
  /-- The order-zero equation in the tail presentation is nonzero. -/
  tail_nonzero : tail.equation ≠ 0

/-- A nonzero equation with bounded total and `Y₁` degrees admits an actual-degree descent when
the characteristic does not divide any positive integer up to its `Y₁` degree. -/
theorem exists_firstOrderFieldDescent
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1) {μ M : ℕ}
    (hQ : Q ≠ 0) (hweight : jetTotalDegree Q ≤ μ)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hchar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F) :
    Nonempty (FirstOrderFieldDescent Q μ M) := by
  let e := jetDegree Q (1 : Fin 2)
  have hcasts : JetDegreeCastsNeZero Q (1 : Fin 2) :=
    jetDegreeCastsNeZero_of_ringChar hchar
  have hstages (j : ℕ) (hj : j ≤ e) :
      jetDerivative Q 1 j ≠ 0 ∧ jetDegree (jetDerivative Q 1 j) 1 = e - j := by
    exact ⟨jetDerivative_ne_zero hQ 1 hj hcasts,
      jetDegree_jetDerivative_eq_sub Q 1 j hcasts⟩
  have hstageWeight (j : ℕ) (hj : j ≤ e) :
      jetTotalDegree (jetDerivative Q 1 j) ≤ μ - j := by
    induction j with
    | zero => simpa using hweight
    | succ j ih =>
        have hj' : j ≤ e := by omega
        have hprev := ih hj'
        rw [jetDerivative_succ]
        have htotal := separant_total_le (jetDerivative Q 1 j) (1 : Fin 2)
        omega
  have htailDegree : jetDegree (jetDerivative Q 1 e) (1 : Fin 2) = 0 := by
    rw [jetDegree_jetDerivative_eq_sub Q 1 e hcasts]
    exact Nat.sub_self e
  obtain ⟨tail⟩ := exists_firstOrderTailPresentation (jetDerivative Q 1 e) htailDegree
  refine ⟨{
    actualDegree := e
    actualDegree_eq := rfl
    actualDegree_le := hdegree
    stage_nonzero := fun j hj ↦ (hstages j hj).1
    stage_degree := fun j hj ↦ by simpa [e] using (hstages j hj).2
    stage_jetTotalDegree_le := hstageWeight
    tail := tail
    tail_nonzero := tail.equation_ne_zero ((hstages e le_rfl).1)
  }⟩

namespace FirstOrderFieldDescent

/-- Every root reaches the order-zero tail or is regular at an earlier `Y₁` derivative stage. -/
theorem root_coverage
    {F : Type*} [Field F] {Q : DifferentialPolynomial F 1} {μ M : ℕ}
    (descent : FirstOrderFieldDescent Q μ M) (P : F[X])
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization descent.tail.equation P = 0 ∨
      ∃ j < descent.actualDegree,
        differentialSpecialization (jetDerivative Q 1 j) P = 0 ∧
          differentialSpecialization (separant (jetDerivative Q 1 j) 1) P ≠ 0 := by
  let value : ℕ → F[X] := fun j ↦ differentialSpecialization (jetDerivative Q 1 j) P
  have hzero : value 0 = 0 := by simpa [value] using hroot
  have hiterate : ∀ (r j : ℕ), descent.actualDegree - j = r → value j = 0 →
      j ≤ descent.actualDegree →
      differentialSpecialization descent.tail.equation P = 0 ∨
        ∃ i, j ≤ i ∧ i < descent.actualDegree ∧ value i = 0 ∧
          differentialSpecialization (separant (jetDerivative Q 1 i) 1) P ≠ 0 := by
    intro r
    induction r with
    | zero =>
        intro j hj hvalue hjle
        have hje : j = descent.actualDegree := by omega
        left
        rw [descent.tail.differentialSpecialization_equation P, ← hje]
        exact hvalue
    | succ r ih =>
        intro j hj hvalue hjle
        have hjlt : j < descent.actualDegree := by omega
        by_cases hnext : value (j + 1) = 0
        · have hrem : descent.actualDegree - (j + 1) = r := by omega
          rcases ih (j + 1) hrem hnext (by omega) with htail | ⟨i, hji, hie, hi, hsep⟩
          · exact Or.inl htail
          · exact Or.inr ⟨i, by omega, hie, hi, hsep⟩
        · right
          refine ⟨j, le_rfl, hjlt, hvalue, ?_⟩
          have hstep : value (j + 1) =
              differentialSpecialization (separant (jetDerivative Q 1 j) 1) P := by
            simp [value, jetDerivative_succ]
          rw [← hstep]
          exact hnext
  rcases hiterate descent.actualDegree 0 (by simp) hzero (Nat.zero_le _) with
    htail | ⟨j, _, hj, hstage, hsep⟩
  · exact Or.inl htail
  · exact Or.inr ⟨j, hj, by simpa [value] using hstage, hsep⟩

end FirstOrderFieldDescent

/-- A first-order symbolic equation together with its actual-degree derivative stages and tail.
The coefficient polynomial is left unevaluated so one descent handles every specialization. -/
structure FirstOrderHybridDescent {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) (μ M : ℕ) where
  /-- The actual degree in `Y₁`. -/
  actualDegree : ℕ
  /-- The actual degree is the degree of the starting equation in `Y₁`. -/
  actualDegree_eq : actualDegree = jetDegree Q (1 : Fin 2)
  /-- The actual degree is at most the supplied derivative cap. -/
  actualDegree_le : actualDegree ≤ M
  /-- Every derivative through the actual degree is nonzero. -/
  stage_nonzero : ∀ j ≤ actualDegree, jetDerivative Q (1 : Fin 2) j ≠ 0
  /-- The `j`-th derivative has `Y₁` degree `actualDegree - j`. -/
  stage_degree : ∀ j ≤ actualDegree,
    jetDegree (jetDerivative Q (1 : Fin 2) j) (1 : Fin 2) = actualDegree - j
  /-- The `j`-th derivative has total jet degree at most `μ - j`. -/
  stage_jetTotalDegree_le : ∀ j ≤ actualDegree,
    jetTotalDegree (jetDerivative Q (1 : Fin 2) j) ≤ μ - j
  /-- The final derivative is presented using only `X` and `Y₀`. -/
  tail : JetPrefixPresentation (jetDerivative Q (1 : Fin 2) actualDegree) 0
  /-- The order-zero equation in the tail presentation is nonzero. -/
  tail_nonzero : tail.equation ≠ 0

private theorem natCast_polynomial_ne_zero_of_char_guard
    {F : Type*} [Field F] {e k : ℕ}
    (hchar : ringChar F = 0 ∨ e < ringChar F) (hk : 0 < k) (hke : k ≤ e) :
    (k : F[X]) ≠ 0 := by
  intro hz
  have hscalar : (k : F) = 0 := by
    simpa using congrArg (Polynomial.eval (0 : F)) hz
  have hdiv := (ringChar.spec F k).mp hscalar
  rcases hchar with hzero | hlt
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hk (hke.trans_lt hlt) hdiv

/-- A nonzero equation with bounded total and `Y₁` degrees admits an actual-degree descent when
the characteristic does not divide any positive integer up to its `Y₁` degree. -/
theorem exists_firstOrderHybridDescent {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) {μ M : ℕ} (hQ : Q ≠ 0)
    (hweight : jetTotalDegree Q ≤ μ) (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hchar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F) :
    Nonempty (FirstOrderHybridDescent Q μ M) := by
  let e := jetDegree Q (1 : Fin 2)
  have hcasts : JetDegreeCastsNeZero Q (1 : Fin 2) := by
    intro k hk hke
    apply natCast_polynomial_ne_zero_of_char_guard hchar hk
    simpa [e] using hke
  have hstages (j : ℕ) (hj : j ≤ e) :
      jetDerivative Q (1 : Fin 2) j ≠ 0 ∧
        jetDegree (jetDerivative Q (1 : Fin 2) j) (1 : Fin 2) = e - j := by
    have hjQ : j ≤ jetDegree Q (1 : Fin 2) := by simpa [e] using hj
    exact ⟨jetDerivative_ne_zero hQ 1 hjQ hcasts,
      jetDegree_jetDerivative_eq_sub Q 1 j hcasts⟩
  have hstageWeight (j : ℕ) :
      jetTotalDegree (jetDerivative Q (1 : Fin 2) j) ≤ μ - j := by
    induction j with
    | zero => simpa [jetDerivative] using hweight
    | succ j ih =>
        rw [jetDerivative_succ]
        have hstep := separant_total_le (jetDerivative Q (1 : Fin 2) j) (1 : Fin 2)
        omega
  have htailDegree : jetDegree (jetDerivative Q (1 : Fin 2) e) (1 : Fin 2) = 0 := by
    simpa [e] using (hstages e le_rfl).2
  obtain ⟨tail⟩ := exists_firstOrderTailPresentation
    (jetDerivative Q (1 : Fin 2) e) htailDegree
  exact ⟨{
    actualDegree := e
    actualDegree_eq := rfl
    actualDegree_le := hdegree
    stage_nonzero := fun j hj ↦ (hstages j hj).1
    stage_degree := fun j hj ↦ (hstages j hj).2
    stage_jetTotalDegree_le := fun j _ ↦ hstageWeight j
    tail := tail
    tail_nonzero := tail.equation_ne_zero (hstages e le_rfl).1
  }⟩

/-- Every specialized root either solves the order-zero tail or is regular at an earlier `Y₁`
derivative stage. -/
theorem FirstOrderHybridDescent.root_coverage {F E : Type*} [Field F] [Field E]
    {Q : DifferentialPolynomial F[X] 1} {μ M : ℕ}
    (descent : FirstOrderHybridDescent Q μ M) (φ : F[X] →+* E) (P : E[X])
    (hroot : differentialSpecialization (MvPolynomial.map φ Q) P = 0) :
    differentialSpecialization (MvPolynomial.map φ descent.tail.equation) P = 0 ∨
      ∃ j < descent.actualDegree,
        differentialSpecialization
          (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) j)) P = 0 ∧
        differentialSpecialization
          (separant (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) j))
            (1 : Fin 2)) P ≠ 0 := by
  let value : ℕ → E[X] := fun j ↦
    differentialSpecialization (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) j)) P
  have hzero : value 0 = 0 := by simpa [value, jetDerivative_zero] using hroot
  have hiterate {e r : ℕ} (he : descent.actualDegree - e = r)
      (hle : e ≤ descent.actualDegree)
      (hvalue : value e = 0) :
      value descent.actualDegree = 0 ∨
        ∃ j < descent.actualDegree,
          value j = 0 ∧ differentialSpecialization
            (separant (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) j))
              (1 : Fin 2)) P ≠ 0 := by
    induction r generalizing e with
    | zero =>
        left
        have : e = descent.actualDegree := by omega
        simpa [this] using hvalue
    | succ r ih =>
        have hj : e < descent.actualDegree := by omega
        by_cases hnext : value (e + 1) = 0
        · have hrem : descent.actualDegree - (e + 1) = r := by omega
          exact ih hrem (by omega) hnext
        · right
          refine ⟨e, hj, hvalue, ?_⟩
          have hstep : value (e + 1) = differentialSpecialization
              (separant (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) e)) (1 : Fin 2)) P := by
            change differentialSpecialization
              (MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) (e + 1))) P = _
            rw [jetDerivative_succ, ← map_separant]
          rw [← hstep]
          exact hnext
  rcases hiterate (e := 0) (r := descent.actualDegree) (by simp)
      (Nat.zero_le _) hzero with
    htail | ⟨j, hj, hstage, hsep⟩
  · left
    change differentialSpecialization (descent.tail.map φ).equation P = 0
    rw [(descent.tail.map φ).differentialSpecialization_equation]
    exact htail
  · right
    exact ⟨j, hj, by simpa [value] using hstage, hsep⟩

open Classical in
/-- A finite regular family of accepted polynomial solutions is bounded by the derivative-capped
first-order Taylor incidence charge. -/
theorem finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
    {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (K k j r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ) (hK : 1 < K)
    (hkK : k ≤ K) (hr : 0 < r) (hrj : r ≤ j)
    (hjet : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 1 ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset F[X])
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q 1) P ≠ 0)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := AlgebraicClosure F
  let scalar : F →+* E := algebraMap F E
  let QE := MvPolynomial.map scalar Q
  have hbinE : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiK hz
    apply hbin i hi hiK
    exact scalar.injective (by simpa using hz)
  obtain ⟨center, jets, hcard, hjets⟩ := exists_regular_solution_jet_family_of_exponent
    (A := A) scalar Q K k τ hτ hkK S domain received hdegree hsol hsep hbinE hagree
  by_cases hempty : jets = ∅
  · have hScard : S.card = 0 := by simpa [hempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  let domainE : Fin n ↪ E := domain.trans ⟨scalar, scalar.injective⟩
  have hcount := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    center QE K k j r τ hτ hτpos hK hr hrj
    (by
      have hw : (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) = jetDegreeWeight := by
        funext i
        cases i <;> rfl
      have hjetE : jetTotalDegree QE ≤ j := by
        rw [jetTotalDegree_map_eq scalar.injective Q]
        exact hjet
      change QE.weightedTotalDegree
        (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) ≤ j
      rw [hw]
      exact hjetE)
    (by
      change jetDegree QE 1 ≤ r
      simpa only [QE, jetDegree_map_eq scalar.injective Q 1] using hderiv)
    domainE (fun i ↦ scalar (received i)) hkA hAn jets
    (fun jet hjetmem ↦ ⟨(hjets jet hjetmem).1, (hjets jet hjetmem).2.1,
      fun l ↦ (hjets jet hjetmem).2.2.1 l.val l.property⟩)
    (fun jet hjetmem ↦ by
      let agreementSet := Finset.univ.filter fun i : Fin n ↦
        MvPolynomial.aeval jet (taylorAgreementEquation center QE K τ
          (scalar (domain i)) (scalar (received i))) = 0
      have hset : {i | MvPolynomial.aeval jet (taylorAgreementEquation center QE K τ
          (domainE i) (scalar (received i))) = 0} =
            (agreementSet : Set (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and, agreementSet, domainE,
          Function.Embedding.coe_trans, Function.Embedding.coeFn_mk, Function.comp_apply]
      rw [hset, Set.ncard_coe_finset]
      simpa only [agreementSet, domainE, Function.Embedding.coeFn_mk] using
        (hjets jet hjetmem).2.2.2)
  rw [hcard] at hcount
  exact hcount

open Classical in
/-- A degree-one message equation is bounded by the identity-pair Taylor incidence count. -/
theorem finite_regular_agreement_solutions_card_le_identityPair
    {F : Type*} [Field F]
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
private theorem finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_stages
    {F : Type*} [Field F] {n D A μ e : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (Q : DifferentialPolynomial F 1)
    (stage : ℕ → DifferentialPolynomial F 1) (tail : DifferentialPolynomial F 0)
    (heμ : e ≤ μ) (hstageWeight : ∀ j < e, jetTotalDegree (stage j) ≤ μ - j)
    (hstageDegree : ∀ j < e, jetDegree (stage j) 1 ≤ e - j)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D e < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A) (b := μ - e)
      domain received tail)
    (S : Finset F[X]) (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hcoverage : ∀ P ∈ S, differentialSpecialization Q P = 0 →
      differentialSpecialization tail P = 0 ∨
        ∃ j < e, differentialSpecialization (stage j) P = 0 ∧
          differentialSpecialization (separant (stage j) 1) P ≠ 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ firstOrderListCharge (agreementIncidenceRatio n D A) D μ e := by
  classical
  let θ := agreementIncidenceRatio n D A
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    apply natCast_ne_zero_of_ringChar_eq_zero_or_lt hchar (by omega)
    exact (show i ≤ D by omega).trans (Nat.le_max_left D e)
  have hτ : TaylorExponentSufficient 1 (D + 1) (regularTaylorExponent D) := by
    simpa [regularTaylorExponent] using taylorExponentSufficient_firstOrder_tight D
  let tailRoots := S.filter fun P ↦
    differentialSpecialization tail P = 0
  let stageRoots : Fin e → Finset F[X] := fun j ↦ S.filter fun P ↦
    differentialSpecialization (stage j) P = 0 ∧
      differentialSpecialization (separant (stage j) (1 : Fin 2)) P ≠ 0
  have htailCard : (tailRoots.card : ℝ) ≤ ((μ - e : ℕ) : ℝ) := by
    apply htail tailRoots
    · intro P hP
      exact (haccept P (Finset.mem_filter.mp hP).1)
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
  have hstageCard (j : Fin e) : (stageRoots j).card ≤
      θ * firstOrderCurveFiberStageOne
        (D + 1) (μ - j) (e - j) (regularTaylorExponent D) := by
    have hj : j.val < e := j.isLt
    have hv : 0 < μ - j := by omega
    have hu : 0 < e - j := by omega
    have huv : e - j ≤ μ - j := Nat.sub_le_sub_right heμ j
    have hjet : jetTotalDegree (stage j) ≤ μ - j := hstageWeight j.val hj
    have hderiv : jetDegree (stage j) 1 ≤ e - j := hstageDegree j.val hj
    have hregular : ((stageRoots j).card : ℚ) ≤
        firstOrderCurveFiberStageOne (D + 1) (μ - j) (e - j) (regularTaylorExponent D) *
          (((n - D : ℕ) : ℚ) / (A - D : ℕ)) := by
      by_cases hDone : D = 1
      · subst D
        have hn : n - 2 + 1 = n - 1 := by omega
        have hA' : A - 2 + 1 = A - 1 := by omega
        simpa only [Nat.reduceAdd, regularTaylorExponent, Nat.reduceMul, Nat.reduceSub,
          hn, hA'] using finite_regular_agreement_solutions_card_le_identityPair
            (stage j) (μ - j) (e - j) hjet domain received (by omega) hAn (stageRoots j)
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
            (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
            (fun P hP ↦ by
              simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
                (Finset.mem_filter.mp hP).2.2)
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
      · have hτpos : 0 < regularTaylorExponent D := by
          unfold regularTaylorExponent
          omega
        have hnum : n - (D + 1) + 1 = n - D := by omega
        have hden : A - (D + 1) + 1 = A - D := by omega
        simpa only [hnum, hden] using
          finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
            (stage j)
            (D + 1) (D + 1) (μ - j) (e - j) (regularTaylorExponent D)
            hτ hτpos (by omega) le_rfl hu huv hjet hderiv domain received
            (by omega) hAn (stageRoots j)
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
            (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
            (fun P hP ↦ by
              simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
                (Finset.mem_filter.mp hP).2.2)
            hbin
            (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
    have hregularReal : ((stageRoots j).card : ℝ) ≤
        (firstOrderCurveFiberStageOne
          (D + 1) (μ - j) (e - j) (regularTaylorExponent D) : ℝ) *
          (((n - D : ℕ) : ℝ) / (A - D : ℕ)) := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hregular
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div] using hcast
    simpa [θ, agreementIncidenceRatio, mul_comm] using hregularReal
  have hcover : S ⊆ tailRoots ∪ Finset.univ.biUnion stageRoots := by
    intro P hP
    rcases hcoverage P hP (hsol P hP) with htailRoot | ⟨j, hj, hstage, hsep⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, htailRoot⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hP, hstage, hsep⟩
  have hcardNat : S.card ≤ tailRoots.card + ∑ j, (stageRoots j).card := by
    calc
      S.card ≤ (tailRoots ∪ Finset.univ.biUnion stageRoots).card :=
        Finset.card_le_card hcover
      _ ≤ tailRoots.card + (Finset.univ.biUnion stageRoots).card := Finset.card_union_le _ _
      _ ≤ tailRoots.card + ∑ j, (stageRoots j).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hcardReal : (S.card : ℝ) ≤
      (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (S.card : ℝ) ≤ (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := hcardReal
    _ ≤ (μ - e : ℕ) + ∑ j : Fin e,
        θ * firstOrderCurveFiberStageOne
          (D + 1) (μ - j) (e - j) (regularTaylorExponent D) := by
      exact add_le_add htailCard (Finset.sum_le_sum fun j _ ↦ hstageCard j)
    _ = firstOrderListCharge θ D μ e := by
      have hfin : (∑ j : Fin e,
          θ * firstOrderCurveFiberStageOne
            (D + 1) (μ - j) (e - j) (regularTaylorExponent D)) =
          ∑ j ∈ Finset.range e,
            θ * firstOrderCurveFiberStageOne
              (D + 1) (μ - j) (e - j) (regularTaylorExponent D) := by
        exact Fin.sum_univ_eq_sum_range (α := ℝ) (fun j : ℕ ↦
          θ * firstOrderCurveFiberStageOne
            (D + 1) (μ - j) (e - j) (regularTaylorExponent D)) e
      rw [hfin, firstOrderListCharge, regularFiberStageSum]
      simp only [Nat.cast_sum]
      rw [Finset.mul_sum]
      ring

open Classical in
/-- A symbolic first-order equation is bounded by the regular-stage charges and an explicit bound
for its specialized order-zero tail. -/
theorem finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F[X] 1) (descent : FirstOrderHybridDescent Q μ M)
    (z : F) (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := μ - descent.actualDegree) domain received
      (MvPolynomial.map (Polynomial.evalRingHom z) descent.tail.equation))
    (S : Finset F[X])
    (hsol : ∀ P ∈ S,
      differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ firstOrderListCharge (agreementIncidenceRatio n D A)
      D μ descent.actualDegree := by
  let φ := Polynomial.evalRingHom z
  let Q' := MvPolynomial.map φ Q
  let stage := fun j ↦ MvPolynomial.map φ (jetDerivative Q (1 : Fin 2) j)
  let tail := MvPolynomial.map φ descent.tail.equation
  have heμ : descent.actualDegree ≤ μ := by
    have hweight := descent.stage_jetTotalDegree_le 0 (Nat.zero_le _)
    calc
      descent.actualDegree = jetDegree Q (1 : Fin 2) := descent.actualDegree_eq
      _ ≤ jetTotalDegree Q := jetDegree_le_total Q 1
      _ ≤ μ := hweight
  have hstageWeight : ∀ j < descent.actualDegree,
      jetTotalDegree (stage j) ≤ μ - j := by
    intro j hj
    exact (jetTotalDegree_map_le φ _).trans
      (descent.stage_jetTotalDegree_le j (Nat.le_of_lt hj))
  have hstageDegree : ∀ j < descent.actualDegree,
      jetDegree (stage j) 1 ≤ descent.actualDegree - j := by
    intro j hj
    exact (jetDegree_map_le φ (jetDerivative Q (1 : Fin 2) j) 1).trans_eq
      (descent.stage_degree j (Nat.le_of_lt hj))
  have hchar' : ringChar F = 0 ∨ max D descent.actualDegree < ringChar F := by
    rcases hchar with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr ((max_le_max_left D descent.actualDegree_le).trans_lt hlt)
  have hcoverage : ∀ P ∈ S, differentialSpecialization Q' P = 0 →
      differentialSpecialization tail P = 0 ∨
        ∃ j < descent.actualDegree,
          differentialSpecialization (stage j) P = 0 ∧
            differentialSpecialization (separant (stage j) 1) P ≠ 0 := by
    intro P hP hroot
    rcases descent.root_coverage φ P hroot with htailRoot |
        ⟨j, hj, hstage, hsep⟩
    · exact Or.inl htailRoot
    · exact Or.inr ⟨j, hj, by simpa [stage] using hstage,
        by simpa [stage] using hsep⟩
  exact finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_stages
    domain received Q' stage tail heμ hstageWeight hstageDegree hD hDA hAn hchar'
    htail S (by simpa [Q'] using hsol) hcoverage haccept

open Classical in
/-- A polynomial-coefficient actual-degree hybrid count gives the optimized, ceiling, and closed
first-order list bounds after specialization. -/
theorem finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_tail
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F[X] 1) (descent : FirstOrderHybridDescent Q μ M)
    (z : F) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := μ - descent.actualDegree) domain received
      (MvPolynomial.map (Polynomial.evalRingHom z) descent.tail.equation))
    (S : Finset F[X])
    (hsol : ∀ P ∈ S,
      differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ maxFirstOrderListCharge (agreementIncidenceRatio n D A) D μ M ∧
      S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M ∧
      (S.card : ℝ) ≤ firstOrderListConstant (agreementIncidenceRatio n D A) D μ M := by
  have hraw := finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail
    domain received Q descent z hD (by omega) hAn hchar htail S hsol haccept
  have hopt := hraw.trans (firstOrderListCharge_le_max descent.actualDegree_le)
  have hceil : S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M := by
    unfold firstOrderListBound maxFirstOrderListCharge at hopt ⊢
    exact_mod_cast hopt.trans (Nat.le_ceil _)
  have hclosed := maxFirstOrderListCharge_le_firstOrderListConstant
    (one_le_agreementIncidenceRatio hDA hAn) hD hMμ
  exact ⟨hopt, hceil, hopt.trans hclosed⟩

open Classical in
/-- The field descent bounds the accepted roots by the regular-stage charges and the tail. -/
private theorem finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_field_tail
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q μ M)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := μ - descent.actualDegree) domain received descent.tail.equation)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ firstOrderListCharge (agreementIncidenceRatio n D A)
      D μ descent.actualDegree := by
  let e := descent.actualDegree
  let stage := fun j ↦ jetDerivative Q 1 j
  have heμ : e ≤ μ := by
    have hweight := descent.stage_jetTotalDegree_le 0 (Nat.zero_le e)
    calc
      e = jetDegree Q (1 : Fin 2) := descent.actualDegree_eq
      _ ≤ jetTotalDegree Q := jetDegree_le_total Q 1
      _ ≤ μ := hweight
  have hstageWeight : ∀ j < e, jetTotalDegree (stage j) ≤ μ - j := by
    intro j hj
    exact descent.stage_jetTotalDegree_le j (Nat.le_of_lt hj)
  have hstageDegree : ∀ j < e, jetDegree (stage j) 1 ≤ e - j := by
    intro j hj
    rw [descent.stage_degree j (Nat.le_of_lt hj)]
  have hcoverage : ∀ P ∈ S, differentialSpecialization Q P = 0 →
      differentialSpecialization descent.tail.equation P = 0 ∨
        ∃ j < e, differentialSpecialization (stage j) P = 0 ∧
          differentialSpecialization (separant (stage j) 1) P ≠ 0 := by
    intro P hP hroot
    rcases descent.root_coverage P hroot with htailRoot | ⟨j, hj, hstage, hsep⟩
    · exact Or.inl htailRoot
    · exact Or.inr ⟨j, hj, by simpa [stage] using hstage,
        by simpa [stage] using hsep⟩
  have hchar' : ringChar F = 0 ∨ max D e < ringChar F := by
    rcases hchar with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr ((max_le_max_left D descent.actualDegree_le).trans_lt hlt)
  exact finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_stages
    domain received Q stage descent.tail.equation heμ hstageWeight hstageDegree
    hD hDA hAn hchar' htail S hsol hcoverage haccept

open Classical in
/-- The actual-degree hybrid count gives the optimized, ceiling, and closed first-order list
bounds. -/
private theorem finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_field_tail
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q μ M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := μ - descent.actualDegree) domain received descent.tail.equation)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ maxFirstOrderListCharge (agreementIncidenceRatio n D A) D μ M ∧
      S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M ∧
      (S.card : ℝ) ≤ firstOrderListConstant (agreementIncidenceRatio n D A) D μ M := by
  have hraw := finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_field_tail
    domain received Q descent hD (by omega) hAn hchar htail S hsol haccept
  have hopt := hraw.trans (firstOrderListCharge_le_max descent.actualDegree_le)
  have hceil : S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M := by
    unfold firstOrderListBound maxFirstOrderListCharge at hopt ⊢
    exact_mod_cast hopt.trans (Nat.le_ceil _)
  have hclosed := maxFirstOrderListCharge_le_firstOrderListConstant
    (one_le_agreementIncidenceRatio hDA hAn) hD hMμ
  exact ⟨hopt, hceil, hopt.trans hclosed⟩

open Classical in
/-- A ground-field first-order equation has no tail premise: its nonzero order-zero tail is bounded
by the degree of its univariate graph equation. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le_raw
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q μ M)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ firstOrderListCharge (agreementIncidenceRatio n D A)
      D μ descent.actualDegree := by
  have htailWeight : jetTotalDegree descent.tail.equation ≤ μ - descent.actualDegree := by
    rw [descent.tail.jetTotalDegree_equation]
    exact descent.stage_jetTotalDegree_le descent.actualDegree le_rfl
  have htail := hasOrderZeroTailListBound_of_nonzero (D := D) (A := A)
    (b := μ - descent.actualDegree) domain received
    descent.tail_nonzero htailWeight
  exact finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_field_tail
    domain received Q descent hD hDA hAn hchar htail S hsol haccept

open Classical in
/-- The ground-field actual-degree count gives optimized, ceiling, and closed list bounds. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q μ M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ maxFirstOrderListCharge (agreementIncidenceRatio n D A) D μ M ∧
      S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M ∧
      (S.card : ℝ) ≤ firstOrderListConstant (agreementIncidenceRatio n D A) D μ M := by
  have htail := hasOrderZeroTailListBound_of_nonzero (D := D) (A := A) domain received
    (b := μ - descent.actualDegree)
    descent.tail_nonzero
    (by
      rw [descent.tail.jetTotalDegree_equation]
      exact descent.stage_jetTotalDegree_le descent.actualDegree le_rfl)
  exact finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_field_tail
    domain received Q descent hD hDA hAn hMμ hchar htail S hsol haccept

open Classical in
/-- A first-order equation's nonzero and degree bounds construct the descent and give the
optimized, ceiling, and closed list bounds. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le
    {F : Type*} [Field F] {n D A μ M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hweight : jetTotalDegree Q ≤ μ) (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ maxFirstOrderListCharge (agreementIncidenceRatio n D A) D μ M ∧
      S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D μ M ∧
      (S.card : ℝ) ≤ firstOrderListConstant (agreementIncidenceRatio n D A) D μ M := by
  have hactualChar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F :=
    hchar.imp_right fun h ↦ (hdegree.trans (Nat.le_max_right D M)).trans_lt h
  obtain ⟨descent⟩ := exists_firstOrderFieldDescent Q hQ hweight hdegree hactualChar
  exact finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized
    domain received Q descent hD hDA hAn hMμ hchar S hsol haccept

open Classical in
/-- The literal automatic first-order parameters produce optimized, ceiling, and closed list
bounds for every received word. -/
theorem finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
    {F : Type*} [Field F] {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max D (automaticDerivativeCap rho a) < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤ maxFirstOrderListCharge (agreementIncidenceRatio n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      S.card ≤ firstOrderListBound (agreementIncidenceRatio n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (S.card : ℝ) ≤ firstOrderListConstant (agreementIncidenceRatio n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  let m := automaticMultiplicity rho a
  let agreement := automaticAgreement rho a
  have hmpos : 0 < m := automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hagreementPos : 0 < agreement :=
    hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha)
  have hArate : agreement * n ≤ A := by
    calc
      agreement * n ≤ a * n :=
        mul_le_mul_of_nonneg_right (automaticAgreement_le rho a) (by positivity)
      _ ≤ A := hA
  have hAposReal : (0 : ℝ) < A := by
    have hpos : (0 : ℝ) < agreement * n := mul_pos hagreementPos (Nat.cast_pos.mpr hn)
    exact hpos.trans_le hArate
  have hApos : 0 < A := by exact_mod_cast hAposReal
  have hbudget : 0 < m * A := Nat.mul_pos hmpos hApos
  have hDrate : (D : ℝ) ≤ rho * n := automatic_degree_le_rate_mul hD hkRate
  let hp : FirstOrderFiniteRateParameters rho agreement := {
    multiplicity := m
    multiplicity_pos := hmpos
    surplus := by
      simpa [FirstOrderFiniteRateTest, FirstOrderFiniteRateParameters.derivativeCap,
        FirstOrderFiniteRateParameters.rankCount, FirstOrderFiniteRateParameters.sourceCount,
        automaticRankCount_eq_raw hrho hrhoOne ha haOne,
        automaticSourceCount_eq_raw hrho hrhoOne ha haOne, m, agreement,
        automaticDerivativeCapRaw, automaticDerivativeRatio, automaticAgreement,
        firstOrderRateDerivativeCap, firstOrderRateBeta, firstOrderRateJetDegree,
        automaticJetDegree] using
        automaticRankCount_lt_sourceCount hrho hrhoOne ha haOne }
  have hthresholdD : 0 < D := by omega
  have hkD : k ≤ D + 1 := by omega
  have hbudget' : 0 < hp.multiplicity * A := by
    change 0 < m * A
    exact hbudget
  obtain ⟨cert⟩ := exists_firstOrderRate_symbolicCertificate hp hn hthresholdD hbudget'
    hkD hDrate hArate domain received received
  let phi := Polynomial.eval₂RingHom (RingHom.id F) (0 : F)
  let Q : DifferentialPolynomial F 1 := MvPolynomial.map phi cert.Q
  obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hweightCert : jetTotalDegree cert.Q ≤ hp.jetDegree := by
    rw [jetTotalDegree_le_iff]
    exact cert.totalJetDegree_le
  have hjetCap : hp.jetDegree = automaticJetDegree rho a := by
    change firstOrderRateJetDegree rho agreement m = automaticJetDegree rho a
    rfl
  have hweight : jetTotalDegree Q ≤ automaticJetDegree rho a := by
    exact (jetTotalDegree_map_le phi cert.Q).trans (hweightCert.trans_eq hjetCap)
  have hdegreeCert : jetDegree cert.Q 1 ≤ hp.derivativeCap := by
    rw [jetDegree, MvPolynomial.degreeOf_le_iff]
    intro u hu
    have hfirst : u (some (⟨1, by omega⟩ : Fin 2)) ≤ hp.derivativeCap := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos,
        jetExponentCoordinatesEquiv_apply] using cert.firstJetDegree_le u hu
    have hcoord : (⟨1, by omega⟩ : Fin 2) = 1 := Fin.ext rfl
    simpa only [hcoord] using hfirst
  have hderivCap : hp.derivativeCap = automaticDerivativeCap rho a := by
    rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
    change firstOrderRateDerivativeCap rho agreement m = automaticDerivativeCapRaw rho a
    rfl
  have hdegree : jetDegree Q 1 ≤ automaticDerivativeCap rho a := by
    exact (jetDegree_map_le phi cert.Q 1).trans
      (hdegreeCert.trans_eq hderivCap)
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    have hPdegree : P.degree < k := (hS P hP).1
    have hcard : A ≤ indices.card := (hS P hP).2
    apply hsound indices P hPdegree hcard
    intro i hi
    have hiAgree := (Finset.mem_filter.mp hi).2
    simpa [receivedLine] using hiAgree
  have hDpos : 1 ≤ D := by omega
  have hDA : D < A := by
    have hkrho : (k : ℝ) ≤ rho * n := hkRate
    have hrhoAgreement : rho < agreement := rho_lt_automaticAgreement hrho hrhoOne ha
    have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hkAreal : (k : ℝ) ≤ A := by
      exact (calc
          (k : ℝ) ≤ rho * n := hkrho
          _ < agreement * n := mul_lt_mul_of_pos_right hrhoAgreement hnreal
          _ ≤ A := hArate).le
    have hkA : k ≤ A := by exact_mod_cast hkAreal
    omega
  have hMμ : automaticDerivativeCap rho a ≤ automaticJetDegree rho a := by
    rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
    exact automaticDerivativeCapRaw_le_jetDegree hrho hrhoOne ha haOne
  have haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
    intro P hP
    have hDk : D + 1 = k := by omega
    have hDkCast : (D : WithBot ℕ) + 1 = k := by exact_mod_cast hDk
    refine ⟨?_, (hS P hP).2⟩
    simpa only [hDkCast] using (hS P hP).1
  exact finite_firstOrder_field_hybrid_agreement_solutions_card_le
    domain received Q hQ hweight hdegree hDpos hDA hAn hMμ hchar S hsol haccept

end

end ReedSolomon.HiddenDerivative
