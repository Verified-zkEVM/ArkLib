/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrder.FirstOrderList
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HybridDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.AutomaticCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants
/-!
# Actual-degree hybrid first-order list counting

This file partitions a finite solution list using only the actual `Y₁` descent.  Each regular
`Y₁` stage receives its derivative-capped fiber charge.  The final nonzero `Y₀`-only equation
is encoded as a univariate polynomial and receives the characteristic-free root bound directly.
No differentiation in `Y₀` and no characteristic bound involving `mu` occurs here.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

open Polynomial SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

open Classical in
/-- Public fixed-stage form of the derivative-capped regular solution count. -/
theorem finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
    {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (K k j r tau : ℕ)
    (htau : TaylorExponentSufficient 1 K tau) (htauPos : 0 < tau) (hK : 1 < K)
    (hkK : k ≤ K) (hj : 0 < j) (hr : 0 < r) (hrj : r ≤ j)
    (hjet : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 1 ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset F[X])
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 1)) P ≠ 0)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r tau *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := AlgebraicClosure F
  let scalar : F →+* E := algebraMap F E
  let QE := MvPolynomial.map scalar Q
  obtain ⟨center, jets, hcard, hjets⟩ := exists_regular_solution_jet_family_of_exponent
    (A := A) scalar Q K k tau htau hkK S domain received hdegree hsol hsep hbin hagree
  by_cases hempty : jets = ∅
  · have hScard : S.card = 0 := by simpa [hempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjetmem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    intro hz
    exact (hjets jet hjetmem).2.1 (by rw [hz, map_zero])
  let domainE : Fin n ↪ E := domain.trans ⟨scalar, scalar.injective⟩
  have hcount := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    center QE K k j r tau htau htauPos hK hsepE hj hr hrj
    (by
      rw [totalJetDegree_map_eq]
      rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
      exact hjet)
    (by
      change jetDegree QE 1 ≤ r
      simpa only [QE, jetDegree_map_eq scalar scalar.injective Q 1] using hderiv)
    domainE (fun i ↦ scalar (received i)) hk hkA hAn jets
    (fun jet hjetmem ↦ ⟨(hjets jet hjetmem).1, (hjets jet hjetmem).2.1,
      fun l ↦ (hjets jet hjetmem).2.2.1 l.val l.property⟩)
    (fun jet hjetmem ↦ (hjets jet hjetmem).2.2.2)
  rw [hcard] at hcount
  exact hcount

/-- The exact characteristic-free fact required of the specialized order-zero tail. -/
def HasOrderZeroTailListBound
    {F : Type*} [Field F] {n D A b : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (Q0 : DifferentialPolynomial F 0) : Prop :=
  ∀ S : Finset F[X],
    (∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) →
    (∀ P ∈ S, differentialSpecialization Q0 P = 0) →
    (S.card : ℝ) ≤ b

/-- Rename `Y₀` to the outer polynomial variable and `X` to the sole coefficient variable. -/
def orderZeroVariableEquiv : JetVariable 0 ≃ Fin 2 :=
  (_root_.finSuccEquiv 1).symm.trans (Equiv.swap 0 1)

/-- An order-zero differential equation is a univariate polynomial in `Y₀` over `F[X]`. -/
def orderZeroAsPolynomial {F : Type*} [Field F]
    (Q0 : DifferentialPolynomial F 0) : F[X][X] :=
  Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.rename orderZeroVariableEquiv Q0))

/-- Evaluation of the `Y₀` polynomial is differential specialization of the order-zero
equation. -/
theorem orderZeroAsPolynomial_eval
    {F : Type*} [Field F] (Q0 : DifferentialPolynomial F 0) (P : F[X]) :
    (orderZeroAsPolynomial Q0).eval P = differentialSpecialization Q0 P := by
  let lhs : DifferentialPolynomial F 0 →ₐ[F] F[X] :=
    ((Polynomial.aeval P).restrictScalars F).comp
      (((Polynomial.mapAlgHom
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toAlgHom).restrictScalars F).comp
          ((MvPolynomial.finSuccEquiv F 1).toAlgHom.comp
            (MvPolynomial.renameEquiv F orderZeroVariableEquiv).toAlgHom))
  have hlhs : lhs Q0 = (orderZeroAsPolynomial Q0).eval P := by rfl
  rw [← hlhs]
  change lhs Q0 = differentialSpecializationHom P Q0
  congr 1
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · dsimp [lhs]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      differentialSpecializationHom_apply, differentialSpecialization_x]
    change Polynomial.eval P (Polynomial.map
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
          (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X (1 : Fin 2)))) = Polynomial.X
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
      MvPolynomial.finSuccEquiv_X_succ]
    rw [Polynomial.map_C, Polynomial.eval_C]
    simp [MvPolynomial.X]
  · fin_cases j
    dsimp [lhs]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      differentialSpecializationHom_apply, differentialSpecialization_jet]
    rw [show orderZeroVariableEquiv (some (0 : Fin 1)) = (0 : Fin 2) by decide]
    change Polynomial.eval P (Polynomial.map
      (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
        (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X (0 : Fin 2)))) =
          Polynomial.hasseDeriv 0 P
    rw [Polynomial.hasseDeriv_zero]
    change Polynomial.eval P (Polynomial.map
      (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
        (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X (0 : Fin 2)))) = P
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X]

/-- The `Y₀` polynomial is nonzero whenever the order-zero differential equation is. -/
theorem orderZeroAsPolynomial_ne_zero
    {F : Type*} [Field F] {Q0 : DifferentialPolynomial F 0} (hQ0 : Q0 ≠ 0) :
    orderZeroAsPolynomial Q0 ≠ 0 := by
  intro hzero
  apply hQ0
  apply (MvPolynomial.renameEquiv F orderZeroVariableEquiv).injective
  apply (MvPolynomial.finSuccEquiv F 1).injective
  have hmap : Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
      (MvPolynomial.finSuccEquiv F 1
        ((MvPolynomial.renameEquiv F orderZeroVariableEquiv) Q0)) =
        Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom 0 := by
    rw [Polynomial.map_zero]
    exact hzero
  exact Polynomial.map_injective (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective hmap

/-- The univariate `Y₀` degree is bounded by total jet weight. -/
theorem orderZeroAsPolynomial_natDegree_le_jetWeight
    {F : Type*} [Field F] (Q0 : DifferentialPolynomial F 0) :
    (orderZeroAsPolynomial Q0).natDegree ≤ SymbolicSeparantChain.jetWeight Q0 := by
  rw [orderZeroAsPolynomial,
    Polynomial.natDegree_map_eq_of_injective
      (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective,
    MvPolynomial.natDegree_finSuccEquiv]
  have hdegree : MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.rename orderZeroVariableEquiv Q0) = jetDegree Q0 0 := by
    change MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.rename orderZeroVariableEquiv Q0) =
        MvPolynomial.degreeOf (some (0 : Fin 1)) Q0
    have hrename := MvPolynomial.degreeOf_rename_of_injective
      orderZeroVariableEquiv.injective (some (0 : Fin 1)) (p := Q0)
    rw [show orderZeroVariableEquiv (some (0 : Fin 1)) = (0 : Fin 2) by decide] at hrename
    exact hrename
  rw [hdegree]
  exact SymbolicSeparantChain.jetDegree_le_jetWeight Q0 0

open Classical in
/-- A nonzero order-zero differential equation has at most its jet weight many polynomial
solutions.  This is the characteristic-free terminal bound used by the hybrid descent. -/
theorem hasOrderZeroTailListBound_of_nonzero
    {F : Type*} [Field F] {n D A b : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) {Q0 : DifferentialPolynomial F 0} (hQ0 : Q0 ≠ 0)
    (hweight : SymbolicSeparantChain.jetWeight Q0 ≤ b) :
    HasOrderZeroTailListBound (D := D) (A := A) (b := b) domain received Q0 := by
  intro S _ hsol
  have hpoly : orderZeroAsPolynomial Q0 ≠ 0 := orderZeroAsPolynomial_ne_zero hQ0
  have hroots : S.val ⊆ (orderZeroAsPolynomial Q0).roots := by
    intro P hP
    apply (Polynomial.mem_roots hpoly).mpr
    rw [Polynomial.IsRoot.def, orderZeroAsPolynomial_eval]
    exact hsol P hP
  have hcard : S.card ≤ (orderZeroAsPolynomial Q0).natDegree :=
    Polynomial.card_le_degree_of_subset_roots hroots
  exact_mod_cast hcard.trans (orderZeroAsPolynomial_natDegree_le_jetWeight Q0 |>.trans hweight)

/-- The `j`-th `Y₁` derivative of an equation already specialized to the ground field. -/
def firstOrderFieldDerivativeStage {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (j : ℕ) : DifferentialPolynomial F 1 :=
  jetDerivative Q (1 : Fin 2) j

@[simp]
theorem firstOrderFieldDerivativeStage_zero {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) : firstOrderFieldDerivativeStage Q 0 = Q := by
  simp [firstOrderFieldDerivativeStage]

@[simp]
theorem firstOrderFieldDerivativeStage_succ {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (j : ℕ) :
    firstOrderFieldDerivativeStage Q (j + 1) =
      separant (firstOrderFieldDerivativeStage Q j) (1 : Fin 2) := by
  simp [firstOrderFieldDerivativeStage]

private theorem natCast_field_ne_zero_of_char_guard
    {F : Type*} [Field F] {e m : ℕ}
    (hchar : ringChar F = 0 ∨ e < ringChar F) (hm : 0 < m) (hme : m ≤ e) :
    (m : F) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec F m).mp hz
  rcases hchar with hzero | hlt
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hm (hme.trans_lt hlt) hdiv

/-- Through the actual `Y₁` degree, the field-specialized derivative stages remain nonzero and
their `Y₁` degrees decrease exactly. -/
theorem firstOrderFieldDerivativeStage_ne_zero_and_degree
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1)
    (hQ : Q ≠ 0) (e : ℕ) (he : jetDegree Q (1 : Fin 2) = e)
    (hchar : ringChar F = 0 ∨ e < ringChar F) :
    ∀ j ≤ e, firstOrderFieldDerivativeStage Q j ≠ 0 ∧
      jetDegree (firstOrderFieldDerivativeStage Q j) (1 : Fin 2) = e - j := by
  intro j hj
  induction j with
  | zero => simpa [he] using And.intro hQ he
  | succ j ih =>
      have hjle : j ≤ e := by omega
      obtain ⟨hne, hdegree⟩ := ih hjle
      have hpos : 0 < jetDegree (firstOrderFieldDerivativeStage Q j) (1 : Fin 2) := by
        rw [hdegree]
        omega
      have hcast :
          (jetDegree (firstOrderFieldDerivativeStage Q j) (1 : Fin 2) : F) ≠ 0 := by
        apply natCast_field_ne_zero_of_char_guard hchar hpos
        rw [hdegree]
        exact Nat.sub_le _ _
      have hdegree' :
          MvPolynomial.degreeOf (some (1 : Fin 2))
            (firstOrderFieldDerivativeStage Q j) = e - j := hdegree
      have hstep :=
        MvPolynomial.pderiv_ne_zero_and_degreeOf_eq_sub_one_of_natCast_ne_zero
          (some (1 : Fin 2)) (firstOrderFieldDerivativeStage Q j) hpos hcast
      rw [firstOrderFieldDerivativeStage_succ]
      exact ⟨hstep.1, by
        change MvPolynomial.degreeOf (some (1 : Fin 2))
          (MvPolynomial.pderiv (some (1 : Fin 2))
            (firstOrderFieldDerivativeStage Q j)) = _
        rw [hstep.2, hdegree']
        omega⟩

/-- Each actual-field `Y₁` derivative spends one unit of total jet weight. -/
theorem firstOrderFieldDerivativeStage_jetWeight_le
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1) {mu j : ℕ}
    (hweight : jetWeight Q ≤ mu) :
    jetWeight (firstOrderFieldDerivativeStage Q j) ≤ mu - j := by
  have hsub : jetWeight (firstOrderFieldDerivativeStage Q j) ≤ jetWeight Q - j := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [firstOrderFieldDerivativeStage_succ]
        have hstep := jetWeight_separant_le (firstOrderFieldDerivativeStage Q j) (1 : Fin 2)
        omega
  exact hsub.trans (Nat.sub_le_sub_right hweight j)

/-- An order-zero presentation of a ground-field equation independent of `Y₁`. -/
structure FirstOrderFieldTailPresentation {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) where
  equation : DifferentialPolynomial F 0
  ambient_eq : MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2)) equation = Q

/-- Degree zero in `Y₁` lets a ground-field first-order equation restrict to `X,Y₀`. -/
theorem exists_firstOrderFieldTailPresentation
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1)
    (hdegree : jetDegree Q (1 : Fin 2) = 0) :
    Nonempty (FirstOrderFieldTailPresentation Q) := by
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
  obtain ⟨tail, htail⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q
    (jetPrefixEmbedding (0 : Fin 2)) (jetPrefixEmbedding (0 : Fin 2)).injective hvars
  exact ⟨⟨tail, htail⟩⟩

theorem FirstOrderFieldTailPresentation.nonzero
    {F : Type*} [Field F] {Q : DifferentialPolynomial F 1}
    (tail : FirstOrderFieldTailPresentation Q) (hQ : Q ≠ 0) : tail.equation ≠ 0 := by
  intro hz
  apply hQ
  rw [← tail.ambient_eq, hz, map_zero]

theorem FirstOrderFieldTailPresentation.specialization
    {F : Type*} [Field F] {Q : DifferentialPolynomial F 1}
    (tail : FirstOrderFieldTailPresentation Q) (P : F[X]) :
    differentialSpecialization tail.equation P = differentialSpecialization Q P := by
  calc
    _ = differentialSpecialization
        (MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2)) tail.equation) P :=
      (differentialSpecialization_rename_jetPrefixEmbedding
        (0 : Fin 2) tail.equation P).symm
    _ = _ := by rw [tail.ambient_eq]

theorem FirstOrderFieldTailPresentation.jetWeight
    {F : Type*} [Field F] {Q : DifferentialPolynomial F 1}
    (tail : FirstOrderFieldTailPresentation Q) :
    SymbolicSeparantChain.jetWeight tail.equation = SymbolicSeparantChain.jetWeight Q := by
  calc
    _ = SymbolicSeparantChain.jetWeight
        (MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2)) tail.equation) :=
      (SymbolicJetPrefix.jetWeight_rename (0 : Fin 2) tail.equation).symm
    _ = _ := congrArg SymbolicSeparantChain.jetWeight tail.ambient_eq

/-- Complete actual-field descent through the actual `Y₁` degree. -/
structure FirstOrderFieldDescent {F : Type*} [Field F]
    (Q : DifferentialPolynomial F 1) (mu M : ℕ) where
  actualDegree : ℕ
  actualDegree_eq : actualDegree = jetDegree Q (1 : Fin 2)
  actualDegree_le : actualDegree ≤ M
  stage_nonzero : ∀ j ≤ actualDegree, firstOrderFieldDerivativeStage Q j ≠ 0
  stage_degree : ∀ j ≤ actualDegree,
    jetDegree (firstOrderFieldDerivativeStage Q j) (1 : Fin 2) = actualDegree - j
  stage_jetWeight_le : ∀ j ≤ actualDegree,
    jetWeight (firstOrderFieldDerivativeStage Q j) ≤ mu - j
  tail : FirstOrderFieldTailPresentation
    (firstOrderFieldDerivativeStage Q actualDegree)
  tail_nonzero : tail.equation ≠ 0

theorem exists_firstOrderFieldDescent
    {F : Type*} [Field F] (Q : DifferentialPolynomial F 1) {mu M : ℕ}
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hchar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F) :
    Nonempty (FirstOrderFieldDescent Q mu M) := by
  let e := jetDegree Q (1 : Fin 2)
  have hstages := firstOrderFieldDerivativeStage_ne_zero_and_degree Q hQ e rfl hchar
  have htailDegree : jetDegree (firstOrderFieldDerivativeStage Q e) (1 : Fin 2) = 0 := by
    simpa [e] using (hstages e le_rfl).2
  obtain ⟨tail⟩ := exists_firstOrderFieldTailPresentation
    (firstOrderFieldDerivativeStage Q e) htailDegree
  exact ⟨{
    actualDegree := e
    actualDegree_eq := rfl
    actualDegree_le := hdegree
    stage_nonzero := fun j hj ↦ (hstages j hj).1
    stage_degree := fun j hj ↦ (hstages j hj).2
    stage_jetWeight_le := fun j _ ↦ firstOrderFieldDerivativeStage_jetWeight_le Q hweight
    tail := tail
    tail_nonzero := tail.nonzero (hstages e le_rfl).1
  }⟩

/-- Every root of a ground-field equation either reaches its nonzero order-zero tail or is
regular at an earlier `Y₁` stage. -/
theorem FirstOrderFieldDescent.root_coverage
    {F : Type*} [Field F] {Q : DifferentialPolynomial F 1} {mu M : ℕ}
    (descent : FirstOrderFieldDescent Q mu M) (P : F[X])
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization descent.tail.equation P = 0 ∨
      ∃ j < descent.actualDegree,
        differentialSpecialization (firstOrderFieldDerivativeStage Q j) P = 0 ∧
          differentialSpecialization
            (separant (firstOrderFieldDerivativeStage Q j) (1 : Fin 2)) P ≠ 0 := by
  let value : ℕ → F[X] := fun j ↦
    differentialSpecialization (firstOrderFieldDerivativeStage Q j) P
  have hzero : value 0 = 0 := by simpa [value] using hroot
  rcases root_reaches_tail_or_regular_stage value descent.actualDegree hzero with
    htail | ⟨j, hj, hz, hnz⟩
  · left
    rw [descent.tail.specialization P]
    exact htail
  · right
    exact ⟨j, hj, hz, by simpa only [value, firstOrderFieldDerivativeStage_succ] using hnz⟩

private theorem weightedTotalDegree_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (weight : sigma → ℕ) (Q : MvPolynomial sigma R) :
    (MvPolynomial.map phi Q).weightedTotalDegree weight ≤ Q.weightedTotalDegree weight := by
  rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  rw [MvPolynomial.mem_restrictWeightedDegree]
  intro exponent hexponent
  exact MvPolynomial.le_weightedTotalDegree weight
    (MvPolynomial.support_map_subset phi Q hexponent)

private theorem degreeOf_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (i : sigma) (Q : MvPolynomial sigma R) :
    MvPolynomial.degreeOf i (MvPolynomial.map phi Q) ≤ MvPolynomial.degreeOf i Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro exponent hexponent
  exact MvPolynomial.monomial_le_degreeOf i
    (MvPolynomial.support_map_subset phi Q hexponent)

private theorem natCast_ne_zero_of_max_char_guard
    {F : Type*} [Field F] {D M i : ℕ}
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) (hi : 0 < i) (hiD : i ≤ D) :
    (i : F) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec F i).mp hz
  rcases hchar with hzero | hpos
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpos) hdiv

open Classical in
/-- The actual-degree descent gives the raw hybrid list charge: derivative-capped regular
`Y₁` stages plus the characteristic-free order-zero tail. -/
theorem finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail
    {F : Type*} [Field F] {n D A mu M h : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F[X] 1)
    (descent : FirstOrderHybridDescent Q mu M h) (z : F)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := mu - descent.actualDegree) domain received
        (MvPolynomial.map (Polynomial.evalRingHom z) descent.tail.equation))
    (S : Finset F[X])
    (hsol : ∀ P ∈ S,
      differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤
      hybridListRaw (hybridTheta n D A) D mu descent.actualDegree := by
  classical
  let e := descent.actualDegree
  let phi := Polynomial.evalRingHom z
  have heμ : e ≤ mu := by
    have hdegree := descent.stage_degree 0 (Nat.zero_le e)
    have hweight := descent.stage_jetWeight_le 0 (Nat.zero_le e)
    have hle := jetDegree_le_jetWeight Q (1 : Fin 2)
    have hjet : jetDegree Q (1 : Fin 2) ≤ mu := by
      simpa only [firstOrderDerivativeStage_zero, Nat.sub_zero] using hle.trans hweight
    exact descent.actualDegree_eq.trans_le hjet
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_max_char_guard hchar (by omega) (by omega)
  have htau : TaylorExponentSufficient 1 (D + 1) (hybridTau D) := by
    convert taylorExponentSufficient_two_mul_sub_three 1 (K := D + 1) (by omega) using 1
    unfold hybridTau
    omega
  let tailRoots := S.filter fun P ↦
    differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom z) descent.tail.equation) P = 0
  let stageRoots : Fin e → Finset F[X] := fun j ↦ S.filter fun P ↦
    differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom z) (firstOrderDerivativeStage Q j)) P = 0 ∧
      differentialSpecialization
        (separant (MvPolynomial.map (Polynomial.evalRingHom z) (firstOrderDerivativeStage Q j))
          (1 : Fin 2)) P ≠ 0
  have htailCard : (tailRoots.card : ℝ) ≤ ((mu - e : ℕ) : ℝ) := by
    apply htail tailRoots
    · intro P hP
      exact haccept P (Finset.mem_filter.mp hP).1
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
  have hstageCard (j : Fin e) : (stageRoots j).card ≤
      hybridTheta n D A * firstOrderCurveFiberStageOne
        (D + 1) (mu - j) (e - j) (hybridTau D) := by
    have hj : j.val < e := j.isLt
    have hv : 0 < mu - j := by omega
    have hu : 0 < e - j := by omega
    have huv : e - j ≤ mu - j := Nat.sub_le_sub_right heμ j
    have hjet : jetTotalDegree
        (MvPolynomial.map (Polynomial.evalRingHom z) (firstOrderDerivativeStage Q j)) ≤ mu - j := by
      rw [jetTotalDegree_eq_weightedTotalDegree_elim]
      exact (weightedTotalDegree_map_le phi _ _).trans
        (descent.stage_jetWeight_le j (Nat.le_of_lt hj))
    have hderiv : jetDegree
        (MvPolynomial.map (Polynomial.evalRingHom z) (firstOrderDerivativeStage Q j)) 1 ≤
          e - j := by
      exact (degreeOf_map_le phi (some (1 : Fin 2)) _).trans_eq
        (descent.stage_degree j (Nat.le_of_lt hj))
    have hbound := finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
      (MvPolynomial.map (Polynomial.evalRingHom z) (firstOrderDerivativeStage Q j))
      (D + 1) (D + 1) (mu - j) (e - j) (hybridTau D)
      htau (by unfold hybridTau; omega) (by omega) le_rfl hv hu huv hjet hderiv
      domain received (by omega) hkA hAn (stageRoots j)
      (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
      (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
      (fun P hP ↦ by
        simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
          (Finset.mem_filter.mp hP).2.2)
      hbin
      (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
    have hnum : n - (D + 1) + 1 = n - D := by omega
    have hden : A - (D + 1) + 1 = A - D := by omega
    rw [hnum, hden] at hbound
    have hboundReal : ((stageRoots j).card : ℝ) ≤
        (firstOrderCurveFiberStageOne
          (D + 1) (mu - j) (e - j) (hybridTau D) : ℝ) *
          (((n - D : ℕ) : ℝ) / (A - D : ℕ)) := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hbound
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div] using hcast
    simpa only [hybridTheta, mul_comm] using hboundReal
  have hcover : S ⊆ tailRoots ∪ Finset.univ.biUnion stageRoots := by
    intro P hP
    rcases descent.root_coverage (Polynomial.evalRingHom z) P (hsol P hP) with
      htailRoot | ⟨j, hj, hstageRoot, hstageSep⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hP, ?_⟩
      exact htailRoot
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨hP, ?_, ?_⟩
      · exact hstageRoot
      · exact hstageSep
  have hcardNat : S.card ≤ tailRoots.card + ∑ j, (stageRoots j).card := by
    calc
      S.card ≤ (tailRoots ∪ Finset.univ.biUnion stageRoots).card :=
        Finset.card_le_card hcover
      _ ≤ tailRoots.card + (Finset.univ.biUnion stageRoots).card :=
        Finset.card_union_le _ _
      _ ≤ tailRoots.card + ∑ j, (stageRoots j).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hcardReal : (S.card : ℝ) ≤
      (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (S.card : ℝ) ≤ (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := hcardReal
    _ ≤ (mu - e : ℕ) + ∑ j : Fin e,
        hybridTheta n D A * firstOrderCurveFiberStageOne
          (D + 1) (mu - j) (e - j) (hybridTau D) := by
      exact add_le_add htailCard (Finset.sum_le_sum fun j _ ↦ hstageCard j)
    _ = hybridListRaw (hybridTheta n D A) D mu e := by
      have hfin : (∑ j : Fin e,
          hybridTheta n D A * firstOrderCurveFiberStageOne
            (D + 1) (mu - j) (e - j) (hybridTau D)) =
          ∑ j ∈ Finset.range e,
            hybridTheta n D A * firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (hybridTau D) := by
        exact Fin.sum_univ_eq_sum_range (α := ℝ) (fun j : ℕ ↦
          hybridTheta n D A * firstOrderCurveFiberStageOne
            (D + 1) (mu - j) (e - j) (hybridTau D)) e
      rw [hfin]
      unfold hybridListRaw hybridB1
      simp only [Nat.cast_sum]
      rw [Finset.mul_sum]
      ring

/-- The actual raw list charge is one entry of the finite optimized maximum. -/
theorem hybridListRaw_le_hybridListOptimizedRaw
    {theta : ℝ} {D mu M e : ℕ} (heM : e ≤ M) :
    hybridListRaw theta D mu e ≤ hybridListOptimizedRaw theta D mu M := by
  classical
  unfold hybridListOptimizedRaw
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨e, ?_, rfl⟩
  simpa only [Finset.mem_range, Nat.lt_add_one_iff] using heM

open Classical in
/-- The actual-degree list theorem exposes optimized raw, optimized ceiling, and printed closed
raw bounds, all from one root-set estimate. -/
theorem finite_firstOrder_hybrid_agreement_solutions_card_le_optimized_of_tail
    {F : Type*} [Field F] {n D A mu M h : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F[X] 1)
    (descent : FirstOrderHybridDescent Q mu M h) (z : F)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrderZeroTailListBound (D := D) (A := A)
      (b := mu - descent.actualDegree) domain received
        (MvPolynomial.map (Polynomial.evalRingHom z) descent.tail.equation))
    (S : Finset F[X])
    (hsol : ∀ P ∈ S,
      differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤ hybridListOptimizedRaw (hybridTheta n D A) D mu M ∧
      S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D mu M ∧
      (S.card : ℝ) ≤ hybridLambdaClosed (hybridTheta n D A) D mu M := by
  have hraw := finite_firstOrder_hybrid_agreement_solutions_card_le_raw_of_tail
    domain received Q descent z hD (by omega) hAn hchar htail S hsol haccept
  have hopt := hraw.trans (hybridListRaw_le_hybridListOptimizedRaw descent.actualDegree_le)
  have hceil : S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D mu M := by
    unfold hybridListOptimizedCeil
    exact_mod_cast hopt.trans (Nat.le_ceil _)
  have hclosed := hybridListOptimizedRaw_le_lambdaClosed hD hDA hAn hMmu
  exact ⟨hopt, hceil, hopt.trans hclosed⟩

open Classical in
/-- After specialization to a nonzero ground-field equation, the actual-degree descent and the
characteristic-free order-zero root count give the raw hybrid list charge without any assumed
tail conclusion. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le_raw
    {F : Type*} [Field F] {n D A mu M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q mu M)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤
      hybridListRaw (hybridTheta n D A) D mu descent.actualDegree := by
  classical
  let e := descent.actualDegree
  have heμ : e ≤ mu := by
    have hdegree := descent.stage_degree 0 (Nat.zero_le e)
    have hweight := descent.stage_jetWeight_le 0 (Nat.zero_le e)
    have hle := jetDegree_le_jetWeight Q (1 : Fin 2)
    have hjet : jetDegree Q (1 : Fin 2) ≤ mu := by
      simpa only [firstOrderFieldDerivativeStage_zero, Nat.sub_zero] using hle.trans hweight
    exact descent.actualDegree_eq.trans_le hjet
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : F) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_max_char_guard hchar (by omega) (by omega)
  have htau : TaylorExponentSufficient 1 (D + 1) (hybridTau D) := by
    convert taylorExponentSufficient_two_mul_sub_three 1 (K := D + 1) (by omega) using 1
    unfold hybridTau
    omega
  let tailRoots := S.filter fun P ↦
    differentialSpecialization descent.tail.equation P = 0
  let stageRoots : Fin e → Finset F[X] := fun j ↦ S.filter fun P ↦
    differentialSpecialization (firstOrderFieldDerivativeStage Q j) P = 0 ∧
      differentialSpecialization
        (separant (firstOrderFieldDerivativeStage Q j) (1 : Fin 2)) P ≠ 0
  have htailWeight : jetWeight descent.tail.equation ≤ mu - e := by
    rw [descent.tail.jetWeight]
    exact descent.stage_jetWeight_le e le_rfl
  have htailBound : HasOrderZeroTailListBound (D := D) (A := A) (b := mu - e)
      domain received descent.tail.equation :=
    hasOrderZeroTailListBound_of_nonzero domain received descent.tail_nonzero htailWeight
  have htailCard : (tailRoots.card : ℝ) ≤ ((mu - e : ℕ) : ℝ) := by
    apply htailBound tailRoots
    · intro P hP
      exact haccept P (Finset.mem_filter.mp hP).1
    · intro P hP
      exact (Finset.mem_filter.mp hP).2
  have hstageCard (j : Fin e) : (stageRoots j).card ≤
      hybridTheta n D A * firstOrderCurveFiberStageOne
        (D + 1) (mu - j) (e - j) (hybridTau D) := by
    have hj : j.val < e := j.isLt
    have hv : 0 < mu - j := by omega
    have hu : 0 < e - j := by omega
    have huv : e - j ≤ mu - j := Nat.sub_le_sub_right heμ j
    have hjet : jetTotalDegree (firstOrderFieldDerivativeStage Q j) ≤ mu - j := by
      rw [jetTotalDegree_eq_weightedTotalDegree_elim]
      exact descent.stage_jetWeight_le j (Nat.le_of_lt hj)
    have hderiv : jetDegree (firstOrderFieldDerivativeStage Q j) 1 ≤ e - j :=
      (descent.stage_degree j (Nat.le_of_lt hj)).le
    have hbound := finite_regular_agreement_solutions_card_le_derivativeCapped_of_exponent
      (firstOrderFieldDerivativeStage Q j)
      (D + 1) (D + 1) (mu - j) (e - j) (hybridTau D)
      htau (by unfold hybridTau; omega) (by omega) le_rfl hv hu huv hjet hderiv
      domain received (by omega) hkA hAn (stageRoots j)
      (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).1)
      (fun P hP ↦ (Finset.mem_filter.mp hP).2.1)
      (fun P hP ↦ by
        simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using
          (Finset.mem_filter.mp hP).2.2)
      hbin
      (fun P hP ↦ (haccept P (Finset.mem_filter.mp hP).1).2)
    have hnum : n - (D + 1) + 1 = n - D := by omega
    have hden : A - (D + 1) + 1 = A - D := by omega
    rw [hnum, hden] at hbound
    have hboundReal : ((stageRoots j).card : ℝ) ≤
        (firstOrderCurveFiberStageOne
          (D + 1) (mu - j) (e - j) (hybridTau D) : ℝ) *
          (((n - D : ℕ) : ℝ) / (A - D : ℕ)) := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hbound
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div] using hcast
    simpa only [hybridTheta, mul_comm] using hboundReal
  have hcover : S ⊆ tailRoots ∪ Finset.univ.biUnion stageRoots := by
    intro P hP
    rcases descent.root_coverage P (hsol P hP) with
      htailRoot | ⟨j, hj, hstageRoot, hstageSep⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hP, htailRoot⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hP, hstageRoot, hstageSep⟩
  have hcardNat : S.card ≤ tailRoots.card + ∑ j, (stageRoots j).card := by
    calc
      S.card ≤ (tailRoots ∪ Finset.univ.biUnion stageRoots).card :=
        Finset.card_le_card hcover
      _ ≤ tailRoots.card + (Finset.univ.biUnion stageRoots).card :=
        Finset.card_union_le _ _
      _ ≤ tailRoots.card + ∑ j, (stageRoots j).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hcardReal : (S.card : ℝ) ≤
      (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (S.card : ℝ) ≤ (tailRoots.card : ℝ) + ∑ j, ((stageRoots j).card : ℝ) := hcardReal
    _ ≤ (mu - e : ℕ) + ∑ j : Fin e,
        hybridTheta n D A * firstOrderCurveFiberStageOne
          (D + 1) (mu - j) (e - j) (hybridTau D) := by
      exact add_le_add htailCard (Finset.sum_le_sum fun j _ ↦ hstageCard j)
    _ = hybridListRaw (hybridTheta n D A) D mu e := by
      have hfin : (∑ j : Fin e,
          hybridTheta n D A * firstOrderCurveFiberStageOne
            (D + 1) (mu - j) (e - j) (hybridTau D)) =
          ∑ j ∈ Finset.range e,
            hybridTheta n D A * firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (hybridTau D) := by
        exact Fin.sum_univ_eq_sum_range (α := ℝ) (fun j : ℕ ↦
          hybridTheta n D A * firstOrderCurveFiberStageOne
            (D + 1) (mu - j) (e - j) (hybridTau D)) e
      rw [hfin]
      unfold hybridListRaw hybridB1
      simp only [Nat.cast_sum]
      rw [Finset.mul_sum]
      ring

open Classical in
/-- Concrete actual-field optimized and closed Lambda bounds.  The order-zero tail bound is
derived internally from nonvanishing, so this theorem has no tail-bound premise. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized
    {F : Type*} [Field F] {n D A mu M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (descent : FirstOrderFieldDescent Q mu M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤ hybridListOptimizedRaw (hybridTheta n D A) D mu M ∧
      S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D mu M ∧
      (S.card : ℝ) ≤ hybridLambdaClosed (hybridTheta n D A) D mu M := by
  have hraw := finite_firstOrder_field_hybrid_agreement_solutions_card_le_raw
    domain received Q descent hD (by omega) hAn hchar S hsol haccept
  have hopt := hraw.trans (hybridListRaw_le_hybridListOptimizedRaw descent.actualDegree_le)
  have hceil : S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D mu M := by
    unfold hybridListOptimizedCeil
    exact_mod_cast hopt.trans (Nat.le_ceil _)
  have hclosed := hybridListOptimizedRaw_le_lambdaClosed hD hDA hAn hMmu
  exact ⟨hopt, hceil, hopt.trans hclosed⟩

open Classical in
/-- Direct construction-and-count form: actual descent begins only after one has a nonzero
equation over the ground field. -/
theorem finite_firstOrder_field_hybrid_agreement_solutions_card_le
    {F : Type*} [Field F] {n D A mu M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hweight : jetWeight Q ≤ mu) (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P) :
    (S.card : ℝ) ≤ hybridListOptimizedRaw (hybridTheta n D A) D mu M ∧
      S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D mu M ∧
      (S.card : ℝ) ≤ hybridLambdaClosed (hybridTheta n D A) D mu M := by
  have hactualChar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F :=
    hchar.imp_right (fun hmax ↦ hdegree.trans (Nat.le_max_right D M) |>.trans_lt hmax)
  obtain ⟨descent⟩ := exists_firstOrderFieldDescent Q hQ hweight hdegree hactualChar
  exact finite_firstOrder_field_hybrid_agreement_solutions_card_le_optimized
    domain received Q descent hD hDA hAn hMmu hchar S hsol haccept

open Classical in
/-- The literal automatic first-order recipe constructs its primitive symbolic certificate,
specializes it to a nonzero ground-field equation, and obtains the optimized and printed closed
Lambda bounds under the `max (D,M)` characteristic guard. -/
theorem finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
    {F : Type*} [Field F] {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max D (automaticDerivativeCap rho a) < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℝ) ≤ hybridListOptimizedRaw (hybridTheta n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      S.card ≤ hybridListOptimizedCeil (hybridTheta n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (S.card : ℝ) ≤ hybridLambdaClosed (hybridTheta n D A) D
        (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
    hrho hrhoOne ha haOne hn hD hk hkRate hA domain received (fun _ ↦ 0)
  let phi := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F 1 := MvPolynomial.map phi cert.Q
  obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hweight : jetWeight Q ≤ automaticJetDegree rho a := by
    exact (weightedTotalDegree_map_le phi _ cert.Q).trans cert.toCurve.jetWeight_le
  have hdegree : jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a := by
    exact (degreeOf_map_le phi (some (1 : Fin 2)) cert.Q).trans cert.toCurve.jetDegree_one_le
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    have hiAgree := (Finset.mem_filter.mp hi).2
    simpa using hiAgree
  have hDpos : 1 ≤ D := by omega
  have hDA : D < A := by
    have hkA : k ≤ A := by
      have hapos : 0 < a :=
        (hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha)).trans_le
          (automaticAgreement_le (rho := rho) (a := a))
      have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hkAreal : (k : ℝ) ≤ A := by
        exact (calc
            (k : ℝ) ≤ rho * n := hkRate
            _ < a * n := mul_lt_mul_of_pos_right
              ((rho_lt_automaticAgreement hrho hrhoOne ha).trans_le automaticAgreement_le) hnreal
            _ ≤ A := hA).le
      exact_mod_cast hkAreal
    omega
  have hMmu : automaticDerivativeCap rho a ≤ automaticJetDegree rho a := by
    rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
    exact automaticDerivativeCapRaw_le_jetDegree hrho hrhoOne ha haOne
  have haccept : ∀ P ∈ S, IsAgreementSolution domain received (D + 1) A P := by
    intro P hP
    have hDk : D + 1 = k := by omega
    simpa only [hDk] using hS P hP
  exact finite_firstOrder_field_hybrid_agreement_solutions_card_le
    domain received Q hQ hweight hdegree hDpos hDA hAn hMmu hchar S hsol haccept

end

end ReedSolomon.HiddenDerivative
