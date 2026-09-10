/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveStages
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain
public import ArkLib.Data.Polynomial.Differential.DerivativeDescent

/-!
# First-order descent through the actual `Y₁` degree

For a first-order symbolic equation, this file differentiates only in `Y₁`, exactly through its
actual degree `e`. The characteristic guard is therefore `p > e`; the total jet bound may be
larger than the characteristic. The last derivative is nonzero and independent of `Y₁`, so it
has an order-zero presentation in `X,Y₀`. Every root either reaches that ordinary tail or is
regular at one of the preceding `Y₁` stages.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative

open MvPolynomial SymbolicReceivedInterpolation SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- If the leading individual degree is a nonzero scalar, one partial derivative is nonzero and
loses exactly one in that variable. This form covers both characteristic zero and positive
characteristic without encoding characteristic zero as an impossible inequality against zero. -/
theorem pderiv_ne_zero_and_degreeOf_eq_sub_one_of_natCast_ne_zero
    {R σ : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    (i : σ) (p : MvPolynomial σ R) (hpos : 0 < degreeOf i p)
    (hcast : (degreeOf i p : R) ≠ 0) :
    pderiv i p ≠ 0 ∧ degreeOf i (pderiv i p) = degreeOf i p - 1 := by
  classical
  have hsupp : p.support.Nonempty := support_nonempty.mpr <|
    ne_zero_of_degreeOf_ne_zero (p := p) (i := i) (Nat.ne_of_gt hpos)
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup p.support hsupp fun m ↦ m i
  rw [← degreeOf_eq_sup i p] at heq
  have hmi : m i ≠ 0 := by omega
  let m' := m - Finsupp.single i 1
  have hm'_add : m' + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel hmi
  have hm'i : m' i + 1 = m i := by
    dsimp [m']
    rw [Finsupp.single_eq_same]
    omega
  have hcast' : (m i : R) ≠ 0 := by simpa [heq] using hcast
  have hcast_eq : (↑(m' i) + 1 : R) = (m i : R) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hm'i]
  have hm'supp : m' ∈ (pderiv i p).support := by
    rw [MvPolynomial.mem_support_iff, coeff_pderiv, hm'_add, hcast_eq]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) hcast'
  constructor
  · exact support_nonempty.mp ⟨m', hm'supp⟩
  · apply Nat.le_antisymm (degreeOf_pderiv_le_sub_one i p)
    have hlower := monomial_le_degreeOf i hm'supp
    rw [heq]
    omega

end MvPolynomial

/-- The symbolic `j`-th derivative in `Y₁`. -/
def firstOrderDerivativeStage {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) (j : ℕ) : DifferentialPolynomial F[X] 1 :=
  jetDerivative Q (1 : Fin 2) j

@[simp]
theorem firstOrderDerivativeStage_zero {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) : firstOrderDerivativeStage Q 0 = Q := by
  simp [firstOrderDerivativeStage]

@[simp]
theorem firstOrderDerivativeStage_succ {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) (j : ℕ) :
    firstOrderDerivativeStage Q (j + 1) =
      separant (firstOrderDerivativeStage Q j) (1 : Fin 2) := by
  simp [firstOrderDerivativeStage]

/-- The base-field characteristic guard makes every positive scalar through `e` nonzero in the
symbolic coefficient ring `F[Z]`. -/
theorem natCast_polynomial_ne_zero_of_char_guard
    {F : Type*} [Field F] {e m : ℕ}
    (hchar : ringChar F = 0 ∨ e < ringChar F) (hm : 0 < m) (hme : m ≤ e) :
    (m : F[X]) ≠ 0 := by
  intro hz
  have hscalar : (m : F) = 0 := by
    simpa using congrArg (Polynomial.eval (0 : F)) hz
  have hdiv := (ringChar.spec F m).mp hscalar
  rcases hchar with hzero | hlt
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hm (hme.trans_lt hlt) hdiv

/-- All actual `Y₁` stages through `e` are nonzero and have degree `e-j`. -/
theorem firstOrderDerivativeStage_ne_zero_and_degree
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1)
    (hQ : Q ≠ 0) (e : ℕ) (he : jetDegree Q (1 : Fin 2) = e)
    (hchar : ringChar F = 0 ∨ e < ringChar F) :
    ∀ j ≤ e, firstOrderDerivativeStage Q j ≠ 0 ∧
      jetDegree (firstOrderDerivativeStage Q j) (1 : Fin 2) = e - j := by
  intro j hj
  induction j with
  | zero => simpa [he] using And.intro hQ he
  | succ j ih =>
      have hjle : j ≤ e := by omega
      obtain ⟨hne, hdegree⟩ := ih hjle
      have hpos : 0 < jetDegree (firstOrderDerivativeStage Q j) (1 : Fin 2) := by
        rw [hdegree]
        omega
      have hcast :
          (jetDegree (firstOrderDerivativeStage Q j) (1 : Fin 2) : F[X]) ≠ 0 := by
        apply natCast_polynomial_ne_zero_of_char_guard hchar
        · exact hpos
        · rw [hdegree]
          exact Nat.sub_le _ _
      have hdegree' :
          degreeOf (some (1 : Fin 2)) (firstOrderDerivativeStage Q j) = e - j := hdegree
      have hstep := MvPolynomial.pderiv_ne_zero_and_degreeOf_eq_sub_one_of_natCast_ne_zero
        (some (1 : Fin 2)) (firstOrderDerivativeStage Q j) hpos hcast
      rw [firstOrderDerivativeStage_succ]
      exact ⟨hstep.1, by
        change degreeOf (some (1 : Fin 2))
          (MvPolynomial.pderiv (some (1 : Fin 2)) (firstOrderDerivativeStage Q j)) = _
        rw [hstep.2, hdegree']
        omega⟩

/-- Each `Y₁` derivative spends one unit of total jet degree. -/
theorem firstOrderDerivativeStage_jetWeight_le_sub
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1) (j : ℕ) :
    jetWeight (firstOrderDerivativeStage Q j) ≤ jetWeight Q - j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [firstOrderDerivativeStage_succ]
      have hstep := jetWeight_separant_le (firstOrderDerivativeStage Q j) (1 : Fin 2)
      omega

/-- Consequently a global total-jet cap drops from `mu` to `mu-j`. -/
theorem firstOrderDerivativeStage_jetWeight_le
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1) {mu j : ℕ}
    (hweight : jetWeight Q ≤ mu) :
    jetWeight (firstOrderDerivativeStage Q j) ≤ mu - j :=
  (firstOrderDerivativeStage_jetWeight_le_sub Q j).trans (Nat.sub_le_sub_right hweight j)

/-- Differentiation in a jet variable does not increase the challenge degree of any
coefficient. -/
theorem firstOrderDerivativeStage_challengeHeight_le
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1) {h : ℕ}
    (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    ∀ j u, (MvPolynomial.coeff u (firstOrderDerivativeStage Q j)).natDegree ≤ h := by
  intro j
  induction j with
  | zero => simpa using hQ
  | succ j ih =>
      rw [firstOrderDerivativeStage_succ]
      exact separant_challengeHeight_le (firstOrderDerivativeStage Q j) (1 : Fin 2) ih

/-- An order-zero presentation of a first-order equation independent of `Y₁`. -/
structure FirstOrderTailPresentation {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) where
  equation : DifferentialPolynomial F[X] 0
  ambient_eq : MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2)) equation = Q

/-- Degree zero in `Y₁` is exactly what is needed to restrict a first-order equation to
`X,Y₀`. -/
theorem exists_firstOrderTailPresentation
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1)
    (hdegree : jetDegree Q (1 : Fin 2) = 0) :
    Nonempty (FirstOrderTailPresentation Q) := by
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

/-- The order-zero presentation of a nonzero ambient tail is nonzero. -/
theorem FirstOrderTailPresentation.nonzero
    {F : Type*} [Field F] {Q : DifferentialPolynomial F[X] 1}
    (tail : FirstOrderTailPresentation Q) (hQ : Q ≠ 0) : tail.equation ≠ 0 := by
  intro hz
  apply hQ
  rw [← tail.ambient_eq, hz, map_zero]

/-- The order-zero presentation preserves differential specialization after every coefficient
specialization. -/
theorem FirstOrderTailPresentation.specialization
    {F E : Type*} [Field F] [Field E] (φ : F[X] →+* E)
    {Q : DifferentialPolynomial F[X] 1} (tail : FirstOrderTailPresentation Q) (P : E[X]) :
    differentialSpecialization (MvPolynomial.map φ tail.equation) P =
      differentialSpecialization (MvPolynomial.map φ Q) P := by
  calc
    _ = differentialSpecialization
        (MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2))
          (MvPolynomial.map φ tail.equation)) P :=
      (differentialSpecialization_rename_jetPrefixEmbedding
        (0 : Fin 2) (MvPolynomial.map φ tail.equation) P).symm
    _ = differentialSpecialization
        (MvPolynomial.map φ
          (MvPolynomial.rename (jetPrefixEmbedding (0 : Fin 2)) tail.equation)) P := by
      rw [MvPolynomial.map_rename]
    _ = _ := by rw [tail.ambient_eq]

/-- Restricting to `X,Y₀` preserves the symbolic challenge-height bound. -/
theorem FirstOrderTailPresentation.challengeHeight_le
    {F : Type*} [Field F] {Q : DifferentialPolynomial F[X] 1}
    (tail : FirstOrderTailPresentation Q) {h : ℕ}
    (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    ∀ u, (MvPolynomial.coeff u tail.equation).natDegree ≤ h := by
  intro u
  rw [← MvPolynomial.coeff_rename_mapDomain _
    (jetPrefixEmbedding (0 : Fin 2)).injective, tail.ambient_eq]
  exact hQ _

/-- Abstract finite first-difference coverage: a root at stage zero either reaches the tail or
has a last zero stage followed by a nonzero next stage. -/
theorem root_reaches_tail_or_regular_stage
    {R : Type*} [Zero R] (stage : ℕ → R) (e : ℕ) (hzero : stage 0 = 0) :
    stage e = 0 ∨ ∃ j < e, stage j = 0 ∧ stage (j + 1) ≠ 0 := by
  classical
  induction e with
  | zero => exact Or.inl hzero
  | succ e ih =>
      rcases ih with htail | ⟨j, hj, hz, hnz⟩
      · by_cases hnext : stage (e + 1) = 0
        · exact Or.inl hnext
        · exact Or.inr ⟨e, Nat.lt_succ_self e, htail, hnext⟩
      · exact Or.inr ⟨j, hj.trans (Nat.lt_succ_self e), hz, hnz⟩

/-- Complete first-order descent package. It stops after the actual `Y₁` degree, leaving an
order-zero equation rather than differentiating in `Y₀`. -/
structure FirstOrderHybridDescent {F : Type*} [Field F]
    (Q : DifferentialPolynomial F[X] 1) (mu M h : ℕ) where
  actualDegree : ℕ
  actualDegree_eq : actualDegree = jetDegree Q (1 : Fin 2)
  actualDegree_le : actualDegree ≤ M
  stage_nonzero : ∀ j ≤ actualDegree, firstOrderDerivativeStage Q j ≠ 0
  stage_degree : ∀ j ≤ actualDegree,
    jetDegree (firstOrderDerivativeStage Q j) (1 : Fin 2) = actualDegree - j
  stage_jetWeight_le : ∀ j ≤ actualDegree,
    jetWeight (firstOrderDerivativeStage Q j) ≤ mu - j
  stage_challengeHeight_le : ∀ j u,
    (MvPolynomial.coeff u (firstOrderDerivativeStage Q j)).natDegree ≤ h
  tail : FirstOrderTailPresentation (firstOrderDerivativeStage Q actualDegree)
  tail_nonzero : tail.equation ≠ 0

/-- The ordinary tail retains the original coefficient-height bound. -/
theorem FirstOrderHybridDescent.tail_challengeHeight_le
    {F : Type*} [Field F] {Q : DifferentialPolynomial F[X] 1} {mu M h : ℕ}
    (descent : FirstOrderHybridDescent Q mu M h) :
    ∀ u, (MvPolynomial.coeff u descent.tail.equation).natDegree ≤ h :=
  descent.tail.challengeHeight_le (descent.stage_challengeHeight_le descent.actualDegree)

/-- A first-order equation with the advertised support bounds admits the descent package under
the actual-degree characteristic guard. -/
theorem exists_firstOrderHybridDescent
    {F : Type*} [Field F] (Q : DifferentialPolynomial F[X] 1) {mu M h : ℕ}
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hheight : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    (hchar : ringChar F = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar F) :
    Nonempty (FirstOrderHybridDescent Q mu M h) := by
  let e := jetDegree Q (1 : Fin 2)
  have hstages := firstOrderDerivativeStage_ne_zero_and_degree Q hQ e rfl hchar
  have htailDegree : jetDegree (firstOrderDerivativeStage Q e) (1 : Fin 2) = 0 := by
    simpa [e] using (hstages e le_rfl).2
  obtain ⟨tail⟩ := exists_firstOrderTailPresentation
    (firstOrderDerivativeStage Q e) htailDegree
  refine ⟨{
    actualDegree := e
    actualDegree_eq := rfl
    actualDegree_le := hdegree
    stage_nonzero := fun j hj ↦ (hstages j hj).1
    stage_degree := fun j hj ↦ (hstages j hj).2
    stage_jetWeight_le := fun j _ ↦ firstOrderDerivativeStage_jetWeight_le Q hweight
    stage_challengeHeight_le := firstOrderDerivativeStage_challengeHeight_le Q hheight
    tail := tail
    tail_nonzero := tail.nonzero (hstages e le_rfl).1
  }⟩

/-- A finite first-order curve certificate supplies all support and height hypotheses for descent;
only the characteristic at its actual `Y₁` degree remains. -/
theorem FirstOrderCurveCertificate.exists_hybridDescent
    {F : Type u} [Field F] {D A m M mu k h n N : ℕ}
    {domain : Fin n ↪ F} {w : Fin n → F[X]} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderCurveCertificate.{u, u} D A m M mu k h domain w columns)
    (hchar : ringChar F = 0 ∨ jetDegree cert.Q (1 : Fin 2) < ringChar F) :
    Nonempty (FirstOrderHybridDescent cert.Q mu M h) :=
  exists_firstOrderHybridDescent cert.Q cert.nonzero cert.jetWeight_le cert.jetDegree_one_le
    cert.challengeDegree_le hchar

/-- The public derivative cap implies the exact characteristic guard used by the descent. This
still permits `mu` to exceed the characteristic. -/
theorem FirstOrderCurveCertificate.exists_hybridDescent_of_derivativeCap_lt_ringChar
    {F : Type u} [Field F] {D A m M mu k h n N : ℕ}
    {domain : Fin n ↪ F} {w : Fin n → F[X]} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderCurveCertificate.{u, u} D A m M mu k h domain w columns)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    Nonempty (FirstOrderHybridDescent cert.Q mu M h) := by
  apply cert.exists_hybridDescent
  exact hchar.imp_right (fun hM ↦ cert.jetDegree_one_le.trans_lt hM)

/-- After any coefficient specialization, every root of the original equation either solves the
ordinary tail or is regular at a `Y₁` stage with index strictly below the actual degree. -/
theorem FirstOrderHybridDescent.root_coverage
    {F E : Type*} [Field F] [Field E]
    {Q : DifferentialPolynomial F[X] 1} {mu M h : ℕ}
    (descent : FirstOrderHybridDescent Q mu M h) (φ : F[X] →+* E) (P : E[X])
    (hroot : differentialSpecialization (MvPolynomial.map φ Q) P = 0) :
    differentialSpecialization (MvPolynomial.map φ descent.tail.equation) P = 0 ∨
      ∃ j < descent.actualDegree,
        differentialSpecialization
            (MvPolynomial.map φ (firstOrderDerivativeStage Q j)) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map φ (firstOrderDerivativeStage Q j)) (1 : Fin 2)) P ≠ 0 := by
  let value : ℕ → E[X] := fun j ↦
    differentialSpecialization (MvPolynomial.map φ (firstOrderDerivativeStage Q j)) P
  have hzero : value 0 = 0 := by simpa [value] using hroot
  rcases root_reaches_tail_or_regular_stage value descent.actualDegree hzero with
    htail | ⟨j, hj, hz, hnz⟩
  · left
    rw [descent.tail.specialization φ P]
    exact htail
  · right
    refine ⟨j, hj, hz, ?_⟩
    simpa only [value, firstOrderDerivativeStage_succ, separant, MvPolynomial.pderiv_map] using hnz

namespace HybridDescentCanary

/-- In characteristic two, the equation `Y₁` has actual `Y₁` degree one. -/
def smallCharacteristicEquation : DifferentialPolynomial (ZMod 2)[X] 1 :=
  MvPolynomial.X (some (1 : Fin 2))

/-- The actual-degree descent works in characteristic two even with the advertised total cap
`mu = 3`, which is already at least the characteristic. -/
theorem smallCharacteristic_with_large_totalCap :
    ringChar (ZMod 2) ≤ 3 ∧
      Nonempty (FirstOrderHybridDescent smallCharacteristicEquation 3 1 0) := by
  constructor
  · norm_num [ZMod.ringChar_zmod_n]
  · apply exists_firstOrderHybridDescent smallCharacteristicEquation
    · intro h
      have hcoeff := congrArg
        (MvPolynomial.coeff (Finsupp.single (some (1 : Fin 2)) 1)) h
      simp [smallCharacteristicEquation] at hcoeff
    · rw [smallCharacteristicEquation, jetWeight, MvPolynomial.X,
        MvPolynomial.weightedTotalDegree_monomial]
      · simp [Finsupp.weight_apply]
      · exact one_ne_zero
    · simp [smallCharacteristicEquation, jetDegree]
    · intro u
      rw [smallCharacteristicEquation, MvPolynomial.coeff_X]
      split_ifs <;> simp
    · right
      norm_num [smallCharacteristicEquation, jetDegree, ZMod.ringChar_zmod_n]

end HybridDescentCanary

end

end ReedSolomon.HiddenDerivative
