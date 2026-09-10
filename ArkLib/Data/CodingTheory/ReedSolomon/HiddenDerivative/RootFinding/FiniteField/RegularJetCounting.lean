/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.BigOperators


/-!
# Counting regular Hasse jets

This file bounds regular scalar jets of a polynomial differential equation over a finite field.
After fixing every assignment coordinate except the selected active jet variable, regular jets
inject into the roots of a nonzero univariate specialization. The number of remaining-coordinate
assignments is the field size to the power `d + 1`.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-! ### Univariate specialization in one distinguished variable -/

/-- The variables other than one distinguished multivariate-polynomial variable. -/
abbrev OtherVariable {σ : Type*} (selected : σ) :=
  {other : σ // other ≠ selected}

/-- Reinsert a distinguished value into an assignment of every other variable. -/
def insertVariableValue {σ : Type*} (selected : σ) (other : OtherVariable selected → F)
    (value : F) : σ → F := by
  classical
  exact fun i ↦ if h : i = selected then value else other ⟨i, h⟩

/-- Regard a multivariate polynomial as univariate in `variable`, then evaluate all other
variables according to `other`. -/
def univariateSpecialization [CommRing F] {σ : Type*} (p : MvPolynomial σ F)
    (selected : σ) (other : OtherVariable selected → F) : F[X] := by
  classical
  exact Polynomial.map (MvPolynomial.eval other) <|
    MvPolynomial.optionEquivLeft F (OtherVariable selected) <|
      MvPolynomial.rename (Equiv.optionSubtypeNe selected).symm p

/-- Evaluating the univariate specialization is the same as evaluating the original
multivariate polynomial after reinserting the distinguished value. -/
theorem eval_univariateSpecialization [CommRing F] {σ : Type*} (p : MvPolynomial σ F)
    (selected : σ) (other : OtherVariable selected → F) (value : F) :
    Polynomial.eval value (univariateSpecialization p selected other) =
      MvPolynomial.eval (insertVariableValue selected other value) p := by
  classical
  rw [univariateSpecialization, ← MvPolynomial.optionEquivLeft_elim_eval]
  rw [MvPolynomial.eval_rename]
  unfold insertVariableValue
  apply congrArg fun assignment ↦ MvPolynomial.eval assignment p
  funext i
  by_cases hi : i = selected
  · subst i
    simp
  · simp [Equiv.optionSubtypeNe_symm_of_ne hi, hi]

/-- Evaluating the other variables cannot increase the degree in the distinguished variable. -/
theorem natDegree_univariateSpecialization_le [CommRing F] {σ : Type*}
    (p : MvPolynomial σ F) (selected : σ)
    (other : OtherVariable selected → F) :
    (univariateSpecialization p selected other).natDegree ≤ p.degreeOf selected := by
  classical
  rw [univariateSpecialization, MvPolynomial.degreeOf_eq_natDegree]
  exact Polynomial.natDegree_map_le

/-- Under `optionEquivLeft`, partial differentiation in the distinguished variable becomes
ordinary univariate differentiation. -/
theorem derivative_optionEquivLeft [CommRing F] {σ : Type*}
    (p : MvPolynomial (Option σ) F) :
    Polynomial.derivative (MvPolynomial.optionEquivLeft F σ p) =
      MvPolynomial.optionEquivLeft F σ (MvPolynomial.pderiv none p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i with
      | none => simp [hp, Polynomial.derivative_mul, mul_comm]
      | some i => simp [hp, Polynomial.derivative_mul, mul_comm]

/-- Specializing all other variables commutes with differentiation in the distinguished
variable. -/
theorem derivative_univariateSpecialization [CommRing F] {σ : Type*}
    (p : MvPolynomial σ F) (selected : σ) (other : OtherVariable selected → F) :
    Polynomial.derivative (univariateSpecialization p selected other) =
      univariateSpecialization (MvPolynomial.pderiv selected p) selected other := by
  classical
  rw [univariateSpecialization, univariateSpecialization, Polynomial.derivative_map,
    derivative_optionEquivLeft]
  apply congrArg fun q ↦ Polynomial.map (MvPolynomial.eval other) <|
    MvPolynomial.optionEquivLeft F (OtherVariable selected) q
  simpa using MvPolynomial.pderiv_rename (Equiv.optionSubtypeNe selected).symm.injective
    selected p

/-! ### Hasse-jet assignments -/

/-- Package a base point and scalar Hasse jet as one assignment to `X, Y₀, ..., Y_d`. -/
def jetAssignment (point : F) (jet : Fin (d + 1) → F) : JetVariable d → F
  | none => point
  | some j => jet j

/-- Restrict a scalar Hasse-jet assignment to every variable except `Y_s`. -/
def otherJetAssignment (s : Fin (d + 1)) (point : F) (jet : Fin (d + 1) → F) :
    OtherVariable (some s : JetVariable d) → F :=
  fun coordinate ↦ jetAssignment point jet coordinate

/-- Reinserting the selected Hasse-jet coordinate reconstructs the full scalar assignment. -/
theorem insertVariableValue_otherJetAssignment (s : Fin (d + 1)) (point : F)
    (jet : Fin (d + 1) → F) :
    insertVariableValue (some s : JetVariable d) (otherJetAssignment s point jet) (jet s) =
      jetAssignment point jet := by
  classical
  funext coordinate
  by_cases hcoordinate : coordinate = some s
  · subst coordinate
    simp [insertVariableValue, jetAssignment]
  · rw [insertVariableValue]
    simp only [dif_neg hcoordinate]
    rfl

/-- The selected univariate specialization evaluates to the differential-polynomial jet
evaluation when its variable is set to the selected jet coordinate. -/
theorem eval_univariateSpecialization_jet [CommRing F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (point : F)
    (jet : Fin (d + 1) → F) :
    Polynomial.eval (jet s)
        (univariateSpecialization Q (some s) (otherJetAssignment s point jet)) =
      jetEvaluation Q point jet := by
  rw [eval_univariateSpecialization, insertVariableValue_otherJetAssignment]
  rfl

/-! ### Regular-jet fibres -/

/-- The assignment away from `Y_s` underlying a regular jet. -/
def _root_.PolynomialDifferential.RegularJet.otherAssignment
    [CommSemiring F] {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (regular : RegularJet Q s) :
    OtherVariable (some s : JetVariable d) → F :=
  otherJetAssignment s regular.1.1 regular.1.2

/-- The selected `Y_s` value underlying a regular jet. -/
def _root_.PolynomialDifferential.RegularJet.activeValue
    [CommSemiring F] {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (regular : RegularJet Q s) : F :=
  regular.1.2 s

/-- A regular jet is determined by its assignment away from `Y_s` and its value at `Y_s`. -/
theorem _root_.PolynomialDifferential.RegularJet.otherAssignment_activeValue_injective
    [CommSemiring F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} :
    Function.Injective fun regular : RegularJet Q s ↦
      (regular.otherAssignment, regular.activeValue) := by
  intro left right heq
  apply Subtype.ext
  apply Prod.ext
  · have hother := congrArg Prod.fst heq
    have hpoint := congrFun hother ⟨none, by simp⟩
    simpa [RegularJet.otherAssignment, otherJetAssignment, jetAssignment] using hpoint
  · funext j
    by_cases hj : j = s
    · subst j
      exact congrArg Prod.snd heq
    · have hother := congrArg Prod.fst heq
      have hjet := congrFun hother ⟨some j, by simp [hj]⟩
      simpa [RegularJet.otherAssignment, otherJetAssignment, jetAssignment] using hjet

/-- A regular jet gives a nonzero univariate specialization after fixing all coordinates other
than its selected active value. -/
theorem univariateSpecialization_ne_zero_of_regular [Field F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (regular : RegularJet Q s) :
    univariateSpecialization Q (some s) regular.otherAssignment ≠ 0 := by
  intro hzero
  have hderivative :
      Polynomial.derivative
          (univariateSpecialization Q (some s) regular.otherAssignment) = 0 := by
    rw [hzero, Polynomial.derivative_zero]
  have hseparant :
      univariateSpecialization (separant Q s) (some s) regular.otherAssignment = 0 := by
    rw [separant, ← derivative_univariateSpecialization]
    exact hderivative
  change univariateSpecialization (separant Q s) (some s)
    (otherJetAssignment s regular.1.1 regular.1.2) = 0 at hseparant
  have heval : jetEvaluation (separant Q s) regular.1.1 regular.1.2 = 0 := by
    calc
      jetEvaluation (separant Q s) regular.1.1 regular.1.2 =
          Polynomial.eval (regular.1.2 s)
            (univariateSpecialization (separant Q s) (some s)
              (otherJetAssignment s regular.1.1 regular.1.2)) :=
        (eval_univariateSpecialization_jet (separant Q s) s regular.1.1 regular.1.2).symm
      _ = 0 := by rw [hseparant]; simp
  exact regular.2.2 heval

/-- Encode a regular jet by its assignment away from `Y_s` and the resulting root of the
univariate specialization. Zero specializations contribute an empty root set. -/
def _root_.PolynomialDifferential.RegularJet.rootEncoding
    [Field F] {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (regular : RegularJet Q s) :
    Σ other : OtherVariable (some s : JetVariable d) → F,
      (univariateSpecialization Q (some s) other).rootSet F := by
  refine ⟨regular.otherAssignment, regular.activeValue, ?_⟩
  apply (Polynomial.mem_rootSet_of_ne
    (univariateSpecialization_ne_zero_of_regular Q s regular)).2
  have heval :
      Polynomial.eval regular.activeValue
        (univariateSpecialization Q (some s) regular.otherAssignment) = 0 := by
    change Polynomial.eval (regular.1.2 s)
      (univariateSpecialization Q (some s)
        (otherJetAssignment s regular.1.1 regular.1.2)) = 0
    rw [eval_univariateSpecialization_jet]
    exact regular.2.1
  simpa using heval

/-- The root-set encoding of regular jets is injective. -/
theorem _root_.PolynomialDifferential.RegularJet.rootEncoding_injective
    [Field F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} :
    Function.Injective (RegularJet.rootEncoding (Q := Q) (s := s)) := by
  intro left right heq
  apply RegularJet.otherAssignment_activeValue_injective
  apply Prod.ext
  · exact congrArg (fun encoded ↦ encoded.1) heq
  · exact congrArg (fun encoded ↦ encoded.2.1) heq

/-! ### Regular jets at a fixed base point -/

/-- Scalar Hasse jets regular for `Q` at one fixed base point. This is the per-point fibre used
when counting root witnesses. -/
def RegularJetAt [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (point : F) :=
  {jet : Fin (d + 1) → F // IsRegularJet Q s point jet}

/-- A fixed-point regular jet gives a regular point-jet pair. -/
def RegularJetAt.toRegularJet [CommSemiring F] {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {point : F} (regular : RegularJetAt Q s point) : RegularJet Q s :=
  ⟨(point, regular.1), regular.2⟩

/-- The jet coordinates other than one selected coordinate `s`. -/
abbrev OtherJetCoordinate (s : Fin (d + 1)) :=
  {j : Fin (d + 1) // j ≠ s}

/-- Restrict a scalar Hasse jet to all coordinates other than `s`. -/
def otherJetCoordinates (s : Fin (d + 1)) (jet : Fin (d + 1) → F) :
    OtherJetCoordinate s → F :=
  fun j ↦ jet j

/-- Reinsert one selected value into an assignment of all other Hasse-jet coordinates. -/
def insertJetValue (s : Fin (d + 1)) (other : OtherJetCoordinate s → F) (value : F) :
    Fin (d + 1) → F := by
  classical
  exact fun j ↦ if h : j = s then value else other ⟨j, h⟩

/-- Fix `X` to `point` and assign every Hasse-jet variable other than `Y_s`. -/
def fixedPointOtherAssignment [Zero F] (s : Fin (d + 1)) (point : F)
    (other : OtherJetCoordinate s → F) : OtherVariable (some s : JetVariable d) → F :=
  otherJetAssignment s point (insertJetValue s other 0)

/-- Restricting a full jet and then forming the fixed-point assignment recovers its assignment
away from `Y_s`. -/
theorem fixedPointOtherAssignment_otherJetCoordinates [Zero F] (s : Fin (d + 1))
    (point : F) (jet : Fin (d + 1) → F) :
    fixedPointOtherAssignment s point (otherJetCoordinates s jet) =
      otherJetAssignment s point jet := by
  funext coordinate
  rcases coordinate with ⟨coordinate, hcoordinate⟩
  cases coordinate with
  | none => rfl
  | some j =>
      have hj : j ≠ s := by
        intro hjs
        apply hcoordinate
        simp [hjs]
      simp [fixedPointOtherAssignment, otherJetAssignment, insertJetValue,
        otherJetCoordinates, jetAssignment, hj]

/-- The univariate specialization at a fixed base point and fixed non-active jet coordinates. -/
def fixedPointSpecialization [CommRing F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (point : F) (other : OtherJetCoordinate s → F) : F[X] :=
  univariateSpecialization Q (some s) (fixedPointOtherAssignment s point other)

/-- A fixed-point regular jet lies on its corresponding univariate specialization. -/
theorem eval_fixedPointSpecialization_eq_zero_of_regular [Field F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (point : F)
    (regular : RegularJetAt Q s point) :
    Polynomial.eval (regular.1 s)
      (fixedPointSpecialization Q s point (otherJetCoordinates s regular.1)) = 0 := by
  rw [fixedPointSpecialization, fixedPointOtherAssignment_otherJetCoordinates,
    eval_univariateSpecialization_jet]
  exact regular.2.1

/-- A fixed-point regular jet gives a nonzero univariate specialization in `Y_s`. -/
theorem fixedPointSpecialization_ne_zero_of_regular [Field F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (point : F)
    (regular : RegularJetAt Q s point) :
    fixedPointSpecialization Q s point (otherJetCoordinates s regular.1) ≠ 0 := by
  rw [fixedPointSpecialization, fixedPointOtherAssignment_otherJetCoordinates]
  change univariateSpecialization Q (some s)
    (RegularJet.otherAssignment regular.toRegularJet) ≠ 0
  exact univariateSpecialization_ne_zero_of_regular Q s regular.toRegularJet

/-- Encode a fixed-point regular jet by its non-active jet coordinates and active root. -/
def RegularJetAt.rootEncoding [Field F] {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {point : F} (regular : RegularJetAt Q s point) :
    Σ other : OtherJetCoordinate s → F,
      (fixedPointSpecialization Q s point other).rootSet F := by
  refine ⟨otherJetCoordinates s regular.1, regular.1 s, ?_⟩
  apply (Polynomial.mem_rootSet_of_ne
    (fixedPointSpecialization_ne_zero_of_regular Q s point regular)).2
  simpa using eval_fixedPointSpecialization_eq_zero_of_regular Q s point regular

/-- A fixed-point jet is determined by its non-active coordinates and active value. -/
theorem RegularJetAt.otherCoordinates_activeValue_injective [CommSemiring F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} {point : F} :
    Function.Injective fun regular : RegularJetAt Q s point ↦
      (otherJetCoordinates s regular.1, regular.1 s) := by
  intro left right heq
  apply Subtype.ext
  funext j
  by_cases hj : j = s
  · subst j
    exact congrArg Prod.snd heq
  · have hother := congrArg Prod.fst heq
    exact congrFun hother ⟨j, hj⟩

/-- The fixed-point root-set encoding is injective. -/
theorem RegularJetAt.rootEncoding_injective [Field F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} {point : F} :
    Function.Injective (RegularJetAt.rootEncoding (Q := Q) (s := s) (point := point)) := by
  intro left right heq
  apply RegularJetAt.otherCoordinates_activeValue_injective
  apply Prod.ext
  · exact congrArg (fun encoded ↦ encoded.1) heq
  · exact congrArg (fun encoded ↦ encoded.2.1) heq

/-! ### Cardinality bounds -/

/-- Removing one selected jet variable from `X, Y₀, ..., Y_d` leaves exactly `d + 1`
coordinates. -/
theorem card_otherJetVariables (s : Fin (d + 1)) :
    Fintype.card (OtherVariable (some s : JetVariable d)) = d + 1 := by
  classical
  rw [Fintype.card_subtype_compl
    (fun coordinate : JetVariable d ↦ coordinate = (some s : JetVariable d))]
  simp [JetVariable]

/-- Exact function-space cardinality for assignments away from one selected jet variable. -/
theorem card_otherJetAssignments [Fintype F] (s : Fin (d + 1)) :
    Fintype.card (OtherVariable (some s : JetVariable d) → F) =
      Fintype.card F ^ (d + 1) := by
  classical
  rw [Fintype.card_fun, card_otherJetVariables]

/-- Removing `Y_s` from the `d + 1` Hasse-jet coordinates leaves exactly `d` coordinates. -/
theorem card_otherJetCoordinates (s : Fin (d + 1)) :
    Fintype.card (OtherJetCoordinate s) = d := by
  classical
  rw [Fintype.card_subtype_compl (fun j : Fin (d + 1) ↦ j = s)]
  simp

/-- Exact cardinality of assignments to the Hasse-jet coordinates other than `Y_s`. -/
theorem card_otherJetCoordinateAssignments [Fintype F] (s : Fin (d + 1)) :
    Fintype.card (OtherJetCoordinate s → F) = Fintype.card F ^ d := by
  classical
  rw [Fintype.card_fun, card_otherJetCoordinates]

/-- At one fixed base point, regular jets are bounded by the selected individual degree times
`q ^ d`, where `q` is the field cardinality. -/
theorem natCard_regularJetAt_le [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (point : F) :
    Nat.card (RegularJetAt Q s point) ≤ jetDegree Q s * Nat.card F ^ d := by
  classical
  let _ := Fintype.ofFinite F
  calc
    Nat.card (RegularJetAt Q s point) ≤
        Nat.card (Σ other : OtherJetCoordinate s → F,
          (fixedPointSpecialization Q s point other).rootSet F) :=
      Nat.card_le_card_of_injective RegularJetAt.rootEncoding
        RegularJetAt.rootEncoding_injective
    _ = ∑ other : OtherJetCoordinate s → F,
          Fintype.card ((fixedPointSpecialization Q s point other).rootSet F) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ ≤ ∑ _other : OtherJetCoordinate s → F, jetDegree Q s := by
      apply Finset.sum_le_sum
      intro other _hother
      rw [Set.fintypeCard_eq_ncard]
      exact (Polynomial.ncard_rootSet_le (fixedPointSpecialization Q s point other) F).trans
        (natDegree_univariateSpecialization_le Q (some s)
          (fixedPointOtherAssignment s point other))
    _ = Fintype.card (OtherJetCoordinate s → F) * jetDegree Q s := by simp
    _ = jetDegree Q s * Nat.card F ^ d := by
      rw [card_otherJetCoordinateAssignments, Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _

/-- Regular jets are bounded by the selected individual degree times the number of assignments
to the other `d + 1` coordinates. -/
theorem natCard_regularJet_le_degree_mul_pow [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    Nat.card (RegularJet Q s) ≤ jetDegree Q s * Nat.card F ^ (d + 1) := by
  classical
  let _ := Fintype.ofFinite F
  calc
    Nat.card (RegularJet Q s) ≤
        Nat.card (Σ other : OtherVariable (some s : JetVariable d) → F,
          (univariateSpecialization Q (some s) other).rootSet F) :=
      Nat.card_le_card_of_injective RegularJet.rootEncoding
        RegularJet.rootEncoding_injective
    _ = ∑ other : OtherVariable (some s : JetVariable d) → F,
          Fintype.card ((univariateSpecialization Q (some s) other).rootSet F) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ ≤ ∑ _other : OtherVariable (some s : JetVariable d) → F, jetDegree Q s := by
      apply Finset.sum_le_sum
      intro other _hother
      rw [Set.fintypeCard_eq_ncard]
      exact (Polynomial.ncard_rootSet_le (univariateSpecialization Q (some s) other) F).trans
        (natDegree_univariateSpecialization_le Q (some s) other)
    _ = Fintype.card (OtherVariable (some s : JetVariable d) → F) * jetDegree Q s := by
      simp
    _ = jetDegree Q s * Nat.card F ^ (d + 1) := by
      rw [card_otherJetAssignments, Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _

/-- Division-free regular-jet bound in the factorization used by differential root counting. -/
theorem natCard_regularJet_le [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    Nat.card (RegularJet Q s) ≤ Nat.card F * jetDegree Q s * Nat.card F ^ d := by
  calc
    Nat.card (RegularJet Q s) ≤ jetDegree Q s * Nat.card F ^ (d + 1) :=
      natCard_regularJet_le_degree_mul_pow Q s
    _ = Nat.card F * jetDegree Q s * Nat.card F ^ d := by
      rw [pow_succ]
      ac_rfl

/-! ### Boundary canaries -/

namespace RegularJetCountingCanary

/-- At a fixed point and derivative order zero, there are no remaining free jet coordinates. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F 0) (s : Fin 1) (point : F) :
    Nat.card (RegularJetAt Q s point) ≤ jetDegree Q s := by
  simpa using natCard_regularJetAt_le Q s point

/-- At derivative order zero, the only coordinate away from `Y₀` is `X`. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F 0) (s : Fin 1) :
    Nat.card (RegularJet Q s) ≤ Nat.card F * jetDegree Q s := by
  simpa using natCard_regularJet_le Q s

/-- Individual degree zero forces the regular-jet type to have cardinality zero. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hdegree : jetDegree Q s = 0) : Nat.card (RegularJet Q s) = 0 := by
  exact Nat.le_zero.mp <| by
    simpa [hdegree] using natCard_regularJet_le_degree_mul_pow Q s

/-- At any fixed point, individual degree zero leaves no regular jets. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (point : F) (hdegree : jetDegree Q s = 0) : Nat.card (RegularJetAt Q s point) = 0 := by
  exact Nat.le_zero.mp <| by
    simpa [hdegree] using natCard_regularJetAt_le Q s point

/-- The zero differential polynomial has no regular jets. -/
example [Field F] [Finite F] (s : Fin (d + 1)) :
    Nat.card (RegularJet (0 : DifferentialPolynomial F d) s) = 0 := by
  exact Nat.le_zero.mp <| by
    simpa [jetDegree] using
      natCard_regularJet_le_degree_mul_pow (0 : DifferentialPolynomial F d) s

/-- The zero differential polynomial has no fixed-point regular jets. -/
example [Field F] [Finite F] (s : Fin (d + 1)) (point : F) :
    Nat.card (RegularJetAt (0 : DifferentialPolynomial F d) s point) = 0 := by
  exact Nat.le_zero.mp <| by
    simpa [jetDegree] using
      natCard_regularJetAt_le (0 : DifferentialPolynomial F d) s point

end RegularJetCountingCanary

end

end HiddenDerivative
end ReedSolomon
