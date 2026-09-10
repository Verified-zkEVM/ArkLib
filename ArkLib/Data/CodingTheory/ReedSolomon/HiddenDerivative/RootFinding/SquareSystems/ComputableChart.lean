/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import ArkLib.ToCompPoly.Multivariate.Substitution
public import ArkLib.ToCompPoly.Multivariate.HeadCoefficient
public import ArkLib.ToCompPoly.Multivariate.Eval
/-!
# Computable initial Taylor-chart equations

These constructors specialize the independent variable of a concrete differential equation while
keeping the initial jet variables symbolic. The denominator is obtained by differentiating the
concrete equation in its highest jet variable before specialization. Their semantic theorems make
the resulting `CMvPolynomial`s usable with the existing rational Taylor chart.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Substitute the center for concrete variable zero and retain all jet variables. -/
def computableInitialJetSubstitution (center : F) (r : ℕ) :
    Fin (r + 2) → CPoly.CMvPolynomial (r + 1) F :=
  Fin.cases (CPoly.CMvPolynomial.C center) CPoly.CMvPolynomial.X

/-- Concrete initial hypersurface equation at a fixed center. -/
def computableInitialJetEquation {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial (r + 1) F :=
  CPoly.CMvPolynomial.bind₁ (computableInitialJetSubstitution center r) Q

/-- Concrete initial separant, obtained from the highest-jet partial derivative. -/
def computableInitialJetSeparant {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial (r + 1) F :=
  CPoly.CMvPolynomial.bind₁ (computableInitialJetSubstitution center r)
    (CPoly.CMvPolynomial.partialDerivative (Fin.last (r + 1)) Q)

theorem finToJetVariable_injective (r : ℕ) :
    Function.Injective (finToJetVariable r) := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j hij => ?_) j
    simp [finToJetVariable] at hij
  · refine Fin.cases (fun hij => ?_) (fun j hij => ?_) j
    · simp [finToJetVariable] at hij
    · exact congrArg Fin.succ (Option.some.inj hij)

@[simp]
theorem finToJetVariable_last (r : ℕ) :
    finToJetVariable r (Fin.last (r + 1)) = some (Fin.last r) := by
  rfl

/-- The concrete initial equation denotes the mathematical initial chart equation. -/
theorem fromCMvPolynomial_computableInitialJetEquation {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    CPoly.fromCMvPolynomial (computableInitialJetEquation center Q) =
      initialJetEquation center (semanticEquation Q) := by
  rw [computableInitialJetEquation, CPoly.CMvPolynomial.fromCMvPolynomial_bind₁]
  rw [initialJetEquation, semanticEquation, MvPolynomial.aeval_rename]
  have hsubstitution :
      (fun i => CPoly.fromCMvPolynomial (computableInitialJetSubstitution center r i)) =
        (fun i => Option.elim i (MvPolynomial.C center) MvPolynomial.X) ∘
          finToJetVariable r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_C center
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_X j
  rw [hsubstitution]

/-- The concrete denominator denotes the mathematical initial separant. -/
theorem fromCMvPolynomial_computableInitialJetSeparant {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    CPoly.fromCMvPolynomial (computableInitialJetSeparant center Q) =
      initialJetSeparant center (semanticEquation Q) := by
  rw [computableInitialJetSeparant, CPoly.CMvPolynomial.fromCMvPolynomial_bind₁]
  rw [CPoly.CMvPolynomial.fromCMvPolynomial_partialDerivative]
  unfold initialJetSeparant semanticEquation separant
  have hderivative := MvPolynomial.pderiv_rename (finToJetVariable_injective r)
    (Fin.last (r + 1)) (CPoly.fromCMvPolynomial Q)
  rw [finToJetVariable_last] at hderivative
  rw [hderivative]
  rw [MvPolynomial.aeval_rename]
  have hsubstitution :
      (fun i => CPoly.fromCMvPolynomial (computableInitialJetSubstitution center r i)) =
        (fun i => Option.elim i (MvPolynomial.C center) MvPolynomial.X) ∘
          finToJetVariable r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_C center
    · exact CPoly.CMvPolynomial.fromCMvPolynomial_X j
  rw [hsubstitution]

/-! ### Universal Taylor residual -/

/-- The concrete variable order `ξ, c₀, ..., c_(K-1)` used for universal Taylor residuals. -/
def finToTaylorVariable (K : ℕ) : Fin (K + 1) → Option (Fin K) :=
  _root_.finSuccEquiv K

/-- A concrete universal Hasse jet in variables `ξ, c₀, ..., c_(K-1)`. -/
def computableUniversalTaylorMonomial {K : ℕ} (j : ℕ) (l : Fin K) :
    CPoly.CMvMonomial (K + 1) :=
  Vector.ofFn (Fin.cases (l.val - j) (fun i => if i = l then 1 else 0))

def computableUniversalTaylorJet (K j : ℕ) : CPoly.CMvPolynomial (K + 1) F :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin K => j ≤ l.val),
    CPoly.CMvPolynomial.monomial
      (computableUniversalTaylorMonomial j l)
      (Nat.choose l.val j : F)

/-- Concrete universal differential residual in variables `ξ, c₀, ..., c_(K-1)`. -/
def computableUniversalTaylorResidual {r : ℕ} (K : ℕ) (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) : CPoly.CMvPolynomial (K + 1) F :=
  CPoly.CMvPolynomial.bind₁
    (Fin.cases
      (CPoly.CMvPolynomial.C center + CPoly.CMvPolynomial.X 0)
      (fun j => computableUniversalTaylorJet K j.val)) Q

theorem toFinsupp_computableUniversalTaylorMonomial {K : ℕ} (j : ℕ) (l : Fin K) :
    (computableUniversalTaylorMonomial j l).toFinsupp =
      Finsupp.single l.succ 1 + Finsupp.single 0 (l.val - j) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [computableUniversalTaylorMonomial, CPoly.CMvMonomial.toFinsupp]
  · by_cases hi : i = l
    · subst i
      simp [computableUniversalTaylorMonomial, CPoly.CMvMonomial.toFinsupp]
    · simp [computableUniversalTaylorMonomial, CPoly.CMvMonomial.toFinsupp,
        hi]

/-- The concrete universal jet denotes the literal Hasse jet after renaming its variables. -/
theorem rename_fromCMvPolynomial_computableUniversalTaylorJet (K j : ℕ) :
    MvPolynomial.rename (finToTaylorVariable K)
        (CPoly.fromCMvPolynomial (computableUniversalTaylorJet (F := F) K j)) =
      universalTaylorJet K j := by
  rw [computableUniversalTaylorJet, CPoly.CMvPolynomial.fromCMvPolynomial_sum]
  simp only [map_sum, CPoly.CMvPolynomial.fromCMvPolynomial_monomial,
    toFinsupp_computableUniversalTaylorMonomial, MvPolynomial.rename_monomial,
    Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rfl

/-- The concrete universal residual denotes the mathematical universal Taylor residual. -/
theorem rename_fromCMvPolynomial_computableUniversalTaylorResidual {r : ℕ}
    (K : ℕ) (center : F) (Q : CPoly.CMvPolynomial (r + 2) F) :
    MvPolynomial.rename (finToTaylorVariable K)
        (CPoly.fromCMvPolynomial (computableUniversalTaylorResidual K center Q)) =
      universalTaylorResidual K center (semanticEquation Q) := by
  rw [computableUniversalTaylorResidual, CPoly.CMvPolynomial.fromCMvPolynomial_bind₁]
  rw [MvPolynomial.comp_aeval_apply]
  unfold universalTaylorResidual semanticEquation
  rw [MvPolynomial.aeval_rename]
  have hsubstitution :
      (fun i => MvPolynomial.rename (finToTaylorVariable K)
        (CPoly.fromCMvPolynomial
          (Fin.cases
            (CPoly.CMvPolynomial.C center + CPoly.CMvPolynomial.X 0)
            (fun j => computableUniversalTaylorJet K j.val) i))) =
        (fun i => Option.elim i
          (MvPolynomial.C center + MvPolynomial.X none)
          (fun j => universalTaylorJet K j.val)) ∘ finToJetVariable r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change MvPolynomial.rename (finToTaylorVariable K)
          (CPoly.fromCMvPolynomial
            (CPoly.CMvPolynomial.C center + CPoly.CMvPolynomial.X 0)) =
        MvPolynomial.C center + MvPolynomial.X none
      rw [CPoly.CMvPolynomial.fromCMvPolynomial_add',
        CPoly.CMvPolynomial.fromCMvPolynomial_C,
        CPoly.CMvPolynomial.fromCMvPolynomial_X, map_add,
        MvPolynomial.rename_C, MvPolynomial.rename_X]
      rfl
    · exact rename_fromCMvPolynomial_computableUniversalTaylorJet K j.val
  rw [hsubstitution]

end ReedSolomon.HiddenDerivative.SquareSystems
