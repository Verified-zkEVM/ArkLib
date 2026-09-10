/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate
/-!
# Shared finite first-order certificate profiles

Concrete Reed--Solomon applications use the same finite support and local interpolation engine.
A `LineProfile` records one row of exact arithmetic. `Verification` checks the shifted line
surplus at degree one, while `CurveVerification` checks the same graded engine at the received
polynomial curve's batching degree.

The structures only certify interpolation.  Exceptional-set and security conclusions require
the separate geometric and probability theorems used by each application.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.CurveProfile

open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

universe u v

/-- One exact finite first-order interpolation row. -/
structure LineProfile where
  n : ℕ
  k : ℕ
  agreement : ℕ
  multiplicity : ℕ
  firstDerivativeCap : ℕ
  totalJetCap : ℕ
  batchingDegree : ℕ
  supportDimension : ℕ
  localRank : ℕ
  columnY₀Weight : ℕ
  height : ℕ
  heightSlots : ℕ
  deriving DecidableEq, Repr

namespace LineProfile

/-- Candidate-degree weight used by the finite first-order support. -/
def D (p : LineProfile) : ℕ := p.k - 1

/-- Support dimension recomputed from the actual finite monomial set. -/
def computedDimension (p : LineProfile) : ℕ :=
  firstOrderDimensionCount p.D p.agreement p.multiplicity p.firstDerivativeCap p.totalJetCap

/-- Certified rank contribution of one received position. -/
def computedLocalRank (p : LineProfile) : ℕ :=
  certifiedEnlargedRankBound 1 p.multiplicity p.firstDerivativeCap 0

/-- Scalar coefficient slots at the recorded height. -/
def computedHeightSlots (p : LineProfile) : ℕ :=
  firstOrderHeightSlotCount p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.height

/-- Executable upper bound on the shifted graded rows at batching degree `ℓ`. -/
def shiftedRowSlots (p : LineProfile) (ℓ : ℕ) : ℕ :=
  firstOrderCurveShiftedRowSlotBound p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.n ℓ p.height

/-- Executable shifted source slots at batching degree `ℓ`. -/
def shiftedHeightSlots (p : LineProfile) (ℓ : ℕ) : ℕ :=
  firstOrderCurveShiftedHeightSlotCount p.D p.agreement p.multiplicity
    p.firstDerivativeCap p.totalJetCap ℓ p.height

/-- Exact facts needed by the scalar finite symbolic constructor. -/
structure Verification (p : LineProfile) : Prop where
  D_pos : 0 < p.D
  budget_pos : 0 < p.multiplicity * p.agreement
  degree_le : p.k ≤ p.D + 1
  cap_le_height : p.totalJetCap ≤ p.height
  dimension_eq : p.computedDimension = p.supportDimension
  localRank_eq : p.computedLocalRank = p.localRank
  heightSlots_eq : p.computedHeightSlots = p.heightSlots
  columnWeight_eq : p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)
  heightSurplus : p.shiftedRowSlots 1 < p.shiftedHeightSlots 1

/-- The recorded dimension is the cardinality of the constrained support. -/
theorem Verification.support_card_eq {p : LineProfile} (hp : p.Verification) :
    (firstOrderExponents p.D p.agreement p.multiplicity p.firstDerivativeCap
      p.totalJetCap).card = p.supportDimension := by
  rw [card_firstOrderExponents_eq_dimensionCount hp.D_pos]
  simpa [computedDimension] using hp.dimension_eq

/-- The recorded column weight equals the sum of all `Y₀` exponents. -/
theorem Verification.columnY₀Weight_eq {p : LineProfile} (hp : p.Verification) :
    p.columnY₀Weight = firstOrderY₀Weight p.D p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap := by
  have hrectangle := firstOrderColumnSlotCount_add_y₀Weight
    (D := p.D) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap) (h := p.height) hp.cap_le_height
  have hslots : firstOrderHeightSlotCount p.D p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap p.height = p.heightSlots := by
    simpa [computedHeightSlots] using hp.heightSlots_eq
  rw [firstOrderColumnSlotCount_eq_heightSlotCount hp.D_pos,
    hslots, hp.support_card_eq] at hrectangle
  exact Nat.add_left_cancel (hp.columnWeight_eq.trans hrectangle.symm)

/-- Canonical enumeration of the complete finite support. -/
abbrev columns (p : LineProfile) :=
  firstOrderColumns (D := p.D) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap)

/-- Symbolic certificate belonging to a profile. -/
abbrev SymbolicCertificate {F : Type u} [Field F] (p : LineProfile)
    (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :=
  FirstOrderSymbolicCertificate.{u, v} p.D p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.k p.height centers f g p.columns

/-- A verified row constructs a primitive, specialization-sound scalar certificate. -/
theorem Verification.exists_symbolicCertificate {F : Type u} [Field F] {p : LineProfile}
    (hp : p.Verification) (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :
    Nonempty (p.SymbolicCertificate.{u, v} centers f g) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    hp.D_pos hp.budget_pos hp.degree_le centers f g hp.heightSurplus

/-- Exact facts required by the polynomial-curve interpolation constructor.

The first four conjuncts are the constructor's hypotheses. The remaining conjuncts re-derive the
recorded fields of the row from the support itself, so that no number in a curve
table can silently drift away from the object it describes. Only `D > 0` is needed: the direct
weighted-degree argument includes degree-one candidate polynomials. -/
def CurveVerification (p : LineProfile) : Prop :=
  0 < p.D ∧ 0 < p.multiplicity * p.agreement ∧ p.k ≤ p.D + 1 ∧
    p.shiftedRowSlots p.batchingDegree < p.shiftedHeightSlots p.batchingDegree ∧
    p.computedDimension = p.supportDimension ∧ p.computedLocalRank = p.localRank ∧
    p.totalJetCap ≤ p.height ∧ p.computedHeightSlots = p.heightSlots ∧
    p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)

instance (p : LineProfile) : Decidable p.CurveVerification := by
  unfold CurveVerification
  infer_instance

/-- A curve-verified row constructs its full polynomial-curve interpolation certificate. -/
theorem CurveVerification.exists_certificate {F : Type*} [Field F] {p : LineProfile}
    (hp : p.CurveVerification) (domain : Fin p.n ↪ F) (w : Fin p.n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ p.batchingDegree) :
    Nonempty (FirstOrderCurveCertificate p.D p.agreement p.multiplicity p.firstDerivativeCap
      p.totalJetCap p.k p.height domain w p.columns) := by
  exact exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    p.batchingDegree hp.1 hp.2.1 hp.2.2.1 domain w hw hp.2.2.2.1

end LineProfile

end

end ReedSolomon.CurveProfile
