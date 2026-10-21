/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate

/-!
# First-order interpolation profiles

A line profile records the finite counts and bounds for one first-order interpolation instance.
Its verification predicates check that those recorded counts agree with the support and that the
shifted coefficient slots exceed the row bound. Verified profiles construct symbolic line
certificates and polynomial-curve certificates through the first-order certificate API.

## Main statements

* `LineProfile.Verification.support_card_eq` and
  `LineProfile.Verification.columnY₀Weight_eq` check the recorded support counts.
* `LineProfile.Verification.exists_symbolicCertificate` constructs a symbolic certificate.
* `LineProfile.CurveVerification.exists_certificate` constructs a curve certificate.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative.CurveProfile

open ReedSolomon.HiddenDerivative

noncomputable section

universe u v

/-- The exact finite counts and parameters for one first-order interpolation instance. -/
structure LineProfile where
  /-- The block length. -/
  n : ℕ
  /-- The polynomial degree bound. -/
  k : ℕ
  /-- The agreement threshold. -/
  agreement : ℕ
  /-- The interpolation multiplicity. -/
  multiplicity : ℕ
  /-- The cap on the first derivative exponent. -/
  firstDerivativeCap : ℕ
  /-- The cap on total jet degree. -/
  totalJetCap : ℕ
  /-- The degree bound for the received polynomial curve. -/
  batchingDegree : ℕ
  /-- The recorded size of the first-order support. -/
  supportDimension : ℕ
  /-- The recorded local rank contribution. -/
  localRank : ℕ
  /-- The recorded sum of the support's `Y₀` exponents. -/
  columnY₀Weight : ℕ
  /-- The coefficient height used by the interpolation certificate. -/
  height : ℕ
  /-- The recorded number of scalar coefficient slots. -/
  heightSlots : ℕ
  deriving DecidableEq, Repr

namespace LineProfile

/-- Candidate polynomial degree, determined by the degree bound `k`. -/
def candidateDegree (p : LineProfile) : ℕ := p.k - 1

/-- Support dimension computed from the first-order exponent set. -/
def computedDimension (p : LineProfile) : ℕ :=
  firstOrderDimensionCount p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap

/-- The certified local rank contribution at one received position. -/
def computedLocalRank (p : LineProfile) : ℕ :=
  certifiedEnlargedRankBound 1 p.multiplicity p.firstDerivativeCap 0

/-- Number of scalar coefficient slots at the recorded height. -/
def computedHeightSlots (p : LineProfile) : ℕ :=
  firstOrderHeightSlotCount p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
    p.totalJetCap p.height

/-- Upper bound on shifted graded-row slots at batching degree `ℓ`. -/
def shiftedRowSlots (p : LineProfile) (ℓ : ℕ) : ℕ :=
  firstOrderCurveShiftedRowSlotBound p.candidateDegree p.agreement p.multiplicity
    p.firstDerivativeCap p.totalJetCap p.n ℓ p.height

/-- Number of shifted source slots at batching degree `ℓ`. -/
def shiftedHeightSlots (p : LineProfile) (ℓ : ℕ) : ℕ :=
  firstOrderCurveShiftedHeightSlotCount p.candidateDegree p.agreement p.multiplicity
    p.firstDerivativeCap p.totalJetCap ℓ p.height

/-- Count equalities and strict surplus needed for a symbolic line certificate. -/
structure Verification (p : LineProfile) : Prop where
  /-- The candidate polynomial degree is positive. -/
  candidateDegree_pos : 0 < p.candidateDegree
  /-- The interpolation budget is positive. -/
  budget_pos : 0 < p.multiplicity * p.agreement
  /-- The total jet cap is covered by the coefficient height. -/
  cap_le_height : p.totalJetCap ≤ p.height
  /-- The recorded dimension equals the first-order dimension count. -/
  dimension_eq : p.computedDimension = p.supportDimension
  /-- The recorded local rank equals the certified local rank. -/
  localRank_eq : p.computedLocalRank = p.localRank
  /-- The recorded height slots equal the computed height slots. -/
  heightSlots_eq : p.computedHeightSlots = p.heightSlots
  /-- The source slots and `Y₀` weight fill the support-height rectangle. -/
  columnWeight_eq : p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)
  /-- Shifted source slots strictly exceed the row slots at degree one. -/
  heightSurplus : p.shiftedRowSlots 1 < p.shiftedHeightSlots 1

/-- The recorded dimension is the cardinality of the constrained support. -/
theorem Verification.support_card_eq {p : LineProfile} (hp : p.Verification) :
    (firstOrderExponents p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
      p.totalJetCap).card = p.supportDimension := by
  rw [card_firstOrderExponents hp.candidateDegree_pos]
  simpa [computedDimension] using hp.dimension_eq

/-- The recorded column weight equals the sum of the `Y₀` exponents in the support. -/
theorem Verification.columnY₀Weight_eq {p : LineProfile} (hp : p.Verification) :
    p.columnY₀Weight = firstOrderY₀Weight p.candidateDegree p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap := by
  have hrectangle := firstOrderColumnSlotCount_add_y₀Weight
    (D := p.candidateDegree) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap) (h := p.height) hp.cap_le_height
  have hslots : firstOrderHeightSlotCount p.candidateDegree p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap p.height = p.heightSlots := by
    simpa [computedHeightSlots] using hp.heightSlots_eq
  rw [firstOrderColumnSlotCount_eq_heightSlotCount hp.candidateDegree_pos,
    hslots, hp.support_card_eq] at hrectangle
  exact Nat.add_left_cancel (hp.columnWeight_eq.trans hrectangle.symm)

/-- Enumeration of every exponent in the first-order support. -/
abbrev columns (p : LineProfile) :=
  firstOrderColumns (D := p.candidateDegree) (A := p.agreement) (m := p.multiplicity)
    (M := p.firstDerivativeCap) (μ := p.totalJetCap)

/-- The symbolic first-order certificate associated with a line profile. -/
abbrev SymbolicCertificate {F : Type u} [Field F] (p : LineProfile)
    (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :=
  FirstOrderSymbolicCertificate.{u, v} p.candidateDegree p.agreement p.multiplicity
    p.firstDerivativeCap p.totalJetCap p.k p.height centers f g p.columns

/-- A verified line profile constructs a primitive, specialization-sound symbolic certificate. -/
theorem Verification.exists_symbolicCertificate {F : Type u} [Field F] {p : LineProfile}
    (hp : p.Verification) (centers : Fin p.n ↪ F) (f g : Fin p.n → F) :
    Nonempty (p.SymbolicCertificate.{u, v} centers f g) := by
  have hkD : p.k ≤ p.candidateDegree + 1 := by
    change p.k ≤ p.k - 1 + 1
    omega
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    hp.candidateDegree_pos hp.budget_pos hkD centers f g hp.heightSurplus

/-- Conditions for a curve certificate, including checks that recorded counts match the support.
-/
def CurveVerification (p : LineProfile) : Prop :=
  0 < p.candidateDegree ∧ 0 < p.multiplicity * p.agreement ∧
    p.shiftedRowSlots p.batchingDegree < p.shiftedHeightSlots p.batchingDegree ∧
    p.computedDimension = p.supportDimension ∧ p.computedLocalRank = p.localRank ∧
    p.totalJetCap ≤ p.height ∧ p.computedHeightSlots = p.heightSlots ∧
    p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)

/-- Curve verification is decidable from the natural-number profile data. -/
instance (p : LineProfile) : Decidable p.CurveVerification := by
  unfold CurveVerification
  infer_instance

/-- A curve-verified line profile constructs its polynomial-curve interpolation certificate. -/
theorem CurveVerification.exists_certificate {F : Type*} [Field F] {p : LineProfile}
    (hp : p.CurveVerification) (domain : Fin p.n ↪ F) (w : Fin p.n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ p.batchingDegree) :
    Nonempty (FirstOrderCurveCertificate p.candidateDegree p.agreement p.multiplicity
      p.firstDerivativeCap p.totalJetCap p.k p.height domain w p.columns) := by
  have hkD : p.k ≤ p.candidateDegree + 1 := by
    change p.k ≤ p.k - 1 + 1
    omega
  exact exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    p.batchingDegree hp.1 hp.2.1 hkD domain w hw hp.2.2.1

end LineProfile

end

end ReedSolomon.HiddenDerivative.CurveProfile
