/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridAgreementCounting
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.OrdinaryTail
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Automatic first-order hybrid transfer

A nonzero first-order equation with bounded total jet degree `μ`, first-derivative degree
`M ≤ μ` and coefficient degree `h` admits a first-order hybrid descent. Its ordinary tail and its
regular stages together give one exceptional set of challenges, outside which every sufficiently
agreeing root has exact degree-one power agreement. The exceptional set is bounded by the
optimized exception charge, by its ceiling, and by the closed exception constant. Over an
arbitrary field the equation is mapped into an algebraic closure, and the result descends to exact
correlated agreement over the base field.

The automatic first-order recipe supplies such an equation for every received line. For a rate
`ρ` and an agreement fraction `a` above the first-order threshold, it fixes `M`, `μ` and `h`
before the field and the received words are chosen.

For `D = k - 1` put `θ = (n - D) / (A - D)` and `T = ∑_{r=1}^M r (2 (μ - M) + r)`. The closed
exception count is `E = E₀ + E₁ + E₂`, where

* `E₀ = (2μ - 1) h + θ (h + μ + 4 D μ h) + (n - D - 1) μ` handles the ordinary tail,
* `E₁ = (24 D² h + 8 D) θ² T` handles joint regular-stage families, and
* `E₂ = 4 D (n - D - 1) θ T` handles generic regular fibers.

## Main statements

* `ReedSolomon.exists_exceptional_firstOrder_hybrid`: the exceptional-set bound for a nonzero
  first-order equation over an algebraically closed extension.
* `ReedSolomon.exists_exceptional_firstOrder_hybrid_base`: the same bound for an equation over an
  arbitrary field, with exact correlated pairs over that field.
* `ReedSolomon.HiddenDerivative.FirstOrderSymbolicCertificate.exists_exceptional_hybrid`: the
  base-field bound for the equation of a symbolic certificate for a received line.
* `ReedSolomon.exists_automaticFirstOrder_hybridEquation` and
  `ReedSolomon.exists_automaticFirstOrder_hybridEquation_base`: the automatic recipe constructs
  the equation for every received line and discharges the hybrid transfer.
* `ReedSolomon.automatic_first_order_line_agreement`: at most `E` exceptional challenges for exact
  correlated agreement along a received line.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential MvPolynomial

namespace ReedSolomon

open HiddenDerivative

noncomputable section

universe u

/-- A nonzero first-order equation over an algebraically closed extension, with total jet degree
at most `mu`, `Y₁` degree at most `M ≤ mu` and coefficient degree at most `h`, has one set of
exceptional challenges bounded by the optimized exception charge, its ceiling, and the closed
exception constant. Outside it, every root of degree at most `D` that agrees with the
power-batched line in at least `A` places has exact degree-one power agreement. The
characteristic is zero or exceeds `max D M`. -/
theorem exists_exceptional_firstOrder_hybrid
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A h mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0) (hweight : jetTotalDegree Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M) (hheight : CoeffNatDegreeLE Q h)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h mu M ∧
      exceptional.card ≤
        firstOrderExceptionBound (agreementIncidenceRatio n D A) n D A h mu M ∧
      (exceptional.card : ℝ) ≤
        firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  have hcharEq : ringChar E = ringChar F := by
    let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
    exact ringChar.eq E (ringChar F)
  obtain ⟨descent⟩ := exists_firstOrderHybridDescent Q hQ hweight hdegree (by
    rw [hcharEq]
    exact hchar.imp_right ((hdegree.trans (Nat.le_max_right D M)).trans_lt ·))
  obtain ⟨exceptional, hraw, hceil, hclosed, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid_optimized_of_tail domain f g iota Q descent hD hDA hAn
      hMmu (hchar.imp_right ((Nat.le_max_left D M).trans_lt ·))
      (descent.hasOrdinaryTailTransfer domain f g iota hD hDA hAn)
  have hθ : 0 ≤ agreementIncidenceRatio n D A := by
    unfold agreementIncidenceRatio
    positivity
  have hQh : coeffNatDegree Q ≤ h := Finset.sup_le fun m _ ↦ hheight m
  have hmaxMin := maxMinFirstOrderExceptionCharge_mono_height (n := n) (D := D) (A := A)
    (μ := mu) (M := M) hθ hQh
  exact ⟨exceptional, hraw.trans hmaxMin, hceil.trans (Nat.ceil_mono hmaxMin),
    hclosed.trans (firstOrderExceptionConstant_mono_height hθ hQh), hgood⟩

/-- A nonzero first-order equation over an arbitrary field, with total jet degree at most `mu`,
`Y₁` degree at most `M ≤ mu` and coefficient degree at most `h`, has one set of exceptional
challenges bounded by the optimized exception charge, its ceiling, and the closed exception
constant. Outside it, every root of degree at most `D` that agrees with the received line in at
least `A` places has an exact correlated pair. The characteristic is zero or exceeds
`max D M`. -/
theorem exists_exceptional_firstOrder_hybrid_base
    {F : Type*} [Field F] [DecidableEq F] {n D A h mu M : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    (hweight : jetTotalDegree Q ≤ mu) (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hheight : CoeffNatDegreeLE Q h) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h mu M ∧
      exceptional.card ≤
        firstOrderExceptionBound (agreementIncidenceRatio n D A) n D A h mu M ∧
      (exceptional.card : ℝ) ≤
        firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h mu M ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  let iota : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hinj : Function.Injective (Polynomial.mapRingHom iota) :=
    Polynomial.map_injective iota iota.injective
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) Q
  have hQE : QE ≠ 0 := fun hzero ↦
    hQ (MvPolynomial.map_injective _ hinj (by simpa only [map_zero] using hzero))
  obtain ⟨extensionExceptional, hraw, hceil, hclosed, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid domain f g iota QE hQE
      ((jetTotalDegree_map_eq hinj Q).trans_le hweight)
      ((jetDegree_map_eq hinj Q 1).trans_le hdegree) (hheight.map_coefficients iota)
      hD hDA hAn hMmu hchar
  obtain ⟨exceptional, hcard, hbase⟩ := exists_exceptional_equation_correlatedAgreement_descend
    domain f g iota Q (D + 1) A extensionExceptional (by
      intro z hz P hP hagree hroot
      apply exactCorrelatedPair_of_powerAgreement_one domain ![f, g] iota z P
      apply hgood z hz P hP _ hroot
      rwa [powerBatchedWord_pair_eq])
  have hcardReal : (exceptional.card : ℝ) ≤ extensionExceptional.card := by
    exact_mod_cast hcard
  exact ⟨exceptional, hcardReal.trans hraw, hcard.trans hceil, hcardReal.trans hclosed, hbase⟩

/-- The equation of a first-order symbolic certificate for a received line is nonzero, has the
certified jet, derivative and challenge degrees, and vanishes after challenge specialization at
every polynomial of degree below `k` agreeing with the line in at least `A` places. -/
private theorem certificate_equation_facts
    {K : Type u} [Field K] [DecidableEq K] {n Dc A m M mu k h N : ℕ} {domain : Fin n ↪ K}
    {f g : Fin n → K} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} Dc A m M mu k h domain f g columns) :
    cert.Q ≠ 0 ∧ jetTotalDegree cert.Q ≤ mu ∧ jetDegree cert.Q (1 : Fin 2) ≤ M ∧
      CoeffNatDegreeLE cert.Q h ∧
      ∀ z : K, ∀ P : K[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        differentialSpecialization (challengeSpecialization cert.Q z) P = 0 := by
  refine ⟨fun hzero ↦ (cert.specialization_sound (RingHom.id K) 0).1 (by rw [hzero, map_zero]),
    (jetTotalDegree_le_iff _ _).2 cert.totalJetDegree_le, cert.toCurve.jetDegree_one_le,
    cert.challengeDegree_le, ?_⟩
  intro z P hP hagree
  have heval : Polynomial.eval₂RingHom (RingHom.id K) z = (Polynomial.aeval z).toRingHom := by
    ext <;> simp
  rw [challengeSpecialization, ← heval]
  exact (cert.specialization_sound (RingHom.id K) z).2 _ P hP hagree fun i hi ↦ by simpa using hi

/-- A first-order symbolic certificate for a received line over an arbitrary field, with
multiplicity `m`, derivative cap `M ≤ mu`, jet degree `mu` and challenge height `h`, gives one
set of exceptional challenges bounded by the optimized exception charge, its ceiling, and the
closed exception constant. Outside it, every polynomial of degree below `k = D + 1` agreeing with
the line in at least `A` places has an exact correlated pair. -/
theorem HiddenDerivative.FirstOrderSymbolicCertificate.exists_exceptional_hybrid
    {F : Type u} [Field F] [DecidableEq F] {n Dc D A m M mu k h N : ℕ} {domain : Fin n ↪ F}
    {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate.{u, u} Dc A m M mu k h domain f g columns)
    (hkD : k = D + 1)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h mu M ∧
      exceptional.card ≤
        firstOrderExceptionBound (agreementIncidenceRatio n D A) n D A h mu M ∧
      (exceptional.card : ℝ) ≤
        firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h mu M ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨hQ, hweight, hdegree, hheight, hroot⟩ := certificate_equation_facts cert
  subst hkD
  obtain ⟨exceptional, hraw, hceil, hclosed, hgood⟩ := exists_exceptional_firstOrder_hybrid_base
    domain f g cert.Q hQ hweight hdegree hheight hD hDA hAn hMmu hchar
  exact ⟨exceptional, hraw, hceil, hclosed, fun z hz P hP hagree ↦
    hgood z hz P (by exact_mod_cast hP) hagree (hroot z P hP hagree)⟩

/-- The degree bounds and root property of the automatic equation for a received line: it is
nonzero, has the automatic jet, derivative and challenge degrees, and vanishes after challenge
specialization at every polynomial of degree below `k` agreeing with the line in at least `A`
places. -/
private theorem exists_automaticFirstOrder_equation
    {K : Type u} [Field K] [DecidableEq K] {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (domain : Fin n ↪ K) (f g : Fin n → K) :
    ∃ Q : DifferentialPolynomial K[X] 1,
      Q ≠ 0 ∧ jetTotalDegree Q ≤ automaticJetDegree rho a ∧
      jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a ∧
      CoeffNatDegreeLE Q (automaticChallengeHeight rho a) ∧
      ∀ z : K, ∀ P : K[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 := by
  obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
    hrho hrhoOne ha haOne hn hD hk hkRate hA domain f g
  obtain ⟨hQ, hweight, hdegree, hheight, hroot⟩ := certificate_equation_facts cert
  exact ⟨cert.Q, hQ,
    hweight.trans_eq (automaticFiniteRateParameters_jetDegree hrho hrhoOne ha haOne),
    hdegree.trans_eq (automaticFiniteRateParameters_derivativeCap hrho hrhoOne ha haOne),
    hheight.mono (automaticFiniteRateParameters_challengeDegree hrho hrhoOne ha haOne).le, hroot⟩

/-- The automatic parameters give `1 ≤ D < A` and `M ≤ μ`. -/
private theorem automaticFirstOrder_degree_bounds {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (ha : firstOrderRateThreshold rho < a)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) :
    1 ≤ D ∧ D < A ∧ automaticDerivativeCap rho a ≤ automaticJetDegree rho a := by
  refine ⟨by omega, ?_, min_le_right _ _⟩
  have hrhoa : rho < a :=
    (rho_lt_automaticAgreement hrho hrhoOne ha).trans_le (automaticAgreement_le rho a)
  have hreal : (D : ℝ) < A :=
    calc
      (D : ℝ) ≤ rho * n := automatic_degree_le_rate_mul hD hkRate
      _ < a * n := mul_lt_mul_of_pos_right hrhoa (by exact_mod_cast hn)
      _ ≤ A := hA
  exact_mod_cast hreal

/-- For a rate `rho` and an agreement fraction `a` above the first-order threshold, the automatic
recipe constructs, for every received line, a nonzero equation over an algebraically closed
extension with the automatic jet, derivative and challenge degrees, whose challenge
specializations vanish at every polynomial of degree below `k` agreeing with the power-batched
line in at least `A` places. One set of exceptional challenges, bounded by the optimized exception
charge, its ceiling, and the closed exception constant, leaves every such polynomial with exact
degree-one power agreement. -/
theorem exists_automaticFirstOrder_hybridEquation
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (hchar : ringChar F = 0 ∨ max D (automaticDerivativeCap rho a) < ringChar F)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E) :
    ∃ Q : DifferentialPolynomial E[X] 1,
      Q ≠ 0 ∧ jetTotalDegree Q ≤ automaticJetDegree rho a ∧
      jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a ∧
      CoeffNatDegreeLE Q (automaticChallengeHeight rho a) ∧
      (∀ z : E, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0) ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℝ) ≤
          maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        exceptional.card ≤
          firstOrderExceptionBound (agreementIncidenceRatio n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        (exceptional.card : ℝ) ≤
          firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
          HasExactPowerAgreement domain ![f, g] iota k z P := by
  obtain ⟨hD₁, hDA, hMmu⟩ :=
    automaticFirstOrder_degree_bounds hrho hrhoOne ha hn hD hk hkRate hA
  obtain ⟨Q, hQ, hweight, hdegree, hheight, hroot⟩ := exists_automaticFirstOrder_equation
    hrho hrhoOne ha haOne hn hD hk hkRate hA (domain.trans ⟨iota, iota.injective⟩)
    (fun i ↦ iota (f i)) (fun i ↦ iota (g i))
  have hsound : ∀ z : E, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
      differentialSpecialization (challengeSpecialization Q z) P = 0 := by
    intro z P hP hagree
    rw [powerBatchedWord_pair_eq] at hagree
    exact hroot z P hP hagree
  obtain rfl : k = D + 1 := by omega
  obtain ⟨exceptional, hraw, hceil, hclosed, hgood⟩ := exists_exceptional_firstOrder_hybrid
    domain f g iota Q hQ hweight hdegree hheight hD₁ hDA hAn hMmu hchar
  exact ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional, hraw, hceil, hclosed,
    fun z hz P hP hagree ↦
      hgood z hz P (by exact_mod_cast hP) hagree (hsound z P hP hagree)⟩

/-- For a rate `rho` and an agreement fraction `a` above the first-order threshold, the automatic
recipe constructs, for every received line over an arbitrary field, a nonzero equation with the
automatic jet, derivative and challenge degrees, whose challenge specializations vanish at every
polynomial of degree below `k` agreeing with the line in at least `A` places. One set of
exceptional challenges, bounded by the optimized exception charge, its ceiling, and the closed
exception constant, leaves every such polynomial with an exact correlated pair. -/
theorem exists_automaticFirstOrder_hybridEquation_base
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] [DecidableEq F]
    (hchar : ringChar F = 0 ∨ max D (automaticDerivativeCap rho a) < ringChar F)
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ Q : DifferentialPolynomial F[X] 1,
      Q ≠ 0 ∧ jetTotalDegree Q ≤ automaticJetDegree rho a ∧
      jetDegree Q (1 : Fin 2) ≤ automaticDerivativeCap rho a ∧
      CoeffNatDegreeLE Q (automaticChallengeHeight rho a) ∧
      (∀ z : F, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        exceptional.card ≤
          firstOrderExceptionBound (agreementIncidenceRatio n D A) n D A
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        (exceptional.card : ℝ) ≤
          firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D
            (automaticChallengeHeight rho a) (automaticJetDegree rho a)
            (automaticDerivativeCap rho a) ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨hD₁, hDA, hMmu⟩ :=
    automaticFirstOrder_degree_bounds hrho hrhoOne ha hn hD hk hkRate hA
  obtain ⟨Q, hQ, hweight, hdegree, hheight, hroot⟩ := exists_automaticFirstOrder_equation
    hrho hrhoOne ha haOne hn hD hk hkRate hA domain f g
  obtain rfl : k = D + 1 := by omega
  obtain ⟨exceptional, hraw, hceil, hclosed, hgood⟩ := exists_exceptional_firstOrder_hybrid_base
    domain f g Q hQ hweight hdegree hheight hD₁ hDA hAn hMmu hchar
  exact ⟨Q, hQ, hweight, hdegree, hheight, hroot, exceptional, hraw, hceil, hclosed,
    fun z hz P hP hagree ↦
      hgood z hz P (by exact_mod_cast hP) hagree (hroot z P hP hagree)⟩

/-- **One exceptional set gives exact correlated agreement along a received line.**

Fix a physical rate upper bound `ρ` and an agreement fraction `a` above the first-order
threshold. The automatic recipe determines `M`, `μ`, and `h` from these two real numbers.
No interpolation certificate or surplus inequality is required from the caller.

For any received words `f` and `g`, there is a set of at most `E` exceptional challenges.
Outside this set, every polynomial `P` of degree `< k` with at least `A` agreements with
`f + z * g` has a representation `P = P₀ + z * P₁`, where both degrees are `< k` and

`Agr(f + z * g, P) = Agr(f, P₀) ∩ Agr(g, P₁)`.

The exceptional set is uniform over all candidate polynomials. The recovered pair may
depend on the challenge and candidate. The field need not be finite. In characteristic zero
the characteristic guard is automatic; in positive characteristic it requires `p > D` and
`p > M`, while the ordinary tail needs no `p > μ` hypothesis.
-/
theorem automatic_first_order_line_agreement
    /-

    Choose the physical rate and agreement fraction before the code data.
    -/
    (ρ a : ℝ)
    (hρ : 0 < ρ)
    (hρone : ρ < 1)
    (ha : firstOrderRateThreshold ρ < a)
    (haone : a < 1)
    /-

    Dimension k means degree strictly below k; A counts agreeing positions.
    -/
    (n k A : ℕ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hrate : (k : ℝ) ≤ ρ * n)
    (hagree : a * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points over an arbitrary field.
    -/
    {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin n ↪ F)
    -- Taylor recovery through degree D divides by 1,...,D; separant descent
    -- differentiates at most M times in Y₁. These require p > D and p > M
    -- in positive characteristic. The ordinary tail is characteristic-free,
    -- so no p > μ assumption is needed.
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap ρ a) < ringChar F)
    (f g : Fin n → F) :
    /-

    D = k - 1 is the largest allowed candidate degree.
    The hypotheses give D < A ≤ n, so the differences below are positive.
    -/
    let D := k - 1
    /-

    θ = (n - D) / (A - D) is the direct agreement-incidence ratio.
    It converts the degree of a fixed-word solution family into a candidate count.
    Here 1 ≤ θ ≤ 1 / (a - ρ); the ratio grows as agreement approaches the rate.
    -/
    let θ := agreementIncidenceRatio n D A
    /-

    The recipe uses a₀ = min(a, (1 + a₁(ρ))/2), β = 3(1-a₀)/(2(2-ρ)),
    and m = ceil(4/S), where S > 0 is the normalized interpolation surplus.
    Then mS ≥ 4 pays for the finite rounding loss 3m², leaving positive surplus.
    M = floor(βm) caps the exponent of the hidden derivative variable Y₁.
    The cap is normalized by min with μ; the recipe proves M ≤ μ.
    -/
    let M := automaticDerivativeCap ρ a
    /-

    μ = ceil(m a₀ / ρ) bounds total degree in the jet variables (Y₀,Y₁).
    This is distinct from the Y₁-degree cap M and the candidate degree D.
    -/
    let μ := automaticJetDegree ρ a
    /-

    h = max(1, floor(r(m,M) μ / (N₀ - r(m,M)))) bounds the degree
    in the challenge variable of the symbolic interpolant.
    N₀ is the normalized source count; r(m,M) is a certified upper bound on the
    local constraint rank.
    The finite-surplus proof gives N₀ - r(m,M) > 0; choosing h this way
    leaves enough challenge-coefficient slots for a nonzero polynomial kernel vector.
    -/
    let h := automaticChallengeHeight ρ a
    /-

    The regular-stage degree sum is
    T = sum_{r=1}^M r(2(μ-M)+r)
      = (μ-M)M(M+1) + M(M+1)(2M+1)/6.
    Retaining M at every separant stage gives this sum instead of a μ-only bound.
    -/
    let T := stageStaircase μ M
    /-

    The closed exception count is E = E₀ + E₁ + E₂, where
    E₀ = (2μ-1)h + θ(h+μ+4Dμh) + (n-D-1)μ is the ordinary-tail budget.
    Its first term covers exceptional content/resultant specializations;
    its second applies incidence to the factorwise rational images;
    its third allows accidental agreements on at most μ persistent graph lines.

    For the regular stages, the joint-family degree satisfies
    J₁ ≤ (12D²h+4D)T and the generic-fiber degree satisfies B₁ ≤ 2DT.
    Keeping L = D + ceil((A-D)/2) common agreements costs at most
    2θ²J₁ + 2(n-D-1)θB₁ exceptions. Thus the two remaining terms are
    E₁ = (24D²h+8D)θ²T and E₂ = 4D(n-D-1)θT.
    E counts challenges; only min(1,E/|F|) is a finite-field probability.
    -/
    let E₀ := ordinaryTailCharge θ n D h μ
    let E : ℝ := E₀ + (24 * D ^ 2 * h + 8 * D) * θ ^ 2 * T +
      4 * D * (n - D - 1 : ℕ) * θ * T
    /-

    Choose one exceptional set before the challenge or candidate polynomial.
    -/
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ E ∧
      /-

      Every qualifying candidate outside the fixed exceptional set admits exact recovery.
      -/
      ∀ z ∉ exceptional,
        ∀ P : F[X],
          P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          /-

          Exact recovery includes equality of the entire agreement set.
          -/
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  obtain ⟨-, -, -, -, -, -, exceptional, -, -, hclosed, hgood⟩ :=
    exists_automaticFirstOrder_hybridEquation_base hρ hρone ha haone hn rfl hk hrate hagree hAn
      hchar domain f g
  exact ⟨exceptional, hclosed, hgood⟩

end

end ReedSolomon
