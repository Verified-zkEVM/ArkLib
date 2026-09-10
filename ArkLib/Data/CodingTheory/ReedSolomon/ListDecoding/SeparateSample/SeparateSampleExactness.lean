/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderCertificate
/-!
# Exactness and initial-input work for one separate-sample execution

The premise is successful direct interpolation, so ambient search and order-zero direct attempts
share this interface. The execution theorem returns one output and primitive cost; semantic
exactness is attached to those exact records and output, without comparing independent runs.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleExactness

open Polynomial JetHornerMachine HiddenDerivative PreparedDecoderCertificate PolynomialDifferential
open PreparedDecoderMachine (Input Element Term)
open SeparateSampleDecoder

variable {F : Type*} [Field F] [DecidableEq F] {a : F}

/-- Actual direct success supplies the interpolation certificate and physical factor layout. -/
theorem attempt_certificate (D d m A : ℕ) (rows : List (F × F))
    (interp : NonzeroInterpolationMachine.Output F)
    (hr : (NonzeroInterpolationMachine.run D d m A rows).1 = some interp) :
    NonzeroInterpolationMachine.Certified (d := d) D m A rows interp ∧
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) interp.terms := by
  obtain ⟨result, c, he, _hc, hs⟩ := NonzeroInterpolationMachine.attempt_complete D m A rows
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  change some interp = result at he'
  subst result
  exact ⟨hs interp rfl, attempt_layout D d m A rows interp hr⟩

/-- Budgeted direct success supplies its interpolation certificate and physical factor layout. -/
theorem attemptWithBudget_certificate (D d m J A : ℕ) (rows : List (F × F))
    (interp : NonzeroInterpolationMachine.Output F)
    (hr : (NonzeroInterpolationMachine.runWithBudget D d m J A rows).1 = some interp) :
    NonzeroInterpolationMachine.CertifiedWithBudget (d := d) D m J A rows interp ∧
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) interp.terms := by
  obtain ⟨result, c, he, _hc, hs⟩ :=
    NonzeroInterpolationMachine.attemptWithBudget_complete D m J A rows
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  change some interp = result at he'
  subst result
  exact ⟨hs interp rfl, attemptWithBudget_layout D d m J A rows interp hr⟩

/-- One initial-budget execution retains a certificate from strict interpolation cutoff `J`. -/
theorem attemptWithBudget_execution (input : Input F a) (guards : List (Element F a))
    (ha : ¬IsSquare a) (interp : NonzeroInterpolationMachine.Output F) (m J Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.runWithBudget input.degree input.order m J
      input.agreement input.received).1 = some interp)
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (hq : 0 < input.alphabet.length) (hdepth : input.order ≤ input.degree)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) ≤ Δ) :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    let Q := MvPolynomial.map (algebraMap F (Element F a))
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp)
    NonzeroInterpolationMachine.CertifiedWithBudget (d := input.order)
      input.degree m J input.agreement input.received interp ∧
    ∃ steps c out, steps ≤ fuel input guards interp.terms Δ ∧
      Trace input guards ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input guards ha (fuel input guards interp.terms Δ) (.start interp.terms) =
        (.done (some out), c) ∧ c ≤ workBound input guards interp.terms Δ ∧
      ∃ stages records,
        SeparantChainRefinement.OrderedChain (initialRootInput input interp.terms).terms Q stages ∧
        StageRootsMachine.Specification (initialRootInput input interp.terms) input.degree
          input.residualLength input.samples stages [] records ∧
        out = CanonicalOutputMachine.result input.order guards (input.degree + 1)
          input.dimension input.agreement input.received records := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    exact ha ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let Q := NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
    input.degree m J input.agreement interp
  obtain ⟨hc, hl⟩ := attemptWithBudget_certificate input.degree input.order m J input.agreement
    input.received interp hr
  have hQne : Q ≠ 0 := by
    intro hz
    have he := hc.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
      input.degree m J input.agreement interp = 0 from hz, map_zero] at he
    exact hc.2.2.2.2.2.2.2.1 he
  refine ⟨hc, execution_input_budget input guards ha interp.terms Δ points hsamples hq hdepth
    (MvPolynomial.map (algebraMap F (Element F a)) Q)
    (MvPolynomial.QuadraticInputMachine.embedded_layout _ _ hl)
    (embedded_representationWithBudget input.received interp hc a) ?_ ?_ ?_ ?_⟩
  · intro hz
    exact hQne (MvPolynomial.map_injective _ (algebraMap F (Element F a)).injective
      (by simpa using hz))
  · exact ((isBelowCharacteristic_map_iff Q input.degree).mpr hchar).2
  · simpa only [jetTotalDegree_map_eq _ (algebraMap F (Element F a)).injective Q] using hdegree
  · simpa only [differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight

/-- One initial-budget execution retains its actual interpolation and root certificates. -/
theorem attempt_execution (input : Input F a) (guards : List (Element F a))
    (ha : ¬IsSquare a) (interp : NonzeroInterpolationMachine.Output F) (m Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.run input.degree input.order m input.agreement
      input.received).1 = some interp)
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (hq : 0 < input.alphabet.length) (hdepth : input.order ≤ input.degree)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree (NonzeroInterpolationMachine.sourceOutput (d := input.order)
      input.degree m input.agreement interp) ≤ Δ) :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    let Q := MvPolynomial.map (algebraMap F (Element F a))
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp)
    NonzeroInterpolationMachine.Certified (d := input.order) input.degree m input.agreement
      input.received interp ∧
    ∃ steps c out, steps ≤ fuel input guards interp.terms Δ ∧
      Trace input guards ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input guards ha (fuel input guards interp.terms Δ) (.start interp.terms) =
        (.done (some out), c) ∧ c ≤ workBound input guards interp.terms Δ ∧
      ∃ stages records,
        SeparantChainRefinement.OrderedChain (initialRootInput input interp.terms).terms Q stages ∧
        StageRootsMachine.Specification (initialRootInput input interp.terms) input.degree
          input.residualLength input.samples stages [] records ∧
        out = CanonicalOutputMachine.result input.order guards (input.degree + 1)
          input.dimension input.agreement input.received records := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    exact ha ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let Q := NonzeroInterpolationMachine.sourceOutput (d := input.order)
    input.degree m input.agreement interp
  obtain ⟨hc, hl⟩ := attempt_certificate input.degree input.order m input.agreement
    input.received interp hr
  have hQne : Q ≠ 0 := by
    intro hz
    have he := hc.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutput (d := input.order)
      input.degree m input.agreement interp = 0 from hz, map_zero] at he
    exact hc.2.2.2.2.2.2.2.1 he
  refine ⟨hc, execution_input_budget input guards ha interp.terms Δ points hsamples hq hdepth
    (MvPolynomial.map (algebraMap F (Element F a)) Q)
    (MvPolynomial.QuadraticInputMachine.embedded_layout _ _ hl)
    (embedded_representation input.received interp hc a) ?_ ?_ ?_ ?_⟩
  · intro hz
    exact hQne (MvPolynomial.map_injective _ (algebraMap F (Element F a)).injective
      (by simpa using hz))
  · exact ((isBelowCharacteristic_map_iff Q input.degree).mpr hchar).2
  · simpa only [jetTotalDegree_map_eq _ (algebraMap F (Element F a)).injective Q] using hdegree
  · simpa only [differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight

/-- Fixed output width turns exact polynomial membership into exact physical-vector membership. -/
theorem vector_membership (out : List (List F)) (k A : ℕ) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hw : ∀ cs ∈ out, cs.length = k)
    (hm : ∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) (cs : List F) :
    cs ∈ out ↔ cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  constructor
  · intro hc
    exact ⟨hw cs hc, (hm _).mp (List.mem_map.mpr ⟨cs, hc, rfl⟩)⟩
  · rintro ⟨hlen, hd, ha⟩
    obtain ⟨bs, hb, hp⟩ := List.mem_map.mp ((hm _).mpr ⟨hd, ha⟩)
    have he := CanonicalRootSelection.coefficients_unique bs cs ((hw bs hb).trans hlen.symm) hp
    simpa only [he] using hb

/-- Full-alphabet exactness and work concern the same initial-budget execution and cost. -/
theorem full_attempt_exact (input : Input F a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output F) (m Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.run input.degree input.order m input.agreement
      input.received).1 = some interp)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hrows : input.received = List.ofFn (fun i ↦ (domain i, received i)))
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup)
    (hdepth : input.order ≤ input.degree) (hk : input.dimension ≤ input.degree + 1)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree (NonzeroInterpolationMachine.sourceOutput (d := input.order)
      input.degree m input.agreement interp) ≤ Δ) :
    ∃ steps c out, steps ≤ fuel input input.samples interp.terms Δ ∧
      Trace input input.samples ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input input.samples ha (fuel input input.samples interp.terms Δ)
        (.start interp.terms) = (.done (some out), c) ∧
      c ≤ workBound input input.samples interp.terms Δ ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔ f.degree < input.dimension ∧
        input.agreement ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List F, cs ∈ out ↔ cs.length = input.dimension ∧
        (coefficientPolynomial cs).degree < input.dimension ∧
        input.agreement ≤
          Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    exact ha ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let Q := NonzeroInterpolationMachine.sourceOutput (d := input.order)
    input.degree m input.agreement interp
  let EQ := MvPolynomial.map (algebraMap F (Element F a)) Q
  let ri := initialRootInput input interp.terms
  obtain ⟨hc, steps, c, out, hsteps, ht, hrun, hcost, stages, records, hchain, hspec, hout⟩ :=
    attempt_execution input input.samples ha interp m Δ hr points hsamples
      (List.length_pos_of_mem (hall 0)) hdepth hchar hweight hdegree
  have hrep := embedded_representation input.received interp hc a
  have hne : EQ ≠ 0 := by
    have h := MvPolynomial.QuadraticInputMachine.embedded_nonzero (a := a) interp.terms
      hc.2.2.2.2.2.2.2.1
    intro hz
    apply h
    rw [hrep, show MvPolynomial.map (algebraMap F (Element F a)) Q = 0 from hz, map_zero]
  have hcharE := (isBelowCharacteristic_map_iff Q input.degree (E := Element F a)).mpr hchar
  have hweightE : differentialWeightedDegree input.degree EQ < input.residualLength := by
    simpa only [EQ, differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight
  obtain ⟨hdup, hmem⟩ := CanonicalOutputProof.stage_result_correct ri points input.samples
    hsamples hall hn hdepth hrep hchain hne hcharE hweightE hspec hk domain received
      (A := input.agreement)
  rw [hrows] at hout hc
  simp only [CanonicalOutputProof.basePolynomials, ← hout] at hdup hmem
  have hexact : ∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < input.dimension ∧
        input.agreement ≤ Code.agree (evalOnPoints domain f) received := by
    intro f
    rw [hmem]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · rintro ⟨hd, hagree⟩
      exact ⟨hd, hagree, certified_embedded_root _ domain received interp hc hk f hd hagree⟩
  have hw : ∀ cs ∈ out, cs.length = input.dimension := by
    intro cs hcs
    have hwidth : ∀ r ∈ records, r.coefficients.length = input.degree + 1 := fun r hr ↦
      (CanonicalRootSelection.current_zero ri points input.samples hsamples
        (List.length_pos_of_mem (hall 0)) hdepth hchain hcharE.2 hweightE hspec r hr).1
    rw [hout] at hcs
    exact (CanonicalOutputMachine.result_sound input.order (input.degree + 1) input.dimension
      input.agreement input.samples records hwidth hk domain received cs hcs).1
  exact ⟨steps, c, out, hsteps, ht, hrun, hcost, hdup, hdup.of_map _, hexact,
    vector_membership out input.dimension input.agreement domain received hw hexact⟩

/-- Full-alphabet exactness for the equation enumerated at strict jet cutoff `J`. -/
theorem full_attemptWithBudget_exact (input : Input F a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output F) (m J Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.runWithBudget input.degree input.order m J
      input.agreement input.received).1 = some interp)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hrows : input.received = List.ofFn (fun i ↦ (domain i, received i)))
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup)
    (hdepth : input.order ≤ input.degree) (hk : input.dimension ≤ input.degree + 1)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) ≤ Δ) :
    ∃ steps c out, steps ≤ fuel input input.samples interp.terms Δ ∧
      Trace input input.samples ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input input.samples ha (fuel input input.samples interp.terms Δ)
        (.start interp.terms) = (.done (some out), c) ∧
      c ≤ workBound input input.samples interp.terms Δ ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔ f.degree < input.dimension ∧
        input.agreement ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List F, cs ∈ out ↔ cs.length = input.dimension ∧
        (coefficientPolynomial cs).degree < input.dimension ∧
        input.agreement ≤
          Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    exact ha ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let Q := NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
    input.degree m J input.agreement interp
  let EQ := MvPolynomial.map (algebraMap F (Element F a)) Q
  let ri := initialRootInput input interp.terms
  obtain ⟨hc, steps, c, out, hsteps, ht, hrun, hcost, stages, records, hchain, hspec, hout⟩ :=
    attemptWithBudget_execution input input.samples ha interp m J Δ hr points hsamples
      (List.length_pos_of_mem (hall 0)) hdepth hchar hweight hdegree
  have hrep := embedded_representationWithBudget input.received interp hc a
  have hne : EQ ≠ 0 := by
    have h := MvPolynomial.QuadraticInputMachine.embedded_nonzero (a := a) interp.terms
      hc.2.2.2.2.2.2.2.1
    intro hz
    apply h
    rw [hrep, show MvPolynomial.map (algebraMap F (Element F a)) Q = 0 from hz, map_zero]
  have hcharE := (isBelowCharacteristic_map_iff Q input.degree (E := Element F a)).mpr hchar
  have hweightE : differentialWeightedDegree input.degree EQ < input.residualLength := by
    simpa only [EQ, differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight
  obtain ⟨hdup, hmem⟩ := CanonicalOutputProof.stage_result_correct ri points input.samples
    hsamples hall hn hdepth hrep hchain hne hcharE hweightE hspec hk domain received
      (A := input.agreement)
  rw [hrows] at hout hc
  simp only [CanonicalOutputProof.basePolynomials, ← hout] at hdup hmem
  have hexact : ∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < input.dimension ∧
        input.agreement ≤ Code.agree (evalOnPoints domain f) received := by
    intro f
    rw [hmem]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · rintro ⟨hd, hagree⟩
      exact ⟨hd, hagree,
        certified_embedded_rootWithBudget _ domain received interp hc hk f hd hagree⟩
  have hw : ∀ cs ∈ out, cs.length = input.dimension := by
    intro cs hcs
    have hwidth : ∀ r ∈ records, r.coefficients.length = input.degree + 1 := fun r hr ↦
      (CanonicalRootSelection.current_zero ri points input.samples hsamples
        (List.length_pos_of_mem (hall 0)) hdepth hchain hcharE.2 hweightE hspec r hr).1
    rw [hout] at hcs
    exact (CanonicalOutputMachine.result_sound input.order (input.degree + 1) input.dimension
      input.agreement input.samples records hwidth hk domain received cs hcs).1
  exact ⟨steps, c, out, hsteps, ht, hrun, hcost, hdup, hdup.of_map _, hexact,
    vector_membership out input.dimension input.agreement domain received hw hexact⟩

-- Direct D=d=0 interpolation succeeds even though the ambient-search interval is empty.
-- Its actual returned vector and terms satisfy the same certificate/layout interface.
example : let interp : NonzeroInterpolationMachine.Output (ZMod 3) :=
    ⟨1, [0, 1], [(1, [(0, 0), (1, 1)])]⟩
    NonzeroInterpolationMachine.Certified (d := 0) 0 1 1 [(0, 0)] interp ∧
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range 2) interp.terms := by
  exact attempt_certificate 0 0 1 1 [(0, 0)] _ (by decide +kernel)

end ReedSolomon.ListDecoding.SeparateSampleExactness
