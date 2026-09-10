/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleExactness
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.RestrictedCollectorProof
public import ArkLib.Data.QuadraticAlgebra.BaseEmbeddingSemantics
/-!
# Restricted-alphabet exactness for the same bounded decoder run

The actual base-embedding output is shared by center enumeration and canonical guards. Root
recovery uses the independent extension sample list. Exactness and primitive work refer to the
one execution returned by the initial-input theorem. The embedding cost is retained separately;
this theorem does not claim that its instructions are part of the separate-sample driver.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleRestricted

open Polynomial JetHornerMachine HiddenDerivative SeparateSampleExactness PolynomialDifferential
open PreparedDecoderMachine (Input Element)
open SeparateSampleDecoder

variable {F : Type*} [Field F] [DecidableEq F] {a : F}

omit [DecidableEq F] in
/-- An actual completed embedding run determines its exact alphabet and observed charge. -/
theorem embedding_output (base : List F) (out : List (Element F a))
    (c : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hr : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) = (.done out, c)) :
    out = base.map (algebraMap F (Element F a)) ∧ c.total = 16 * base.length + 8 := by
  obtain ⟨c', he, hc⟩ := QuadraticAlgebra.BaseEmbeddingMachine.evaluation_runFuel (a := a) base
  have h := hr.symm.trans he
  cases h
  exact ⟨QuadraticAlgebra.BaseEmbeddingMachine.embedded_eq_map base, hc⟩

variable [Finite F]

/-- Direct interpolation, actual base embedding, exact output and initial work share fixed runs. -/
theorem restricted_attempt_exact (input : Input F a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output F) (m Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.run input.degree input.order m input.agreement
      input.received).1 = some interp)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hrows : input.received = List.ofFn (fun i ↦ (domain i, received i)))
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hdepth : input.order ≤ input.degree) (hk : input.dimension ≤ input.degree + 1)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutput (d := input.order)
        input.degree m input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree (NonzeroInterpolationMachine.sourceOutput (d := input.order)
      input.degree m input.agreement interp) ≤ Δ)
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    embeddingCost.total = 16 * base.length + 8 ∧
    ∃ steps c out, steps ≤ fuel input input.alphabet interp.terms Δ ∧
      Trace input input.alphabet ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input input.alphabet ha (fuel input input.alphabet interp.terms Δ)
        (.start interp.terms) = (.done (some out), c) ∧
      c ≤ workBound input input.alphabet interp.terms Δ ∧
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
  obtain ⟨halphabet, hembedCost⟩ := embedding_output base input.alphabet embeddingCost hembed
  have hq : 0 < input.alphabet.length := by
    rw [halphabet, List.length_map]
    exact List.length_pos_of_mem (hall 0)
  let Q := NonzeroInterpolationMachine.sourceOutput (d := input.order)
    input.degree m input.agreement interp
  let ri := initialRootInput input interp.terms
  obtain ⟨hc, steps, c, out, hsteps, ht, hrun, hcost, stages, records, hchain, hspec, hout⟩ :=
    attempt_execution input input.alphabet ha interp m Δ hr points hsamples hq hdepth
      hchar hweight hdegree
  rw [hrows] at hc hout
  obtain ⟨hdup, hmem⟩ := RestrictedCollectorProof.result_exact base hall hn ri halphabet points
    input.samples hsamples hdepth interp domain received hc rfl hchain hchar hweight hspec
    hk hlarge
  dsimp only [ri, initialRootInput, PreparedDecoderMachine.rootInput] at hdup hmem
  simp only [CanonicalOutputProof.basePolynomials, ← hout] at hdup hmem
  have hcharE := (isBelowCharacteristic_map_iff Q input.degree (E := Element F a)).mpr hchar
  have hweightE : differentialWeightedDegree input.degree
      (MvPolynomial.map (algebraMap F (Element F a)) Q) < input.residualLength := by
    simpa only [differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight
  have hw : ∀ cs ∈ out, cs.length = input.dimension := by
    intro cs hcs
    have hwidth : ∀ r ∈ records, r.coefficients.length = input.degree + 1 := fun r hr ↦
      (CanonicalRootSelection.current_zero ri points input.samples hsamples hq hdepth hchain
        hcharE.2 hweightE hspec r hr).1
    rw [hout] at hcs
    exact (CanonicalOutputMachine.result_sound input.order (input.degree + 1) input.dimension
      input.agreement input.alphabet records hwidth hk domain received cs hcs).1
  exact ⟨hembedCost, steps, c, out, hsteps, ht, hrun, hcost, hdup, hdup.of_map _, hmem,
    vector_membership out input.dimension input.agreement domain received hw hmem⟩

/-- Restricted-alphabet exactness for interpolation run at strict jet cutoff `J`. -/
theorem restricted_attemptWithBudget_exact (input : Input F a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output F) (m J Δ : ℕ)
    (hr : (NonzeroInterpolationMachine.runWithBudget input.degree input.order m J
      input.agreement input.received).1 = some interp)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hrows : input.received = List.ofFn (fun i ↦ (domain i, received i)))
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hdepth : input.order ≤ input.degree) (hk : input.dimension ≤ input.degree + 1)
    (hchar : IsBelowCharacteristic input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp))
    (hweight : differentialWeightedDegree input.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) < input.residualLength)
    (hdegree : jetTotalDegree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
        input.degree m J input.agreement interp) ≤ Δ)
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    embeddingCost.total = 16 * base.length + 8 ∧
    ∃ steps c out, steps ≤ fuel input input.alphabet interp.terms Δ ∧
      Trace input input.alphabet ha steps (.start interp.terms) c (.done (some out)) ∧
      runFuel input input.alphabet ha (fuel input input.alphabet interp.terms Δ)
        (.start interp.terms) = (.done (some out), c) ∧
      c ≤ workBound input input.alphabet interp.terms Δ ∧
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
  obtain ⟨halphabet, hembedCost⟩ := embedding_output base input.alphabet embeddingCost hembed
  have hq : 0 < input.alphabet.length := by
    rw [halphabet, List.length_map]
    exact List.length_pos_of_mem (hall 0)
  let Q := NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
    input.degree m J input.agreement interp
  let ri := initialRootInput input interp.terms
  obtain ⟨hc, steps, c, out, hsteps, ht, hrun, hcost, stages, records, hchain, hspec, hout⟩ :=
    attemptWithBudget_execution input input.alphabet ha interp m J Δ hr points hsamples hq hdepth
      hchar hweight hdegree
  rw [hrows] at hc hout
  have hQne : Q ≠ 0 := by
    intro hz
    have hi := hc.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutputWithBudget (d := input.order)
      input.degree m J input.agreement interp = 0 from hz, map_zero] at hi
    exact hc.2.2.2.2.2.2.2.1 hi
  obtain ⟨hdup, hmem⟩ := RestrictedCollectorProof.result_exact_of_roots
    (Q := Q) base hall hn ri halphabet points input.samples hsamples hdepth domain received
      hchain hchar hweight hspec hk hlarge hQne (fun f hd hagree ↦ by
        simpa only [Q] using PreparedDecoderCertificate.certified_embedded_rootWithBudget
          (algebraMap F (Element F a)) domain received interp hc hk f hd hagree)
  dsimp only [ri, initialRootInput, PreparedDecoderMachine.rootInput] at hdup hmem
  simp only [CanonicalOutputProof.basePolynomials, ← hout] at hdup hmem
  have hcharE := (isBelowCharacteristic_map_iff Q input.degree (E := Element F a)).mpr hchar
  have hweightE : differentialWeightedDegree input.degree
      (MvPolynomial.map (algebraMap F (Element F a)) Q) < input.residualLength := by
    simpa only [differentialWeightedDegree_map_eq _ (algebraMap F (Element F a)).injective Q]
      using hweight
  have hw : ∀ cs ∈ out, cs.length = input.dimension := by
    intro cs hcs
    have hwidth : ∀ r ∈ records, r.coefficients.length = input.degree + 1 := fun r hr ↦
      (CanonicalRootSelection.current_zero ri points input.samples hsamples hq hdepth hchain
        hcharE.2 hweightE hspec r hr).1
    rw [hout] at hcs
    exact (CanonicalOutputMachine.result_sound input.order (input.degree + 1) input.dimension
      input.agreement input.alphabet records hwidth hk domain received cs hcs).1
  exact ⟨hembedCost, steps, c, out, hsteps, ht, hrun, hcost, hdup, hdup.of_map _, hmem,
    vector_membership out input.dimension input.agreement domain received hw hmem⟩

-- The actual three-element embedding emits the shared base alphabet with its exact charge.
example :
    let r := QuadraticAlgebra.BaseEmbeddingMachine.runFuel 8
      (.scan [0, 1, 2] [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration (ZMod 3) 2)
    r.1 = .done [0, 1, 2] ∧ r.2.total = 56 := by decide +kernel

end ReedSolomon.ListDecoding.SeparateSampleRestricted
