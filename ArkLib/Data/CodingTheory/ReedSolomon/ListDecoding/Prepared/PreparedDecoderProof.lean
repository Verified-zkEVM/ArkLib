/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageInputExecution
/-!
# Exact prepared decoding after actual successful interpolation

The certificate supplies agreement-to-root completeness. The scalar allocator, root scan and
collector execute their actual programs, and their completed traces compose in the existing
prepared driver. No semantic output or agreement-to-output callback is assumed.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PreparedDecoderProof

open Polynomial JetHornerMachine HiddenDerivative PreparedDecoderCertificate PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Search success exposes the exact certificate, ambient bounds, and physical sparse layout. -/
theorem search_certificate {k d m A n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (found : AmbientSearchMachine.Output F)
    (hr : (AmbientSearchMachine.run k d m A
      (List.ofFn fun i ↦ (domain i, received i))).1 = some found) :
    NonzeroInterpolationMachine.Certified (d := d) found.degree m A
      (List.ofFn fun i ↦ (domain i, received i)) found.interpolant ∧
    d ≤ found.degree ∧ k ≤ found.degree + 1 ∧ found.degree < n ∧
    MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2))
      found.interpolant.terms := by
  obtain ⟨result, c, he, _hc, hs⟩ := AmbientSearchMachine.run_complete k d m A
    (List.ofFn fun i ↦ (domain i, received i))
  have hr' := congrArg Prod.fst he
  rw [hr] at hr'
  change some found = result at hr'
  subst result
  obtain ⟨hl, hu, hcert⟩ := hs found rfl
  refine ⟨hcert, ?_, ?_, by simpa only [List.length_ofFn] using hu,
    run_layout k d m A _ found hr⟩
  · have := le_max_right (k - 1) (d + 1)
    omega
  · have := le_max_left (k - 1) (d + 1)
    omega

/-- The prepared driver returns each target-degree agreeing base polynomial exactly once.
The premise is actual successful interpolation; all three later child executions are proved.
The returned cost is the actual trace charge, with no claimed whole-instance majorant. -/
theorem run_exact {k d m A n L : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (found : AmbientSearchMachine.Output F)
    (hr : (AmbientSearchMachine.run k d m A
      (List.ofFn fun i ↦ (domain i, received i))).1 = some found)
    (a : F) (ha : ¬IsSquare a) (alphabet samples : List (QuadraticAlgebra F a 0))
    (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hall : ∀ x : QuadraticAlgebra F a 0, x ∈ alphabet) (hn : alphabet.Nodup)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant) < L) :
    let input : PreparedDecoderMachine.Input F a :=
      ⟨alphabet, samples, List.ofFn (fun i ↦ (domain i, received i)), d, found.degree, L, k, A⟩
    ∃ steps cost out,
      PreparedDecoderMachine.Trace input ha steps (.start found.interpolant.terms) cost
        (.done (some out)) ∧
      PreparedDecoderMachine.runFuel input ha steps (.start found.interpolant.terms) =
        (.done (some out), cost) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    apply ha
    exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let input : PreparedDecoderMachine.Input F a :=
    ⟨alphabet, samples, List.ofFn (fun i ↦ (domain i, received i)), d, found.degree, L, k, A⟩
  let Q := NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant
  let EQ := MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0)) Q
  let ets := MvPolynomial.QuadraticInputMachine.embedded (a := a) found.interpolant.terms
  let ri := PreparedDecoderMachine.rootInput input ets
  obtain ⟨hc, hdepth, hk, _hD, hl⟩ := search_certificate domain received found hr
  have hrep : MvPolynomial.EvaluationMachine.sparsePolynomial ets =
      MvPolynomial.rename HighestJetTransport.encodeJet EQ :=
    embedded_representation _ found.interpolant hc a
  have hQne : Q ≠ 0 := by
    intro hz
    have he := hc.2.2.2.2.2.2.1
    have hnz := hc.2.2.2.2.2.2.2.1
    rw [show NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A
      found.interpolant = 0 from hz, map_zero] at he
    exact hnz he
  have hEQne : EQ ≠ 0 := by
    intro hz
    apply hQne
    exact MvPolynomial.map_injective _
      (algebraMap F (QuadraticAlgebra F a 0)).injective (by simpa [EQ] using hz)
  have hEQchar : IsBelowCharacteristic found.degree EQ :=
    (isBelowCharacteristic_map_iff Q found.degree).mpr hchar
  have hEQweight : differentialWeightedDegree found.degree EQ < L := by
    simpa only [EQ, differentialWeightedDegree_map_eq _
      (algebraMap F (QuadraticAlgebra F a 0)).injective Q] using hweight
  have hElayout : MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (d + 2)) ets :=
    MvPolynomial.QuadraticInputMachine.embedded_layout _ _ hl
  obtain ⟨cc, hconvert, _hcc⟩ := MvPolynomial.QuadraticInputMachine.scan_trace
    found.interpolant.terms ([] : List (MvPolynomial.QuadraticInputMachine.Term
      (QuadraticAlgebra F a 0)))
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hconvert
  obtain ⟨stages, records, cr, hchain, _hstagecount, hrun, _hvisited, hspec,
      _hwidth, _hcount, _hrootcost⟩ := StageRootsMachine.execution_input_budget ri points samples
    hsamples (List.length_pos_of_mem (hall 0)) hdepth (jetTotalDegree EQ) EQ
    hElayout hrep hEQne hEQchar.2 le_rfl hEQweight
  obtain ⟨nr, _hnr, hroots⟩ := StageRootsMachine.runFuel_refines ri found.degree L
    (StageRootsMachine.inputFuel ri found.degree L samples.length (jetTotalDegree EQ))
    (.start samples)
  rw [hrun] at hroots
  obtain ⟨out, co, hcollectrun, hout, _hlen, hdup, hvecdup, hwidth, hpoly, _hcost⟩ :=
    CanonicalOutputProof.stage_runFuel_correct ri points samples hsamples hall hn hdepth hrep
      hchain hEQne hEQchar hEQweight hspec hk domain received (A := A)
  obtain ⟨no, _hno, hcollect⟩ := CanonicalOutputMachine.runFuel_refines d (found.degree + 1) k A
    (CanonicalOutputMachine.fuel d samples (found.degree + 1) k n records) samples
    (List.ofFn fun i ↦ (domain i, received i)) (.start records)
  rw [hcollectrun] at hcollect
  have hpipeline := PreparedDecoderMachine.pipeline_trace input ha found.interpolant.terms ets
    records out (2 * found.interpolant.terms.length + 3) nr no co cc cr hconvert hroots hcollect
  refine ⟨_, _, out, hpipeline, ?_, hdup, hvecdup, ?_, ?_⟩
  · simpa only [Nat.add_zero] using hpipeline.runFuel_done 0
  · intro f
    rw [hpoly]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · rintro ⟨hd, hagree⟩
      exact ⟨hd, hagree, certified_embedded_root _ domain received found.interpolant hc hk
        f hd hagree⟩
  · intro cs
    constructor
    · intro hm
      have hf := (hpoly _).mp (List.mem_map.mpr ⟨cs, hm, rfl⟩)
      exact ⟨hwidth cs hm, hf.1, hf.2.1⟩
    · rintro ⟨hw, hd, hagree⟩
      have hf := (hpoly _).mpr ⟨hd, hagree, certified_embedded_root _ domain received
        found.interpolant hc hk (coefficientPolynomial cs) hd hagree⟩
      obtain ⟨bs, hb, he⟩ := List.mem_map.mp hf
      have heq := CanonicalRootSelection.coefficients_unique bs cs
        ((hwidth bs hb).trans hw.symm) he
      simpa only [heq] using hb

end ReedSolomon.ListDecoding.PreparedDecoderProof
