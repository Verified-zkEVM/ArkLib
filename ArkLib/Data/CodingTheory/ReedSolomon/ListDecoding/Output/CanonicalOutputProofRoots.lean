/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputProof
/-!
# Exact base outputs from the actual ordered root scan

The existing collector enumerates each base polynomial satisfying the initial differential
identity, target degree, and exact agreement threshold once. Its existing fuel and work bound
are preserved. The implication from interpolation constraints to the identity is a separate join.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputProof

open Polynomial JetHornerMachine HiddenDerivative PolynomialDifferential
open StageRootsMachine (Record Stage Term)

variable {F : Type*} [Field F] [DecidableEq F] {a b : F}
variable [Fact (∀ r : F, r ^ 2 ≠ a + b * r)]

omit [DecidableEq F] in
/-- The target degree bound implies the root scan's bound after base-field embedding. -/
theorem embedded_natDegree_le {D k : ℕ} (hk : k ≤ D + 1) (f : F[X]) (hf : f.degree < k) :
    (f.map (algebraMap F (QuadraticAlgebra F a b))).natDegree ≤ D := by
  apply natDegree_map_le.trans
  by_cases hz : f = 0
  · simp [hz]
  · have hlt : f.natDegree < k := (natDegree_lt_iff_degree_lt hz).mpr hf
    omega

variable {d D L k A : ℕ} (input : StageRootsMachine.Input (QuadraticAlgebra F a b))
    (points : Fin L ↪ QuadraticAlgebra F a b) (samples : List (QuadraticAlgebra F a b))
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hall : ∀ x : QuadraticAlgebra F a b, x ∈ input.alphabet) (hn : input.alphabet.Nodup)
    (hdepth : d ≤ D) {ts : List (Term (QuadraticAlgebra F a b))}
    {Q : DifferentialPolynomial (QuadraticAlgebra F a b) d}
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q)
    {stages : List (Stage (QuadraticAlgebra F a b))}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hne : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hweight : differentialWeightedDegree D Q < L)
    {records : List (Record (QuadraticAlgebra F a b))}
    (hspec : StageRootsMachine.Specification input D L samples stages [] records)
    (hk : k ≤ D + 1) {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)

include hsamples hall hn hdepth hQ hchain hne hchar hweight hspec hk

/-- Actual stage roots and canonical selection give exact, duplicate-free base membership. -/
theorem stage_result_correct :
    (basePolynomials d (D + 1) k A samples
      (List.ofFn fun i ↦ (domain i, received i)) records).Nodup ∧
    ∀ f : F[X], f ∈ basePolynomials d (D + 1) k A samples
      (List.ofFn fun i ↦ (domain i, received i)) records ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received ∧
      differentialSpecialization Q (f.map (algebraMap F (QuadraticAlgebra F a b))) = 0 := by
  have hwidth : ∀ r ∈ records, r.coefficients.length = D + 1 := fun r hr ↦
    (CanonicalRootSelection.current_zero input points samples hsamples
      (List.length_pos_of_mem (hall 0)) hdepth hchain hchar.2 hweight hspec r hr).1
  obtain ⟨hrootNodup, hroots⟩ := CanonicalRootSelection.selection_correct input points samples
    hsamples hall hn hdepth hQ hchain hne hchar hweight hspec
  refine ⟨basePolynomials_nodup d (D + 1) k A samples records hwidth hk domain received
    hrootNodup, ?_⟩
  intro f
  rw [mem_basePolynomials_iff d (D + 1) k A samples records hwidth hk domain received f,
    hroots]
  constructor
  · rintro ⟨hd, ha, _hbound, hroot⟩
    exact ⟨hd, ha, hroot⟩
  · rintro ⟨hd, ha, hroot⟩
    exact ⟨hd, ha, embedded_natDegree_le hk f hd, hroot⟩

/-- The same collector run emits precisely the base solutions once, within its existing bound. -/
theorem stage_runFuel_correct :
    ∃ out c, Output.runFuel d samples (D + 1) k A
        (List.ofFn fun i ↦ (domain i, received i))
        (Output.fuel d samples (D + 1) k n records) (.start records) = (.done out, c) ∧
      out = Output.result d samples (D + 1) k A
        (List.ofFn fun i ↦ (domain i, received i)) records ∧
      out.length ≤ records.length ∧ (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ cs ∈ out, cs.length = k) ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received ∧
        differentialSpecialization Q (f.map (algebraMap F (QuadraticAlgebra F a b))) = 0) ∧
      c ≤ Output.workBound d samples (D + 1) k n records := by
  have hwidth : ∀ r ∈ records, r.coefficients.length = D + 1 := fun r hr ↦
    (CanonicalRootSelection.current_zero input points samples hsamples
      (List.length_pos_of_mem (hall 0)) hdepth hchain hchar.2 hweight hspec r hr).1
  obtain ⟨out, c, hrun, hout, hlen, hsound, hcost⟩ :=
    CanonicalOutputMachine.evaluation_runFuel_correct d (D + 1) k A samples records hwidth hk
      domain received
  obtain ⟨hdup, hmem⟩ := stage_result_correct input points samples hsamples hall hn hdepth hQ
    hchain hne hchar hweight hspec hk domain received (A := A)
  change ((Output.result d samples (D + 1) k A
    (List.ofFn fun i ↦ (domain i, received i)) records).map coefficientPolynomial).Nodup at hdup
  rw [← hout] at hdup
  refine ⟨out, c, hrun, hout, hlen, hdup, hdup.of_map _,
    fun cs hcs ↦ (hsound cs hcs).1, ?_, hcost⟩
  simpa only [basePolynomials, ← hout] using hmem

/-- Physical output membership is exact at width `k`, including canonical zero padding. -/
theorem stage_vector_mem_iff (cs : List F) :
    cs ∈ Output.result d samples (D + 1) k A
      (List.ofFn fun i ↦ (domain i, received i)) records ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
      differentialSpecialization Q
        ((coefficientPolynomial cs).map (algebraMap F (QuadraticAlgebra F a b))) = 0 := by
  obtain ⟨out, c, _hrun, hout, _hlen, _hdup, _hvecdup, hwidth, hmem, _hcost⟩ :=
    stage_runFuel_correct input points samples hsamples hall hn hdepth hQ hchain hne hchar
      hweight hspec hk domain received (A := A)
  rw [← hout]
  constructor
  · intro hc
    exact ⟨hwidth cs hc, (hmem _).mp (List.mem_map.mpr ⟨cs, hc, rfl⟩)⟩
  · rintro ⟨hlen, hd, ha, hroot⟩
    obtain ⟨bs, hb, hp⟩ := List.mem_map.mp ((hmem _).mpr ⟨hd, ha, hroot⟩)
    have he : bs = cs := CanonicalRootSelection.coefficients_unique bs cs
      ((hwidth bs hb).trans hlen.symm) hp
    simpa only [he] using hb

end ReedSolomon.ListDecoding.CanonicalOutputProof
