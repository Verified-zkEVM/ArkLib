/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.RestrictedRootSelection
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderCertificate
/-!
# Exact base outputs with restricted enumeration and separate recovery samples

The materialized enumeration alphabet is explicitly related to the embedded full base list.
The same list supplies guard witnesses; independent extension samples supply root recovery.
Output soundness comes directly from degree and agreement acceptance. Completeness uses the
actual interpolation certificate and a canonical regular base center, not guard-grid soundness.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.RestrictedCollectorProof

open Polynomial JetHornerMachine HiddenDerivative PolynomialDifferential
open StageRootsMachine (Record Stage Term)

/-- The original reduced bound remains sufficient when descending search returns a larger degree.
Zero exceptional degree is included; only a nonempty witness alphabet is needed. -/
theorem reduced_bound_lt {weight L d prescribed D q : ℕ} (hweight : weight < L)
    (hdepth : d ≤ D) (hD : prescribed ≤ D) (hq : 0 < q)
    (hlarge : 2 * (L + d - (prescribed + 1)) ≤ q) : weight - (D - d) < q := by
  omega

variable {F : Type*} [Field F] [DecidableEq F] [Finite F] {a b : F}
variable [Fact (∀ r : F, r ^ 2 ≠ a + b * r)]

omit [DecidableEq F] [Finite F] in
/-- Initial jets of a base polynomial at a base center remain in the embedded base alphabet. -/
theorem embedded_jets {d : ℕ} (base : List F) (hall : ∀ x : F, x ∈ base) (f : F[X])
    (x : QuadraticAlgebra F a b) (hx : x ∈ base.map (algebraMap F (QuadraticAlgebra F a b)))
    (j : Fin (d + 1)) :
    polynomialJet x (f.map (algebraMap F (QuadraticAlgebra F a b))) j ∈
      base.map (algebraMap F (QuadraticAlgebra F a b)) := by
  obtain ⟨y, _hy, rfl⟩ := List.mem_map.mp hx
  refine List.mem_map.mpr ⟨(hasseDeriv j.val f).eval y, hall _, ?_⟩
  simp only [polynomialJet, hasseJet_apply]
  rw [← map_hasseDeriv, eval_map_apply]

variable {d D L k m A : ℕ} (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (input : StageRootsMachine.Input (QuadraticAlgebra F a b))
    (halphabet : input.alphabet = base.map (algebraMap F (QuadraticAlgebra F a b)))
    (points : Fin L ↪ QuadraticAlgebra F a b) (samples : List (QuadraticAlgebra F a b))
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hdepth : d ≤ D)
    {Q : DifferentialPolynomial F d} (interp : NonzeroInterpolationMachine.Output F)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hcert : NonzeroInterpolationMachine.Certified (d := d) D m A
      (List.ofFn fun i ↦ (domain i, received i)) interp)
    (hQ : NonzeroInterpolationMachine.sourceOutput (d := d) D m A interp = Q)
    {stages : List (Stage (QuadraticAlgebra F a b))}
    (hchain : SeparantChainRefinement.OrderedChain input.terms
      (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a b)) Q) stages)
    (hchar : IsBelowCharacteristic D Q) (hweight : differentialWeightedDegree D Q < L)
    {records : List (Record (QuadraticAlgebra F a b))}
    (hspec : StageRootsMachine.Specification input D L samples stages [] records)
    (hk : k ≤ D + 1) (hlarge : 2 * (L + d - (D + 1)) ≤ base.length)

include hall hn halphabet hsamples hdepth hcert hQ hchain hchar hweight hspec hk hlarge

/-- Exact existing collector membership and uniqueness need completeness only for base roots. -/
theorem result_exact :
    (CanonicalOutputProof.basePolynomials d (D + 1) k A input.alphabet
      (List.ofFn fun i ↦ (domain i, received i)) records).Nodup ∧
    ∀ f : F[X], f ∈ CanonicalOutputProof.basePolynomials d (D + 1) k A input.alphabet
      (List.ofFn fun i ↦ (domain i, received i)) records ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received := by
  let : Finite (QuadraticAlgebra F a b) :=
    Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd a b).symm
  let EQ := MvPolynomial.map (algebraMap F (QuadraticAlgebra F a b)) Q
  have hq : 0 < input.alphabet.length := by
    rw [halphabet, List.length_map]
    exact List.length_pos_of_mem (hall 0)
  have hnalphabet : input.alphabet.Nodup := by
    rw [halphabet]
    exact hn.map (algebraMap F (QuadraticAlgebra F a b)).injective
  have hcharE : IsBelowCharacteristic D EQ := (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hweightE : differentialWeightedDegree D EQ < L := by
    simpa only [EQ, differentialWeightedDegree_map_eq _
      (algebraMap F (QuadraticAlgebra F a b)).injective Q] using hweight
  have hwidth : ∀ r ∈ records, r.coefficients.length = D + 1 := fun r hr ↦
    (CanonicalRootSelection.current_identity input points samples hsamples hq hdepth hchain
      hcharE.2 hweightE hspec r hr).1
  have hdup := CanonicalRootSelection.polynomials_nodup_on input points samples input.alphabet
    hsamples hq hnalphabet hdepth hchain hcharE.2 hweightE hspec
  refine ⟨CanonicalOutputProof.basePolynomials_nodup d (D + 1) k A input.alphabet records
    hwidth hk domain received hdup, ?_⟩
  intro f
  rw [CanonicalOutputProof.mem_basePolynomials_iff d (D + 1) k A input.alphabet records
    hwidth hk domain received f]
  constructor
  · exact fun h ↦ ⟨h.1, h.2.1⟩
  · rintro ⟨hd, hagree⟩
    have hroot : differentialSpecialization EQ
        (f.map (algebraMap F (QuadraticAlgebra F a b))) = 0 := by
      simpa only [hQ] using PreparedDecoderCertificate.certified_embedded_root
        (algebraMap F (QuadraticAlgebra F a b)) domain received interp hcert hk f hd hagree
    have hf := CanonicalOutputProof.embedded_natDegree_le (a := a) (b := b) hk f hd
    have hmem : f.map (algebraMap F (QuadraticAlgebra F a b)) ∈
        Polynomial.degreeLT (QuadraticAlgebra F a b) (D + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hf)
    let P : BoundedSolution EQ D := ⟨⟨_, hmem⟩, hroot⟩
    have hne : EQ ≠ 0 := by
      intro hz
      have hQne : Q ≠ 0 := by
        intro hzero
        have hi := hcert.2.2.2.2.2.2.1
        rw [hQ, hzero, map_zero] at hi
        exact hcert.2.2.2.2.2.2.2.1 hi
      apply hQne
      exact MvPolynomial.map_injective _ (algebraMap F (QuadraticAlgebra F a b)).injective
        (by simpa [EQ] using hz)
    have hcard : differentialWeightedDegree D EQ - (D - d) < input.alphabet.length := by
      rw [halphabet, List.length_map]
      exact reduced_bound_lt hweightE hdepth le_rfl (List.length_pos_of_mem (hall 0)) hlarge
    obtain ⟨record, hr, hp⟩ := CanonicalRootSelection.selected_complete_of_jet_mem input points
      samples hsamples hnalphabet hdepth hchain hne hcharE hweightE hspec P hcard (by
        intro x hx j
        rw [halphabet] at hx ⊢
        exact embedded_jets base hall f x hx j)
    exact ⟨hd, hagree, List.mem_map.mpr ⟨record, hr, hp⟩⟩

omit hcert hQ in
/-- Restricted collection is exact from an abstract base-root certificate. -/
theorem result_exact_of_roots (hQne : Q ≠ 0)
    (hroots : ∀ f : F[X], f.degree < k →
      A ≤ Code.agree (evalOnPoints domain f) received →
      differentialSpecialization
        (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a b)) Q)
        (f.map (algebraMap F (QuadraticAlgebra F a b))) = 0) :
    (CanonicalOutputProof.basePolynomials d (D + 1) k A input.alphabet
      (List.ofFn fun i ↦ (domain i, received i)) records).Nodup ∧
    ∀ f : F[X], f ∈ CanonicalOutputProof.basePolynomials d (D + 1) k A input.alphabet
      (List.ofFn fun i ↦ (domain i, received i)) records ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received := by
  let : Finite (QuadraticAlgebra F a b) :=
    Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd a b).symm
  let EQ := MvPolynomial.map (algebraMap F (QuadraticAlgebra F a b)) Q
  have hq : 0 < input.alphabet.length := by
    rw [halphabet, List.length_map]
    exact List.length_pos_of_mem (hall 0)
  have hnalphabet : input.alphabet.Nodup := by
    rw [halphabet]
    exact hn.map (algebraMap F (QuadraticAlgebra F a b)).injective
  have hcharE : IsBelowCharacteristic D EQ := (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hweightE : differentialWeightedDegree D EQ < L := by
    simpa only [EQ, differentialWeightedDegree_map_eq _
      (algebraMap F (QuadraticAlgebra F a b)).injective Q] using hweight
  have hwidth : ∀ r ∈ records, r.coefficients.length = D + 1 := fun r hr ↦
    (CanonicalRootSelection.current_identity input points samples hsamples hq hdepth hchain
      hcharE.2 hweightE hspec r hr).1
  have hdup := CanonicalRootSelection.polynomials_nodup_on input points samples input.alphabet
    hsamples hq hnalphabet hdepth hchain hcharE.2 hweightE hspec
  refine ⟨CanonicalOutputProof.basePolynomials_nodup d (D + 1) k A input.alphabet records
    hwidth hk domain received hdup, ?_⟩
  intro f
  rw [CanonicalOutputProof.mem_basePolynomials_iff d (D + 1) k A input.alphabet records
    hwidth hk domain received f]
  constructor
  · exact fun h ↦ ⟨h.1, h.2.1⟩
  · rintro ⟨hd, hagree⟩
    have hroot : differentialSpecialization EQ
        (f.map (algebraMap F (QuadraticAlgebra F a b))) = 0 := hroots f hd hagree
    have hf := CanonicalOutputProof.embedded_natDegree_le (a := a) (b := b) hk f hd
    have hmem : f.map (algebraMap F (QuadraticAlgebra F a b)) ∈
        Polynomial.degreeLT (QuadraticAlgebra F a b) (D + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hf)
    let P : BoundedSolution EQ D := ⟨⟨_, hmem⟩, hroot⟩
    have hne : EQ ≠ 0 := by
      intro hz
      apply hQne
      exact MvPolynomial.map_injective _ (algebraMap F (QuadraticAlgebra F a b)).injective
        (by simpa [EQ] using hz)
    have hcard : differentialWeightedDegree D EQ - (D - d) < input.alphabet.length := by
      rw [halphabet, List.length_map]
      exact reduced_bound_lt hweightE hdepth le_rfl (List.length_pos_of_mem (hall 0)) hlarge
    obtain ⟨record, hr, hp⟩ := CanonicalRootSelection.selected_complete_of_jet_mem input points
      samples hsamples hnalphabet hdepth hchain hne hcharE hweightE hspec P hcard (by
        intro x hx j
        rw [halphabet] at hx ⊢
        exact embedded_jets base hall f x hx j)
    exact ⟨hd, hagree, List.mem_map.mpr ⟨record, hr, hp⟩⟩

/-- The actual collector run preserves its existing budget and emits precisely the base messages. -/
theorem run_exact :
    ∃ out c, CanonicalOutputMachine.runFuel d input.alphabet (D + 1) k A
        (List.ofFn fun i ↦ (domain i, received i))
        (CanonicalOutputMachine.fuel d input.alphabet (D + 1) k n records) (.start records) =
          (.done out, c) ∧
      (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
      (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
        f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
      (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) ∧
      c ≤ CanonicalOutputMachine.workBound d input.alphabet (D + 1) k n records := by
  have hq : 0 < input.alphabet.length := by
    rw [halphabet, List.length_map]
    exact List.length_pos_of_mem (hall 0)
  have hcharE := (isBelowCharacteristic_map_iff Q D
    (E := QuadraticAlgebra F a b)).mpr hchar
  have hweightE : differentialWeightedDegree D
      (MvPolynomial.map (algebraMap F (QuadraticAlgebra F a b)) Q) < L := by
    simpa only [differentialWeightedDegree_map_eq _
      (algebraMap F (QuadraticAlgebra F a b)).injective Q] using hweight
  have hwidth : ∀ r ∈ records, r.coefficients.length = D + 1 := fun r hr ↦
    (CanonicalRootSelection.current_identity input points samples hsamples hq hdepth hchain
      hcharE.2 hweightE hspec r hr).1
  obtain ⟨out, c, hr, hout, _hlen, hs, hc⟩ :=
    CanonicalOutputMachine.evaluation_runFuel_correct d (D + 1) k A input.alphabet records hwidth
      hk domain received
  obtain ⟨hdup, hmem⟩ := result_exact base hall hn input halphabet points samples hsamples hdepth
    interp domain received hcert hQ hchain hchar hweight hspec hk hlarge
  simp only [CanonicalOutputProof.basePolynomials, ← hout] at hdup hmem
  refine ⟨out, c, hr, hdup, hdup.of_map _, hmem, ?_, hc⟩
  intro cs
  constructor
  · intro hm
    exact ⟨(hs cs hm).1, (hmem _).mp (List.mem_map.mpr ⟨cs, hm, rfl⟩)⟩
  · rintro ⟨hw, hd, ha⟩
    obtain ⟨bs, hb, hp⟩ := List.mem_map.mp ((hmem _).mpr ⟨hd, ha⟩)
    have he := CanonicalRootSelection.coefficients_unique bs cs ((hs bs hb).1.trans hw.symm) hp
    simpa only [he] using hb

omit hall hn halphabet hsamples hdepth hcert hQ hchain hchar hweight hspec hk hlarge

section Checks

abbrev Base := ZMod 3
abbrev Extension := QuadraticAlgebra Base 2 0

local instance : Fact (∀ r : Base, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

def baseWitnesses : List Extension := [0, 1, 2]
def recoverySamples : List Extension := [0, ⟨0, 1⟩]

def restrictedFixture : Option (List (List Base)) :=
  let input : StageRootsMachine.Input Extension :=
    ⟨baseWitnesses, [(1, [(0, 1), (1, 1)])], 0⟩
  match (StageRootsMachine.runFuel input 0 2 50000 (.start recoverySamples)).1 with
  | .done (some records) =>
      some (CanonicalOutputMachine.result 0 baseWitnesses 1 1 1 [(0, 0)] records)
  | _ => none

-- X*Y₀ has reduced separant degree one. Recovery encounters an extension witness first;
-- restricted base guards still retain exactly the zero base message from the actual root run.
example : restrictedFixture = some [[0]] := by decide +kernel

-- The recovery grid's first regular point is outside the complete embedded base alphabet.
example : (⟨0, 1⟩ : Extension) ∉ baseWitnesses := by decide +kernel

-- Keeping the two sample roles separate changes the guard decision at base center one.
example : let r : Record Extension :=
    ⟨⟨⟨[(1, [(0, 1), (1, 1)])], some (1, 1)⟩, [], [(1, [(0, 1), (1, 0)])]⟩, 1, [0]⟩
    CanonicalRootSelection.accepted 0 baseWitnesses r = true ∧
      CanonicalRootSelection.accepted 0 recoverySamples r = false := by decide +kernel

-- Zero exceptional degree satisfies the reduced bound, including a strictly larger found D.
example : 0 - (4 - 1) < 7 :=
  reduced_bound_lt (L := 3) (prescribed := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end Checks

end ReedSolomon.ListDecoding.RestrictedCollectorProof
