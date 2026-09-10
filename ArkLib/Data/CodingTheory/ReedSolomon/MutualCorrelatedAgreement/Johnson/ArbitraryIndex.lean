/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement

/-!
# Johnson mutual correlated agreement on an arbitrary finite index type

The geometric Johnson theorem is most naturally stated for coordinates indexed by `Fin n`.
This file transfers it to the public Reed--Solomon code interface, whose coordinates may have any
finite nonempty index type.

The exceptional set is selected before the agreement subset and the candidate. For a candidate in
the projected code, we first recover one global degree-bounded polynomial. Its full agreement set
contains the requested subset, so the exact line-recovery theorem applies there. We then restrict
the recovered witnesses back to the original subset. This is the quantifier order needed by the
MCA exceptional-set bridge.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- **Every-subset Johnson recovery on an arbitrary finite nonempty coordinate type.**

The code contains evaluations of polynomials of degree at most `D`. At agreement
`sqrt(D/n) + eta`, fix one exceptional set for the received pair before the challenge, agreement
subset, and projected-code candidate. Outside it, both received constituents extend to global
degree-bounded Reed--Solomon codewords on every qualifying subset.

The field may be infinite and have arbitrary characteristic. Finite-field probability sampling
is a separate corollary below.
-/
theorem exists_exceptional_johnson_lineMCA_arbitrary_index
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
    (domain : ι ↪ F) (D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1)
    (U : Fin 2 → ι → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        johnsonE0 (Fintype.card ι) D
          ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta ∧
      ∀ z, z ∉ exceptional → ∀ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι *
          (1 - (1 - johnsonAgreement (Fintype.card ι) D eta)) →
        projectedWord (fun i => ∑ j, AffineLineGenerator F z j • U j i) T ∈
          projectedCodeSubmod (code domain (D + 1)) T →
        ∃ p : Fin 2 → code domain (D + 1),
          ∀ j i, i ∈ T → (p j).val i = U j i := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let domainFin : Fin n ↪ F := e.symm.toEmbedding.trans domain
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_johnson_lineMCA_at_ceil n D eta hD hDn heta ha
      domainFin (fun i ↦ U 0 (e.symm i)) (fun i ↦ U 1 (e.symm i))
  refine ⟨exceptional, ?_, ?_⟩
  · simpa only [n, A] using hcard
  · intro z hz T hT hcombination
    have hcombination' :
        projectedWord (fun i ↦ U 0 i + z * U 1 i) T ∈
          projectedCodeSubmod (code domain (D + 1)) T := by
      simpa [AffineLineGenerator, Fin.sum_univ_two, smul_eq_mul] using hcombination
    obtain ⟨P, hPdegree, hPOnT⟩ :=
      (projectedWord_mem_code_iff_exists_polynomial domain (D + 1)
        (fun i ↦ U 0 i + z * U 1 i) T).mp hcombination'
    let TFin : Finset (Fin n) := T.image e
    have hTFinCard : TFin.card = T.card := by
      simpa only [TFin] using Finset.card_image_of_injective T e.injective
    have hAT : A ≤ T.card := by
      apply Nat.ceil_le.mpr
      have hT' : (johnsonAgreement n D eta * n : ℝ) ≤ T.card := by
        simpa only [n, sub_sub_cancel, mul_comm] using hT
      exact hT'
    have hTFinSubset :
        TFin ⊆ polynomialAgreementSet domainFin
          (fun i ↦ U 0 (e.symm i) + z * U 1 (e.symm i)) P := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [domainFin, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Equiv.symm_apply_apply] using hPOnT i hi
    have hAgreement :
        A ≤ (polynomialAgreementSet domainFin
          (fun i ↦ U 0 (e.symm i) + z * U 1 (e.symm i)) P).card :=
      (hAT.trans_eq hTFinCard.symm).trans (Finset.card_le_card hTFinSubset)
    obtain ⟨pair, hpair0, hpair1, _hformula, hfull⟩ :=
      hgood z hz P hPdegree hAgreement
    let P0 : (code domain (D + 1) : Set (ι → F)) :=
      ⟨evalOnPoints domain pair.1, evalOnPoints_mem_code_of_degree_lt hpair0⟩
    let P1 : (code domain (D + 1) : Set (ι → F)) :=
      ⟨evalOnPoints domain pair.2, evalOnPoints_mem_code_of_degree_lt hpair1⟩
    refine ⟨![P0, P1], ?_⟩
    intro j i hi
    have hiFin : e i ∈ TFin := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hiAgreement := hTFinSubset hiFin
    have hiCommon :
        e i ∈ commonPolynomialAgreementSet domainFin
          (fun t ↦ U 0 (e.symm t)) (fun t ↦ U 1 (e.symm t)) pair.1 pair.2 := by
      rw [← hfull]
      exact hiAgreement
    have hiBoth := (Finset.mem_filter.mp hiCommon).2
    fin_cases j
    · change pair.1.eval (domain i) = U 0 i
      simpa only [domainFin, Function.Embedding.trans_apply,
        Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hiBoth.1
    · change pair.2.eval (domain i) = U 1 i
      simpa only [domainFin, Function.Embedding.trans_apply,
        Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hiBoth.2

open Classical in
/-- **The direct Johnson line-MCA probability bound on arbitrary finite coordinates.**

Uniform finite-field sampling converts the preceding arbitrary-field exceptional-set theorem to
the uncapped quotient `johnsonE0 / |F|`. A capped presentation remains available from the
`Fin n` probability theorem, but the direct quotient is the useful quantitative interface.
-/
theorem johnson_mcaError_le_arbitrary_index
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (AffineLineGenerator F) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal
        (johnsonE0 (Fintype.card ι) D
          ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta /
            (Fintype.card F : ℝ)) := by
  apply CoreDefinitions.mcaError_le_of_exists_exceptional_set_codewords
  intro U
  exact exists_exceptional_johnson_lineMCA_arbitrary_index
    domain D eta hD hDn heta ha U

end ReedSolomon
