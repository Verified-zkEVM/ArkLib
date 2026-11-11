/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Program
public import ArkLib.ProofSystem.Fri.Spec.InputRelation

/-!
# Recovery from a safe retained FRI history

The measured history extractor recovers a bounded-degree witness from sufficiently many
accepting positions. Its witness agrees with the initial word at every accepting position.
The recovery statement is independent of the number of random verifier queries.

This instantiates the accepting-position interpolation argument in Corollary 5.6 of the
March 27, 2026 revision of [GMW25] for the named executable extractor.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly Finset
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

private theorem acceptedList_length (hs : (∑ j, (s j).val) ≤ n) :
    (acceptedList s o α hs (List.finRange (2 ^ n))).length =
      (acceptingQueries s hs o α).card := by
  classical
  have hn : (acceptedList s o α hs (List.finRange (2 ^ n))).Nodup :=
    (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext z
  simp [acceptedList]

private theorem selection_interpolation_eq (hs : (∑ j, (s j).val) ≤ n) (D : ℕ)
    (state : Selection s o D)
    (hvalid : state.Valid s o (acceptedList s o α hs (List.finRange (2 ^ n))))
    (hcard : D ≤ (acceptingQueries s hs o α).card) :
    ∃ zs : Fin D → Fin (2 ^ n), Function.Injective zs ∧
      (∀ i, zs i ∈ acceptingQueries s hs o α) ∧
      CPolynomial.CLagrange.interpolate Finset.univ
        (fun j : Fin D ↦ state.nodes[j.val]?.getD 0)
        (fun j : Fin D ↦ state.values[j.val]?.getD 0) =
      CPolynomial.CLagrange.interpolate Finset.univ (fun i ↦ ω (zs i))
        (fun i ↦ initialWord s o (zs i)) := by
  classical
  have hlen : state.selected.length = D := by
    rw [hvalid.2, List.length_take, acceptedList_length, Nat.min_eq_left hcard]
  have hnodup : state.selected.Nodup := by
    rw [hvalid.2]
    exact ((List.nodup_finRange _).filter _).take
  let zs : Fin D → Fin (2 ^ n) := fun i ↦
    state.selected.get (i.cast hlen.symm)
  refine ⟨zs, ?_, ?_, ?_⟩
  · intro i j h
    have hcast := hnodup.injective_get h
    exact Fin.ext (congrArg (fun z : Fin state.selected.length ↦ z.val) hcast)
  · intro i
    have hm : zs i ∈ state.selected := List.get_mem _ _
    rw [hvalid.2] at hm
    have ha := List.mem_of_mem_take hm
    simpa [acceptedList] using ha
  · have hx : (fun j : Fin D ↦ state.nodes[j.val]?.getD 0) =
        (fun j ↦ ω (zs j)) := by
      funext j
      rw [state.nodes_eq]
      have hj : j.val < state.selected.length := by rw [hlen]; exact j.isLt
      simp [zs, List.get_eq_getElem, List.getElem?_eq_getElem hj]
    have hy : (fun j : Fin D ↦ state.values[j.val]?.getD 0) =
        (fun j ↦ initialWord s o (zs j)) := by
      funext j
      rw [state.values_eq]
      have hj : j.val < state.selected.length := by rw [hlen]; exact j.isLt
      simp [zs, List.get_eq_getElem, List.getElem?_eq_getElem hj]
    rw [hx, hy]

end Fri.Spec.Extractor

namespace Fri.Spec

open Domain Polynomial ReedSolomon OracleComp Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- Interpolation at distinct accepting positions recovers a bounded-degree witness agreeing
with the initial word at every accepting position. -/
private theorem interpolate_acceptingQueries_agrees
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ (acceptingQueries s hs o α).card)
    (zs : Fin (2 ^ (∑ j, (s j).val) * d.val) → Fin (2 ^ n))
    (hzs : Function.Injective zs) (hmem : ∀ i, zs i ∈ acceptingQueries s hs o α) :
    let p := CompPoly.CPolynomial.CLagrange.interpolate univ
      (fun i ↦ ω (zs i)) (fun i ↦ initialWord s o (zs i))
    p ∈ Witness F s d 0 ∧ ∀ z ∈ acceptingQueries s hs o α,
      p.eval (ω z) = initialWord s o z := by
  classical
  obtain ⟨u, hu, hagree⟩ := exists_codeword_agree_of_acceptingQueries s d hs o α θ
    hsafe hdegree (acceptingQueries s hs o α) (fun _ h ↦ h) hlarge
  obtain ⟨q, hq, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hu
  have hnodes : Set.InjOn (fun i ↦ ω (zs i)) (univ : Finset
      (Fin (2 ^ (∑ j, (s j).val) * d.val))) :=
    (Domain.CosetFftDomain.injective.comp hzs).injOn
  have hqeq : q = Lagrange.interpolate univ
      (fun i ↦ ω (zs i)) (fun i ↦ initialWord s o (zs i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hnodes
    · simpa using hq
    · intro i _
      exact (heval (zs i)).trans (hagree (zs i) (hmem i))
  constructor
  · change _ ∈ CompPoly.CPolynomial.degreeLT (2 ^ (∑ j, (s j).val) * d.val)
    rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT,
      CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate, ← hqeq]
    exact hq
  · intro z hz
    rw [CompPoly.CPolynomial.eval_toPoly,
      CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate, ← hqeq]
    exact (heval z).trans (hagree z hz)

/-- Agreement at every accepting position bounds a polynomial's relative input distance. -/
private theorem relHammingDist_le_one_sub_card_div_of_agree_acceptingQueries
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (p : CompPoly.CPolynomial F)
    (hagree : ∀ z ∈ acceptingQueries s hs o α, p.eval (ω z) = initialWord s o z) :
    (Code.relHammingDist (initialWord s o) (fun z ↦ p.eval (ω z)) : ℝ) ≤
      1 - (acceptingQueries s hs o α).card / (2 ^ n : ℝ) := by
  have hcard : (acceptingQueries s hs o α).card ≤
      Code.agree (fun z ↦ p.eval (ω z)) (initialWord s o) := by
    apply Finset.card_le_card
    intro z hz
    exact mem_filter.mpr ⟨mem_univ z, hagree z hz⟩
  simpa using Code.relHammingDist_le_one_sub_div_of_le_agree hcard

/-- The inclusive rate threshold supplies enough accepting positions for interpolation. -/
private theorem interpolationDimension_le_card_acceptingQueries
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) (τ : ℝ)
    (hrate : τ ≤ 1 - (2 ^ (∑ j, (s j).val) * d.val : ℕ) / (2 ^ n : ℝ))
    (hlarge : (2 ^ n : ℝ) * (1 - τ) ≤ (acceptingQueries s hs o α).card) :
    2 ^ (∑ j, (s j).val) * d.val ≤ (acceptingQueries s hs o α).card := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hdim : ((2 ^ (∑ j, (s j).val) * d.val : ℕ) : ℝ) ≤
      (2 ^ n : ℝ) * (1 - τ) := by
    have h : ((2 ^ (∑ j, (s j).val) * d.val : ℕ) : ℝ) / 2 ^ n ≤ 1 - τ := by
      linarith
    simpa only [mul_comm] using (div_le_iff₀ hN).mp h
  exact_mod_cast hdim.trans hlarge

/-- Agreement at the threshold gives the required closed-ball proximity. -/
private theorem relHammingDist_le_of_agree_acceptingQueries
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (p : CompPoly.CPolynomial F) (τ : ℝ)
    (hlarge : (2 ^ n : ℝ) * (1 - τ) ≤ (acceptingQueries s hs o α).card)
    (hagree : ∀ z ∈ acceptingQueries s hs o α, p.eval (ω z) = initialWord s o z) :
    (Code.relHammingDist (initialWord s o) (fun z ↦ p.eval (ω z)) : ℝ) ≤ τ := by
  refine (relHammingDist_le_one_sub_card_div_of_agree_acceptingQueries s hs o α p hagree).trans ?_
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have h := (le_div_iff₀ hN).mpr (show (1 - τ) * 2 ^ n ≤ _ by
    simpa only [mul_comm] using hlarge)
  linarith


end Fri.Spec

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly Finset
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

private theorem interpolate_selection_agrees (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ (acceptingQueries s hs o α).card)
    (hcard : 2 ^ (∑ j, (s j).val) * d.val ≤ (acceptingQueries s hs o α).card)
    (state : Selection s o (2 ^ (∑ j, (s j).val) * d.val))
    (hvalid : state.Valid s o (acceptedList s o α hs (List.finRange (2 ^ n)))) :
    let p := CPolynomial.CLagrange.interpolate Finset.univ
      (fun j : Fin (2 ^ (∑ j, (s j).val) * d.val) ↦ state.nodes[j.val]?.getD 0)
      (fun j : Fin (2 ^ (∑ j, (s j).val) * d.val) ↦ state.values[j.val]?.getD 0)
    p ∈ Witness F s d 0 ∧ ∀ z ∈ acceptingQueries s hs o α,
      p.eval (ω z) = initialWord s o z := by
  obtain ⟨zs, hinj, hmem, heq⟩ := selection_interpolation_eq s o α hs _ state hvalid hcard
  dsimp only
  rw [heq]
  exact interpolate_acceptingQueries_agrees s d hs o α θ hsafe hdegree hlarge zs hinj hmem

end Fri.Spec.Extractor

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly Finset
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

private theorem prepareInputs_eq_some (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (hdegree : (finalPolynomial s o).natDegree < d.val) :
    ∃ input, (profile s o α (prepareInputs s o α d)).1 = some input := by
  simp only [prepareInputs, profile_bind, profile_certified_fst, profile_pure,
    dite_eq_left hdegree]
  exact ⟨_, rfl⟩

private theorem interpolateSelection_eq_some (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ (acceptingQueries s hs o α).card)
    (hcard : 2 ^ (∑ j, (s j).val) * d.val ≤ (acceptingQueries s hs o α).card)
    (state : Selection s o (foldingDegree s d 0))
    (hvalid : state.Valid s o (acceptedList s o α hs (List.finRange (2 ^ n)))) :
    ∃ p, (profile s o α (interpolateSelection s d o α state)).1 = some p ∧
      ∀ z ∈ acceptingQueries s hs o α, p.1.eval (ω z) = initialWord s o z := by
  let p := CPolynomial.CLagrange.interpolate Finset.univ
    (fun j : Fin (foldingDegree s d 0) ↦ state.nodes[j.val]?.getD 0)
    (fun j : Fin (foldingDegree s d 0) ↦ state.values[j.val]?.getD 0)
  have hp : p ∈ Witness F s d 0 ∧ ∀ z ∈ acceptingQueries s hs o α,
      p.eval (ω z) = initialWord s o z :=
    interpolate_selection_agrees s d hs o α θ hsafe hdegree hlarge hcard state hvalid
  have hcount : foldingDegree s d 0 ≤ state.count := by
    rw [hvalid.1, acceptedList_length]
    simpa [foldingDegree] using hcard
  have hD : 0 < foldingDegree s d 0 := by unfold foldingDegree; positivity
  have hpolydegree : p.toPoly.degree < foldingDegree s d 0 := by
    have hp' : p ∈ CPolynomial.degreeLT (foldingDegree s d 0) := hp.1
    rw [CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT] at hp'
    exact hp'
  have hdegreep : p.natDegree < foldingDegree s d 0 := by
    rw [CPolynomial.natDegree_toPoly]
    by_cases hp0 : p.toPoly = 0
    · rw [hp0, Polynomial.natDegree_zero]
      exact hD
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpolydegree
  dsimp only [p] at hdegreep
  refine ⟨⟨p, hp.1⟩, ?_, hp.2⟩
  simp only [interpolateSelection, dite_eq_left hcount, profile_bind,
    profile_certified_fst, profile_pure, dite_eq_left hdegreep]
  rfl

/-- A safe history with enough accepting positions yields a witness agreeing on every
accepting position. -/
theorem extractHistory_eq_some_of_safeHistory (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ (acceptingQueries s hs o α).card)
    (hcard : 2 ^ (∑ j, (s j).val) * d.val ≤ (acceptingQueries s hs o α).card) :
    ∃ p, extractHistory s d hs o α = some p ∧
      ∀ z ∈ acceptingQueries s hs o α, p.1.eval (ω z) = initialWord s o z := by
  obtain ⟨input, hinput⟩ := prepareInputs_eq_some s d o α hdegree
  unfold extractHistory extractProgram
  rw [profile_bind]
  dsimp only
  rw [hinput]
  dsimp only
  rw [profile_bind]
  dsimp only
  exact interpolateSelection_eq_some s d hs o α θ hsafe hdegree hlarge hcard _
    (profile s o α (scan s o α hs input.generator (checkPosition s o α hs input)
      (foldingDegree s d 0))).1.property

end Fri.Spec.Extractor

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly Finset
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- A safe history above the density threshold yields a witness within distance `τ`. -/
theorem extractHistory_eq_some_of_density (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ τ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hτ : τ ≤ θ)
    (hrate : τ ≤ 1 - (2 ^ (∑ j, (s j).val) * d.val : ℕ) / (2 ^ n : ℝ))
    (hlarge : (2 ^ n : ℝ) * (1 - τ) ≤ (acceptingQueries s hs o α).card) :
    ∃ p, extractHistory s d hs o α = some p ∧
      (Code.relHammingDist (initialWord s o) (fun z ↦ p.1.eval (ω z)) : ℝ) ≤ τ := by
  have hcard := interpolationDimension_le_card_acceptingQueries s d hs o α τ hrate hlarge
  have hlift : (2 ^ n : ℝ) * (1 - θ) ≤ (acceptingQueries s hs o α).card :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hτ 1) (by positivity)).trans hlarge
  obtain ⟨p, hp, hagree⟩ := extractHistory_eq_some_of_safeHistory s d hs o α θ hsafe
    hdegree hlift hcard
  exact ⟨p, hp, relHammingDist_le_of_agree_acceptingQueries s hs o α p.1 τ hlarge hagree⟩

end Fri.Spec.Extractor
