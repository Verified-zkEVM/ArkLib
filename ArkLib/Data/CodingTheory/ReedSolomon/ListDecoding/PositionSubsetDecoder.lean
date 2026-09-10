/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SampleInterpolation
public import Mathlib.Data.Finset.Powerset
/-!
# Reference decoder from agreeing position subsets

This executable decoder enumerates `k`-subsets of the received positions, interpolates the unique
polynomial through each subset, checks its full agreement, and removes duplicate coefficient
vectors. It never enumerates field elements. The construction is exponential in the block length
and is intended as a correctness reference and as the bounded-length branch of faster decoders.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PositionSubsetDecoder

open Polynomial JetHornerMachine
open SampleInterpolation

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- All `k`-subsets of the materialized positions, in the finset's executable canonical order. -/
def samples (n k : ℕ) : List (Finset (Fin n)) :=
  (List.sublistsLen k (List.ofFn id)).map List.toFinset

/-- The executable list contains exactly the `k`-element sets of input positions. -/
theorem mem_samples_iff (sample : Finset (Fin n)) (k : ℕ) :
    sample ∈ samples n k ↔ sample.card = k := by
  constructor
  · intro hsample
    rcases List.mem_map.mp hsample with ⟨positions, hpositions, hset⟩
    have hspec := List.mem_sublistsLen.mp hpositions
    have hnodup : positions.Nodup :=
      (List.nodup_ofFn.mpr Function.injective_id).sublist hspec.1
    rw [← hset, List.toFinset_card_of_nodup hnodup, hspec.2]
  · intro hcard
    let positions := (List.ofFn id).filter fun i ↦ i ∈ sample
    have hsub : List.Sublist positions (List.ofFn id) := List.filter_sublist
    have hnodup : positions.Nodup :=
      (List.nodup_ofFn.mpr Function.injective_id).filter _
    have hset : positions.toFinset = sample := by
      ext i
      simp [positions]
    have hlength : positions.length = k := by
      rw [← List.toFinset_card_of_nodup hnodup, hset, hcard]
    exact List.mem_map.mpr ⟨positions, List.mem_sublistsLen.mpr ⟨hsub, hlength⟩, hset⟩

/-- Reference decoder obtained by checking every position-subset interpolation and deduplicating. -/
def run (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : List (List F) :=
  ((samples n k).filterMap (checkedCandidate domain received k A)).dedup

private theorem mem_run_iff (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (cs : List F) :
    cs ∈ run domain received k A ↔
      ∃ sample : Finset (Fin n), sample.card = k ∧
        checkedCandidate domain received k A sample = some cs := by
  simp [run, mem_samples_iff]

private theorem exists_mem_run_polynomial (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (P : F[X]) (hdegree : P.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain P) received) :
    ∃ cs ∈ run domain received k A, coefficientPolynomial cs = P := by
  have hcardAgreement : A ≤ (polynomialAgreementSet domain received P).card := by
    change A ≤ ({i : Fin n | P.eval (domain i) = received i} : Finset (Fin n)).card at hagreement
    change A ≤ ({i : Fin n | P.eval (domain i) = received i} : Finset (Fin n)).card
    exact hagreement
  obtain ⟨sample, hsample, hcard⟩ :=
    Finset.exists_subset_card_eq (hAk.trans hcardAgreement)
  have hinterpolation : Lagrange.interpolate sample domain received = P :=
    interpolate_eq_of_agrees_on domain received k sample hcard P hdegree hsample
  have hcandidate : coefficientPolynomial (sampleCandidate domain received k sample) = P :=
    (sampleCandidate_polynomial domain received k sample).trans hinterpolation
  have hcandidateAgreement :
      A ≤ Code.agree
        (evalOnPoints domain
          (coefficientPolynomial (sampleCandidate domain received k sample))) received := by
    rwa [hcandidate]
  have hchecked := checkedCandidate_of_agreement domain received k A sample hcard
    hcandidateAgreement
  exact ⟨sampleCandidate domain received k sample,
    (mem_run_iff domain received k A _).mpr ⟨sample, hcard, hchecked⟩, hcandidate⟩

/-- The actual position-subset decoder returns exactly the duplicate-free fixed-width agreement
list whenever the threshold supplies at least `k` agreeing positions per wanted message. -/
theorem run_exact (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A) :
    ExactOutput domain received k A (run domain received k A) := by
  apply exactOutput_of_sound_complete domain received k A _ (List.nodup_dedup _)
  · intro cs hcs
    rcases (mem_run_iff domain received k A cs).mp hcs with ⟨sample, hcard, hchecked⟩
    have hp := checkedCandidate_properties domain received k A sample hcard cs hchecked
    exact ⟨hp.1, hp.2.2⟩
  · exact exists_mem_run_polynomial domain received k A hAk

end ReedSolomon.ListDecoding.PositionSubsetDecoder
