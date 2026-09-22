/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Finset.Preimage

/-!
# Exact finite enumerations and candidate filtering

This file packages a general pattern for finite, duplicate-free enumeration.  An exact
enumerator returns precisely the outputs satisfying a predicate.  A possibly larger finite set
of ambient candidates can be pulled back along an embedding and filtered by that predicate;
completeness for the embedded accepted outputs then makes the filtered enumeration exact.

The construction is independent of codes, fields, polynomials, and decoding.  Those applications
only have to supply the input type, output predicate, and embedding into their ambient candidate
type.
-/

@[expose] public section

namespace Finset

noncomputable section

/-- A finite, duplicate-free enumeration depending on an input. -/
abbrev Enumeration (Input Output : Type*) := Input → Finset Output

/-- An enumeration is exact when membership is equivalent to the target predicate. -/
def IsExactEnumeration {Input Output : Type*} [DecidableEq Output]
    (accepts : Input → Output → Prop) (enumerate : Enumeration Input Output) : Prop :=
  ∀ input output, output ∈ enumerate input ↔ accepts input output

/-- An exact enumeration together with a uniform bound on its output size. -/
structure EnumerationCertificate {Input Output : Type*} [DecidableEq Output]
    (accepts : Input → Output → Prop) (bound : ℕ) where
  /-- The certified enumeration. -/
  enumerate : Enumeration Input Output
  /-- Soundness and completeness of the enumeration. -/
  isExact : IsExactEnumeration accepts enumerate
  /-- Uniform output-cardinality bound. -/
  card_le : ∀ input, (enumerate input).card ≤ bound

/-- A finite ambient candidate generator containing every embedded accepted output. -/
structure CandidateCertificate {Input Output Ambient : Type*}
    [DecidableEq Output] [DecidableEq Ambient]
    (embed : Output ↪ Ambient) (accepts : Input → Output → Prop) (bound : ℕ) where
  /-- The ambient candidates generated for each input. -/
  candidates : Input → Finset Ambient
  /-- Every accepted output appears through its embedding. -/
  complete : ∀ input output, accepts input output → embed output ∈ candidates input
  /-- Uniform ambient-candidate bound. -/
  card_le : ∀ input, (candidates input).card ≤ bound

open Classical in
/-- Pull ambient candidates back along an embedding and retain exactly the accepted outputs. -/
def filterCandidates {Input Output Ambient : Type*}
    [DecidableEq Output] [DecidableEq Ambient]
    (embed : Output ↪ Ambient) (accepts : Input → Output → Prop)
    (candidates : Input → Finset Ambient) : Enumeration Input Output := fun input =>
  ((candidates input).preimage embed embed.injective.injOn).filter (accepts input)

/-- Membership in a filtered candidate enumeration separates into ambient membership and the
target predicate. -/
theorem mem_filterCandidates {Input Output Ambient : Type*}
    [DecidableEq Output] [DecidableEq Ambient]
    (embed : Output ↪ Ambient) (accepts : Input → Output → Prop)
    (candidates : Input → Finset Ambient) (input : Input) (output : Output) :
    output ∈ filterCandidates embed accepts candidates input ↔
      embed output ∈ candidates input ∧ accepts input output := by
  classical
  simp [filterCandidates]

/-- Pullback and filtering cannot increase the ambient candidate-set cardinality. -/
theorem card_filterCandidates_le {Input Output Ambient : Type*}
    [DecidableEq Output] [DecidableEq Ambient]
    (embed : Output ↪ Ambient) (accepts : Input → Output → Prop)
    (candidates : Input → Finset Ambient) (input : Input) :
    (filterCandidates embed accepts candidates input).card ≤ (candidates input).card := by
  classical
  unfold filterCandidates
  calc
    (((candidates input).preimage embed embed.injective.injOn).filter
        (accepts input)).card ≤
        ((candidates input).preimage embed embed.injective.injOn).card :=
      Finset.card_filter_le _ _
    _ ≤ (candidates input).card := by
      apply Finset.card_le_card_of_injOn embed
      · intro output houtput
        exact Finset.mem_preimage.mp houtput
      · exact embed.injective.injOn

/-- Filtering a complete ambient candidate generator is exact. -/
theorem CandidateCertificate.isExact_filterCandidates
    {Input Output Ambient : Type*} [DecidableEq Output] [DecidableEq Ambient]
    {embed : Output ↪ Ambient} {accepts : Input → Output → Prop} {bound : ℕ}
    (certificate : CandidateCertificate embed accepts bound) :
    IsExactEnumeration accepts
      (filterCandidates embed accepts certificate.candidates) := by
  intro input output
  rw [mem_filterCandidates]
  exact and_iff_right_of_imp (certificate.complete input output)

/-- Package filtered ambient candidates as an exact bounded enumeration. -/
def CandidateCertificate.toEnumerationCertificate
    {Input Output Ambient : Type*} [DecidableEq Output] [DecidableEq Ambient]
    {embed : Output ↪ Ambient} {accepts : Input → Output → Prop} {bound : ℕ}
    (certificate : CandidateCertificate embed accepts bound) :
    EnumerationCertificate accepts bound where
  enumerate := filterCandidates embed accepts certificate.candidates
  isExact := certificate.isExact_filterCandidates
  card_le := fun input =>
    (card_filterCandidates_le embed accepts certificate.candidates input).trans
      (certificate.card_le input)

/-- Every enumerated output satisfies the target predicate. -/
theorem EnumerationCertificate.accepts_of_mem
    {Input Output : Type*} [DecidableEq Output]
    {accepts : Input → Output → Prop} {bound : ℕ}
    (certificate : EnumerationCertificate accepts bound)
    {input : Input} {output : Output} (houtput : output ∈ certificate.enumerate input) :
    accepts input output :=
  (certificate.isExact input output).mp houtput

/-- Every accepted output is enumerated. -/
theorem EnumerationCertificate.mem_of_accepts
    {Input Output : Type*} [DecidableEq Output]
    {accepts : Input → Output → Prop} {bound : ℕ}
    (certificate : EnumerationCertificate accepts bound)
    {input : Input} {output : Output} (houtput : accepts input output) :
    output ∈ certificate.enumerate input :=
  (certificate.isExact input output).mpr houtput

/-- If no output is accepted at an input, an exact enumeration is empty there. -/
theorem IsExactEnumeration.eq_empty_of_forall_not
    {Input Output : Type*} [DecidableEq Output]
    {accepts : Input → Output → Prop} {enumerate : Enumeration Input Output}
    (hExact : IsExactEnumeration accepts enumerate) (input : Input)
    (hnone : ∀ output, ¬ accepts input output) : enumerate input = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro output houtput
  exact hnone output ((hExact input output).mp houtput)

end

end Finset
