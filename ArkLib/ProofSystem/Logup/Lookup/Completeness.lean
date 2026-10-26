/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Prover
public import ArkLib.ProofSystem.Logup.Prover.Completeness

/-!
# Completeness of actual indexed scalar lookup

The actual initial multiplicity sender is the computed natural histogram. Valid indices give
mapped balance through the existing characteristic-independent histogram theorem. The scalar
sender-bind law then invokes the unchanged complete weighted endpoint and its actual source law.

Query membership in the declared collection identifies the weighted mapped value support with
only the declared physical table support, independent of multiplicities. Its finite image is
computable with explicit equality, but the verifier never calls or scans it. This sharpens honest
pole loss to the table support, bounded by P times the Boolean row count. No retry is introduced.

These are correctness/completeness results for an explicit message implementation. The final
measured default and the complete work/storage ledger are separate consumer obligations.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators ENNReal ProbabilityTheory
namespace Logup.Lookup.Honest

/-- Finite mapped support of all declared physical table pieces, used only in analysis. -/
def tableSupport {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n M P : Nat}
    (f : B →+* E) (data : Logup.Lookup.Data B n M P) : Finset E :=
  ((Finset.univ : Finset (Fin P)).product (Finset.univ : Finset (Fin (2 ^ n)))).image
    (fun p => f ((data (.inr p.1)).get p.2))

/-- Membership means one actual declared table entry maps to the scalar. -/
theorem mem_tableSupport {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P : Nat} (f : B →+* E) (data : Logup.Lookup.Data B n M P) (alpha : E) :
    alpha ∈ tableSupport f data ↔ ∃ p u, f ((data (.inr p)).get u) = alpha := by
  rw [tableSupport, Finset.mem_image]
  constructor
  · rintro ⟨⟨p, u⟩, _, h⟩
    exact ⟨p, u, h⟩
  · rintro ⟨p, u, h⟩
    exact ⟨(p, u), by simp, h⟩

/-- There are at most P times the Boolean row count distinct mapped table values. -/
theorem card_tableSupport_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P : Nat} (f : B →+* E) (data : Logup.Lookup.Data B n M P) :
    (tableSupport f data).card ≤ P * 2 ^ n := by
  apply Finset.card_image_le.trans
  simp

/-- Lookup membership makes the signed collection support exactly the declared-table support.
This identity is independent of the supplied multiplicities. -/
theorem valueSupport_weighted_eq_tableSupport
    {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P : Nat} (f : B →+* E) (data : Logup.Lookup.Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (hlookup : InLanguage data) :
    Logup.Prover.Honest.valueSupport f (weightedData data mu) = tableSupport f data := by
  ext alpha
  rw [Logup.Prover.Honest.mem_valueSupport, mem_tableSupport]
  constructor
  · rintro ⟨i, u, h⟩
    simp only [weightedData_value] at h
    cases hkeyeq : finSumFinEquiv.symm i with
    | inl q =>
      obtain ⟨p, row, heq⟩ := hlookup q u
      refine ⟨p, row, ?_⟩
      rw [hkeyeq] at h
      exact (congrArg f heq).symm.trans h
    | inr p =>
      exact ⟨p, u, by simpa only [hkeyeq] using h⟩
  · rintro ⟨p, u, h⟩
    refine ⟨Fin.natAdd M p, u, ?_⟩
    simpa only [weightedData_value, finSumFinEquiv_symm_apply_natAdd] using h

/-- The actual histogram sender reduces the complete scalar endpoint
to its weighted continuation. -/
theorem execute_proverWith_eq {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) :
    execute f n M P ell cfg ambient alphaDraw jointDraw roundDraw A valuesView impl
      (proverWith f cfg data indices ambient build) =
    Logup.Interaction.execute f n (M + P) ell cfg.weighted ambient alphaDraw jointDraw roundDraw
      (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
      (Access.extendImpl A (multiplicityInterface f n P) impl (multiplicities indices))
      (Logup.Prover.Honest.honestWith f cfg.weighted
        (weightedData data (multiplicities indices)) ambient build) := by
  rw [execute_eq_sender_bind]
  rfl


/-- The named scalar sampler endpoint delegates to the same weighted uniform endpoint. -/
theorem uniformExecute_proverWith_eq
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) :
    uniformExecute f n M P ell cfg A valuesView impl
      (proverWith f cfg data indices unifSpec build) =
    Logup.Interaction.uniformExecute f n (M + P) ell cfg.weighted
      (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
      (Access.extendImpl A (multiplicityInterface f n P) impl (multiplicities indices))
      (Logup.Prover.Honest.honestWith f cfg.weighted
        (weightedData data (multiplicities indices)) unifSpec build) := by
  rw [uniformExecute, execute_proverWith_eq]
  rfl

/-- The actual scalar honest endpoint fails with at most the mapped table pole fraction. -/
theorem uniformExecute_proverWith_failure_le
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (hvalid : ValidIndices data indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data) :
    Pr{let accepted ← (uniformExecute f n M P ell cfg A valuesView impl
      (proverWith f cfg data indices unifSpec build))}[accepted = false] ≤
      ((tableSupport f data).card : ℝ≥0∞) / Fintype.card E := by
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  have hlookup : InLanguage data :=
    (inLanguage_iff_exists_validIndices data).mpr ⟨indices, hvalid⟩
  rw [uniformExecute_proverWith_eq]
  have h := Logup.Prover.Honest.uniformExecute_honestWith_failure_le f cfg.weighted
    (weightedData data mu) build hbuild
    (mapped_weighted_fiber_multiplicities_eq_zero f data indices hvalid)
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
    (Access.extendImpl A (multiplicityInterface f n P) impl mu)
    (weightedView_realizes f n M P A valuesView impl data hinput mu)
  rw [valueSupport_weighted_eq_tableSupport f data mu hlookup] at h
  exact h

/-- The actual scalar honest endpoint succeeds with at least one minus its table pole fraction. -/
theorem uniformExecute_proverWith_success_ge
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (hvalid : ValidIndices data indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data) :
    1 - ((tableSupport f data).card : ℝ≥0∞) / Fintype.card E ≤
      Pr{let accepted ← (uniformExecute f n M P ell cfg A valuesView impl
        (proverWith f cfg data indices unifSpec build))}[accepted = true] := by
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  have hlookup : InLanguage data :=
    (inLanguage_iff_exists_validIndices data).mpr ⟨indices, hvalid⟩
  rw [uniformExecute_proverWith_eq]
  have h := Logup.Prover.Honest.uniformExecute_honestWith_success_ge f cfg.weighted
    (weightedData data mu) build hbuild
    (mapped_weighted_fiber_multiplicities_eq_zero f data indices hvalid)
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
    (Access.extendImpl A (multiplicityInterface f n P) impl mu)
    (weightedView_realizes f n M P A valuesView impl data hinput mu)
  rw [valueSupport_weighted_eq_tableSupport f data mu hlookup] at h
  exact h

/-- Total probability is preserved, including public abort returning false. -/
theorem uniformExecute_proverWith_total
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) :
    Pr{let _ ← (uniformExecute f n M P ell cfg A valuesView impl
      (proverWith f cfg data indices unifSpec build))}[True] = 1 :=
  OracleComp.prEvent_true_eq_one _


/-- Every supported scalar honest execution accepts when alpha avoids the declared table support. -/
theorem execute_proverWith_support_completeness
    {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (hvalid : ValidIndices data indices)
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (alphaDraw : OracleComp ambient E)
    (hoff : ∀ alpha ∈ support alphaDraw, alpha ∉ tableSupport f data)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data) :
    ∀ accepted ∈ support
      (execute f n M P ell cfg ambient alphaDraw jointDraw roundDraw A valuesView impl
        (proverWith f cfg data indices ambient build)), accepted = true := by
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  have hlookup : InLanguage data :=
    (inLanguage_iff_exists_validIndices data).mpr ⟨indices, hvalid⟩
  rw [execute_proverWith_eq]
  apply Logup.Prover.Honest.execute_honestWith_support_completeness f cfg.weighted
    (weightedData data mu) build hbuild
    (mapped_weighted_fiber_multiplicities_eq_zero f data indices hvalid)
    ambient alphaDraw _ jointDraw roundDraw
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
    (Access.extendImpl A (multiplicityInterface f n P) impl mu)
    (weightedView_realizes f n M P A valuesView impl data hinput mu)
  intro alpha halpha
  apply (Logup.Prover.Honest.offPole_iff_not_mem_valueSupport f (weightedData data mu) alpha).mpr
  rw [valueSupport_weighted_eq_tableSupport f data mu hlookup]
  exact hoff alpha halpha

/-- The scalar honest failure probability is at most the declared table row count
over field size. -/
theorem uniformExecute_proverWith_failure_le_rows
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (hvalid : ValidIndices data indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data) :
    Pr{let accepted ← (uniformExecute f n M P ell cfg A valuesView impl
      (proverWith f cfg data indices unifSpec build))}[accepted = false] ≤
      ((P * 2 ^ n : Nat) : ℝ≥0∞) / Fintype.card E := by
  apply (uniformExecute_proverWith_failure_le f cfg data indices hvalid build hbuild
    A valuesView impl hinput).trans
  exact ENNReal.div_le_div_right (by exact_mod_cast card_tableSupport_le f data) _

/-- The scalar honest success probability is at least one minus that table row fraction. -/
theorem uniformExecute_proverWith_success_ge_rows
    {B E : Type} [CommRing B] [Field E] [DecidableEq E] [Fintype E] [SampleableType E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (hvalid : ValidIndices data indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data) :
    1 - ((P * 2 ^ n : Nat) : ℝ≥0∞) / Fintype.card E ≤
      Pr{let accepted ← (uniformExecute f n M P ell cfg A valuesView impl
        (proverWith f cfg data indices unifSpec build))}[accepted = true] := by
  have hbound : ((tableSupport f data).card : ℝ≥0∞) / Fintype.card E ≤
      ((P * 2 ^ n : Nat) : ℝ≥0∞) / Fintype.card E :=
    ENNReal.div_le_div_right (by exact_mod_cast card_tableSupport_le f data) _
  exact (tsub_le_tsub_left hbound 1).trans
    (uniformExecute_proverWith_success_ge f cfg data indices hvalid build hbuild
      A valuesView impl hinput)

end Logup.Lookup.Honest
