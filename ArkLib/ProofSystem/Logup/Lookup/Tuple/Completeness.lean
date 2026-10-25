/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Prover
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Execution
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Initial
public import ArkLib.ProofSystem.Logup.Lookup.Completeness

/-!
# Completeness of the actual indexed tuple prover

Valid semantic indices remain valid after every fingerprint, including collisions. The honest
base histogram therefore balances the compressed weighted tables for every beta. The actual
sender/beta bind delegates to the unchanged complete weighted prover over the genuine coefficient
source and the retained multiplicity message.

For each beta, all compressed query values occur in the declared table collection. Its existing
finite table support bounds honest alpha-pole loss by the number of declared table rows. Averaging
over beta adds no compression loss, union bound or retry. The uniform endpoint retains mass1,
including aborts returning false. The reference data depend only on beta and the fixed input;
weighted initialization materializes each value column after alpha and caches its denominators.

The round builder is explicit. A later measured default must account separately for tuple
compression and data construction; output correctness does not transfer E-core resource profiles.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators ENNReal ProbabilityTheory
namespace Logup.Lookup.Tuple.Honest

section Compression

variable {B E : Type} [CommRing B] [CommRing E]
variable {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

/-- The same semantic witness indices remain valid after every fingerprint, including collisions. -/
theorem validIndices_fingerprintData (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices prepared.keyData indices) :
    ValidIndices (prepared.fingerprintData f beta) indices := by
  intro i
  have h := congrArg (schema.fingerprint f beta) (hvalid i)
  simpa only [columnEntries, PreparedProvider.fingerprintData, Vector.get_eq_getElem,
    Vector.getElem_ofFn, Vector.getElem_map] using h

end Compression

variable {B E : Type} [CommRing B] [Field E]
variable {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

variable [DecidableEq E]

/-- The actual histogram sender and pure beta response leave the unchanged weighted endpoint. -/
theorem execute_proverWith_eq (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) :
    execute f n M P W ell cfg ambient betaDraw alphaDraw jointDraw roundDraw A view impl
      (proverWith f cfg prepared indices ambient build) =
    (do
      let beta ← betaDraw
      Logup.Interaction.execute (RingHom.id E) n (M + P) ell cfg.weighted ambient
        alphaDraw jointDraw roundDraw (Access.extend A (multiplicityInterface f n P))
        (weightedView f n M P W beta A view)
        (Access.extendImpl A (multiplicityInterface f n P) impl (multiplicities indices))
        (Logup.Prover.Honest.honestWith (RingHom.id E) cfg.weighted
          (prepared.weightedData f beta (multiplicities indices)) ambient build)) := by
  rw [execute_eq_sender_beta_bind]
  rfl


/-- Semantic membership makes weighted compressed support equal compressed table support. -/
theorem valueSupport_weighted_eq_tableSupport (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (mu : Vector (CMlPolynomialEval B n) P)
    (hlookup : InLanguage prepared.keyData) :
    Logup.Prover.Honest.valueSupport (RingHom.id E) (prepared.weightedData f beta mu) =
      Logup.Lookup.Honest.tableSupport (RingHom.id E) (prepared.fingerprintData f beta) := by
  apply Logup.Lookup.Honest.valueSupport_weighted_eq_tableSupport
  intro q row
  obtain ⟨piece, tableRow, heq⟩ := hlookup q row
  refine ⟨piece, tableRow, ?_⟩
  simpa only [PreparedProvider.fingerprintData, Vector.get_eq_getElem, Vector.getElem_map] using
    congrArg (schema.fingerprint f beta) heq

/-- The named uniform endpoint samples beta before the unchanged weighted uniform endpoint. -/
theorem uniformExecute_proverWith_eq [SampleableType E]
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) :
    uniformExecute f n M P W ell cfg A view impl
      (proverWith f cfg prepared indices unifSpec build) =
    (do
      let beta ← $ᵗ E
      Logup.Interaction.uniformExecute (RingHom.id E) n (M + P) ell cfg.weighted
        (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P W beta A view)
        (Access.extendImpl A (multiplicityInterface f n P) impl (multiplicities indices))
        (Logup.Prover.Honest.honestWith (RingHom.id E) cfg.weighted
          (prepared.weightedData f beta (multiplicities indices)) unifSpec build)) := by
  rw [uniformExecute, execute_proverWith_eq]
  rfl

/-- Every supported honest execution accepts when alpha avoids the compressed table support
for every supported beta; joint and native draw programs remain arbitrary. -/
theorem execute_proverWith_support_completeness
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices prepared.keyData indices)
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (betaDraw alphaDraw : OracleComp ambient E)
    (hoff : ∀ beta ∈ support betaDraw, ∀ alpha ∈ support alphaDraw,
      alpha ∉ Logup.Lookup.Honest.tableSupport (RingHom.id E) (prepared.fingerprintData f beta))
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2)) :
    ∀ accepted ∈ support
      (execute f n M P W ell cfg ambient betaDraw alphaDraw jointDraw roundDraw A view impl
        (proverWith f cfg prepared indices ambient build)), accepted = true := by
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  have hlookup : InLanguage prepared.keyData :=
    (inLanguage_iff_exists_validIndices prepared.keyData).mpr ⟨indices, hvalid⟩
  rw [execute_proverWith_eq]
  intro accepted haccepted
  obtain ⟨beta, hbeta, haccepted⟩ := support_bind_exists haccepted
  apply Logup.Prover.Honest.execute_honestWith_support_completeness (RingHom.id E) cfg.weighted
    (prepared.weightedData f beta mu) build hbuild
    (fun encoded => by simpa only [RingHom.id_apply] using
      prepared.weighted_fiber_multiplicities_eq_zero f indices hvalid beta encoded)
    ambient alphaDraw _ jointDraw roundDraw
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P W beta A view)
    (Access.extendImpl A (multiplicityInterface f n P) impl mu)
    (weightedView_realizes prepared f beta A view impl hinput mu) accepted haccepted
  intro alpha halpha
  apply (Logup.Prover.Honest.offPole_iff_not_mem_valueSupport (RingHom.id E)
    (prepared.weightedData f beta mu) alpha).mpr
  rw [valueSupport_weighted_eq_tableSupport prepared f beta mu hlookup]
  exact hoff beta hbeta alpha halpha


/-- The actual honest tuple endpoint fails with at most the declared table row fraction.
Fingerprint collisions introduce no additional completeness loss. -/
theorem uniformExecute_proverWith_failure_le_rows [Fintype E] [SampleableType E]
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices prepared.keyData indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2)) :
    Pr{let accepted ← (uniformExecute f n M P W ell cfg A view impl
      (proverWith f cfg prepared indices unifSpec build))}[accepted = false] ≤
      ((P * 2 ^ n : Nat) : ℝ≥0∞) / Fintype.card E := by
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  have hlookup : InLanguage prepared.keyData :=
    (inLanguage_iff_exists_validIndices prepared.keyData).mpr ⟨indices, hvalid⟩
  rw [uniformExecute_proverWith_eq]
  apply prEvent_bind_le_of_forall_le
  intro beta
  have h := Logup.Prover.Honest.uniformExecute_honestWith_failure_le (RingHom.id E) cfg.weighted
    (prepared.weightedData f beta mu) build hbuild
    (fun encoded => by simpa only [RingHom.id_apply] using
      prepared.weighted_fiber_multiplicities_eq_zero f indices hvalid beta encoded)
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P W beta A view)
    (Access.extendImpl A (multiplicityInterface f n P) impl mu)
    (weightedView_realizes prepared f beta A view impl hinput mu)
  rw [valueSupport_weighted_eq_tableSupport prepared f beta mu hlookup] at h
  apply h.trans
  exact ENNReal.div_le_div_right
    (by exact_mod_cast (Logup.Lookup.Honest.card_tableSupport_le (RingHom.id E)
      (prepared.fingerprintData f beta))) _

/-- The actual honest tuple endpoint succeeds with at least one minus the table row fraction. -/
theorem uniformExecute_proverWith_success_ge_rows [Fintype E] [SampleableType E]
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices prepared.keyData indices)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (hbuild : Logup.Prover.Honest.HeadMessageCorrect cfg.weighted.groups build)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2)) :
    1 - ((P * 2 ^ n : Nat) : ℝ≥0∞) / Fintype.card E ≤
      Pr{let accepted ← (uniformExecute f n M P W ell cfg A view impl
        (proverWith f cfg prepared indices unifSpec build))}[accepted = true] := by
  let program := uniformExecute f n M P W ell cfg A view impl
    (proverWith f cfg prepared indices unifSpec build)
  have hfail := uniformExecute_proverWith_failure_le_rows f cfg prepared indices hvalid
    build hbuild A view impl hinput
  have htotal : Pr{let accepted ← program}[accepted = true] =
      1 - Pr{let accepted ← program}[accepted = false] := by
    convert OracleComp.prEvent_not_eq_one_sub program (fun accepted => accepted = false) using 1
    apply prEvent_congr
    intro accepted
    cases accepted <;> simp
  rw [htotal]
  exact tsub_le_tsub_left hfail 1

/-- Total probability is preserved, including public abort returning false. -/
theorem uniformExecute_proverWith_total [SampleableType E]
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) :
    Pr{let _ ← (uniformExecute f n M P W ell cfg A view impl
      (proverWith f cfg prepared indices unifSpec build))}[True] = 1 :=
  OracleComp.prEvent_true_eq_one _

end Logup.Lookup.Tuple.Honest
