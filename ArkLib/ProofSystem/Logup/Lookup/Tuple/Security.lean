/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Execution
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.CompressionSoundness
public import ArkLib.ProofSystem.Logup.Security.Soundness

/-!
# Whole-program soundness of tuple lookup

The actual base multiplicity message is retained before beta. For each such fixed message, the
selected-key compression bound charges only `(s - 1) * W / |E|`, where s counts the original
semantic keys across queries and all declared pieces. Outside compressed balance, the existing
weighted verifier over the actual coefficient source incurs the scalar/native error bound.

The proof follows the real sender and beta-response binds, preserving arbitrary private effects,
missing mass and path-dependent output. It assumes genuine stored coefficient realization and
false original semantic membership, rather than an assumed message kernel or helper honesty.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped ProbabilityTheory ENNReal
namespace Logup.Lookup.Tuple

variable {B E : Type} [Field B] [Field E] [Fintype E] [DecidableEq B] [DecidableEq E]
  [SampleableType E] [BEq E] [LawfulBEq E]

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary whole tuple prover obeys the selected-compression plus weighted error bound. -/
theorem uniformExecute_soundness (f : B →+* E) (n M P W ell : Nat)
    (cfg : Logup.Lookup.Config B n M P ell) {b : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : coeffView.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2))
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) (hfalse : ¬ InLanguage prepared.keyData) :
    Pr{let accepted ← uniformExecute f n M P W ell cfg A coeffView impl prover}[accepted = true] ≤
      (((prepared.occurringKeys.card - 1) * W + (M + P) * 2 ^ n + n * (ell + 3) : Nat) :
        ℝ≥0∞) / Fintype.card E := by
  classical
  have : CharP B cfg.characteristic := cfg.charP
  rw [uniformExecute, execute_eq_sender_beta_bind]
  apply prEvent_bind_le_of_forall_le
  intro sent
  refine (prEvent_bind_le_prEvent_add _ _
    (fun beta => ∀ encoded,
      ((Finset.univ : Finset (Fin n → Fin 2)).product
        (Finset.univ : Finset (Fin (M + P)))).sumFiber
        (fun i => (prepared.weightedData f beta sent.1 (0, i.2)).get (finFunctionFinEquiv i.1))
        (fun i => (prepared.weightedData f beta sent.1 (1, i.2)).get (finFunctionFinEquiv i.1))
        encoded = 0)
    (fun accepted => accepted = true)
    (ε := (((M + P) * 2 ^ n + n * (ell + 3) : Nat) : ℝ≥0∞) / Fintype.card E) ?_).trans ?_
  · intro beta hgood
    apply prEvent_bind_le_of_forall_le (sent.2 beta)
    intro continuation
    apply Logup.Interaction.uniformExecute_soundness (RingHom.id E) n (M + P) ell cfg.weighted
      (Access.extend A (multiplicityInterface f n P))
      (weightedView f n M P W beta A coeffView)
      (Access.extendImpl A (multiplicityInterface f n P) impl sent.1)
      (prepared.weightedData f beta sent.1)
      (weightedView_realizes prepared f beta A coeffView impl hinput sent.1)
      (OutP := fun path => OutP ⟨sent.1, ⟨beta, path⟩⟩) continuation
    push Not at hgood
    simpa only [RingHom.id_apply] using hgood
  · simpa only [Nat.cast_add, ENNReal.add_div, add_assoc] using
      add_le_add (prob_weightedData_balanced_le prepared f cfg.characteristic sent.1
        cfg.queryBudget hfalse) (le_refl
          ((((M + P) * 2 ^ n + n * (ell + 3) : Nat) : ℝ≥0∞) / Fintype.card E))
end Logup.Lookup.Tuple
