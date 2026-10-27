/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Protocol
public import ArkLib.ProofSystem.Logup.Security.Soundness

/-!
# Whole-program soundness of scalar lookup

For every actual initial multiplicity message, false lookup membership gives a nonzero mapped
weighted fiber under the certified query-count budget. The actual sender-bind law then applies
the weighted soundness theorem to each retained message and continuation. Subprobability
averaging preserves the bound without assuming malicious losslessness or restricting private
sender effects and path-dependent output. No table-size characteristic bound is required.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped ProbabilityTheory ENNReal

namespace Logup.Lookup

variable {B E : Type} [Field B] [Field E] [Fintype E] [DecidableEq E]
  [SampleableType E] [BEq E] [LawfulBEq E]

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary whole prover satisfies the scalar error bound on a false declared lookup. -/
theorem uniformExecute_soundness (f : B →+* E) (n M P ell : ℕ)
    (cfg : Config B n M P ell) (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) (data : Data B n M P)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) (hfalse : ¬ InLanguage data) :
    Pr{let accepted ←
      uniformExecute f n M P ell cfg A valuesView impl prover}[accepted = true] ≤
      (((M + P) * 2 ^ n + n * (ell + 3) : Nat) : ℝ≥0∞) / Fintype.card E := by
  have : CharP B cfg.characteristic := cfg.charP
  rw [uniformExecute, execute_eq_sender_bind]
  apply prEvent_bind_le_of_forall_le
  intro sent
  exact Logup.Interaction.uniformExecute_soundness f n (M + P) ell cfg.weighted
    (Access.extend A (multiplicityInterface f n P)) (weightedView f n M P A valuesView)
    (Access.extendImpl A (multiplicityInterface f n P) impl sent.1) (weightedData data sent.1)
    (weightedView_realizes f n M P A valuesView impl data hinput sent.1)
    (OutP := fun path => OutP ⟨sent.1, path⟩) sent.2
    (exists_mapped_weighted_fiber_ne_zero f cfg.characteristic data sent.1 cfg.queryBudget hfalse)

end Logup.Lookup
