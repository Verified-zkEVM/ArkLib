/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Protocol

/-!
# Exact execution of the tuple lookup prefix

The actual base multiplicity sender runs before the public beta draw and the prover's effectful
beta response. This equality preserves all ambient effects, aborts and path-dependent private
output while exposing the unchanged weighted verifier over the same retained original source.
No continuation kernel or execution-equality premise is supplied by the caller.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly

namespace Logup.Lookup.Tuple

variable {B E : Type} [CommRing B] [CommRing E]
variable (f : B →+* E) (n M P W ell : Nat) (cfg : Logup.Lookup.Config B n M P ell)
variable {ι : Type} (ambient : OracleSpec ι) [DecidableEq E]

set_option backward.isDefEq.respectTransparency false in
/-- The actual base sender and beta response retain their private effects and dependent outputs.
The same received multiplicity realization closes the complete weighted suffix's source. -/
theorem execute_eq_sender_beta_bind (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) :
    execute f n M P W ell cfg ambient betaDraw alphaDraw jointDraw roundDraw
      A coeffView impl prover =
      (do
        let sent ← prover
        let beta ← betaDraw
        let continuation ← sent.2 beta
        Logup.Interaction.execute (RingHom.id E) n (M + P) ell cfg.weighted ambient
          alphaDraw jointDraw roundDraw (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
          (weightedView f n M P W beta A coeffView)
          (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl sent.1)
          (OutP := fun path => OutP ⟨sent.1, ⟨beta, path⟩⟩) continuation) := by
  have lift_eq (access : PFunctor) (handler : QueryImpl (ofPFunctor access) Id)
      {X : Type} (program : OracleComp ambient X) :
      simulateQ (Verifier.liftAccessImpl ambient access handler)
        (OracleComp.liftComp program (ambient + ofPFunctor access)) = program := by
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply
      (impl₁ := QueryImpl.id' ambient) (h := fun _ => rfl), simulateQ_id']
  unfold execute
  simp only [protocol, Protocol.oracleWith, Protocol.public]
  rw [executeStrategies_oracle]
  simp only [verifier, simulateQ_pure, bind_assoc, pure_bind]
  congr 1
  funext sent
  rw [executeStrategies_public_receiver]
  simp only [simulateQ_bind, simulateQ_pure, lift_eq, bind_assoc, pure_bind]
  rfl

end Logup.Lookup.Tuple
