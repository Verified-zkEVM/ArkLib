/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude

/-!
# Functional commitment compatibility

Knowledge arguments require the committed polynomial to be determined before the verifier's
challenge. This is a separate property of a compatibility relation, not a field imposed on every
oracle interface: `AbstractOStmtIn.Functional` says that an oracle statement is compatible with at
most one packed polynomial. Without it, a prover may choose the packed polynomial after the
batching challenge, and the batching and sum-check errors do not bound extraction. Honest-input
compatibility inherits the property from the relaxed relation
(`AbstractOStmtIn.Functional.strictView`).
-/

@[expose] public section

namespace RingSwitching

variable {L : Type} [CommRing L] {ℓ : ℕ}

/-- One oracle statement is compatible with at most one polynomial. -/
def AbstractOStmtIn.Functional (a : AbstractOStmtIn L ℓ) : Prop :=
  ∀ o t₁ t₂, a.initialCompatibility (t₁, o) →
    a.initialCompatibility (t₂, o) → t₁ = t₂

/-- Restricting compatibility to honest inputs preserves uniqueness. -/
theorem AbstractOStmtIn.Functional.strictView {a : AbstractOStmtIn L ℓ}
    (h : a.Functional) : a.strictView.Functional := by
  intro o t₁ t₂ h₁ h₂
  exact h o t₁ t₂
    (a.strictInitialCompatibility_implies_initialCompatibility o t₁ h₁)
    (a.strictInitialCompatibility_implies_initialCompatibility o t₂ h₂)

end RingSwitching
