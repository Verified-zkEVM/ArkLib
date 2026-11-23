/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Relation.Basic
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Multivariate sum-check oracle interface

The bounded multivariate polynomial is exposed through evaluation queries. The same interface
is used by the specification and by the computational polynomial handler.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open _root_.Interaction.Oracle

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The original multivariate polynomial remains available at every round boundary. -/
noncomputable def polynomialFamily : OracleFamily Unit (Spec.OracleStatement R n deg) :=
  ⟨fun _ => inferInstance⟩

end Sumcheck.Interaction.MultivariateRound
