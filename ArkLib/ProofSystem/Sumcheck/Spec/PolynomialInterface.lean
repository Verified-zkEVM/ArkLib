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

namespace Sumcheck.Spec

open _root_.Interaction.Oracle

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The multivariate polynomial oracle with evaluation queries. The original polynomial remains
available at every round boundary.

It is noncomputable because the legacy evaluation interface of multivariate polynomials is. A
verifier that uses only its types stays executable. -/
noncomputable def polynomialFamily : OracleFamily Unit (OracleStatement R n deg) :=
  ⟨fun _ => inferInstance⟩

end Sumcheck.Spec

namespace Sumcheck.Interaction.MultivariateRound

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The former name of `Sumcheck.Spec.polynomialFamily`, kept for the frozen interaction layer
and `scripts/SumcheckRuntime.lean`. Remove this alias when the frozen interaction layer
and its runtime callers are migrated. -/
noncomputable abbrev polynomialFamily := Spec.polynomialFamily R n deg

end Sumcheck.Interaction.MultivariateRound
