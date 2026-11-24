/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.PolynomialInterface

/-! # Compatibility of projected round oracles with the Sumcheck specification -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
variable (R : Type) [CommSemiring R] (deg : ℕ)

/-! ## The projection map -/

section Projection

variable (n : ℕ) {d : ℕ} (D : Fin d ↪ R)

/-- The univariate round polynomial with evaluation queries. -/
noncomputable def messageFamily : OracleFamily Unit (Spec.SingleRound.Simple.OStmtIn R deg) :=
  ⟨fun _ => inferInstance⟩

/-- The projection of the multivariate input to the univariate polynomial of round `i`: the sum of
the input over the remaining domain, with the earlier variables fixed to the statement's
challenges. A univariate evaluation query makes one multivariate query per remaining point. -/
noncomputable def projectionMap (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc) :
    OracleMap (Spec.polynomialFamily R n deg) (messageFamily R deg) where
  f x _ := Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ())
  impl := Spec.SingleRound.simulateProjectedRoundPolynomial R n deg D i stmt
  law x q := Spec.SingleRound.simulateProjectedRoundPolynomial_eq R n deg D i stmt x q

variable {R deg n D}

/-- The projected data is the legacy projected round polynomial. -/
@[simp] theorem projectionMap_f (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (x : ∀ j, Spec.OracleStatement R n deg j) (u : Unit) :
    (projectionMap R deg n D i stmt).f x u =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ()) := rfl

/-- Answering a projected query from the multivariate input evaluates the projected round
polynomial at the query point. -/
theorem simulateQ_projectionMap (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (x : ∀ j, Spec.OracleStatement R n deg j) (r : R) :
    simulateQ ((Spec.polynomialFamily R n deg).behaviorOfRealizations x)
        ((projectionMap R deg n D i stmt).impl ⟨(), r⟩) =
      (Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ())).val.eval
        r :=
  (projectionMap R deg n D i stmt).law x ⟨(), r⟩

end Projection

end Sumcheck.Core
