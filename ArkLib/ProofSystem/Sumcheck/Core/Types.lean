/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.OracleInterface
public import ArkLib.Interaction.Core.OracleVerifier
public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.MvPolynomial.EvalExcept
public import ArkLib.Data.Fin.Basic

/-! # Sumcheck claims and polynomial resources -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial Interaction.Core Interaction.Oracle

/-- A Sumcheck claim after fixing the first `i` variables. -/
structure RoundStatement (R : Type) (n : ℕ) (i : Fin (n + 1)) where
  /-- The claimed remaining sum. -/
  target : R
  /-- The public challenges already drawn. -/
  challenges : Fin i → R

/-- The polynomial resource carried unchanged through Sumcheck. -/
@[reducible]
def PolynomialData (R : Type) [CommSemiring R] (n deg : ℕ) : Unit → Type :=
  fun _ => R⦃≤ deg⦄[X Fin n]

/-- The input and output evaluation oracle for the multivariate polynomial.
Polynomial evaluation uses Mathlib's noncomputable representations. -/
noncomputable def polynomialFamily (R : Type) [CommSemiring R] (n deg : ℕ) :
    OracleFamily Unit (PolynomialData R n deg) := ⟨fun _ => inferInstance⟩

/-- Assign all variables except the round's free coordinate. -/
def roundSuffix {R : Type} {n : ℕ} (i : Fin n) (challenges : Fin i.castSucc → R)
    (x : Fin (n - 1 - i) → R) : Fin (n - 1) → R :=
  Fin.append challenges x ∘ Fin.cast (by have := i.isLt; simp; omega)

end Sumcheck.Core
