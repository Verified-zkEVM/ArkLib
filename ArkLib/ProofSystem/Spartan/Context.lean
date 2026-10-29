/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Layout

/-!
# Retained Spartan public contexts

Each context extends the preceding public data. The matrix and witness tables remain separate
oracle statements throughout the protocol.
-/

@[expose] public section

namespace Spartan

variable {R : Type} [CommRing R] (pp : PublicParams)

namespace Evaluation

/-- The first sumcheck's terminal claim and retained public input. -/
structure Statement where
  x : R1CS.Statement R pp.toSizeR1CS
  τ : Fin pp.ℓ_m → R
  r_x : Fin pp.ℓ_m → R
  e : R

end Evaluation

namespace Batching

/-- The row claims and first sumcheck terminal statement, fixed before batching. -/
abbrev InputStatement := (R1CS.MatrixIdx → R) × Evaluation.Statement (R := R) pp

/-- The independent coefficients, claimed sum, and retained row claims. -/
structure Statement where
  input : InputStatement (R := R) pp
  ρ : R1CS.MatrixIdx → R
  c : R

end Batching

namespace Realization

/-- The final sumcheck evaluation and all retained batching data. -/
structure FinalStatement where
  input : Batching.Statement (R := R) pp
  r_y : Fin pp.ℓ_n → R
  e : R

/-- The original public input retained by the terminal statement. -/
def FinalStatement.x (s : FinalStatement (R := R) pp) := s.input.input.2.x

/-- The first sumcheck point retained by the terminal statement. -/
def FinalStatement.r_x (s : FinalStatement (R := R) pp) := s.input.input.2.r_x

/-- The independent batching coefficients retained by the terminal statement. -/
def FinalStatement.ρ (s : FinalStatement (R := R) pp) := s.input.ρ

end Realization

end Spartan
