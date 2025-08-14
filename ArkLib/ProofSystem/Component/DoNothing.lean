/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # The Trivial (Oracle) Reduction: Do Nothing!

  This is a zero-round (oracle) reduction. Both the (oracle) prover and the (oracle) verifier simply
  pass on their inputs unchanged.

  We still define this as the base for realizing other zero-round reductions, via lens / lifting.

  NOTE: we have already defined these as trivial (oracle) reductions
-/

namespace DoNothing

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type)

section Reduction

/-- The prover for the `DoNothing` reduction. -/
@[inline, specialize, simp]
def prover : Prover oSpec Statement Witness Statement Witness !p[] := Prover.id

/-- The verifier for the `DoNothing` reduction. -/
@[inline, specialize, simp]
def verifier : Verifier oSpec Statement Statement !p[] := Verifier.id

/-- The reduction for the `DoNothing` reduction.
  - Prover simply returns the statement and witness.
  - Verifier simply returns the statement.

  NOTE: this is just a wrapper around `Reduction.id`
-/
@[inline, specialize, simp]
def reduction : Reduction oSpec Statement Witness Statement Witness !p[] := Reduction.id

variable {oSpec} {Statement} {Witness}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (rel : Set (Statement × Witness))

/-- The `DoNothing` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_perfectCompleteness (hInit : init.neverFails):
    (reduction oSpec Statement Witness).perfectCompleteness init impl rel rel :=
  Reduction.id_perfectCompleteness init impl hInit

/-- The `DoNothing` verifier is perfectly round-by-round knowledge sound. -/
@[simp]
theorem verifier_rbrKnowledgeSoundness :
    (verifier oSpec Statement).rbrKnowledgeSoundness init impl rel rel 0 :=
  Verifier.id_rbrKnowledgeSoundness init impl

end Reduction

section OracleReduction

/-- The oracle prover for the `DoNothing` oracle reduction. -/
@[inline, specialize, simp]
def oracleProver : OracleProver oSpec
    Statement OStatement Witness Statement OStatement Witness !p[] := OracleProver.id

/-- The oracle verifier for the `DoNothing` oracle reduction. -/
@[inline, specialize, simp]
def oracleVerifier : OracleVerifier oSpec Statement OStatement Statement OStatement !p[] :=
  OracleVerifier.id

/-- The oracle reduction for the `DoNothing` oracle reduction.
  - Prover simply returns the (non-oracle and oracle) statement and witness.
  - Verifier simply returns the (non-oracle and oracle) statement.

  NOTE: this is just a wrapper around `OracleReduction.id`
-/
@[inline, specialize, simp]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Witness Statement OStatement Witness !p[] := OracleReduction.id

variable {oSpec} {Statement} {OStatement} {Witness}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (rel : Set ((Statement × (∀ i, OStatement i)) × Witness))
  (relOut : Set ((Statement × Witness) × (∀ i, OStatement i)))

/-- The `DoNothing` oracle reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem oracleReduction_perfectCompleteness (hInit : init.neverFails) :
    (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness init impl rel rel :=
  OracleReduction.id_perfectCompleteness init impl hInit

/-- The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound. -/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness :
    (oracleVerifier oSpec Statement OStatement).rbrKnowledgeSoundness init impl rel rel 0 :=
  OracleVerifier.id_rbrKnowledgeSoundness init impl

end OracleReduction

end DoNothing
