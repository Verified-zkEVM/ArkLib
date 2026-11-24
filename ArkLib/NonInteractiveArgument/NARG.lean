/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.Security.Game
public import ArkLib.Security.PrivateCoins

/-!
# Non-interactive arguments

The honest prover generates an argument string from a statement and witness. The verifier
consumes the statement and argument string directly. Both algorithms share an oracle environment.

In the adaptive security games, the adversary chooses the statement and argument string. Public
oracle state is shared, and private samples are excluded from query budgets and extractor logs.
This module defines the failure events and the adversary and extractor types. The experiments
are in `ArkLib.OracleReduction.Security.Basic`. The security predicates, such as
`Verifier.adaptiveNARGSoundness`, are in `ArkLib.InteractiveProof.Soundness`: each is the
adaptive interactive predicate at the one-message protocol `⟨!v[.P_to_V], !v[Proof]⟩`. The games
impose no running-time bound. The interfaces depend only on oracle computations.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec
open scoped NNReal ProbabilityTheory

/-! ## Honest execution and completeness -/

section HonestArgument

/-- A non-interactive argument consists of NARG string generation and a decision algorithm.
No reduced statement or witness is computed or returned. -/
structure NonInteractiveArgument {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness NARGString : Type) where
  prover : Statement → Witness → OracleComp oSpec NARGString
  verifier : Statement → NARGString → OracleComp oSpec Bool

variable {ι : Type} {oSpec : OracleSpec ι} {Statement Witness NARGString : Type}

/-- Generate a NARG string and verify it in the same oracle world. -/
def NonInteractiveArgument.run
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (stmt : Statement) (wit : Witness) : OracleComp oSpec Bool := do
  argument.verifier stmt (← argument.prover stmt wit)

/-- Completeness requires acceptance for every valid input, with the stated error bound. -/
def NonInteractiveArgument.completeness {σ : Type}
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (error : ℝ≥0) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation →
    Pr{let accepted ← (simulateQ impl (argument.run stmt wit)).run' (← init)}[
      accepted = true] ≥ 1 - error

end HonestArgument

/-! ## Failure events and adversary types -/

/-- False-acceptance event on the NARG soundness experiment output
`Option (StmtIn × StmtOut)`: the prover output a false statement (`x ∉ langIn`) the verifier
accepted into `stmtOut ∈ langOut`. The unbounded and query-bounded predicates use the
same event. A statement-size bound `size x ≤ n` belongs in the event: take
`langIn := {x | size x ≤ n → x ∈ L}`, or, for a Boolean verifier, run
`Verifier.restrictSize size n`, which rejects larger statements. -/
def nargSoundFailEvent {StmtIn StmtOut : Type} (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (StmtIn × StmtOut) → Prop
  | some (x, stmtOut) => x ∉ langIn ∧ stmtOut ∈ langOut
  | none => False

/-- Extraction-failure event on the NARG-KS experiment output
`StmtIn × Option WitIn × Option StmtOut`: the verifier accepted into `langOut` yet the extracted
input witness misses `relIn` (or none was produced). No output witness is supplied by the malicious
NARG prover: Definition 3.6 quantifies over the same adversaries producing only a statement and
NARG string `(x, π)` as Definition 3.5. -/
def nargKSFailEvent {StmtIn WitIn StmtOut : Type}
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut) :
    StmtIn × Option WitIn × Option StmtOut → Prop
  | (x, some witIn, some stmtOut) => stmtOut ∈ langOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut) => stmtOut ∈ langOut
  | _ => False

namespace NARG

/-- A malicious NARG prover chooses a statement and NARG string and has private coins. -/
abbrev Prover {ι : Type} (publicSpec : OracleSpec ι) (Statement NARGString : Type) :=
  OracleComp (publicSpec + unifSpec) (Statement × NARGString)

/-- A straight-line NARG extractor receives the statement, the NARG string, and both public
query logs. It runs in the final shared oracle state: its public queries go to the game's oracle
handler and its private coins are uniform. -/
abbrev Extractor {ι : Type} (publicSpec : OracleSpec ι) (Statement Witness NARGString : Type) :=
  Statement → NARGString → QueryLog publicSpec → QueryLog publicSpec →
    OptionT (OracleComp (publicSpec + unifSpec)) Witness

end NARG
