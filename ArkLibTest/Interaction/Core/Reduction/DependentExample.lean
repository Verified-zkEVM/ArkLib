/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Composition

/-!
# A dependent composed plain reduction

The prefix sends a `Bool`. A `false` prefix selects a `Bool` suffix message, while a `true` prefix
selects a `Fin 3` suffix message. Both branches execute through one composed reduction, built with
`Prover.append` and `Verifier.append`. A second composition keeps distinct prover and verifier
intermediate statements and the prover's private witness.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp

namespace Interaction.Core.DependentExampleTests

-- DependentExample 1, restated: the shared, statement, witness and interaction universes are
-- independent, as in the frozen canary. A family of reductions over a shared index is a function
-- from the index; ownership comes from the signature, so there is no role decoration. The output
-- statement and the prover output stay in the interaction universe, as in the frozen canary. The
-- ambient index is also in the interaction universe, because the prover runs in
-- `OracleComp ambient : Type u → Type u` (implementation note 18, premise-required); the frozen
-- canary has no ambient oracles, which the empty specification below recovers.
section UniverseCanary

universe uShared uStatement uWitness uInteraction

/-- Compile-time canary that shared, statement, witness and interaction universes remain
independent. -/
abbrev UniverseSeparatedReduction {ι : Type uInteraction}
    (ambient : OracleSpec.{uInteraction, uInteraction} ι)
    (Shared : Type uShared)
    (Context : Shared → Protocol.{uInteraction})
    (Statement : Shared → Type uStatement)
    (Witness : Shared → Type uWitness)
    (StatementOut : (i : Shared) → Path (Context i) → Type uInteraction)
    (WitnessOut : (i : Shared) → PathAlong plainSig (Context i) → Type uInteraction) :=
  (i : Shared) → Reduction ambient (Context i) (Statement i) (Witness i) (StatementOut i)
    (WitnessOut i)

end UniverseCanary

-- The canary at four distinct universes, with no ambient oracles: the shared index lies in
-- `Type 3`, the statements in `Type 2`, the witnesses in `Type 1` and the interaction in `Type 0`.
example : UniverseSeparatedReduction ([]ₒ : OracleSpec.{0, 0} PEmpty) (Type 2)
    (fun _ => (.pure ⟨⟩ : Protocol)) (fun X => X) (fun _ => Type) (fun _ _ => Unit)
    (fun _ _ => PUnit) :=
  fun _ => { prover := fun _ _ => pure ⟨⟩, verifier := { decide := fun _ _ _ => pure () } }

/-- No ambient oracle. -/
abbrev ambient : OracleSpec PEmpty := []ₒ

/-- The first interaction sends one Boolean. -/
@[instance_reducible] def prefixTree : Protocol := .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- The continuation changes its message type according to the complete prefix path. -/
@[instance_reducible] def suffixTree : Path prefixTree → Protocol
  | ⟨false, ⟨⟩⟩ => .liftBind (.message Bool) (fun _ => .pure ⟨⟩)
  | ⟨true, ⟨⟩⟩ => .liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩)

/-- The prefix followed by the path-dependent suffix. -/
abbrev composedTree : Protocol := prefixTree.append suffixTree

/-- The prefix prover sends its witness bit and keeps it as statement, with no private witness. -/
def prefixProver (bit : Bool) : Prover plainSig ambient prefixTree (fun _ => Bool × Unit) :=
  pure ⟨bit, pure (bit, ())⟩

/-- The prefix verifier forwards the sent bit as its intermediate statement. -/
def prefixVerifier : Verifier ambient prefixTree Unit (fun _ => Bool) where
  decide _ p _ := pure p.1

/-- The suffix prover emits a branch-specific message and claims the statement 0 or 2.

The explicit dependent match is the canary: the two branches cannot be replaced by one constant
continuation because their move types differ. -/
def suffixProver : (p : Path prefixTree) →
    Prover plainSig ambient (suffixTree p) (fun _ => Nat × Unit)
  | ⟨false, ⟨⟩⟩ => pure ⟨false, pure (0, ())⟩
  | ⟨true, ⟨⟩⟩ => pure ⟨(2 : Fin 3), pure (2, ())⟩

/-- The suffix verifier turns its branch-specific message into a natural-number statement. -/
def suffixVerifier : (p : Path prefixTree) → Verifier ambient (suffixTree p) Bool (fun _ => Nat)
  | ⟨false, ⟨⟩⟩ => ⟨fun _ q _ => pure (if (show Bool from q.1) then 1 else 0)⟩
  | ⟨true, ⟨⟩⟩ => ⟨fun _ q _ => pure (show Fin 3 from q.1).val⟩

/-- The dependent two-stage reduction: the suffix prover is chosen by the prefix transcript. -/
def composed : Reduction ambient composedTree Unit Bool (fun _ => Nat) (fun _ => Nat × Unit) where
  prover _ bit := Prover.append (prefixProver bit)
    (fun tr _ => pure (suffixProver (projectPathAlong plainSig prefixTree tr)))
  verifier := prefixVerifier.append suffixVerifier

/-- No challenges and no ambient queries: evaluate a run in `Option`. -/
def evaluate {α : Type} (program : OracleComp (ambient + challengeSpec plainSig composedTree) α) :
    Option α :=
  simulateQ (fun q => match q with
    | .inl q => q.elim
    | .inr c => nomatch c : QueryImpl (ambient + challengeSpec plainSig composedTree) Option)
    program

/-- The shape path, the prover's statement and the verifier's verdict of one honest run. -/
def summary (bit : Bool) : Option (Path composedTree × Nat × Option Nat) :=
  evaluate ((fun obs => (projectPathAlong plainSig composedTree obs.1, obs.2.1.1, obs.2.2)) <$>
    composed.observe () bit)

-- DependentExample 2, restated: the false prefix message selects the `Bool` suffix branch; the
-- path is a shape path of the appended protocol.
example : (summary false).map (·.1) = some ⟨false, false, ⟨⟩⟩ := rfl

-- DependentExample 3, restated: the true prefix message selects the `Fin 3` suffix branch.
example : (summary true).map (·.1) = some ⟨true, (2 : Fin 3), ⟨⟩⟩ := rfl

-- DependentExample 4, restated: the full result on the `Bool` branch. The prover's output and the
-- verifier's accepted verdict are both 0. The frozen `packAppend` wrapping is not needed, because
-- outputs are typed over the appended transcript directly.
example : summary false = some (⟨false, false, ⟨⟩⟩, 0, some 0) := rfl

-- DependentExample 5, restated: the full result on the `Fin 3` branch: both statements are 2.
example : summary true = some (⟨true, (2 : Fin 3), ⟨⟩⟩, 2, some 2) := rfl

-- The same results, from the full observation without the summary projection.
example : composed.observe () false =
    pure ⟨⟨false, false, ⟨⟩⟩, (0, ()), some 0⟩ := rfl

example : composed.observe () true =
    pure ⟨⟨true, (2 : Fin 3), ⟨⟩⟩, (2, ()), some 2⟩ := rfl

/-! ## Distinct intermediate outputs

Composition keeps each participant's own intermediate statement and the prover's private witness,
even when the two statements disagree. -/

/-- The prefix prover claims `true` with private witness 7. -/
def disagreeingProver (bit : Bool) : Prover plainSig ambient prefixTree (fun _ => Bool × Nat) :=
  pure ⟨bit, pure (true, 7)⟩

/-- The prefix verifier decides `false`, whatever is sent. -/
def disagreeingVerifier : Verifier ambient prefixTree Unit (fun _ => Bool) where
  decide _ _ _ := pure false

/-- A terminal suffix exposing the statement and witness it actually received. -/
def observingProver (mid : Bool × Nat) : Prover plainSig ambient (.pure ⟨⟩) (fun _ => Bool × Nat) :=
  pure (mid.1, mid.2 + 1)

/-- A terminal suffix decision that returns the statement it received. -/
def observingVerifier : Verifier ambient (.pure ⟨⟩) Bool (fun _ => Bool) where
  decide stmt _ _ := pure stmt

/-- The prefix followed by a terminal suffix. -/
abbrev observedTree : Protocol := prefixTree.append (fun _ => .pure ⟨⟩)

/-- The suffix prover is built from the prefix prover's output; the suffix verifier receives the
prefix verifier's decided statement. -/
def disagreeing : Reduction ambient observedTree Unit Bool (fun _ => Bool)
    (fun _ => Bool × Nat) where
  prover _ bit := Prover.append (disagreeingProver bit) (fun _ mid => pure (observingProver mid))
  verifier := disagreeingVerifier.append (fun _ => observingVerifier)

-- DependentExample 6, restated: the suffix prover sees the prover's `true` and witness 7 (8
-- after its step); the suffix verifier sees the verifier's `false`. Stated for both sent bits.
example (bit : Bool) : disagreeing.observe () bit = pure ⟨⟨bit, ⟨⟩⟩, (true, 8), some false⟩ := by
  cases bit <;> rfl

end Interaction.Core.DependentExampleTests
