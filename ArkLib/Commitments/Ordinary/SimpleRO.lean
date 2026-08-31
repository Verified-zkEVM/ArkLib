/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/

import ArkLib.Commitments.Ordinary.Basic
import VCVio

/-!
  # Simple Random-Oracle Commitment Scheme

  A simple non-interactive commitment scheme in the random-oracle model, expressed as an
  *ordinary* commitment scheme (VCV-io's `CommitmentScheme`):

  - The public parameter is the random oracle itself, modeled as a uniformly sampled function
    `ro : α × β → γ`. Over finite query and response spaces a uniformly random function is exactly
    a random oracle.
  - To commit to a message `v : α`, sample randomness `r : β` and output the commitment
    `ro (v, r) : γ` together with the opening `r`.
  - To open the commitment `cm`, the committer reveals `(v, r)`; verification recomputes
    `ro (v, r)` and checks that it equals `cm`.

  Because opening reveals the whole message `v` (rather than an oracle evaluation of hidden data),
  this is an *ordinary* commitment, so it instantiates VCV-io's oracle-free
  `CommitmentScheme PP M C D` directly. It mirrors VCV-io's standard-model hash commitment
  `CollisionResistance.KeyedHashFamily.toCommitment`, with a random oracle in place of a keyed
  hash family. For commitments with oracle openings, see `ArkLib.Commitments.Functional.Basic`.

  DISCLAIMER: this works but is a bit weird — it's an oracle commitment scheme without an oracle.
  VCV-io's `CommitmentScheme` only supports `ProbComp` (`OracleComp unifSpec`), not a general
  `OracleComp`, so the random oracle is baked in as a sampled function `ro : α × β → γ`. Two
  cleaner fixes: (1) model it as a functional commitment whose function just opens the whole
  commitment (weird, since it's then not really functional), or (2) extend VCV-io's
  `CommitmentScheme` to support a general `OracleComp`, not just `ProbComp`.
-/

open OracleComp CommitmentScheme

namespace SimpleRO

variable {α β γ : Type}

/-- A random oracle, modeled as a function from queries `α × β` to responses `γ`. -/
abbrev RandomOracle (α β γ : Type) := α × β → γ

/-- Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`. -/
def commit (ro : RandomOracle α β γ) (v : α) (r : β) : γ := ro (v, r)

/-- Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash. -/
def verify [DecidableEq γ] (ro : RandomOracle α β γ) (v : α) (cm : γ) (r : β) : Bool :=
  decide (commit ro v r = cm)

/-- The simple random-oracle commitment as an (ordinary) `CommitmentScheme`.

  Setup samples a uniformly random oracle `ro : α × β → γ`; committing to `v` samples randomness
  `r ← β` and returns `(ro (v, r), r)`; verification recomputes `ro (v, r)` and compares. -/
def commitmentScheme [FinEnum α] [FinEnum β] [SampleableType β] [SampleableType γ]
    [DecidableEq γ] :
    CommitmentScheme (RandomOracle α β γ) α γ β where
  setup := $ᵗ (RandomOracle α β γ)
  commit ro v := do
    let r ← $ᵗ β
    return (commit ro v r, r)
  verify ro v cm r := verify ro v cm r

end SimpleRO
