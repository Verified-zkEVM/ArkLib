/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import Mathlib.Algebra.Field.ZMod

/-!
# Sampling Support for KZG-Style Setup

This file contains small shared probabilistic helpers used by KZG setup and its reductions.

## Notation

* `Groups.sampleNonzeroZMod` samples the SRS trapdoor from `ZMod p \ {0}`.
-/

open OracleSpec OracleComp

namespace Groups

section PrimeOrder

variable {p : outParam ℕ} [Fact (Nat.Prime p)]

/-- Uniformly sample a nonzero element of `ZMod p`.

The implementation samples an index in `{0, ..., p - 2}` and shifts it by one, so the support is
exactly the canonical representatives `1, ..., p - 1` modulo `p`. -/
def sampleNonzeroZMod : ProbComp (ZMod p) :=
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  (fun i : Fin (p - 1) => ((i : ℕ) + 1 : ZMod p)) <$> ($ᵗ (Fin (p - 1)))

/-- Simulating the random oracle leaves the nonzero SRS trapdoor sampler unchanged. -/
lemma simulateQ_randomOracle_sampleNonzeroZMod :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (sampleNonzeroZMod (p := p) : ProbComp (ZMod p)) :
        StateT unifSpec.QueryCache ProbComp (ZMod p))).run' ∅ =
      sampleNonzeroZMod (p := p) := by
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  unfold sampleNonzeroZMod
  cases p with
  | zero =>
      exact False.elim (Nat.not_prime_zero Fact.out)
  | succ p' =>
      cases p' with
      | zero =>
          exact False.elim (Nat.not_prime_one Fact.out)
      | succ p'' =>
          exact simulateQ_randomOracle_map_uniformFin p''
            (fun i : Fin (p'' + 1) => ((i : ℕ) + 1 : ZMod (p'' + 1 + 1)))

end PrimeOrder

end Groups
