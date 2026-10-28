/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.WitnessAttachment
public import ArkLib.ProofSystem.Spartan.ZeroCheck
public import ArkLib.ProofSystem.Spartan.FirstSumcheck
public import ArkLib.ProofSystem.Spartan.SendEvaluations
public import ArkLib.ProofSystem.Spartan.Batching
public import ArkLib.ProofSystem.Spartan.SecondSumcheck
public import ArkLib.ProofSystem.Spartan.Terminal

/-!
# Spartan PIOP stages

Witness attachment embeds an arbitrary R1CS instance into the power-of-two layout and sends
its padded witness table. Zero-check samples the row point, and the first sumcheck reduces the
weighted residual sum to a point evaluation. Sending the three row evaluations and batching
with independent coefficients supplies the second sumcheck claim. The terminal stage checks
that claim through the retained matrix and witness oracles.

Each stage provides its own executable reduction, perfect completeness theorem, and
fixed-prefix knowledge-soundness certificate. The sumcheck lenses evaluate virtual polynomials
through the retained oracles; neither virtual polynomial is sent as a new oracle.
-/

@[expose] public section
