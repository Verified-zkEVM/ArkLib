/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Security

/-!
# Spartan PIOP

Witness attachment embeds an arbitrary R1CS instance into the power-of-two layout and sends
its padded witness table. Zero-check samples the row point, and the first sumcheck reduces the
weighted residual sum to a point evaluation. Sending the three row evaluations and batching
with independent coefficients supplies the second sumcheck claim. The terminal stage checks
that claim through the retained matrix and witness oracles.

`oracleReduction` composes the seven stages with an executable honest prover.
`perfectCompleteness`, `rbrKnowledgeSoundnessWith`, and `knowledgeSoundness`
certify this reduction for the original R1CS relation. Its additive knowledge error is
`(4s + 2t + 1) / |R|`, and `knowledgeSoundness_clipped` caps the bound at one.
The sumcheck lenses use the retained oracles; neither virtual polynomial is sent as a new oracle.
-/

@[expose] public section
