/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.TerminalComposed

/-!
# The Spartan PIOP

This module is the canonical entrypoint for the native `Interaction.Oracle`
formalization of the Spartan polynomial interactive oracle proof.

The protocol is parametrized by:

- `R`, a finite integral domain.
- `ℓ_m`, where `2 ^ ℓ_m` is the number of R1CS constraints.
- `ℓ_n`, where `2 ^ ℓ_n` is the padded length of the full R1CS vector.
- `ℓ_w`, where `2 ^ ℓ_w` is the number of witness variables.

All dimensions are powers of two. Non-power-of-two instances are intended to
enter this padded protocol through the R1CS padding layer.

Spartan proves the correctness of an R1CS relation

`(A *ᵥ z) * (B *ᵥ z) = C *ᵥ z`,

where `A`, `B`, and `C` are the R1CS matrices, `x` is the public input,
`w` is the private witness, and `z = x ‖ w`.

## Native Interaction Structure

The formalization is built directly as an `Interaction.Oracle.Reduction`.
There is no separate Spartan-specific interaction DSL layer. The main pieces
are:

- `Spartan.Types`: public parameters, local statement types, oracle families,
  and the intermediate state carried through the protocol.
- `Spartan.OracleInterfaces`: oracle interfaces for the matrix, witness, and
  virtual sum-check oracle families.
- `Spartan.Setup`: the witness oracle message and first verifier challenge.
- `Spartan.FirstSumcheck`: the first virtual sum-check boundary, materializer,
  query evaluator, and continuation reduction.
- `Spartan.EvalClaims`: the public `A z(r_x)`, `B z(r_x)`, and `C z(r_x)`
  evaluation-claim message, followed by the random linear combination
  challenge.
- `Spartan.SecondSumcheck`: the second virtual sum-check boundary,
  materializer, query evaluator, and continuation reduction.
- `Spartan.Terminal`: the final verifier-owned query check.
- `Spartan.Composed` and `Spartan.TerminalComposed`: sequential composition of
  the above native reductions.

## Protocol Stages

Stage 0: the verifier starts with oracle access to the multilinear extensions
of the R1CS matrices. Equivalently, this is the input matrix oracle family
indexed by `R1CS.MatrixIdx`.

Stage 1: the prover sends the witness oracle. The verifier samples
`τ : Fin ℓ_m → R`.

Stage 2: the first sum-check verifies the virtual polynomial

`∑ x ∈ {0,1}^ℓ_m, eq(τ, x) * (A z(x) * B z(x) - C z(x)) = 0`.

It terminates with a verifier point `r_x : Fin ℓ_m → R` and a claimed value at
that point.

Stage 3: the prover sends the three evaluation claims

`v_A = A z(r_x)`, `v_B = B z(r_x)`, and `v_C = C z(r_x)`.

The verifier samples random coefficients `ρ_A`, `ρ_B`, and `ρ_C`.

Stage 4: the second sum-check verifies the random linear combination

`∑ y ∈ {0,1}^ℓ_n,
  (ρ_A * A(r_x, y) + ρ_B * B(r_x, y) + ρ_C * C(r_x, y)) * z(y)
  = ρ_A * v_A + ρ_B * v_B + ρ_C * v_C`.

It terminates with a verifier point `r_y : Fin ℓ_n → R` and a claimed value at
that point.

Stage 5: the terminal verifier check queries `A`, `B`, `C`, and the witness
oracle as needed to compute `z(r_y)` and checks the final claimed value:

`e_y =
  (ρ_A * A(r_x, r_y) + ρ_B * B(r_x, r_y) + ρ_C * C(r_x, r_y)) * z(r_y)`.

## Future Component Abstractions

The retired draft version of this file sketched several one-round oracle
reductions using generic components such as witness sending, public challenge
sampling, public claim sending, and terminal claim checking. Those ideas are
still important: the native Spartan construction should eventually factor
these repeated one-round patterns into reusable `Interaction.Oracle`
components.

The intended reusable components are:

- A witness-oracle message component generalizing the current witness round.
- A verifier-public-challenge component generalizing the `τ` and `ρ` rounds.
- A public-claim message component generalizing the evaluation-claim round.
- A terminal oracle-query claim checker generalizing the final Spartan check.

These are intentionally recorded here as design targets rather than preserved
as incomplete legacy definitions. Spartan itself is now the first protocol
whose public API is the native `Interaction.Oracle` construction directly.
-/
