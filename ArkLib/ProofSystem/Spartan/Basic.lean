/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Component.SendWitness
import ArkLib.ProofSystem.Component.RandomQuery
import ArkLib.ProofSystem.Component.SendClaim
import ArkLib.ProofSystem.Component.CheckClaim

/-!
  # The Spartan PIOP (Polynomial Interactive Oracle Proof)

  The protocol is parametrized by the following parameters:

  - `R` is the underlying ring, required to be a finite integral domain.
  - `n := 2 ^ ℓ_n` is the number of variables in the R1CS relation.
  - `m := 2 ^ ℓ_m` is the number of constraints in the R1CS relation.
  - `k := 2 ^ ℓ_k` is the number of witness variables, where `ℓ_k < ℓ_n`.

  Note that all dimensions are required to be powers of two.

  It is used to prove the correctness of R1CS relations: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where:
  - `A, B, C : Matrix (Fin m) (Fin n) R` are the R1CS constraint matrices.
  - `𝕩 : Fin (n - k) → R` is the public input.
  - `𝕨 : Fin k → R` is the private witness.
  - `𝕫 = 𝕩 ‖ 𝕨` is the concatenation of the public input `𝕩` and the private witness `𝕨`.
  - `*ᵥ` denotes the standard matrix-vector product, and `*` denotes the component-wise product.

  The protocol may prove R1CS relations whose dimensions are not powers of two by zero-padding.
  (details in the `R1CS.lean` file)

  The protocol (described as a PIOP, before composing with poly commitments) proceeds as follows:

  **I. Interaction Phase:**

  - **Stage 0:** The oracle verifier may optionally receive oracle access to the multilinear
  extensions `MLE A, MLE B, MLE C : R[X Fin ℓ_n][X Fin ℓ_m]` of the R1CS matrices `A`, `B`,
  and `C`. Otherwise, the oracle verifier may see the matrices `A`, `B`, and `C` directly
  (as part of the input statement).

  - **Stage 1:** The prover sends the multilinear extension `MLE 𝕨 : R[X Fin ℓ_k]` of the witness
  `w` to the verifier. The verifier sends back a challenge `τ : Fin ℓ_m → R`.

  - **Stage 2:** The prover and verifier engage in a sum-check protocol to verify the computation:
      `∑ x ∈ {0, 1}^ℓ_m, eqPoly ⸨τ, x⸩ * (A_x ⸨x⸩ * B_x ⸨x⸩ - C_x ⸨x⸩) = 0`,

    where `A_x ⸨X⸩ = ∑ y ∈ {0, 1}^ℓ_m, (MLE A) ⸨X, y⸩ * (MLE 𝕫) ⸨y⸩`, and similarly for
    `B_x` and `C_x`.

    The sum-check protocol terminates with random challenges `r_x : Fin ℓ_m → R`, and the purported
    evaluation `e_x` of `eqPoly ⸨τ, r_x⸩ * (A_x ⸨r_x⸩ * B_x ⸨r_x⸩ - C_x ⸨r_x⸩)`.

  - **Stage 3:** The prover sends further evaluation claims to the verifier:
    `v_A = A_x ⸨r_x⸩`, `v_B = B_x ⸨r_x⸩`, `v_C = C_x ⸨r_x⸩`

    The verifier sends back challenges `r_A, r_B, r_C : R`.

  - **Stage 4:** The prover and verifier engage in another sum-check protocol to verify the
  computation:
    `∑ y ∈ {0, 1}^ℓ_n, r_A * (MLE A) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ + r_B * (MLE B) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ `
      `+ r_C * (MLE C) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ = r_A * v_A + r_B * v_B + r_C * v_C`

    The sum-check protocol terminates with random challenges `r_y : Fin ℓ_n → R`, and the purported
    evaluation `e_y` of
      `(r_A * (MLE A) ⸨r_x, r_y⸩ + r_B * (MLE B) ⸨r_x, r_y⸩ + r_C * (MLE C) ⸨r_x, r_y⸩) `
        `* (MLE 𝕫) ⸨r_y⸩`.

  **II. Verification Phase:**

  1. The verifier makes a query to the polynomial oracle `MLE 𝕨` at
  `r_y [ℓ_n - ℓ_k :] : Fin ℓ_k → R`, and obtain an evaluation value `v_𝕨 : R`.

  2. The verifier makes three queries to the polynomial oracles `MLE A, MLE B, MLE C` at
  `r_y ‖ r_x : Fin (ℓ_n + ℓ_m) → R`, and obtain evaluation values `v_1, v_2, v_3 : R`.

  Alternatively, if the verifier does not receive oracle access, then it computes the
  evaluation values directly.

  3. The verifier computes `v_𝕫 := 𝕩 *ᵢₚ (⊗ i, (1, r_y i))[: n - k] + (∏ i < ℓ_k, r_y i) * v_𝕨`,
  where `*ᵢₚ` denotes the inner product, and `⊗` denotes the tensor product.

  4. The verifier accepts if and only if both of the following holds:
    - `e_x = eqPoly ⸨τ, r_x⸩ * (v_A * v_B - v_C)`
    - `e_y = (r_A * v_1 + r_B * v_2 + r_C * v_3) * v_𝕫`.

-/

open MvPolynomial

namespace Spartan

noncomputable section

structure PublicParams where
  ℓ_n : ℕ
  ℓ_m : ℕ
  ℓ_k : ℕ

def PublicParams.toSizeR1CS (pp : PublicParams) : R1CS.Size := {
  m := 2 ^ pp.ℓ_m
  n_x := 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_k
  n_w := 2 ^ pp.ℓ_k
}

namespace Spec

variable (R : Type) [CommSemiring R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- The input types and relation is just the R1CS relation for the given size -/

abbrev InputStatement (pp : PublicParams) := R1CS.Statement R pp.toSizeR1CS

abbrev InputOracleStatement (pp : PublicParams) := R1CS.OracleStatement R pp.toSizeR1CS

abbrev InputWitness (pp : PublicParams) := R1CS.Witness R pp.toSizeR1CS

abbrev inputRelation (pp : PublicParams) := R1CS.relation R pp.toSizeR1CS

/-!
  ## First message
  We invoke the protocol `SendSingleWitness` to send the witness `𝕨` to the verifier.
-/


@[reducible]
def WitnessMLE (pp : PublicParams) : Type := R⦃≤ 1⦄[X Fin pp.ℓ_k]

@[reducible]
def pSpecFirstMessage : ProtocolSpec 1 := ![(.P_to_V, WitnessMLE R pp)]

open ProtocolSpec in
instance : ProverOnly (pSpecFirstMessage R pp) where
  prover_first' := by simp [pSpecFirstMessage]

def relationR1CS := R1CS.relation R (pp.toSizeR1CS)

/-!
  ## First challenge
  We invoke the protocol `RandomQuery` on the "virtual" polynomial:
    `𝒢(Z) = ∑_{x} eq ⸨Z, x⸩ * (A ⸨x⸩ * B ⸨x⸩ - C ⸨x⸩)`
-/

def pSpecFirstChallenge : ProtocolSpec 1 := ![(.V_to_P, Fin pp.ℓ_m → R)]

/-!
  ## First sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℱ(X) = eq ⸨τ, X⸩ * (A ⸨X⸩ * B ⸨X⸩ - C ⸨X⸩)`
-/

/-!
  ## Send evaluation claims

  We send the evaluation claims `v_A, v_B, v_C` to the verifier.

  (i.e. invoking `SendClaim` on these "virtual" values)
-/

/-!
  ## Random linear combination challenges

  The verifier sends back random linear combination challenges `r_A, r_B, r_C : R`.
-/

/-!
  ## Second sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℳ(Y) = r_A * (MLE A) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩ + r_B * (MLE B) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
      `+ r_C * (MLE C) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
-/

/-!
  ## Final check

  We invoke the `CheckClaim` protocol to check the two evaluation claims.
-/

end Spec

end


end Spartan
