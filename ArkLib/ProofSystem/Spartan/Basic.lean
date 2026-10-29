/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Layout
public import ArkLib.ProofSystem.Spartan.Algebra
public import ArkLib.ProofSystem.Spartan.VirtualOracle
public import ArkLib.ProofSystem.Spartan.SendEvaluations
public import ArkLib.ProofSystem.Spartan.Batching
public import ArkLib.ProofSystem.Component.SendWitness
public import ArkLib.ProofSystem.Spartan.ZeroCheck

/-!
  # The Spartan PIOP (Polynomial Interactive Oracle Proof)

  The protocol is parametrized by the following parameters:

  - `R` is the underlying ring, required to be a finite integral domain.
  - `n := 2 ^ ℓ_n` is the number of variables in the R1CS relation.
  - `m := 2 ^ ℓ_m` is the number of constraints in the R1CS relation.
  - `n_w := 2 ^ ℓ_w` is the number of witness variables, where `ℓ_w ≤ ℓ_n`.

  Note that all dimensions are required to be powers of two.

  It is used to prove the correctness of R1CS relations: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where:
  - `A, B, C : Matrix (Fin m) (Fin n) R` are the R1CS constraint matrices.
  - `𝕩 : Fin (n - n_w) → R` is the public input.
  - `𝕨 : Fin n_w → R` is the private witness.
  - `𝕫 = 𝕩 ‖ 𝕨` is the concatenation of the public input `𝕩` and the private witness `𝕨`.
  - `*ᵥ` denotes the standard matrix-vector product, and `*` denotes the component-wise product.

  Arbitrary R1CS instances embed into this layout by padding the public and witness blocks
  separately and relocating witness columns; see `Spartan.Layout`. Ordinary right-padding with
  an unchanged public-input length is insufficient.

  The protocol (described as a PIOP, before composing with poly commitments) proceeds as follows:

  **I. Interaction Phase:**

  - **Stage 0:** The oracle verifier may optionally receive oracle access to the multilinear
    extensions `MLE A, MLE B, MLE C : R[X Fin ℓ_n][X Fin ℓ_m]` of the R1CS matrices `A`, `B`, and
    `C`. Otherwise, the oracle verifier may see the matrices `A`, `B`, and `C` directly (as part of
    the input statement).

  - **Stage 1:** The prover sends the multilinear extension `MLE 𝕨 : R[X Fin ℓ_w]` of the witness
    `w` to the verifier. The verifier sends back a challenge `τ : Fin ℓ_m → R`.

  - **Stage 2:** The prover and verifier engage in a sum-check protocol to verify the computation:
      `∑ x ∈ {0, 1}^ℓ_m, eqPoly ⸨τ, x⸩ * (A𝕫 ⸨x⸩ * B𝕫 ⸨x⸩ - C𝕫 ⸨x⸩) = 0`,

    where `A𝕫 ⸨X⸩ = ∑ y ∈ {0, 1}^ℓ_n, (MLE A) ⸨X⸩ ⸨y⸩ * (MLE 𝕫) ⸨y⸩`, and similarly for `B𝕫` and
    `C𝕫`.

    The sum-check protocol terminates with random challenges `r_x : Fin ℓ_m → R`, and the purported
    evaluation `e_x` of `eqPoly ⸨τ, r_x⸩ * (A𝕫 ⸨r_x⸩ * B𝕫 ⸨r_x⸩ - C𝕫 ⸨r_x⸩)`.

  - **Stage 3:** The prover sends further evaluation claims to the verifier:

      `v_A = A𝕫 ⸨r_x⸩`, `v_B = B𝕫 ⸨r_x⸩`, `v_C = C𝕫 ⸨r_x⸩`

    The verifier sends back challenges `r_A, r_B, r_C : R`.

  - **Stage 4:** The prover and verifier engage in another sum-check protocol to verify the
    computation:

      `∑ y ∈ {0, 1}^ℓ_n, r_A * (MLE A) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ + r_B * (MLE B) ⸨r_x, y⸩ *`
      `(MLE 𝕫) ⸨y⸩ + r_C * (MLE C) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ = r_A * v_A + r_B * v_B + r_C * v_C`

    The sum-check protocol terminates with random challenges `r_y : Fin ℓ_n → R`, and the purported
    evaluation `e_y` of

      `(r_A * (MLE A) ⸨r_x, r_y⸩ + r_B * (MLE B) ⸨r_x, r_y⸩ + r_C * (MLE C) ⸨r_x, r_y⸩) *`
      `(MLE 𝕫) ⸨r_y⸩`.

  **II. Verification Phase:**

  1. The verifier queries the witness MLE at the low `ℓ_w` coordinates of `r_y`, obtaining
     `v_𝕨 : R`. Integer indices use the little-endian convention of `finFunctionFinEquiv`.

  2. The verifier queries each matrix MLE at `(r_x, r_y)`: row point first, column point second.
     If it has the matrices directly, it computes these evaluations instead.

  3. The verifier reconstructs the assignment evaluation as the equality-kernel weighted sum
     of public entries, plus `(∏ i ≥ ℓ_w, r_y i) * v_𝕨`. This is the unequal suffix layout
     specified by `assignment_mle_split`; no constant-one coordinate is inserted implicitly.

  4. The verifier accepts if and only if both of the following holds:
    - `e_x = eqPoly ⸨τ, r_x⸩ * (v_A * v_B - v_C)`
    - `e_y = (r_A * v_1 + r_B * v_2 + r_C * v_3) * v_𝕫`.

-/

@[expose] public section

open MvPolynomial Matrix OracleComp ProtocolSpec

namespace Spartan

namespace Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

section Construction

/- The input types and relation is just the R1CS relation for the given size -/

/-- This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R` -/
@[simp]
abbrev Statement := R1CS.Statement R pp.toSizeR1CS

/-- This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R` -/
@[simp]
abbrev OracleStatement := R1CS.OracleStatement R pp.toSizeR1CS

/-- This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R` -/
@[simp]
abbrev Witness := R1CS.Witness R pp.toSizeR1CS

/-- This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨` -/
@[simp]
abbrev relation := R1CS.relation R pp.toSizeR1CS

/-- Matrix oracles evaluate their original finite tables. -/
instance : ∀ i, OracleInterface (OracleStatement R pp i) :=
  Terminal.matrixInterface pp

/-- The witness oracle evaluates the multilinear extension of its finite table. -/
instance : OracleInterface (Witness R pp) := Terminal.witnessInterface pp

/-!
  ## First message
  We invoke the protocol `SendSingleWitness` to send the witness `𝕨` to the verifier.
-/

/-- Unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R` -/
@[simp]
abbrev Statement.AfterFirstMessage : Type := Statement R pp

/-- Unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R` and `𝕨 : Fin 2 ^ ℓ_w → R` -/
@[simp]
abbrev OracleStatement.AfterFirstMessage : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  Realization.OracleStatement (R := R) pp

/-- Unfolds to `() : Unit` -/
@[simp]
abbrev Witness.AfterFirstMessage : Type := Unit

def oracleReduction.firstMessage :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) Unit
      ⟨!v[.P_to_V], !v[Witness R pp]⟩ :=
  SendSingleWitness.oracleReduction oSpec
    (Statement R pp) (OracleStatement R pp) (Witness R pp)

/-!
  ## First challenge
  The zero-check challenge uses the abstract residual polynomial:
    `𝒢(Z) = ∑_{x} eq ⸨Z, x⸩ * (A𝕫 ⸨x⸩ * B𝕫 ⸨x⸩ - C𝕫 ⸨x⸩)`, which is supposed to be `0`.
-/

/-- The residual MLE view uses the noncomputable semantic polynomial representation. -/
noncomputable def zeroCheckVirtualPolynomial (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
      MvPolynomial (Fin pp.ℓ_m) R :=
  ZeroCheck.polynomial pp 𝕩 oStmt

/-- Unfolds to `τ : Fin ℓ_m → R` -/
@[simp]
abbrev FirstChallenge : Type := Fin pp.ℓ_m → R

/-- The sampled row point and unchanged public input. -/
@[simp]
abbrev Statement.AfterFirstChallenge : Type :=
  FirstChallenge R pp × Statement.AfterFirstMessage R pp

/-- Is equivalent to `((A, B, C), 𝕨) :`
  `(fun _ => (Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R)) × (Fin 2 ^ ℓ_w → R)` -/
@[simp]
abbrev OracleStatement.AfterFirstChallenge : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterFirstMessage R pp

@[simp]
abbrev Witness.AfterFirstChallenge : Type := Unit

def oracleReduction.firstChallenge :
    OracleReduction oSpec
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) Unit
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      ⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ :=
  ZeroCheck.oracleReduction pp oSpec

/-!
  ## First sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℱ(X) = eq ⸨τ, X⸩ * (A ⸨X⸩ * B ⸨X⸩ - C ⸨X⸩)`
-/

/-- Unfolds to `r_x : Fin ℓ_m → R` -/
@[simp]
abbrev FirstSumcheckChallenge : Type := Fin pp.ℓ_m → R

/-- The first sumcheck terminal claim, with its row point and retained input. -/
@[simp]
abbrev Statement.AfterFirstSumcheck : Type :=
  Evaluation.Statement (R := R) pp

/-- Is equivalent to `((A, B, C), 𝕨) :`
  `(fun _ => (Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R)) × (Fin 2 ^ ℓ_w → R)` -/
@[simp]
abbrev OracleStatement.AfterFirstSumcheck : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterFirstChallenge R pp

@[simp]
abbrev Witness.AfterFirstSumcheck : Type := Unit

/-!
  ## Send evaluation claims

  We send the evaluation claims `v_A, v_B, v_C` to the verifier.

  The verifier checks the equality-weighted scalar residual.
-/

/-- The scalar claims are public values alongside the first terminal statement. -/
@[simp]
abbrev Statement.AfterSendEvalClaim : Type :=
  (R1CS.MatrixIdx → R) × Statement.AfterFirstSumcheck R pp

/-- Sending scalar evaluations retains the original matrix and witness oracles. -/
@[simp]
abbrev OracleStatement.AfterSendEvalClaim : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterFirstSumcheck R pp

@[simp]
abbrev Witness.AfterSendEvalClaim : Type := Unit

/-- Send the three row values and check their equality-weighted residual. -/
def oracleReduction.sendEvalClaim :
    OracleReduction oSpec
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      (SendEvaluations.pSpec R) :=
  SendEvaluations.oracleReduction pp oSpec

/-!
  ## Random linear combination challenges

  The verifier sends back random linear combination challenges `r_A, r_B, r_C : R`.
-/

@[simp]
abbrev LinearCombinationChallenge : Type := R1CS.MatrixIdx → R

/-- The independent coefficients, claimed sum, and retained row claims. -/
@[simp]
abbrev Statement.AfterLinearCombination : Type :=
  Batching.Statement (R := R) pp

@[simp]
abbrev OracleStatement.AfterLinearCombination : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterSendEvalClaim R pp

@[simp]
abbrev Witness.AfterLinearCombination : Type := Unit

def oracleReduction.linearCombination :
    OracleReduction oSpec
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :=
  Batching.oracleReduction pp oSpec

/-!
  ## Second sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℳ(Y) = r_A * (MLE A) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩ + r_B * (MLE B) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
      `+ r_C * (MLE C) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
-/

/-- The second virtual polynomial, as a noncomputable semantic polynomial view. -/
noncomputable def secondSumCheckVirtualPolynomial
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
      MvPolynomial (Fin pp.ℓ_n) R :=
  Algebra.secondVirtual (fun i => oStmt (.inl i))
    (R1CS.𝕫 stmt.input.2.x (oStmt (.inr 0))) stmt.input.2.r_x stmt.ρ

@[simp]
abbrev SecondSumcheckChallenge : Type := Fin pp.ℓ_n → R

/-- The second sumcheck terminal claim and its two evaluation points. -/
@[simp]
abbrev Statement.AfterSecondSumcheck : Type :=
  Realization.FinalStatement (R := R) pp

@[simp]
abbrev OracleStatement.AfterSecondSumcheck : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterLinearCombination R pp

@[simp]
abbrev Witness.AfterSecondSumcheck : Type := Unit

/-!
  ## Final check

  The terminal verifier evaluates the second virtual polynomial through four oracle queries.
-/

/-- The semantic terminal equation. -/
def finalCheck := Realization.terminalRelation (R := R) pp

/-- Check the second sumcheck terminal claim against the retained original oracles. -/
def oracleReduction.finalCheck :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheck R pp) (OracleStatement.AfterSecondSumcheck R pp) Unit
      Unit (OracleStatement.AfterSecondSumcheck R pp) Unit !p[] :=
  Terminal.finalReduction pp oSpec

end Construction

end Spec

end Spartan
