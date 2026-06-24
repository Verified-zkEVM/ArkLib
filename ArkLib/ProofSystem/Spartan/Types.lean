/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.ProofSystem.Sumcheck.Interaction.General

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

structure PublicParams where
  ℓ_m : ℕ
  ℓ_n : ℕ
  ℓ_w : ℕ
  ℓ_w_le_ℓ_n : ℓ_w ≤ ℓ_n := by omega

namespace PublicParams

/-- R1CS dimensions determined by Spartan's padded public parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size where
  m := 2 ^ pp.ℓ_m
  n := 2 ^ pp.ℓ_n
  n_w := 2 ^ pp.ℓ_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n

end PublicParams

section Types

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Public R1CS input. -/
abbrev Statement : Type :=
  R1CS.Statement R pp.toSizeR1CS

/-- Matrix oracle family for the R1CS instance. -/
abbrev InputOracleFamily : R1CS.MatrixIdx → Type :=
  R1CS.OracleStatement R pp.toSizeR1CS

/-- Private R1CS witness. -/
abbrev Witness : Type :=
  R1CS.Witness R pp.toSizeR1CS

/-- The R1CS relation induced by Spartan's padded public parameters. -/
abbrev relation
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (InputOracleFamily R pp))
    (witness : Witness R pp) : Prop :=
  R1CS.relation R pp.toSizeR1CS stmt oracleStmt witness

/-- After the witness oracle message, the verifier has access to both the input
matrix oracle family and the witness oracle. -/
abbrev WithWitnessOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  Sum.elim (InputOracleFamily R pp) (fun _ => Witness R pp)

/-- First Spartan challenge, sampled over the constraint-index variables. -/
abbrev FirstChallenge : Type :=
  Fin pp.ℓ_m → R

/-- Local state after the first challenge: challenge plus public R1CS input. -/
abbrev AfterFirstChallengeStatement : Type :=
  FirstChallenge R pp × Statement R pp

/-- Oracle family after the first challenge is unchanged from the post-witness
state. -/
abbrev AfterFirstChallengeOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  WithWitnessOracleFamily R pp

/-- Spartan's first sum-check checks a degree-three virtual polynomial in the
constraint-index variables. -/
def firstSumcheckDegree : ℕ :=
  3

/-- The first sum-check input claim is the zero claim. -/
abbrev FirstSumcheckClaim : Type :=
  Sumcheck.RoundClaim R

/-- Terminal output of Spartan's first sum-check: the verifier challenge point
`r_x` together with the claimed value at that point. -/
abbrev FirstSumcheckResult : Type :=
  Sumcheck.FinalClaim R pp.ℓ_m

/-- Local state after the first sum-check: verifier result plus the previous
Spartan state. -/
abbrev AfterFirstSumcheckStatement : Type :=
  Option (FirstSumcheckResult R pp) × AfterFirstChallengeStatement R pp

/-- The Spartan oracle family is unchanged by the first sum-check view. -/
abbrev AfterFirstSumcheckOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  WithWitnessOracleFamily R pp

/-- Evaluation claims sent after the first sum-check: `A z(r_x)`,
`B z(r_x)`, and `C z(r_x)`. -/
abbrev EvalClaims : Type :=
  R1CS.MatrixIdx → R

/-- Local state after the prover sends the three matrix-vector evaluation
claims. -/
abbrev AfterEvalClaimStatement : Type :=
  EvalClaims R × AfterFirstSumcheckStatement R pp

/-- The Spartan oracle family is unchanged by the evaluation-claim message. -/
abbrev AfterEvalClaimOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  AfterFirstSumcheckOracleFamily R pp

/-- Verifier challenges for taking a random linear combination of the three
matrix-vector evaluation claims. -/
abbrev LinearCombinationChallenge : Type :=
  R1CS.MatrixIdx → R

/-- Local state after the verifier samples the linear-combination challenge. -/
abbrev AfterLinearCombinationStatement : Type :=
  LinearCombinationChallenge R × AfterEvalClaimStatement R pp

/-- The Spartan oracle family is unchanged by the linear-combination
challenge. -/
abbrev AfterLinearCombinationOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  AfterEvalClaimOracleFamily R pp

/-- Spartan's second sum-check checks a degree-two virtual polynomial in the
variable-index variables. -/
def secondSumcheckDegree : ℕ :=
  2

/-- The second sum-check input claim is the random linear combination of the
matrix-vector evaluation claims. -/
abbrev SecondSumcheckClaim : Type :=
  Sumcheck.RoundClaim R

/-- Terminal output of Spartan's second sum-check: the verifier challenge point
`r_y` together with the claimed value at that point. -/
abbrev SecondSumcheckResult : Type :=
  Sumcheck.FinalClaim R pp.ℓ_n

/-- Local state after the second sum-check. -/
abbrev AfterSecondSumcheckStatement : Type :=
  Option (SecondSumcheckResult R pp) × AfterLinearCombinationStatement R pp

/-- The Spartan oracle family is unchanged by the second sum-check view. -/
abbrev AfterSecondSumcheckOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  AfterLinearCombinationOracleFamily R pp

end Types

section SumcheckTypes

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Degree-bounded statement for Spartan's first virtual sum-check polynomial. -/
abbrev FirstSumcheckOracle : Type :=
  Sumcheck.PolyStmt R firstSumcheckDegree pp.ℓ_m

/-- Singleton oracle family carrying the first virtual sum-check polynomial. -/
abbrev FirstSumcheckOracleFamily : Unit → Type :=
  Sumcheck.PolyFamily R firstSumcheckDegree pp.ℓ_m

/-- Degree-bounded statement for Spartan's second virtual sum-check polynomial. -/
abbrev SecondSumcheckOracle : Type :=
  Sumcheck.PolyStmt R secondSumcheckDegree pp.ℓ_n

/-- Singleton oracle family carrying the second virtual sum-check polynomial. -/
abbrev SecondSumcheckOracleFamily : Unit → Type :=
  Sumcheck.PolyFamily R secondSumcheckDegree pp.ℓ_n

end SumcheckTypes

end

end OracleLayer

end Spartan
