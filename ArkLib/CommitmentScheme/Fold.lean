/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import Batteries.Data.Vector.Basic
import ArkLib.OracleReduction.OracleInterface
import Mathlib.Data.FinEnum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ArkLib.Data.CodingTheory.ProximityGap

/-!
  # Folding-based Polynomial Commitment Schemes

  NOTE: this file should be deprecated now in favor of newer developments on FRI/STIR/WHIR in
  `ProofSystem`

  We define the folding IOP underlying polynomial commitment schemes such as FRI, Circle-FRI,
  BaseFold, FRI-Binius, and so on.

  In each round, the prover sends the verifier the claimed folding of the prior message, and the
  verifier performs a consistency check.

-/

open Batteries ProtocolSpec

open scoped Polynomial MvPolynomial NNReal

-- class MultiplicativeSubgroupPowerOfTwo (R : Type) [CommRing R] (n : ℕ) where
--   carrier : Subgroup Rˣ
--   carrier_equiv : carrier ≃ Fin (2 ^ n)
--   square_mem : ∀ x ∈ carrier, x * x ∈ carrier


-- namespace FRI

-- variable (R : Type) [CommRing R] [Sampleable R] (n : ℕ) (deg : ℕ) (ζ : Rˣ)
--   (hPrim : IsPrimitiveRoot ζ (2 ^ n))

-- structure StatementIn where
--   initialEvals : Vector R (2 ^ n)

-- structure StatementRound (k : Fin n) where
--   initialEvals : Vector R (2 ^ n)
--   chals : Fin k → R
--   earlyReject : Bool

-- structure Witness where
--   poly : R⦃≤ deg⦄[X]

-- /-- The proximity relation for the initial statement and witness

-- For completeness, we will use `δ = 0`, while for soundness, we will use `δ` as determined by the
-- proximity gap results -/
-- noncomputable def relationIn (δ : ℝ≥0) : StatementIn R n → (Witness R deg) → Prop :=
--   fun stmt wit =>
--     Δ₀( fun i => wit.poly.1.eval (ζ ^ i.val).val, stmt.initialEvals.get ) ≤ δ

-- /-- The proximity relation for the intermediate statement and witness after each round -/
-- noncomputable def relationRound (k : Fin n) (δ : ℝ≥0) :
--     StatementRound R n k → Witness R deg → Prop :=
--   fun stmt _ => stmt.earlyReject = false
--     -- Δ₀(fun i => wit.poly.1.eval (ζ ^ i.val).val, stmt.evals.get) ≤ δ

-- -- We first define FRI as an IOP. In fact, we will simply define a single round of FRI.

-- def pSpec : ProtocolSpec 2 := ⟨!v[.P_to_V], !v[Vector R (2 ^ n)]⟩ ++ₚ ⟨!v[.V_to_P], !v[R]⟩

-- variable {R} {n}

-- instance : IsSingleRound (pSpec R n) where
--   prover_first' := by simp [pSpec]
--   verifier_last' := by simp [pSpec, Neg.neg]

-- /-- Recognize that the (only) message from the prover to the verifier has type `Vector R (2 ^ n)`,
--   and hence can be turned into an oracle for evaluating the polynomial -/
-- instance instOracleInterfaceMessagePSpec : OracleInterface ((pSpec R n).Message default) := by
--   simp [pSpec, default, Message, getType]
--   exact instOracleInterfaceVector

-- /-- Recognize that the challenge from the verifier to the prover has type `R`, and hence can be
--   sampled uniformly at random -/
-- instance instSampleableChallengePSpec : Sampleable ((pSpec R n).Challenge default) := by
--   simp [Challenge, pSpec, default]
--   infer_instance

-- structure PrvState (k : Fin n) where
--   poly : R⦃≤ deg⦄[X]
--   foldedEvals : Vector R (2 ^ k.val)

-- /-- Given a polynomial p(x), returns (p_even, p_odd) where
--     p(x) = p_even(x²) + x * p_odd(x²) -/
-- noncomputable def splitEvenOdd (p : R[X]) : R[X] × R[X] :=
--   let evenSupp := p.support.filter (fun i => Even i)
--   let oddSupp := p.support.filter (fun i => Odd i)
--   (∑ i ∈ evenSupp, p.coeff i • (Polynomial.X ^ i), ∑ i ∈ oddSupp, p.coeff i • (Polynomial.X ^ i))

-- theorem splitEvenOdd_even_le_half_natDegree (p : R[X]) :
--   (splitEvenOdd p).1.natDegree ≤ p.natDegree / 2 := by
--   sorry

-- theorem splitEvenOdd_odd_le_half_natDegree (p : R[X]) :
--   (splitEvenOdd p).2.natDegree ≤ p.natDegree / 2 := by
--   sorry

-- /-- Alternative version that returns a bivariate polynomial q(x,y) that is linear in x
--     such that p(x) = q(x, x²) -/
-- noncomputable def splitEvenOddBivariate (p : R[X]) : R[X][X] :=
--   let (pEven, pOdd) := splitEvenOdd p
--   Polynomial.C pEven + pOdd • Polynomial.X

-- noncomputable def splitEvenOdd' (p : R⦃< 2 * n⦄[X]) : R⦃< n⦄[X] × R⦃< n⦄[X] :=
--   let ⟨pEven, pOdd⟩ := splitEvenOdd p
--   -- have hEven : pEven ∈ R⦃< deg⦄[X] := by sorry
--   -- have hOdd : pOdd ∈ R⦃< deg⦄[X] := by sorry
--   (⟨pEven, sorry⟩, ⟨pOdd, sorry⟩)

-- end FRI
