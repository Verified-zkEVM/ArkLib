/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail

/-!
# Singular-tail envelopes

Concrete envelope values, counterexamples showing that `M ≤ B` and `0 < M` are needed in the
envelope inequalities and that `0 < r` is needed for the common-root statement, and the forms of
the degree statements with the extra hypotheses `0 < r`, `r ≤ j` and `A.natDegree = r`.
-/

open Polynomial ReedSolomon.FirstOrder.Squarefree

namespace SingularTailTest

-- For `B = 10` and `M = 3` the resultant term `5 * 10 - 9 = 41` dominates.
example : ordinaryDegreeEnvelope 10 3 = 41 := by decide

-- For `M = 1` the resultant term `10 - 1 = 9` is below the budget `10`.
example : ordinaryDegreeEnvelope 10 1 = 10 := by decide

example : resultantChallengeEnvelope 7 3 = 35 := by decide

-- `M ≤ B` is needed in `content_add_resultantDegree_le`: with `B = 10`, `r = 5`, `M = 100`,
-- `j = 10`, `bU = 0` and `d = 65`, the other hypotheses hold and the envelope is `10`.
example : 5 ≤ 100 ∧ 0 + 10 ≤ 10 ∧ 65 + 5 ^ 2 ≤ (2 * 5 - 1) * 10 ∧
    ¬ 0 + 65 ≤ ordinaryDegreeEnvelope 10 100 := by decide

-- `0 < M` is needed in `content_add_resultantChallenge_le`: with `M = r = 0`, `H = hU = 1`,
-- `hV = d = 0`, the other hypotheses hold and the envelope is `0`.
example : 0 ≤ 0 ∧ 1 + 0 ≤ 1 ∧ 0 ≤ (2 * 0 - 1) * 0 ∧
    ¬ 1 + 0 ≤ resultantChallengeEnvelope 1 0 := by decide

-- The form with the extra hypotheses `0 < r` and `r ≤ j`.
example {B M bU j r d : ℕ} (_hr : 0 < r) (_hrj : r ≤ j) (hrM : r ≤ M) (hMB : M ≤ B)
    (hbudget : bU + j ≤ B) (hresultant : d + r ^ 2 ≤ (2 * r - 1) * j) :
    bU + d ≤ ordinaryDegreeEnvelope B M :=
  content_add_resultantDegree_le hrM hMB hbudget hresultant

-- The form with `0 < r` in place of `0 < M`.
example {H M hU hV r d : ℕ} (hr : 0 < r) (hrM : r ≤ M) (hbudget : hU + hV ≤ H)
    (hresultant : d ≤ (2 * r - 1) * hV) : hU + d ≤ resultantChallengeEnvelope H M :=
  content_add_resultantChallenge_le (hr.trans_le hrM) hrM hbudget hresultant

-- The degree statement with the extra hypotheses `0 < r`, `r ≤ j` and `A.natDegree = r`, and
-- the coefficient triangle at every index.
example {R : Type*} [CommRing R] (U : R[X]) (A : R[X][X]) {B M bU j r : ℕ}
    (_hr : 0 < r) (_hrj : r ≤ j) (hrM : r ≤ M) (hMB : M ≤ B)
    (hcontent : U.natDegree ≤ bU) (hbudget : bU + j ≤ B) (_hdegree : A.natDegree = r)
    (hcoeff : ∀ i, i ≤ r → i + (A.coeff i).natDegree ≤ j) :
    (singularTail U A r).natDegree ≤ ordinaryDegreeEnvelope B M :=
  natDegree_singularTail_le U A hrM hMB hcontent hbudget hcoeff

-- `0 < r` is needed in `singularTail_map_eq_zero_of_common_root`: for `r = 0` the resultant is
-- the empty determinant `1`, so the tail of `A = 0` with content `1` is `1`, although every
-- point is a common root of `0` and its derivative.
example : singularTail (1 : ℚ[X]) 0 0 = 1 := by
  simp [singularTail]

-- A concrete common root: `A = Y ^ 2` has the double root `0`, so its tail vanishes.
example (U : ℚ[X]) : singularTail U (X ^ 2 : ℚ[X][X]) 2 = 0 := by
  have h := singularTail_map_eq_zero_of_common_root U (X ^ 2 : ℚ[X][X]) two_pos
    (by simp) (RingHom.id ℚ[X]) 0 (by simp) (by simp)
  simpa using h

end SingularTailTest
