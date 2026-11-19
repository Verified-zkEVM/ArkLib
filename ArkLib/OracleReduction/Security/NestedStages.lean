/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.VecTreeInterpolation
public import VCVio.CryptoFoundations.Rewinding.ThresholdFinder
import Mathlib.Data.NNRat.BigOperators

/-!
  # Nested stages: error and tree size of a protocol whose challenges are interpolated

  A public-coin protocol has stages `r`, each with a vector challenge. A stage is *nested* when
  extraction branches on its coordinates one at a time: below every prefix of the coordinates there
  are `arity r u` distinct choices of coordinate `u`, each with its own complete continuation.
  Taking the coordinates of all stages in order as the rounds of one challenge tree, such a
  protocol is extracted by the threshold finder of `VCVio.CryptoFoundations.Rewinding`.

  ## Main definitions

  - `NestedStages`: the number of coordinates, the alphabet and the arity of every coordinate of
    every stage.
  - `NestedStages.stageError`, `NestedStages.stageSize`: for one stage, the sum
    `∑ u, (arity r u - 1) / |alphabet r u|` and the product `∏ u, arity r u`.
  - `NestedStages.error`, `NestedStages.size`: the sum of the stage errors and the product of the
    stage sizes.
  - `NestedStages.roundEquiv`: the coordinates of all stages, in order, as the rounds of one tree.

  ## Main statements

  - `Rewinding.thresholdError_le_sum`: the threshold error is at most the sum of the per-round
    errors.
  - `NestedStages.finder_bounds`: the threshold finder on the rounds of the stages returns
    only accepting trees with distinct siblings, succeeds with probability at least the acceptance
    rate minus `error`, and makes at most `size` acceptance-oracle calls in expectation.

  ## Computability

  The data and the two quantities `error` and `size` are computable; `error` takes values in
  `ℚ≥0`. The statements about the finder are probabilistic specifications and are not claimed to be
  executable beyond `Rewinding.thresholdFinder`, which is.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal NNReal NNRat

namespace Rewinding

/-- For numbers `a r`, `1 - ∏ r, (1 - a r) ≤ ∑ r, a r`. -/
theorem one_sub_prod_one_sub_le_sum {R : Type*} (s : Finset R) (a : R → ℝ≥0∞) :
    1 - ∏ r ∈ s, (1 - a r) ≤ ∑ r ∈ s, a r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      by_cases ha : 1 ≤ a j
      · rw [tsub_eq_zero_of_le ha, zero_mul, tsub_zero]
        exact le_add_right ha
      · have ha' : a j ≤ 1 := (not_le.mp ha).le
        have hP : ∏ r ∈ s, (1 - a r) ≤ 1 :=
          Finset.prod_le_one (fun r _ => tsub_le_self)
        rw [tsub_le_iff_right]
        calc 1 ≤ ∑ r ∈ s, a r + ∏ r ∈ s, (1 - a r) := tsub_le_iff_right.mp ih
          _ = ∑ r ∈ s, a r + ((1 - a j) * ∏ r ∈ s, (1 - a r) + a j * ∏ r ∈ s, (1 - a r)) := by
              rw [← add_mul, tsub_add_cancel_of_le ha', one_mul]
          _ ≤ ∑ r ∈ s, a r + ((1 - a j) * ∏ r ∈ s, (1 - a r) + a j) := by
              gcongr
              exact mul_le_of_le_one_right zero_le hP
          _ = a j + ∑ r ∈ s, a r + (1 - a j) * ∏ r ∈ s, (1 - a r) := by ring

/-- The threshold error is at most the sum of the per-round errors `(k r - 1) / |C r|`. -/
theorem thresholdError_le_sum {R : Type} [Fintype R] (C : R → Type) [∀ r, Fintype (C r)]
    (k : R → ℕ) :
    thresholdError C k ≤ ∑ r, ((k r - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C r) :=
  one_sub_prod_one_sub_le_sum Finset.univ _

end Rewinding

/-- The coordinates, alphabets and arities of the nested stages of a public-coin protocol with `m`
stages. Stage `r` has `coords r` coordinates. Coordinate `u` ranges over `alphabet r u`, and
extraction needs `arity r u` distinct values of it below every prefix of the earlier coordinates. -/
structure NestedStages (m : ℕ) where
  /-- The number of coordinates of the challenge of stage `r`. -/
  coords : Fin m → ℕ
  /-- The alphabet of coordinate `u` of stage `r`. -/
  alphabet : (r : Fin m) → Fin (coords r) → Type
  /-- The number of distinct values of coordinate `u` of stage `r` that extraction needs. -/
  arity : (r : Fin m) → Fin (coords r) → ℕ

namespace NestedStages

variable {m : ℕ} (D : NestedStages m)

/-- The size of stage `r`: the product of the arities of its coordinates. -/
def stageSize (r : Fin m) : ℕ := ∏ u, D.arity r u

/-- The size of the tree of the protocol: the product of the sizes of its stages. -/
def size : ℕ := ∏ r, D.stageSize r

section Error

variable [∀ r u, Fintype (D.alphabet r u)]

/-- The error of stage `r`: the sum over its coordinates of `(arity - 1) / |alphabet|`. -/
def stageError (r : Fin m) : ℚ≥0 :=
  ∑ u, ((D.arity r u - 1 : ℕ) : ℚ≥0) / Fintype.card (D.alphabet r u)

/-- The error of the protocol: the sum of the errors of its stages. -/
def error : ℚ≥0 := ∑ r, D.stageError r

end Error

/-- The coordinates of all stages, in order, as the rounds of one challenge tree. -/
def roundEquiv : (Σ r, Fin (D.coords r)) ≃ Fin (∑ r, D.coords r) := finSigmaFinEquiv

/-- The alphabet of a round of the flattened tree. -/
abbrev roundAlphabet (j : Fin (∑ r, D.coords r)) : Type :=
  D.alphabet (D.roundEquiv.symm j).1 (D.roundEquiv.symm j).2

/-- The arity of a round of the flattened tree. -/
abbrev roundArity (j : Fin (∑ r, D.coords r)) : ℕ :=
  D.arity (D.roundEquiv.symm j).1 (D.roundEquiv.symm j).2

/-- The product of the arities of the rounds is the size of the tree. -/
theorem prod_roundArity : ∏ j, D.roundArity j = D.size :=
  (Equiv.prod_comp D.roundEquiv.symm fun x : (Σ r, Fin (D.coords r)) => D.arity x.1 x.2).trans
    (Fintype.prod_sigma _)

section Flatten

variable [∀ r u, Fintype (D.alphabet r u)]

/-- The per-round errors of the flattened tree add up to the error of the protocol. -/
theorem sum_round_error
    (hcard : ∀ (r : Fin m) (u : Fin (D.coords r)), 0 < Fintype.card (D.alphabet r u)) :
    ∑ j, ((D.roundArity j - 1 : ℕ) : ℝ≥0∞) / Fintype.card (D.roundAlphabet j) =
      ((D.error : ℝ≥0) : ℝ≥0∞) := by
  refine (Equiv.sum_comp (M := ℝ≥0∞) D.roundEquiv.symm fun x : (Σ r, Fin (D.coords r)) =>
    ((D.arity x.1 x.2 - 1 : ℕ) : ℝ≥0∞) / Fintype.card (D.alphabet x.1 x.2)).trans
    ((Fintype.sum_sigma _).trans ?_)
  simp only [error, stageError, NNRat.cast_sum, NNRat.cast_div, NNRat.cast_natCast,
    ENNReal.ofNNReal_finsetSum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun u _ => ?_
  rw [ENNReal.coe_div (by exact_mod_cast (hcard r u).ne')]
  simp

/-- The threshold finder on the rounds of nested stages. -/
abbrev finder [∀ r u, SampleableType (D.alphabet r u)] [∀ r u, DecidableEq (D.alphabet r u)] :
    OracleComp (unifSpec + Rewinding.accSpec D.roundAlphabet)
      (Option (Rewinding.VecTree D.roundAlphabet D.roundArity)) :=
  Rewinding.thresholdFinder D.roundAlphabet D.roundArity

variable [∀ r u, SampleableType (D.alphabet r u)] [∀ r u, DecidableEq (D.alphabet r u)]

/-- **The threshold finder on the rounds of nested stages.** Suppose each coordinate needs at least
one and at most `|alphabet|` values. Then against every Boolean acceptance function `f` on the
challenge vectors of the rounds:
* every tree it returns has pairwise distinct siblings at every node and accepts at every leaf;
* it succeeds with probability at least the acceptance rate of `f` minus `error`;
* it makes at most `size` acceptance-oracle calls in expectation, counted over complete runs
  whether or not they succeed. -/
theorem finder_bounds
    (hk : ∀ (r : Fin m) (u : Fin (D.coords r)),
      1 ≤ D.arity r u ∧ D.arity r u ≤ Fintype.card (D.alphabet r u))
    (f : ((j : Fin (∑ r, D.coords r)) → D.roundAlphabet j) → Bool) :
    (∀ z ∈ support (Rewinding.runFinder D.finder f), ∀ t, z.1 = some t →
      t.IsStructured (fun _ ch => Function.Injective ch) ∧ ∀ p, f (t.leaf p) = true) ∧
    Rewinding.acceptRate f - ((D.error : ℝ≥0) : ℝ≥0∞) ≤
      Pr{let z ← Rewinding.runFinder D.finder f}[z.1.isSome] ∧
    Rewinding.expectedCalls (Rewinding.runFinder D.finder f) ≤ (D.size : ℝ≥0∞) := by
  have h := Rewinding.isTreeFinder_thresholdFinder D.roundAlphabet D.roundArity
    fun j => hk _ _
  have hE : Rewinding.thresholdError D.roundAlphabet D.roundArity ≤ ((D.error : ℝ≥0) : ℝ≥0∞) :=
    (Rewinding.thresholdError_le_sum _ _).trans
      (D.sum_round_error fun r u => lt_of_lt_of_le (hk r u).1 (hk r u).2).le
  refine ⟨h.sound f, (tsub_le_tsub_left hE _).trans (h.acceptRate_sub_le f), ?_⟩
  refine (h.cost f).trans ?_
  rw [← D.prod_roundArity]
  push_cast
  exact le_rfl

end Flatten

end NestedStages
