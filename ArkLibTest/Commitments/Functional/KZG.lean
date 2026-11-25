/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.Functional.KZG.Correctness
import ArkLib.Commitments.Functional.KZG.Security
import Mathlib.Algebra.Field.ZMod

/-!
# KZG: executable checks

The KZG algorithms and both binding reductions run over `ZMod 7`, with `ZMod 7` acting on itself
as every group, `g₁ = g₂ = 1`, multiplication as the pairing, and trapdoor `τ = 3`. With `τ` in
hand, the checks forge accepted openings and confirm that each reduction returns a winning
answer. The last section instantiates the game-level bounds of `KZG.Security` over the same
field.
-/

open KZG KZG.FunctionBinding

namespace KZGTest

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev F := ZMod 7

/-- Multiplication as an `F`-bilinear pairing on `F`. -/
private def e : F →ₗ[F] F →ₗ[F] F :=
  LinearMap.mk₂ F (· * ·) add_mul (fun _ _ _ => mul_assoc _ _ _) mul_add
    (fun _ _ _ => mul_left_comm _ _ _)

private def τ : F := 3

private def vk : Fin 2 → F := verifierKey 1 τ

/-! ### Correctness for `f = 1 + 2X + 3X²` at `q = 2` -/

private def ck₂ : Fin 3 → F := committerKey 1 τ 2
private def c : Fin 3 → F := ![1, 2, 3]

-- `f(3) = 34 = 6`, `f(2) = 17 = 3`, and the quotient `3X + 1` gives `π = 10 = 3`.
/-- info: (6, 3, 3) -/
#guard_msgs in
#eval (commit ck₂ c, evaluate c 2, generateOpening ck₂ c 2)

-- The honest opening is accepted and a wrong value is rejected.
/-- info: (true, false) -/
#guard_msgs in
#eval (verifyOpening e 1 vk (commit ck₂ c) 2 (evaluate c 2) (generateOpening ck₂ c 2),
  verifyOpening e 1 vk (commit ck₂ c) 2 4 (generateOpening ck₂ c 2))

/-! ### Evaluation binding -/

-- The forged opening `(4, 2)` at `q = 2` is accepted next to the honest `(3, 3)`. The reduction
-- returns `(-2, 1)`, which satisfies `τ + c ≠ 0 ∧ h = (τ + c)⁻¹ • g₁`.
/-- info: (true, true, (5, 1), true) -/
#guard_msgs in
#eval
  let r := evalBindingReduction (2 : F) 3 (3 : F) 4 2
  (verifyOpening e 1 vk (6 : F) 2 3 3, verifyOpening e 1 vk (6 : F) 2 4 2, r,
    decide (τ + r.1 ≠ 0 ∧ r.2 = (τ + r.1)⁻¹ • (1 : F)))

/-! ### Function binding with `n = 1` -/

private def ck₁ : Fin 2 → F := committerKey 1 τ 1

/-- The points `0, 1, 2`. -/
private def pts : Fin 3 ↪ F := ⟨fun i => (i.val : F), by decide⟩

/-- The ARSDH win predicate with `Z_S(τ)` written as `∏ s ∈ S, (τ - s)`. -/
private def wins (out : Finset F × F × F) : Bool :=
  let Z := ∏ s ∈ out.1, (τ - s)
  decide (out.1.card = 2 ∧ Z ≠ 0 ∧ out.2.1 ≠ 0 ∧ out.2.2 = Z⁻¹ • out.2.1)

/-- Whether every opening is accepted for `cm`. -/
private def allAccepted (cm : F) (os : List (Opening F F)) : Bool :=
  os.all fun o => verifyOpening e 1 vk cm o.1 o.2.1 o.2.2

/-- Run the reduction and report acceptance, `(|S|, h₁, h₂)` and the win predicate. -/
private def run (cm : F) (os : List (Opening F F)) : Bool × (ℕ × F × F) × Bool :=
  let out := functionBindingReduction pts ck₁ vk cm os
  (allAccepted cm os, (out.1.card, out.2.1, out.2.2), wins out)

-- Interpolation case: `cm = 5` and values `0, 1, 5` at `0, 1, 2`, which no line fits. The
-- interpolant through the first two openings is `X`, so `h₁ = 5 - 3 = 2`.
/-- info: (true, (2, 2, 5), true) -/
#guard_msgs in
#eval run 5 [(0, 0, 4), (1, 1, 2), (2, 5, 0)]

-- Interpolation case with the second node set: for `cm = 3` the interpolant `X` gives `h₁ = 0`,
-- so the reduction replaces the node at `0` by the opening at `2`.
/-- info: (true, (2, 1, 4), true) -/
#guard_msgs in
#eval run 3 [(0, 0, 1), (1, 1, 1), (2, 5, 5)]

-- Conflict case: two accepted openings at `2` with values `5` and `4`.
/-- info: (true, (2, 3, 1), true) -/
#guard_msgs in
#eval run 5 [(2, 5, 0), (2, 4, 1)]

-- Trapdoor case: an opening at `τ = 3`.
/-- info: (true, (2, 1, 6), true) -/
#guard_msgs in
#eval run 5 [(3, 5, 0), (0, 0, 4)]

/-! ### Game-level bounds over `ZMod 7` -/

private theorem e_one_one : e 1 1 ≠ 0 := by
  change (1 : F) * 1 ≠ 0
  decide

private theorem one_smul_surjective : Function.Surjective (· • (1 : F) : F → F) :=
  fun y => ⟨y, by simp⟩

/-- Evaluation binding for degree-`2` commitments over `ZMod 7` is bounded by t-SDH. -/
example (A : EvalBindingAdversary F F F 2) :
    Pr{let b ← evalBindingExperiment e 1 1 A}[b = true] ≤
      Pr{let b ← TSDH.experiment (1 : F) (1 : F) (evalBindingAdversary A)}[b = true] :=
  evalBinding_le_tsdh e_one_one one_smul_surjective A

/-- Function binding for degree-`1` commitments over `ZMod 7` is bounded by ARSDH. -/
example (A : FunctionBindingAdversary F F F 1) :
    Pr{let b ← functionBindingExperiment e 1 1 A}[b = true] ≤
      Pr{let b ← ARSDH.experiment (1 : F) (1 : F) (functionBindingAdversary pts A)}[b = true] :=
  functionBinding_le_arsdh e_one_one one_smul_surjective pts A

/-- The class corollaries apply to any adversary class that contains the reduction. -/
example {Adv : Set (TSDH.Adversary F F F 2)} {ε : ENNReal}
    (hε : ∀ B ∈ Adv, Pr{let b ← TSDH.experiment (1 : F) (1 : F) B}[b = true] ≤ ε)
    (A : EvalBindingAdversary F F F 2) (hA : evalBindingAdversary A ∈ Adv) :
    Pr{let b ← evalBindingExperiment e 1 1 A}[b = true] ≤ ε :=
  evalBinding_le_of_tsdh e_one_one one_smul_surjective hε A hA

example {Adv : Set (ARSDH.Adversary F F F 1)} {ε : ENNReal}
    (hε : ∀ B ∈ Adv, Pr{let b ← ARSDH.experiment (1 : F) (1 : F) B}[b = true] ≤ ε)
    (A : FunctionBindingAdversary F F F 1) (hA : functionBindingAdversary pts A ∈ Adv) :
    Pr{let b ← functionBindingExperiment e 1 1 A}[b = true] ≤ ε :=
  functionBinding_le_of_arsdh e_one_one one_smul_surjective pts hε A hA

end KZGTest
