/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.Functional.KZG.Correctness
import ArkLib.Commitments.Functional.KZG.Security
import ArkLib.Commitments.Functional.KZG.AGM.Security
import ArkLib.Commitments.Functional.KZG.AGM.RandomizedSecurity
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

/-! ### Function binding

`run n pts cm os` reports three things: whether `os` wins the function-binding game for `cm`
(`functionBindingWins`, which checks every opening and that no polynomial of degree at most `n`
fits), the reduction's answer `(|S|, h₁, h₂)`, and whether that answer wins ARSDH. -/

/-- The ARSDH win predicate with `Z_S(τ)` written as `∏ s ∈ S, (τ - s)`. -/
private def wins (n : ℕ) (out : Finset F × F × F) : Bool :=
  let Z := ∏ s ∈ out.1, (τ - s)
  decide (out.1.card = n + 1 ∧ Z ≠ 0 ∧ out.2.1 ≠ 0 ∧ out.2.2 = Z⁻¹ • out.2.1)

/-- Run the reduction and report the game's win predicate, `(|S|, h₁, h₂)` and the ARSDH win
predicate. -/
private def run (n : ℕ) (pts : Fin (n + 2) ↪ F) (cm : F) (os : List (Opening F F)) :
    Bool × (ℕ × F × F) × Bool :=
  let out := functionBindingReduction pts (committerKey 1 τ n) vk cm os
  (functionBindingWins (n := n) e 1 vk (cm, os), (out.1.card, out.2.1, out.2.2), wins n out)

/-- The points `0, 1, 2`. -/
private def pts₁ : Fin 3 ↪ F := ⟨fun i => (i.val : F), by decide⟩

/-- The points `0, 1`. -/
private def pts₀ : Fin 2 ↪ F := ⟨fun i => (i.val : F), by decide⟩

-- Interpolation case: `cm = 5` and values `0, 1, 5` at `0, 1, 2`, which no line fits. The
-- interpolant through the first two openings is `X`, so `h₁ = 5 - 3 = 2`.
/-- info: (true, (2, 2, 5), true) -/
#guard_msgs in
#eval run 1 pts₁ 5 [(0, 0, 4), (1, 1, 2), (2, 5, 0)]

-- Interpolation case with the second node set: for `cm = 3` the interpolant `X` gives `h₁ = 0`,
-- so the reduction replaces the node at `0` by the opening at `2`.
/-- info: (true, (2, 1, 4), true) -/
#guard_msgs in
#eval run 1 pts₁ 3 [(0, 0, 1), (1, 1, 1), (2, 5, 5)]

-- Conflict case: two accepted openings at `2` with values `5` and `4`.
/-- info: (true, (2, 3, 1), true) -/
#guard_msgs in
#eval run 1 pts₁ 5 [(2, 5, 0), (2, 4, 1)]

-- Trapdoor case: an opening at `τ = 3` with value `cm = 5`, plus openings at `0` and `1`. The
-- line through `(3, 5)` and `(0, 0)` is `4X`, which misses `(1, 1)`, so the game is won.
/-- info: (true, (2, 1, 6), true) -/
#guard_msgs in
#eval run 1 pts₁ 5 [(3, 5, 0), (0, 0, 4), (1, 1, 2)]

-- Degree `n = 0`: accepted openings with values `5` at `0` and `1` at `1`, which no constant
-- fits. The ARSDH answer uses a single point.
/-- info: (true, (1, 4, 2), true) -/
#guard_msgs in
#eval run 0 pts₀ 5 [(0, 5, 0), (1, 1, 2)]

-- Outputs that do not win the game: no openings, and a repeated opening that agrees with the
-- line `X`.
/-- info: (false, false) -/
#guard_msgs in
#eval (functionBindingWins (n := 1) e 1 vk ((5 : F), []),
  functionBindingWins (n := 1) e 1 vk ((5 : F), [(0, 0, 4), (0, 0, 4), (1, 1, 2)]))

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
      Pr{let b ← ARSDH.experiment (1 : F) (1 : F) (functionBindingAdversary pts₁ A)}[b = true] :=
  functionBinding_le_arsdh e_one_one one_smul_surjective pts₁ A

/-- The class corollaries apply to any adversary class that contains the reduction. -/
example {Adv : Set (TSDH.Adversary F F F 2)} {ε : ENNReal}
    (hε : ∀ B ∈ Adv, Pr{let b ← TSDH.experiment (1 : F) (1 : F) B}[b = true] ≤ ε)
    (A : EvalBindingAdversary F F F 2) (hA : evalBindingAdversary A ∈ Adv) :
    Pr{let b ← evalBindingExperiment e 1 1 A}[b = true] ≤ ε :=
  evalBinding_le_of_tsdh e_one_one one_smul_surjective hε A hA

example {Adv : Set (ARSDH.Adversary F F F 1)} {ε : ENNReal}
    (hε : ∀ B ∈ Adv, Pr{let b ← ARSDH.experiment (1 : F) (1 : F) B}[b = true] ≤ ε)
    (A : FunctionBindingAdversary F F F 1) (hA : functionBindingAdversary pts₁ A ∈ Adv) :
    Pr{let b ← functionBindingExperiment e 1 1 A}[b = true] ≤ ε :=
  functionBinding_le_of_arsdh e_one_one one_smul_surjective pts₁ hε A hA

end KZGTest

namespace KZGTest

/-- Exhaustive roots for the small executable regression example. -/
private def enumeratingRoots (p : CompPoly.CPolynomial F) : List F :=
  ((List.range 7).map fun i => (i : F)).filter fun x => p.eval x == 0

/-- For degree zero, `cm = 0` and `π = 1` have explanations `[0]` and `[1]`.
The accepted claim `f(0) = -τ` disagrees with the extracted constant polynomial. -/
private def constantForgery : AGM.Output F F F (List (F × F)) :=
  ⟨⟨[(0, -τ)], AGM.groupInputs [0, 1] []⟩,
    fun | false => [[0], [1]] | true => []⟩

-- Recovery uses the verifier key, even though the committer key has no trapdoor entry.
/-- info: (true, 3) -/
#guard_msgs in
#eval (AGM.extractWins (n := 0) e 1 vk id constantForgery,
  AGM.recover (n := 0) 1 vk enumeratingRoots id constantForgery)

end KZGTest

namespace KZGTest

open CompPoly CompPoly.CPolynomial.Roots.FiniteField

/-- Explicit finite-field data for the executable Las Vegas example. -/
private def rootContext : FiniteFieldContext F where
  q := 7
  finite := inferInstance
  card_eq := by simp [Nat.card_eq_fintype_card]
  frobenius_fixed := by decide

/-- The seven residues supply the splitter's enumeration fallback. -/
private def rootEnumeration : FieldEnumeration F :=
  fieldEnumerationOfArray #[0, 1, 2, 3, 4, 5, 6] (by
    unfold ContainsAllFieldElements
    decide)

-- Both a nonzero probe and a zero probe find exactly the roots 2 and 5 of (X - 2)(X - 5).
-- The zero probe exercises the enumeration fallback after the bounded splitting attempt.
/-- info: true -/
#guard_msgs in
#eval
  let p := (CPolynomial.X - CPolynomial.C (2 : F)) *
    (CPolynomial.X - CPolynomial.C (5 : F))
  [CPolynomial.X, (0 : CPolynomial F)].all fun probe =>
    let roots := AGM.lasVegasRoots CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive rootContext rootEnumeration { cutoff := 1 } [probe] p
    roots.length == 2 && roots.contains 2 && roots.contains 5

end KZGTest
