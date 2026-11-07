/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
public import ArkLib.Data.CodingTheory.Basic.Entropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.Set.Card

/-!
# Random linear codes: definitions

Definitions for the proof of `CodingTheory.random_linear_lambda_lower`.

## Main definitions

* `CodingTheory.RandomLinearInternal.law`, `CodingTheory.RandomLinearInternal.entQ`: the law and the
  base-`q` entropy of a random variable under a weight `μ` on a finite type.
* `CodingTheory.RandomLinearInternal.prodLaw`: the product weight on `I → A`.
* `CodingTheory.RandomLinearInternal.ber`: the `q`-ary Bernoulli weight `Ber_q(t)`.
* `CodingTheory.RandomLinearInternal.badLaw`, `CodingTheory.RandomLinearInternal.badRow`: the weight
  of `(u, α)` with `u ∼ Ber_q(p)^L` and `α` uniform, and the row `u + α · 1_L`. This is the bad
  distribution of [GLMRSW22].
* `CodingTheory.RandomLinearInternal.rowOrbit`: the matrices obtained by permuting the rows of a
  matrix.
* `CodingTheory.RandomLinearInternal.pcCode`: the code cut out by `m` parity checks.

The weights are real-valued, so `law`, `entQ`, `prodLaw`, `ber`, `pstar` and `badLaw` are
noncomputable (`Real` arithmetic and `Real.log`).

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

variable {Ω : Type} [Fintype Ω]

/-- A probability weight on a finite type. -/
def IsProb (μ : Ω → ℝ) : Prop := (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1

/-- The law (push-forward weight) of `X` under `μ`. -/
noncomputable def law {β : Type} [DecidableEq β] (μ : Ω → ℝ) (X : Ω → β) (b : β) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => X ω = b), μ ω

/-- Base-`q` Shannon entropy of `X` under `μ`. -/
noncomputable def entQ (q : ℕ) {β : Type} [Fintype β] [DecidableEq β]
    (μ : Ω → ℝ) (X : Ω → β) : ℝ :=
  (∑ b, Real.negMulLog (law μ X b)) / Real.log q

/-- The product weight on `I → A`. -/
noncomputable def prodLaw {I A : Type} [Fintype I] (b : I → A → ℝ) : (I → A) → ℝ :=
  fun ω => ∏ i, b i (ω i)

/-- `Ber_q(t)`: `0 ↦ 1 - t`, each nonzero symbol `↦ t/(q-1)`. -/
noncomputable def ber (q : ℕ) {A : Type} [Zero A] [DecidableEq A] (t : ℝ) (a : A) : ℝ :=
  if a = 0 then 1 - t else t / ((q : ℝ) - 1)

/-- The parameter `p + p' - p p' q / (q - 1)` of `Ber_q(p) + w · Ber_q(p')` for `w ≠ 0`. -/
noncomputable def pstar (q : ℕ) (p p' : ℝ) : ℝ := p + p' - p * p' * q / ((q : ℝ) - 1)



variable {ι : Type} {F : Type}

/-- The bad distribution on `Option (Fin L) → F`: the coordinates `some i` are `Ber_q(p)` (the
vector `u`), and the coordinate `none` is `Ber_q(1 - 1/q)`, the uniform weight (the scalar `α`). -/
noncomputable def badLaw (q : ℕ) (p : ℝ) (L : ℕ) (F : Type) [Field F] [DecidableEq F] :
    (Option (Fin L) → F) → ℝ :=
  prodLaw (fun o => ber q (o.elim (1 - 1 / (q : ℝ)) (fun _ => p)))

/-- The row `u + α · 1_L` of a sample of the bad distribution. -/
def badRow {L : ℕ} [Add F] (ω : Option (Fin L) → F) : Fin L → F :=
  fun i => ω (some i) + ω none

/-- The columns of a matrix given by its rows. This is `Function.swap M`, written as a lambda so
that `simp [cols]` evaluates it. -/
def cols {L : ℕ} (M : ι → Fin L → F) : Fin L → (ι → F) := fun i j => M j i

/-- The row-permutation orbit of `N`. -/
def rowOrbit {β : Type} (N : ι → β) : Set (ι → β) := Set.range fun σ : Equiv.Perm ι => N ∘ σ

/-- The code cut out by `m` parity checks. -/
def pcCode [Field F] (m : ℕ) (H : Fin m → Module.Dual F (ι → F)) : Submodule F (ι → F) :=
  ⨅ i, LinearMap.ker (H i)

end CodingTheory.RandomLinearInternal
