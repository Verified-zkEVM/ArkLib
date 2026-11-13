/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
public import ArkLib.Data.CodingTheory.Basic.Entropy
public import ArkLib.Data.CodingTheory.Basic.ParityCheck
public import ArkLib.Data.Probability.FiniteEntropy
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Random linear codes: definitions

Definitions for the proof of `CodingTheory.random_linear_lambda_lower`.

## Main definitions

* `CodingTheory.RandomLinearInternal.ber`: the `q`-ary Bernoulli weight `Ber_q(t)`.
* `CodingTheory.RandomLinearInternal.badLaw`, `CodingTheory.RandomLinearInternal.badRow`: the weight
  of `(u, α)` with `u ∼ Ber_q(p)^L` and `α` uniform, and the row `u + α · 1_L`. This is the bad
  distribution of [GLMRSW22].
* `CodingTheory.RandomLinearInternal.rowOrbit`: the matrices obtained by permuting the rows of a
  matrix, as an orbit of `(Equiv.Perm ι)ᵈᵐᵃ`.

The weights, the entropy and the product weight are those of
`ArkLib.Data.Probability.FiniteEntropy`. `ber`, `pstar` and `badLaw` are noncomputable (`Real`
arithmetic).

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Probability

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

/-- The row-permutation orbit of `N`. -/
def rowOrbit {β : Type} (N : ι → β) : Set (ι → β) := MulAction.orbit (Equiv.Perm ι)ᵈᵐᵃ N

theorem mem_rowOrbit {β : Type} {N M : ι → β} : M ∈ rowOrbit N ↔ ∃ σ : Equiv.Perm ι, N ∘ σ = M :=
  ⟨fun ⟨g, hg⟩ => ⟨DomMulAct.mk.symm g, hg⟩, fun ⟨σ, hσ⟩ => ⟨DomMulAct.mk σ, hσ⟩⟩

end CodingTheory.RandomLinearInternal
