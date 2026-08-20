/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Erasure
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Toy problem definitions

This file defines the exact and relaxed relations for the toy IOP of [ABF26, Section 6],
together with its winning-challenge set. The encoding map is part of the data: replacing it by
an existentially chosen map with the same range would change the constrained relation.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal

variable {ι F A : Type*} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]

/-- The toy-problem relation for a fixed linear encoder. Each word is the encoding of one
message row, and every message row satisfies its prescribed linear constraint. -/
def RelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ M : Fin ℓ → Fin k → F, (∀ i, W i = encode (M i)) ∧
    ∀ i, ∑ j, M i j * v j = μ i

/-- The relaxed toy-problem relation. A word stack is valid when it agrees with an exact
instance on at least a `1 - δ` fraction of coordinate blocks. -/
def RelaxedRelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ Wstar : Fin ℓ → ι → A, RelationFor encode v μ Wstar ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i, ∀ j ∈ S, W i j = Wstar i j

/-- The challenges for which the affine combination of two words and constraints is a valid
one-row relaxed instance. -/
def winningSetFor {k : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) : Set F :=
  {γ | RelaxedRelationFor (ℓ := 1) encode δ v
    (fun _ ↦ μ₁ + γ * μ₂) (fun _ j ↦ f₁ j + γ • f₂ j)}

end ToyProblem
