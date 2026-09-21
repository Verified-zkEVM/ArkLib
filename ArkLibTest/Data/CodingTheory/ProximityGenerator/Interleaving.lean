/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# Interleaving transfer clients

These clients check the field-size boundary, an empty row type, and the absence of a
finite-field assumption in the row-functional avoidance lemma.
-/

open CoreDefinitions Code LinearCode

-- The affine-line case needs neither a positive width assumption nor radius bounds.
example {ι F A : Type} [Fintype ι] [Field F] [Fintype F] [SampleableType F]
    [AddCommMonoid A] [Module F A] (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError (AffineLineGenerator F) (C^⋈(Fin 3)) δ ≤
      mcaError (AffineLineGenerator F) C δ :=
  mcaError_moduleInterleavedCode_le_of_card_le (AffineLineGenerator F) C δ le_rfl

-- The same transfer applies to another generator with seed type F.
example {ι F A : Type} [Fintype ι] [Field F] [Fintype F] [SampleableType F]
    [AddCommMonoid A] [Module F A] (C : ModuleCode ι F A) (d : ℕ) (δ : ℝ) :
    mcaError (univariatePowersGenerator F d) (C^⋈(Fin 2)) δ ≤
      mcaError (univariatePowersGenerator F d) C δ :=
  mcaError_moduleInterleavedCode_le_of_card_le (univariatePowersGenerator F d) C δ le_rfl

-- Forward transfer covers an empty row type.
example {ι F A : Type} [Fintype ι] [Field F] [Fintype F] [SampleableType F]
    [AddCommMonoid A] [Module F A] (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError (AffineLineGenerator F) (C^⋈(Fin 0)) δ ≤
      mcaError (AffineLineGenerator F) C δ :=
  mcaError_moduleInterleavedCode_le_of_card_le (AffineLineGenerator F) C δ le_rfl

-- An arbitrary finite set of failures can be detected over an infinite field.
example {ι κ ℓ σ : Type} [Fintype κ] (C : ModuleCode ι ℚ ℚ)
    (U : ℓ → ι → κ → ℚ) (s : Finset σ) (T : σ → Finset ι)
    (hbad : ∀ x ∈ s, ∃ j,
      projectedWord (U j) (T x) ∉ projectedCodeSubmod (C^⋈κ) (T x)) :
    ∃ l : κ → ℚ, ∀ x ∈ s, ∃ j,
      projectedWord (fun i ↦ ∑ r, l r • U j i r) (T x) ∉
        projectedCodeSubmod C (T x) := by
  exact exists_rowFunctional_forall_notMem C U s T (by simp) hbad

-- Equality requires a nonempty row type; Fin 1 supplies it.
example {ι F A S ℓ : Type} [Fintype ι] [Field F] [Fintype S] [Nonempty S]
    [SampleableType S] [Fintype ℓ] [AddCommMonoid A] [Module F A] (G : Generator S ℓ F)
    (C : ModuleCode ι F A) (δ : ℝ) (hS : ENat.card S ≤ ENat.card F) :
    mcaError G (C^⋈(Fin 1)) δ = mcaError G C δ :=
  mcaError_moduleInterleavedCode_eq_of_card_le G C δ hS

-- The reverse transfer has no finiteness requirement on the row type.
example {ι F A S ℓ : Type} [Fintype ι] [Field F] [Fintype S] [Nonempty S]
    [SampleableType S] [Fintype ℓ] [AddCommMonoid A] [Module F A] (G : Generator S ℓ F)
    (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError G C δ ≤ mcaError G (C^⋈ℕ) δ :=
  mcaError_le_mcaError_moduleInterleavedCode G C δ
