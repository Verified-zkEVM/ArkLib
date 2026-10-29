/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Data
public import ArkLib.Data.CodingTheory.ProximityGenerator.ZeroEvading

/-! # Plonk batching data

Three residuals of degree at most `D` combine into a polynomial with the same inclusive degree
bound. Evaluation commutes with this operation, and vanishing is interpreted on the row domain.
-/

@[expose] public section

namespace Plonk.Batch

open CompPoly CoreDefinitions

variable {F : Type} [Field F] [DecidableEq F] {n d : ℕ}

/-- The finite set of row nodes. -/
def points (ω : F) (hω : IsPrimitiveRoot ω n) : Finset F :=
  Finset.univ.image (EvaluationDomain.primitiveRoot ω hω).node

/-- Vanishing on the indexed row domain agrees with vanishing on its finite node set. -/
theorem vanishes_iff_zeroOn (ω : F) (hω : IsPrimitiveRoot ω n) (p : Polynomial F) :
    (EvaluationDomain.primitiveRoot ω hω).Vanishes p ↔ Polynomial.ZeroOn (points ω hω) p := by
  simp [EvaluationDomain.Vanishes, Polynomial.ZeroOn, points]

/-- Repackage the component's actual batch with the exact inclusive residual budget. -/
def batch (f : Fin 3 → GeneratorBatch.Poly F (d + 1)) (α : F) :
    FiniteDomainQuotient.Poly F d :=
  ⟨(GeneratorBatch.batch (Nat.succ_pos d) f (powerBatchGenerator F 3 α)).val,
    Nat.le_of_lt_succ (GeneratorBatch.batch_natDegree_lt
      (Nat.succ_pos d) f (powerBatchGenerator F 3 α))⟩

/-- Tightening the degree proof preserves the component's polynomial value. -/
theorem batch_val (f : Fin 3 → GeneratorBatch.Poly F (d + 1)) (α : F) :
    (batch f α).val =
      (GeneratorBatch.batch (Nat.succ_pos d) f (powerBatchGenerator F 3 α)).val := rfl

end Plonk.Batch
