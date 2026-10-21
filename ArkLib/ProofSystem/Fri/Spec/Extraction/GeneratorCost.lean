/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Generator

/-!
# Domain-generator profiles

The complete cost vectors count initialization accesses and all arithmetic instructions used to
generate later points. Bounds concern algebraic primitives and designated control ticks.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

@[simp]
theorem profile_readDomain (z : Fin (2 ^ n)) :
    profile s o α (readDomain s o α z) =
      (accessAnswer s o α (.domainRead z), instructionCost (ω := ω) s (.inr (.domainRead z))) := by
  exact profile_query s o α (.inr (.domainRead z))

/-- Domain-generator initialization uses at most two reads, one inverse, and one multiplication. -/
theorem profile_initGenerator :
    (profile s o α (initGenerator s o α)).2 = fun kind ↦ match kind with
      | .inr .domainRead => if n = 0 then 1 else 2
      | .inl .inv | .inl .mul => if n = 0 then 0 else 1
      | _ => 0 := by
  by_cases hn : n = 0
  · simp only [initGenerator, hn, dite_true]
    funext kind
    cases kind with
    | inl kind => cases kind <;>
        simp [instructionCost, AccessOp.costKind]
    | inr kind => cases kind <;>
        simp [instructionCost, AccessOp.costKind]
  · simp only [initGenerator, hn, dite_false, profile_bind, profile_readDomain]
    funext kind
    cases kind with
    | inl kind => cases kind <;>
        simp [embedArithmeticCost, arithmeticCost, ArithmeticOp.costKind,
          instructionCost, AccessOp.costKind]
    | inr kind => cases kind <;>
        simp [embedArithmeticCost, instructionCost, AccessOp.costKind]

/-- Generating one domain point uses a binary power and one multiplication. -/
theorem profile_initialPoint_apply_le (gen : Generator ω) (z : Fin (2 ^ n))
    (kind : CostKind) :
    (profile s o α (initialPoint s o α gen z)).2 kind ≤
      if kind = .inl .mul then 2 * n + 1 else if kind = .inl .metadata then n else 0 := by
  have hpow := Arithmetic.profileArithmetic_powerBits_apply_le gen.ratio n z.val z.isLt
  cases kind with
  | inl kind =>
    have hp := hpow kind
    cases kind <;>
      simp [initialPoint, profile_bind, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind] at hp ⊢ <;> omega
  | inr kind =>
    simp [initialPoint, profile_bind, embedArithmeticCost]

end Fri.Spec.Extractor
