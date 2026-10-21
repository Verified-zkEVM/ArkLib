/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Program

/-!
# Profiles of retained-history extraction

These profiles count the same instruction programs whose erased results define the extractor.
Bounds include every input, including histories rejected by the initial degree guard.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- A word access contributes exactly one word-read instruction. -/
@[simp]
theorem profile_readWord (i : Fin (k + 1))
    (x : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset) :
    profile s o α (readWord s o α i x) =
      (accessAnswer s o α (.wordRead i x), instructionCost s (.inr (.wordRead i x))) := by
  exact profile_query s o α (.inr (.wordRead i x))

/-- A challenge access contributes exactly one immutable challenge read. -/
@[simp]
theorem profile_readChallenge (i : Fin (k + 1)) :
    profile s o α (readChallenge s o α i) =
      (accessAnswer s o α (.challengeRead i),
        instructionCost (ω := ω) s (.inr (.challengeRead i))) := by
  exact profile_query s o α (.inr (.challengeRead i))

/-- Reading the final polynomial does not traverse its coefficients. -/
@[simp]
theorem profile_readFinalPolynomial :
    profile s o α (readFinalPolynomial s o α) =
      (accessAnswer s o α .finalPolynomialRead,
        instructionCost (ω := ω) s (.inr .finalPolynomialRead)) := by
  exact profile_query s o α (.inr .finalPolynomialRead)

/-- Reading a degree contributes one metadata instruction. -/
@[simp]
theorem profile_readDegree (p : CPolynomial F) :
    profile s o α (readDegree s o α p) =
      (accessAnswer s o α (.polynomialDegreeRead p),
        instructionCost (ω := ω) s (.inr (.polynomialDegreeRead p))) := by
  exact profile_query s o α (.inr (.polynomialDegreeRead p))

/-- A lifted metadata tick contributes one unit only in the metadata coordinate. -/
@[simp]
theorem embedArithmeticCost_metadata_apply {K : Type} (kind : CostKind) :
    embedArithmeticCost (arithmeticCost (ArithmeticOp.metadata : ArithmeticOp K)) kind =
      if kind = .inl .metadata then 1 else 0 := by
  cases kind <;> simp [embedArithmeticCost, arithmeticCost, ArithmeticOp.costKind]
  rfl

/-- Traversal adds its step profiles and one control tick per list cell and terminator. -/
theorem profile_mapProgram_apply {A B : Type} (f : A → B)
    (step : (a : A) → OracleComp (InstructionSpec s o α) {b : B // b = f a})
    (xs : List A) (kind : CostKind) :
    (profile s o α (mapProgram s o α f step xs)).2 kind =
      (xs.map (fun a ↦ (profile s o α (step a)).2 kind)).sum +
        if kind = .inl .metadata then xs.length + 1 else 0 := by
  induction xs with
  | nil =>
    simp [mapProgram]
  | cons a xs ih =>
    by_cases hkind : kind = .inl .metadata
    · subst kind
      simp [mapProgram, profile_bind, ih]
      omega
    · simp [mapProgram, profile_bind, ih, hkind]

/-- Array construction has the same step profiles as its explicit finite-index traversal. -/
theorem profile_arrayProgram_apply {m : ℕ} (f : Fin m → F)
    (step : (i : Fin m) → OracleComp (InstructionSpec s o α) {a : F // a = f i})
    (kind : CostKind) :
    (profile s o α (arrayProgram s o α f step)).2 kind =
      ((List.finRange m).map (fun i ↦ (profile s o α (step i)).2 kind)).sum +
        if kind = .inl .metadata then m + 1 else 0 := by
  simp [arrayProgram, profile_mapProgram_apply]

/-- A uniform step bound gives an array-traversal bound including its control ticks. -/
theorem profile_arrayProgram_apply_le {m : ℕ} (f : Fin m → F)
    (step : (i : Fin m) → OracleComp (InstructionSpec s o α) {a : F // a = f i})
    (kind : CostKind) (B : ℕ) (hstep : ∀ i, (profile s o α (step i)).2 kind ≤ B) :
    (profile s o α (arrayProgram s o α f step)).2 kind ≤
      m * B + if kind = .inl .metadata then m + 1 else 0 := by
  rw [profile_arrayProgram_apply, ← List.ofFn_eq_map, List.sum_ofFn]
  have hsum : (∑ i : Fin m, (profile s o α (step i)).2 kind) ≤ ∑ _i : Fin m, B :=
    Finset.sum_le_sum (fun i _ ↦ hstep i)
  exact Nat.add_le_add_right (by simpa using hsum) _

/-- A sequential program is bounded by its first-step cost and a uniform continuation bound. -/
theorem profile_bind_apply_le {A B : Type}
    (p : OracleComp (InstructionSpec s o α) A)
    (f : A → OracleComp (InstructionSpec s o α) B) (kind : CostKind) (P Q : ℕ)
    (hp : (profile s o α p).2 kind ≤ P)
    (hf : ∀ a, (profile s o α (f a)).2 kind ≤ Q) :
    (profile s o α (p >>= f)).2 kind ≤ P + Q := by
  rw [profile_bind]
  exact Nat.add_le_add hp (hf (profile s o α p).1)

/-- Arithmetic lifting preserves every primitive-coordinate upper bound. -/
theorem profile_liftComp_apply_le {A : Type} (p : OracleComp (ArithmeticSpec F) A)
    (bound : ArithmeticCost) (hbound : ∀ kind, (profileArithmetic p).2 kind ≤ bound kind)
    (kind : CostKind) :
    (profile s o α (liftComp p _)).2 kind ≤ embedArithmeticCost bound kind := by
  rw [profile_liftComp_arithmetic]
  cases kind with
  | inl kind => exact hbound kind
  | inr kind => exact le_refl _

end Fri.Spec.Extractor
