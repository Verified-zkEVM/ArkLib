/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.RoundCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.LoopCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.GeneratorCost

/-!
# Complete scan profile envelopes

The recurrences account for every executed branch of the scan and its short-circuit local checks.
Bounds use the complete round schedule and apply to arbitrary retained words.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- A round list never exceeds the sum of its local envelopes and traversal ticks. -/
theorem profile_checkRounds_apply_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (x : (ω.subdomain 0).toFinset)
    (indices : List (Fin (k + 1))) (kind : CostKind) :
    (profile s o α (checkRounds s o α hs input x indices)).2 kind ≤
      (indices.map (fun i ↦ roundProfileBound s d.val i kind)).sum +
        if kind = .inl .metadata then indices.length else 0 := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    have hround := profile_checkRoundProgram_apply_le s o α hs input i x kind
    rw [profile_checkRounds_cons]
    by_cases hkind : kind = .inl .metadata
    · subst kind
      by_cases hb : (profile s o α (checkRoundProgram s o α hs input i x)).1.val = true <;>
        simp only [hb, Bool.false_eq_true, ite_true, ite_false, Pi.add_apply,
          embedArithmeticCost_metadata_apply, List.map_cons, List.sum_cons,
          List.length_cons, Pi.zero_apply] at ih hround ⊢ <;> omega
    · by_cases hb : (profile s o α (checkRoundProgram s o α hs input i x)).1.val = true <;>
        simp only [hb, Bool.false_eq_true, ite_true, ite_false, Pi.add_apply,
          embedArithmeticCost_metadata_apply, hkind, List.map_cons, List.sum_cons,
          List.length_cons, Pi.zero_apply] at ih hround ⊢ <;> omega

/-- The complete position-check envelope is the sum over all rounds and their ticks. -/
def positionProfileBound {r : ℕ} (s : Fin (r + 1) → ℕ+) (d : ℕ) (kind : CostKind) : ℕ :=
  (∑ i, roundProfileBound s d i kind) + if kind = .inl .metadata then r + 1 else 0

/-- Every position check obeys its complete-schedule envelope. -/
theorem profile_checkPosition_apply_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (z : Fin (2 ^ n))
    (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) (kind : CostKind) :
    (profile s o α (checkPosition s o α hs input z x)).2 kind ≤
      positionProfileBound s d.val kind := by
  have h := profile_checkRounds_apply_le s o α hs input x.val
    (List.finRange (k + 1)) kind
  have hsum : ((List.finRange (k + 1)).map
      (fun i ↦ roundProfileBound s d.val i kind)).sum =
        ∑ i, roundProfileBound s d.val i kind := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  rw [hsum] at h
  simpa [checkPosition, profile_bind, positionProfileBound] using h

/-- Reading a selected sample charges one retained-word access and no other instruction. -/
theorem profile_readSample_apply (z : Fin (2 ^ n))
    (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) (kind : CostKind) :
    (profile s o α (readSample s o α z x)).2 kind =
      if kind = .inr .wordRead then 1 else 0 := by
  unfold readSample
  dsimp only
  erw [profile_bind]
  simp only [profile_pure, add_zero]
  erw [profile_readWord]
  cases kind with
  | inl kind => cases kind <;> simp [instructionCost, AccessOp.costKind]
  | inr kind => cases kind <;> simp [instructionCost, AccessOp.costKind]

/-- A sample-selection step pays one tick and at most one retained-word read. -/
theorem profile_selectSample_apply_le {D : ℕ} (state : Selection s o D)
    (z : Fin (2 ^ n)) (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z})
    (kind : CostKind) :
    (profile s o α (selectSample s o α state z x)).2 kind ≤
      if kind = .inl .metadata ∨ kind = .inr .wordRead then 1 else 0 := by
  by_cases hcap : state.selected.length < D <;>
    cases kind with
    | inl kind => cases kind <;>
        simp [selectSample, hcap, profile_bind, profile_readSample_apply, embedArithmeticCost,
          arithmeticCost, ArithmeticOp.costKind]
    | inr kind => cases kind <;>
        simp [selectSample, hcap, profile_bind, profile_readSample_apply, embedArithmeticCost,
          ]

/-- An initial point uses binary generation, with no immutable-input reads after setup. -/
def initialPointProfileBound (n : ℕ) (kind : CostKind) : ℕ :=
  if kind = .inl .mul then 2 * n + 1 else if kind = .inl .metadata then n else 0

/-- A scan's per-position envelope includes generation, checks, selection and its loop tick. -/
def scanCellProfileBound (n : ℕ) (checks : Cost) (kind : CostKind) : ℕ :=
  initialPointProfileBound n kind + checks kind +
    (if kind = .inl .metadata ∨ kind = .inr .wordRead then 1 else 0) +
    if kind = .inl .metadata then 1 else 0

/-- Every explicit scan list obeys its per-position envelope and final loop tick. -/
theorem profile_scanAux_apply_le (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α})
    (checks : Cost) (hcheck : ∀ z x kind, (profile s o α (check z x)).2 kind ≤ checks kind)
    {D : ℕ} (xs : List (Fin (2 ^ n))) (state : Selection s o D) (kind : CostKind) :
    (profile s o α (scanAux s o α hs gen check xs state)).2 kind ≤
      xs.length * scanCellProfileBound n checks kind +
        if kind = .inl .metadata then 1 else 0 := by
  induction xs generalizing state with
  | nil => simp [scanAux, scanCellProfileBound, embedArithmeticCost_metadata_apply]
  | cons z zs ih =>
    let x := (profile s o α (generateInitialQuery s o α gen z)).1
    let b := (profile s o α (check z x)).1
    have hc := hcheck z x kind
    have hg := profile_initialPoint_apply_le s o α gen z kind
    by_cases hb : b.val = true
    · let next := (profile s o α (selectSample s o α state z x)).1
      have hr := ih next.val
      have hp := profile_selectSample_apply_le s o α state z x kind
      dsimp only [b, x] at hb hc hp
      simp only [scanAux, profile_bind, profile_liftComp_arithmetic,
        profileArithmetic_tick, Pi.add_apply, embedArithmeticCost_metadata_apply]
      simp only [hb, dite_true, profile_bind, profile_pure, Pi.add_apply, add_zero]
      dsimp only [next, x] at hr
      simp only [generateInitialQuery, profile_bind, profile_pure, add_zero] at *
      simp only [List.length_cons, Nat.add_mul, one_mul, scanCellProfileBound,
        initialPointProfileBound] at *
      omega
    · have hr := ih state
      dsimp only [b, x] at hb hc
      simp only [scanAux, profile_bind, profile_liftComp_arithmetic,
        profileArithmetic_tick, Pi.add_apply, embedArithmeticCost_metadata_apply]
      simp only [hb, Bool.false_eq_true, dite_false, profile_bind, profile_pure, add_zero]
      simp only [generateInitialQuery, profile_bind, profile_pure, add_zero] at *
      simp only [List.length_cons, Nat.add_mul, one_mul, scanCellProfileBound,
        initialPointProfileBound] at *
      omega

/-- Scanning the whole initial domain satisfies its explicit per-position envelope. -/
theorem profile_scan_apply_le (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α})
    (checks : Cost) (hcheck : ∀ z x kind, (profile s o α (check z x)).2 kind ≤ checks kind)
    (D : ℕ) (kind : CostKind) :
    (profile s o α (scan s o α hs gen check D)).2 kind ≤
      2 ^ n * scanCellProfileBound n checks kind +
        if kind = .inl .metadata then 1 else 0 := by
  simpa [scan, profile_bind] using
    profile_scanAux_apply_le s o α hs gen check checks hcheck
      (List.finRange (2 ^ n)) (emptySelection s o D) kind

end Fri.Spec.Extractor
