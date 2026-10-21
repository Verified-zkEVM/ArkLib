/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Access

/-!
# Certified instruction traversal

List and array traversals execute explicit instruction steps and charge designated control ticks.
Their reference functions occur only in the erased correctness certificates.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Traverse an explicit list without executing its certified reference function. -/
def mapProgram {A B : Type} (f : A → B)
    (step : (a : A) → OracleComp (InstructionSpec s o α) {b : B // b = f a}) :
    (xs : List A) → OracleComp (InstructionSpec s o α) {ys : List B // ys = xs.map f}
  | [] => do
    liftComp (Arithmetic.tick (F := F)) _
    pure ⟨[], rfl⟩
  | x :: xs => do
    liftComp (Arithmetic.tick (F := F)) _
    let y ← step x
    let ys ← mapProgram f step xs
    pure ⟨y.val :: ys.val, by rw [y.property, ys.property]; rfl⟩

/-- Build a field array by certified operations on its explicit index list. -/
def arrayProgram {m : ℕ} (f : Fin m → F)
    (step : (i : Fin m) → OracleComp (InstructionSpec s o α) {a : F // a = f i}) :
    OracleComp (InstructionSpec s o α) {a : Array F // a = Array.ofFn f} := do
  let xs ← mapProgram s o α f step (List.finRange m)
  pure ⟨xs.val.toArray, by rw [xs.property, ← List.ofFn_eq_map, List.toArray_ofFn]⟩

/-- Copy explicit coefficients through individually charged array accesses. -/
def copyCoefficients (p : CPolynomial.Raw F) :
    OracleComp (InstructionSpec s o α) {a : Array F // a = p} := do
  let xs ← arrayProgram s o α (fun i : Fin p.size ↦ p[i]) fun i ↦ do
    let a ← liftComp (Arithmetic.coefficientRead p i.val) _
    pure ⟨a.val, by simpa using a.property⟩
  pure ⟨xs.val, by rw [xs.property]; exact Array.ofFn_getElem⟩

end Fri.Spec.Extractor
