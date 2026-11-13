/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Compiled tuple operations

Check the compiler rules and read nested snocs and long appends through ordinary callers.
-/

namespace ArkLibTest.FinTupleCompiledForms

open Fin

open Lean Meta in
/-- Fails unless compiled code runs each snoc and append of `Fin` tuples as its form by one
comparison. -/
def checkCompiledForms : MetaM Unit := do
  let s := Compiler.CSimp.ext.getState (← getEnv)
  for (f, g) in [(``Fin.vconcat, ``Fin.vconcatSnoc), (``Fin.fconcat, ``Fin.fconcatSnoc),
      (``Fin.fconcat₂, ``Fin.fconcat₂Snoc), (``Fin.hconcat, ``Fin.hconcatSnoc),
      (``Fin.fappend, ``Fin.fappendAddCases), (``Fin.fappend₂, ``Fin.fappend₂AddCases),
      (``Fin.happend, ``Fin.happendAddCases)] do
    unless (s.map.find? f).map (·.toDeclName) == some g do
      throwError "compiled code does not run `{f}` as `{g}`"

/-- A tuple of copies of one type, appended to another, is a tuple of that type. -/
theorem vappend_const {m n : ℕ} {α : Sort*} (a : α) (i : Fin (m + n)) :
    vappend (fun _ : Fin m => a) (fun _ : Fin n => a) i = a := by
  refine addCases (fun j => ?_) (fun j => ?_) i
  · exact vappend_left _ _ j
  · exact vappend_right _ _ j

/-- `k` entries, each added by `vconcat`: entry `i` is `i`. -/
def vsnocs : (k : ℕ) → Fin k → ℕ
  | 0 => elim0
  | k + 1 => vconcat (vsnocs k) k

/-- `k` entries, each added by `fconcat`: entry `i` is `i`. -/
def snocs : (k : ℕ) → Fin k → ℕ
  | 0 => elim0
  | k + 1 => fconcat (A := Unit) (F := fun _ => ℕ) (α := fun _ => ()) (β := ()) (snocs k) k

/-- `k` entries, each added by `fconcat₂`: entry `i` is `i`. -/
def snocs₂ : (k : ℕ) → Fin k → ℕ
  | 0 => elim0
  | k + 1 => fconcat₂ (A := Unit) (B := Unit) (F := fun _ _ => ℕ) (α₁ := fun _ => ())
      (β₁ := ()) (α₂ := fun _ => ()) (β₂ := ()) (snocs₂ k) k

/-- The entry types of `k` entries, each added by `hconcat`. -/
def hsnocsType : (k : ℕ) → Fin k → Type
  | 0 => elim0
  | k + 1 => vconcat (hsnocsType k) ℕ

/-- Every entry of `hsnocsType k` is `ℕ`. -/
theorem hsnocsType_eq : ∀ (k : ℕ) (i : Fin k), hsnocsType k i = ℕ
  | 0, i => i.elim0
  | k + 1, i => by
    refine lastCases ?_ (fun j => ?_) i
    · exact vconcat_last _ _
    · exact (vconcat_castSucc _ _ j).trans (hsnocsType_eq k j)

/-- `k` entries, each added by `hconcat`: entry `i` is `i`. -/
def hsnocs : (k : ℕ) → (i : Fin k) → hsnocsType k i
  | 0 => fun i => i.elim0
  | k + 1 => hconcat (hsnocs k) k

/-- An append whose second tuple has `k` entries: entry `i` is `i`. -/
def wide (k : ℕ) : Fin (1 + k) → ℕ :=
  fappend (A := Unit) (F := fun _ => ℕ) (α := fun _ => ()) (β := fun _ => ()) (fun _ => 0)
    (fun j => j.val + 1)

/-- An append by `fappend₂` whose second tuple has `k` entries: entry `i` is `i`. -/
def wide₂ (k : ℕ) : Fin (1 + k) → ℕ :=
  fappend₂ (A := Unit) (B := Unit) (F := fun _ _ => ℕ) (α₁ := fun _ => ()) (β₁ := fun _ => ())
    (α₂ := fun _ => ()) (β₂ := fun _ => ()) (fun _ => 0) (fun j => j.val + 1)

/-- An append by `happend` whose second tuple has `k` entries: entry `i` is `i`. -/
def hwide (k : ℕ) : Fin (1 + k) → ℕ := fun i =>
  cast (vappend_const ℕ i)
    (happend (α := fun _ : Fin 1 => ℕ) (β := fun _ : Fin k => ℕ) (fun _ => 0)
      (fun j => j.val + 1) i)

-- These ordinary callers require generated code, which runs the forms by one comparison.
private def compiledChecks : IO Unit := do
  unless List.ofFn (vsnocs 40) = List.range 40 do
    throw (IO.userError "Incorrect entries of nested `vconcat`")
  unless List.ofFn (snocs 40) = List.range 40 do
    throw (IO.userError "Incorrect entries of nested `fconcat`")
  unless List.ofFn (snocs₂ 40) = List.range 40 do
    throw (IO.userError "Incorrect entries of nested `fconcat₂`")
  unless List.ofFn (fun i => cast (hsnocsType_eq 40 i) (hsnocs 40 i)) = List.range 40 do
    throw (IO.userError "Incorrect entries of nested `hconcat`")
  unless List.ofFn (wide 40) = List.range 41 do
    throw (IO.userError "Incorrect entries of a long `fappend`")
  unless List.ofFn (wide₂ 40) = List.range 41 do
    throw (IO.userError "Incorrect entries of a long `fappend₂`")
  unless List.ofFn (hwide 40) = List.range 41 do
    throw (IO.userError "Incorrect entries of a long `happend`")
  IO.println "Compiled tuple checks passed."

-- The registrations are checked first, so that a missing one fails at once instead of running
-- the recursive definitions.
/-- info: Compiled tuple checks passed. -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  checkCompiledForms
  compiledChecks

end ArkLibTest.FinTupleCompiledForms
