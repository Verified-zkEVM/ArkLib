/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.Command
public import ArkLib.Data.Computation.AlgebraicMachine.Representation
public import Lean.Elab.Tactic.Omega

/-!
# Horner evaluation by a materialized list traversal

Coefficients are supplied in descending order. Registers zero through four hold the
list cursor, evaluation point, accumulator, coefficient scratch, and loop test.
Registers five through seven are available to callers. The point and caller registers
are preserved, and no heap cell is allocated or changed.
-/

@[expose] public section

namespace AlgebraicMachine.Horner

abbrev cursor : Fin 8 := 0
abbrev point : Fin 8 := 1
abbrev accumulator : Fin 8 := 2
abbrev coefficient : Fin 8 := 3
abbrev test : Fin 8 := 4

/-- Refresh the Boolean loop condition by inspecting just the cursor atom. -/
def check : Command 8 := .seq (.primitive (.isNull test cursor))
  (.primitive (.boolNot test test))

/-- One Horner iteration, with the next condition explicitly computed. -/
def body : Command 8 :=
  .seq (.primitive (.first coefficient cursor))
    (.seq (.primitive (.fieldMul accumulator accumulator point))
      (.seq (.primitive (.fieldAdd accumulator accumulator coefficient))
        (.seq (.primitive (.second cursor cursor)) check)))

/-- The loop expects a freshly computed condition in the test register. -/
def loop : Command 8 := .while test body

/-- Traverse with the supplied initial accumulator. -/
def checkedLoop : Command 8 := .seq check loop

/-- The closed evaluation program initializes its accumulator to zero. -/
def program : Command 8 := .seq (.primitive (.fieldZero accumulator)) checkedLoop

variable {F : Type*} [Field F] [DecidableEq F]

/-- Proof-side description of the cursor test, not a program primitive. -/
def nullFlag : Value F → Bool
  | .null => true
  | _ => false

/-- The state after refreshing the loop test. -/
def checked (s : State F 8) (root : Value F) : State F 8 :=
  (s.write test (.boolean (nullFlag root))).write test (.boolean (!(nullFlag root)))

/-- The state after one iteration, retaining the literal sequence of register writes. -/
def advanced (s : State F 8) (c z x : F) (tail : Value F) : State F 8 :=
  checked ((((s.write coefficient (.field c)).write accumulator (.field (z * x))).write
    accumulator (.field (z * x + c))).write cursor tail) tail

/-- Every register outside the four mutable slots is preserved. -/
def Preserves (s t : State F 8) : Prop :=
  ∀ j, j ≠ cursor → j ≠ accumulator → j ≠ coefficient → j ≠ test →
    t.registers j = s.registers j

theorem check_executes (s : State F 8) (root : Value F)
    (hc : s.registers cursor = root) : Executes check s 3 (checked s root) := by
  apply Executes.seq (m := 1) (n := 1)
    (t := s.write test (.boolean (nullFlag root)))
  · apply Executes.primitive
    cases root <;> simp [Primitive.eval, hc, nullFlag]
  · apply Executes.primitive
    simp [Primitive.eval, State.write, checked]

omit [DecidableEq F] in
theorem advanced_preserves (s : State F 8) (c z x : F) (tail : Value F) :
    Preserves s (advanced s c z x tail) := by
  intro j hj₀ hj₂ hj₃ hj₄
  simp [advanced, checked, State.write, Function.update, hj₀, hj₂, hj₃, hj₄]

omit [Field F] [DecidableEq F] in
theorem checked_preserves (s : State F 8) (root : Value F) :
    Preserves s (checked s root) := by
  intro j _ _ _ hj
  simp [checked, State.write, Function.update, hj]

theorem body_executes (s : State F 8) (address : ℕ) (c z x : F) (tail : Value F)
    (hc : s.registers cursor = .pointer address)
    (hp : s.registers point = .field x)
    (ha : s.registers accumulator = .field z)
    (hh : s.heap.cells address = some (.field c, tail)) :
    Executes body s 11 (advanced s c z x tail) := by
  let s₁ := s.write coefficient (.field c)
  let s₂ := s₁.write accumulator (.field (z * x))
  let s₃ := s₂.write accumulator (.field (z * x + c))
  let s₄ := s₃.write cursor tail
  refine Executes.seq (m := 1) (n := 9) (t := s₁) (Executes.primitive ?_)
    (Executes.seq (m := 1) (n := 7) (t := s₂) (Executes.primitive ?_)
      (Executes.seq (m := 1) (n := 5) (t := s₃) (Executes.primitive ?_)
        (Executes.seq (m := 1) (n := 3) (t := s₄) (Executes.primitive ?_) ?_)))
  · simp [s₁, Primitive.eval, hc, hh]
  · simp [s₂, s₁, Primitive.eval, State.write, Function.update, hp, ha,
      accumulator, coefficient, point]
  · simp [s₃, s₂, s₁, Primitive.eval, State.write, Function.update, accumulator, coefficient]
  · simp [s₄, s₃, s₂, s₁, Primitive.eval, State.write, Function.update, hc, hh,
      cursor, accumulator, coefficient]
  · exact check_executes s₄ tail (by simp [s₄, State.write])

omit [Field F] [DecidableEq F] in
theorem represented_nullFlag {h : Heap F} {root : Value F} {xs : List F}
    (hr : RepresentsList h root (xs.map Value.field)) :
    nullFlag root = xs.isEmpty := by
  cases xs with
  | nil => cases hr; rfl
  | cons c cs => cases hr; rfl

/-- The loop terminates with an arbitrary accumulator; the exact cost includes all tests
and sequence dispatches. List interpretation is used solely in this specification. -/
theorem loop_executes (xs : List F) (s : State F 8) (root : Value F) (z x : F)
    (hr : RepresentsList s.heap root (xs.map Value.field))
    (hc : s.registers cursor = root) (hp : s.registers point = .field x)
    (ha : s.registers accumulator = .field z)
    (ht : s.registers test = .boolean (!xs.isEmpty)) :
    ∃ t, Executes loop s (12 * xs.length + 1) t ∧
      t.registers accumulator = .field (xs.foldl (fun a c => a * x + c) z) ∧
      t.registers cursor = .null ∧ t.heap = s.heap ∧ Preserves s t := by
  induction xs generalizing s root z with
  | nil =>
      cases hr
      refine ⟨s, Executes.whileFalse ht, ha, hc, rfl, ?_⟩
      intro j _ _ _ _
      rfl
  | cons c cs ih =>
      cases hr with
      | @cons address head tail rest hcell hrest =>
          let mid := advanced s c z x tail
          have hm : Executes body s 11 mid := body_executes s address c z x tail hc hp ha hcell
          have hmacc : mid.registers accumulator = .field (z * x + c) := by
            simp [mid, advanced, checked, State.write, Function.update, accumulator, cursor, test]
          have hmcur : mid.registers cursor = tail := by
            simp [mid, advanced, checked, State.write, Function.update, cursor, test]
          have hmpoint : mid.registers point = .field x :=
            (advanced_preserves s c z x tail point (by decide) (by decide)
              (by decide) (by decide)).trans hp
          have hmtest : mid.registers test = .boolean (!cs.isEmpty) := by
            simp [mid, advanced, checked, State.write, represented_nullFlag hrest]
          obtain ⟨t, he, hacc, hcur, hheap, hframe⟩ :=
            ih mid tail (z * x + c) hrest hmcur hmpoint hmacc hmtest
          refine ⟨t, ?_, hacc, hcur, hheap, ?_⟩
          · have he' := Executes.whileTrue ht hm he
            have hcost : 11 + (12 * cs.length + 1) + 1 = 12 * (c :: cs).length + 1 := by
              simp only [List.length_cons]
              omega
            rw [hcost] at he'
            exact he'
          · intro j hj₀ hj₂ hj₃ hj₄
            exact (hframe j hj₀ hj₂ hj₃ hj₄).trans
              (advanced_preserves s c z x tail j hj₀ hj₂ hj₃ hj₄)

/-- Initial condition refresh costs four steps including its sequence dispatch. -/
theorem checkedLoop_executes (xs : List F) (s : State F 8) (root : Value F) (z x : F)
    (hr : RepresentsList s.heap root (xs.map Value.field))
    (hc : s.registers cursor = root) (hp : s.registers point = .field x)
    (ha : s.registers accumulator = .field z) :
    ∃ t, Executes checkedLoop s (12 * xs.length + 5) t ∧
      t.registers accumulator = .field (xs.foldl (fun a c => a * x + c) z) ∧
      t.registers cursor = .null ∧ t.heap = s.heap ∧ Preserves s t := by
  have hframe := checked_preserves s root
  obtain ⟨t, he, hacc, hcur, hheap, hkeep⟩ := loop_executes xs (checked s root) root z x hr
    (by simpa [checked, State.write, Function.update, cursor, test] using hc)
    ((hframe point (by decide) (by decide) (by decide) (by decide)).trans hp)
    (by simpa [checked, State.write, Function.update, accumulator, test] using ha)
    (by simp [checked, State.write, represented_nullFlag hr])
  refine ⟨t, ?_, hacc, hcur, hheap, ?_⟩
  · have hcost : 3 + (12 * xs.length + 1) + 1 = 12 * xs.length + 5 := by omega
    have he' := Executes.seq (check_executes s root hc) he
    rw [hcost] at he'
    exact he'
  · intro j hj₀ hj₂ hj₃ hj₄
    exact (hkeep j hj₀ hj₂ hj₃ hj₄).trans (hframe j hj₀ hj₂ hj₃ hj₄)

/-- Horner's complete program has exact affine operational cost and preserves its heap
and all registers outside the four specified mutable slots. -/
theorem program_executes (xs : List F) (s : State F 8) (root : Value F) (x : F)
    (hw : s.heap.WellFormed)
    (hr : RepresentsList s.heap root (xs.map Value.field))
    (hc : s.registers cursor = root) (hp : s.registers point = .field x) :
    ∃ t, Executes program s (12 * xs.length + 7) t ∧
      t.registers accumulator = .field (xs.foldl (fun a c => a * x + c) 0) ∧
      t.registers cursor = .null ∧ t.heap = s.heap ∧ t.heap.WellFormed ∧ Preserves s t := by
  obtain ⟨t, he, hacc, hcur, hheap, hframe⟩ :=
    checkedLoop_executes xs (s.write accumulator (.field 0)) root 0 x hr
      (by simpa [State.write, Function.update, cursor, accumulator] using hc)
      (by simpa [State.write, Function.update, point, accumulator] using hp)
      (by simp [State.write])
  refine ⟨t, ?_, hacc, hcur, hheap, ?_, ?_⟩
  · have hcost : 1 + (12 * xs.length + 5) + 1 = 12 * xs.length + 7 := by omega
    have he' := Executes.seq
      (Executes.primitive (p := .fieldZero accumulator) (s := s) rfl) he
    rw [hcost] at he'
    exact he'
  · rw [hheap]
    exact hw
  · intro j hj₀ hj₂ hj₃ hj₄
    simpa [State.write, Function.update, hj₂] using hframe j hj₀ hj₂ hj₃ hj₄

end AlgebraicMachine.Horner
