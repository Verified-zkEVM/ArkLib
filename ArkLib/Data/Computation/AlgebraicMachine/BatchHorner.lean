/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.Horner

/-!
# Materialized batch Horner evaluation

The fixed eight-register program traverses points and calls the scalar Horner program
on the saved coefficient list. Each result is allocated at the head of an output list.
Thus the output order is explicitly the reverse of the input point order; no reversal
is performed for free. Coefficients are supplied in descending order.
-/

@[expose] public section

namespace AlgebraicMachine.BatchHorner

abbrev coefficients : Fin 8 := 5
abbrev points : Fin 8 := 6
abbrev output : Fin 8 := 7

/-- Refresh the outer traversal condition. -/
def check : Command 8 := .seq (.primitive (.isNull Horner.test points))
  (.primitive (.boolNot Horner.test Horner.test))

/-- A point read, scalar call, allocation, and cursor advance. -/
def body : Command 8 :=
  .seq (.primitive (.first Horner.point points))
    (.seq (.primitive (.copy Horner.cursor coefficients))
      (.seq (.call Horner.program)
        (.seq (.primitive (.pair output Horner.accumulator output))
          (.seq (.primitive (.second points points)) check))))

/-- Outer traversal with a freshly computed condition. -/
def loop : Command 8 := .while Horner.test body

/-- Initialize the reverse output list and traverse all supplied points. -/
def program : Command 8 :=
  .seq (.primitive (.null output)) (.seq check loop)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Mathematical specification of descending-coefficient evaluation. -/
def evaluate (cs : List F) (x : F) : F := cs.foldl (fun a c => a * x + c) 0

/-- State after refreshing the outer cursor condition. -/
def checked (s : State F 8) (root : Value F) : State F 8 :=
  (s.write Horner.test (.boolean (Horner.nullFlag root))).write Horner.test
    (.boolean (!(Horner.nullFlag root)))

theorem check_executes (s : State F 8) (root : Value F)
    (hp : s.registers points = root) : Executes check s 3 (checked s root) := by
  apply Executes.seq (m := 1) (n := 1)
    (t := s.write Horner.test (.boolean (Horner.nullFlag root)))
  · apply Executes.primitive
    cases root <;> simp [Primitive.eval, hp, Horner.nullFlag]
  · apply Executes.primitive
    simp [Primitive.eval, State.write, checked]

/-- One iteration preserves the input lists and materializes one output cell. -/
theorem body_executes (cs xs : List F) (s : State F 8) (cr out tail : Value F)
    (address : ℕ) (x : F) (ys : List (Value F))
    (hw : s.heap.WellFormed)
    (hc : s.registers coefficients = cr)
    (hp : s.registers points = .pointer address)
    (ho : s.registers output = out)
    (hcs : RepresentsList s.heap cr (cs.map Value.field))
    (hcell : s.heap.cells address = some (.field x, tail))
    (hxs : RepresentsList s.heap tail (xs.map Value.field))
    (hys : RepresentsList s.heap out ys) :
    ∃ t, Executes body s (12 * cs.length + 21) t ∧ t.heap.WellFormed ∧
      t.registers coefficients = cr ∧ t.registers points = tail ∧
      t.registers Horner.test = .boolean (!xs.isEmpty) ∧
      RepresentsList t.heap cr (cs.map Value.field) ∧
      RepresentsList t.heap tail (xs.map Value.field) ∧
      RepresentsList t.heap (t.registers output) (.field (evaluate cs x) :: ys) := by
  let s₁ := s.write Horner.point (.field x)
  let s₂ := s₁.write Horner.cursor cr
  have he₁ : Executes (.primitive (.first Horner.point points)) s 1 s₁ :=
    .primitive (by simp [Primitive.eval, hp, hcell, s₁])
  have he₂ : Executes (.primitive (.copy Horner.cursor coefficients)) s₁ 1 s₂ :=
    .primitive (by simp [Primitive.eval, s₂, s₁, State.write, Function.update,
      coefficients, Horner.point, hc])
  obtain ⟨u, heu, hua, _, huh, huw, huf⟩ := Horner.program_executes cs s₂ cr x hw hcs
    (by simp [s₂, State.write])
    (by simp [s₂, s₁, State.write, Function.update, Horner.point, Horner.cursor])
  have hu5 : u.registers coefficients = cr := by
    simpa [s₂, s₁, State.write, Function.update, coefficients, Horner.cursor,
      Horner.point, hc] using huf coefficients (by decide) (by decide) (by decide) (by decide)
  have hu6 : u.registers points = .pointer address := by
    simpa [s₂, s₁, State.write, Function.update, points, Horner.cursor,
      Horner.point, hp] using huf points (by decide) (by decide) (by decide) (by decide)
  have hu7 : u.registers output = out := by
    simpa [s₂, s₁, State.write, Function.update, output, Horner.cursor,
      Horner.point, ho] using huf output (by decide) (by decide) (by decide) (by decide)
  have huh' : u.heap = s.heap := huh
  let v : State F 8 :=
    ({ u with heap := u.heap.allocate (.field (evaluate cs x)) out } : State F 8).write
      output (.pointer u.heap.next)
  let w := v.write points tail
  let t := checked w tail
  have hev : Executes (.primitive (.pair output Horner.accumulator output)) u 1 v :=
    .primitive (by simp [Primitive.eval, hua, hu7, v, evaluate])
  have hvc : v.heap.cells address = some (.field x, tail) := by
    have hold : u.heap.cells address = some (.field x, tail) := by rw [huh']; exact hcell
    exact ((u.heap.allocate_extends (.field (evaluate cs x)) out).cells_eq address
      (Heap.address_lt_next huw hold)).trans hold
  have hv6 : v.registers points = .pointer address := by
    simp [v, State.write, Function.update, points, output, hu6]
  have hew : Executes (.primitive (.second points points)) v 1 w :=
    .primitive (by simp [Primitive.eval, hv6, hvc, w])
  have het : Executes check w 3 t := check_executes w tail (by simp [w, State.write])
  have hvw : v.heap.WellFormed := Heap.allocate_wellFormed huw _ _
  have hcr : RepresentsList u.heap cr (cs.map Value.field) := by rw [huh']; exact hcs
  have hxr : RepresentsList u.heap tail (xs.map Value.field) := by rw [huh']; exact hxs
  have hyr : RepresentsList u.heap out ys := by rw [huh']; exact hys
  refine ⟨t, ?_, hvw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he' := Executes.seq he₁ (Executes.seq he₂
        (Executes.seq (Executes.call heu) (Executes.seq hev (Executes.seq hew het))))
    have hcost : 1 + (1 + ((12 * cs.length + 7 + 2) +
        (1 + (1 + 3 + 1) + 1) + 1) + 1) + 1 = 12 * cs.length + 21 := by omega
    rw [hcost] at he'
    exact he'
  · simp [t, checked, w, v, State.write, Function.update, coefficients, Horner.test,
      points, output, hu5]
  · simp [t, checked, w, State.write, Function.update, points, Horner.test]
  · simp [t, checked, State.write, Horner.represented_nullFlag hxs]
  · exact hcr.extends huw (u.heap.allocate_extends _ _)
  · exact hxr.extends huw (u.heap.allocate_extends _ _)
  · simpa [t, checked, w, v, State.write, Function.update, output, points, Horner.test]
      using hyr.allocate_cons huw (.field (evaluate cs x))

/-- The output accumulator contains evaluations prepended in traversal order. -/
theorem loop_executes (cs xs : List F) (s : State F 8) (cr root : Value F)
    (ys : List (Value F)) (hw : s.heap.WellFormed)
    (hc : s.registers coefficients = cr) (hp : s.registers points = root)
    (ht : s.registers Horner.test = .boolean (!xs.isEmpty))
    (hcs : RepresentsList s.heap cr (cs.map Value.field))
    (hxs : RepresentsList s.heap root (xs.map Value.field))
    (hys : RepresentsList s.heap (s.registers output) ys) :
    ∃ t, Executes loop s ((12 * cs.length + 22) * xs.length + 1) t ∧
      t.heap.WellFormed ∧ t.registers coefficients = cr ∧ t.registers points = .null ∧
      RepresentsList t.heap cr (cs.map Value.field) ∧
      RepresentsList t.heap (t.registers output)
        (xs.foldl (fun acc x => .field (evaluate cs x) :: acc) ys) := by
  induction xs generalizing s root ys with
  | nil =>
      cases hxs
      exact ⟨s, .whileFalse ht, hw, hc, hp, hcs, hys⟩
  | cons x xs ih =>
      cases hxs with
      | @cons address head tail rest hcell hrest =>
          obtain ⟨u, heu, huw, huc, hup, hut, hucs, huxs, huys⟩ :=
            body_executes cs xs s cr (s.registers output) tail address x ys
              hw hc hp rfl hcs hcell hrest hys
          obtain ⟨t, het, htw, htc, htp, htcs, htys⟩ :=
            ih u tail (.field (evaluate cs x) :: ys) huw huc hup hut hucs huxs huys
          refine ⟨t, ?_, htw, htc, htp, htcs, htys⟩
          have he' := Executes.whileTrue ht heu het
          have hcost : (12 * cs.length + 21) +
              ((12 * cs.length + 22) * xs.length + 1) + 1 =
              (12 * cs.length + 22) * (x :: xs).length + 1 := by
            simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
            omega
          rw [hcost] at he'
          exact he'

/-- Exact batch work, with results represented in reverse point order. All result nodes
are allocated by the program, and the coefficient root and its list remain valid. -/
theorem program_executes (cs xs : List F) (s : State F 8) (cr root : Value F)
    (hw : s.heap.WellFormed) (hc : s.registers coefficients = cr)
    (hp : s.registers points = root)
    (hcs : RepresentsList s.heap cr (cs.map Value.field))
    (hxs : RepresentsList s.heap root (xs.map Value.field)) :
    ∃ t, Executes program s ((12 * cs.length + 22) * xs.length + 7) t ∧
      t.heap.WellFormed ∧ t.registers coefficients = cr ∧ t.registers points = .null ∧
      RepresentsList t.heap cr (cs.map Value.field) ∧
      RepresentsList t.heap (t.registers output)
        (xs.reverse.map (fun x => Value.field (evaluate cs x))) := by
  let u := s.write output .null
  let v := checked u root
  have hep : u.registers points = root := by
    simpa [u, State.write, Function.update, points, output] using hp
  obtain ⟨t, het, htw, htc, htp, htcs, htys⟩ := loop_executes cs xs v cr root [] hw
    (by simpa [v, checked, u, State.write, Function.update, coefficients, output,
      Horner.test] using hc)
    (by simpa [v, checked, State.write, Function.update, points, Horner.test] using hep)
    (by simp [v, checked, State.write, Horner.represented_nullFlag hxs]) hcs hxs
    (by simpa [v, checked, u, State.write, Function.update, output, Horner.test] using
      (RepresentsList.nil (heap := s.heap)))
  refine ⟨t, ?_, htw, htc, htp, htcs, ?_⟩
  · have he' := Executes.seq (Executes.primitive (p := .null output) (s := s) rfl)
        (Executes.seq (check_executes u root hep) het)
    have hcost : 1 + (3 + ((12 * cs.length + 22) * xs.length + 1) + 1) + 1 =
        (12 * cs.length + 22) * xs.length + 7 := by omega
    rw [hcost] at he'
    exact he'
  · have hfold : ∀ (zs : List F) (acc : List (Value F)),
        zs.foldl (fun acc x => .field (evaluate cs x) :: acc) acc =
          zs.reverse.map (fun x => .field (evaluate cs x)) ++ acc := by
      intro zs
      induction zs with
      | nil => intro acc; rfl
      | cons z zs ih =>
          intro acc
          simp [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.append_assoc]
    simpa [hfold] using htys

end AlgebraicMachine.BatchHorner
