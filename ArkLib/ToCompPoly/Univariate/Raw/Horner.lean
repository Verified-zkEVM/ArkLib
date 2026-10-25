/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module
public import CompPoly.Univariate.Raw.Ops
import Mathlib.Data.List.Induction
-- The bridge unfolds the pinned package evaluator, whose body is not exposed.
import all CompPoly.Univariate.Raw.Ops
/-!
# Seeded Horner evaluation with shared monadic control

Read the highest stored coefficient once, then traverse lower indices in reverse order. The
operation callbacks share one tail-recursive driver between ordinary evaluation and arithmetic
instrumentation. No reverse list or extra coefficient array is built by the runtime loop.

The pure evaluator preserves the package evaluator's right-multiplication order over arbitrary
semirings. Array reads, length and natural-number control are distinct from field operations.
-/

@[expose] public section

namespace CompPoly.CPolynomial.Raw
universe u v
variable {R : Type u} {m : Type u → Type v} [Monad m]

/-- Traverse lower indices from n-1 to zero using an existing accumulator. The arithmetic
interpreter profiles this same loop, so its body remains available to that owner. -/
@[specialize]
def hornerLoopM (read : Nat → m R) (mul add : R → R → m R) (x : R) :
    Nat → R → m R
  | 0, acc => pure acc
  | n + 1, acc => do
    let coefficient ← read n
    let product ← mul acc x
    let next ← add product coefficient
    hornerLoopM read mul add x n next

/-- Evaluate with explicit coefficient/operation callbacks, seeding a nonempty input at its last
coefficient. Empty input returns zero without invoking a callback. -/
@[inline]
def evalHornerM [Zero R] (read : Nat → m R) (mul add : R → R → m R)
    (length : Nat) (x : R) : m R :=
  match length with
  | 0 => pure 0
  | n + 1 => do
    let seed ← read n
    hornerLoopM read mul add x n seed

private theorem hornerLoopM_congr_read
    (left right : Nat → m R) (mul add : R → R → m R) (x : R) (n : Nat) (acc : R)
    (h : ∀ i, i < n → left i = right i) :
    hornerLoopM left mul add x n acc = hornerLoopM right mul add x n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [hornerLoopM]
    rw [h n (Nat.lt_succ_self n)]
    congr 1
    funext coefficient
    congr 1
    funext product
    congr 1
    funext next
    exact ih next (fun i hi => h i (by omega))

/-- Only the declared coefficient indices affect evaluation, including callback effects. -/
theorem evalHornerM_congr_read [Zero R]
    (left right : Nat → m R) (mul add : R → R → m R) (length : Nat) (x : R)
    (h : ∀ i, i < length → left i = right i) :
    evalHornerM left mul add length x = evalHornerM right mul add length x := by
  cases length with
  | zero => rfl
  | succ n =>
    simp only [evalHornerM]
    rw [h n (Nat.lt_succ_self n)]
    congr 1
    funext seed
    exact hornerLoopM_congr_read left right mul add x n seed (fun i hi => h i (by omega))

/-- The ordinary array evaluator uses the shared driver with its Id interpretation. -/
@[inline]
def evalHornerSeeded [Zero R] [Mul R] [Add R] (x : R) (p : Array R) : R :=
  Id.run (evalHornerM (m := Id) (fun i => p[i]?.getD 0)
    (fun a b => a * b) (fun a b => a + b) p.size x)

private theorem array_push_induction {P : Array R → Prop}
    (empty : P #[]) (push : ∀ p a, P p → P (p.push a)) (p : Array R) : P p := by
  rcases p with ⟨xs⟩
  induction xs using List.reverseRecOn with
  | nil => exact empty
  | append_singleton xs x ih =>
    simpa [Array.push, List.concat_eq_append] using push (Array.mk xs) x ih

private theorem hornerLoopM_array_foldr [Zero R] [Mul R] [Add R]
    (x : R) (p : Array R) (acc : R) :
    hornerLoopM (m := Id) (fun i => p[i]?.getD 0)
      (fun a b => a * b) (fun a b => a + b) x p.size acc =
      p.foldr (fun coefficient acc => acc * x + coefficient) acc := by
  induction p using array_push_induction generalizing acc with
  | empty => rfl
  | @push p a ih =>
    simp only [Array.size_push, hornerLoopM]
    change hornerLoopM (m := Id) (fun i => (p.push a)[i]?.getD 0)
      (fun a b => a * b) (fun a b => a + b) x p.size
      (acc * x + (p.push a)[p.size]?.getD 0) = _
    have hread : ∀ i, i < p.size → (p.push a)[i]?.getD 0 = p[i]?.getD 0 := by
      intro i hi
      simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]
    rw [show (p.push a)[p.size]?.getD 0 = a by simp,
      hornerLoopM_congr_read (m := Id) (fun i => (p.push a)[i]?.getD 0) (fun i => p[i]?.getD 0)
        _ _ _ _ _ hread, ih, Array.foldr_push' rfl]

/-- Seeding with the highest coefficient preserves the existing semiring evaluation answer. -/
theorem evalHornerSeeded_eq_evalHorner [Semiring R] (x : R) (p : Array R) :
    evalHornerSeeded x p = evalHorner x p := by
  change evalHornerSeeded x p = p.foldr (fun coefficient acc => acc * x + coefficient) 0
  induction p using array_push_induction with
  | empty => rfl
  | @push p a ih =>
    simp only [evalHornerSeeded, Array.size_push, evalHornerM]
    change hornerLoopM (m := Id) (fun i => (p.push a)[i]?.getD 0)
      (fun a b => a * b) (fun a b => a + b) x p.size ((p.push a)[p.size]?.getD 0) = _
    have hread : ∀ i, i < p.size → (p.push a)[i]?.getD 0 = p[i]?.getD 0 := by
      intro i hi
      simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]
    rw [show (p.push a)[p.size]?.getD 0 = a by simp,
      hornerLoopM_congr_read (m := Id) (fun i => (p.push a)[i]?.getD 0) (fun i => p[i]?.getD 0)
        _ _ _ _ _ hread, hornerLoopM_array_foldr, Array.foldr_push' rfl]
    simp
end CompPoly.CPolynomial.Raw
