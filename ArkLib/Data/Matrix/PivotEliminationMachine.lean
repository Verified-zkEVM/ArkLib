/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.RowReductionMachine

/-!
# Composed elimination of one target entry

Materialized pivot and target rows are scanned together at the supplied column. Missing entries
and a zero pivot reject explicitly. Inversion, negation and multiplication compute the elimination
factor; every subsequent row transition is an actual `RowReductionMachine.Step`, including its
reversal. Equal-length inputs produce the target row with the chosen entry zeroed. Unequal lengths
are rejected by the delegated row machine, even if both selected entries existed.

This is the per-target kernel for a later column driver. Pivot search, extraction/writeback,
iteration over target rows, and output-row-list construction are separate obligations. It is not a
column loop or full solver. Inputs and initial lookup cursors are already materialized. The inner
machine charges its own dispatch; lifting its rule does not introduce a second uncharged dispatch.
Costs count internal row-return and external result events separately. Host fuel bookkeeping and
field bit costs remain outside this abstract primitive model.
-/

@[expose] public section

namespace Matrix.PivotEliminationMachine

/-- Charges extend the row machine with inversion, negation, equality, and index operations. -/
@[ext] structure Cost where
  row : RowReductionMachine.Cost
  inversions : ℕ
  negations : ℕ
  equalities : ℕ
  natural : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b =>
  ⟨a.row + b.row, a.inversions + b.inversions, a.negations + b.negations,
    a.equalities + b.equalities, a.natural + b.natural⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.row + b.row, a.inversions + b.inversions, a.negations + b.negations,
      a.equalities + b.equalities, a.natural + b.natural⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; simp

/-- Preserve every primitive charge of a delegated row transition. -/
def embed (c : RowReductionMachine.Cost) : Cost := ⟨c, 0, 0, 0, 0⟩
@[simp] theorem embed_zero : embed 0 = 0 := rfl
@[simp] theorem embed_add (c d : RowReductionMachine.Cost) :
    embed (c + d) = embed c + embed d := rfl

private theorem cost_add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Two cell reads, index read/test/decrement, and three cursor/index writes. -/
def seekCost : Cost := ⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 2⟩
/-- Read two selected cells and the index; test zero and write both scalar entries. -/
def hitCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 1⟩
/-- Read both cursors and emit invalid-index rejection. -/
def missingCost : Cost := ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩
/-- Read and compare the pivot with zero. -/
def checkCost : Cost := ⟨⟨0, 0, 1, 1, 0⟩, 0, 0, 1, 0⟩
/-- The zero-pivot branch additionally emits rejection. -/
def zeroCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 1, 0⟩
/-- Read the pivot and write its inverse. -/
def inverseCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 1, 0, 0, 0⟩
/-- Read the target entry and write its negation. -/
def negateCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 1, 0, 0⟩
/-- Read two scalars, multiply/write factor, read row roots, initialize reversed-output pointer. -/
def factorCost : Cost := ⟨⟨0, 1, 1, 6, 0⟩, 0, 0, 0, 0⟩
/-- Read the delegated result handle and emit the external tagged result. -/
def returnCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩

/-- Fixed lookup, scalar and delegated-row phases. Original rows are retained for the row call. -/
inductive Configuration (F : Type*) where
  | lookup (pivot target pcursor tcursor : List F) (index : ℕ)
  | check (pivot target : List F) (p e : F)
  | inverse (pivot target : List F) (p e : F)
  | negate (pivot target : List F) (e inverse : F)
  | factor (pivot target : List F) (negative inverse : F)
  | row (factor : F) (inner : RowReductionMachine.Configuration F)
  | done (target : List F)
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent closed rules, including genuine inner row-machine transitions. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | missingPivot {p t ts i} : Step (.lookup p t [] ts i) missingCost .rejected
  | missingTarget {p t x xs i} : Step (.lookup p t (x :: xs) [] i) missingCost .rejected
  | hit {p t x xs y ys} : Step (.lookup p t (x :: xs) (y :: ys) 0) hitCost (.check p t x y)
  | seek {p t x xs y ys i} : Step (.lookup p t (x :: xs) (y :: ys) (i + 1)) seekCost
      (.lookup p t xs ys i)
  | zero {p t e} : Step (.check p t 0 e) zeroCost .rejected
  | nonzero {p t x e} (hx : x ≠ 0) : Step (.check p t x e) checkCost (.inverse p t x e)
  | inverse {p t x e} : Step (.inverse p t x e) inverseCost (.negate p t e x⁻¹)
  | negate {p t e inv} : Step (.negate p t e inv) negateCost (.factor p t (-e) inv)
  | factor {p t neg inv} : Step (.factor p t neg inv) factorCost
      (.row (neg * inv) (.scan t p []))
  | row {a s c t} (h : RowReductionMachine.Step a s c t) : Step (.row a s) (embed c) (.row a t)
  | returned {a out} : Step (.row a (.done out)) returnCost (.done out)
  | rejected {a} : Step (.row a .rejected) returnCost .rejected

/-- Executable dispatch calls only the inner one-transition interpreter. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .done _ | .rejected => none
  | .lookup _ _ [] _ _ | .lookup _ _ (_ :: _) [] _ => some (.rejected, missingCost)
  | .lookup p t (x :: _) (y :: _) 0 => some (.check p t x y, hitCost)
  | .lookup p t (_ :: xs) (_ :: ys) (i + 1) => some (.lookup p t xs ys i, seekCost)
  | .check p t x e => if x = 0 then some (.rejected, zeroCost)
      else some (.inverse p t x e, checkCost)
  | .inverse p t x e => some (.negate p t e x⁻¹, inverseCost)
  | .negate p t e inv => some (.factor p t (-e) inv, negateCost)
  | .factor p t neg inv => some (.row (neg * inv) (.scan t p []), factorCost)
  | .row _ (.done out) => some (.done out, returnCost)
  | .row _ .rejected => some (.rejected, returnCost)
  | .row a inner =>
      match RowReductionMachine.step a inner with
      | none => none
      | some (next, cost) => some (.row a next, embed cost)

/-- Every independent transition is executed with its exact charge. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | row h => cases h <;> rfl
  | nonzero hx => simp [step, hx]
  | zero => simp [step]
  | _ => rfl

/-- Every executable dispatch is justified by an independent rule. -/
theorem step_sound {s t : Configuration F} {c : Cost}
    (h : step s = some (t, c)) : Step s c t := by
  cases s with
  | done out => simp [step] at h
  | rejected => simp [step] at h
  | lookup p t xs ys i =>
      cases xs with
      | nil => cases h; exact Step.missingPivot
      | cons x xs =>
          cases ys with
          | nil => cases h; exact Step.missingTarget
          | cons y ys =>
              cases i with
              | zero => cases h; exact Step.hit
              | succ i => cases h; exact Step.seek
  | check p t x e =>
      by_cases hx : x = 0
      · subst x; simp only [step] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.zero
      · simp only [step, if_neg hx, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.nonzero hx
  | inverse p t x e => cases h; exact Step.inverse
  | negate p t e inv => cases h; exact Step.negate
  | factor p t neg inv => cases h; exact Step.factor
  | row a inner =>
      cases inner with
      | done out => cases h; exact Step.returned
      | rejected => cases h; exact Step.rejected
      | scan ts ss rev =>
          cases ts <;> cases ss <;> cases h
          · exact Step.row RowReductionMachine.Step.beginReverse
          · exact Step.row RowReductionMachine.Step.shortTarget
          · exact Step.row RowReductionMachine.Step.shortSource
          · exact Step.row RowReductionMachine.Step.take
      | multiply ts ss rev x y => cases h; exact Step.row RowReductionMachine.Step.multiply
      | add ts ss rev x prod => cases h; exact Step.row RowReductionMachine.Step.add
      | reverse xs out =>
          cases xs with
          | nil => cases h; exact Step.row RowReductionMachine.Step.emit
          | cons x xs => cases h; exact Step.row RowReductionMachine.Step.reverse

omit [DecidableEq F] in
/-- Both successor and primitive charge are determined by the current phase. -/
theorem Step.deterministic {s t u : Configuration F} {c d : Cost}
    (h : Step s c t) (h' : Step s d u) : t = u ∧ c = d := by
  classical
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- Finite composed transition trace. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

omit [DecidableEq F] in
/-- Trace composition accounts for every inner charge. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace n s c u) (h' : Trace m u d t) : Trace (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

omit [DecidableEq F] in
/-- Lift every actual inner transition; no whole-row evaluation is used as a primitive. -/
theorem Trace.row {a : F} {n : ℕ} {s t : RowReductionMachine.Configuration F}
    {c : RowReductionMachine.Cost} (h : RowReductionMachine.Trace a n s c t) :
    Trace n (.row a s) (embed c) (.row a t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih => exact Trace.cons (Step.row head) ih

/-- Fuel execution returns the reached phase and charges, including partial work on exhaustion. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel n t
          (result.1, c + result.2)

/-- Every execution has an independent trace with identical costs. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel reproduces its state and charge. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n s c t) : runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Exact successful lookup cost at zero-based index `j`. -/
def lookupCost (j : ℕ) : Cost := ⟨⟨0, 0, j + 1, 6 * j + 5, 0⟩, 0, 0, 0, 2 * j + 1⟩

/-- Fixed scalar setup charges. -/
def setupCost : Cost := checkCost + (inverseCost + (negateCost + factorCost))

/-- Exact valid-input cost: linear in row length and selected column, with one field inverse. -/
def eliminationCost (n j : ℕ) : Cost :=
  ⟨⟨n, n + 1, 4 * n + j + 8, 19 * n + 6 * j + 22, 2⟩, 1, 1, 1, 2 * j + 1⟩

/-- The scalar computed by the explicit inversion/negation/multiplication phases. -/
def eliminationFactor (entry pivot : F) : F := -entry * pivot⁻¹

omit [DecidableEq F] in
/-- Successful lookup is proved using actual list entries, with no default value. -/
theorem lookup_trace (pivot target ps ts : List F) (j : ℕ) (p e : F)
    (hp : ps[j]? = some p) (he : ts[j]? = some e) :
    Trace (j + 1) (.lookup pivot target ps ts j) (lookupCost j) (.check pivot target p e) := by
  induction j generalizing ps ts with
  | zero =>
      cases ps with
      | nil => simp at hp
      | cons x xs =>
          cases ts with
          | nil => simp at he
          | cons y ys =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp he
              subst p; subst e
              simpa [lookupCost, hitCost] using
                Trace.cons (Step.hit (p := pivot) (t := target) (x := x) (xs := xs)
                  (y := y) (ys := ys)) (Trace.nil _)
  | succ j ih =>
      cases ps with
      | nil => simp at hp
      | cons x xs =>
          cases ts with
          | nil => simp at he
          | cons y ys =>
              simp only [List.getElem?_cons_succ] at hp he
              simpa [lookupCost, seekCost, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using Trace.cons Step.seek (ih xs ys hp he)

omit [DecidableEq F] in
/-- Scalar phases really execute the charged field operations before entering the row code. -/
theorem setup_trace (pivot target : List F) (p e : F) (hp : p ≠ 0) :
    Trace 4 (.check pivot target p e) setupCost
      (.row (eliminationFactor e p) (.scan target pivot [])) := by
  simpa [setupCost, eliminationFactor] using
    Trace.cons (Step.nonzero hp) (Trace.cons Step.inverse
      (Trace.cons Step.negate (Trace.cons Step.factor (Trace.nil _))))

/-- Complete valid-input execution composes lookup, scalar setup, every row step, and return. -/
theorem elimination_runFuel (pivot target : List F) (j : ℕ) (p e : F)
    (hp : pivot[j]? = some p) (he : target[j]? = some e) (hp0 : p ≠ 0)
    (hlen : target.length = pivot.length) :
    runFuel (4 * target.length + j + 8) (.lookup pivot target pivot target j) =
      (.done (List.zipWith (fun t s => t + eliminationFactor e p * s) target pivot),
        eliminationCost target.length j) := by
  have hrow := Trace.row
    (RowReductionMachine.scan_trace (eliminationFactor e p) target pivot [] hlen)
  have hreturn := Trace.cons (Step.returned (a := eliminationFactor e p)
    (out := List.zipWith (fun t s => t + eliminationFactor e p * s) target pivot)) (Trace.nil _)
  have h := (lookup_trace pivot target pivot target j p e hp he).trans
    ((setup_trace pivot target p e hp0).trans (hrow.trans hreturn))
  have hsteps : j + 1 + (4 + (4 * target.length + 0 + 2 + (0 + 1))) =
      4 * target.length + j + 8 := by omega
  have hcost : lookupCost j + (setupCost +
      (embed (RowReductionMachine.scanCost target.length 0) + (returnCost + 0))) =
        eliminationCost target.length j := by
    ext <;>
      simp [eliminationCost, lookupCost, setupCost, checkCost, inverseCost, negateCost,
        factorCost, returnCost, embed, RowReductionMachine.scanCost] <;> omega
  have h' := h.runFuel_eq
  simp only [List.length_nil] at h'
  rw [hsteps, hcost] at h'
  exact h'

/-- If both selected entries exist but row lengths differ, the actual inner rejection propagates. -/
theorem unequal_runFuel (pivot target : List F) (j : ℕ) (p e : F)
    (hp : pivot[j]? = some p) (he : target[j]? = some e) (hp0 : p ≠ 0)
    (hlen : target.length ≠ pivot.length) :
    runFuel (j + 1 + (4 + (3 * min target.length pivot.length + 1 + 1)))
      (.lookup pivot target pivot target j) =
      (.rejected, lookupCost j + (setupCost +
        (embed (RowReductionMachine.rejectionCost (min target.length pivot.length)) +
          returnCost))) := by
  have hrow := Trace.row
    (RowReductionMachine.rejection_trace (eliminationFactor e p) target pivot [] hlen)
  have h := (lookup_trace pivot target pivot target j p e hp he).trans
    ((setup_trace pivot target p e hp0).trans
      (hrow.trans (Trace.cons Step.rejected (Trace.nil _))))
  simpa using h.runFuel_eq

/-- A selected zero pivot rejects before inversion or row arithmetic. -/
theorem zeroPivot_runFuel (pivot target : List F) (j : ℕ) (e : F)
    (hp : pivot[j]? = some 0) (he : target[j]? = some e) :
    runFuel (j + 2) (.lookup pivot target pivot target j) =
      (.rejected, lookupCost j + zeroCost) := by
  have h := (lookup_trace pivot target pivot target j 0 e hp he).trans
    (Trace.cons Step.zero (Trace.nil _))
  simpa [Nat.add_assoc] using h.runFuel_eq

/-- Lookup rejection after `k` consumed pairs; no field operation has yet executed. -/
def missingLookupCost (k : ℕ) : Cost := ⟨⟨0, 0, k + 1, 6 * k + 2, 1⟩, 0, 0, 0, 2 * k⟩

omit [DecidableEq F] in
/-- Invalid indices terminate at the first exhausted row cursor, without using a default value. -/
theorem missing_lookup_trace (pivot target ps ts : List F) (j : ℕ)
    (hmissing : ps[j]? = none ∨ ts[j]? = none) :
    Trace (min j (min ps.length ts.length) + 1) (.lookup pivot target ps ts j)
      (missingLookupCost (min j (min ps.length ts.length))) .rejected := by
  induction ps generalizing ts j with
  | nil =>
      simpa [missingLookupCost, missingCost] using
        Trace.cons (Step.missingPivot (p := pivot) (t := target) (ts := ts) (i := j)) (Trace.nil _)
  | cons p ps ih =>
      cases ts with
      | nil =>
          simpa [missingLookupCost, missingCost] using
            Trace.cons (Step.missingTarget (p := pivot) (t := target) (x := p)
              (xs := ps) (i := j)) (Trace.nil _)
      | cons e ts =>
          cases j with
          | zero => simp at hmissing
          | succ j =>
              have h := Trace.cons (Step.seek (x := p) (y := e))
                (ih ts j (by simpa using hmissing))
              simpa [missingLookupCost, seekCost, Nat.mul_add, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using h

/-- Invalid lookup has an explicit terminating rejection and a linear traversal cost. -/
theorem missing_runFuel (pivot target : List F) (j : ℕ)
    (hmissing : pivot[j]? = none ∨ target[j]? = none) :
    runFuel (min j (min pivot.length target.length) + 1)
      (.lookup pivot target pivot target j) =
      (.rejected, missingLookupCost (min j (min pivot.length target.length))) :=
  (missing_lookup_trace pivot target pivot target j hmissing).runFuel_eq

omit [DecidableEq F] in
/-- A nonzero pivot cancels the selected target entry exactly. -/
theorem eliminated_entry (entry pivot : F) (hp : pivot ≠ 0) :
    entry + eliminationFactor entry pivot * pivot = 0 := by
  simp [eliminationFactor, mul_assoc, inv_mul_cancel₀ hp]

omit [DecidableEq F] in
/-- The produced row has zero at the selected column, even if that entry was already zero. -/
theorem output_entry_zero (pivot target : List F) (j : ℕ)
    (hjP : j < pivot.length) (hjT : j < target.length) (hp : pivot[j] ≠ 0) :
    (List.zipWith (fun t s => t + eliminationFactor target[j] pivot[j] * s) target pivot)[j]'(by
      simp only [List.length_zipWith]; omega) = 0 := by
  rw [List.getElem_zipWith]
  exact eliminated_entry _ _ hp

/-- Canonical matrix update specified by this per-target elimination kernel. -/
def eliminateMatrix {m n : Type*} [DecidableEq m]
    (A : Matrix m n F) (t s : m) (j : n) : Matrix m n F :=
  RowReductionMachine.addMultiple A t s (eliminationFactor (A t j) (A s j))

/-- Actual materialized matrix rows execute to the specified updated target row. -/
theorem elimination_runFuel_matrix {m : Type*} {n : ℕ} [DecidableEq m]
    (A : Matrix m (Fin n) F) (t s : m) (j : Fin n) (hp : A s j ≠ 0) :
    runFuel (4 * n + j.val + 8)
      (.lookup (List.ofFn (A s)) (List.ofFn (A t))
        (List.ofFn (A s)) (List.ofFn (A t)) j.val) =
      (.done (List.ofFn (eliminateMatrix A t s j t)), eliminationCost n j.val) := by
  have h := elimination_runFuel (List.ofFn (A s)) (List.ofFn (A t)) j.val
    (A s j) (A t j) (by simp) (by simp) hp (by simp)
  have hrows : List.zipWith (fun x y => x + eliminationFactor (A t j) (A s j) * y)
      (List.ofFn (A t)) (List.ofFn (A s)) = List.ofFn (eliminateMatrix A t s j t) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi
      simp [eliminateMatrix, RowReductionMachine.addMultiple]
  simpa [hrows] using h

omit [DecidableEq F] in
/-- The specified matrix operation zeros the chosen column in the target row. -/
theorem eliminateMatrix_entry {m n : Type*} [DecidableEq m]
    (A : Matrix m n F) (t s : m) (j : n) (hp : A s j ≠ 0) :
    eliminateMatrix A t s j t j = 0 := by
  simp only [eliminateMatrix, RowReductionMachine.addMultiple, Matrix.updateRow_self]
  exact eliminated_entry _ _ hp

omit [DecidableEq F] in
/-- Augmented-system semantics: apply the same scalar row operation to the right-hand side. -/
theorem eliminateMatrix_solution_iff {m n : Type*} [DecidableEq m] [Fintype n]
    (A : Matrix m n F) (b : m → F) (t s : m) (j : n) (hts : t ≠ s) (x : n → F) :
    eliminateMatrix A t s j *ᵥ x =
      Function.update b t (b t + eliminationFactor (A t j) (A s j) * b s) ↔ A *ᵥ x = b :=
  RowReductionMachine.addMultiple_solution_iff A b t s _ hts x

omit [DecidableEq F] in
/-- Homogeneous solutions are preserved for distinct target/source rows. -/
theorem eliminateMatrix_kernel_iff {m n : Type*} [DecidableEq m] [Fintype n]
    (A : Matrix m n F) (t s : m) (j : n) (hts : t ≠ s) (x : n → F) :
    eliminateMatrix A t s j *ᵥ x = 0 ↔ A *ᵥ x = 0 :=
  RowReductionMachine.addMultiple_kernel_iff A t s _ hts x

end Matrix.PivotEliminationMachine
