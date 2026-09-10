/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Univariate.Basic
import all CompPoly.Univariate.Basic

/-!
# A closed machine for Horner evaluation

Programs are arrays of instructions with literal jump targets. There are no host-language
callbacks, arbitrary pure expressions, or opaque polynomial-evaluation instructions. The five
instruction forms suffice for Horner's coefficient loop. An independent transition relation fixes
both the state changes and charges; a fuel interpreter is related to its finite traces.

Costs distinguish field additions, field multiplications, control dispatches, indexed code fetches,
data accesses, and emitted field elements. Each executed instruction has one dispatch and one
indexed fetch. Data accesses count the code-cell read as well as the named scalar/list register
reads and writes; control-register management belongs to dispatch. A list-cell read retrieves its
head and tail together. Zero is a literal constant, not a natural-number cast. The input point and
coefficient list are already materialized. Creating or converting these inputs is outside this
subroutine's contract, not a free instruction of the machine.

This is an abstract field-operation and data-access model. It does not measure the host Lean
interpreter's allocation, fuel bookkeeping, or wall-clock time. Refinement to a concrete field
representation and its bit costs is a separate obligation. Natural casts, field enumeration,
extension construction, and arbitrary polynomial operations are not primitives of this language.
-/

@[expose] public section

namespace Polynomial.HornerMachine

/-- Counts of executed primitive operations in the abstract machine. -/
@[ext]
structure Cost where
  additions : ℕ
  multiplications : ℕ
  control : ℕ
  indexing : ℕ
  data : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

instance : Add Cost := ⟨fun a b =>
  ⟨a.additions + b.additions, a.multiplications + b.multiplications,
    a.control + b.control, a.indexing + b.indexing, a.data + b.data,
    a.output + b.output⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0, 0⟩ := rfl

@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.multiplications + b.multiplications,
      a.control + b.control, a.indexing + b.indexing, a.data + b.data,
      a.output + b.output⟩ := rfl

@[simp] theorem cost_add_zero (c : Cost) : c + 0 = c := by cases c; rfl

/-- Closed instructions: all successors are literal code addresses. -/
inductive Instruction where
  | reset (next : ℕ)
  | take (empty next : ℕ)
  | multiply (next : ℕ)
  | add (next : ℕ)
  | emit
  deriving DecidableEq, Repr

/-- The coefficient register is initialized separately from the accumulator. -/
inductive Configuration (F : Type*) where
  | running (pc : ℕ) (remaining : List F) (accumulator coefficient : F)
  | halted (value : F)
  deriving DecidableEq, Repr

/-- Reset writes the accumulator; the instruction fetch reads one code cell. -/
def resetCost : Cost := ⟨0, 0, 1, 1, 2, 0⟩

/-- Testing the empty coefficient list reads its register and the code cell. -/
def emptyCost : Cost := ⟨0, 0, 1, 1, 2, 0⟩

/-- Taking a coefficient reads one list cell, writes two registers, and fetches code. -/
def takeCost : Cost := ⟨0, 0, 1, 1, 4, 0⟩

/-- Multiplication reads two field registers, writes the accumulator, and fetches code. -/
def multiplyCost : Cost := ⟨0, 1, 1, 1, 4, 0⟩

/-- Addition reads two field registers, writes the accumulator, and fetches code. -/
def addCost : Cost := ⟨1, 0, 1, 1, 4, 0⟩

/-- Emission reads the accumulator and code cell, and outputs one field element. -/
def emitCost : Cost := ⟨0, 0, 1, 1, 2, 1⟩

variable {F : Type*} [Semiring F]

/-- Independent operational rules. Malformed addresses have no transition, and halted states
have no outgoing transition. Every successful rule fixes its own charge. -/
inductive Step (code : Array Instruction) (x : F) :
    Configuration F → Cost → Configuration F → Prop where
  | reset {pc next xs a c} (fetch : code[pc]? = some (.reset next)) :
      Step code x (.running pc xs a c) resetCost (.running next xs 0 c)
  | empty {pc empty next a c} (fetch : code[pc]? = some (.take empty next)) :
      Step code x (.running pc [] a c) emptyCost (.running empty [] a c)
  | take {pc empty next h t a c} (fetch : code[pc]? = some (.take empty next)) :
      Step code x (.running pc (h :: t) a c) takeCost (.running next t a h)
  | multiply {pc next xs a c} (fetch : code[pc]? = some (.multiply next)) :
      Step code x (.running pc xs a c) multiplyCost (.running next xs (a * x) c)
  | add {pc next xs a c} (fetch : code[pc]? = some (.add next)) :
      Step code x (.running pc xs a c) addCost (.running next xs (a + c) c)
  | emit {pc xs a c} (fetch : code[pc]? = some .emit) :
      Step code x (.running pc xs a c) emitCost (.halted a)

/-- Executable instruction dispatch. Neither output nor charge is supplied by a caller. -/
def step (code : Array Instruction) (x : F) :
    Configuration F → Option (Configuration F × Cost)
  | .halted _ => none
  | .running pc xs a c =>
      match code[pc]? with
      | none => none
      | some (.reset next) => some (.running next xs 0 c, resetCost)
      | some (.take empty next) =>
          match xs with
          | [] => some (.running empty [] a c, emptyCost)
          | h :: t => some (.running next t a h, takeCost)
      | some (.multiply next) => some (.running next xs (a * x) c, multiplyCost)
      | some (.add next) => some (.running next xs (a + c) c, addCost)
      | some .emit => some (.halted a, emitCost)

/-- Every operational transition is implemented with exactly its prescribed charge. -/
theorem Step.step_eq {code : Array Instruction} {x : F} {s t : Configuration F} {c : Cost}
    (h : Step code x s c t) : step code x s = some (t, c) := by
  cases h <;> simp [step, *]

/-- Every successful executable dispatch satisfies an independent operational rule. -/
theorem step_sound {code : Array Instruction} {x : F} {s t : Configuration F} {c : Cost}
    (h : step code x s = some (t, c)) : Step code x s c t := by
  cases s with
  | halted value => simp [step] at h
  | running pc xs a current =>
      cases hf : code[pc]? with
      | none => simp [step, hf] at h
      | some instruction =>
          cases instruction with
          | reset next =>
              simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.reset hf
          | take empty next =>
              cases xs with
              | nil =>
                  simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact Step.empty hf
              | cons head tail =>
                  simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  exact Step.take hf
          | multiply next =>
              simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.multiply hf
          | add next =>
              simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.add hf
          | emit =>
              simp only [step, hf, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.emit hf

/-- Both the next state and charge are deterministic. -/
theorem Step.deterministic {code : Array Instruction} {x : F}
    {s t₁ t₂ : Configuration F} {c₁ c₂ : Cost}
    (h₁ : Step code x s c₁ t₁) (h₂ : Step code x s c₂ t₂) : t₁ = t₂ ∧ c₁ = c₂ := by
  have h := h₁.step_eq.symm.trans h₂.step_eq
  simpa only [Option.some.injEq, Prod.mk.injEq] using h

/-- A finite operational trace with its length and the sum of its actual transition charges. -/
inductive Trace (code : Array Instruction) (x : F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace code x 0 s 0 s
  | cons {n s u t c d} (head : Step code x s c u) (tail : Trace code x n u d t) :
      Trace code x (n + 1) s (c + d) t

/-- Execute at most `fuel` instructions, returning the reached state and accumulated charges.
Exhaustion and malformed code remain distinguishable from a halted output in the returned state. -/
def runFuel (code : Array Instruction) (x : F) :
    ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step code x s with
      | none => (s, 0)
      | some (u, c) =>
          let result := runFuel code x n u
          (result.1, c + result.2)

/-- The fuel interpreter always returns an operational trace with the same state and cost. -/
theorem runFuel_refines (code : Array Instruction) (x : F) (fuel : ℕ)
    (s : Configuration F) :
    ∃ n ≤ fuel, Trace code x n s (runFuel code x fuel s).2 (runFuel code x fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step code x s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (x := x) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          refine ⟨n + 1, Nat.succ_le_succ hn, ?_⟩
          simpa [runFuel, hs] using Trace.cons (step_sound hs) ht

/-- Conversely, fuel equal to an operational trace's length reproduces its state and cost. -/
theorem Trace.runFuel_eq {code : Array Instruction} {x : F}
    {n : ℕ} {s t : Configuration F} {c : Cost} (h : Trace code x n s c t) :
    runFuel code x n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-! ## The fixed Horner program -/

/-- Reset, branch/pop, multiply, add/back-edge, emit. Coefficients are read highest degree first. -/
def hornerCode : Array Instruction :=
  #[.reset 1, .take 4 2, .multiply 3, .add 1, .emit]

/-- Operational cost from the coefficient-loop header, including the empty test and emission. -/
def loopCost (n : ℕ) : Cost := ⟨n, n, 3 * n + 2, 3 * n + 2, 12 * n + 4, 1⟩

/-- Full cost of the fixed program on `n` supplied coefficient cells. -/
def hornerCost (n : ℕ) : Cost := ⟨n, n, 3 * n + 3, 3 * n + 3, 12 * n + 6, 1⟩

/-- The loop's operational trace implements the Horner fold and its exact operation vector. -/
theorem horner_loop_trace (x : F) (xs : List F) (a c : F) :
    Trace hornerCode x (3 * xs.length + 2) (.running 1 xs a c) (loopCost xs.length)
      (.halted (xs.foldl (fun acc coeff => acc * x + coeff) a)) := by
  induction xs generalizing a c with
  | nil =>
      have h := Trace.cons (Step.empty (code := hornerCode) (x := x)
        (pc := 1) (empty := 4) (next := 2) (a := a) (c := c) (by decide))
        (Trace.cons (Step.emit (by decide)) (Trace.nil _))
      simpa [loopCost, emptyCost, emitCost, cost_add] using h
  | cons head tail ih =>
      have h := Trace.cons (Step.take (code := hornerCode) (x := x)
        (pc := 1) (empty := 4) (next := 2) (h := head) (t := tail) (a := a) (c := c) (by decide))
        (Trace.cons (Step.multiply (next := 3) (by decide))
          (Trace.cons (Step.add (by decide)) (ih (a * x + head) head)))
      convert h using 1 <;>
        simp [loopCost, takeCost, multiplyCost, addCost,
          cost_add, Nat.mul_add, Nat.add_assoc]
      omega

/-- The same closed program has both the desired output and the proved exact operation count. -/
theorem horner_runFuel (x : F) (xs : List F) :
    runFuel hornerCode x (3 * xs.length + 3) (.running 0 xs 0 0) =
      (.halted (xs.foldl (fun acc coeff => acc * x + coeff) 0), hornerCost xs.length) := by
  have h := Trace.cons (Step.reset (code := hornerCode) (x := x)
    (pc := 0) (xs := xs) (a := 0) (c := 0) (by decide)) (horner_loop_trace x xs 0 0)
  convert h.runFuel_eq using 1
  simp [hornerCost, loopCost, resetCost, cost_add]
  omega

/-- Polynomial refinement with an explicit representation precondition. The theorem executes on
`coefficients`, not on a hidden conversion of `p`; preparing that list is a separate operation. -/
theorem horner_runFuel_eq_eval (x : F) (p : CompPoly.CPolynomial F)
    (coefficients : List F) (hcoefficients : coefficients = p.val.toList.reverse) :
    runFuel hornerCode x (3 * coefficients.length + 3) (.running 0 coefficients 0 0) =
      (.halted (p.eval x), hornerCost coefficients.length) := by
  rw [horner_runFuel]
  congr 2
  rw [hcoefficients, List.foldl_reverse]
  change p.val.toList.foldr (fun coeff acc => acc * x + coeff) 0 = p.eval x
  rw [Array.foldr_toList]
  exact CompPoly.CPolynomial.eval_horner_eq_eval x p

end Polynomial.HornerMachine
