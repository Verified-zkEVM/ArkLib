/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.FiniteWitness
public import Mathlib.Data.ZMod.Basic

/-!
# Quadratic arithmetic by base-field instructions

Fixed programs operate on eight scalar and two Boolean registers. Each instruction performs at
most one base-field operation. Inversion computes the norm explicitly and shares one base inverse.
Pair-coordinate loads, instruction fetches, register accesses, pair allocation and final emission
are charged. Initialization writes eight scalar zeros and two Boolean false constants, charged as
ten constant writes. Retained registers are shared; interpreter fuel and field bit costs are not
part of this field-operation model. Input pairs and the parameter are already materialized.

Decoding is a semantic representation map, not a bulk conversion instruction. No extension-field
operation occurs in dispatch. Only the inverse refinement requires a nonsquare parameter.
-/

@[expose] public section

namespace QuadraticAlgebra.ArithmeticMachine

/-- Separate base-field operations and administrative charges. -/
@[ext] structure Cost where
  additions : ℕ := 0
  multiplications : ℕ := 0
  negations : ℕ := 0
  inversions : ℕ := 0
  equalities : ℕ := 0
  control : ℕ := 0
  data : ℕ := 0
  constants : ℕ := 0
  output : ℕ := 0
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨{}⟩
instance : Add Cost := ⟨fun c d ↦
  ⟨c.additions + d.additions, c.multiplications + d.multiplications,
    c.negations + d.negations, c.inversions + d.inversions, c.equalities + d.equalities,
    c.control + d.control, c.data + d.data, c.constants + d.constants, c.output + d.output⟩⟩

/-- Total unit-cost primitives, including administrative work. -/
def Cost.total (c : Cost) : ℕ := c.additions + c.multiplications + c.negations +
  c.inversions + c.equalities + c.control + c.data + c.constants + c.output

abbrev Pair (F : Type*) := F × F
abbrev Register := Fin 8

/-- Already materialized immutable input registers. -/
structure Input (F : Type*) where
  parameter : F
  left : Pair F
  right : Pair F
  deriving DecidableEq, Repr

inductive Source where
  | leftRe | leftIm | rightRe | rightIm | parameter
  deriving DecidableEq, Repr

/-- Every arithmetic instruction has exactly one base-field operation. -/
inductive Instruction where
  | load (source : Source) (dst : Register)
  | add (x y dst : Register)
  | mul (x y dst : Register)
  | neg (x dst : Register)
  | inv (x dst : Register)
  | equal (x y : Register) (dst : Fin 2)
  | pair (x y : Register)
  | boolean
  deriving DecidableEq, Repr

inductive Operation where
  | add | mul | neg | inv | equal
  deriving DecidableEq, Repr

/-- Literal programs; register five is temporary and six/seven hold result coordinates. -/
def program : Operation → List Instruction
  | .add => [.load .leftRe 0, .load .leftIm 1, .load .rightRe 2, .load .rightIm 3,
      .add 0 2 6, .add 1 3 7, .pair 6 7]
  | .mul => [.load .leftRe 0, .load .leftIm 1, .load .rightRe 2, .load .rightIm 3,
      .load .parameter 4, .mul 0 2 5, .mul 4 1 6, .mul 6 3 6, .add 5 6 6,
      .mul 0 3 5, .mul 1 2 7, .add 5 7 7, .pair 6 7]
  | .neg => [.load .leftRe 0, .load .leftIm 1, .neg 0 6, .neg 1 7, .pair 6 7]
  | .inv => [.load .leftRe 0, .load .leftIm 1, .load .parameter 4,
      .mul 0 0 5, .mul 4 1 6, .mul 6 1 6, .neg 6 6, .add 5 6 5,
      .inv 5 5, .mul 5 0 6, .mul 5 1 7, .neg 7 7, .pair 6 7]
  | .equal => [.load .leftRe 0, .load .leftIm 1, .load .rightRe 2, .load .rightIm 3,
      .equal 0 2 0, .equal 1 3 1, .boolean]

/-- Fetch and cursor advancement cost two data accesses; binary operations read two registers
and write one.
Pair return reads two registers and allocates both coordinate slots before emission.
Boolean return reads both flags and performs one charged Boolean conjunction. -/
def instructionCost : Instruction → Cost
  | .load _ _ => { control := 1, data := 4 }
  | .add _ _ _ => { additions := 1, control := 1, data := 5 }
  | .mul _ _ _ => { multiplications := 1, control := 1, data := 5 }
  | .neg _ _ => { negations := 1, control := 1, data := 4 }
  | .inv _ _ => { inversions := 1, control := 1, data := 4 }
  | .equal _ _ _ => { equalities := 1, control := 1, data := 5 }
  | .pair _ _ => { control := 1, data := 6, output := 1 }
  | .boolean => { control := 2, data := 4, output := 1 }

/-- Initialize the fixed register bank and write the selected literal program pointer. -/
def startCost : Cost := { control := 1, data := 11, constants := 10 }

inductive Result (F : Type*) where
  | pair (value : Pair F)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

inductive Configuration (F : Type*) where
  | start (operation : Operation)
  | running (remaining : List Instruction) (scalars : Register → F) (flags : Fin 2 → Bool)
  | done (result : Result F)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Read one coordinate or the supplied parameter. -/
def readSource (input : Input F) : Source → F
  | .leftRe => input.left.1
  | .leftIm => input.left.2
  | .rightRe => input.right.1
  | .rightIm => input.right.2
  | .parameter => input.parameter

/-- One instruction updates fixed registers, or constructs and emits one result. -/
def execute (input : Input F) (i : Instruction) (rest : List Instruction)
    (r : Register → F) (b : Fin 2 → Bool) : Configuration F :=
  match i with
  | .load s d => .running rest (Function.update r d (readSource input s)) b
  | .add x y d => .running rest (Function.update r d (r x + r y)) b
  | .mul x y d => .running rest (Function.update r d (r x * r y)) b
  | .neg x d => .running rest (Function.update r d (-r x)) b
  | .inv x d => .running rest (Function.update r d (r x)⁻¹) b
  | .equal x y d => .running rest r (Function.update b d (decide (r x = r y)))
  | .pair x y => .done (.pair (r x, r y))
  | .boolean => .done (.boolean (b 0 && b 1))

/-- Dispatch never executes more than one instruction. Empty malformed programs stop. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start op => some (.running (program op) (fun _ ↦ 0) (fun _ ↦ false), startCost)
  | .running [] _ _ => none
  | .running (i :: rest) r b => some (execute input i rest r b, instructionCost i)
  | .done _ => none

/-- Operational rules preserve the actual instruction charge. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | start (op) : Step input (.start op) startCost
      (.running (program op) (fun _ ↦ 0) (fun _ ↦ false))
  | instruction (i rest r b) : Step input (.running (i :: rest) r b) (instructionCost i)
      (execute input i rest r b)

/-- Every rule agrees with the executable successor and charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by cases h <;> rfl

/-- Dispatch is exhausted by the explicit initialization and instruction rules. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start op => cases h; exact Step.start op
  | running rest r b =>
    cases rest with
    | nil => simp [step] at h
    | cons i rest => cases h; exact Step.instruction i rest r b
  | done result => simp [step] at h

inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

/-- Fuel executes individual instructions and accumulates all primitive categories. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Every actual run has a trace with the same accumulated cost. -/
theorem runFuel_refines (input : Input F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input n s (runFuel input fuel s).2 (runFuel input fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ n ih =>
    cases hs : step input s with
    | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (input := input) s⟩
    | some pair =>
      obtain ⟨k, hk, h⟩ := ih pair.1
      exact ⟨k + 1, Nat.succ_le_succ hk, by
        simpa [runFuel, hs] using Trace.cons (step_sound hs) h⟩

/-- Initialization plus one step for each instruction of the literal program. -/
def fuel (op : Operation) : ℕ := (program op).length + 1

/-- Exact cost vectors for the five fixed programs. -/
def cost : Operation → Cost
  | .add => ⟨2, 0, 0, 0, 0, 8, 43, 10, 1⟩
  | .mul => ⟨2, 5, 0, 0, 0, 14, 72, 10, 1⟩
  | .neg => ⟨0, 0, 2, 0, 0, 6, 33, 10, 1⟩
  | .inv => ⟨1, 5, 2, 1, 0, 14, 71, 10, 1⟩
  | .equal => ⟨0, 0, 0, 0, 2, 9, 41, 10, 1⟩

/-- Coordinate-level specification; no cost claim is made for evaluating this expression. -/
def specification (input : Input F) : Operation → Result F
  | .add => .pair (input.left.1 + input.right.1, input.left.2 + input.right.2)
  | .mul => .pair (input.left.1 * input.right.1 +
      input.parameter * input.left.2 * input.right.2,
      input.left.1 * input.right.2 + input.left.2 * input.right.1)
  | .neg => .pair (-input.left.1, -input.left.2)
  | .inv => let t := (input.left.1 * input.left.1 +
      -(input.parameter * input.left.2 * input.left.2))⁻¹
    .pair (t * input.left.1, -(t * input.left.2))
  | .equal => .boolean (decide (input.left.1 = input.right.1) &&
      decide (input.left.2 = input.right.2))

/-- Actual instruction execution realizes each specification and its exact cost vector. -/
theorem runFuel_eq (input : Input F) (op : Operation) :
    runFuel input (fuel op) (.start op) = (.done (specification input op), cost op) := by
  cases op <;>
    simp [runFuel, fuel, program, step, execute, readSource, specification,
      cost, instructionCost, startCost] <;> rfl

/-- A uniform bound includes base arithmetic, initialization, accesses and final output. -/
theorem cost_total_le (op : Operation) : (cost op).total ≤ 128 := by
  cases op <;> decide

/-- Mathematical decoding of one coordinate pair. -/
def decode (a : F) (p : Pair F) : QuadraticAlgebra F a 0 := ⟨p.1, p.2⟩

/-- Observe only a completed result, then apply the mathematical representation map. -/
def decodedOutput (a : F) : Configuration F → Option (QuadraticAlgebra F a 0 ⊕ Bool)
  | .done (.pair p) => some (.inl (decode a p))
  | .done (.boolean b) => some (.inr b)
  | _ => none

/-- Executed addition agrees with canonical quadratic addition. -/
theorem add_correct (input : Input F) :
    decodedOutput input.parameter (runFuel input (fuel .add) (.start .add)).1 =
      some (.inl (decode input.parameter input.left + decode input.parameter input.right)) := by
  rw [runFuel_eq]
  rfl

/-- Executed multiplication agrees with the zero-linear-coefficient quadratic algebra. -/
theorem mul_correct (input : Input F) :
    decodedOutput input.parameter (runFuel input (fuel .mul) (.start .mul)).1 =
      some (.inl (decode input.parameter input.left * decode input.parameter input.right)) := by
  rw [runFuel_eq]
  change some (Sum.inl (mulCoordinates input.parameter
    (decode input.parameter input.left) (decode input.parameter input.right))) = _
  rw [mulCoordinates_eq]

/-- Executed negation agrees with canonical coordinate negation. -/
theorem neg_correct (input : Input F) :
    decodedOutput input.parameter (runFuel input (fuel .neg) (.start .neg)).1 =
      some (.inl (-decode input.parameter input.left)) := by
  rw [runFuel_eq]
  rfl

/-- The actual inverse program agrees with certified field inversion, also on zero. -/
theorem inv_correct (input : Input F) (ha : ¬IsSquare input.parameter) :
    letI := fieldOfNonsquare input.parameter ha
    decodedOutput input.parameter (runFuel input (fuel .inv) (.start .inv)).1 =
      some (.inl ((decode input.parameter input.left)⁻¹)) := by
  let := fieldOfNonsquare input.parameter ha
  rw [runFuel_eq]
  have h := invCoordinates_eq input.parameter ha (decode input.parameter input.left)
  simpa only [invCoordinates, decodedOutput, specification, decode, sub_eq_add_neg] using congrArg
    (fun z ↦ some (Sum.inl z : QuadraticAlgebra F input.parameter 0 ⊕ Bool)) h

omit [DecidableEq F] in
/-- Decoding reflects coordinate equality. -/
theorem decode_eq_iff (a : F) (p r : Pair F) : decode a p = decode a r ↔ p = r := by
  constructor
  · intro h
    exact Prod.ext (congrArg QuadraticAlgebra.re h) (congrArg QuadraticAlgebra.im h)
  · rintro rfl
    rfl

/-- Both base equality tests are executed, and their conjunction is extension equality. -/
theorem equal_correct (input : Input F) :
    decodedOutput input.parameter (runFuel input (fuel .equal) (.start .equal)).1 =
      some (.inr (decide (decode input.parameter input.left =
        decode input.parameter input.right))) := by
  rw [runFuel_eq]
  simp [decodedOutput, specification, decode_eq_iff, Prod.ext_iff]

/-- The actual run, rather than only its declared vector, obeys the uniform bound. -/
theorem runFuel_cost_le (input : Input F) (op : Operation) :
    (runFuel input (fuel op) (.start op)).2.total ≤ 128 := by
  rw [runFuel_eq]
  exact cost_total_le op

/-- Every selected program finishes in at most fourteen charged transitions. -/
theorem execution_trace (input : Input F) (op : Operation) :
    ∃ n ≤ 14, Trace input n (.start op) (cost op) (.done (specification input op)) := by
  obtain ⟨n, hn, h⟩ := runFuel_refines input (fuel op) (.start op)
  rw [runFuel_eq] at h
  refine ⟨n, hn.trans ?_, h⟩
  cases op <;> decide

/-- Zero inversion executes the same program, including its one base inverse. -/
example : decodedOutput (2 : ZMod 3)
    (runFuel ⟨2, (0, 0), (0, 0)⟩ 14 (.start .inv)).1 =
      some (.inl ⟨0, 0⟩) := by decide

/-- A nonzero input exercises the nonsquare quadratic norm and both inverse coordinates. -/
example : decodedOutput (2 : ZMod 3)
    (runFuel ⟨2, (1, 1), (0, 0)⟩ 14 (.start .inv)).1 =
      some (.inl ⟨2, 1⟩) := by
  change decodedOutput (2 : ZMod 3)
    (runFuel ⟨2, (1, 1), (0, 0)⟩ (fuel .inv) (.start .inv)).1 = _
  rw [runFuel_eq]
  norm_num [decodedOutput, specification, decode]
  decide

/-- Addition respects base characteristic two without requiring a nonsquare parameter. -/
example : decodedOutput (1 : ZMod 2)
    (runFuel ⟨1, (1, 1), (1, 0)⟩ 8 (.start .add)).1 =
      some (.inl ⟨0, 1⟩) := by decide

/-- Equal real coordinates cannot hide unequal imaginary coordinates. -/
example : decodedOutput (2 : ZMod 3)
    (runFuel ⟨2, (1, 1), (1, 2)⟩ 8 (.start .equal)).1 =
      some (.inr false) := by decide

end QuadraticAlgebra.ArithmeticMachine
