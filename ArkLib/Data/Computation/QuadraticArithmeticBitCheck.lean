/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitAddExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitMulExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitNegExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitInvExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitEqualExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitLoad
public import ArkLib.Data.Computation.QuadraticArithmeticBitBoolean

/-!
# Independent full-bank scalar instruction replay

Expected results are literal modular arithmetic values, not applications of correctness theorems.
Every check observes all thirteen work tapes, eight registers, five input tapes and two physical
flag tapes. Thus the same replay checks output width, reduced value, unmodified registers,
retained modulus and inputs, and blank temporary tapes. All five binary-register alias patterns
are covered, as are unary destination aliases and physical zero words.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitCheck

open BinaryWordMachine (Word)

private abbrev Register := Fin 8
private abbrev Slot := Fin 13 ⊕ (Register ⊕ (Fin 5 ⊕ Fin 2))
private def q5 : Word := [true, false, true]
private def q3 : Word := [true, true]
private def regs5 : Register → Word := ![
  [true, true, false], [false, false, true], [true, false, false], [false, true, false],
  [false, false, false], [true, true, false], [false, false, true], [true, false, false]]
private def regs3 : Register → Word := ![
  [false, true], [true, false], [false, false], [true, false],
  [false, false], [false, true], [true, false], [false, false]]
private def inputs : Fin 5 → Word := ![[true], [false], [true, false], [], [false, true]]
private def flags : Fin 2 → Bool := ![true, false]

private def observe (bank : Slot → Word) : List Word :=
  List.ofFn (fun i : Fin 13 ↦ bank (.inl i)) ++
    List.ofFn (fun i : Register ↦ bank (.inr (.inl i))) ++
    List.ofFn (fun i : Fin 5 ↦ bank (.inr (.inr (.inl i)))) ++
    List.ofFn (fun i : Fin 2 ↦ bank (.inr (.inr (.inr i))))

private def expected (q : Word) (regs : Register → Word) (dst : Register)
    (out : Word) : List Word :=
  List.replicate 4 [] ++ [q] ++ List.replicate 8 [] ++
    List.ofFn (Function.update regs dst out) ++ List.ofFn inputs ++ [[true], [false]]

private def add (x y dst : Register) := observe (QuadraticArithmeticBitAdd.tapes inputs flags
  (QuadraticArithmeticBitAdd.runFuel 114 (.start q5 x y dst regs5)))
private def mul (x y dst : Register) := observe (QuadraticArithmeticBitMul.tapes inputs flags
  (QuadraticArithmeticBitMul.runFuel 677 (.start q5 x y dst regs5)))
private def neg (x dst : Register) := observe (QuadraticArithmeticBitNeg.tapes inputs flags
  (QuadraticArithmeticBitNeg.runFuel 78 (.start q5 x dst regs5)))
private def inv (x dst : Register) := observe (QuadraticArithmeticBitInv.tapes inputs flags
  (QuadraticArithmeticBitInv.runFuel 1106 (.start q3 x dst regs3)))

-- Distinct registers, equal sources, destination equals left, equals right, or equals both.
example : add 0 1 2 = expected q5 regs5 2 [false, true, false] := by decide +kernel
example : add 0 0 2 = expected q5 regs5 2 [true, false, false] := by decide +kernel
example : add 0 1 0 = expected q5 regs5 0 [false, true, false] := by decide +kernel
example : add 0 1 1 = expected q5 regs5 1 [false, true, false] := by decide +kernel
example : add 0 0 0 = expected q5 regs5 0 [true, false, false] := by decide +kernel

-- Multiplication also destroys its retained operand copy, including on both zero paths.
example : mul 0 1 2 = expected q5 regs5 2 [false, true, false] := by decide +kernel
example : mul 0 0 2 = expected q5 regs5 2 [false, false, true] := by decide +kernel
example : mul 0 1 0 = expected q5 regs5 0 [false, true, false] := by decide +kernel
example : mul 0 1 1 = expected q5 regs5 1 [false, true, false] := by decide +kernel
example : mul 0 0 0 = expected q5 regs5 0 [false, false, true] := by decide +kernel
example : mul 4 1 2 = expected q5 regs5 2 [false, false, false] := by decide +kernel
example : mul 1 4 1 = expected q5 regs5 1 [false, false, false] := by decide +kernel

-- Negation consumes its operand; zero still has the modulus's full physical width.
example : neg 0 1 = expected q5 regs5 1 [false, true, false] := by decide +kernel
example : neg 0 0 = expected q5 regs5 0 [false, true, false] := by decide +kernel
example : neg 4 4 = expected q5 regs5 4 [false, false, false] := by decide +kernel

-- Inversion returns two for two modulo three, preserves one, and totalizes zero to zero.
example : inv 0 1 = expected q3 regs3 1 [false, true] := by decide +kernel
example : inv 0 0 = expected q3 regs3 0 [false, true] := by decide +kernel
example : inv 2 2 = expected q3 regs3 2 [false, false] := by decide +kernel
example : inv 1 0 = expected q3 regs3 0 [true, false] := by decide +kernel

private def equalityState (n : ℕ) (x y : Register) (dst : Fin 2) :=
  QuadraticArithmeticBitEqual.runFuel n (.start q5 x y dst regs5)
private def equality (x y : Register) (dst : Fin 2) :=
  observe (QuadraticArithmeticBitEqual.tapes inputs flags (equalityState 30 x y dst))
private def expectedFlags (out : List Word) : List Word :=
  List.replicate 4 [] ++ [q5] ++ List.replicate 8 [] ++
    List.ofFn regs5 ++ List.ofFn inputs ++ out
private def firstFlag (n : ℕ) := QuadraticArithmeticBitEqual.tapes inputs flags
  (equalityState n 0 1 0) (.inr (.inr (.inr 0)))

-- Equality preserves scalar registers and changes only its selected physical flag.
example : equality 0 1 0 = expectedFlags [[false], [false]] := by decide +kernel
example : equality 0 5 1 = expectedFlags [[true], [true]] := by decide +kernel
example : equality 0 0 1 = expectedFlags [[true], [true]] := by decide +kernel
example : firstFlag 28 = [true] := by decide +kernel
example : firstFlag 29 = [] := by decide +kernel
example : firstFlag 30 = [false] := by decide +kernel
theorem equality_updates_only_selected_flag :
    List.ofFn (QuadraticArithmeticBitEqual.resultFlags ![true, false]
      (QuadraticArithmeticBitEqual.runFuel 30
        (.start [true, false, true] 0 1 0 ![
          [true, true, false], [false, false, true], [true, false, false],
          [false, true, false], [false, false, false], [true, true, false],
          [false, false, true], [true, false, false]]))) =
    [false, false] := by decide +kernel

private def loadState (n : ℕ) (source : QuadraticAlgebra.ArithmeticMachine.Source)
    (dst : Register) := QuadraticArithmeticBitLoad.runFuel n
  (.start q5 (QuadraticArithmeticBitLoad.sourceIndex source) dst regs5 inputs)
private def load (n : ℕ) (source : QuadraticAlgebra.ArithmeticMachine.Source)
    (dst : Register) := observe (QuadraticArithmeticBitLoad.tapes flags (loadState n source dst))

-- All five source selectors, including empty and nonpalindromic words, clear a dirty destination.
-- Input and register zero remain distinct physical tapes even when their indices coincide.
example : load 10 .leftRe 0 = expected q5 regs5 0 [true] := by decide +kernel
example : load 10 .leftIm 1 = expected q5 regs5 1 [false] := by decide +kernel
example : load 12 .rightRe 2 = expected q5 regs5 2 [true, false] := by decide +kernel
example : load 8 .rightIm 3 = expected q5 regs5 3 [] := by decide +kernel
example : load 12 .parameter 7 = expected q5 regs5 7 [false, true] := by decide +kernel
example : load 1 .rightIm 0 = observe (QuadraticArithmeticBitLoad.tapes flags
    (.start q5 3 0 regs5 inputs)) := by decide +kernel
example : QuadraticArithmeticBitLoad.registers (loadState 2 .rightIm 0) 0 =
    [true, false] := by decide +kernel

private def pair (n : ℕ) (x y : Register) (r : Register → Word) :=
  observe (QuadraticArithmeticBitPair.tapes inputs flags
    (QuadraticArithmeticBitPair.runFuel n (.start q5 x y r)))
private def expectedOutput (r : Register → Word) (left right : Word)
    (b : Fin 2 → Bool) : List Word :=
  [left, right, [], [], q5] ++ List.replicate 8 [] ++
    List.ofFn r ++ List.ofFn inputs ++ List.ofFn (fun i ↦ [b i])
private def emptyFirst := Function.update regs5 0 []

-- Pair emission preserves nonpalindromic sources, source aliases, and empty physical words.
example : pair 21 0 1 regs5 =
    expectedOutput regs5 [true, true, false] [false, false, true] flags := by decide +kernel
example : pair 21 0 0 regs5 =
    expectedOutput regs5 [true, true, false] [true, true, false] flags := by decide +kernel
example : pair 21 1 0 regs5 =
    expectedOutput regs5 [false, false, true] [true, true, false] flags := by decide +kernel
example : pair 15 0 1 emptyFirst =
    expectedOutput emptyFirst [] [false, false, true] flags := by decide +kernel
example : pair 9 0 0 emptyFirst = expectedOutput emptyFirst [] [] flags := by decide +kernel

private def boolean (a b : Bool) := observe (QuadraticArithmeticBitBoolean.tapes inputs
  (QuadraticArithmeticBitBoolean.runFuel 1 (.start q5 regs5 ![a, b])))

-- The result is a physical one-bit tape even when the conjunction is false.
example : boolean false false = expectedOutput regs5 [false] [] ![false, false] := by
  decide +kernel
example : boolean false true = expectedOutput regs5 [false] [] ![false, true] := by
  decide +kernel
example : boolean true false = expectedOutput regs5 [false] [] ![true, false] := by
  decide +kernel
example : boolean true true = expectedOutput regs5 [true] [] ![true, true] := by
  decide +kernel

end Computation.QuadraticArithmeticBitCheck
