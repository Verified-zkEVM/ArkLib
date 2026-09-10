/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListHornerExecution
public import ArkLib.Data.Polynomial.HornerMachine
-- The polynomial refinement intentionally reduces CompPoly's array representation.
import all CompPoly.Univariate.Basic

/-!
# Refinement of the existing Horner source loop to shared-list bit RAM

The physical heap consumer and the existing closed field-level loop halt with the same scalar.
Their stated costs are separate counts of their actual traces. The polynomial corollary uses
an explicit coefficient representation and a physically supplied zero accumulator. Neither
coefficient encoding nor accumulator initialization is hidden in this loop-header refinement.
-/

@[expose] public section

namespace Computation.SharedListHornerMachine

open AddressedBits (Memory)
open BinaryWordMachine (Word value)
open SharedListHeap (RepList nilPointer)

/-- This physical run lowers the actual existing Horner program from its coefficient-loop header. -/
theorem source_loop_execution {mem : Memory} {w : ℕ} {q point acc p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs)
    (hacc : value acc < value q) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q)
    (hwacc : acc.length = q.length) (hwpoint : point.length = q.length) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .taking acc point (.scan q p [] false)⟩
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      runFuel n ⟨mem, .taking acc point (.scan q p [] false)⟩ =
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      Polynomial.HornerMachine.runFuel Polynomial.HornerMachine.hornerCode
        (value point : ZMod (value q)) (3 * xs.length + 2)
        (.running 1 (xs.map (fun c ↦ (value c : ZMod (value q))))
          (value acc : ZMod (value q)) 0) =
        (.halted (value out : ZMod (value q)), Polynomial.HornerMachine.loopCost xs.length) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hv⟩ :=
    loop_execution hr hacc hpoint hcoeff hwacc hwpoint
  have hs := (Polynomial.HornerMachine.horner_loop_trace
    (value point : ZMod (value q)) (xs.map (fun c ↦ (value c : ZMod (value q))))
    (value acc : ZMod (value q)) 0).runFuel_eq
  rw [← hv] at hs
  exact ⟨n, hn, out, ht, hf, hw, hb, by simpa only [List.length_map] using hs⟩

/-- A represented highest-degree-first polynomial is evaluated by this one bounded physical run.
The starting zero is an explicit word input; the modulus, point and coefficient RAM are retained. -/
theorem polynomial_execution {mem : Memory} {w : ℕ} {q point acc p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs)
    (hacc : value acc < value q) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q)
    (hwacc : acc.length = q.length) (hwpoint : point.length = q.length)
    (hzero : value acc = 0) (poly : CompPoly.CPolynomial (ZMod (value q)))
    (hpoly : xs.map (fun c ↦ (value c : ZMod (value q))) = poly.val.toList.reverse) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .taking acc point (.scan q p [] false)⟩
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      runFuel n ⟨mem, .taking acc point (.scan q p [] false)⟩ =
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      (value out : ZMod (value q)) = poly.eval (value point : ZMod (value q)) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hv⟩ :=
    loop_execution hr hacc hpoint hcoeff hwacc hwpoint
  refine ⟨n, hn, out, ht, hf, hw, hb, ?_⟩
  rw [hv, hpoly, hzero, Nat.cast_zero, List.foldl_reverse]
  change poly.val.toList.foldr
    (fun coeff acc ↦ acc * (value point : ZMod (value q)) + coeff) 0 = poly.eval _
  rw [Array.foldr_toList]
  exact CompPoly.CPolynomial.eval_horner_eq_eval _ poly

end Computation.SharedListHornerMachine
