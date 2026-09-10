/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateDecoderMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SmallBlock.SmallBlockDecoderMachine
/-!
# Integer-input coordinate capacity decoder

One executable dispatch covers oversized thresholds, exceptional small blocks, and coordinate
hidden-derivative decoding. The real gap is not an input to this program: it determines fixed
integer parameters in the correctness theorem. Order zero uses block-dependent multiplicity.
Inputs outside the correctness hypotheses may return failure or an empty list; no mathematical
list witness is used to choose the runtime result.

Every executed child retains its ledger, including failure. The constant outer allowance covers
primitive scalar checks and fixed-size handoffs; it does not price arbitrary-precision arithmetic,
input/output serialization, or scalar-fuel computation. Those require the bit-RAM refinement.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateCapacityMachine

/-- At order zero the interpolation multiplicity grows with the supplied block length. -/
def multiplicity (n d m : ℕ) : ℕ := if d = 0 then n / 2 else m

variable {q : ℕ} [Fact q.Prime]

/-- Total integer-input program; `n` describes the materialized rows in the specification.
Only primality is a proof argument. No gap real, exact list, or success proof is input. -/
def run (n k d m A : ℕ) (rows : List (ZMod q × ZMod q)) :
    Option (List (List (ZMod q))) × ℕ :=
  if n < A ∨ n ≤ 2 then
    let small := SmallBlockDecoderMachine.runFuel n A rows 5 .start
    match small.1 with
    | .done out => (some out, small.2 + 40)
    | _ => (none, small.2 + 40)
  else
    if h : q ≠ 2 ∧ multiplicity n d m * A ≤ q ^ 2 then
      let decoded := CoordinateDecoderMachine.run k d (multiplicity n d m) A rows h.1 h.2
      (decoded.1, decoded.2 + 40)
    else (none, 40)

/-- The small-block child is the actual executed branch, with its observed cost retained. -/
theorem run_of_small (n k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (hsmall : n < A ∨ n ≤ 2) (out : List (List (ZMod q))) (cost : ℕ)
    (hr : SmallBlockDecoderMachine.runFuel n A rows 5 .start = (.done out, cost)) :
    run n k d m A rows = (some out, cost + 40) := by
  simp only [run, if_pos hsmall, hr]

/-- On nonexceptional inputs the same coordinate child result and ledger are returned. -/
theorem run_of_coordinate (n k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (hA : A ≤ n) (hn : 3 ≤ n) (hodd : q ≠ 2)
    (hL : multiplicity n d m * A ≤ q ^ 2) (out : List (List (ZMod q))) (cost : ℕ)
    (hr : CoordinateDecoderMachine.run k d (multiplicity n d m) A rows hodd hL =
      (some out, cost)) : run n k d m A rows = (some out, cost + 40) := by
  have hsmall : ¬(n < A ∨ n ≤ 2) := by omega
  have hgood : q ≠ 2 ∧ multiplicity n d m * A ≤ q ^ 2 := ⟨hodd, hL⟩
  simp only [run, if_neg hsmall, dif_pos hgood, hr]

end ReedSolomon.ListDecoding.CoordinateCapacityMachine
