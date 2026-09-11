/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateCapacityExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CapacityOutputBounds
/-!
# Retained reference coordinate decoder at every rate

This module states the retained coordinate decoder's exact-output and primitive-work theorem. It is
a correctness reference for the capacity specification, not the paper's integrated norm and
square-system decoder. The purely mathematical list-existence theorem lives separately in
`ListDecodability/Capacity.lean`; the status of the paper algorithms is indexed in
`ListDecoding/PaperAlgorithms.lean`.
The integer agreement threshold `A` is an instance parameter;
the real gap `delta` is fixed before any block length, rate, field, or received word is chosen.

The output is a list of coefficient vectors. Polynomial membership means degree less than
`k` and at least `A` agreements. In particular, zero is not excluded by a natural-degree convention.
For gaps below one quarter, the prescribed derivative order and multiplicity give exponents `2d`
and `d`, with the explicit prefactor `4m`, in the two field-size regimes.
For larger gaps the bounds are one and strictly less than
the block length `n`. Taking `A = k + ceil(delta*n)` gives radius `1 - k/n - delta`;
the rounding and `Code.Lambda` formulation are established in `Capacity/Radius.lean`.

`capacity_decoder_exact_output_and_primitive_work` executes the integer-input
coordinate decoder and attaches these bounds to its actual coefficient-list output, together
with the observed primitive-work ledger. The runtime materializes its coordinate alphabets and
executes the raw-coordinate recovery, guards and collection. Both field-size inequalities concern
the identical run and list.

**Verification boundary.** The theorem proves a bound on the returned primitive-work ledger.
A same-output refinement to a restricted algebraic machine remains outstanding, including
scalar preparation and control overhead. This is the next algorithmic proof obligation;
a binary backend is not required for that algebraic-machine theorem. No bit-RAM or native
Lean running time is claimed by the primitive ledger below.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], capacity specification and Lean
  reference-decoder appendix.
* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], hidden-derivative interpolation.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

noncomputable section

/-- A single integer-input decoder outputs exactly the capacity list with both sharp size bounds.
The positive coefficient depends only on the gap. The observed `work` belongs to this same run.

This is a primitive-work theorem, not a bit-complexity theorem. A field operation, scalar check,
fixed-size record operation or charged machine transition has its declared primitive cost;
arbitrary-precision arithmetic, fuel calculation and host administration are not bit-priced here.
The real gap fixes only the integer program constants, and is not an executable input.
Output vectors have exactly `k` coefficients; both vector and polynomial duplicates are excluded.
The use of `Polynomial.degree` includes the zero polynomial in the exact membership statement. -/
theorem capacity_decoder_exact_output_and_primitive_work
    (delta : ℝ) (hdelta : 0 < delta) (hOne : delta < 1) :
    let d : ℕ := if (1 / 4 : ℝ) ≤ delta then 0
      else Nat.ceil (Real.exp (((27 : ℝ) / 10) / delta))
    let m : ℕ := Nat.ceil (100 * (d : ℝ) ^ 2 *
      ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1))
    let N : ℕ := if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m
    ∃ C : ℕ, 0 < C ∧
      ∀ n k q A : ℕ, N ≤ n → 0 < k → k ≤ n → (hq : q.Prime) → n ≤ q →
        (k : ℝ) + delta * n ≤ A → A ≤ 2 * n →
        let : Fact q.Prime := ⟨hq⟩
        ∀ (alpha : Fin n ↪ ZMod q) (y : Fin n → ZMod q),
          ∃ (out : List (List (ZMod q))) (work : ℕ),
            ListDecoding.CoordinateCapacityMachine.run n k d m A
              (List.ofFn (fun i ↦ (alpha i, y i))) = (some out, work) ∧
            out.Nodup ∧ (out.map JetHornerMachine.coefficientPolynomial).Nodup ∧
            (∀ P : Polynomial (ZMod q),
              P ∈ out.map JetHornerMachine.coefficientPolynomial ↔
                P.degree < k ∧ A ≤ Code.agree (fun i ↦ P.eval (alpha i)) y) ∧
            (∀ cs : List (ZMod q), cs ∈ out ↔ cs.length = k ∧
              (JetHornerMachine.coefficientPolynomial cs).degree < k ∧
              A ≤ Code.agree (fun i ↦
                (JetHornerMachine.coefficientPolynomial cs).eval (alpha i)) y) ∧
            (n < A → out = []) ∧
            ((1 / 2 : ℝ) ≤ delta → out.length ≤ 1) ∧
            ((1 / 4 : ℝ) ≤ delta → out.length < n) ∧
            work ≤ C * q ^ (2 * d + 29) ∧
            (delta < (1 / 4 : ℝ) → out.length ≤ 4 * m * q ^ (2 * d) ∧
              (2 * (m * A + d - max k ⌊delta * (n : ℝ) / 2⌋₊) ≤ q →
                out.length ≤ 4 * m * q ^ d ∧ work ≤ C * q ^ (d + 29))) := by
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity delta
  refine ⟨ListDecoding.CoordinateCapacityMachine.workCoefficient d m, ?_, ?_⟩
  · unfold ListDecoding.CoordinateCapacityMachine.workCoefficient
    omega
  · intro n k q A hn hk hkn hq hnq hA hAupper
    let : Fact q.Prime := ⟨hq⟩
    dsimp only
    intro alpha y
    have hthreshold := (agreementThreshold_le_iff_real hdelta.le n k A).mpr hA
    obtain ⟨out, work, hr, he, hw, hlarger⟩ := ListDecoding.CoordinateCapacityMachine.run_exact
      delta hdelta n k A hn hk hkn hnq hthreshold alpha y
    obtain ⟨hos, hhalf, hquarter, hsmall⟩ :=
      ListDecoding.CapacityOutputBounds.capacity_output_bounds
      delta hdelta hOne n k q A hn hk hkn hq hnq hA hAupper alpha y out he
    refine ⟨out, work, hr, he.2.1, he.1, he.2.2.1, he.2.2.2,
      hos, hhalf, hquarter, hw, ?_⟩
    intro hs
    exact ⟨(hsmall hs).1, fun hf ↦ ⟨(hsmall hs).2 hf, hlarger hs hf⟩⟩

end
end ReedSolomon
