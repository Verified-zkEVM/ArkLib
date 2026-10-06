/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Hachi §3.1 conformance to the shared checked-observation interface

Hachi's one-message trace head shares the `CheckedObservation` interface with the other packing
heads: `observation` is a `CheckedObservation` whose observation is the `ψ`-coordinate inner
product, equivalent to the scaled trace check (`check_iff_observation`). Its packing itself is
Hachi-specific: `ψ` over CompPoly's `CMlPolynomial`, rather than the shared `PackingData`
polynomial layer, which is built on `MvPolynomial`.

The conformance theorem states the head's exact relation correspondence: a passing check with a
valid ring-level opening holds iff the scalar relation holds and the sent value is honest. It
applies the head's read-back and honest-check lemmas, which are the shared
`CheckedObservation.readback` and `CheckedObservation.honest_check` at Hachi's observation. The
concrete instances show the honest side inhabited by a nonconstant polynomial, and that for a
false claim no sent ring value both passes the check and opens validly against the same weak
opening. The check alone is not enough: for the false claim `0` the message `0` passes it.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter

namespace ArkLibTest.RingSwitchingConformance.Hachi

section Universal

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (α κ : ℕ) {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
  (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)

/-- **Hachi §3.1 conformance.** The trace head's check-and-forward step corresponds exactly to
the scalar relation. -/
theorem traceHead_conforms
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (check α κ hk s Y = true ∧ (output α κ s Y, w) ∈
        relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) ↔
      ((s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound ∧ Y = honestMessage α κ base s w) := by
  constructor
  · rintro ⟨hc, hout⟩
    exact ⟨mem_relScalarEval_of_output α κ hk h2 pp base βSq γ bound s Y w hc hout,
      ((output_mem_relPolyEval_iff α κ hk h2 pp base βSq γ bound s Y w).1 hout).2⟩
  · rintro ⟨hin, rfl⟩
    exact ⟨check_honestMessage α κ hk h2 pp base βSq γ bound s w hin,
      output_mem_relPolyEval_of_mem_relScalarEval α κ hk h2 pp base βSq γ bound s w hin⟩

end Universal

section Concrete

open HachiTraceHeadTest

private theorem hk : 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide

/-- The honest side is inhabited: the committed nonconstant polynomial passes the check and its
forwarded value carries a valid ring-level opening. -/
example : check 1 0 hk s (honestMessage 1 0 2 s w) = true ∧
    (output 1 0 s (honestMessage 1 0 2 s w), w) ∈ relPolyEval Φ pp 2 6 1 1 :=
  (traceHead_conforms 1 0 hk h2 pp 2 6 1 1 s _ w).2 ⟨source_valid.1, rfl⟩

/-- For a false scalar claim, no sent ring value both passes the check and opens validly against
the same commitment and weak opening. -/
example (Y : Rq Φ) :
    ¬ (check 1 0 hk bad Y = true ∧ (output 1 0 bad Y, w) ∈ relPolyEval Φ pp 2 6 1 1) := by
  intro h
  have hbad := ((traceHead_conforms 1 0 hk h2 pp 2 6 1 1 bad Y w).1 h).1
  have hz : s.value = 0 := source_valid.1.2.symm.trans hbad.2
  rw [claim_two] at hz
  exact HachiTraceHeadAlgebraTest.value_ne_zero (congrArg Subtype.val hz)

end Concrete

end ArkLibTest.RingSwitchingConformance.Hachi
