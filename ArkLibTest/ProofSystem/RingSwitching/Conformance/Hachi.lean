/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Hachi §3.1 conformance to the shared packing algebra

Hachi's one-message trace head instantiates the shared ring-switching algebra: `packingData` is
a `PackingData` whose packing algebra is `Rq` and whose opening algebra is its fixed subring, and
`observation` is a `CheckedObservation` whose observation is the `ψ`-coordinate inner product,
equivalent to the scaled trace check (`check_iff_observation`).

The conformance theorem derives the head's exact relation correspondence from the shared
`CheckedObservation.honest_check` and `CheckedObservation.readback`: a passing check with a
valid ring-level opening holds iff the scalar relation holds and the sent value is honest. The
concrete instances show the honest side inhabited by a nonconstant polynomial, and that for a
false claim no sent ring value both passes the check and opens validly. The check alone is not
enough: for the false claim `0` the message `0` passes it.
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
the scalar relation, by the shared checked-observation laws. -/
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
      ((s, w) ∈ relIn α κ hk h2 pp base βSq γ bound ∧ Y = honestMessage α κ base s w) := by
  let D := observation α κ hk h2 base (innerRows := innerRows) (messageDigits := messageDigits)
    (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)
  constructor
  · rintro ⟨hc, hout⟩
    obtain ⟨hopen, hY⟩ := (output_mem_relPolyEval_iff α κ hk h2 pp base βSq γ bound s Y w).1 hout
    have hval : s.value = D.scalarEval s (D.witnessEquiv.symm w) :=
      D.readback ((check_iff_observation α κ hk h2 base s Y).1 hc) hY
    exact ⟨(relIn_iff_observation α κ hk h2 pp base βSq γ bound s w).2 ⟨hopen, hval⟩, hY⟩
  · rintro ⟨hin, rfl⟩
    obtain ⟨-, hval⟩ := (relIn_iff_observation α κ hk h2 pp base βSq γ bound s w).1 hin
    exact ⟨(check_iff_observation α κ hk h2 base s _).2 (D.honest_check hval),
      mem_output_of_relIn α κ hk h2 pp base βSq γ bound s w hin⟩

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
