/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Commitment
import ArkLibTest.ProofSystem.RingSwitching.Conformance.Hachi

/-!
# The Hachi trace head with a nontrivial second generator

At `q = 5`, `d = 2^3 = 8` and `k = 2^1 = 2`, the exponent of `σ_{4k+1} = σ₉` is not `1` modulo
`2d = 16`, so these are parameters at which the second generator of `H = ⟨σ₋₁, σ₉⟩` is not the
identity. The trace head packs the final two variables into four `ψ`-coordinates. Through the
general theorems, the committer's opening satisfies the scalar relation, the honest message passes,
and a false claim cannot both pass the check and open validly against the same weak opening.

The data here are base-field numerals, so no step computes `σ₉` on an element outside `ZMod 5`.
Evaluating `galoisAut` or the trace concretely needs `Rq` arithmetic, which does not reduce in the
kernel (`modByMonic` is defined by well-founded recursion), so `decide` cannot be used.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter

namespace HachiTraceHeadProperSubringTest

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev Φ := powTwoCyclotomic (R := ZMod 5) 3
abbrev B : Type := ↥(fixedSubring (R := ZMod 5) 3 (2 ^ 1))

/-- The second generator of `H` is not the identity modulo `2d`. -/
example : genExp (2 ^ 1) % (2 * 2 ^ 3) ≠ 1 := by decide

/-- Finite Ajtai parameters, all matrix entries equal to one. -/
def pp : PublicParamsD Φ 1 (2 ^ 0) (Nat.clog 2 5) 1 (2 ^ 1) (Nat.clog 2 5) 1 where
  innerMatrix := fun _ _ => 1
  outerMatrix := fun _ _ => 1
  dMatrix := fun _ _ => 1

private theorem hb : 1 < 2 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide
private theorem hk : 2 * 2 ^ 1 ∣ 2 ^ 3 := by decide

/-- A polynomial in one retained and two packed variables with distinct coefficients. -/
def f : CMlPolynomial B ((1 + 0) + (3 - 1)) := #v[1, 2, 3, 4, 0, 1, 2, 3]

def s : Statement 5 3 1 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 :=
  committedStatement 2 hb pp hk h2 f #v[2] #v[] #v[3, 4]

def w := committedOpening 2 hb pp (packCoefficients (coefficientEquiv 5 3 1 h2 hk) f)

/-- The honest committer's opening satisfies the scalar relation with its norm bounds. -/
theorem source_valid : (s, w) ∈ relScalarEvalMsgShort 3 1 hk h2 pp 2 24 1 1 1 :=
  committedStatement_mem_relScalarEvalMsgShort 2 hb pp hk h2 (by decide) (by decide)
    (by rw [powTwoCyclotomic_natDegree]; decide) (by decide) f #v[2] #v[] #v[3, 4]

/-- The honest message passes the check and its forwarded value opens validly. -/
example : check 3 1 hk s (honestMessage 3 1 2 s w) = true ∧
    (output 3 1 s (honestMessage 3 1 2 s w), w) ∈ relPolyEval Φ pp 2 24 1 1 :=
  (ArkLibTest.RingSwitchingConformance.Hachi.traceHead_conforms 3 1 hk h2 pp 2 24 1 1 s _ w).2
    ⟨source_valid.1, rfl⟩

/-- Shifting the claim by one keeps every key, commitment, point and opening fixed. -/
def bad : Statement 5 3 1 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 := {s with value := s.value + 1}

/-- For the false claim, no sent ring value both passes the check and opens validly. -/
example (Y : Rq Φ) :
    ¬ (check 3 1 hk bad Y = true ∧ (output 3 1 bad Y, w) ∈ relPolyEval Φ pp 2 24 1 1) := by
  intro h
  have hbad :=
    ((ArkLibTest.RingSwitchingConformance.Hachi.traceHead_conforms 3 1 hk h2 pp 2 24 1 1
      bad Y w).1 h).1
  have hsum : s.value + 1 = s.value := hbad.2.symm.trans source_valid.1.2
  have : Nontrivial (Rq Φ) := (Fintype.one_lt_card_iff_nontrivial).mp (by
    rw [Rq.card_powTwo]
    decide)
  exact one_ne_zero (add_eq_left.mp hsum)

end

end HachiTraceHeadProperSubringTest
