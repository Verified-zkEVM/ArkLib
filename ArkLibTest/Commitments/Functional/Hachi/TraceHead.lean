/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Commitment
import ArkLibTest.Commitments.Functional.Hachi.TraceHeadAlgebra

/-! # Hachi committer and one-message trace-head acceptance -/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter
open OracleComp OracleSpec ProtocolSpec

namespace HachiTraceHeadTest

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev B := HachiTraceHeadAlgebraTest.B
abbrev A := HachiTraceHeadAlgebraTest.A
abbrev Φ := powTwoCyclotomic (R := ZMod 5) 1

/-- Finite Ajtai parameters, all matrix entries equal to one. -/
def pp : PublicParamsD Φ 1 (2 ^ 0) (Nat.clog 2 5) 1 (2 ^ 1) (Nat.clog 2 5) 1 where
  innerMatrix := fun _ _ => 1
  outerMatrix := fun _ _ => 1
  dMatrix := fun _ _ => 1

private theorem hb : 1 < 2 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide
private theorem hk : 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide
private theorem hdeg : 1 ≤ Φ.φ.natDegree := by rw [powTwoCyclotomic_natDegree]; decide
private theorem hclog : 0 < Nat.clog 2 5 := by decide

abbrev f := HachiTraceHeadAlgebraTest.f

def s : Statement 5 1 0 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 :=
  committedStatement 2 hb pp hk h2 f #v[0] #v[] #v[1]

def w := committedOpening 2 hb pp (packCoefficients (n := 1) (t := 1)
  (coefficientEquiv 5 1 0 h2 hk) f)

/-- The nonconstant scalar polynomial has a weak opening from the committer,
with the concrete balanced-digit norm bounds and nonzero evaluation claim. -/
theorem source_valid : (s, w) ∈ relInMsgShort 1 0 hk h2 pp 2 6 1 1 1 := by
  exact committed_source_valid 2 hb pp hk h2 (by decide) hdeg hclog
    (by decide) (by rw [powTwoCyclotomic_natDegree]; decide) (by decide) f #v[0] #v[] #v[1]

/-- The source claim is the nonzero scalar value two. -/
theorem claim_two : s.value = (2 : B) :=
  HachiTraceHeadAlgebraTest.scalar_evaluation

/-- Honest execution retains the exact original opening and agrees on the forwarded ring value. -/
theorem run_retains_opening {ι : Type} (oSpec : OracleSpec ι) :
    (reduction (oSpec := oSpec) 1 0 hk 2).run s w =
      pure ((honestTranscript 1 0 2 s w, output 1 0 s (honestMessage 1 0 2 s w), w),
        output 1 0 s (honestMessage 1 0 2 s w)) :=
  reduction_run 1 0 hk h2 pp 2 6 1 1 s w source_valid.1

/-- A false source claim keeps every key, commitment, point, and opening fixed. -/
def bad : Statement 5 1 0 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 := {s with value := 0}

/-- Changing the scalar claim to zero makes the guard fail. -/
theorem false_claim_check : check 1 0 hk bad (honestMessage 1 0 2 s w) = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hout := mem_output_of_relIn 1 0 hk h2 pp 2 6 1 1 s w source_valid.1
  have hbout : (output 1 0 bad (honestMessage 1 0 2 s w), w) ∈
      relPolyEval Φ pp 2 6 1 1 := hout
  have hbad := mem_relIn_of_output 1 0 hk h2 pp 2 6 1 1 bad _ w hc hbout
  have hsource := source_valid.1.2
  have hz : s.value = 0 := hsource.symm.trans hbad.2
  rw [claim_two] at hz
  have hzA : (2 : A) = 0 := congrArg Subtype.val hz
  exact HachiTraceHeadAlgebraTest.value_ne_zero hzA

/-- False-claim rejection is verifier failure at the production wire format. -/
theorem false_claim_failure {ι : Type} (oSpec : OracleSpec ι) :
    (verifier (q := 5) (oSpec := oSpec) 1 0 hk).run bad (honestTranscript 1 0 2 s w) =
      failure := by
  simp only [Verifier.run, TraceHead.verifier, honestTranscript, false_claim_check,
    Bool.false_eq_true, if_false]

/-- The full honest-prover reduction also aborts after changing only the source scalar claim. -/
theorem false_claim_reduction_failure {ι : Type} (oSpec : OracleSpec ι) :
    (reduction (oSpec := oSpec) 1 0 hk 2).run bad w = failure := by
  unfold Reduction.run
  rw [show (reduction (oSpec := oSpec) 1 0 hk 2).prover = TraceHead.prover 1 0 2 from rfl,
    prover_run]
  simp only [liftM_pure, pure_bind]
  rw [show (reduction (oSpec := oSpec) 1 0 hk 2).verifier =
      TraceHead.verifier 1 0 hk from rfl,
    show honestTranscript 1 0 2 bad w = honestTranscript 1 0 2 s w from rfl,
    false_claim_failure]
  simp

/-- The live consumer instantiates the strong completeness theorem at every shared state. -/
theorem perfectCompleteness {ι σ : Type} (oSpec : OracleSpec ι)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (reduction (oSpec := oSpec) 1 0 hk 2).perfectCompleteness init impl
      (relInMsgShort 1 0 hk h2 pp 2 6 1 1 1) (relPolyEvalMsgShort Φ pp 2 6 1 1 1) :=
  perfectCompleteness_msgShort 1 0 hk h2 init impl pp 2 6 1 1 1

/-- The live consumer uses zero-challenge CWSS at the weak-opening relation. -/
theorem coordinate_wise_special_soundness {ι σ : Type} (oSpec : OracleSpec ι)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    Verifier.coordinateWiseSpecialSoundWith init impl CWSSStructure.ofIsEmpty
      (TraceHead.relIn 1 0 hk h2 pp 2 6 1 1) (relPolyEval Φ pp 2 6 1 1)
      (verifier (oSpec := oSpec) 1 0 hk) (extractor 1 0) :=
  coordinateWiseSpecialSoundWith 1 0 hk h2 init impl pp 2 6 1 1

end

end HachiTraceHeadTest
