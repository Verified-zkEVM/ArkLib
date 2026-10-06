/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Finite observation in the Hachi trace head

A polynomial with distinct coefficients, evaluated at non-Boolean points, through the production
committer, weak opening and rejecting verifier. The general theorems guard the pack/unpack index
order; the concrete computation here is the scalar evaluation.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter
open OracleComp OracleSpec ProtocolSpec

namespace HachiTraceHeadObservationTest

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev B := HachiTraceHeadAlgebraTest.B
abbrev A := HachiTraceHeadAlgebraTest.A
abbrev Φ := HachiTraceHeadTest.Φ
abbrev pp := HachiTraceHeadTest.pp

private theorem hb : 1 < 2 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide
private theorem hk : 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide

/-- The coefficients are ordered as `1 + 2X + 3Y + 4XY`. -/
def f : CMlPolynomial B (1 + 1) := #v[1, 2, 3, 4]

def F : CMlPolynomial A 1 := packCoefficients (coefficientEquiv 5 1 0 h2 hk) f

/-- Monomial evaluation at two non-Boolean points. -/
theorem scalar_value : f.eval (#v[(2 : B)] ++ #v[(3 : B)]) = (3 : B) := by
  have heval : f.eval (#v[(2 : B)] ++ #v[(3 : B)]) = (38 : B) := by
    rw [eval_eq_sum]
    simp [f, monomialBasis_get, Fin.sum_univ_succ, Fin.prod_univ_succ]
    norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [heval]
  apply Subtype.ext
  change (38 : A) = 3
  apply (Rq.equivQuotient Φ).injective
  simp only [map_ofNat]
  simpa only [map_ofNat] using congrArg (algebraMap (ZMod 5) Φ.CyclotomicRing)
    (by decide : (38 : ZMod 5) = 3)

/-- The observation reconstructs the original coefficient claim from the packed evaluation. -/
theorem observation_value :
    ∑ j, (coefficientEquiv 5 1 0 h2 hk).symm (F.eval ((#v[(2 : B)]).map (algebraMap B A))) j *
        (CMlPolynomial.monomialBasis #v[(3 : B)]).get j = (3 : B) := by
  refine (unpackCoefficients_eval (coefficientEquiv 5 1 0 h2 hk) F #v[2] #v[3]).symm.trans ?_
  rw [F, unpackCoefficients_packCoefficients]
  exact scalar_value

/-- The concrete verifier's trace remains scaled by two. -/
theorem scaled_trace :
    traceH 1 1 (F.eval ((#v[(2 : B)]).map (algebraMap B A)) *
      conjAut 1 (coefficientEquiv 5 1 0 h2 hk (CMlPolynomial.monomialBasis #v[(3 : B)]).get)) =
        2 • (3 : A) := by
  apply (traceH_eval_eq_iff 5 1 0 h2 hk F #v[2] #v[3] 3).2
  rw [unpackCoefficients_eval]
  exact observation_value

def s : Statement 5 1 0 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 :=
  committedStatement 2 hb pp hk h2 f #v[2] #v[] #v[3]

def w := committedOpening 2 hb pp F

/-- The balanced-gadget committer gives the original, norm-conditioned weak opening. -/
theorem source_valid : (s, w) ∈ relScalarEvalMsgShort 1 0 hk h2 pp 2 6 1 1 1 :=
  committedStatement_mem_relScalarEvalMsgShort 2 hb pp hk h2 (by decide)
    (by decide) (by rw [powTwoCyclotomic_natDegree]; decide) (by decide) f #v[2] #v[] #v[3]

/-- The protocol checks the asymmetric source, forwarding the same weak opening. -/
theorem run {ι : Type} (oSpec : OracleSpec ι) :
    (traceHeadReduction (oSpec := oSpec) 1 0 hk 2).run s w =
      pure ((honestTranscript 1 0 2 s w, output 1 0 s (honestMessage 1 0 2 s w), w),
        output 1 0 s (honestMessage 1 0 2 s w)) :=
  traceHeadReduction_run 1 0 hk h2 pp 2 6 1 1 s w source_valid.1

/-- Only the scalar value changes; all commitment, query and witness data are retained. -/
def bad : Statement 5 1 0 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1 := {s with value := 0}

/-- A false scalar claim fails the trace check on the same valid ring opening. -/
theorem false_claim_check : check 1 0 hk bad (honestMessage 1 0 2 s w) = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hout := output_mem_relPolyEval_of_mem_relScalarEval 1 0 hk h2 pp 2 6 1 1 s w source_valid.1
  have hbout : (output 1 0 bad (honestMessage 1 0 2 s w), w) ∈
      relPolyEval Φ pp 2 6 1 1 := hout
  have hbad := mem_relScalarEval_of_output 1 0 hk h2 pp 2 6 1 1 bad _ w hc hbout
  have hz : s.value = 0 := source_valid.1.2.symm.trans hbad.2
  change f.eval (#v[2] ++ #v[3]) = 0 at hz
  rw [scalar_value] at hz
  have hzA : (3 : A) = 0 := congrArg Subtype.val hz
  have htwo : (2 : A) = 0 := by
    have hfive : (5 : A) = 0 := by
      apply (Rq.equivQuotient Φ).injective
      simp only [map_ofNat, map_zero]
      simpa only [map_ofNat, map_zero] using congrArg
        (algebraMap (ZMod 5) Φ.CyclotomicRing) (by decide : (5 : ZMod 5) = 0)
    calc
      (2 : A) = 5 - 3 := by ring
      _ = 0 := by rw [hfive, hzA, sub_self]
  exact HachiTraceHeadAlgebraTest.value_ne_zero htwo

/-- Rejection is failure at the existing one-message production wire format. -/
theorem verifier_failure {ι : Type} (oSpec : OracleSpec ι) :
    (traceHeadVerifier (q := 5) (oSpec := oSpec) 1 0 hk).run bad (honestTranscript 1 0 2 s w) =
      failure := by
  simp only [Verifier.run, TraceHead.traceHeadVerifier, honestTranscript, false_claim_check,
    Bool.false_eq_true, ite_false]

/-- The complete production reduction also aborts for the same false scalar claim. -/
theorem reduction_failure {ι : Type} (oSpec : OracleSpec ι) :
    (traceHeadReduction (oSpec := oSpec) 1 0 hk 2).run bad w = failure := by
  unfold Reduction.run
  rw [show (traceHeadReduction (oSpec := oSpec) 1 0 hk 2).prover =
      TraceHead.traceHeadProver 1 0 2 from rfl,
    traceHeadProver_run]
  simp only [liftM_pure, pure_bind]
  rw [show (traceHeadReduction (oSpec := oSpec) 1 0 hk 2).verifier =
      TraceHead.traceHeadVerifier 1 0 hk from rfl,
    show honestTranscript 1 0 2 bad w = honestTranscript 1 0 2 s w from rfl, verifier_failure]
  simp

/-- With no retained variables the observation pairs the packed constant with the monomials. -/
theorem no_retained_variables (G : CMlPolynomial A 0) (xp : Vector B 1) :
    (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk) G).eval ((#v[] : Vector B 0) ++ xp) =
      ∑ j, (coefficientEquiv 5 1 0 h2 hk).symm (G.eval (#v[] : Vector A 0)) j *
        (CMlPolynomial.monomialBasis xp).get j :=
  unpackCoefficients_eval _ G #v[] xp

end

end HachiTraceHeadObservationTest
