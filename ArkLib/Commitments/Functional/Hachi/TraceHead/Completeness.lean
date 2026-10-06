/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Commitments.Functional.Hachi.TraceHead.Protocol
public import ArkLib.OracleReduction.Security.Basic

/-! # Honest execution of Hachi's trace head

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai.InnerOuter
open OracleComp OracleSpec ProtocolSpec

namespace ArkLib.Lattices.Hachi.TraceHead

noncomputable section

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
variable (α κ : ℕ)
variable {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
variable {ι : Type} {oSpec : OracleSpec ι}

/-- The honest transcript contains exactly the one ring evaluation sent by the prover. -/
def honestTranscript (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (pSpecTraceHead (q := q) α).FullTranscript
  | ⟨0, _⟩ => honestMessage α κ base s w

omit [NeZero q] in
/-- The prover run has no effects and emits the trace message while preserving the opening. -/
theorem traceHeadProver_run (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (traceHeadProver (oSpec := oSpec) α κ base).run s w =
      pure (honestTranscript α κ base s w,
        output α κ s (honestMessage α κ base s w), w) := by
  rw [Prover.run_of_prover_first]
  simp only [traceHeadProver, liftComp_pure, pure_bind]
  congr 2

/-- Every valid source produces a successful run with identical prover and verifier outputs. -/
theorem traceHeadReduction_run (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound) :
    (traceHeadReduction (oSpec := oSpec) α κ hk base).run s w =
      pure ((honestTranscript α κ base s w,
        output α κ s (honestMessage α κ base s w), w),
          output α κ s (honestMessage α κ base s w)) := by
  have hc := check_honestMessage α κ hk h2 pp base βSq γ bound s w h
  unfold Reduction.run
  rw [show (traceHeadReduction (oSpec := oSpec) α κ hk base).prover =
      traceHeadProver α κ base from rfl,
    traceHeadProver_run]
  simp only [liftM_pure, pure_bind, traceHeadReduction, Verifier.run, traceHeadVerifier,
    honestTranscript, hc, ite_true]
  rfl

/-- Perfect completeness of the trace head from every shared initial state. -/
theorem traceHeadReduction_perfectCompleteness (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ) :
    (traceHeadReduction (oSpec := oSpec) α κ hk base).perfectCompleteness init impl
      (relScalarEval α κ hk h2 pp base βSq γ bound)
      (relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  rw [traceHeadReduction_run α κ hk h2 pp base βSq γ bound s w h] at hx
  simp only [OptionT.run_pure, mem_support_pure_iff] at hx
  subst hx
  exact ⟨_, rfl,
    output_mem_relPolyEval_of_mem_relScalarEval α κ hk h2 pp base βSq γ bound s w h, rfl⟩

/-- The honest-chain source variant carries exactly the existing message-decomposition bound.
The security relation remains the ordinary norm-conditioned weak-opening relation. -/
def relScalarEvalMsgShort (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    Set (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
      QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  {p | p ∈ relScalarEval α κ hk h2 pp base βSq γ bound ∧
    ∀ i, vecLInftyNorm (powTwoCyclotomic (R := ZMod q) α) (p.2.message i) ≤ msgBound}

/-- Perfect completeness with the stronger message norm bound on the opening witness. -/
theorem traceHeadReduction_perfectCompleteness_msgShort
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    (traceHeadReduction (oSpec := oSpec) α κ hk base).perfectCompleteness init impl
      (relScalarEvalMsgShort α κ hk h2 pp base βSq γ bound msgBound)
      (relPolyEvalMsgShort (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound msgBound) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  rw [traceHeadReduction_run α κ hk h2 pp base βSq γ bound s w h.1] at hx
  simp only [OptionT.run_pure, mem_support_pure_iff] at hx
  subst hx
  exact ⟨_, rfl,
    ⟨output_mem_relPolyEval_of_mem_relScalarEval α κ hk h2 pp base βSq γ bound s w h.1, h.2⟩,
    rfl⟩

/--
Coordinate-wise special soundness with the additional message norm bound and the identity
opening extractor.
-/
theorem traceHeadVerifier_coordinateWiseSpecialSoundWith_msgShort
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    Verifier.coordinateWiseSpecialSoundWith init impl CWSSStructure.ofIsEmpty
      (relScalarEvalMsgShort α κ hk h2 pp base βSq γ bound msgBound)
      (relPolyEvalMsgShort (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound msgBound)
      (traceHeadVerifier (oSpec := oSpec) α κ hk) (traceHeadExtractor α κ) :=
  traceHeadVerifier_coordinateWiseSpecialSoundWith_of_output α κ hk init impl fun s Y w hc h =>
    ⟨mem_relScalarEval_of_output α κ hk h2 pp base βSq γ bound s Y w hc h.1, h.2⟩

end

end ArkLib.Lattices.Hachi.TraceHead
