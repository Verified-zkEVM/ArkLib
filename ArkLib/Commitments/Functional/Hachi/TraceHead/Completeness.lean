/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Protocol
import ArkLib.OracleReduction.Security.Basic

/-! # Honest execution of Hachi's trace head -/

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
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) : (pSpec (q := q) α).FullTranscript
  | ⟨0, _⟩ => honestMessage α κ base s w

omit [NeZero q] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual prover run has no effects and emits the stated message and untouched opening. -/
theorem prover_run (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (prover (oSpec := oSpec) α κ base).run s w =
      pure (honestTranscript α κ base s w,
        output α κ s (honestMessage α κ base s w), w) := by
  have step1 : (prover (oSpec := oSpec) α κ base).runToRound (Fin.last 1) s w =
      (prover (oSpec := oSpec) α κ base).processRound (0 : Fin 1)
        ((prover (oSpec := oSpec) α κ base).runToRound ((0 : Fin 1).castSucc) s w) :=
    Prover.runToRound_succ (0 : Fin 1) s w _
  have step0 : (prover (oSpec := oSpec) α κ base).runToRound ((0 : Fin 1).castSucc) s w =
      pure ((fun i => Fin.elim0 i), (s, w)) := rfl
  unfold Prover.run
  rw [step1, step0, Prover.processRound_of_dir_eq_P_to_V (0 : Fin 1) rfl]
  simp only [prover, Fin.isValue, liftM_pure, pure_bind]
  congr 2
  funext i
  fin_cases i
  rfl

/-- Every valid source produces a successful run with identical prover and verifier outputs. -/
theorem reduction_run (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (s, w) ∈ relIn α κ hk h2 pp base βSq γ bound) :
    (reduction (oSpec := oSpec) α κ hk base).run s w =
      pure ((honestTranscript α κ base s w,
        output α κ s (honestMessage α κ base s w), w),
          output α κ s (honestMessage α κ base s w)) := by
  have hc := check_honestMessage α κ hk h2 pp base βSq γ bound s w h
  unfold Reduction.run
  rw [show (reduction (oSpec := oSpec) α κ hk base).prover = prover α κ base from rfl,
    prover_run]
  simp only [liftM_pure, pure_bind, reduction, Verifier.run, verifier, honestTranscript, hc,
    if_true]
  rfl

/-- Perfect completeness for the actual trace-head reduction, from every shared initial state. -/
theorem perfectCompleteness (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ) :
    (reduction (oSpec := oSpec) α κ hk base).perfectCompleteness init impl
      (relIn α κ hk h2 pp base βSq γ bound)
      (relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  rw [reduction_run α κ hk h2 pp base βSq γ bound s w h] at hx
  simp only [OptionT.run_pure, mem_support_pure_iff] at hx
  subst hx
  exact ⟨_, rfl, mem_output_of_relIn α κ hk h2 pp base βSq γ bound s w h, rfl⟩

/-- The honest-chain source variant carries exactly the existing message-decomposition bound.
The security relation remains the ordinary norm-conditioned weak-opening relation. -/
def relInMsgShort (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    Set (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
      QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  {p | p ∈ relIn α κ hk h2 pp base βSq γ bound ∧
    ∀ i, vecLInftyNorm (powTwoCyclotomic (R := ZMod q) α) (p.2.message i) ≤ msgBound}

/-- The unchanged opening transports the stronger honest-chain bound without any inverse
packing norm inference. -/
theorem perfectCompleteness_msgShort (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    (reduction (oSpec := oSpec) α κ hk base).perfectCompleteness init impl
      (relInMsgShort α κ hk h2 pp base βSq γ bound msgBound)
      (relPolyEvalMsgShort (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound msgBound) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  rw [reduction_run α κ hk h2 pp base βSq γ bound s w h.1] at hx
  simp only [OptionT.run_pure, mem_support_pure_iff] at hx
  subst hx
  exact ⟨_, rfl, ⟨mem_output_of_relIn α κ hk h2 pp base βSq γ bound s w h.1, h.2⟩, rfl⟩

/-- The same actual extractor also preserves the honest-chain message-bound variant.
This statement is distinct from ordinary weak-opening CWSS and uses its matching output relation. -/
theorem coordinateWiseSpecialSoundWith_msgShort
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound msgBound : ℕ) :
    Verifier.coordinateWiseSpecialSoundWith init impl CWSSStructure.ofIsEmpty
      (relInMsgShort α κ hk h2 pp base βSq γ bound msgBound)
      (relPolyEvalMsgShort (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound msgBound)
      (verifier (oSpec := oSpec) α κ hk) (extractor α κ) := by
  intro s tree _ hAcc leaves hvalid
  obtain ⟨w, hw, out, hout, hrel⟩ := hvalid tree.onlyPath
  have hc : check α κ hk s (tree.onlyPath.fullTranscript 0) = true := by
    by_contra hfail
    exact Verifier.not_accepting_of_failure
      (V := verifier (oSpec := oSpec) α κ hk) (stmt := s)
      (tr := tree.onlyPath.fullTranscript) (by simp [verifier, hfail])
      (hAcc _ tree.onlyPath.mem_fullTranscripts)
  have hout' := Verifier.outputs_guarded_subsingleton init impl
    (verifier (oSpec := oSpec) α κ hk) (guardedForm α κ hk).check
    (guardedForm α κ hk).out (guardedForm α κ hk).verify_eq
    s tree.onlyPath.fullTranscript hout
  rw [hout'] at hrel
  exact ⟨w, hw, ⟨mem_relIn_of_output α κ hk h2 pp base βSq γ bound s _ w hc hrel.1, hrel.2⟩⟩

end

end ArkLib.Lattices.Hachi.TraceHead
