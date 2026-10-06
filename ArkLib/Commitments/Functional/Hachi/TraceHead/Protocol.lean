/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Commitments.Functional.Hachi.TraceHead.Coordinates
public import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation
public import ArkLib.Commitments.Functional.Hachi.QuadEval.Bridge
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import ArkLib.OracleReduction.Composition.Sequential.Append.OneMessage

/-!
# Hachi §3.1: the one-message scalar-to-ring trace head

The input polynomial is the coefficientwise decoding of the weak opening of the
committed ring polynomial. The sole message is the latter's evaluation at the retained point.
The verifier checks the unnormalized trace equation and forwards the same commitment and weak
opening to `relPolyEval`. All norm and key parameters of `VerifiedOpening` remain unchanged.
The verifier is stated with the noncomputable `traceH`; the computable `traceHComp` agrees with it
(`traceHComp_eq`), but this protocol is not wired to it.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai.InnerOuter ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise

namespace ArkLib.Lattices.Hachi.TraceHead

noncomputable section

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
variable (α κ : ℕ)
variable {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
variable {ι : Type} {oSpec : OracleSpec ι}

/--
A scalar query with retained variables split into low/high blocks, followed by the packed
suffix.
-/
structure Statement (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
    (α κ innerRows messageDigits outerRows innerDigits dRows m r : ℕ) where
  /-- The outer commitment used by the ring-level opening protocol. -/
  u : Commitment (powTwoCyclotomic (R := ZMod q) α) outerRows
  /-- The first retained variables, indexing matrix rows downstream. -/
  xl : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) r
  /-- The remaining retained variables, indexing matrix columns downstream. -/
  xh : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) m
  /-- The final variables, whose monomial coefficients are packed. -/
  xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ)
  /-- The claimed scalar evaluation. -/
  value : fixedSubring (R := ZMod q) α (2 ^ κ)

/-- Exactly one ring-element message and no challenge. -/
def pSpecTraceHead : ProtocolSpec 1 :=
  ProtocolSpec.oneMessage (Rq (powTwoCyclotomic (R := ZMod q) α))

instance : IsEmpty (pSpecTraceHead (q := q) α).ChallengeIdx :=
  inferInstanceAs (IsEmpty (ProtocolSpec.oneMessage _).ChallengeIdx)
instance : ∀ i, SampleableType ((pSpecTraceHead (q := q) α).Challenge i) :=
  inferInstanceAs (∀ i, SampleableType ((ProtocolSpec.oneMessage _).Challenge i))
instance : ProverOnly (pSpecTraceHead (q := q) α) :=
  inferInstanceAs (ProverOnly (ProtocolSpec.oneMessage _))

/-- The ring-level statement drops the suffix and forwards the sent value. -/
def output (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α)) :
    PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
      innerRows messageDigits outerRows innerDigits dRows m r where
  u := s.u
  xl := s.xl.map (algebraMap _ _)
  xh := s.xh.map (algebraMap _ _)
  y := Y

variable (hk : 2 * 2 ^ κ ∣ 2 ^ α)

/-- The packed monomial vector computed by `psi`. -/
def packedMonomial (xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ)) :
    Rq (powTwoCyclotomic (R := ZMod q) α) :=
  psi α (2 ^ κ) (fun j => (CMlPolynomial.monomialBasis xp).get
    (finCongr (packingRank_eq α κ hk) j))

/-- The scaled trace equality checked in the quotient ring. -/
def check (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α)) : Bool :=
  traceH α (2 ^ κ) (Y * conjAut α (packedMonomial α κ hk s.xp)) ==
    (2 ^ α / 2 ^ κ) • (s.value : Rq (powTwoCyclotomic (R := ZMod q) α))

/-- A failed scalar trace check aborts; a passing one forwards the sent ring evaluation. -/
def traceHeadVerifier : Verifier oSpec
    (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
      innerRows messageDigits outerRows innerDigits dRows m r) (pSpecTraceHead (q := q) α) where
  verify := fun s tr => if check α κ hk s (tr 0) then pure (output α κ s (tr 0)) else failure

/-- The exact runtime guard and output are data for guarded composition. -/
def traceHeadGuardedForm : (traceHeadVerifier (q := q) (oSpec := oSpec) α κ hk
    (innerRows := innerRows) (messageDigits := messageDigits) (outerRows := outerRows)
    (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)).GuardedForm where
  check := fun s tr => check α κ hk s (tr 0)
  out := fun s tr => output α κ s (tr 0)
  verify_eq := fun _ _ => rfl

variable (h2 : (2 : ZMod q) ≠ 0)

/--
A norm-conditioned weak opening of the commitment whose coefficientwise decoding has the
claimed scalar evaluation.
-/
def relScalarEval
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ) :
    Set (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
      QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  {p | VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
      pp.toPublicParams p.1.u p.2 ∧
    (unpackCoefficients (coefficientEquiv q α κ h2 hk)
      (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base p.2)).eval
        ((p.1.xl ++ p.1.xh) ++ p.1.xp) = p.1.value}

/-- Evaluate the ring polynomial extracted from the weak opening at the retained point. -/
def honestMessage (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    Rq (powTwoCyclotomic (R := ZMod q) α) :=
  (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w).eval
    ((s.xl ++ s.xh).map (algebraMap _ _))

/--
Checked observation of the ring evaluation, using the coefficient packing equivalence and
preserving the weak-opening witness.
-/
def observation (base : ZMod q) : RingSwitching.Packing.CheckedObservation
    (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (Rq (powTwoCyclotomic (R := ZMod q) α)) (fixedSubring (R := ZMod q) α (2 ^ κ)) where
  witnessEquiv := Equiv.refl _
  honestMsg := honestMessage α κ base
  scalarEval s w :=
    (unpackCoefficients (coefficientEquiv q α κ h2 hk)
      (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w)).eval
        ((s.xl ++ s.xh) ++ s.xp)
  observe s Y := ∑ j, (coefficientEquiv q α κ h2 hk).symm Y j *
    (CMlPolynomial.monomialBasis s.xp).get j
  eval_eq_observe s w := unpackCoefficients_eval (coefficientEquiv q α κ h2 hk)
    (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w) (s.xl ++ s.xh) s.xp

/--
The input relation is the conjunction of the weak-opening predicate and the scalar observation
equation.
-/
theorem mem_relScalarEval_iff_observation
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound ↔
      VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
        pp.toPublicParams s.u w ∧
          s.value = (observation α κ hk h2 base).scalarEval s w := by
  exact and_congr_right fun _ => eq_comm

/-- The scaled-trace guard is equivalent to the observation equality for every sent ring value. -/
theorem check_iff_observation (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α)) :
    check α κ hk s Y = true ↔ s.value = (observation α κ hk h2 base).observe s Y := by
  have h := traceH_coefficientEquiv_eq_iff q α κ h2 hk
    ((coefficientEquiv q α κ h2 hk).symm Y) (CMlPolynomial.monomialBasis s.xp).get s.value
  rw [LinearEquiv.apply_symm_apply] at h
  rw [check, beq_iff_eq]
  change traceH α (2 ^ κ) (Y * conjAut α
      (coefficientEquiv q α κ h2 hk (CMlPolynomial.monomialBasis s.xp).get)) =
    (2 ^ α / 2 ^ κ) • (s.value : Rq (powTwoCyclotomic α)) ↔ _
  rw [h]
  exact eq_comm

/-- The existing output relation fixes the honest ring value and keeps the original opening. -/
theorem output_mem_relPolyEval_iff
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (output α κ s Y, w) ∈
      relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound ↔
      VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
        pp.toPublicParams s.u w ∧
          Y = (observation α κ hk h2 base).honestMsg s w := by
  change (_ ∧ (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w).eval
    (s.xl.map (algebraMap _ _) ++ s.xh.map (algebraMap _ _)) = Y) ↔ _
  simp only [observation, honestMessage, Vector.map_append]
  exact and_congr_right fun _ => eq_comm

/-- A valid ring-level opening and a passing check imply the original scalar claim. -/
theorem mem_relScalarEval_of_output
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (hc : check α κ hk s Y = true)
    (hout : (output α κ s Y, w) ∈
      relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) :
    (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound := by
  apply (mem_relScalarEval_iff_observation α κ hk h2 pp base βSq γ bound s w).2
  have ho := (output_mem_relPolyEval_iff α κ hk h2 pp base βSq γ bound s Y w).1 hout
  have hr := (observation α κ hk h2 base).readback
    ((check_iff_observation α κ hk h2 base s Y).1 hc) ho.2
  exact ⟨by simpa only [Equiv.apply_symm_apply] using ho.1, hr⟩

/-- Scalar source validity makes the honest ring evaluation pass the exact trace check. -/
theorem check_honestMessage
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound) :
    check α κ hk s (honestMessage α κ base s w) = true := by
  apply (check_iff_observation α κ hk h2 base s _).2
  exact (observation α κ hk h2 base).honest_check
    ((mem_relScalarEval_iff_observation α κ hk h2 pp base βSq γ bound s w).1 h).2

/-- The honest output preserves the norm-conditioned opening and gives its ring evaluation. -/
theorem output_mem_relPolyEval_of_mem_relScalarEval
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound) :
    (output α κ s (honestMessage α κ base s w), w) ∈
      relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound := by
  refine ⟨h.1, ?_⟩
  simp only [output, honestMessage, Vector.map_append]

/-- The one-message prover forwards its input weak opening. -/
def traceHeadProver (base : ZMod q) : Prover oSpec
    (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
      innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) (pSpecTraceHead (q := q) α) where
  PrvState
    | 0 => Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
        QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
          innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits
    | 1 => Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
        QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
          innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (honestMessage α κ base st.1 st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun st => pure (output α κ st.1 (honestMessage α κ base st.1 st.2), st.2)

/-- The trace head's protocol object uses precisely the verifier certified below. -/
def traceHeadReduction (base : ZMod q) : Reduction oSpec
    (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
      innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) (pSpecTraceHead (q := q) α) where
  prover := traceHeadProver α κ base
  verifier := traceHeadVerifier α κ hk

/-- The extractor returns the weak opening from the unique valid leaf. -/
def traceHeadExtractor : Extractor.TreeBased
    (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (pSpecTraceHead (q := q) α)
    (CWSSStructure.ofIsEmpty (pSpec := pSpecTraceHead (q := q) α)).toShape.arity :=
  fun _ tree leaves => leaves tree.onlyPath

omit [NeZero q] in
/--
Zero-challenge coordinate-wise special soundness of the guarded trace head between any relations
for which a passing check and a valid output leaf certify the input, extracting the weak opening
from that leaf.
-/
theorem traceHeadVerifier_coordinateWiseSpecialSoundWith_of_output {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn' : Set (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r ×
      QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)}
    {relOut' : Set (PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
        innerRows messageDigits outerRows innerDigits dRows m r ×
      QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)}
    (h : ∀ s Y w, check α κ hk s Y = true → (output α κ s Y, w) ∈ relOut' → (s, w) ∈ relIn') :
    Verifier.coordinateWiseSpecialSoundWith init impl CWSSStructure.ofIsEmpty relIn' relOut'
      (traceHeadVerifier (oSpec := oSpec) α κ hk) (traceHeadExtractor α κ) := by
  intro s tree _ hAcc leaves hvalid
  obtain ⟨w, hw, out, hout, hrel⟩ := hvalid tree.onlyPath
  have hc : check α κ hk s (tree.onlyPath.fullTranscript 0) = true := by
    by_contra hfail
    exact Verifier.not_accepting_of_failure
      (V := traceHeadVerifier (oSpec := oSpec) α κ hk) (stmt := s)
      (tr := tree.onlyPath.fullTranscript) (by simp [traceHeadVerifier, hfail])
      (hAcc _ tree.onlyPath.mem_fullTranscripts)
  have hout' := Verifier.outputs_guarded_subsingleton init impl
    (traceHeadVerifier (oSpec := oSpec) α κ hk) (traceHeadGuardedForm α κ hk).check
    (traceHeadGuardedForm α κ hk).out (traceHeadGuardedForm α κ hk).verify_eq
    s tree.onlyPath.fullTranscript hout
  rw [hout'] at hrel
  exact ⟨w, hw, h s _ w hc hrel⟩

/--
Zero-challenge coordinate-wise special soundness of the guarded trace head into `relPolyEval`.
-/
theorem traceHeadVerifier_coordinateWiseSpecialSoundWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ) :
    Verifier.coordinateWiseSpecialSoundWith init impl CWSSStructure.ofIsEmpty
      (relScalarEval α κ hk h2 pp base βSq γ bound)
      (relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound)
      (traceHeadVerifier (oSpec := oSpec) α κ hk) (traceHeadExtractor α κ) :=
  traceHeadVerifier_coordinateWiseSpecialSoundWith_of_output α κ hk init impl
    (mem_relScalarEval_of_output α κ hk h2 pp base βSq γ bound)

/--
Guarded coordinate-wise special soundness data for composition with downstream weak-opening
reductions.
-/
def traceHeadPackage {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ) : GCWSSPackage init impl
      (Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (PolyEvalStatement (powTwoCyclotomic (R := ZMod q) α)
        innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
        innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) (pSpecTraceHead (q := q) α) where
  verifier := traceHeadVerifier α κ hk
  struct := CWSSStructure.ofIsEmpty
  relIn := relScalarEval α κ hk h2 pp base βSq γ bound
  relOut := relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound
  isGuarded := traceHeadGuardedForm α κ hk
  extractor := traceHeadExtractor α κ
  isCWSS := traceHeadVerifier_coordinateWiseSpecialSoundWith α κ hk h2 init impl pp base βSq γ bound

end

end ArkLib.Lattices.Hachi.TraceHead
