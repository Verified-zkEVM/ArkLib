/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.Commitments.Ordinary.Ajtai.Simple.Correctness
import ArkLib.Commitments.Functional.Hachi.GadgetNorms

/-!
# Correctness of the Inner-Outer Ajtai Commitment

Perfect correctness for lawful gadget decompositions: if the message and inner gadget
decompositions invert their gadget matrices, an honest commitment always verifies.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec (Rq Φ) messageRows)]
variable [DecidableEq (PolyVec (Rq Φ) innerRows)]
variable [DecidableEq (Commitment Φ outerRows)]

omit [DecidableEq (PolyVec (Rq Φ) messageRows)] [DecidableEq (PolyVec (Rq Φ) innerRows)]
  [DecidableEq (Commitment Φ outerRows)] in
/-- Honest message decompositions recover the message: `G · sᵢ = mᵢ` (`derivedMessage = m`). -/
theorem generateDecomps_derivedMessage (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) (i : Fin blocks) :
    derivedMessage Φ base (generateDecomps Φ decomp pp m) i = m i := by
  simpa [derivedMessage, Simple.commit, gadgetMul, generateDecomps] using hMessageDecomp (m i)

omit [DecidableEq (PolyVec (Rq Φ) innerRows)] [DecidableEq (Commitment Φ outerRows)] in
/-- Honest message decompositions pass the message gadget checks. -/
theorem generateDecomps_message_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base messageRows messageDigits)
        ((generateDecomps Φ decomp pp m).message i) (m i) ()) = true := by
  simp only [List.all_eq_true]
  intro i _
  have hprod : Simple.commit Φ (gadgetMatrix Φ base messageRows messageDigits)
      ((generateDecomps Φ decomp pp m).message i) = m i := by
    simpa [Simple.commit, gadgetMul, generateDecomps] using hMessageDecomp (m i)
  simp [Simple.verify, hprod]

omit [DecidableEq (PolyVec (Rq Φ) messageRows)] [DecidableEq (PolyVec (Rq Φ) innerRows)]
  [DecidableEq (Commitment Φ outerRows)] in
/-- Honest inner decompositions satisfy the inner gadget relation `G · t̂ᵢ = A sᵢ`. -/
theorem generateDecomps_inner_eq (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) (i : Fin blocks) :
    Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits)
        ((generateDecomps Φ decomp pp m).innerDecomp i) =
      Simple.commit Φ pp.innerMatrix ((generateDecomps Φ decomp pp m).message i) := by
  simpa [Simple.commit, gadgetMul, generateDecomps] using
    hInnerDecomp (Simple.commit Φ pp.innerMatrix (decomp.message (m i)))

omit [DecidableEq (PolyVec (Rq Φ) messageRows)] [DecidableEq (Commitment Φ outerRows)] in
/-- Honest inner decompositions pass the inner gadget checks. -/
theorem generateDecomps_inner_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        ((generateDecomps Φ decomp pp m).innerDecomp i)
        (Simple.commit Φ pp.innerMatrix ((generateDecomps Φ decomp pp m).message i)) ())
      = true := by
  simp only [List.all_eq_true]
  intro i _
  simp [Simple.verify, generateDecomps_inner_eq Φ base decomp hInnerDecomp pp m i]

end ArkLib.Lattices.Ajtai.InnerOuter

/-! ## Concrete instantiation over `ZMod q`

The genuine base-`b` (binary) gadget decomposition `zmodDigitDecomposition` instantiates the
inner-outer commitment over `R = ZMod q`, giving perfect correctness whenever `1 < b`, every
residue fits in the chosen digit count (`q ≤ b ^ digits`), and `1 ≤ deg φ`. -/

namespace ArkLib.Lattices.Ajtai.InnerOuter

section ZMod

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

omit [NeZero q] in
/-- **Perfect correctness of the inner-outer Ajtai commitment for lawful decompositions.**

The honest opening uses the trivial challenge `cᵢ = 1`, under which `verify_weak` reduces to the
ordinary honest check. Correctness therefore needs, beyond gadget lawfulness:
* the trivial challenge is an admissible challenge: `0 < ‖1‖₁` and `‖1‖₁ ≤ κ`;
* each honest message decomposition is `ℓ₂²`-short: `‖sᵢ‖₂² ≤ βSq`;
* the flattened honest inner decomposition is `ℓ∞`-short: `‖t̂‖∞ ≤ γ`.

The gadget relations (`derivedMessage = m`, inner `A sᵢ = G t̂ᵢ`, outer commit) hold structurally
from lawfulness; the bounds are exactly the weak-verifier side conditions for the honest case. -/
theorem perfectlyCorrect_of_lawful (base : ZMod q) (βSq γ κ : Nat)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (hκpos : 0 < ‖(1 : Rq Φ)‖₁)
    (hκle : ‖(1 : Rq Φ)‖₁ ≤ κ)
    (hβ : ∀ (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
            (m : Message Φ messageRows blocks) (i : Fin blocks),
            ‖(generateDecomps Φ decomp pp m).message i‖₂² ≤ βSq)
    (hγ : ∀ (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
            (m : Message Φ messageRows blocks),
            vecLInftyNorm Φ
              (PolyVec.flattenBlocks (generateDecomps Φ decomp pp m).innerDecomp) ≤ γ) :
    (commitmentScheme Φ (outerRows := outerRows) (blocks := blocks) base βSq γ κ
      decomp).PerfectlyCorrect := by
  intro pp _ m cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  simp only [commitmentScheme, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- the claimed message is the derived message of every block
    rw [List.all_eq_true]
    intro i _
    rw [decide_eq_true_eq]
    exact generateDecomps_derivedMessage Φ base decomp hMessageDecomp pp m i
  · -- the honest opening (challenge `cᵢ = 1`) passes weak verification
    have hone : ∀ (v : PolyVec (Rq Φ) (messageRows * messageDigits)),
        (1 : Rq Φ) •ᵥ v = v := fun v => by funext j; simp
    simp only [verify_weak, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro i _
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨hκpos, hκle⟩, ?_⟩, ?_⟩
      · rw [hone]; exact hβ pp m i
      · rw [Simple.verify_eq_true_iff]
        exact generateDecomps_inner_eq Φ base decomp hInnerDecomp pp m i
    · rw [decide_eq_true_eq]; exact hγ pp m
    · rw [Simple.verify_eq_true_iff]; rfl

omit [NeZero q] in
/-- **Perfect correctness for genuine base-`b` (Hachi gadget `G⁻¹`) decompositions**, modulo the
weak-verifier shortness side conditions. Instantiates `perfectlyCorrect_of_lawful` with
`gadgetDecompose` (lawful by `gadgetDecompose_lawful`), discharging gadget lawfulness; the
trivial-challenge admissibility (`hκpos`, `hκle`) and the honest shortness bounds (`hβ`, `hγ`)
remain explicit. For the concrete binary decomposition they are discharged unconditionally by
`perfectlyCorrect` below (via `Rq.l1Norm_one` and the `GadgetNorms` bounds). -/
theorem perfectlyCorrect_of_digits (base : ZMod q) (βSq γ κ : Nat)
    (hdeg : 1 ≤ Φ.φ.natDegree) (hmsg : 0 < messageDigits) (hinner : 0 < innerDigits)
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits)
    (hκpos : 0 < ‖(1 : Rq Φ)‖₁) (hκle : ‖(1 : Rq Φ)‖₁ ≤ κ)
    (hβ : ∀ (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
            (m : Message Φ messageRows blocks) (i : Fin blocks),
            ‖(generateDecomps Φ (Decomposition.ofDigits Φ ddMsg ddInner) pp m).message i‖₂² ≤ βSq)
    (hγ : ∀ (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
            (m : Message Φ messageRows blocks),
            vecLInftyNorm Φ (PolyVec.flattenBlocks
              (generateDecomps Φ (Decomposition.ofDigits Φ ddMsg ddInner) pp m).innerDecomp) ≤ γ) :
    (commitmentScheme Φ (messageRows := messageRows) (innerRows := innerRows)
      (outerRows := outerRows) (blocks := blocks) base βSq γ κ
      (Decomposition.ofDigits Φ ddMsg ddInner)).PerfectlyCorrect :=
  perfectlyCorrect_of_lawful Φ base βSq γ κ (Decomposition.ofDigits Φ ddMsg ddInner)
    (gadgetDecompose_lawful Φ hmsg hdeg ddMsg)
    (gadgetDecompose_lawful Φ hinner hdeg ddInner)
    hκpos hκle hβ hγ

/-- **Unconditional perfect correctness with the concrete binary decomposition.** Both message
and inner decompositions are the genuine base-`b` digit decomposition of `ZMod q`
(`zmodDigitDecomposition`, the Hachi gadget inverse `G⁻¹`). All weak-verifier side conditions are
discharged automatically: the trivial challenge `cᵢ = 1` is short (`Rq.l1Norm_one`), and the
digit decompositions are short (`GadgetNorms`), with `βSq := (mr·md)·(deg φ)·(b-1)²` and
`γ := b - 1`. The hypotheses are exactly those for reconstruction (`1 < b`, `q ≤ bᵈⁱᵍⁱᵗˢ`,
`1 ≤ deg φ`, positive digit counts), plus `1 ≤ κ` and the no-wraparound condition `b - 1 ≤ q/2`
for the centered digit norm. -/
theorem perfectlyCorrect (b κ : ℕ) (hb : 1 < b) (hκ : 1 ≤ κ) (hbq : b - 1 ≤ q / 2)
    (hdeg : 1 ≤ Φ.φ.natDegree) (hmsg : 0 < messageDigits) (hinner : 0 < innerDigits)
    (hqm : q ≤ b ^ messageDigits) (hqi : q ≤ b ^ innerDigits) :
    (commitmentScheme Φ (messageRows := messageRows) (innerRows := innerRows)
        (outerRows := outerRows) (blocks := blocks) (b : ZMod q)
        (messageRows * messageDigits * (Φ.φ.natDegree * (b - 1) ^ 2))
        (b - 1) κ
        (Decomposition.ofDigits Φ (zmodDigitDecomposition b messageDigits hb hqm)
          (zmodDigitDecomposition b innerDigits hb hqi))).PerfectlyCorrect := by
  refine perfectlyCorrect_of_digits Φ (b : ZMod q) _ _ κ hdeg hmsg hinner _ _ ?_ ?_ ?_ ?_
  · rw [Rq.l1Norm_one Φ hdeg]; norm_num
  · rw [Rq.l1Norm_one Φ hdeg]; exact hκ
  · intro pp m i
    exact gadgetDecompose_zmod_vecL2NormSq_le Φ hb hqm hbq hdeg (m i)
  · intro pp m
    exact vecLInftyNorm_flattenBlocks_le Φ _
      (fun i => gadgetDecompose_zmod_vecLInftyNorm_le Φ hb hqi hbq hdeg _)

end ZMod

end ArkLib.Lattices.Ajtai.InnerOuter
