/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Completeness
import ArkLib.Commitments.Functional.Hachi.Correctness

/-!
# Honest commitment coverage for the Hachi scalar trace head

The original scalar polynomial is packed coefficientwise, and the existing balanced-gadget
Hachi committer is applied to that ring polynomial. Its actual decommitment yields the same
norm-conditioned weak opening consumed by the trace head. No inverse packing norm is assumed.
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai ArkLib.Lattices.Ajtai.InnerOuter

namespace ArkLib.Lattices.Hachi.TraceHead

noncomputable section

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
variable {α κ innerRows outerRows dRows m r : ℕ}
variable (b : ℕ) (hb : 1 < b)
variable (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
  innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r) (Nat.clog b q) dRows)

/-- The weak opening carried by the actual honest committer, with challenge coefficients one. -/
def committedOpening (F : CMlPolynomial (Rq (powTwoCyclotomic (R := ZMod q) α)) (r + m)) :
    QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q) :=
  commitInputWitMap b (F, (commit b hb pp F).2)

/-- The actual honest decommitment decodes to the committed ring polynomial. -/
theorem extractedPoly_committedOpening
    (hdeg : 1 ≤ (powTwoCyclotomic (R := ZMod q) α).φ.natDegree)
    (hclog : 0 < Nat.clog b q)
    (F : CMlPolynomial (Rq (powTwoCyclotomic (R := ZMod q) α)) (r + m)) :
    extractedPoly (powTwoCyclotomic (R := ZMod q) α) (b : ZMod q)
      (committedOpening b hb pp F) = F := by
  let Φ := powTwoCyclotomic (R := ZMod q) α
  let dd := balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)
  have hw : committedOpening b hb pp F = honestOpening Φ
      (Decomposition.ofDigits Φ dd dd) pp.toPublicParams (Hachi.toMatrix F) := by
    unfold committedOpening commitInputWitMap honestOpening
    rw [commit_snd]
  rw [hw, extractedPoly]
  have hM : derivedMsgMatrix Φ (b : ZMod q) (honestOpening Φ
      (Decomposition.ofDigits Φ dd dd) pp.toPublicParams (Hachi.toMatrix F)) =
        Hachi.toMatrix F := by
    funext i k
    exact congrFun (generateDecomps_derivedMessage Φ (b : ZMod q)
      (Decomposition.ofDigits Φ dd dd) (gadgetDecompose_lawful Φ hclog hdeg dd)
      pp.toPublicParams (Hachi.toMatrix F) i) k
  rw [hM, Hachi.toPolynomial_toMatrix]

variable (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)

/-- The actual scalar opening statement commits its packed monomial coefficients using the
existing Hachi committer and claims the scalar polynomial's evaluation. -/
def committedStatement
    (f : CMlPolynomial (fixedSubring (R := ZMod q) α (2 ^ κ)) ((r + m) + (α - κ)))
    (xl : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) r)
    (xh : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) m)
    (xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ)) :
    Statement q α κ innerRows (Nat.clog b q) outerRows (Nat.clog b q) dRows m r where
  u := (commit b hb pp (packCoefficients (coefficientEquiv q α κ h2 hk) f)).1
  xl := xl
  xh := xh
  xp := xp
  value := f.eval ((xl ++ xh) ++ xp)

/-- Every scalar coefficient polynomial and every scalar query has an honest source witness,
under the real Hachi balanced-digit norm bounds. This also supplies the stronger message bound
required by the current nonrecursive honest chain. -/
theorem committed_source_valid
    (hbq : b ≤ q / 2) (hdeg : 1 ≤ (powTwoCyclotomic (R := ZMod q) α).φ.natDegree)
    (hclog : 0 < Nat.clog b q) {βSq γ bound : ℕ} (hbound : 1 ≤ bound)
    (hβSq : (2 ^ m) * Nat.clog b q *
      ((powTwoCyclotomic (R := ZMod q) α).φ.natDegree * (b / 2) ^ 2) ≤ βSq)
    (hγ : b / 2 ≤ γ)
    (f : CMlPolynomial (fixedSubring (R := ZMod q) α (2 ^ κ)) ((r + m) + (α - κ)))
    (xl : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) r)
    (xh : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) m)
    (xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ)) :
    (committedStatement b hb pp hk h2 f xl xh xp,
      committedOpening b hb pp (packCoefficients (coefficientEquiv q α κ h2 hk) f)) ∈
      relInMsgShort α κ hk h2 pp (b : ZMod q) βSq γ bound (b / 2) := by
  let F := packCoefficients (coefficientEquiv q α κ h2 hk) f
  let x := (xl ++ xh).map (algebraMap _ (Rq (powTwoCyclotomic (R := ZMod q) α)))
  have hh := mem_relPolyEvalMsgShort_of_relCommitInput b hb hbq hdeg hclog hbound hβSq hγ pp
    ⟨(commit b hb pp F).1, ⟨x, F.eval x⟩⟩ (F, (commit b hb pp F).2) ⟨rfl, rfl⟩
  refine ⟨⟨hh.1.1, ?_⟩, hh.2⟩
  change (unpackCoefficients (coefficientEquiv q α κ h2 hk)
    (extractedPoly (powTwoCyclotomic (R := ZMod q) α) (b : ZMod q)
      (committedOpening b hb pp F))).eval ((xl ++ xh) ++ xp) = _
  rw [extractedPoly_committedOpening b hb pp hdeg hclog]
  change (unpackCoefficients (coefficientEquiv q α κ h2 hk)
    (packCoefficients (coefficientEquiv q α κ h2 hk) f)).eval _ = _
  rw [unpack_packCoefficients]
  rfl

end

end ArkLib.Lattices.Hachi.TraceHead
