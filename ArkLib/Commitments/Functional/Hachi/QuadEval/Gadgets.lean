/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic

/-!
  # Hachi polynomial-evaluation reduction — gadget algebra (Hachi §4.2, Figure 3)

  Gadget algebra supporting **Hachi Lemma 8** — the coordinate-wise special soundness of Hachi's
  polynomial-evaluation reduction (Hachi [NOZ26] §4.2, Figure 3), proved in
  `QuadEval/Soundness.lean`. In that reduction the prover folds `2ʳ` committed witness blocks
  under a verifier challenge vector `c`, and the extractor recovers block `j` from two accepting
  transcripts whose challenges differ only in coordinate `j`: subtract the two verification
  equations so every other block cancels, then divide by the challenge difference. This file
  provides the definitions those equations are stated in and the subtraction/isolation identities
  the extraction step relies on; the protocol itself lives in `QuadEval/Reduction.lean`.

  Throughout, `G` is the base-`b` gadget matrix `I ⊗ [1, b, …]` of `Gadget/Core.lean` and `G⁻¹`
  its digit decomposition, with `G *ᵥ G⁻¹(x) = x`.

  ## Main definitions

  * `PublicParamsD`: the inner-outer public parameters `(A, B)` extended with the Hachi
    short-commitment matrix `D` (Hachi Eq. (16)).
  * `carrier`, `carrierDecomp`, `carrierCommit`: the honest-prover carrier `w` with
    `wᵢ = aᵀ G sᵢ` — the intermediate values tying the witness blocks `sᵢ` to the evaluation —
    its decomposition `ŵ = G⁻¹(w)`, and its short commitment `v = D ŵ` (Figure 3 round 0);
    `carrier_eq_gadget` is the roundtrip `w = G *ᵥ ŵ`.
  * `jMatrix`, `zDecomp`: the `J` gadget `J := I ⊗ [1, base, …]` (Eq. (18)–(20)) and the
    decomposed response `ẑ = J⁻¹(z)`; `z_eq_jMatrix` is the verifier's reconstruction
    `z = J *ᵥ ẑ`.
  * `tensorG`, `tensorG1`: the block-weighted gadget sums — the vector `(cᵀ ⊗ G_k) x̂`
    (Eq. (20) row 5) and the scalar `(cᵀ ⊗ G₁) ŵ` (Eq. (20) row 4).

  ## Main results

  * `tensorG_sub_challenge`, `tensorG1_sub_challenge`: both sums are subtractive in the challenge
    vector — Lemma 8's two-transcript subtraction.
  * `tensorG_coord_diff`, `tensorG1_coord_diff`: if `c` and `c'` differ only in coordinate `j`,
    the difference sum collapses to the single block `j` — the coordinate isolation that is the
    algebraic crux of the Lemma 8 subtract-and-divide extraction.

  Hachi's reduction (§4.2) is the multilinear / inner-outer lift of Greyhound's [NS24, §3.1]
  folding-based polynomial-evaluation protocol; this file is its gadget layer.

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open scoped BigOperators

namespace ArkLib.Lattices.Hachi

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- Inner-outer params `(A, B)` extended with the Hachi short-commitment matrix `D`
(Hachi [NOZ26] Eq. (16); the analogue of Greyhound's [NS24, §3.1] carrier commitment): `D`
commits to the block-major carrier decomposition `ŵ ∈ Rq^{blocks·messageDigits}`. -/
structure PublicParamsD (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits dRows : Nat) extends
    InnerOuter.PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits where
  /-- The Hachi short-commitment matrix `D` (Hachi [NOZ26] Eq. (16)). -/
  dMatrix : Simple.PublicParams Φ dRows (blocks * messageDigits)

/-! ## The carrier `w`, its decomposition `ŵ`, and the short commitment `v = D ŵ`

The honest-prover side of Figure 3 round 0; the completeness layer instantiates
`QuadEval.prover` from these definitions. -/

section Carrier
variable {messageRows messageDigits blocks : Nat} (base : R)

/-- The carrier entry `wᵢ := aᵀ · G_{2^m} · sᵢ` (Hachi Eq. (16)/(17)). -/
def carrierEntry (a : PolyVec (Rq Φ) messageRows)
    (s : PolyVec (Rq Φ) (messageRows * messageDigits)) : Rq Φ :=
  ArkLib.Lattices.splitForm (gadgetMatrix Φ base messageRows messageDigits) a s

/-- The carrier `w := (w₁, …, w_{2ʳ})`, `wᵢ = aᵀ G_{2^m} sᵢ` (Hachi [NOZ26] Eq. (16)). -/
def carrier (a : PolyVec (Rq Φ) messageRows)
    (s : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks) : PolyVec (Rq Φ) blocks :=
  fun i => carrierEntry Φ base a (s i)

variable [DecidableEq R]   -- introduced after the pure defs (else `unusedSectionVars`)

/-- The carrier decomposition `ŵ := G⁻¹_{blocks}(w)` (Hachi [NOZ26] Eq. (16)/(17)), block-major,
length `blocks * messageDigits`. `base` is IMPLICIT (pinned by `ddCarrier`). -/
def carrierDecomp {base : R} (ddCarrier : DigitDecomposition base messageDigits)
    (a : PolyVec (Rq Φ) messageRows)
    (s : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks) :
    PolyVec (Rq Φ) (blocks * messageDigits) :=
  gadgetDecompose Φ ddCarrier (carrier Φ base a s)

/-- Roundtrip `w = G_{blocks} *ᵥ ŵ` (Hachi Eq. (17)). -/
theorem carrier_eq_gadget {base : R} (hd : 0 < messageDigits) (h1 : 1 ≤ Φ.φ.natDegree)
    (ddCarrier : DigitDecomposition base messageDigits) (a : PolyVec (Rq Φ) messageRows)
    (s : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks) :
    carrier Φ base a s
      = gadgetMatrix Φ base blocks messageDigits *ᵥ carrierDecomp Φ ddCarrier a s := by
  rw [carrierDecomp]; exact (gadgetDecompose_lawful Φ hd h1 ddCarrier (carrier Φ base a s)).symm

/-- The honest short carrier commitment `v := D ŵ` (Hachi Eq. (16), Figure 3 round 0). -/
def carrierCommit {dRows : Nat} (D : Simple.PublicParams Φ dRows (blocks * messageDigits))
    {base : R} (ddCarrier : DigitDecomposition base messageDigits)
    (a : PolyVec (Rq Φ) messageRows)
    (s : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks) :
    Simple.Commitment Φ dRows :=
  Simple.commit Φ D (carrierDecomp Φ ddCarrier a s)

end Carrier

/-! ## The `J` gadget and the response decomposition `ẑ` -/

section JGadget

/-- The `J` gadget `J_n := I_n ⊗ [1, base, …, base^(zDigits-1)]` (Hachi Eq. (18)–(20)); in this
reduction `n = messageRows * messageDigits` and `zDigits = τ`. The verifier reconstructs
`z = J *ᵥ ẑ` from the decomposed response `ẑ`. -/
def jMatrix (base : R) (n zDigits : Nat) : PolyMatrix (Rq Φ) n (n * zDigits) :=
  gadgetMatrix Φ base n zDigits

variable [DecidableEq R]

/-- The response decomposition `ẑ := J⁻¹(z)` (Hachi Eq. (20), the `ẑ` the prover commits to
implicitly), block-major, length `n * zDigits`. `base` is IMPLICIT (pinned by `ddZ`). -/
def zDecomp {n zDigits : Nat} {base : R} (ddZ : DigitDecomposition base zDigits)
    (z : PolyVec (Rq Φ) n) : PolyVec (Rq Φ) (n * zDigits) :=
  gadgetDecompose Φ ddZ z

/-- Roundtrip `z = J *ᵥ ẑ` (the verifier's reconstruction of `z` from `ẑ`, Eq. (20)). -/
theorem z_eq_jMatrix {n zDigits : Nat} {base : R} (hd : 0 < zDigits)
    (h1 : 1 ≤ Φ.φ.natDegree) (ddZ : DigitDecomposition base zDigits) (z : PolyVec (Rq Φ) n) :
    z = jMatrix Φ base n zDigits *ᵥ zDecomp Φ ddZ z := by
  rw [zDecomp, jMatrix]; exact (gadgetDecompose_lawful Φ hd h1 ddZ z).symm

end JGadget

/-! ### The bounded `J⁻¹` — the short-`z` decomposition Hachi's `τ` is sized for

Hachi's `ẑ = J⁻¹(z)` is the one gadget step whose digit count `τ` the paper does **not** take to be
`⌈log_b q⌉`: `z = Σᵢ cᵢ sᵢ` is deterministically short in an honest run ([NOZ26] §4.4), and `τ` is
chosen from that bound. Correspondingly `zDecompBounded` decomposes with a
`BoundedDigitDecomposition` (`Gadget/Core.lean`), whose round-trip below is conditional on the
`ℓ∞` shortness of `z` — the whole content of the separation between `τ` and `δ`. -/

section BoundedJGadget

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- The **bounded** response decomposition `ẑ := J⁻¹(z)` (Hachi Eq. (20)), over a
`BoundedDigitDecomposition`. Executable and total: the digit map is total, and only the round-trip
identity is conditional. -/
def zDecompBounded {n zDigits zBound : Nat} {base : ZMod q}
    (bddZ : BoundedDigitDecomposition base zDigits zBound) (z : PolyVec (Rq Φ) n) :
    PolyVec (Rq Φ) (n * zDigits) :=
  bddZ.gadgetDecompose Φ z

omit [NeZero q] in
/-- `zDecompBounded` at the compatibility wrapper `DigitDecomposition.toBounded` is the ordinary
full-width `zDecomp` — the `τ := δ` path, unchanged. -/
@[simp] theorem zDecompBounded_toBounded {n zDigits : Nat} {base : ZMod q}
    (ddZ : DigitDecomposition base zDigits) (zBound : ℕ) (z : PolyVec (Rq Φ) n) :
    zDecompBounded Φ (ddZ.toBounded zBound) z = zDecomp Φ ddZ z := rfl

omit [NeZero q] in
/-- **Conditional roundtrip `z = J *ᵥ ẑ` for the bounded decomposition**: the verifier's Eq. (20)
reconstruction of `z` from `ẑ`, valid exactly when `z` is within the decomposition's bound. At the
`ℓ = 30` parameters with ArkLib's conservative `τ = 5` (`Params.lean`) this is what makes that
digit count correct while `q ≤ 16⁵` is false. -/
theorem z_eq_jMatrix_bounded {n zDigits zBound : Nat} {base : ZMod q} (hd : 0 < zDigits)
    (h1 : 1 ≤ Φ.φ.natDegree) (bddZ : BoundedDigitDecomposition base zDigits zBound)
    (z : PolyVec (Rq Φ) n) (hz : vecLInftyNorm Φ z ≤ zBound) :
    z = jMatrix Φ base n zDigits *ᵥ zDecompBounded Φ bddZ z := by
  rw [zDecompBounded, jMatrix]
  exact (boundedGadgetDecompose_gadgetMul_eq_of_vecLInftyNorm_le Φ hd h1 bddZ z hz).symm

end BoundedJGadget

/-! ## The block-weighted gadget sums `tensorG` (c5) and `tensorG1` (c4) -/

section TensorG
variable {k digits blocks : Nat}

/-- `tensorG_k c x := Σᵢ cᵢ •ᵥ (G_k *ᵥ xᵢ) : PolyVec (Rq Φ) k` — the Lean rendering of
`(cᵀ ⊗ G_{k}) x̂` on a block family `x` (Eq. (19)/(20) row 5, with `k = n_A`). -/
def tensorG (base : R) (k digits : Nat) (c : PolyVec (Rq Φ) blocks)
    (x : PolyVec (PolyVec (Rq Φ) (k * digits)) blocks) : PolyVec (Rq Φ) k :=
  ∑ i : Fin blocks, (c i) •ᵥ (gadgetMatrix Φ base k digits *ᵥ x i)

/-- `tensorG` is subtractive in the challenge vector (Hachi Lemma 8's two-transcript subtraction
of Eq. (20) row 5). -/
theorem tensorG_sub_challenge (base : R) (k digits : Nat) (c c' : PolyVec (Rq Φ) blocks)
    (x : PolyVec (PolyVec (Rq Φ) (k * digits)) blocks) :
    tensorG Φ base k digits (c - c') x
      = tensorG Φ base k digits c x - tensorG Φ base k digits c' x := by
  simp only [tensorG, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext r
  simp only [Pi.sub_apply, scalarVecMul_apply, sub_mul]

/-- Coordinate isolation (Hachi Lemma 8, case (C), the c5 subtract-and-divide crux): if
`c ≡ⱼ c'`, the challenge-difference sum collapses to the `j`-th block,
`tensorG (c − c') x = (cⱼ − c'ⱼ) •ᵥ (G_k *ᵥ xⱼ)`. -/
theorem tensorG_coord_diff (base : R) (k digits : Nat)
    {c c' : PolyVec (Rq Φ) blocks} {j : Fin blocks} (h : CoordinateWise.CoordEq j c c')
    (x : PolyVec (PolyVec (Rq Φ) (k * digits)) blocks) :
    tensorG Φ base k digits (c - c') x = (c j - c' j) •ᵥ (gadgetMatrix Φ base k digits *ᵥ x j) := by
  simp only [tensorG]; rw [Finset.sum_eq_single j]
  · funext r; simp only [scalarVecMul_apply, Pi.sub_apply]
  · intro i _ hij
    have hzero : (c - c') i = 0 := by simp only [Pi.sub_apply]; rw [h.2 i hij, sub_self]
    funext r; simp only [scalarVecMul_apply, hzero, Pi.zero_apply, zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

end TensorG

section TensorG1
variable {blocks : Nat}

/-- The scalar `(cᵀ ⊗ G₁) x` of Eq. (18)/(20) row 4, on the block-major FLAT carrier
decomposition `x = ŵ ∈ Rq^{blocks·digits}`: since `cᵀ ⊗ G₁ = cᵀ · (I_blocks ⊗ G₁)`, this is
`⟨c, G_blocks *ᵥ x⟩` — the challenge-weighted sum of the recomposed carrier `w = G_blocks ŵ`. -/
def tensorG1 (base : R) (digits : Nat) (c : PolyVec (Rq Φ) blocks)
    (x : PolyVec (Rq Φ) (blocks * digits)) : Rq Φ :=
  dot c (gadgetMatrix Φ base blocks digits *ᵥ x)

/-- `tensorG1` is subtractive in the challenge vector (Hachi Lemma 8's two-transcript subtraction
of Eq. (20) row 4). -/
theorem tensorG1_sub_challenge (base : R) (digits : Nat) (c c' : PolyVec (Rq Φ) blocks)
    (x : PolyVec (Rq Φ) (blocks * digits)) :
    tensorG1 Φ base digits (c - c') x
      = tensorG1 Φ base digits c x - tensorG1 Φ base digits c' x := by
  simp only [tensorG1, dot_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Coordinate isolation at `k = 1` (Hachi Lemma 8, case (C), the c4 subtract-and-divide crux):
if `c ≡ⱼ c'`, then `tensorG1 (c − c') ŵ = (cⱼ − c'ⱼ) · wⱼ` where `w := G_blocks *ᵥ ŵ` is the
recomposed carrier. -/
theorem tensorG1_coord_diff (base : R) (digits : Nat)
    {c c' : PolyVec (Rq Φ) blocks} {j : Fin blocks} (h : CoordinateWise.CoordEq j c c')
    (x : PolyVec (Rq Φ) (blocks * digits)) :
    tensorG1 Φ base digits (c - c') x
      = (c j - c' j) * (gadgetMatrix Φ base blocks digits *ᵥ x) j := by
  simp only [tensorG1, dot_eq_sum]; rw [Finset.sum_eq_single j]
  · simp only [Pi.sub_apply]
  · intro i _ hij
    have hzero : (c - c') i = 0 := by simp only [Pi.sub_apply]; rw [h.2 i hij, sub_self]
    rw [hzero, zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

end TensorG1

end ArkLib.Lattices.Hachi
