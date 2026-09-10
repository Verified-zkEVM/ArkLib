/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.Errors
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound
public import Mathlib.FieldTheory.RatFunc.Basic
/-!
# Agreement bounds for interleaved Reed--Solomon codes

This file transports two scalar Reed--Solomon conclusions to the actual row-wise interleaved
code.  For mutual correlated agreement, affine-line MCA is invariant under every nonempty
interleaving at radii strictly between zero and one.  Thus a scalar exact-line certificate gives
the same MCA probability bound for the interleaved code.

For list size, an interleaved symbol `(a₀, ..., aₜ₋₁)` is packed injectively as the
rational function represented by

```text
a₀ + a₁ Z + ... + aₜ₋₁ Z^(t-1).
```

Packing every row polynomial in the same way produces one polynomial over `RatFunc F` of the
same degree, and injectivity makes its scalar agreement set exactly the interleaved agreement set.
Consequently any scalar finite-list theorem that is uniform over fields applies over `RatFunc F`
and gives the *same* list bound, independent of the interleaving width.  These are coding-theoretic
statements: they quantify over every received interleaved word and make no transcript or
whole-protocol claim.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial Code CoreDefinitions LinearCode ListDecoding

/-! ## Rational-function packing -/

/-- The polynomial whose first `t` coefficients are the entries of a tuple. -/
def tuplePolynomial {F : Type*} [Semiring F] {t : ℕ} (v : Fin t → F) : F[X] :=
  ∑ j, Polynomial.monomial j.val (v j)

/-- Inject a finite tuple over `F` into the rational-function field `F(Z)`. -/
def tupleRatFunc {F : Type*} [Field F] {t : ℕ} (v : Fin t → F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (tuplePolynomial v)

/-- Coefficient packing into `F(Z)` is injective for every finite width. -/
theorem tupleRatFunc_injective {F : Type*} [Field F] {t : ℕ} :
    Function.Injective (tupleRatFunc (F := F) (t := t)) := by
  intro u v huv
  apply _root_.funext
  intro j
  have hpoly : tuplePolynomial u = tuplePolynomial v :=
    RatFunc.algebraMap_injective F huv
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff j.val) hpoly
  simpa [tuplePolynomial, Polynomial.coeff_monomial, ← Fin.ext_iff] using hcoeff

/-- Passing to the rational-function field preserves the characteristic. -/
theorem ringChar_ratFunc {F : Type*} [Field F] : ringChar (RatFunc F) = ringChar F := by
  exact ringChar.eq _ (ringChar F)

/-- Pack a tuple of scalar row polynomials into one polynomial over `F(Z)`. -/
def packRowPolynomials {F : Type*} [Field F] {t : ℕ} (P : Fin t → F[X]) :
    (RatFunc F)[X] :=
  ∑ j, algebraMap F[X] (RatFunc F) (Polynomial.X ^ j.val) •
    (P j).map (algebraMap F (RatFunc F))

/-- Packed row-polynomial evaluation is coefficient packing of the row evaluations. -/
theorem packRowPolynomials_eval {F : Type*} [Field F] {t : ℕ}
    (P : Fin t → F[X]) (x : F) :
    (packRowPolynomials P).eval (algebraMap F (RatFunc F) x) =
      tupleRatFunc (fun j ↦ (P j).eval x) := by
  simp only [packRowPolynomials, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul, Polynomial.eval_map, Polynomial.eval₂_at_apply, tupleRatFunc,
    tuplePolynomial, map_sum, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1

/-- Packing row polynomials does not increase their common degree bound. -/
theorem packRowPolynomials_degree_lt {F : Type*} [Field F] {t k : ℕ}
    (P : Fin t → F[X]) (hP : ∀ j, (P j).degree < k) :
    (packRowPolynomials P).degree < k := by
  apply Polynomial.mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Polynomial.mem_degreeLT.mpr (Polynomial.degree_map_le.trans_lt (hP j))

/-- A scalar exact-line certificate gives the same affine-line MCA bound for every nonempty
row-wise interleaving. -/
theorem mcaError_interleaved_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k A t : ℕ} (domain : Fin n ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B)
    (radius : NNReal) (ht : 0 < t) (hradiusPos : 0 < radius) (hradiusLt : radius < 1)
    (hthreshold : A ≤ ⌈(n : ℝ) * (1 - (radius : ℝ))⌉₊) :
    mcaError (AffineLineGenerator F)
        ((ReedSolomon.code domain k) ^⋈ (Fin t)) (radius : ℝ) ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ)) := by
  rw [ProximityGap.mcaError_interleaved_eq
    (ReedSolomon.code domain k) t radius ht hradiusPos hradiusLt]
  exact mcaError_affineLine_le_of_exactAgreement domain B hline radius hthreshold

open Classical in
/-- A uniform finite-family polynomial agreement bound gives the scalar Reed--Solomon `Lambda`
bound at the corresponding capacity-gap radius.  Finiteness of the complete polynomial list is
derived from `k ≤ agreementThreshold`; callers only supply the cardinality theorem. -/
theorem lambda_rs_le_of_finite_polynomial_agreement_bound
    {F : Type*} [Field F]
    {n k L : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta) (hn : 0 < n)
    (domain : Fin n ↪ F)
    (hbound : ∀ (received : Fin n → F) (S : Finset F[X]),
      (∀ P ∈ S, P.degree < k ∧
        agreementThreshold delta n k ≤ (polynomialAgreementSet domain received P).card) →
      S.card ≤ L) :
    Lambda (ReedSolomon.code domain k : Set (Fin n → F))
        (capacityRadius delta n k) ≤ (L : ℕ∞) := by
  apply lambda_le_of_forall_agreeingPolynomials_encard_le hdelta hn domain
  intro received
  apply (agreeingPolynomials_encard_le_closePolynomialSet
    (k := k) (A := agreementThreshold delta n k) domain received).trans
  have hfinite :
      (closePolynomialSet domain received k (agreementThreshold delta n k)).Finite :=
    closePolynomialSet_finite domain received (by simp [agreementThreshold])
  rw [← hfinite.cast_ncard_eq]
  have hcard := hbound received hfinite.toFinset (by
    intro P hP
    exact hfinite.mem_toFinset.mp hP)
  have hncard :
      (closePolynomialSet domain received k (agreementThreshold delta n k)).ncard ≤ L :=
    (Set.ncard_eq_toFinset_card _ hfinite) ▸ hcard
  exact_mod_cast hncard

open Classical in
/-- A scalar finite-family theorem over `F(Z)` bounds the actual row-wise interleaved
Reed--Solomon code by the *same* list size.  The received word and the finite candidate family are
universally quantified by `hbound`; no list bound for the interleaved code is assumed.

The proof packs tuple symbols and their row polynomials into `RatFunc F`.  Packing is injective,
preserves degree, and preserves the complete agreement set, so it injects every finite subset of
an interleaved point list into a scalar polynomial agreement list. -/
theorem lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
    {F : Type*} [Field F]
    {n k L t : ℕ} (delta : ℝ) (hdelta : 0 ≤ delta) (hn : 0 < n)
    (domain : Fin n ↪ F)
    (hbound : ∀ (received : Fin n → RatFunc F) (S : Finset (RatFunc F)[X]),
      (∀ P ∈ S, P.degree < k ∧
        agreementThreshold delta n k ≤
          (polynomialAgreementSet
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩) received P).card) →
      S.card ≤ L) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin t)
          (ReedSolomon.code domain k : Set (Fin n → F)))
        (capacityRadius delta n k) ≤ (L : ℕ∞) := by
  apply Code.Lambda_le_of_forall_finset_card_le
  intro received T hT
  let ratDomain : Fin n ↪ RatFunc F :=
    domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩
  have hcode (c : ↑T) :
      c.1 ∈ Code.interleavedCodeSet (κ := Fin t)
        (ReedSolomon.code domain k : Set (Fin n → F)) :=
    (Code.mem_closeCodewordsRel_iff.mp (hT c.1 c.2)).1
  let rowPolynomial (c : ↑T) (j : Fin t) : F[X] :=
    Classical.choose (ReedSolomon.mem_code_iff_eval.mp (hcode c j))
  have hrowDegree (c : ↑T) (j : Fin t) : (rowPolynomial c j).degree < k :=
    (Classical.choose_spec (ReedSolomon.mem_code_iff_eval.mp (hcode c j))).1
  have hrowEval (c : ↑T) (j : Fin t) (i : Fin n) :
      (rowPolynomial c j).eval (domain i) = c.1 i j :=
    (Classical.choose_spec (ReedSolomon.mem_code_iff_eval.mp (hcode c j))).2 i
  let packedPolynomial (c : ↑T) : (RatFunc F)[X] :=
    packRowPolynomials (fun j ↦ rowPolynomial c j)
  have hpackedDegree (c : ↑T) : (packedPolynomial c).degree < k :=
    packRowPolynomials_degree_lt _ (hrowDegree c)
  have hpackedEval (c : ↑T) (i : Fin n) :
      (packedPolynomial c).eval (ratDomain i) = tupleRatFunc (c.1 i) := by
    change (packRowPolynomials (fun j ↦ rowPolynomial c j)).eval
      (algebraMap F (RatFunc F) (domain i)) = tupleRatFunc (c.1 i)
    rw [packRowPolynomials_eval]
    congr 1
    funext j
    exact hrowEval c j i
  have hpackedInjective : Function.Injective packedPolynomial := by
    intro c d hcd
    apply SetCoe.ext
    funext i
    apply tupleRatFunc_injective
    rw [← hpackedEval c i, ← hpackedEval d i, hcd]
  let S : Finset (RatFunc F)[X] := T.attach.image packedPolynomial
  have hScard : S.card = T.card := by
    change (T.attach.image packedPolynomial).card = T.card
    rw [Finset.card_image_of_injective _ hpackedInjective, Finset.card_attach]
  have hSbound : S.card ≤ L := hbound (fun i ↦ tupleRatFunc (received i)) S (by
    intro P hP
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨hpackedDegree c, ?_⟩
    have hclose := (Code.mem_closeCodewordsRel_iff.mp (hT c.1 c.2)).2
    have hpackedClose :
        (Code.relHammingDist (fun i ↦ tupleRatFunc (received i))
          (ReedSolomon.evalOnPoints ratDomain (packedPolynomial c)) : ℝ) ≤
            capacityRadius delta n k := by
      have hcomp := Code.relHammingDist_comp
        (tupleRatFunc_injective (F := F) (t := t)) received c.1
      rw [← hcomp] at hclose
      rw [show ReedSolomon.evalOnPoints ratDomain (packedPolynomial c) =
        fun i ↦ tupleRatFunc (c.1 i) by
          funext i
          exact hpackedEval c i]
      change (Code.relHammingDist (tupleRatFunc ∘ received)
        (tupleRatFunc ∘ c.1) : ℝ) ≤ capacityRadius delta n k
      exact hclose
    have hagree :=
      (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
        hdelta hn (ReedSolomon.evalOnPoints ratDomain (packedPolynomial c))
          (fun i ↦ tupleRatFunc (received i))).mp hpackedClose
    change agreementThreshold delta n k ≤
      Code.agree (ReedSolomon.evalOnPoints ratDomain (packedPolynomial c))
        (fun i ↦ tupleRatFunc (received i))
    exact hagree)
  rwa [hScard] at hSbound

end

end ReedSolomon
