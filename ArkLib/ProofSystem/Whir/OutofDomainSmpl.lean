/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.Probability.Notation

namespace OutOfDomSmpl

open ListDecodable MvPolynomial NNReal ProbabilityTheory ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lemma 4.24
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter, then for every `r₁,...,rₛ ∈ Fᵐ`
  the following statements are equivalent:
    - ∃ distinct u, u' ∈ Λ(C,f,δ) such that ∀ i < s, uPoly(rᵢ) = uPoly'(rᵢ)
      where, Λ(C,f,δ) denotes the list of codewords of C δ-close to f
             uPoly, uPoly' denotes the decoded multivariate polynomials of u and u'
    - ∃ σ₁,..,σₛ : F, such that |Λ(C',f,δ)| > 1
      where, C' is a multiconstrained RS = MCRS[F, ι, φ, m, s, w, σ]
             σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(rᵢ) -/
lemma crs_equiv_rs_random_point_agreement
  {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ] :
  ∀ (r : Fin s → Fin m → F) (δ : ℝ≥0) (hδLe : δ ≤ 1),
    (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ relHammingBall (smoothCode φ m) f δ ∧
      u'.val ∈ relHammingBall (smoothCode φ m) f δ ∧
      ∀ i : Fin s, (mVdecode u).eval (r i) = (mVdecode u').eval (r i))
    ↔
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i => MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial (r i))
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ relHammingBall multiCRSCode f δ ∧
        u' ∈ relHammingBall multiCRSCode f δ)
  := by sorry

/-- Lemma 4.25 part 1
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  `Pr_{r ← F} [ ∃ σ₁,..,σₛ : F, |Λ(C',f,δ)| > 1 ] =`
  `Pr_{r ← F} [ ∃ distinct u, u' ∈ RS[F, ι, φ, m] s.t. uPoly(pow(r)) = uPoly'(pow(r))]`
    where, pow(x,m) = {x^2⁰,x^2¹,....,x^2^{m-1}}
           C' = CRS [F, ι, φ, m, s, w, σ]
           σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(pow(r,m)) -/
lemma oodSampling_crs_eq_rs
    {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (l δ : ℝ≥0) (hδLe : δ ≤ 1)
    {C : Set (ι → F)} (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ σ : Fin s → F,
                        let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
                          fun i =>
                            let ri := rs i
                            let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                            MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial rVec)
                        let multiCRSCode := multiConstrainedCode φ m s w σ
                        ∃ u u' : ι → F, u ≠ u' ∧
                          u ∈ relHammingBall multiCRSCode f δ ∧
                          u' ∈ relHammingBall multiCRSCode f δ)]
    =
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ relHammingBall C f δ ∧
                        u'.val ∈ relHammingBall C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec))]
  := by sorry

/-- Lemma 4.25 part 2
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  the above equation is bounded as `≤ l²/2 * (2ᵐ/|F|)ˢ` -/
lemma oodSampling_rs_le_bound
    {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (δ l : ℝ≥0) (hδLe : δ ≤ 1)
    (C : Set (ι → F)) (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ ∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ relHammingBall C f δ ∧
                        u'.val ∈ relHammingBall C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec)
                      ] ≤ ENNReal.ofReal (((l : ℝ)^2 / 2) * (((2^m : ℝ) / Fintype.card F)^s))
:= by sorry

end OutOfDomSmpl
