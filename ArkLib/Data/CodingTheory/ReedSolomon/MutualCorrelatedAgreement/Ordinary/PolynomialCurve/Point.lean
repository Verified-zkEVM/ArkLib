/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExceptionalSet
public import ArkLib.ToMathlib.Polynomial.SparseContraction
/-!
# Point recognition for Frobenius-pulled polynomial curves

Sparse Taylor reconstruction contracts a polynomial whose exponents are divisible by `p ^ e`
back to the original message degree.  A common sample then recognizes all constituents of a
power-batched received curve at once.  This is the arbitrary-curve analogue of the ordinary
line point-recognition lemma and uses no bound on the characteristic relative to the curve
degree.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial
open scoped BigOperators

/-- Recognition uses `k` original positions even though the Frobenius-pulled polynomial may have
degree as large as `p ^ e * k - 1`.  The contracted polynomial is the power combination of one
base-field tuple, with challenge `z ^ (p ^ e)`. -/
theorem exists_frobeniusPowerGraph_polynomials_of_sample
    {F : Type*} [Field F] {n k ℓ : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (p e : ℕ) [ExpChar E p]
        (roots : Fin n → E) (center z : E) (Q : E[X]),
        (∀ i, roots i ^ (p ^ e) = ι (domain i)) →
        Q.degree < p ^ e * k →
        (∀ j : ℕ, ¬p ^ e ∣ j → (taylor center Q).coeff j = 0) →
        (∀ i ∈ sample,
          Q.eval (roots i) = ∑ t, z ^ (p ^ e * t.val) * ι (values t i)) →
        Q = expand E (p ^ e)
            (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) ∧
          Q.eval center =
            (powerBatchedPolynomial (fun t ↦ (P t).map ι)
              (z ^ (p ^ e))).eval (center ^ (p ^ e)) := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain values k sample hsample
  refine ⟨P, hPdegree, hPsample, ?_⟩
  intro E _ ι p e _ roots center z Q hroots hdegree hsparse hagree
  obtain ⟨R, ⟨hRdegree, hRQ⟩, _⟩ :=
    existsUnique_expand_of_sparse_taylor p e k Q center hsparse hdegree
  have hRagree : ∀ i ∈ sample,
      R.eval (mappedDomain domain ι i) =
        ∑ t, (z ^ (p ^ e)) ^ t.val * ι (values t i) := by
    intro i hi
    have hiAgree := hagree i hi
    rw [← hRQ, expand_eval, hroots] at hiAgree
    simpa only [mappedDomain, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk, pow_mul] using hiAgree
  have hRidentity := hrecognize ι (z ^ (p ^ e)) R hRdegree hRagree
  constructor
  · rw [← hRQ, hRidentity]
  · rw [← hRQ, expand_eval, hRidentity]

open Classical in
/-- A retained sample supplies the common agreements needed by the exact accidental-challenge
bound.  The resulting exceptional budget is exactly `ℓ * (n - k)`. -/
theorem exists_exceptional_frobeniusPower_challenges_of_sample
    {F E : Type*} [Field F] [Field E] [DecidableEq E]
    {n k ℓ : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (P : Fin (ℓ + 1) → F[X])
    (hdegree : ∀ t, (P t).degree < k)
    (hsampleP : ∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i)
    (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (n - k) ∧
      ∀ z ∉ exceptional,
        HasExactPowerAgreement domain values ι k z
          (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) := by
  have hcommon : k ≤ (commonCurveAgreementSet domain values P).card := by
    rw [← hsample]
    apply Finset.card_le_card
    intro i hi
    simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsampleP i hi
  exact exists_exceptional_exactPowerAgreement domain values P ι hdegree hcommon

end ReedSolomon
