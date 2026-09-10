/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.ToMathlib.Polynomial.SparseContraction
/-!
# Recognizing a sparse Frobenius-pulled polynomial from a sample

A sample of the original dimension suffices after sparse Taylor reconstruction. The
base-field pair is fixed before the extension, prime power, challenge, and candidate.
This point-level result does not assert that a rational chart supplies the sparse cutoffs.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

/-- Recognition uses `k` original positions, even though the pulled polynomial can have degree
up to `p^e*k-1`. Its root value lies on the graph parametrized by the original challenge `w^p^e`.
-/
theorem exists_frobeniusGraphLine_polynomials_of_sample
    {F : Type*} [Field F] {n k : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (sample : Finset (Fin n)) (hsample : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < ↑k ∧ G₀.degree < ↑k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (p e : ℕ) [ExpChar E p]
        (roots : Fin n → E) (center w : E) (P : E[X]),
        (∀ i, roots i ^ (p ^ e) = ι (domain i)) →
        P.degree < ↑(p ^ e * k) →
        (∀ j : ℕ, ¬ p ^ e ∣ j → (taylor center P).coeff j = 0) →
        (∀ i ∈ sample, P.eval (roots i) = ι (f i) + w ^ (p ^ e) * ι (g i)) →
        P = expand E (p ^ e) (F₀.map ι + C (w ^ (p ^ e)) * G₀.map ι) ∧
          P.eval center = (F₀.map ι).eval (center ^ (p ^ e)) +
            w ^ (p ^ e) * (G₀.map ι).eval (center ^ (p ^ e)) := by
  obtain ⟨F₀, G₀, hF, hG, hsampleFG, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨F₀, G₀, hF, hG, hsampleFG, ?_⟩
  intro E _ ι p e _ roots center w P hroots hdegree hsparse hagree
  obtain ⟨Q, ⟨hQdegree, hQP⟩, _⟩ :=
    existsUnique_expand_of_sparse_taylor p e k P center hsparse hdegree
  have hQagree : ∀ i ∈ sample,
      Q.eval (mappedDomain domain ι i) = ι (f i) + w ^ (p ^ e) * ι (g i) := by
    intro i hi
    have h := hagree i hi
    rw [← hQP, expand_eval, hroots] at h
    exact h
  have hQ := hrecognize ι (w ^ (p ^ e)) Q hQdegree hQagree
  have hP : P = expand E (p ^ e) (F₀.map ι + C (w ^ (p ^ e)) * G₀.map ι) := by
    rw [← hQP, hQ]
  refine ⟨hP, ?_⟩
  rw [hP, expand_eval, eval_add, eval_mul, eval_C]

/-- A retained sample of size `k` leaves at most `n-k` accidental challenges. The conclusion
preserves the complete agreement set in the original challenge coordinate. -/
theorem exists_exceptional_graphLine_challenges_of_sample
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n k : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k) (F₀ G₀ : F[X])
    (hfg : ∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)
    (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ n - k ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (mappedDomain domain ι)
            (fun i ↦ ι (f i) + z * ι (g i)) (F₀.map ι + C z * G₀.map ι) =
          commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_graphLine_challenges domain f g F₀ G₀ ι
  have hsubset : sample ⊆ commonPolynomialAgreementSet domain f g F₀ G₀ := by
    intro i hi
    simpa only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfg i hi
  have hk : k ≤ (commonPolynomialAgreementSet domain f g F₀ G₀).card := by
    rw [← hsample]
    exact Finset.card_le_card hsubset
  exact ⟨exceptional, hcard.trans (Nat.sub_le_sub_left hk n), hagree⟩

end ReedSolomon
