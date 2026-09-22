/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.Data.CodingTheory.ProximityGap.Folding
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Agreement preservation in FRI folding

The folding soundness argument of [GMW25], using ArkLib's existing Reed–Solomon codes,
block interpolants, and mutual correlated agreement error. Agreement of the coefficient
words on a set lifts to agreement on its entire preimage under the folding map. Consequently,
failure to lift agreement is contained in the MCA bad event, with no union bound over sets.

We follow the March 27, 2026 revision: the tradeoff parameter is independent of the input
distance, and the size threshold is non-strict. The proof strategy was also informed by
[zkSecurity's Lean formalization](https://github.com/zksecurity/simple-rbr-fri), credited there
to Yoichi Hirai and Harmonic's Aristotle, with subsequent work by Pietro Monticone.
We reuse ArkLib's definitions throughout.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri

open Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions
open OracleComp
open scoped BigOperators ProbabilityTheory NNReal

variable {F : Type} [Field F] [DecidableEq F] {n k d : ℕ}

/-- Agreement of all coefficient words with smaller RS codewords lifts to agreement with a
single original RS codeword on every block above the agreement set. -/
theorem exists_codeword_agree_of_coefficients
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d)
    (T : Finset (Fin (2 ^ (n - k))))
    (h : ∀ j : Fin (2 ^ k),
      projectedWord (fun x ↦ foldWordAuxCoeff domain f k j (domain.subdomain k x)) T ∈
        projectedCodeSubmod (code (domain.subdomain k) d) T) :
    ∃ u ∈ code domain (2 ^ k * d),
      ∀ i x, x ∈ T → domain i ^ (2 ^ k) = domain.subdomain k x → u i = f i := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hpoly : ∀ j : Fin (2 ^ k), ∃ p : F[X], p.natDegree < d ∧
      ∀ x ∈ T, p.eval (domain.subdomain k x) =
        foldWordAuxCoeff domain f k j (domain.subdomain k x) := by
    intro j
    obtain ⟨u, hu, heq⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp (h j)
    obtain ⟨p, hp, rfl⟩ := mem_code_iff_exists_polynomial_of_ne_zero.mp hu
    refine ⟨p, hp, fun x hx ↦ ?_⟩
    exact (congrFun heq ⟨x, hx⟩).symm
  choose p hp hagree using hpoly
  let q : F[X] := ∑ j : Fin (2 ^ k),
    Polynomial.X ^ (j : ℕ) * (p j).comp (Polynomial.X ^ (2 ^ k))
  have hdeg : q.natDegree < 2 ^ k * d := by
    apply Polynomial.Bivariate.natDegree_sum_lt_of_forall_lt (by positivity)
    intro j _
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    simp only [natDegree_pow, natDegree_X, mul_one, natDegree_comp]
    have hj := j.isLt
    have hpj := hp j
    nlinarith
  refine ⟨evalOnPoints domain q, evalOnPoints_mem_code_of_natDegree_lt hdeg, ?_⟩
  intro i x hx hix
  change q.eval (domain i) = f i
  calc
    q.eval (domain i) =
        ∑ j : Fin (2 ^ k), domain i ^ (j : ℕ) *
          foldWordAuxCoeff domain f k j (domain.subdomain k x) := by
      simp [q, eval_finsetSum, hix, hagree _ _ hx]
    _ = foldValue domain f k (domain i) (domain i ^ (2 ^ k)) := by
      rw [foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha, hix]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ = f i := foldValue_pow_x_k

/-- A folding challenge is bad if some large set admits a folded codeword but agreement
cannot be lifted to all the original positions above that set. -/
def FoldingAgreementFailure (domain : SmoothCosetFftDomain n F)
    (f : Fin (2 ^ n) → F) (k d : ℕ) (θ : ℝ) (α : F) : Prop :=
  ∃ T : Finset (Fin (2 ^ (n - k))),
    (Fintype.card (Fin (2 ^ (n - k))) : ℝ) * (1 - θ) ≤ T.card ∧
    projectedWord (foldWord domain f k α) T ∈
      projectedCodeSubmod (code (domain.subdomain k) d) T ∧
    ¬ ∃ u ∈ code domain (2 ^ k * d),
      ∀ i x, x ∈ T → domain i ^ (2 ^ k) = domain.subdomain k x → u i = f i

/-- The folding bad event is contained in the existing MCA event for the coefficient words. -/
theorem isMCA_of_foldingAgreementFailure [Fintype F]
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d)
    (θ : ℝ) (α : F) (h : FoldingAgreementFailure domain f k d θ α) :
    IsMCA (fun α (j : Fin (2 ^ k)) ↦ α ^ (j : ℕ)) (code (domain.subdomain k) d) α
      (fun j x ↦ foldWordAuxCoeff domain f k j (domain.subdomain k x)) θ := by
  classical
  obtain ⟨T, hT, hfold, hbad⟩ := h
  refine ⟨T, hT, ?_, ?_⟩
  · convert hfold using 1
    ext x
    simp only [projectedWord, Set.domRestrict_apply, smul_eq_mul, foldWord,
      foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  · by_contra! h
    exact hbad (exists_codeword_agree_of_coefficients domain f hd T h)

/-- FRI's single-fold soundness error is bounded by ArkLib's MCA error value. The bound is
uniform over all agreement sets and does not depend on the prover's next message. -/
theorem foldingAgreementFailure_prob_le [Fintype F] [SampleableType F]
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d) (θ : ℝ) :
    Pr{let α ←$ᵗ F}[FoldingAgreementFailure domain f k d θ α] ≤
      mcaError (fun α (j : Fin (2 ^ k)) ↦ α ^ (j : ℕ))
        (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ := by
  apply le_trans (prEvent_mono _ _ _
    (isMCA_of_foldingAgreementFailure domain f hd θ))
  exact le_iSup (fun U ↦ Pr{let α ←$ᵗ F}[
    IsMCA (fun α (j : Fin (2 ^ k)) ↦ α ^ (j : ℕ))
      (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) α U θ]) _

/-- The folding bound stated using the existing named powers generator, whose parameter is
the largest exponent (one less than the number of coefficient words). -/
theorem foldingAgreementFailure_prob_le_powers [Fintype F] [SampleableType F]
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d) (θ : ℝ) :
    Pr{let α ←$ᵗ F}[FoldingAgreementFailure domain f k d θ α] ≤
      mcaError (univariatePowersGenerator F (2 ^ k - 1))
        (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ := by
  have h := foldingAgreementFailure_prob_le (k := k) domain f hd θ
  have heq : ∀ m : ℕ, 0 < m →
      mcaError (fun α (j : Fin m) ↦ α ^ (j : ℕ))
          (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ =
        mcaError (univariatePowersGenerator F (m - 1))
          (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d) θ := by
    intro m hm
    cases m with
    | zero => omega
    | succ m => rfl
  rwa [heq _ (by positivity)] at h

/-- Any existing certified MCA bound for powers instantiates the FRI folding error. -/
theorem foldingAgreementFailure_prob_le_of_isMCAGenerator [Fintype F] [SampleableType F]
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d)
    (ε : unitInterval → ℝ≥0)
    (hMCA : IsMCAGenerator (univariatePowersGenerator F (2 ^ k - 1)) ε
      (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d)) (θ : unitInterval) :
    Pr{let α ←$ᵗ F}[FoldingAgreementFailure domain f k d θ α] ≤ (ε θ : ENNReal) :=
  (foldingAgreementFailure_prob_le_powers domain f hd θ).trans (hMCA θ)

end Fri
