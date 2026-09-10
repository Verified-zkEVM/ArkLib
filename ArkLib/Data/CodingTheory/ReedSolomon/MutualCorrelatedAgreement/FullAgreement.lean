/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
/-!
# Exact agreement sets from mutual correlated agreement

Outside the canonical MCA bad event, every sufficiently close Reed–Solomon polynomial
is the specified linear combination of constituent polynomials. Their common agreement
set equals the full agreement set of that polynomial. This is the bridge from the subset
projection API to the exact-set conclusion for affine families in [DKTZ26].

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators

variable {F ι ℓ S : Type} [Field F] [Fintype ι] [Fintype ℓ]
  [Fintype S] [Nonempty S]

omit [Fintype ι] in
/-- Projecting a Reed–Solomon codeword is precisely interpolation on the chosen positions. -/
theorem projectedWord_mem_code_iff_exists_polynomial
    (domain : ι ↪ F) (k : ℕ) (w : ι → F) (T : Finset ι) :
    projectedWord w T ∈ projectedCodeSubmod (code domain k) T ↔
      ∃ p : F[X], p.degree < k ∧ ∀ i ∈ T, p.eval (domain i) = w i := by
  rw [mem_projectedCodeSubmod_iff]
  constructor
  · rintro ⟨c, hc, hrestrict⟩
    obtain ⟨p, hp, heval⟩ := mem_code_iff_eval.mp hc
    refine ⟨p, hp, fun i hi ↦ ?_⟩
    have h := congrFun hrestrict ⟨i, hi⟩
    exact (heval i).trans h.symm
  · rintro ⟨p, hp, heval⟩
    refine ⟨evalOnPoints domain p, evalOnPoints_mem_code_of_degree_lt hp, ?_⟩
    funext i
    exact (heval i i.property).symm

open Classical in
/-- Absence of the MCA bad event supplies constituent polynomials and equality of full
agreement sets. The threshold is large enough for polynomial uniqueness; witnesses may
have extra individual agreements, while their common set is exactly the original set. -/
theorem exists_polynomials_full_agreement_of_not_isMCA
    (domain : ι ↪ F) (k : ℕ) (G : Generator S ℓ F) (x : S)
    (U : ℓ → ι → F) (δ : ℝ) (hk : (k : ℝ) ≤ Fintype.card ι * (1 - δ))
    (hgood : ¬ IsMCA G (code domain k) x U δ)
    (p : F[X]) (hp : p.degree < k)
    (hclose : ((Finset.univ.filter fun i ↦
      p.eval (domain i) = ∑ j, G x j * U j i).card : ℝ) ≥
        Fintype.card ι * (1 - δ)) :
    ∃ P : ℓ → F[X], (∀ j, (P j).degree < k) ∧ p = ∑ j, G x j • P j ∧
      ∀ i, (p.eval (domain i) = ∑ j, G x j * U j i) ↔
        ∀ j, (P j).eval (domain i) = U j i := by
  classical
  let T := Finset.univ.filter fun i ↦ p.eval (domain i) = ∑ j, G x j * U j i
  have hmem : projectedWord (fun i ↦ ∑ j, G x j • U j i) T ∈
      projectedCodeSubmod (code domain k) T := by
    apply (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mpr
    refine ⟨p, hp, fun i hi ↦ ?_⟩
    simpa only [smul_eq_mul] using (Finset.mem_filter.mp hi).2
  have hall : ∀ j, projectedWord (U j) T ∈ projectedCodeSubmod (code domain k) T := by
    intro j
    by_contra hj
    exact hgood ⟨T, hclose, hmem, j, hj⟩
  choose P hP hPeval using fun j ↦
    (projectedWord_mem_code_iff_exists_polynomial domain k (U j) T).mp (hall j)
  have hkT : k ≤ T.card := by exact_mod_cast hk.trans hclose
  have hsum : (∑ j, G x j • P j).degree < k := by
    apply mem_degreeLT.mp
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (mem_degreeLT.mpr (hP j))
  have heq : p = ∑ j, G x j • P j := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T) domain.injective.injOn
      (hp.trans_le (by exact_mod_cast hkT)) (hsum.trans_le (by exact_mod_cast hkT))
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (G x j * ·) (hPeval j i hi).symm
  refine ⟨P, hP, heq, fun i ↦ ⟨fun hi j ↦ hPeval j i ?_, fun hi ↦ ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  · rw [heq]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, hi]

end ReedSolomon
