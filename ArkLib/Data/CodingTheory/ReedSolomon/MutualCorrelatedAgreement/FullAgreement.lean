/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
/-!
# Polynomial witnesses for full mutual correlated agreement

ArkLib's MCA predicate is expressed through code projections onto sets of coordinates.
Applications to Reed–Solomon codes often need actual polynomials and their full agreement
sets instead. This module proves the bridge without assuming a decoding theorem.

## Main results

* `projectedWord_mem_code_iff_exists_polynomial` identifies a projected codeword with a
  polynomial of degree strictly less than the message length that interpolates the selected
  coordinates. It applies to arbitrary coordinate types and finite selected sets.
* `exists_polynomials_full_agreement_of_not_isMCA` fixes a generator challenge outside the
  MCA bad event. Every sufficiently agreeing polynomial then equals the generator's linear
  combination of constituent polynomials. Their simultaneous agreement set equals the full
  agreement set of the original polynomial.

## The role of the threshold

The agreement count must be at least the message length. This gives uniqueness of a
polynomial of degree strictly less than that length from its values on the agreement set.
The theorem needs no characteristic restriction or a priori bound on the number of bad
challenges. It converts the pointwise complement of the MCA event, not a probability claim.

## Proof organization

First obtain constituent codewords on the selected set from the MCA hypothesis. Convert each
projection witness to a polynomial, identify their linear combination by interpolation,
and then prove both inclusions of the full agreement sets. Individual witnesses may have
extra agreements; only their simultaneous agreement set is asserted to be exact.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators

/-- Projecting a Reed–Solomon codeword is precisely interpolation on the chosen positions. -/
theorem projectedWord_mem_code_iff_exists_polynomial
    {F ι : Type*} [Semiring F]
    (domain : ι ↪ F) (k : ℕ) (w : ι → F) (T : Finset ι) :
    projectedWord w T ∈ projectedCodeSubmod (code domain k) T ↔
      ∃ p : F[X], p.degree < k ∧ ∀ i ∈ T, p.eval (domain i) = w i := by
  -- Unpack a projected codeword before choosing its polynomial explanation.
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

variable {F ι ℓ S : Type} [Field F] [Fintype ι] [Fintype ℓ]
  [Fintype S] [Nonempty S]

noncomputable local instance : DecidableEq F := Classical.decEq _

open Classical in
/-- Absence of the MCA bad event supplies constituent polynomials and equality of full
agreement sets. The threshold is large enough for polynomial uniqueness; witnesses may
have extra individual agreements, while their common set is exactly the original set. -/
theorem exists_polynomials_full_agreement_of_not_isMCA
    (domain : ι ↪ F) (k : ℕ) (G : Generator S ℓ F) (x : S)
    (U : ℓ → ι → F) (δ : ℝ) (hk : (k : ℝ) ≤ Fintype.card ι * (1 - δ))
    (hgood : ¬ IsMCA G (code domain k) x U δ)
    (p : F[X]) (hp : p.degree < k)
    (hclose : Fintype.card ι * (1 - δ) ≤
      ((polynomialAgreementSet domain (fun i ↦ ∑ j, G x j * U j i) p).card : ℝ)) :
    ∃ P : ℓ → F[X], (∀ j, (P j).degree < k) ∧ p = ∑ j, G x j • P j ∧
      ∀ i, i ∈ polynomialAgreementSet domain (fun i ↦ ∑ j, G x j * U j i) p ↔
        ∀ j, i ∈ polynomialAgreementSet domain (U j) (P j) := by
  classical
  -- Work on the entire agreement set of the given polynomial.
  let T := polynomialAgreementSet domain (fun i ↦ ∑ j, G x j * U j i) p
  have hmem : projectedWord (fun i ↦ ∑ j, G x j • U j i) T ∈
      projectedCodeSubmod (code domain k) T := by
    apply (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mpr
    refine ⟨p, hp, fun i hi ↦ ?_⟩
    simpa only [smul_eq_mul] using (mem_polynomialAgreementSet _ _ _ _).mp hi
  --
  -- A good challenge forces every constituent word to have a codeword on this set.
  obtain ⟨c, hc⟩ :=
    (not_isMCA_iff_forall_exists_codewords G (code domain k) x U δ).mp hgood T hclose hmem
  choose P hP hPeval using fun j ↦ mem_code_iff_eval.mp (c j).property
  have hPevalT : ∀ j i, i ∈ T → (P j).eval (domain i) = U j i :=
    fun j i hi ↦ (hPeval j i).trans (hc j i hi)
  --
  -- Enough common evaluations identify the polynomial linear combination uniquely.
  have hkT : k ≤ T.card := by exact_mod_cast hk.trans hclose
  have hsum : (∑ j, G x j • P j).degree < k := by
    apply mem_degreeLT.mp
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (mem_degreeLT.mpr (hP j))
  have heq : p = ∑ j, G x j • P j := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T) domain.injective.injOn
      (hp.trans_le (by exact_mod_cast hkT)) (hsum.trans_le (by exact_mod_cast hkT))
    intro i hi
    rw [(mem_polynomialAgreementSet _ _ _ _).mp hi]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (G x j * ·) (hPevalT j i hi).symm
  --
  -- Recover equality of the full sets, not merely inclusion of a selected subset.
  refine ⟨P, hP, heq, fun i ↦ ?_⟩
  simp only [mem_polynomialAgreementSet]
  constructor
  · intro hi j
    exact hPevalT j i ((mem_polynomialAgreementSet _ _ _ _).mpr hi)
  · intro hi
    rw [heq]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, hi]

end ReedSolomon
