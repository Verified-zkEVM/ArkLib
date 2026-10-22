/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.FoldingSoundness
public import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius

/-!
# Agreement lifting along the executable FRI query projections

The executable specification indexes every domain from the original domain. This module
applies the single-fold agreement theorem to positions projected through an arbitrary
prefix of folding rounds, keeping the original query set fixed.
-/

@[expose] public section

namespace Fri

open Domain ProximityGap ReedSolomon LinearCode Polynomial
open CosetFftDomainClass (sqFoldMapGen)

variable {F : Type} [Field F] [DecidableEq F] {n a k d : ℕ}

/-! ## Density under projection -/

omit [DecidableEq F] in
/-- Taking the image under a folding map cannot decrease the density of a set. -/
theorem card_le_mul_card_sqFoldMapGen_image {n : ℕ} (domain : SmoothCosetFftDomain n F)
    (k : ℕ) (S : Finset (Fin (2 ^ n))) :
    S.card ≤ 2 ^ k * (S.image (sqFoldMapGen (i := k))).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro x _
  apply le_trans (Finset.card_le_card (t :=
    CosetFftDomainClass.blockIdx domain k (domain.subdomain k x)) ?_)
    (by simp)
  intro i hi
  obtain ⟨_, hix⟩ := Finset.mem_filter.mp hi
  rw [CosetFftDomainClass.mem_blockIdx,
    ← CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain) (i := k) i, hix]

/-- Convert agreement on a large accepting set into a density bound. The lifting premise
is independent of the representation of a commitment transcript. -/
theorem accepting_density_le_of_agreement {n d : ℕ} (domain : SmoothCosetFftDomain n F)
    (f : Fin (2 ^ n) → F) (S : Finset (Fin (2 ^ n))) (θ δ : ℝ)
    (hlift : (2 ^ n : ℝ) * (1 - θ) ≤ S.card →
      ∃ u ∈ code domain d, ∀ i ∈ S, u i = f i)
    (hdist : ∀ u ∈ code domain d, δ ≤ (Code.relHammingDist f u : ℝ)) :
    (S.card : ℝ) / 2 ^ n ≤ 1 - min θ δ := by
  classical
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  by_cases hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ S.card
  · obtain ⟨u, hu, hagree⟩ := hlift hlarge
    have hc : S.card ≤ Code.agree u f := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree i hi⟩
    have hdensity : δ ≤ 1 - (S.card : ℝ) / 2 ^ n := by
      have h := (hdist u hu).trans (Code.relHammingDist_le_one_sub_div_of_le_agree hc)
      simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h
    exact (le_sub_comm.mp hdensity).trans (sub_le_sub_left (min_le_right θ δ) 1)
  · have hdensity : (S.card : ℝ) / 2 ^ n ≤ 1 - θ := by
      exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using (not_le.mp hlarge).le)
    exact hdensity.trans (sub_le_sub_left (min_le_left θ δ) 1)

/-! ## Lifting through a projected fold -/

/-- Lift a polynomial agreement certificate through a safe fold, on the projected positions
of a large set of original queries. This reconciles absolute and nested domain indexing. -/
theorem exists_polynomial_agree_on_projection
    (domain : SmoothCosetFftDomain n F) (hak : a + k ≤ n) (hd : 0 < d)
    (f : Fin (2 ^ (n - a)) → F) (α : F) (θ : ℝ)
    (hsafe : ¬ FoldingAgreementFailure (domain.subdomain a) f k d θ α)
    (S : Finset (Fin (2 ^ n))) (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ S.card)
    (p : F[X]) (hp : p.natDegree < d)
    (hcheck : ∀ z ∈ S,
      foldValue (domain.subdomain a) f k α ((domain z ^ (2 ^ a)) ^ (2 ^ k)) =
        p.eval ((domain z ^ (2 ^ a)) ^ (2 ^ k))) :
    ∃ q : F[X], q.natDegree < 2 ^ k * d ∧
      ∀ z ∈ S, q.eval (domain z ^ (2 ^ a)) = f (sqFoldMapGen (i := a) z) := by
  classical
  let T := (S.image (sqFoldMapGen (i := a))).image (sqFoldMapGen (i := k))
  have hTlarge : (2 ^ (n - a - k) : ℝ) * (1 - θ) ≤ T.card := by
    have h₁ : (S.card : ℝ) ≤
        2 ^ a * ((S.image (sqFoldMapGen (i := a))).card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image domain a S
    have h₂ : ((S.image (sqFoldMapGen (i := a))).card : ℝ) ≤
        2 ^ k * (T.card : ℝ) := by
      exact_mod_cast card_le_mul_card_sqFoldMapGen_image (domain.subdomain a) k
        (S.image (sqFoldMapGen (i := a)))
    have hn : (2 : ℝ) ^ n = 2 ^ a * (2 ^ k * 2 ^ (n - a - k)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hn] at hlarge
    have hmul := mul_le_mul_of_nonneg_left h₂ (show (0 : ℝ) ≤ 2 ^ a by positivity)
    have hproduct : (0 : ℝ) < 2 ^ a * 2 ^ k := by positivity
    nlinarith
  have hpow (z : Fin (2 ^ n)) :
      (domain.subdomain a).subdomain k
          (sqFoldMapGen (i := k) (sqFoldMapGen (i := a) z)) =
        (domain z ^ (2 ^ a)) ^ (2 ^ k) := by
    rw [CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen,
      CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen]
  have hfold : projectedWord (foldWord (domain.subdomain a) f k α) T ∈
      projectedCodeSubmod (code ((domain.subdomain a).subdomain k) d) T := by
    rw [mem_projectedCodeSubmod_iff]
    refine ⟨evalOnPoints _ p, evalOnPoints_mem_code_of_natDegree_lt hp, ?_⟩
    funext x
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.property
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    change foldValue _ f k α (((domain.subdomain a).subdomain k) x.val) =
      p.eval (((domain.subdomain a).subdomain k) x.val)
    rw [← hxy, hpow]
    exact hcheck z hz
  have hlift : ∃ u ∈ code (domain.subdomain a) (2 ^ k * d),
      ∀ i x, x ∈ T → domain.subdomain a i ^ (2 ^ k) =
        (domain.subdomain a).subdomain k x → u i = f i := by
    by_contra h
    exact hsafe ⟨T, by simpa using hTlarge, hfold, h⟩
  obtain ⟨u, hu, hagree⟩ := hlift
  let : NeZero (2 ^ k * d) := ⟨by positivity⟩
  obtain ⟨q, hq, rfl⟩ := mem_code_iff_exists_polynomial_of_ne_zero.mp hu
  refine ⟨q, hq, fun z hz ↦ ?_⟩
  have h := hagree (sqFoldMapGen (i := a) z)
    (sqFoldMapGen (i := k) (sqFoldMapGen (i := a) z))
    (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hz))
    (CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen (ω := domain.subdomain a) _).symm
  change q.eval (domain.subdomain a (sqFoldMapGen (i := a) z)) = _ at h
  rwa [CosetFftDomainClass.pow_eq_subdomain_sqFoldMapGen] at h

end Fri
