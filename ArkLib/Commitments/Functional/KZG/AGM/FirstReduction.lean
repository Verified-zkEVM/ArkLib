/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.Security
public import CompPoly.Univariate.ToPoly.Degree

/-!
# KZG recovery from the first inconsistent claim

Selecting one inconsistent claim, filtering roots, and removing duplicates bounds the number
of verifier-key tests independently of the number of claims. Both binding games accept every
opening, so the selected claim still supplies a trapdoor root.

References: [KZG10TR]; Fuchsbauer–Kiltz–Loss, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
open scoped ENNReal

namespace KZG.AGM

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- The first claim inconsistent with the extracted commitment, retaining its proof index. -/
def firstClaim (cs : ℕ → Fin (n + 1) → F) (claims : List (F × F)) :
    Option (Fin claims.length) :=
  (List.finRange claims.length).find? fun i => decide (claims[i].2 ≠ evaluate (cs 0) claims[i].1)

/-- Scalar-only candidate generation; arbitrary root-finder output is checked and deduplicated. -/
def candidatesFirstData (roots : CPolynomial F → List F)
    (cs : ℕ → Fin (n + 1) → F) (claims : List (F × F)) : List F :=
  match firstClaim cs claims with
  | none => []
  | some i =>
      let p := openingPolynomial (cs 0) (cs (i.val + 1)) claims[i].1 claims[i].2
      ((roots p).filter fun a => decide (p.eval a = 0)).dedup

/-- A polynomial built from `n + 1` coefficients has degree at most `n`. -/
theorem natDegree_ofFn_le (f : Fin (n + 1) → F) :
    (CPolynomial.ofFn f).natDegree ≤ n := by
  rw [CPolynomial.natDegree_toPoly]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofFn]
  simp [show ¬ k < n + 1 by omega]

/-- Opening equations have degree at most `n + 1`. -/
theorem natDegree_openingPolynomial_le (f q : Fin (n + 1) → F) (z v : F) :
    (openingPolynomial f q z v).natDegree ≤ n + 1 := by
  unfold openingPolynomial
  apply (CPolynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (CPolynomial.natDegree_sub_le _ _).trans
      (max_le ((natDegree_ofFn_le f).trans (by omega)) (by rw [CPolynomial.natDegree_C]; omega))
  · exact (CPolynomial.natDegree_mul_le _ _).trans
      (by simpa only [CPolynomial.natDegree_X_sub_C] using
        Nat.add_le_add_right (natDegree_ofFn_le q) 1)

/-- Checked distinct roots of a nonzero polynomial are bounded by its degree. -/
theorem length_checkedRoots_le (roots : CPolynomial F → List F) (p : CPolynomial F)
    (hp : p ≠ 0) :
    (((roots p).filter fun a => decide (p.eval a = 0)).dedup).length ≤ p.natDegree := by
  let xs := ((roots p).filter fun a => decide (p.eval a = 0)).dedup
  have hn : xs.Nodup := List.nodup_dedup _
  have h := Polynomial.card_le_degree_of_subset_roots (p := p.toPoly)
    (Z := xs.toFinset) (by
      intro a ha
      have ha' : a ∈ xs := by simpa using ha
      have he : p.eval a = 0 := by simpa [xs] using (List.mem_filter.mp (List.mem_dedup.mp ha')).2
      exact (Polynomial.mem_roots ((CPolynomial.toPoly_eq_zero_iff p).not.mpr hp)).mpr
        (by simpa only [Polynomial.IsRoot, CPolynomial.toPoly_eval] using he))
  simpa only [List.toFinset_card_of_nodup hn, ← CPolynomial.natDegree_toPoly] using h

/-- Candidate tests cost at most `n + 1`, without any correctness assumption on the root finder. -/
theorem length_candidatesFirstData_le (roots : CPolynomial F → List F)
    (cs : ℕ → Fin (n + 1) → F) (claims : List (F × F)) :
    (candidatesFirstData roots cs claims).length ≤ n + 1 := by
  unfold candidatesFirstData
  cases h : firstClaim cs claims with
  | none => simp
  | some i =>
      unfold firstClaim at h
      have hi := List.find?_some h
      simp only [decide_eq_true_eq] at hi
      exact (length_checkedRoots_le roots _ (openingPolynomial_ne_zero _ _ _ _ hi)).trans
        (natDegree_openingPolynomial_le _ _ _ _)

variable {G₁ G₂ Gₜ D : Type}
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]

/-- Select roots using only output data and its coefficient explanations. -/
def candidatesFirst (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (out : Output F G₁ G₂ D) : List F :=
  candidatesFirstData roots (coefficients (n := n) out) (claims out.value.data)

/-- Match the selected candidates against the second verifier-key entry. -/
def recoverFirst [DecidableEq G₂] (g₂ : G₂) (vk : Fin 2 → G₂)
    (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (out : Output F G₁ G₂ D) : F :=
  ((candidatesFirst (n := n) roots claims out).find? fun r => decide (r • g₂ = vk 1)).getD 0

/-- A binding reduction whose root-testing cost is independent of the claim count. -/
def reductionFirst [DecidableEq G₂] (g₂ : G₂) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (A : Adversary F G₁ G₂ D) :
    PairingDLog.Adversary F G₁ G₂ n 1 :=
  fun ck vk => recoverFirst (n := n) g₂ vk roots claims <$> run A ck vk

/-- All openings are accepted and at least one disagrees with the extracted commitment. -/
def bindingWitness [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁)
    (vk : Fin 2 → G₂) (claims : D → List (F × F)) (out : Output F G₁ G₂ D) : Prop :=
  (∀ o ∈ openings claims out, verifyOpening e g₁ vk (point out 0) o.1 o.2.1 o.2.2 = true) ∧
    ∃ i : Fin (claims out.value.data).length,
      (claims out.value.data)[i].2 ≠
        evaluate (coefficients (n := n) out 0) (claims out.value.data)[i].1

/-- A binding winner puts the trapdoor in the first claim's checked root list. -/
theorem trapdoor_mem_candidatesFirst [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (claims : D → List (F × F)) (τ : F) (out : Output F G₁ G₂ D)
    (hvalid : out.Valid (initialInput (committerKey g₁ τ n) (verifierKey g₂ τ)).groups)
    (hwin : bindingWitness (n := n) e g₁ (verifierKey g₂ τ) claims out) :
    τ ∈ candidatesFirst (n := n) roots claims out := by
  unfold candidatesFirst candidatesFirstData
  cases hf : firstClaim (coefficients (n := n) out) (claims out.value.data) with
  | none =>
      unfold firstClaim at hf
      obtain ⟨i, hi⟩ := hwin.2
      have hn := List.find?_eq_none.mp hf i (List.mem_finRange i)
      simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_not] at hn
      exact (hi hn).elim
  | some i =>
      unfold firstClaim at hf
      have hi := List.find?_some hf
      simp only [decide_eq_true_eq] at hi
      have ha := hwin.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      have hc := point_eq_commit out _ _ hvalid
      change verifyOpening _ _ _ (point out 0) _ _ (point out (i.val + 1)) = true at ha
      rw [hc 0, hc (i.val + 1)] at ha
      have hp := accepted_opening_root he (coefficients out 0) (coefficients out (i.val + 1))
        τ _ _ ha hi
      exact List.mem_dedup.mpr (List.mem_filter.mpr ⟨hroots _ hp.1 τ hp.2, by simpa using hp.2⟩)

/-- A matching candidate uniquely identifies the trapdoor. -/
theorem recoverFirst_eq [DecidableEq G₂]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (τ : F) (out : Output F G₁ G₂ D)
    (hm : τ ∈ candidatesFirst (n := n) roots claims out) :
    recoverFirst (n := n) g₂ (verifierKey g₂ τ) roots claims out = τ := by
  unfold recoverFirst
  cases hf : (candidatesFirst (n := n) roots claims out).find?
      (fun r => decide (r • g₂ = (verifierKey g₂ τ) 1)) with
  | none =>
      have hn := List.find?_eq_none.mp hf τ hm
      simp [verifierKey] at hn
  | some r =>
      have hr := List.find?_some hf
      have hr' : r • g₂ = τ • g₂ := by
        simpa [verifierKey] using of_decide_eq_true hr
      exact smul_right_injective_of_pairing_ne_zero he hr'

end KZG.AGM
