/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.FullAgreement

/-!
# Nested power agreement

The exceptional scalar sets are selected before the candidate polynomial. The outer set may
depend on the first challenge; the inner sets depend only on the received groups. Counting
pairs therefore gives the sum of the scalar exception budgets times the field size.
-/

noncomputable section
namespace ReedSolomon
open Polynomial
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}

/-- A scalar exceptional set works simultaneously for every degree-bounded candidate with
at least `L` agreements. This is the reusable leaf contract, including its quantifier order. -/
def UniformExactPowerAgreement {ℓ : ℕ} (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (k L E : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ E ∧ ∀ z ∉ bad, ∀ Q : F[X], Q.degree < k →
    L ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
    HasExactPowerAgreement domain w (RingHom.id F) k z Q

/-- A group with one word uses no challenge and has no exceptional scalars. -/
theorem uniformExactPowerAgreement_singleton (domain : Fin n ↪ F)
    (w : Fin (0 + 1) → Fin n → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ _
  refine ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [polynomialAgreementSet, commonCurveAgreementSet, mappedDomain, powerBatchedWord]

/-- The exact nested conclusion recovers each original message, its degree, the complete
polynomial identity, and equality of the entire agreement set. -/
def HasExactNestedPowerAgreement (domain : Fin n ↪ F) (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → Fin n → F)
    (k : ℕ) (u v : F) (Q : F[X]) : Prop :=
  ∃ P : (g : Fin (m + 1)) → Fin (ℓ g + 1) → F[X],
    (∀ g j, (P g j).degree < k) ∧
    Q = powerBatchedPolynomial (fun g ↦ powerBatchedPolynomial (P g) u) v ∧
    polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q =
      Finset.univ.filter (fun i ↦ ∀ g j, (P g j).eval (domain i) = w g j i)

/-- Exact outer agreement makes every recovered group polynomial at least as close as the
outer candidate. Exact inner agreement can then be applied to those group polynomials. -/
theorem exactNestedPowerAgreement_of_exact (domain : Fin n ↪ F)
    (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → Fin n → F)
    (k L : ℕ) (u v : F) (Q : F[X])
    (hclose : L ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q).card)
    (houter : HasExactPowerAgreement domain (fun g ↦ powerBatchedWord (w g) u)
      (RingHom.id F) k v Q)
    (hinner : ∀ g (R : F[X]), R.degree < k →
      L ≤ (polynomialAgreementSet domain (powerBatchedWord (w g) u) R).card →
      HasExactPowerAgreement domain (w g) (RingHom.id F) k u R) :
    HasExactNestedPowerAgreement domain ℓ w k u v Q := by
  obtain ⟨R, hRdeg, hReq, hRset⟩ := houter
  simp only [Polynomial.map_id] at hReq
  have hRset' : polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q =
      commonCurveAgreementSet domain (fun g ↦ powerBatchedWord (w g) u) R := by
    simpa [mappedDomain] using hRset
  have hRclose (g) : L ≤
      (polynomialAgreementSet domain (powerBatchedWord (w g) u) (R g)).card := by
    apply hclose.trans
    rw [hRset']
    apply Finset.card_le_card
    intro i hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [polynomialAgreementSet, hi g]
  choose P hPdeg hPeq hPset using fun g ↦ hinner g (R g) (hRdeg g) (hRclose g)
  refine ⟨P, hPdeg, ?_, ?_⟩
  · simpa only [Polynomial.map_id] using hReq.trans (congrArg
      (fun S ↦ powerBatchedPolynomial S v) (funext fun g ↦ hPeq g))
  · rw [hRset']
    ext i
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro g
    have h := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) (hPset g)
    simpa [polynomialAgreementSet, commonCurveAgreementSet, mappedDomain, powerBatchedWord,
      Finset.mem_filter] using h

/-- Two independent uniform scalar challenges compose the leaf contracts. The pair exceptional
set is fixed before `Q`; outer scalar exceptions may vary with `u`. Its cardinality is at most
`|F| * (sum innerE + outerE)`, hence its uniform-pair probability is bounded by the sum of
scalar budgets divided by `|F|`. Group widths are arbitrary positive natural numbers. A
singleton group supplies its inner contract with budget zero by
`uniformExactPowerAgreement_singleton`. -/
theorem nestedPowerAgreement [Fintype F] (domain : Fin n ↪ F)
    (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → Fin n → F)
    (k L : ℕ) (innerE : Fin (m + 1) → ℕ) (outerE : ℕ)
    (hinner : ∀ g, UniformExactPowerAgreement domain (w g) k L (innerE g))
    (houter : ∀ u, UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (w g) u) k L outerE) :
    ∃ bad : Finset (F × F),
      bad.card ≤ Fintype.card F * ((∑ g, innerE g) + outerE) ∧
      ∀ u v, (u, v) ∉ bad → ∀ Q : F[X], Q.degree < k →
        L ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q).card →
        HasExactNestedPowerAgreement domain ℓ w k u v Q := by
  classical
  choose innerBad hinnerCard hinnerGood using hinner
  choose outerBad houterCard houterGood using houter
  let innerUnion := Finset.univ.biUnion innerBad
  let outerPairs := Finset.univ.biUnion (fun u ↦ ({u} : Finset F).product (outerBad u))
  let bad := innerUnion.product (Finset.univ : Finset F) ∪ outerPairs
  have hi : innerUnion.card ≤ ∑ g, innerE g :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun g _ ↦ hinnerCard g)
  have ho : outerPairs.card ≤ Fintype.card F * outerE := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ u : F, (({u} : Finset F).product (outerBad u)).card ≤ ∑ _u : F, outerE := by
        apply Finset.sum_le_sum
        intro u _
        simpa using houterCard u
      _ = Fintype.card F * outerE := by simp
  refine ⟨bad, ?_, ?_⟩
  · calc
      bad.card ≤ (innerUnion.product (Finset.univ : Finset F)).card + outerPairs.card :=
        Finset.card_union_le _ _
      _ ≤ (∑ g, innerE g) * Fintype.card F + Fintype.card F * outerE := by
        simpa using Nat.add_le_add (Nat.mul_le_mul_right (Fintype.card F) hi) ho
      _ = _ := by ring
  · intro u v huv Q hQ hclose
    have hui : ∀ g, u ∉ innerBad g := by
      intro g hg
      apply huv
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hg⟩, Finset.mem_univ _⟩))
    have hvo : v ∉ outerBad u := by
      intro hv
      apply huv
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, by simp [hv]⟩))
    exact exactNestedPowerAgreement_of_exact domain ℓ w k L u v Q hclose
      (houterGood u v hvo Q hQ hclose) (fun g ↦ hinnerGood g u (hui g))

omit [DecidableEq F] in
/-- Under independent uniform sampling, each challenge pair has mass `1 / |F|²`.
This translates the integer exceptional-pair bound into the scalar-budget ratio. -/
theorem nestedPowerAgreement_probability_bound [Fintype F] (bad : Finset (F × F))
    (E : ℕ) (hbad : bad.card ≤ Fintype.card F * E) :
    (bad.card : ℚ) / (Fintype.card F : ℚ) ^ 2 ≤ (E : ℚ) / Fintype.card F := by
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hb : (bad.card : ℚ) ≤ (Fintype.card F : ℚ) * E := by exact_mod_cast hbad
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  calc
    (bad.card : ℚ) ≤ (Fintype.card F : ℚ) * E := hb
    _ = (E : ℚ) / Fintype.card F * (Fintype.card F : ℚ) ^ 2 := by
      field_simp

end ReedSolomon
