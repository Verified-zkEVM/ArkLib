/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for graph-line recognition

On the domain `0, 1` in `ℚ`, the received words `f = (1, 2)` and `g = (1, 1)` and the pair
`F₀ = G₀ = 0` have an empty common agreement set, while the affine polynomial `0` agrees with
`f + z • g` at one coordinate for `z = -1` and `z = -2`. Both challenges are exceptional, so the
bound `Fintype.card ι - #(polynomialAgreementSet domain g G₀) = 2` is attained. When `G₀` agrees
with `g` everywhere, no challenge is exceptional. The recognition theorem identifies a concrete
polynomial over `ℚ`. The special cases over `Fin n`, with the mapped domain written
`mappedDomain`, are derived from the general ones.
-/

open Polynomial Finset

namespace ReedSolomon.GraphLineTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

@[simp] lemma dom_apply (i : Fin 2) : dom i = ![0, 1] i := rfl

/-- The count by disagreements of `G₀` is attained: every exceptional set for
`f = (1, 2)`, `g = (1, 1)`, `F₀ = G₀ = 0` contains `-1` and `-2`. -/
example (exceptional : Finset ℚ)
    (h : ∀ z ∉ exceptional,
      polynomialAgreementSet (dom.trans ⟨RingHom.id ℚ, (RingHom.id ℚ).injective⟩)
          (fun i ↦ RingHom.id ℚ (![1, 2] i) + z * RingHom.id ℚ (![1, 1] i))
          ((0 : ℚ[X]).map (RingHom.id ℚ) + C z * (0 : ℚ[X]).map (RingHom.id ℚ)) =
        commonPolynomialAgreementSet dom ![1, 2] ![1, 1] 0 0) :
    Fintype.card (Fin 2) - (polynomialAgreementSet dom ![1, 1] 0).card ≤ exceptional.card := by
  have hcommon : commonPolynomialAgreementSet dom ![1, 2] ![1, 1] (0 : ℚ[X]) 0 = ∅ := by
    ext i
    fin_cases i <;> simp
  have hmem : ∀ z : ℚ, ∀ i : Fin 2, z = -![1, 2] i → z ∈ exceptional := by
    intro z i hz
    by_contra hnot
    have hi := congrArg (i ∈ ·) (h z hnot)
    simp only [hcommon, Finset.notMem_empty, eq_iff_iff, iff_false] at hi
    apply hi
    rw [mem_polynomialAgreementSet]
    fin_cases i <;> simp_all
  have h1 := hmem (-1) 0 (by simp)
  have h2 := hmem (-2) 1 (by simp)
  have hg : polynomialAgreementSet dom ![1, 1] (0 : ℚ[X]) = ∅ := by
    ext i
    fin_cases i <;> simp
  rw [hg, card_empty, Fintype.card_fin]
  calc 2 - 0 = ({-1, -2} : Finset ℚ).card := by norm_num
    _ ≤ exceptional.card := card_le_card (by simp [insert_subset_iff, h1, h2])

/-- If `G₀` agrees with `g` everywhere, no challenge is exceptional: for every `z`, the agreement
set of `F₀ + C z * G₀` with `f + z • g` is the agreement set of `F₀` with `f`. -/
example (f : Fin 2 → ℚ) (F₀ : ℚ[X]) (z : ℚ) :
    polynomialAgreementSet (dom.trans ⟨RingHom.id ℚ, (RingHom.id ℚ).injective⟩)
        (fun i ↦ RingHom.id ℚ (f i) + z * RingHom.id ℚ (1 : ℚ))
        (F₀.map (RingHom.id ℚ) + C z * (C 1 : ℚ[X]).map (RingHom.id ℚ)) =
      commonPolynomialAgreementSet dom f (fun _ ↦ 1) F₀ (C 1) := by
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_graphLine_challenges_le_disagreement dom f (fun _ ↦ 1) F₀ (C 1)
      (RingHom.id ℚ)
  have hfull : polynomialAgreementSet dom (fun _ ↦ 1) (C 1 : ℚ[X]) = univ := by
    ext i
    simp
  rw [hfull, card_univ, Nat.sub_self, Nat.le_zero, card_eq_zero] at hcard
  exact hagree z (by simp [hcard])

/-- Recognition over `ℚ`: on the sample of both coordinates, `C 1 + C (1 + z) * X` agrees with
`f + z • g` for `f = (1, 2)` and `g = (0, 1)`, so it is `F₀ + C z * G₀` for the pair fixed before
`z`. Two challenges give the same pair. -/
example : ∃ F₀ G₀ : ℚ[X], ∀ z : ℚ, C 1 + C (1 + z) * X = F₀ + C z * G₀ := by
  obtain ⟨F₀, G₀, -, -, -, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample dom ![1, 2] ![0, 1] univ (card_univ.trans rfl)
  refine ⟨F₀, G₀, fun z ↦ ?_⟩
  have h := hrecognize (RingHom.id ℚ) z (C 1 + C (1 + z) * X) (by
    rw [Fintype.card_fin]
    compute_degree!) (by
    intro i _
    fin_cases i
    · simp
    · simp
      ring)
  simpa using h

section FinCoordinates

variable {F E : Type*} [Field F] [Field E] {n : ℕ}

/-- The evaluation domain mapped along the field homomorphism `iota`. -/
def mappedDomain (domain : Fin n ↪ F) (iota : F →+* E) : Fin n ↪ E :=
  domain.trans ⟨iota, iota.injective⟩

/-- `exists_graphLine_polynomials_of_sample` over coordinates `Fin n`. -/
example {k : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsampleCard : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ {E : Type*} [Field E] (iota : F →+* E) (z : E) (P : E[X]),
        P.degree < k →
        (∀ i ∈ sample,
          P.eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i)) →
        P = F₀.map iota + Polynomial.C z * G₀.map iota :=
  exists_graphLine_polynomials_of_sample domain f g sample hsampleCard

/-- `exists_exceptional_graphLine_challenges` over coordinates `Fin n`. -/
example [DecidableEq F] [DecidableEq E] (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X])
    (iota : F →+* E) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ n - (commonPolynomialAgreementSet domain f g F₀ G₀).card ∧
      ∀ z ∉ exceptional,
      polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i))
          (F₀.map iota + Polynomial.C z * G₀.map iota) =
        commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa [mappedDomain] using exists_exceptional_graphLine_challenges domain f g F₀ G₀ iota

/-- `exists_graphLine_polynomials_and_exceptional_challenges` over coordinates `Fin n`, with the
weaker bound `n`. -/
example [DecidableEq F] {k : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsampleCard : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      (∀ {E : Type*} [Field E] (iota : F →+* E) (z : E) (P : E[X]),
        P.degree < k →
        (∀ i ∈ sample,
          P.eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i)) →
        P = F₀.map iota + Polynomial.C z * G₀.map iota) ∧
      ∀ {E : Type*} [Field E] [DecidableEq E] (iota : F →+* E),
        ∃ exceptional : Finset E, exceptional.card ≤ n ∧ ∀ z ∉ exceptional,
          polynomialAgreementSet (mappedDomain domain iota)
              (fun i ↦ iota (f i) + z * iota (g i))
              (F₀.map iota + Polynomial.C z * G₀.map iota) =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize, hexceptional⟩ :=
    exists_graphLine_polynomials_and_exceptional_challenges domain f g sample hsampleCard
  refine ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize, fun iota ↦ ?_⟩
  obtain ⟨exceptional, hcard, hagree⟩ := hexceptional iota
  exact ⟨exceptional, hcard.trans (by simp), hagree⟩

/-- `exists_frobeniusGraphLine_polynomials_of_sample` over coordinates `Fin n`, with the root
condition on every coordinate. -/
example {k : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) :
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
  obtain ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize⟩ :=
    exists_frobeniusGraphLine_polynomials_of_sample domain f g sample hsample
  exact ⟨F₀, G₀, hF₀, hG₀, hfg, fun ι p e _ roots center w P hroots ↦
    hrecognize ι p e roots center w P fun i _ ↦ hroots i⟩

/-- `exists_exceptional_graphLine_challenges_of_sample` over coordinates `Fin n`. -/
example [DecidableEq F] [DecidableEq E] {k : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k) (F₀ G₀ : F[X])
    (hfg : ∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)
    (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ n - k ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (mappedDomain domain ι)
            (fun i ↦ ι (f i) + z * ι (g i)) (F₀.map ι + C z * G₀.map ι) =
          commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa [mappedDomain] using
    exists_exceptional_graphLine_challenges_of_sample domain f g sample hsample F₀ G₀ hfg ι

end FinCoordinates

end ReedSolomon.GraphLineTest
