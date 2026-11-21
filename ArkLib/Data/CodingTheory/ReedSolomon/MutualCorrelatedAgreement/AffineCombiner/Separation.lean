/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lower bounds for scalar and affine combiner errors

Write `n` for the domain size and `q` for the field size.
Each lower bound uses an explicit received word pair with many exceptional challenges.
The bounds formalize Propositions 6.1 and 6.2 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records their hypotheses and scope.

## Affine combiner without agreement loss

Let `f = 0`, and let `g` be zero on a set `C` of size `A - 1` and one elsewhere.
For `z` outside `C` and `β ≠ 0`, the affine multiplier of the challenge `(-β z, β)` vanishes
at `z` and nowhere else.
The zero candidate therefore agrees on `C ∪ {z}`, a set of size `A`.
If `d + 1 < A`, a witness of degree below `d` that vanishes on `C` must be zero, so it
cannot agree with `g` at `z`.
The `(n - A + 1)(q - 1)` distinct challenges give the zero-loss lower bound.

## Scalar combiner with agreement loss

Let `g` evaluate the vanishing polynomial of a set of size `A - s - 1`.
If `d + s + 1 < A`, no polynomial of degree at most `d` agrees with `g` on `A - s` positions.
Partition the remaining coordinates into blocks of size `s + 1`, with a smaller final block
if necessary, and give each block a distinct challenge `γ`.
On that block set `f = -γ g`.
Since `g` vanishes only on the first set, the zero candidate agrees on that set and the block.
Each full block thus gives exactly `A` agreements and no witness of loss at most `s`.
Proposition 6.1 asserts these facts, and the error bound is their consequence.

## Main definitions

* `ReedSolomon.exactZeroChallenges`: the challenges whose combined word has exactly `A` zeros.

The set is noncomputable because it is phrased through the constant polynomial `C α`.

## Main statements

* `ReedSolomon.le_affineMcaError_zero_loss`: the bound `(n - A + 1)(q - 1) / q²`.
* `ReedSolomon.le_affineMcaError_zero_loss_div_two`: the bound `(n - A + 1) / (2q)`.
* `ReedSolomon.isScalarExceptional_of_forall_card_lt`: if `g` is far from the code, every
  candidate with `A` agreements is scalar exceptional.
* `ReedSolomon.le_scalarMcaError_of_forall_card_lt`: for such words, the error is at least the
  probability that `f + α g` has exactly `A` zeros.
* `ReedSolomon.exists_words_forall_isScalarExceptional_zero`: the words of Proposition 6.1,
  with `1 + ⌊(n - A) / (s + 1)⌋` challenges of exactly `A` agreements, all exceptional.
* `ReedSolomon.le_scalarMcaError_of_degree_add_loss_add_one_lt`:
  the bound `(1 + ⌊(n - A) / (s + 1)⌋) / q`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- In a fixed enumeration, the coordinates whose position lies in `U` number exactly `#U`.

Every element of `U` must be a valid position. -/
private theorem card_filter_equivFin_mem (U : Finset ℕ) (hU : ∀ k ∈ U, k < Fintype.card ι) :
    #{i : ι | (Fintype.equivFin ι i : ℕ) ∈ U} = #U := by
  classical
  rw [← card_image_of_injective _
    (Fin.val_injective.comp (Fintype.equivFin ι).injective)]
  congr 1
  ext k
  simp only [mem_image, mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hk
    exact ⟨(Fintype.equivFin ι).symm ⟨k, hU k hk⟩, by simpa using hk, by simp⟩

/-- If `d + 1 < A ≤ n`, the affine error at loss zero is at least
`(n - A + 1)(q - 1) / q²`, where `n = |ι|` and `q = |F|`. -/
theorem le_affineMcaError_zero_loss [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hdA : d + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ENNReal.ofReal (((Fintype.card ι - A + 1 : ℕ) : ℝ) * ((Fintype.card F : ℝ) - 1) /
        (Fintype.card F : ℝ) ^ 2) ≤
      affineMcaError domain d A 0 := by
  classical
  set n := Fintype.card ι
  set pos : ι → ℕ := fun i ↦ (Fintype.equivFin ι i : ℕ)
  have hpos_inj : Function.Injective pos :=
    Fin.val_injective.comp (Fintype.equivFin ι).injective
  have hpos_lt : ∀ i, pos i < n := fun i ↦ (Fintype.equivFin ι i).isLt
  let g : ι → F := fun i ↦ if pos i < A - 1 then 0 else 1
  -- The agreement set of the zero candidate contains the first `A - 1` coordinates and `z`.
  have hS : ∀ z β i, pos i < A - 1 ∨ i = z →
      i ∈ polynomialAgreementSet domain (combinedWord domain 0 g
        (affineMultiplier (-(β * domain z)) β)) 0 := by
    rintro z β i (hi | rfl)
    · simp [g, hi]
    · simp
  have hexc : ∀ z β, A - 1 ≤ pos z → β ≠ 0 →
      IsAffineExceptional domain 0 g d A 0 (-(β * domain z)) β 0 := by
    intro z β hz hβ
    refine ⟨by simp, ?_, ?_⟩
    · have hU : ∀ k ∈ insert (pos z) (range (A - 1)), k < n := by
        intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · exact hpos_lt z
        · have := mem_range.mp hk
          omega
      calc A = #(insert (pos z) (range (A - 1))) := by
              rw [card_insert_of_notMem (by simpa using hz), card_range]
              omega
        _ = #{i : ι | pos i ∈ insert (pos z) (range (A - 1))} :=
              (card_filter_equivFin_mem _ hU).symm
        _ ≤ _ := by
              refine card_le_card fun i hi ↦ hS z β i ?_
              simp only [mem_filter, mem_univ, true_and, mem_insert, mem_range] at hi
              rcases hi with hi | hi
              · exact Or.inr (hpos_inj hi)
              · exact Or.inl hi
    · intro F₀ G₀ _ hG ⟨_, hloss⟩
      -- Without loss, `G₀` agrees with `g` on the whole agreement set.
      have hagree : ∀ i, pos i < A - 1 ∨ i = z → G₀.eval (domain i) = g i := by
        intro i hi
        by_contra hne
        have hmem : i ∈ agreementLoss domain 0 g (affineMultiplier (-(β * domain z)) β) 0
            F₀ G₀ := mem_filter.mpr ⟨hS z β i hi, Or.inr hne⟩
        exact (card_pos.mpr ⟨i, hmem⟩).ne' (Nat.le_zero.mp hloss)
      -- So `G₀` vanishes on `A - 1 > d` points, hence is zero, but `g z = 1`.
      have hG0 : G₀ = 0 := by
        refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' G₀
          ((univ.filter fun i : ι ↦ pos i ∈ range (A - 1)).map domain) ?_ ?_
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
          have hi : pos i < A - 1 := by simpa using hi
          rw [hagree i (Or.inl hi)]
          simp [g, hi]
        · rw [card_map, card_filter_equivFin_mem _ fun k hk ↦ by
            have := mem_range.mp hk; omega, card_range]
          have := natDegree_le_of_degree_le hG.le
          omega
      have := hagree z (Or.inr rfl)
      simp [hG0, g, not_lt.mpr hz] at this
  set q := Fintype.card F
  have hq : 1 ≤ q := Fintype.card_pos
  -- The challenges `(-β x_z, β)` with `β ≠ 0` and `z` outside the first `A - 1` coordinates.
  let E : Finset (F × F) :=
    ((univ.filter fun z : ι ↦ pos z ∈ Ico (A - 1) n) ×ˢ (univ.erase (0 : F))).image
      fun p ↦ (-(p.2 * domain p.1), p.2)
  have hEcard : #E = (n - (A - 1)) * (q - 1) := by
    rw [card_image_of_injOn, card_product, card_erase_of_mem (mem_univ _), card_univ,
      card_filter_equivFin_mem _ fun k hk ↦ (mem_Ico.mp hk).2, Nat.card_Ico]
    rintro ⟨z, β⟩ hzβ ⟨z', β'⟩ hzβ' h
    simp only [Prod.mk.injEq, neg_inj] at h
    obtain ⟨h1, rfl⟩ := h
    have hβ : β ≠ 0 := (mem_erase.mp (mem_product.mp hzβ).2).1
    rw [mul_right_inj' hβ, domain.apply_eq_iff_eq] at h1
    rw [h1]
  have hEsub :
      E ⊆ univ.filter fun c : F × F ↦ ∃ P, IsAffineExceptional domain 0 g d A 0 c.1 c.2 P := by
    intro c hc
    obtain ⟨⟨z, β⟩, hzβ, rfl⟩ := mem_image.mp hc
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_Ico, mem_erase] at hzβ
    exact mem_filter.mpr ⟨mem_univ _, 0, hexc z β hzβ.1.1 hzβ.2.1⟩
  refine le_trans ?_ (le_affineMcaError domain d A 0 0 g)
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ((n - A + 1 : ℕ) : ℝ) * ((q : ℝ) - 1) = (#E : ℝ) := by
        rw [hEcard, show n - A + 1 = n - (A - 1) by omega]
        push_cast [hq]
        ring
    _ ≤ _ := by exact_mod_cast card_le_card hEsub

/-- If `d + 1 < A ≤ n`, the affine error at loss zero is at least `(n - A + 1) / (2q)`,
where `n = |ι|` and `q = |F|`. -/
theorem le_affineMcaError_zero_loss_div_two [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hdA : d + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ENNReal.ofReal (((Fintype.card ι - A + 1 : ℕ) : ℝ) /
        (2 * (Fintype.card F : ℝ))) ≤
      affineMcaError domain d A 0 := by
  refine le_trans ?_ (le_affineMcaError_zero_loss domain hdA hAn)
  apply ENNReal.ofReal_le_ofReal
  have hq : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hN : (0 : ℝ) ≤ ((Fintype.card ι - A + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hN (by linarith : (0 : ℝ) ≤ Fintype.card F))
    (by linarith : (0 : ℝ) ≤ Fintype.card F - 2)]

/-- The challenges `α` for which the word `f + α g` has exactly `A` zeros on the domain. -/
def exactZeroChallenges [Fintype F] (f g : ι → F) (A : ℕ) :
    Finset F :=
  {α : F | #{i : ι | f i + α * g i = 0} = A}

/-- A challenge lies in the set exactly when its combined word has `A` zeros. -/
@[simp] theorem mem_exactZeroChallenges [Fintype F] (f g : ι → F) (A : ℕ) (α : F) :
    α ∈ exactZeroChallenges f g A ↔ #{i : ι | f i + α * g i = 0} = A := by
  simp [exactZeroChallenges]

/-- The zero positions are the agreement set with the zero polynomial on any domain. -/
theorem mem_exactZeroChallenges_iff_card_polynomialAgreementSet [Fintype F]
    (domain : ι ↪ F) (f g : ι → F) (A : ℕ) (α : F) :
    α ∈ exactZeroChallenges f g A ↔
      #(polynomialAgreementSet domain (combinedWord domain f g (C α)) 0) = A := by
  simp [polynomialAgreementSet, combinedWord, eq_comm]

/-- Suppose no polynomial of degree at most `d` agrees with `g` on `A - s` domain points.

Let `P` have degree at most `d` and agree with `f + α g` on at least `A` points.

Then `P` is scalar exceptional for `α` at threshold `A` and loss `s`. -/
theorem isScalarExceptional_of_forall_card_lt (domain : ι ↪ F) {f g : ι → F}
    {d A s : ℕ} (hfar : ∀ G : F[X], G.degree ≤ d → #(polynomialAgreementSet domain g G) < A - s)
    {α : F} {P : F[X]} (hP : P.degree ≤ d)
    (hA : A ≤ #(polynomialAgreementSet domain (combinedWord domain f g (C α)) P)) :
    IsScalarExceptional domain f g d A s α P := by
  refine ⟨hP, hA, fun F₀ G₀ _ hG ⟨_, hloss⟩ ↦ ?_⟩
  -- Off the lost points, the witness `G₀` agrees with `g`.
  have hsplit := card_filter_add_card_filter_not
    (s := polynomialAgreementSet domain (combinedWord domain f g (C α)) P)
    fun i ↦ F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i
  have hkept : #((polynomialAgreementSet domain (combinedWord domain f g (C α)) P).filter
      fun i ↦ ¬(F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i)) ≤
      #(polynomialAgreementSet domain g G₀) := by
    refine card_le_card fun i hi ↦ ?_
    simp only [mem_filter, ne_eq, not_or, not_not] at hi
    simp [hi.2.2]
  have := hfar G₀ hG
  unfold agreementLoss at hloss
  omega

/-- Suppose no polynomial of degree at most `d` agrees with `g` on `A - s` domain points.

Let `q = |F|` be the field size.

Let `E` be the set of challenges `α` for which `f + α g` has exactly `A` zeros.

Then the scalar error at loss `s` is at least `|E| / q`. -/
theorem le_scalarMcaError_of_forall_card_lt [Fintype F] (domain : ι ↪ F) {f g : ι → F}
    {d A s : ℕ} (hfar : ∀ G : F[X], G.degree ≤ d → #(polynomialAgreementSet domain g G) < A - s) :
    ENNReal.ofReal ((#(exactZeroChallenges f g A) : ℝ) / (Fintype.card F : ℝ)) ≤
      scalarMcaError domain d A s := by
  classical
  refine le_trans ?_ (le_scalarMcaError domain d A s f g)
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : exactZeroChallenges f g A ⊆
      ({α : F | ∃ P, IsScalarExceptional domain f g d A s α P} : Finset F) := fun α hα ↦
    mem_filter.mpr ⟨mem_univ _, 0, isScalarExceptional_of_forall_card_lt domain hfar (by simp)
      ((mem_exactZeroChallenges_iff_card_polynomialAgreementSet domain f g A α).mp hα).ge⟩
  exact_mod_cast card_le_card hsub

/-- Received words separating scalar combiners.

Let `n = |ι|` be the domain size and `q = |F|` the field size.
Assume `d + s + 1 < A ≤ n`.
There are words `f, g` such that no polynomial of degree `≤ d` agrees with `g` on `A - s` points.
Let `α` be a challenge for which the word `f + α g` has exactly `A` zeros.
Then the zero candidate is scalar exceptional for `α` at threshold `A` and loss `s`.
At least `1 + ⌊(n - A) / (s + 1)⌋` challenges give exactly `A` zeros. -/
theorem exists_words_forall_isScalarExceptional_zero [Fintype F] (domain : ι ↪ F)
    {d A s : ℕ} (hdA : d + s + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ∃ f g : ι → F,
      (∀ G : F[X], G.degree ≤ d → #(polynomialAgreementSet domain g G) < A - s) ∧
      (∀ α : F, #(polynomialAgreementSet domain (combinedWord domain f g (C α)) 0) = A →
        IsScalarExceptional domain f g d A s α 0) ∧
      1 + (Fintype.card ι - A) / (s + 1) ≤ #(exactZeroChallenges f g A) := by
  classical
  set n := Fintype.card ι
  set pos : ι → ℕ := fun i ↦ (Fintype.equivFin ι i : ℕ)
  set m := A - s - 1
  set k := 1 + (n - A) / (s + 1) with hk
  have hkn : m + k * (s + 1) ≤ n := by
    have := Nat.div_mul_le_self (n - A) (s + 1)
    have : k * (s + 1) = (s + 1) + (n - A) / (s + 1) * (s + 1) := by rw [hk]; ring
    omega
  -- The vanishing polynomial `V` of the first `m` coordinates is the second received word.
  set C₀ := univ.filter fun i : ι ↦ pos i ∈ range m
  have hCcard : #C₀ = m := by
    rw [card_filter_equivFin_mem _ fun k hk ↦ by have := mem_range.mp hk; omega, card_range]
  set V : F[X] := Lagrange.nodal C₀ domain
  have hVdeg : V.natDegree = m := by rw [Lagrange.natDegree_nodal, hCcard]
  set g : ι → F := fun i ↦ V.eval (domain i)
  have hg0 : ∀ i, g i = 0 ↔ pos i < m := by
    intro i
    refine ⟨fun h ↦ ?_, fun hi ↦ Lagrange.eval_nodal_at_node (by simpa [C₀] using hi)⟩
    by_contra hi
    refine Lagrange.eval_nodal_not_at_node (fun c hc hic ↦ hi ?_) h
    rw [domain.injective hic]
    simpa [C₀] using hc
  -- Distinct challenges, one per block of `s + 1` coordinates after the first `m`.
  set γ : ℕ → F := fun j ↦ if h : j < n then domain ((Fintype.equivFin ι).symm ⟨j, h⟩) else 0
  have hγ : Set.InjOn γ (range n) := by
    intro j hj j' hj' h
    have hj : j < n := mem_range.mp hj
    have hj' : j' < n := mem_range.mp hj'
    simpa [γ, hj, hj'] using h
  set lab : ι → ℕ := fun i ↦ (pos i - m) / (s + 1)
  have hlab : ∀ i, lab i < n := fun i ↦
    (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt (Fintype.equivFin ι i).isLt)
  set f : ι → F := fun i ↦ -(γ (lab i) * g i)
  -- No polynomial of degree at most `d < m` agrees with `V` on `m + 1` points.
  have hfar : ∀ G : F[X], G.degree ≤ d → #(polynomialAgreementSet domain g G) < A - s := by
    intro G hG
    by_contra hge
    have hGd := natDegree_le_of_degree_le hG
    have hzero : V - G = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        ((polynomialAgreementSet domain g G).map domain) (fun x hx ↦ ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
        rw [mem_polynomialAgreementSet] at hi
        simp [g, hi]
      · rw [card_map]
        have := natDegree_sub_le V G
        omega
    rw [sub_eq_zero] at hzero
    rw [hzero] at hVdeg
    omega
  -- The zeros of `f + γ_j g` are the first `m` coordinates and the block `j`.
  have hzeros : ∀ j < n, ∀ i,
      i ∈ polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0 ↔
        pos i < m ∨ lab i = j := by
    intro j hj i
    simp only [mem_polynomialAgreementSet, combinedWord, eval_zero, eval_C, f]
    by_cases hi : pos i < m
    · simp [(hg0 i).mpr hi, hi]
    · have hgi : g i ≠ 0 := fun h ↦ hi ((hg0 i).mp h)
      rw [show -(γ (lab i) * g i) + γ j * g i = (γ j - γ (lab i)) * g i by ring, eq_comm,
        mul_eq_zero, sub_eq_zero]
      simp only [hgi, or_false, hi, false_or]
      exact ⟨fun h ↦ (hγ (mem_range.mpr hj) (mem_range.mpr (hlab i)) h).symm,
        fun h ↦ by rw [h]⟩
  have hcard : ∀ j < k,
      #(polynomialAgreementSet domain (combinedWord domain f g (Polynomial.C (γ j))) 0) = A := by
    intro j hj
    have hjk : (j + 1) * (s + 1) ≤ k * (s + 1) := Nat.mul_le_mul_right _ hj
    have hjn : j < n := by
      have : k ≤ k * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hU : ∀ x ∈ range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1)), x < n := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · have := mem_range.mp hx; omega
      · have := mem_Ico.mp hx; omega
    calc _ = #{i : ι | pos i ∈ range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1))} := by
          congr 1
          ext i
          rw [hzeros j hjn i]
          simp only [mem_filter, mem_univ, true_and, mem_union, mem_range, mem_Ico]
          constructor
          · rintro (hi | hi)
            · exact Or.inl hi
            · by_cases him : pos i < m
              · exact Or.inl him
              · have h1 := Nat.div_mul_le_self (pos i - m) (s + 1)
                have h2 := Nat.lt_div_mul_add (a := pos i - m) (b := s + 1) (by omega)
                simp only [lab] at hi
                rw [hi] at h1 h2
                refine Or.inr ⟨by omega, ?_⟩
                rw [add_mul, one_mul]
                omega
          · rintro (hi | hi)
            · exact Or.inl hi
            · exact Or.inr (Nat.div_eq_of_lt_le (by omega) (by omega))
      _ = #(range m ∪ Ico (m + j * (s + 1)) (m + (j + 1) * (s + 1))) :=
          card_filter_equivFin_mem _ hU
      _ = A := by
          rw [card_union_of_disjoint (disjoint_left.mpr fun x hx hx' ↦ by
            have := mem_range.mp hx; have := mem_Ico.mp hx'; omega), card_range, Nat.card_Ico]
          rw [add_mul]
          omega
  refine ⟨f, g, hfar, fun α hα ↦ isScalarExceptional_of_forall_card_lt domain hfar
    (by simp) hα.ge, ?_⟩
  rw [← card_range k]
  refine card_le_card_of_injOn γ (fun j hj ↦ ?_) (hγ.mono ?_)
  · exact (mem_exactZeroChallenges_iff_card_polynomialAgreementSet domain f g A _).mpr
      (hcard j (mem_range.mp hj))
  · intro j hj
    simp only [coe_range, Set.mem_Iio] at hj ⊢
    have : k ≤ k * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- Let `n = |ι|` be the domain size and `q = |F|` the field size.

If `d + s + 1 < A ≤ n`, the scalar error at loss `s` is at least `(1 + ⌊(n - A)/(s + 1)⌋) / q`. -/
theorem le_scalarMcaError_of_degree_add_loss_add_one_lt [Fintype F] (domain : ι ↪ F) {d A s : ℕ}
    (hdA : d + s + 1 < A) (hAn : A ≤ Fintype.card ι) :
    ENNReal.ofReal (((1 + (Fintype.card ι - A) / (s + 1) : ℕ) : ℝ) /
        (Fintype.card F : ℝ)) ≤
      scalarMcaError domain d A s := by
  obtain ⟨f, g, hfar, -, hcount⟩ := exists_words_forall_isScalarExceptional_zero domain hdA hAn
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (le_scalarMcaError_of_forall_card_lt domain (f := f) hfar)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

end ReedSolomon
