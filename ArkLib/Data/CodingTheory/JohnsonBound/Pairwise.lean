/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.Data.Finset.PairwiseIntersection

/-!
# Pairwise Johnson bound for arbitrary codes

This file turns the elementary pairwise-intersection count into an exact integral list-size bound
for an arbitrary code over an arbitrary alphabet. Neither the alphabet nor the code is assumed
finite: finiteness of every point list follows from the uniform bound on its finite subsets.

If distinct codewords agree in at most `D` coordinates and every word in a finite family agrees
with a received word in at least `A` coordinates, then the family has cardinality at most

`⌊n(A - D) / (A² - nD)⌋`,

provided `D ≤ A` and `nD < A²`. The relative-radius statements use radius `1 - A / n` and handle
the formally possible case `A > n` by observing that the corresponding Hamming ball is empty.
-/

@[expose] public section

namespace Code

/-- The natural-number quotient in the pairwise Johnson expression.

This definition is total. The theorems using it assume `n * D < A * A`, which makes its
denominator positive. -/
def pairwiseJohnsonListBound (n D A : ℕ) : ℕ :=
  n * (A - D) / (A * A - n * D)

/-- Exact integral pairwise Johnson bound for a finite family of codewords.

The code and alphabet may be infinite. Every member of `T` belongs to `C` and agrees with the
received word in at least `A` coordinates; distinct codewords in `C` agree in at most `D`
coordinates. -/
theorem finset_card_le_pairwiseJohnson
    {ι alphabet : Type*} [Fintype ι] [DecidableEq alphabet]
    (C : Set (ι → alphabet)) (received : ι → alphabet) (D A : ℕ)
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → agree c c' ≤ D)
    (T : Finset (ι → alphabet))
    (hT : ∀ c ∈ T, c ∈ C ∧ A ≤ agree c received) :
    T.card ≤ pairwiseJohnsonListBound (Fintype.card ι) D A := by
  classical
  let S : (ι → alphabet) → Finset ι := fun c => Finset.univ.filter fun i => c i = received i
  have hclose : ∀ c ∈ T, A ≤ (S c).card := by
    intro c hc
    simpa [S, agree] using (hT c hc).2
  have hinter : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → ((S c) ∩ (S c')).card ≤ D := by
    intro c hc c' hc' hne
    calc
      ((S c) ∩ (S c')).card ≤ agree c c' := by
        apply Finset.card_le_card
        intro i hi
        simp only [S, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi.1.trans hi.2.symm
      _ ≤ D := hpair c (hT c hc).1 c' (hT c' hc').1 hne
  have hmul := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    T S A D hDA hpositive hclose hinter
  rw [pairwiseJohnsonListBound]
  exact (Nat.le_div_iff_mul_le (by omega : 0 < A * A - Fintype.card ι * D)).2 hmul

/-- The complete exact-agreement list is finite and satisfies the integral pairwise Johnson bound.

This formulation does not require a finite alphabet or a finite ambient code. -/
theorem agreementSet_finite_and_ncard_le_pairwiseJohnson
    {ι alphabet : Type*} [Fintype ι] [DecidableEq alphabet]
    (C : Set (ι → alphabet)) (received : ι → alphabet) (D A : ℕ)
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → agree c c' ≤ D) :
    {c | c ∈ C ∧ A ≤ agree c received}.Finite ∧
      {c | c ∈ C ∧ A ≤ agree c received}.ncard ≤
        pairwiseJohnsonListBound (Fintype.card ι) D A := by
  let L : Set (ι → alphabet) := {c | c ∈ C ∧ A ≤ agree c received}
  have hfinite : L.Finite := Set.finite_of_forall_finset_card_le (R := ℕ) fun T hsub =>
    finset_card_le_pairwiseJohnson C received D A hDA hpositive hpair T fun c hc => hsub hc
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact finset_card_le_pairwiseJohnson C received D A hDA hpositive hpair hfinite.toFinset
    fun c hc => hfinite.mem_toFinset.mp hc

/-- The exact integral pairwise Johnson bound controls `Code.Lambda` at relative radius
`1 - A / n`, for arbitrary alphabets and possibly infinite codes. -/
theorem Lambda_le_pairwiseJohnson
    {ι alphabet : Type*} [Fintype ι] [Nonempty ι] [DecidableEq alphabet]
    (C : Set (ι → alphabet)) (D A : ℕ)
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → agree c c' ≤ D) :
    Lambda C (1 - (A : ℝ) / Fintype.card ι) ≤
      (pairwiseJohnsonListBound (Fintype.card ι) D A : ℕ∞) := by
  apply Lambda_le_of_forall_finset_card_le
  intro received T hT
  apply finset_card_le_pairwiseJohnson C received D A hDA hpositive hpair T
  intro c hc
  have hmem := (mem_closeCodewordsRel_iff.mp (hT c hc))
  refine ⟨hmem.1, ?_⟩
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hdist := hmem.2
  rw [relHammingDist_coe] at hdist
  have hagree := agree_add_hammingDist (u := c) (v := received)
  have hcast : ((hammingDist received c : ℕ) : ℝ) = hammingDist c received := by
    rw [hammingDist_comm]
  rw [hcast] at hdist
  field_simp [ne_of_gt hnpos] at hdist
  have hagreeR : ((agree c received : ℕ) : ℝ) + hammingDist c received =
      Fintype.card ι := by
    exact_mod_cast hagree
  have hreal : (A : ℝ) ≤ agree c received := by nlinarith
  exact_mod_cast hreal

/-- An arbitrary code with the pairwise agreement hypothesis is list decodable at the exact
integral pairwise Johnson bound. -/
theorem isListDecodable_pairwiseJohnson
    {ι alphabet : Type*} [Fintype ι] [Nonempty ι] [DecidableEq alphabet]
    (C : Set (ι → alphabet)) (D A : ℕ)
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → agree c c' ≤ D) :
    IsListDecodable C (1 - (A : ℝ) / Fintype.card ι)
      ((pairwiseJohnsonListBound (Fintype.card ι) D A : ℕ) : NNReal) := by
  rw [isListDecodable_natCast_iff]
  exact Lambda_le_pairwiseJohnson C D A hDA hpositive hpair

end Code
