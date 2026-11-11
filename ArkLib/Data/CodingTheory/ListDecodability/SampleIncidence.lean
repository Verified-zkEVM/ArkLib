/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.Finset.SampleIncidence

/-!
# Sample incidence for code agreement lists

This file applies the generic finite-set sample-incidence theorem to arbitrary codes.  It assumes
only that distinct codewords agree on fewer than `k` coordinates; the alphabet and the code may
both be infinite.
-/

@[expose] public section

namespace Code

open Classical in
/-- The complete absolute-agreement list of an arbitrary code is finite and satisfies the sharp
sample-incidence inequality whenever distinct codewords agree on fewer than `k` coordinates. -/
theorem agreement_set_finite_and_ncard_mul_choose_le
    {ι A : Type*} [Fintype ι] [DecidableEq A]
    (C : Set (ι → A)) (received : ι → A) (minAgreement k : ℕ)
    (hkA : k ≤ minAgreement)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → agree c c' < k) :
    {c | c ∈ C ∧ minAgreement ≤ agree c received}.Finite ∧
      {c | c ∈ C ∧ minAgreement ≤ agree c received}.ncard *
          minAgreement.choose k ≤ (Fintype.card ι).choose k := by
  let S : (ι → A) → Finset ι := fun c => Finset.univ.filter fun i => c i = received i
  apply Set.finite_and_ncard_mul_choose_le_of_inter_card_lt
    {c | c ∈ C ∧ minAgreement ≤ agree c received} S minAgreement k hkA
  · intro c hc
    simpa [S, agree] using hc.2
  · intro c hc c' hc' hne
    apply lt_of_le_of_lt ?_ (hpair c hc.1 c' hc'.1 hne)
    apply Finset.card_le_card
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
    simpa [agree] using hi'.1.trans hi'.2.symm

end Code
