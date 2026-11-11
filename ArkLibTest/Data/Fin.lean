/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevaundray Wedderburn
-/

import ArkLib.Data.Fin.Basic

/-! `castSum` indexes summands by their value, not by an occurrence in the list.
Repeated summand sizes therefore cannot support unrestricted dependent elimination.
This counterexample records why the former admitted `Fin.sumCases` was removed. -/

namespace Fin

/-- With two summands of size one, every membership-indexed case sees index zero.
Such cases cannot construct a value at index one for an arbitrary motive. -/
theorem no_unrestricted_sumCases_for_duplicate_summands :
    ¬ (∀ (motive : Fin ([1, 1] : List ℕ).sum → Prop),
      (∀ (n : ℕ) (h : n ∈ ([1, 1] : List ℕ)) (i : Fin n),
        motive (castSum [1, 1] h i)) →
      ∀ i, motive i) := by
  intro h
  have hcases : ∀ (n : ℕ) (hn : n ∈ ([1, 1] : List ℕ)) (i : Fin n),
      (castSum [1, 1] hn i).val = 0 := by
    intro n hn i
    have hn1 : n = 1 := by simpa using hn
    subst n
    fin_cases i
    simp [castSum]
  have hfalse := h (fun i => i.val = 0) hcases ⟨1, by decide⟩
  exact Nat.one_ne_zero hfalse

end Fin

#print axioms Fin.no_unrestricted_sumCases_for_duplicate_summands
