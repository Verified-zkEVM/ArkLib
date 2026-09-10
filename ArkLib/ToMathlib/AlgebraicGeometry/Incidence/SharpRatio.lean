/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement

/-!
# The coupled good-cut incidence ratio

Keeping the number of identically vanishing cuts in both numerator and denominator
gives the sharp ratio used by the finite agreement incidence induction.
-/

@[expose] public section

namespace AffineHilbert

/-- If fewer than `k` of `n` cuts vanish identically, the ratio of remaining cuts to
remaining agreements is maximized when exactly `k-1` cuts vanish identically. -/
theorem goodCuts_div_agreements_le
    {n A k m : ℕ} (hmk : m < k) (hkA : k ≤ A) (hAn : A ≤ n) :
    ((n - m : ℕ) : ℚ) / ((A - m : ℕ) : ℚ) ≤
      ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hmA : m ≤ A := (Nat.le_of_lt hmk).trans hkA
  have hmn : m ≤ n := hmA.trans hAn
  have hk1A : k - 1 ≤ A := (Nat.sub_le k 1).trans hkA
  have hk1n : k - 1 ≤ n := hk1A.trans hAn
  have hden : (0 : ℚ) < (A - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt (hmk.trans_le hkA)
  have hden' : (0 : ℚ) < (A - k + 1 : ℕ) := by positivity
  rw [div_le_div_iff₀ hden hden']
  rw [Nat.cast_sub hmn, Nat.cast_sub hmA]
  have hkpos : 0 < k := Nat.zero_lt_of_lt hmk
  rw [show n - k + 1 = n - (k - 1) by omega,
    show A - k + 1 = A - (k - 1) by omega,
    Nat.cast_sub hk1n, Nat.cast_sub hk1A]
  have hmk1q : (m : ℚ) ≤ (k - 1 : ℕ) := by exact_mod_cast (show m ≤ k - 1 by omega)
  have hAnq : (A : ℚ) ≤ n := by exact_mod_cast hAn
  nlinarith

/-- Exact bipartite-incidence lower bound retaining the actual number of bad cuts. -/
theorem finiteAgreementIncidence_lower_sharp {X : Type*} {n A : ℕ}
    (S : Finset X) (Bad : Finset (Fin n)) (zero : X → Fin n → Prop)
    [∀ x i, Decidable (zero x i)]
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter (zero x)).card) :
    S.card * (A - Bad.card) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ Bad), (S.filter fun x ↦ zero x i).card := by
  classical
  let good : Finset (Fin n) := Finset.univ.filter (fun i ↦ i ∉ Bad)
  have hpoint : ∀ x ∈ S, A - Bad.card ≤ (good.filter (zero x)).card := by
    intro x hx
    have hcover := Finset.card_le_card_sdiff_add_card
      (s := Finset.univ.filter (zero x)) (t := Bad)
    have heq : (Finset.univ.filter (zero x)) \ Bad = good.filter (zero x) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, good]
      tauto
    rw [heq] at hcover
    have := hA x hx
    omega
  calc
    S.card * (A - Bad.card) = ∑ _x ∈ S, (A - Bad.card) := by simp
    _ ≤ ∑ x ∈ S, (good.filter (zero x)).card := Finset.sum_le_sum hpoint
    _ = ∑ i ∈ good, (S.filter fun x ↦ zero x i).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow zero
        (s := S) (t := good)

end AffineHilbert
