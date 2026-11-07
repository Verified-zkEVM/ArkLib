/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.NotRare
public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.SecondMoment

/-!
# Random linear codes contain bad lists

Suppose that the bad distribution is not `β`-implicitly rare for some `β > 1 - ρ`. Take a
uniformly random `k`-dimensional code of rate at least `ρ`. Except with probability `q^{-c n}`,
it contains `L` independent codewords in one Hamming ball of radius `⌊δ n⌋`.
With the parameter choice `exists_rate_margin`, this gives
`CodingTheory.random_linear_lambda_lower`, which is [GLMRSW22], Theorem 4.1.

## Main statements

* `CodingTheory.RandomLinearInternal.exists_rate_margin`: the choice of `γ`.
* `CodingTheory.RandomLinearInternal.random_linear_contains_list`: the counting bound.

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Code

/-- With `h = H_q(δ)` and `γ = min (h/(L₀+1)) ((1-h)/2)`, every rate `ρ ∈ (1 - h - γ, 1 - h)` is
positive, the list size `L = ⌊h/(1 - h - ρ) - ε⌋` is at least `L₀`, and
`1 - ρ < h + h/(L + ε/2)`. -/
theorem exists_rate_margin (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 - 1 / q)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (L₀ : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
      0 < ρ ∧ L₀ ≤ Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) ∧
      1 - ρ < qEntropy q δ + qEntropy q δ /
        ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) + ε / 2) := by
  set h := qEntropy q δ with hh
  have hh0 : 0 < h := qEntropy_pos hq hδ0 (by
    have : (0 : ℝ) < 1 / q := by positivity
    linarith)
  have hh1 : h < 1 := qEntropy_lt_one hq hδ0.le hδ1
  have hL : (0 : ℝ) < (L₀ : ℝ) + 1 := by positivity
  refine ⟨min (h / (L₀ + 1)) ((1 - h) / 2), lt_min (by positivity) (by linarith), ?_⟩
  intro ρ hρ1 hρ2
  have hγ1 : min (h / (L₀ + 1)) ((1 - h) / 2) ≤ h / (L₀ + 1) := min_le_left _ _
  have hγ2 : min (h / (L₀ + 1)) ((1 - h) / 2) ≤ (1 - h) / 2 := min_le_right _ _
  set d := 1 - h - ρ with hd
  have hd0 : 0 < d := by linarith
  have hdγ : d < h / (L₀ + 1) := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hlow : (L₀ : ℝ) + 1 < h / d := by
    rw [lt_div_iff₀ hd0]
    rw [lt_div_iff₀ hL] at hdγ
    linarith
  have hf : (L₀ : ℝ) ≤ h / d - ε := by linarith
  refine ⟨hρ0, Nat.le_floor hf, ?_⟩
  set f := Nat.floor (h / d - ε) with hfdef
  have hfle : (f : ℝ) ≤ h / d - ε := Nat.floor_le (by linarith)
  have hpos : (0 : ℝ) < (f : ℝ) + ε / 2 := by positivity
  have hlt : (f : ℝ) + ε / 2 < h / d := by linarith
  have : d < h / ((f : ℝ) + ε / 2) := by
    rw [lt_div_iff₀ hpos]
    rw [lt_div_iff₀ hd0] at hlt
    linarith
  linarith

/-- Polynomial factors are absorbed by an exponential margin. -/
theorem exists_mul_poly_rpow_le (q K : ℕ) (hq : 2 ≤ q) (a c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      a * (Real.exp 1 * (n + 1)) ^ K * (q : ℝ) ^ (-(3 * c * n)) ≤ (q : ℝ) ^ (-(c * n)) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set r : ℝ := (q : ℝ) ^ (-(2 * c)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one K
    (r := r) (by rw [abs_of_pos hr0]; exact hr1)).comp (Filter.tendsto_add_atTop_nat 1)
  set C : ℝ := |a| * Real.exp 1 ^ K + 1 with hC
  have hC0 : 0 < C := by positivity
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < r / C by positivity)))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 := hn₀ n hn
  simp only [Function.comp] at h1
  have hrn : r ^ n = (q : ℝ) ^ (-(2 * c * n)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; ring_nf
  have h3 : C * (((n : ℝ) + 1) ^ K * r ^ n) < 1 := by
    have : ((n : ℝ) + 1) ^ K * (r ^ n * r) < r / C := by
      push_cast at h1; rw [pow_succ] at h1; exact h1
    rw [lt_div_iff₀ hC0] at this
    have h4 : (C * (((n : ℝ) + 1) ^ K * r ^ n)) * r < 1 * r := by nlinarith
    exact lt_of_mul_lt_mul_right h4 hr0.le
  have hsplit : (q : ℝ) ^ (-(3 * c * n)) = (q : ℝ) ^ (-(c * n)) * r ^ n := by
    rw [hrn, ← Real.rpow_add hq0]; ring_nf
  have hpos : 0 < (q : ℝ) ^ (-(c * n)) := Real.rpow_pos_of_pos hq0 _
  have hE : (Real.exp 1 * ((n : ℝ) + 1)) ^ K = Real.exp 1 ^ K * ((n : ℝ) + 1) ^ K := mul_pow _ _ _
  have hle : |a| * Real.exp 1 ^ K ≤ C := by rw [hC]; linarith
  have hP : 0 ≤ ((n : ℝ) + 1) ^ K * r ^ n := by positivity
  calc a * (Real.exp 1 * ((n : ℝ) + 1)) ^ K * (q : ℝ) ^ (-(3 * c * n))
      ≤ |a| * (Real.exp 1 * ((n : ℝ) + 1)) ^ K * (q : ℝ) ^ (-(3 * c * n)) := by
        gcongr; exact le_abs_self a
    _ = (|a| * Real.exp 1 ^ K * (((n : ℝ) + 1) ^ K * r ^ n)) * (q : ℝ) ^ (-(c * n)) := by
        rw [hsplit, hE]; ring
    _ ≤ (C * (((n : ℝ) + 1) ^ K * r ^ n)) * (q : ℝ) ^ (-(c * n)) := by gcongr
    _ ≤ 1 * (q : ℝ) ^ (-(c * n)) := by gcongr
    _ = _ := one_mul _

/-- Let `1 - ρ < β`, and let every full-rank image `A (u + α · 1_L)` with `s` rows have entropy
at least `s β` under the bad distribution. Then at most a fraction `q^{-c n}` of the
`k`-dimensional codes with `k ≥ ρ n` have `Λ(C, δ) < L`. -/
theorem random_linear_contains_list (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 - 1 / q) (L : ℕ) (β : ℝ)
    (hent : ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F], Fintype.card F = q →
      ∀ s : ℕ, 1 ≤ s → ∀ A : Matrix (Fin s) (Fin L) F, LinearIndependent F A →
        (s : ℝ) * β ≤ entQ q (badLaw q δ L F) (fun ω => A.mulVec (badRow ω)))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hβρ : 1 - ρ < β) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F],
        Fintype.card F = q → n₀ ≤ Fintype.card ι → ∀ k : ℕ, ρ ≤ (k : ℝ) / Fintype.card ι →
        (({C : Submodule F (ι → F) | Module.finrank F C = k ∧
            Code.Lambda ((C : Set (ι → F))) δ < ((L : ℕ) : ℕ∞)}.ncard : ℝ))
          ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) *
            (({C : Submodule F (ι → F) | Module.finrank F C = k}.ncard : ℝ)) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = (β - (1 - ρ)) / 4 := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; linarith
  obtain ⟨n₁, hn₁⟩ := exists_badMatrix q hq δ hδ0 hδ1 L c₀ hc₀0
  obtain ⟨n₂, hn₂⟩ := exists_mul_poly_rpow_le q (q ^ L) hq (2 * L * (q : ℝ) ^ (2 * L ^ 2)) c₀ hc₀0
  refine ⟨c₀, hc₀0, max n₁ n₂, ?_⟩
  intro ι _ _ _ F _ _ _ hF hn k hk
  have hn1 : n₁ ≤ Fintype.card ι := le_trans (le_max_left _ _) hn
  have hn2 : n₂ ≤ Fintype.card ι := le_trans (le_max_right _ _) hn
  have hFq : (Fintype.card F : ℝ) = q := by exact_mod_cast hF
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hkρ : ρ * Fintype.card ι ≤ k := by rwa [le_div_iff₀ hnpos] at hk
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    subst h0
    simp at hkρ
    nlinarith
  by_cases hkn : Fintype.card ι < k
  · have hE : ∀ C : Submodule F (ι → F), Module.finrank F C ≠ k := by
      intro C hC
      have := Submodule.finrank_le C
      rw [Module.finrank_fintype_fun_eq_card] at this
      omega
    have h1 : {C : Submodule F (ι → F) | Module.finrank F C = k ∧
        Code.Lambda ((C : Set (ι → F))) δ < ((L : ℕ) : ℕ∞)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun C hC => hE C hC.1
    have h2 : {C : Submodule F (ι → F) | Module.finrank F C = k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun C hC => hE C hC
    rw [h1, h2]
    simp
  replace hkn := not_lt.1 hkn
  obtain ⟨m, hkm⟩ : ∃ m, k + m = Fintype.card ι := ⟨Fintype.card ι - k, by omega⟩
  have hmρ : (m : ℝ) ≤ (1 - ρ) * Fintype.card ι := by
    have : ((k + m : ℕ) : ℝ) = Fintype.card ι := by exact_mod_cast hkm
    push_cast at this
    nlinarith
  obtain ⟨M₀, ⟨z, hz⟩, hli, horb⟩ := hn₁ hF hn1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (Real.exp 1 * (Fintype.card ι + 1)) ^ (q ^ L) := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPdef]; positivity
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (q : ℝ) ^ (3 * c₀ * Fintype.card ι) / P := ⟨_, rfl⟩
  have hR : 0 < R := by
    rw [hRdef]
    have := Real.rpow_pos_of_pos hq0 (3 * c₀ * Fintype.card ι)
    positivity
  have hrare : ∀ s : ℕ, 1 ≤ s → ∀ A : Matrix (Fin s) (Fin L) F, LinearIndependent F A →
      R * (Fintype.card F : ℝ) ^ (m * s) ≤ (rowOrbit (fun j => A.mulVec (M₀ j))).ncard := by
    intro s hs A hA
    have h1 := horb s hs A hA
    have h2 := hent hF s hs A hA
    rw [← hPdef] at h1
    rw [hFq, hRdef, div_mul_eq_mul_div, div_le_iff₀ hP]
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hms : (m : ℝ) * s ≤ (1 - ρ) * Fintype.card ι * s :=
      mul_le_mul_of_nonneg_right hmρ (by positivity)
    have hnE := mul_le_mul_of_nonneg_left h2 hnpos.le
    have hx := mul_nonneg (mul_nonneg (sub_nonneg.2 hs') hnpos.le) hc₀0.le
    have hexp : 3 * c₀ * Fintype.card ι + ((m * s : ℕ) : ℝ) ≤
        (Fintype.card ι : ℝ) * (entQ q (badLaw q δ L F)
          (fun ω => A.mulVec (badRow ω)) - c₀) := by
      push_cast
      have : β = 4 * c₀ + (1 - ρ) := by rw [hc₀def]; ring
      rw [this] at hnE
      nlinarith
    calc (q : ℝ) ^ (3 * c₀ * Fintype.card ι) * (q : ℝ) ^ (m * s)
        = (q : ℝ) ^ (3 * c₀ * Fintype.card ι + ((m * s : ℕ) : ℝ)) := by
          rw [Real.rpow_add hq0, Real.rpow_natCast]
      _ ≤ (q : ℝ) ^ ((Fintype.card ι : ℝ) * (entQ q (badLaw q δ L F)
          (fun ω => A.mulVec (badRow ω)) - c₀)) :=
          Real.rpow_le_rpow_of_exponent_le hq1.le hexp
      _ ≤ _ := h1.trans_eq (mul_comm _ _)
  have hav := card_pc_avoid_le M₀ hli m R hR hrare
  have : Finite (Module.Dual F (ι → F)) := Module.finite_of_finite F
  have hsub : Nat.card {H : Fin m → Module.Dual F (ι → F) //
      Code.Lambda ((pcCode m H : Submodule F (ι → F)) : Set (ι → F)) δ < ((L : ℕ) : ℕ∞)} ≤
      Nat.card {H : Fin m → Module.Dual F (ι → F) //
        ∀ M ∈ rowOrbit M₀, ¬ ∀ i, cols M i ∈ pcCode m H} := by
    refine Nat.card_le_card_of_injective (fun H => ⟨H.1, ?_⟩) ?_
    · intro M hM hall
      obtain ⟨z', hz'⟩ := exists_center_of_mem_rowOrbit hM _ z hz
      have := lambda_ge_of_contains δ hδ0.le (pcCode m H.1) M
        (linearIndependent_cols_of_mem_rowOrbit hM hli) hall z' hz'
      exact absurd (lt_of_le_of_lt this H.2) (lt_irrefl _)
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext this
  have htr := ncard_subspace_le_of_pc (F := F) (ι := ι)
    (fun C => Code.Lambda ((C : Set (ι → F))) δ < ((L : ℕ) : ℕ∞)) k m hkm hk1
  have hqn : (0 : ℝ) < (Fintype.card F : ℝ) ^ (Fintype.card ι * m) := by rw [hFq]; positivity
  have habs := hn₂ _ hn2
  rw [← hPdef] at habs
  have hA : ((Nat.card {H : Fin m → Module.Dual F (ι → F) //
      Code.Lambda ((pcCode m H : Submodule F (ι → F)) : Set (ι → F)) δ < ((L : ℕ) : ℕ∞)} : ℕ) : ℝ)
      / (Fintype.card F : ℝ) ^ (Fintype.card ι * m) ≤ (L : ℝ) * (q : ℝ) ^ (2 * L ^ 2) / R := by
    rw [div_le_iff₀ hqn]
    have h3 : ((Nat.card {H : Fin m → Module.Dual F (ι → F) //
      Code.Lambda ((pcCode m H : Submodule F (ι → F)) : Set (ι → F)) δ < ((L : ℕ) : ℕ∞)} : ℕ) : ℝ)
      ≤ _ := Nat.cast_le.2 hsub
    rw [hFq] at hav ⊢
    exact h3.trans hav
  have hkey : 2 * ((L : ℝ) * (q : ℝ) ^ (2 * L ^ 2) / R) ≤ (q : ℝ) ^ (-(c₀ * Fintype.card ι)) := by
    refine le_trans (le_of_eq ?_) habs
    rw [hRdef, Real.rpow_neg hq0.le]
    field_simp
  have hN : (0 : ℝ) ≤ ({C : Submodule F (ι → F) | Module.finrank F C = k}.ncard : ℝ) := by
    positivity
  calc _ ≤ _ := htr
    _ ≤ (2 * ((L : ℝ) * (q : ℝ) ^ (2 * L ^ 2) / R)) *
        ({C : Submodule F (ι → F) | Module.finrank F C = k}.ncard : ℝ) := by
        gcongr
    _ ≤ _ := by gcongr

end CodingTheory.RandomLinearInternal
