/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon.PrimitiveRootDomain
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Large lists for Reed--Solomon codes on multiplicative subgroups

Let `ω` be a primitive `n`-th root of unity, `s ∣ n` and `N = n / s`. For `S ⊆ {1, …, N - 1}`
with `|S| = r`, put

* `R_S(Y) = ∏_{j ∈ S} (Y - ω^{s j})`, whose roots `Y = x ^ s` cut out `r` cosets of `μ_s`;
* `P_T(X) = ∏_{1 ≤ t < s} (X - ω^{N t})`, vanishing on `μ_s ∖ {1}`;
* the received word `w(x) = x ^ (n - s) · P_T(x) · (a + x ^ (s r))`;
* the codeword `g_S = P_T · expand s ((a + X ^ r - R_S) /ₘ X)`.

When `R_S(0) = a`, the polynomial `g_S` has degree `< s (r - 1)` and agrees with `w` on the
`s r + s - 1` points where `P_T(x) R_S(x ^ s) = 0`. The value `R_S(0)` depends only on
`(∑ S) mod N`, so a pigeonhole choice of `a` gives `⌊C(N - 1, r) / N⌋` distinct codewords of
`RS[F, (ωⁱ)ᵢ, k]` with agreement `s r + s - 1`, for every `k` with `s (r - 1) ≤ k ≤ s r + s - 1`.

## Main results

* `ReedSolomon.CosetList.big_list`: the list-size lower bound above.

## References

* [Kin26] for the coset construction on multiplicative subgroups.
-/

@[expose] public section

open Polynomial Finset

namespace ReedSolomon.CosetList

variable {F : Type} [Field F] {ω : F} {n : ℕ}

/-- The index set `{1, …, N - 1}`. -/
private def J (N : ℕ) : Finset ℕ := (range N).erase 0

/-- `P_T = ∏_{1 ≤ t < s} (X - ω^{N t})`. -/
private noncomputable def PT (ω : F) (N s : ℕ) : F[X] :=
  ∏ t ∈ Ico 1 s, (X - C (ω ^ (N * t)))

/-- `R_S = ∏_{j ∈ S} (X - ω^{s j})`. -/
private noncomputable def R (ω : F) (s : ℕ) (S : Finset ℕ) : F[X] :=
  ∏ j ∈ S, (X - C (ω ^ (s * j)))

/-- `a + X ^ r - R_S`. -/
private noncomputable def D (ω a : F) (s r : ℕ) (S : Finset ℕ) : F[X] :=
  C a + X ^ r - R ω s S

/-- The codeword polynomial `g_S = P_T · expand s ((a + X ^ r - R_S) /ₘ X)`. -/
private noncomputable def g (ω a : F) (N s r : ℕ) (S : Finset ℕ) : F[X] :=
  PT ω N s * expand F s (D ω a s r S /ₘ X)

/-- The received word `w(ωⁱ) = (ωⁱ) ^ (n - s) · P_T(ωⁱ) · (a + (ωⁱ) ^ (s r))`. -/
private noncomputable def word (ω a : F) (N s r : ℕ) (i : Fin n) : F :=
  (ω ^ (i : ℕ)) ^ (n - s) * (PT ω N s).eval (ω ^ (i : ℕ)) * (a + (ω ^ (i : ℕ)) ^ (s * r))

private theorem mem_J {N j : ℕ} : j ∈ J N ↔ j ≠ 0 ∧ j < N := by simp [J]

private theorem card_J (N : ℕ) : (J N).card = N - 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [J]
  · rw [J, card_erase_of_mem (mem_range.mpr hN), card_range]

private theorem R_monic {s : ℕ} (S : Finset ℕ) : (R ω s S).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

private theorem R_natDegree {s : ℕ} (S : Finset ℕ) : (R ω s S).natDegree = S.card := by
  rw [R, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

private theorem PT_monic {N s : ℕ} : (PT ω N s).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

private theorem PT_natDegree {N s : ℕ} : (PT ω N s).natDegree = s - 1 := by
  rw [PT, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, Nat.card_Ico]

private theorem D_degree_lt (a : F) {s r : ℕ} {S : Finset ℕ} (hS : S.card = r) (hr : 1 ≤ r) :
    (D ω a s r S).degree < r := by
  have hR : (R ω s S).degree = (r : WithBot ℕ) := by
    rw [degree_eq_natDegree (R_monic S).ne_zero, R_natDegree, hS]
  have h1 : (X ^ r - R ω s S : F[X]).degree < (r : WithBot ℕ) := by
    have := degree_sub_lt_left (p := (X ^ r : F[X])) (q := R ω s S)
      (by rw [degree_X_pow, hR]) (pow_ne_zero _ X_ne_zero)
      (by rw [leadingCoeff_X_pow, (R_monic S).leadingCoeff])
    rwa [degree_X_pow] at this
  calc (D ω a s r S).degree = (C a + (X ^ r - R ω s S)).degree := by rw [D, add_sub_assoc]
    _ ≤ max (C a).degree (X ^ r - R ω s S).degree := degree_add_le _ _
    _ < r := max_lt (lt_of_le_of_lt degree_C_le (by exact_mod_cast (show 0 < r by omega))) h1

private theorem X_mul_div {a : F} {s r : ℕ} {S : Finset ℕ} (h0 : (D ω a s r S).eval 0 = 0) :
    X * (D ω a s r S /ₘ X) = D ω a s r S := by
  have h := mul_divByMonic_eq_iff_isRoot.mpr (show IsRoot (D ω a s r S) 0 from h0)
  simpa using h

/-- `g_S` has degree `< k` as soon as `s (r - 1) ≤ k`. For `r = 1` the quotient vanishes and
`g_S = 0`. -/
private theorem g_degree_lt (a : F) {N s r k : ℕ} {S : Finset ℕ} (hs : 0 < s) (hS : S.card = r)
    (hr : 1 ≤ r) (hdeg : s * (r - 1) ≤ k) : (g ω a N s r S).degree < k := by
  by_cases hQ0 : D ω a s r S /ₘ X = 0
  · simp [g, hQ0]
  have hD0 : D ω a s r S ≠ 0 := by
    intro h; apply hQ0; rw [h, zero_divByMonic]
  have hD : (D ω a s r S).natDegree ≤ r - 1 := by
    have := (natDegree_lt_iff_degree_lt hD0).mpr (D_degree_lt a hS hr)
    omega
  have hDpos : 1 ≤ (D ω a s r S).natDegree := by
    by_contra hlt
    apply hQ0
    rw [divByMonic_eq_zero_iff monic_X, degree_X]
    exact degree_le_natDegree.trans_lt
      (by exact_mod_cast (show (D ω a s r S).natDegree < 1 by omega))
  have hQ : (D ω a s r S /ₘ X).natDegree = (D ω a s r S).natDegree - 1 := by
    rw [natDegree_divByMonic _ monic_X, natDegree_X]
  have hE : (expand F s (D ω a s r S /ₘ X)).natDegree ≤ s * (r - 2) := by
    rw [natDegree_expand, hQ]
    exact (mul_comm _ _).trans_le (Nat.mul_le_mul (le_refl s) (by omega))
  have hsplit : s * (r - 1) = s * (r - 2) + s := by
    rw [show r - 1 = (r - 2) + 1 by omega, mul_add, mul_one]
  have key : s * (r - 2) + s ≤ k := by rw [← hsplit]; exact hdeg
  generalize s * (r - 2) = M at hE key
  have hg : (g ω a N s r S).natDegree < k := by
    calc (g ω a N s r S).natDegree
        ≤ (PT ω N s).natDegree + (expand F s (D ω a s r S /ₘ X)).natDegree := natDegree_mul_le
      _ < k := by rw [PT_natDegree]; omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hg)

/-- The key identity: if `P_T(x) · R_S(x ^ s) = 0` and `x ^ n = 1`, then `g_S(x) = w(x)`. -/
private theorem eval_agree {a : F} {N s r : ℕ} {S : Finset ℕ} (hsn : s ≤ n)
    (h0 : (D ω a s r S).eval 0 = 0) {x : F} (hx : x ^ n = 1)
    (hz : (PT ω N s).eval x * (R ω s S).eval (x ^ s) = 0) :
    (g ω a N s r S).eval x = x ^ (n - s) * (PT ω N s).eval x * (a + x ^ (s * r)) := by
  have hD := congrArg (eval (x ^ s)) (X_mul_div h0)
  have hDv : (D ω a s r S).eval (x ^ s) = a + (x ^ s) ^ r - (R ω s S).eval (x ^ s) := by
    simp only [D, eval_add, eval_sub, eval_C, eval_pow, eval_X]
  rw [eval_mul, eval_X, hDv, ← pow_mul] at hD
  have hxn : x ^ (n - s) * x ^ s = x ^ n := by rw [← pow_add, Nat.sub_add_cancel hsn]
  simp only [g, eval_mul, expand_eval]
  linear_combination (x ^ (n - s) * (PT ω N s).eval x) * hD
    - ((PT ω N s).eval x * (D ω a s r S /ₘ X).eval (x ^ s)) * hxn
    - ((PT ω N s).eval x * (D ω a s r S /ₘ X).eval (x ^ s)) * hx - x ^ (n - s) * hz

private theorem R_eval_eq_zero_iff (hω : IsPrimitiveRoot ω n) {N s : ℕ} (hs : 0 < s)
    (hsN : s * N = n)
    {S : Finset ℕ} (hSJ : S ⊆ J N) {j : ℕ} (hj : j ∈ J N) :
    (R ω s S).eval (ω ^ (s * j)) = 0 ↔ j ∈ S := by
  rw [R, eval_prod, prod_eq_zero_iff]
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨j', hj', h⟩
    have hjl := (mem_J.mp hj).2
    have hj'l := (mem_J.mp (hSJ hj')).2
    have h1 := Nat.mul_le_mul (le_refl s) (show j + 1 ≤ N by omega)
    have h2 := Nat.mul_le_mul (le_refl s) (show j' + 1 ≤ N by omega)
    rw [mul_add, mul_one] at h1 h2
    have := hω.pow_inj (by omega) (by omega) h
    have : j = j' := Nat.eq_of_mul_eq_mul_left hs this
    exact this ▸ hj'
  · intro h; exact ⟨j, h, rfl⟩

private theorem R_eval_zero (hω : IsPrimitiveRoot ω n) {N s r : ℕ} (hsN : s * N = n)
    {S : Finset ℕ} (hS : S.card = r) :
    (R ω s S).eval 0 = (-1) ^ r * (ω ^ s) ^ ((∑ j ∈ S, j) % N) := by
  have hN : (ω ^ s) ^ N = 1 := by rw [← pow_mul, hsN]; exact hω.pow_eq_one
  rw [R, eval_prod]
  have hfac : ∀ j ∈ S, eval 0 (X - C (ω ^ (s * j))) = (-1) * (ω ^ s) ^ j := by
    intro j _
    rw [eval_sub, eval_X, eval_C, zero_sub, pow_mul, neg_one_mul]
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, hS, prod_pow_eq_pow_sum,
    pow_eq_pow_mod _ hN]

/-- `big_list` with `N = n / s` as a parameter. -/
private theorem big_list_of_mul_eq (hω : IsPrimitiveRoot ω n) {N s r k : ℕ} (hn : 0 < n)
    (hs : 0 < s) (hsN : s * N = n) (hr : 1 ≤ r) (hdeg : s * (r - 1) ≤ k)
    (hkA : k ≤ s * r + s - 1) :
    ∃ w : Fin n → F, ((Nat.choose (N - 1) r / N : ℕ) : ℕ∞) ≤
      (Code.closeCodewordsRel (ReedSolomon.code (primitiveRootDomain hω) k : Set (Fin n → F)) w
        (((n : ℝ) - (s * r + s - 1 : ℕ)) / n)).encard := by
  classical
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · omega
    · exact h
  have hsn : s ≤ n := by
    have := Nat.mul_le_mul (le_refl s) (show 1 ≤ N from hNpos)
    rwa [mul_one, hsN] at this
  obtain ⟨y, -, hy⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := (J N).powersetCard r) (t := range N) (f := fun S ↦ (∑ j ∈ S, j) % N)
    (n := Nat.choose (N - 1) r / N)
    (fun S _ ↦ mem_range.mpr (Nat.mod_lt _ hNpos)) ⟨0, mem_range.mpr hNpos⟩
    (by rw [card_powersetCard, card_J, card_range]; exact Nat.mul_div_le _ _)
  set 𝒮 := ((J N).powersetCard r).filter fun S ↦ (∑ j ∈ S, j) % N = y with h𝒮
  set a : F := (-1) ^ r * (ω ^ s) ^ y with ha
  have hmem : ∀ S ∈ 𝒮, S ⊆ J N ∧ S.card = r ∧ (D ω a s r S).eval 0 = 0 := by
    intro S hS
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    obtain ⟨hSJ, hSc⟩ := mem_powersetCard.mp hS1
    refine ⟨hSJ, hSc, ?_⟩
    simp only [D, eval_sub, eval_add, eval_C, eval_pow, eval_X, R_eval_zero hω hsN hSc, hS2, ha,
      zero_pow (show r ≠ 0 by omega)]
    ring
  refine ⟨word ω a N s r, ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set A : ℕ := s * r + s - 1 with hA
  have hdelta : (0 : ℝ) ≤ ((A : ℝ) - k) / n := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    rw [sub_nonneg]; exact_mod_cast hkA
  have hrad : capacityRadius (((A : ℝ) - k) / n) (Fintype.card (Fin n)) k =
      ((n : ℝ) - (A : ℕ)) / n := by
    simp only [capacityRadius, Fintype.card_fin]
    rw [show (1 : ℝ) = n / n from (div_self hn0).symm, div_sub_div_same, div_sub_div_same]
    congr 1
    ring
  have hthr : capacityAgreementThreshold (((A : ℝ) - k) / n) (Fintype.card (Fin n)) k = A := by
    simp only [capacityAgreementThreshold, Fintype.card_fin]
    rw [div_mul_cancel₀ _ hn0, ← Nat.cast_sub hkA, Nat.ceil_natCast]
    omega
  rw [← hrad, closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta (by simpa using hn),
    hthr]
  let φ : Finset ℕ → (Fin n → F) := fun S ↦
    ReedSolomon.evalOnPoints (primitiveRootDomain hω) (g ω a N s r S)
  have hinj : Set.InjOn φ (𝒮 : Set (Finset ℕ)) := by
    intro S hS S' hS' heq
    obtain ⟨hSJ, hSc, h0⟩ := hmem S hS
    obtain ⟨hSJ', hSc', h0'⟩ := hmem S' hS'
    have hg : g ω a N s r S = g ω a N s r S' := by
      apply eq_of_degree_sub_lt_of_eval_finset_eq (univ.map (primitiveRootDomain hω))
      · rw [card_map, card_univ, Fintype.card_fin]
        calc (g ω a N s r S - g ω a N s r S').degree
            ≤ max (g ω a N s r S).degree (g ω a N s r S').degree := degree_sub_le _ _
          _ < k := max_lt (g_degree_lt a hs hSc hr hdeg) (g_degree_lt a hs hSc' hr hdeg)
          _ ≤ n := by exact_mod_cast (show k ≤ n by
                have := Nat.mul_le_mul (le_refl s) (show r + 1 ≤ N by
                  have := card_le_card hSJ
                  rw [card_J, hSc] at this
                  omega)
                rw [hsN, mul_add, mul_one] at this
                omega)
      · intro x hx
        obtain ⟨i, -, rfl⟩ := mem_map.mp hx
        exact congrFun heq i
    have hE : expand F s (D ω a s r S /ₘ X) = expand F s (D ω a s r S' /ₘ X) :=
      mul_left_cancel₀ PT_monic.ne_zero hg
    have hQ := expand_injective hs hE
    have hDD : D ω a s r S = D ω a s r S' := by rw [← X_mul_div h0, ← X_mul_div h0', hQ]
    have hR : R ω s S = R ω s S' := by
      simp only [D] at hDD; exact sub_right_injective hDD
    ext j
    by_cases hj : j ∈ J N
    · rw [← R_eval_eq_zero_iff hω hs hsN hSJ hj, ← R_eval_eq_zero_iff hω hs hsN hSJ' hj, hR]
    · exact ⟨fun h ↦ absurd (hSJ h) hj, fun h ↦ absurd (hSJ' h) hj⟩
  have hsub : φ '' (𝒮 : Set (Finset ℕ)) ⊆
      (fun p : ListDecoding.MessagePolynomial F k ↦
        ReedSolomon.evalOnPoints (primitiveRootDomain hω) p) ''
        agreeingPolynomials (primitiveRootDomain hω) k A (word ω a N s r) := by
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨hSJ, hSc, h0⟩ := hmem S hS
    refine ⟨⟨g ω a N s r S, mem_degreeLT.mpr (g_degree_lt a hs hSc hr hdeg)⟩, ?_, rfl⟩
    change A ≤ Code.agree (ReedSolomon.evalOnPoints (primitiveRootDomain hω) (g ω a N s r S))
      (word ω a N s r)
    let pts : Finset (ℕ × ℕ) := (S ×ˢ range s) ∪ ({0} ×ˢ Ico 1 s)
    have hdisj : Disjoint (S ×ˢ range s) ({0} ×ˢ Ico 1 s) := by
      rw [disjoint_left]
      intro p hp hp'
      have h1 := (mem_product.mp hp).1
      have h2 := (mem_product.mp hp').1
      rw [mem_singleton] at h2
      exact (mem_J.mp (hSJ h1)).1 h2
    have hcard : pts.card = A := by
      rw [card_union_of_disjoint hdisj, card_product, card_product, hSc, card_range,
        card_singleton, Nat.card_Ico, hA, mul_comm r s]
      omega
    have hbound : ∀ p ∈ pts, p.1 < N ∧ p.2 < s := by
      intro p hp
      rcases mem_union.mp hp with h | h
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        exact ⟨(mem_J.mp (hSJ h1)).2, mem_range.mp h2⟩
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        rw [mem_singleton] at h1
        rw [mem_Ico] at h2
        exact ⟨by omega, h2.2⟩
    have hlt : ∀ p ∈ pts, p.1 + N * p.2 < n := by
      intro p hp
      obtain ⟨h1, h2⟩ := hbound p hp
      have := Nat.mul_le_mul (le_refl N) (show p.2 + 1 ≤ s by omega)
      rw [mul_add, mul_one, mul_comm N s, hsN] at this
      omega
    let f : ℕ × ℕ → Fin n := fun p ↦ ⟨(p.1 + N * p.2) % n, Nat.mod_lt _ hn⟩
    have hfval : ∀ p ∈ pts, ((f p : Fin n) : ℕ) = p.1 + N * p.2 := fun p hp ↦
      Nat.mod_eq_of_lt (hlt p hp)
    rw [← hcard]
    unfold Code.agree
    refine card_le_card_of_injOn f ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      have hv := hfval p hp
      change (g ω a N s r S).eval (ω ^ ((f p : Fin n) : ℕ)) = word ω a N s r (f p)
      simp only [word]
      rw [hv]
      have hx : (ω ^ (p.1 + N * p.2)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
      refine eval_agree hsn h0 hx ?_
      rcases mem_union.mp hp with h | h
      · obtain ⟨h1, -⟩ := mem_product.mp h
        have h4 : (ω ^ (p.1 + N * p.2)) ^ s = ω ^ (s * p.1) := by
          rw [← pow_mul, show (p.1 + N * p.2) * s = s * p.1 + (s * N) * p.2 by ring, hsN,
            pow_add, pow_mul ω n p.2, hω.pow_eq_one, one_pow, mul_one]
        rw [h4, (R_eval_eq_zero_iff hω hs hsN hSJ (hSJ h1)).mpr h1, mul_zero]
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        rw [mem_singleton] at h1
        have hPT : (PT ω N s).eval (ω ^ (p.1 + N * p.2)) = 0 := by
          rw [PT, eval_prod, prod_eq_zero_iff]
          refine ⟨p.2, h2, ?_⟩
          simp only [eval_sub, eval_X, eval_C, h1, zero_add, sub_self]
        rw [hPT, zero_mul]
    · intro p hp q hq hpq
      have h1 := hfval p hp
      have h2 := hfval q hq
      have hb1 := hbound p hp
      have hb2 := hbound q hq
      have heq : p.1 + N * p.2 = q.1 + N * q.2 := by rw [← h1, ← h2, hpq]
      have e1 : p.1 = q.1 := by
        have h := congrArg (· % N) heq
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb1.1,
          Nat.mod_eq_of_lt hb2.1] at h
        exact h
      have e2 : p.2 = q.2 := by
        have h := congrArg (· / N) heq
        simp only [Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hb1.1,
          Nat.div_eq_of_lt hb2.1, zero_add] at h
        exact h
      exact Prod.ext e1 e2
  calc ((Nat.choose (N - 1) r / N : ℕ) : ℕ∞) ≤ (𝒮.card : ℕ∞) := by exact_mod_cast hy
    _ = (φ '' (𝒮 : Set (Finset ℕ))).encard := by
        rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard]
    _ ≤ _ := Set.encard_mono hsub

/-- There is a received word with at least `⌊C(n / s - 1, r) / (n / s)⌋` codewords of
`RS[F, (ωⁱ)ᵢ, k]` within relative distance `(n - (s r + s - 1)) / n`, whenever `s ∣ n`,
`1 ≤ r` and `s (r - 1) ≤ k ≤ s r + s - 1`. -/
theorem big_list (hω : IsPrimitiveRoot ω n) {s r k : ℕ}
    (hs : 0 < s) (hsn : s ∣ n)
    (hr : 1 ≤ r) (hdeg : s * (r - 1) ≤ k)
    (hkA : k ≤ s * r + s - 1) :
    ∃ w : Fin n → F,
      ((Nat.choose (n / s - 1) r / (n / s) : ℕ) : ℕ∞) ≤
        (Code.closeCodewordsRel
          (ReedSolomon.code (primitiveRootDomain hω) k : Set (Fin n → F)) w
          (((n : ℝ) - (s * r + s - 1 : ℕ)) / n)).encard := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  exact big_list_of_mul_eq hω hn hs (Nat.mul_div_cancel' hsn) hr hdeg hkA

end ReedSolomon.CosetList
