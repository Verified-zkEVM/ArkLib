/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.Goldilocks512.Lower
public import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
public import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Unsafe-side grand-challenge witnesses for `RS[512, 128]` over Goldilocks cubic fields

Let `F` be a field with `|F| = p ^ 3`, `p = 2 ^ 64 - 2 ^ 32 + 1`, and let `ω` be a primitive
`512`-th root of unity in `F`. For the Reed--Solomon code `RS[F, (ωⁱ)ᵢ, 128]` at threshold
`ε* = 2⁻¹²⁸`, this file constructs

* `listUpperWitness`: a `ListUpperWitness` at `δ = 377/512` for every interleaving `m ≥ 1`;
* `mcaUpperWitness`: a `McaUpperWitness` at `δ = 377/512`.

Together with `Goldilocks512.Lower` this brackets both thresholds:
`273/512 ≤ δ* < 377/512`.

## The coset construction

For `S ⊆ {1, …, 127}` with `|S| = 33`, put

* `R_S(Y) = ∏_{j ∈ S} (Y - ω^{4j})`, whose roots `Y = x⁴` cut out `33` cosets of `μ₄`;
* `P_T(X) = ∏_{t ∈ {1, 2, 3}} (X - ω^{128 t})`;
* the received word `w(x) = x⁵⁰⁸ · P_T(x) · (a + x¹³²)`;
* the codeword `g_S = P_T · expand 4 ((a + X³³ - R_S) /ₘ X)`.

When `R_S(0) = a`, the polynomial `g_S` has degree `< 128` and agrees with `w` on the
`3 + 4 · 33 = 135` points where `P_T(x) R_S(x⁴) = 0`. The value `R_S(0)` depends only on
`(∑ S) mod 128`, so a pigeonhole choice of `a` yields at least `⌊C(127, 33) / 128⌋ ≈ 2 ^ 94.3`
distinct codewords at agreement `135 = 512 - 377`, which exceeds `p ³ / 2 ¹²⁸`.

The `RS[129]` list obtained from the inclusion `RS[128] ⊆ RS[129]` then forces the CA error above
`2⁻¹²⁸` through the list-to-CA transfer theorem `CodingTheory.rs_Lambda_extended_le_of_epsCa`.

The polynomial-valued definitions are `noncomputable` because Mathlib's `Polynomial` is.

## References

* [Kin26] for the coset construction on multiplicative subgroups;
* [CS25] for the transfer from list size to correlated-agreement error;
* [ABF26] for the grand-challenge formulation.
-/

@[expose] public section

open Polynomial ReedSolomon Finset
open scoped NNReal

namespace ProximityGap.GrandChallenges.Goldilocks512

/-- The list-size lower bound `⌊C(127, 33) / 128⌋`, named so that `simp` does not evaluate the
binomial coefficient. -/
def Nbig : ℕ := Nat.choose 127 33 / 128

namespace Coset

variable {F : Type} [Field F] {ω : F}

/-- The evaluation domain `(ωⁱ)_{i < 512}`. -/
def dom (hω : IsPrimitiveRoot ω 512) : Fin 512 ↪ F :=
  ⟨fun i ↦ ω ^ (i : ℕ), fun i j h ↦ Fin.ext (hω.pow_inj i.isLt j.isLt h)⟩

/-- The index set `{1, …, 127}`. -/
def J : Finset ℕ := (range 128).erase 0

/-- `P_T = ∏_{t ∈ {1, 2, 3}} (X - ω^{128 t})`. -/
noncomputable def PT (ω : F) : F[X] := ∏ t ∈ ({1, 2, 3} : Finset ℕ), (X - C (ω ^ (128 * t)))

/-- `R_S = ∏_{j ∈ S} (X - ω^{4j})`. -/
noncomputable def R (ω : F) (S : Finset ℕ) : F[X] := ∏ j ∈ S, (X - C (ω ^ (4 * j)))

/-- `a + X³³ - R_S`. -/
noncomputable def D (ω a : F) (S : Finset ℕ) : F[X] := C a + X ^ 33 - R ω S

/-- The codeword polynomial `g_S = P_T · expand 4 ((a + X³³ - R_S) /ₘ X)`. -/
noncomputable def g (ω a : F) (S : Finset ℕ) : F[X] := PT ω * expand F 4 (D ω a S /ₘ X)

/-- The received word `w(ωⁱ) = (ωⁱ)⁵⁰⁸ · P_T(ωⁱ) · (a + (ωⁱ)¹³²)`. -/
noncomputable def word (ω a : F) (i : Fin 512) : F :=
  (ω ^ (i : ℕ)) ^ 508 * (PT ω).eval (ω ^ (i : ℕ)) * (a + (ω ^ (i : ℕ)) ^ 132)

theorem mem_J {j : ℕ} : j ∈ J ↔ j ≠ 0 ∧ j < 128 := by simp [J]

theorem card_J : J.card = 127 := by simp [J]

theorem R_monic (S : Finset ℕ) : (R ω S).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem R_natDegree (S : Finset ℕ) : (R ω S).natDegree = S.card := by
  rw [R, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

theorem PT_monic : (PT ω).Monic := monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem PT_natDegree : (PT ω).natDegree = 3 := by
  rw [PT, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
  rfl

theorem D_degree_lt (a : F) {S : Finset ℕ} (hS : S.card = 33) : (D ω a S).degree < 33 := by
  have hR : (R ω S).degree = 33 := by
    rw [degree_eq_natDegree (R_monic S).ne_zero, R_natDegree, hS]; rfl
  have h1 : (X ^ 33 - R ω S).degree < 33 := by
    have := degree_sub_lt_left (p := (X ^ 33 : F[X])) (q := R ω S)
      (by rw [degree_X_pow, hR]; norm_cast) (pow_ne_zero _ X_ne_zero)
      (by rw [leadingCoeff_X_pow, (R_monic S).leadingCoeff])
    rwa [degree_X_pow] at this
  calc (D ω a S).degree = (C a + (X ^ 33 - R ω S)).degree := by rw [D, add_sub_assoc]
    _ ≤ max (C a).degree (X ^ 33 - R ω S).degree := degree_add_le _ _
    _ < 33 := max_lt (lt_of_le_of_lt degree_C_le
        (by exact_mod_cast (show (0 : ℕ) < 33 by norm_num))) h1

theorem X_mul_div {a : F} {S : Finset ℕ} (h0 : (D ω a S).eval 0 = 0) :
    X * (D ω a S /ₘ X) = D ω a S := by
  have h := mul_divByMonic_eq_iff_isRoot.mpr (show IsRoot (D ω a S) 0 from h0)
  simpa using h

theorem g_degree_lt (a : F) {S : Finset ℕ} (hS : S.card = 33) : (g ω a S).degree < 128 := by
  have hD : (D ω a S).natDegree ≤ 32 := by
    by_cases h : D ω a S = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt (n := 33) h).mpr (by exact_mod_cast D_degree_lt a hS)
      omega
  have hQ : (D ω a S /ₘ X).natDegree ≤ 31 := by
    rw [natDegree_divByMonic _ monic_X, natDegree_X]; omega
  have hE : (expand F 4 (D ω a S /ₘ X)).natDegree ≤ 124 := by
    rw [natDegree_expand]; omega
  have hg : (g ω a S).natDegree ≤ 127 := by
    calc (g ω a S).natDegree ≤ (PT ω).natDegree + (expand F 4 (D ω a S /ₘ X)).natDegree :=
          natDegree_mul_le
      _ ≤ 127 := by rw [PT_natDegree]; omega
  exact (degree_le_natDegree).trans_lt
    (by exact_mod_cast (show (g ω a S).natDegree < 128 by omega))

/-- The key identity: if `P_T(x) · R_S(x⁴) = 0` and `x ^ 512 = 1`, then `g_S(x) = w(x)`. -/
theorem eval_agree {a : F} {S : Finset ℕ} (h0 : (D ω a S).eval 0 = 0) {x : F}
    (hx : x ^ 512 = 1) (hz : (PT ω).eval x * (R ω S).eval (x ^ 4) = 0) :
    (g ω a S).eval x = x ^ 508 * (PT ω).eval x * (a + x ^ 132) := by
  have hD := congrArg (eval (x ^ 4)) (X_mul_div h0)
  have hDv : (D ω a S).eval (x ^ 4) = a + (x ^ 4) ^ 33 - (R ω S).eval (x ^ 4) := by
    simp only [D, eval_add, eval_sub, eval_C, eval_pow, eval_X]
  rw [eval_mul, eval_X, hDv] at hD
  simp only [g, eval_mul, expand_eval]
  linear_combination (x ^ 508 * (PT ω).eval x) * hD - ((PT ω).eval x *
    (D ω a S /ₘ X).eval (x ^ 4)) * hx - x ^ 508 * hz

theorem R_eval_eq_zero_iff (hω : IsPrimitiveRoot ω 512) {S : Finset ℕ} (hSJ : S ⊆ J)
    {j : ℕ} (hj : j ∈ J) : (R ω S).eval (ω ^ (4 * j)) = 0 ↔ j ∈ S := by
  rw [R, eval_prod, prod_eq_zero_iff]
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨j', hj', h⟩
    have hjl := (mem_J.mp hj).2
    have hj'l := (mem_J.mp (hSJ hj')).2
    have := hω.pow_inj (by omega) (by omega) h
    have : j = j' := by omega
    exact this ▸ hj'
  · intro h; exact ⟨j, h, rfl⟩

theorem pow_mod128 {M : Type*} [Monoid M] {y : M} (h : y ^ 128 = 1) (n : ℕ) :
    y ^ n = y ^ (n % 128) := by
  conv_lhs => rw [← Nat.mod_add_div n 128, pow_add, pow_mul, h, one_pow, mul_one]

theorem R_eval_zero (hω : IsPrimitiveRoot ω 512) {S : Finset ℕ} (hS : S.card = 33) :
    (R ω S).eval 0 = (-1) ^ 33 * (ω ^ 4) ^ ((∑ j ∈ S, j) % 128) := by
  have h128 : (ω ^ 4) ^ 128 = 1 := by rw [← pow_mul]; exact hω.pow_eq_one
  rw [R, eval_prod]
  have hfac : ∀ j ∈ S, eval 0 (X - C (ω ^ (4 * j))) = (-1) * (ω ^ 4) ^ j := by
    intro j _
    rw [eval_sub, eval_X, eval_C, zero_sub, pow_mul, neg_one_mul]
  rw [prod_congr rfl hfac, prod_mul_distrib, prod_const, hS, prod_pow_eq_pow_sum,
    pow_mod128 h128]

/-- There is a received word with at least `⌊C(127, 33) / 128⌋` codewords of
`RS[F, (ωⁱ)ᵢ, 128]` within relative distance `377/512`. -/
theorem big_list (hω : IsPrimitiveRoot ω 512) :
    ∃ w : Fin 512 → F, ((Nbig : ℕ) : ℕ∞) ≤
      (Code.closeCodewordsRel (ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F)) w
        (377 / 512)).encard := by
  classical
  obtain ⟨y, -, hy⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := J.powersetCard 33) (t := range 128) (f := fun S ↦ (∑ j ∈ S, j) % 128)
    (n := Nbig)
    (fun S _ ↦ mem_range.mpr (Nat.mod_lt _ (by norm_num))) ⟨0, by simp⟩
    (by rw [card_powersetCard, card_J, card_range]; unfold Nbig; exact Nat.mul_div_le _ _)
  set 𝒮 := (J.powersetCard 33).filter fun S ↦ (∑ j ∈ S, j) % 128 = y with h𝒮
  set a : F := (-1) ^ 33 * (ω ^ 4) ^ y with ha
  have hmem : ∀ S ∈ 𝒮, S ⊆ J ∧ S.card = 33 ∧ (D ω a S).eval 0 = 0 := by
    intro S hS
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    obtain ⟨hSJ, hSc⟩ := mem_powersetCard.mp hS1
    refine ⟨hSJ, hSc, ?_⟩
    simp only [D, eval_sub, eval_add, eval_C, eval_pow, eval_X, R_eval_zero hω hSc, hS2, ha]
    ring
  refine ⟨word ω a, ?_⟩
  have hrad : capacityRadius (7 / 512) (Fintype.card (Fin 512)) 128 = 377 / 512 := by
    simp only [capacityRadius, Fintype.card_fin]; norm_num
  have hthr : capacityAgreementThreshold (7 / 512) (Fintype.card (Fin 512)) 128 = 135 := by
    simp only [capacityAgreementThreshold, Fintype.card_fin]; norm_num
  rw [← hrad, closeCodewordsRel_eq_eval_image_agreeingPolynomials (by norm_num) (by simp), hthr]
  -- the map `S ↦ (g_S(ωⁱ))ᵢ`
  let φ : Finset ℕ → (Fin 512 → F) := fun S ↦ ReedSolomon.evalOnPoints (dom hω) (g ω a S)
  have hinj : Set.InjOn φ (𝒮 : Set (Finset ℕ)) := by
    intro S hS S' hS' heq
    obtain ⟨hSJ, hSc, h0⟩ := hmem S hS
    obtain ⟨hSJ', hSc', h0'⟩ := hmem S' hS'
    have hg : g ω a S = g ω a S' := by
      apply eq_of_degree_sub_lt_of_eval_finset_eq (univ.map (dom hω))
      · rw [card_map, card_univ, Fintype.card_fin]
        calc (g ω a S - g ω a S').degree ≤ max (g ω a S).degree (g ω a S').degree :=
              degree_sub_le _ _
          _ < 128 := max_lt (g_degree_lt a hSc) (g_degree_lt a hSc')
          _ ≤ 512 := by exact_mod_cast (show (128 : ℕ) ≤ 512 by norm_num)
      · intro x hx
        obtain ⟨i, -, rfl⟩ := mem_map.mp hx
        exact congrFun heq i
    have hE : expand F 4 (D ω a S /ₘ X) = expand F 4 (D ω a S' /ₘ X) :=
      mul_left_cancel₀ PT_monic.ne_zero hg
    have hQ := expand_injective (by norm_num : 0 < 4) hE
    have hDD : D ω a S = D ω a S' := by rw [← X_mul_div h0, ← X_mul_div h0', hQ]
    have hR : R ω S = R ω S' := by
      simp only [D] at hDD; exact sub_right_injective hDD
    ext j
    by_cases hj : j ∈ J
    · rw [← R_eval_eq_zero_iff hω hSJ hj, ← R_eval_eq_zero_iff hω hSJ' hj, hR]
    · exact ⟨fun h ↦ absurd (hSJ h) hj, fun h ↦ absurd (hSJ' h) hj⟩
  have hsub : φ '' (𝒮 : Set (Finset ℕ)) ⊆
      (fun p : ListDecoding.MessagePolynomial F 128 ↦ ReedSolomon.evalOnPoints (dom hω) p) ''
        agreeingPolynomials (dom hω) 128 135 (word ω a) := by
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨hSJ, hSc, h0⟩ := hmem S hS
    refine ⟨⟨g ω a S, mem_degreeLT.mpr (g_degree_lt a hSc)⟩, ?_, rfl⟩
    change 135 ≤ Code.agree (ReedSolomon.evalOnPoints (dom hω) (g ω a S)) (word ω a)
    let s : Finset (ℕ × ℕ) := (S ×ˢ range 4) ∪ ({0} ×ˢ {1, 2, 3})
    have hdisj : Disjoint (S ×ˢ range 4) ({0} ×ˢ ({1, 2, 3} : Finset ℕ)) := by
      rw [disjoint_left]
      intro p hp hp'
      have h1 := (mem_product.mp hp).1
      have h2 := (mem_product.mp hp').1
      rw [mem_singleton] at h2
      exact (mem_J.mp (hSJ h1)).1 h2
    have hcard : s.card = 135 := by
      rw [card_union_of_disjoint hdisj, card_product, card_product, hSc]; rfl
    have hbound : ∀ p ∈ s, p.1 < 128 ∧ p.2 < 4 := by
      intro p hp
      rcases mem_union.mp hp with h | h
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        exact ⟨(mem_J.mp (hSJ h1)).2, mem_range.mp h2⟩
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        rw [mem_singleton] at h1
        simp only [mem_insert, mem_singleton] at h2
        omega
    let f : ℕ × ℕ → Fin 512 := fun p ↦ ⟨(p.1 + 128 * p.2) % 512, Nat.mod_lt _ (by norm_num)⟩
    have hfval : ∀ p ∈ s, ((f p : Fin 512) : ℕ) = p.1 + 128 * p.2 := by
      intro p hp
      have := hbound p hp
      change (p.1 + 128 * p.2) % 512 = p.1 + 128 * p.2
      exact Nat.mod_eq_of_lt (by omega)
    rw [← hcard]
    unfold Code.agree
    refine card_le_card_of_injOn f ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      have hv := hfval p hp
      change (g ω a S).eval (ω ^ ((f p : Fin 512) : ℕ)) = word ω a (f p)
      simp only [word]
      rw [hv]
      have hx : (ω ^ (p.1 + 128 * p.2)) ^ 512 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
      refine eval_agree h0 hx ?_
      rcases mem_union.mp hp with h | h
      · obtain ⟨h1, -⟩ := mem_product.mp h
        have h4 : (ω ^ (p.1 + 128 * p.2)) ^ 4 = ω ^ (4 * p.1) := by
          rw [← pow_mul, show (p.1 + 128 * p.2) * 4 = 4 * p.1 + 512 * p.2 by ring, pow_add,
            pow_mul ω 512 p.2, hω.pow_eq_one, one_pow, mul_one]
        rw [h4, (R_eval_eq_zero_iff hω hSJ (hSJ h1)).mpr h1, mul_zero]
      · obtain ⟨h1, h2⟩ := mem_product.mp h
        rw [mem_singleton] at h1
        have hPT : (PT ω).eval (ω ^ (p.1 + 128 * p.2)) = 0 := by
          rw [PT, eval_prod, prod_eq_zero_iff]
          refine ⟨p.2, h2, ?_⟩
          simp only [eval_sub, eval_X, eval_C, h1, zero_add, sub_self]
        rw [hPT, zero_mul]
    · intro p hp q hq hpq
      have h1 := hfval p hp
      have h2 := hfval q hq
      have hb1 := hbound p hp
      have hb2 := hbound q hq
      have : p.1 + 128 * p.2 = q.1 + 128 * q.2 := by rw [← h1, ← h2, hpq]
      exact Prod.ext (by omega) (by omega)
  calc ((Nbig : ℕ) : ℕ∞) ≤ (𝒮.card : ℕ∞) := by exact_mod_cast hy
    _ = (φ '' (𝒮 : Set (Finset ℕ))).encard := by
        rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard]
    _ ≤ _ := Set.encard_mono hsub

end Coset

open Coset

theorem choose_bound : goldilocks ^ 3 < Nbig * 2 ^ 128 := by
  unfold Nbig; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel

theorem choose_bound2 : 2 * goldilocks ^ 3 < (Nbig - 1) * 2 ^ 128 := by
  unfold Nbig; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel

/-- Unsafe-side witness for the list-decoding grand challenge at `δ = 377/512`, for every
interleaving `m ≥ 1`, on the domain of powers of a primitive `512`-th root of unity.

It is `noncomputable` because the received word is chosen by `Classical.choose`. -/
noncomputable def listUpperWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] {ω : F} (hω : IsPrimitiveRoot ω 512)
    (hcard : Fintype.card F = goldilocks ^ 3) (m : ℕ) (hm : 1 ≤ m) :
    ListUpperWitness (ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F)) m (1 / 2 ^ 128) :=
  ListUpperWitness.ofEncardGt (δ := 377 / 512)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (fun i _ ↦ (big_list hω).choose i) (by
      have hδ : ((377 / 512 : ℝ≥0) : ℝ) = 377 / 512 := by push_cast; ring
      rw [hδ, hcard]
      have he : Function.Injective (fun (a : F) (_ : Fin m) ↦ a) :=
        fun a b h ↦ congrFun h ⟨0, by omega⟩
      have hCD : ∀ c ∈ (ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F)),
          (fun (a : F) (_ : Fin m) ↦ a) ∘ c ∈
            ((ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F)) ^⋈ (Fin m)) := by
        intro c hc j; exact hc
      have hle := (big_list hω).choose_spec.trans
        (Code.encard_closeCodewordsRel_le_of_injective_comp he hCD
          (big_list hω).choose (377 / 512))
      have hnum : ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) * ((goldilocks ^ 3 : ℕ) : ENNReal) <
          ((Nbig : ℕ) : ENNReal) := by
        rw [← ENNReal.coe_natCast (goldilocks ^ 3), ← ENNReal.coe_natCast Nbig,
          ← ENNReal.coe_mul, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
        have h := (Nat.cast_lt (α := ℝ)).mpr choose_bound
        push_cast at h ⊢
        linarith
      calc ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) * ((goldilocks ^ 3 : ℕ) : ENNReal)
          < ((Nbig : ℕ) : ENNReal) := hnum
        _ = (((Nbig : ℕ) : ℕ∞) : ENNReal) := (ENat.toENNReal_coe _).symm
        _ ≤ _ := by exact_mod_cast hle)

/-- The list from `big_list` also lies in `RS[F, (ωⁱ)ᵢ, 129]`. -/
theorem lambda129_ge {F : Type} [Field F] {ω : F}
    (hω : IsPrimitiveRoot ω 512) :
    ((Nbig : ℕ) : ℕ∞) ≤
      Code.Lambda (ReedSolomon.code (dom hω) 129 : Set (Fin 512 → F)) (377 / 512) := by
  classical
  obtain ⟨w, hw⟩ := big_list hω
  refine hw.trans ((Code.encard_closeCodewordsRel_le_Lambda _ _ w).trans ?_)
  refine Code.Lambda_le_of_injective_comp (e := id) Function.injective_id ?_ _
  intro c hc
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
  refine Submodule.mem_map.mpr ⟨p, ?_, rfl⟩
  rw [mem_degreeLT] at hp ⊢
  exact hp.trans (by exact_mod_cast (show (128 : ℕ) < 129 by norm_num))

/-- The CA error of `RS[F, (ωⁱ)ᵢ, 128]` at `δ = 377/512` exceeds `2⁻¹²⁸` when
`|F| = p ^ 3`. -/
theorem epsCa_gt {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F] {ω : F}
    (hω : IsPrimitiveRoot ω 512) (hcard : Fintype.card F = goldilocks ^ 3) :
    ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) <
      ProximityGap.epsCa (F := F) (A := F) (ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F))
        (377 / 512 : ℝ).toNNReal (377 / 512 : ℝ).toNNReal := by
  set ε := ProximityGap.epsCa (F := F) (A := F)
    (ReedSolomon.code (dom hω) 128 : Set (Fin 512 → F))
    (377 / 512 : ℝ).toNNReal (377 / 512 : ℝ).toNNReal with hε
  set N := Nbig with hNdef
  have hq : (Fintype.card F : ℝ) = (goldilocks : ℝ) ^ 3 := by rw [hcard]; push_cast; ring
  have hG3 : (2 : ℝ) ^ 64 ≤ (goldilocks : ℝ) ^ 3 := by
    have : 2 ^ 64 ≤ goldilocks ^ 3 := by unfold goldilocks; norm_num
    exact_mod_cast this
  have hc1 : 1 ≤ N := by
    rw [hNdef]; unfold Nbig; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have hbig : 2 * (goldilocks : ℝ) ^ 3 < ((N : ℝ) - 1) * 2 ^ 128 := by
    have h := (Nat.cast_lt (α := ℝ)).mpr choose_bound2
    rw [← hNdef] at h
    push_cast [Nat.cast_sub hc1] at h
    linarith
  have hreal : ((2 : ℝ) ^ 128)⁻¹ < ε.toReal := by
    refine lt_of_not_ge fun hcon ↦ ?_
    have hsmall : (512 : ℝ) / (128 * (goldilocks : ℝ) ^ 3) ≤ 1 / 256 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hL := CodingTheory.rs_Lambda_extended_le_of_epsCa (dom hω) 128 (377 / 512) (1 / 2)
      (by norm_num) (by norm_num) (by rw [Fintype.card_fin]; norm_num) (by norm_num)
      (by norm_num) (by rw [Fintype.card_fin, hcard]; unfold goldilocks; norm_num) (by
        rw [Fintype.card_fin, hq]
        refine hcon.trans ?_
        push_cast
        have h2 : ((2 : ℝ) ^ 128)⁻¹ ≤ 1 / 2 * (1 / 128 - 1 / 256) := by norm_num
        linarith)
    have hN : N ≤ ⌈(Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal⌉₊ := by
      have := (lambda129_ge hω).trans hL
      exact_mod_cast this
    have hx0 : 0 ≤ (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal := by positivity
    have h1 : (N : ℝ) < (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal + 1 :=
      lt_of_le_of_lt (by exact_mod_cast hN) (Nat.ceil_lt_add_one hx0)
    have hx : (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal =
        2 * (goldilocks : ℝ) ^ 3 * ε.toReal := by rw [hq]; ring
    rw [hx] at h1
    have hε1 : ε.toReal * 2 ^ 128 ≤ 1 := by
      calc ε.toReal * 2 ^ 128 ≤ ((2 : ℝ) ^ 128)⁻¹ * 2 ^ 128 :=
            mul_le_mul_of_nonneg_right hcon (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have hA := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < 2 ^ 128)
    have hB := mul_le_mul_of_nonneg_left hε1
      (by positivity : (0 : ℝ) ≤ 2 * (goldilocks : ℝ) ^ 3)
    linarith
  have hne : ε ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hreal
    exact absurd hreal (not_lt.mpr (by positivity))
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hne]
  push_cast
  simpa [one_div] using hreal

/-- Unsafe-side witness for the mutual-correlated-agreement grand challenge at `δ = 377/512`, on
the domain of powers of a primitive `512`-th root of unity.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def mcaUpperWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] {ω : F} (hω : IsPrimitiveRoot ω 512)
    (hcard : Fintype.card F = goldilocks ^ 3) :
    McaUpperWitness (ReedSolomon.code (dom hω) 128) (1 / 2 ^ 128) :=
  McaUpperWitness.ofEpsCaGt (δ := (377 / 512 : ℝ).toNNReal)
    (by rw [Real.toNNReal_le_one]; norm_num) (epsCa_gt hω hcard)

end ProximityGap.GrandChallenges.Goldilocks512
