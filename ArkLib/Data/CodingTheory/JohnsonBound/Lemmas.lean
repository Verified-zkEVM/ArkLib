/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations

namespace JohnsonBound

/-- The function used for `q`-ary Johnson Bound (local copy for lemmas).
-/
noncomputable def J' (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - Real.sqrt (1 - frac * δ))

/-- A lemma for proving sqrt_le_J (local copy for lemmas).
-/
lemma division_by_conjugate' {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
  a - b.sqrt = (a^2 - b)/(a + b.sqrt) := by
  rw [eq_div_iff hnonzero]
  ring_nf
  simp_all

section

variable {n : ℕ}
variable {F : Type*} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {i : Fin n}

private def Fi (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset (Fin n → F) :=
  { x | x ∈ B ∧ x i = α }

private abbrev K (B : Finset (Fin n → F)) (i : Fin n) (α : F) : ℕ :=
  (Fi B i α).card

private lemma Fis_cover_B : B = Finset.univ.biUnion (Fi B i) := by
  aesop (add simp [Fi])

private lemma Fis_pairwise_disjoint : Set.PairwiseDisjoint Set.univ (Fi B i) := by
  unfold Fi
  rintro x - y - h₁ _ h₂ h₃ _ contra
  specialize h₂ contra
  specialize h₃ contra
  aesop

private lemma sum_K_eq_card : ∑ (α : F), K B i α = B.card := by
  rw (occs := [2]) [Fis_cover_B (B := B) (i := i)]
  rw [Finset.card_biUnion (by simp [Fis_pairwise_disjoint])]

private lemma K_eq_sum {α : F} : K B i α = ∑ (x : B), if x.1 i = α then 1 else 0 := by
  simp [K, Fi]
  simp_rw [Finset.card_filter, Finset.sum_attach_eq_sum_dite]
  apply Finset.sum_congr <;> aesop

@[simp]
private lemma K_le_card {α : F} : K B i α ≤ B.card := by
  simp [K, Fi]
  exact Finset.card_le_card fun _ ha ↦ by simp at ha; exact ha.1

open Finset in
private lemma sum_choose_K' [Zero F]
  (h_card : 2 ≤ (Fintype.card F))
  :
  (Fintype.card (α := F) - 1) * choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤
  ∑ (α : F) with α ≠ 0, choose_2 (K B i α) := by
  rw [←sum_K_eq_card (i := i), Nat.cast_sum]
  set X₁ : ℚ := Fintype.card F - 1
  have X₁h : X₁ ≠ 0 := by simp [X₁, sub_eq_zero]; omega
  set X₂ := K B i
  suffices X₁ * choose_2 (∑ x with x ≠ 0, (fun _ ↦ X₁⁻¹) x • (Nat.cast (R := ℚ) ∘ X₂) x) ≤
           ∑ α with α ≠ 0, choose_2 ↑(X₂ α) by
    simp at this
    convert this
    rw [sum_eq_sum_diff_singleton_add (i := 0) (by simp)]
    ring_nf
    rw [sum_mul]
    apply sum_congr (ext _) <;> field_simp
  apply le_trans
  · rewrite [mul_le_mul_left (by aesop)]
    apply ConvexOn.map_sum_le choose_2_convex
            (by aesop (add safe (by omega)))
            (by simp [X₁]; rw [Field.mul_inv_cancel _ X₁h])
            (by simp)
  · rw [mul_sum]; field_simp

private def sum_choose_K_i (B : Finset (Fin n → F)) (i : Fin n) : ℚ :=
  ∑ (α : F), choose_2 (K B i α)

private lemma le_sum_choose_K [Zero F]
  (h_card : 2 ≤ (Fintype.card F)) :
  choose_2 (K B i 0) + (Fintype.card (α := F) - 1) *
  choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤ sum_choose_K_i B i := by
  unfold sum_choose_K_i
  rw [show Finset.univ = {0} ∪ {x : F | x ≠ 0}.toFinset by ext; simp; tauto]
  simp [Finset.sum_union, sum_choose_K' h_card]

private def k [Zero F] (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ) / n * ∑ i, K B i 0

omit [Fintype F] in
private lemma hamming_weight_eq_sum [Zero F] {x : Fin n → F}
  :
  ‖x‖₀ = ∑ i, if x i = 0 then 0 else 1 := by simp [hammingNorm, Finset.sum_ite]

private lemma sum_hamming_weight_sum [Zero F]
  :
  ∑ x ∈ B, (‖x‖₀ : ℚ) = n * B.card - ∑ i, K B i 0 := by
  simp only [hamming_weight_eq_sum, Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    K_eq_sum, Finset.sum_boole, Nat.cast_id]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, eq_sub_iff_add_eq]
  simp_rw [Nat.cast_sum, Nat.cast_ite]
  conv in Finset.sum _ _ => arg 2; ext; arg 2; ext; rw [←ite_not]
  simp_rw [Finset.univ_eq_attach, Finset.sum_attach_eq_sum_dite]
  simp only [Nat.cast_one, CharP.cast_eq_zero, dite_eq_ite, Finset.sum_ite_mem, Finset.univ_inter]
  rw [←Finset.sum_add_distrib]
  simp_rw [←Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]
  simp

private lemma k_and_e [Zero F]
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  k B = B.card * (n - e B 0) / n := by
  simp [e, k, sum_hamming_weight_sum]
  field_simp

private lemma k_and_e' [Zero F]
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  k B / B.card = (n - e B 0) / n := by
  rw [k_and_e h_n h_B]
  field_simp
  ring

private lemma k_choose_2 [Zero F] {B : Finset (Fin n → F)}
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1:ℚ) / n) i • (fun i ↦ K B i 0) i) * n ≤
           ∑ i, choose_2 (K B i 0) by
    rw [mul_comm]; convert this
    simp [k, Finset.mul_sum]
  transitivity
  apply (mul_le_mul_right (by simp; omega)).2
          (ConvexOn.map_sum_le
            choose_2_convex
            (by simp)
            (by field_simp)
            (by simp))
  rw [Finset.sum_mul]
  field_simp

private def aux_frac (B : Finset (Fin n → F)) (x : ℚ) : ℚ :=
  (B.card - x) / (Fintype.card F - 1)

private lemma sum_1_over_n_aux_frac_k_i [Zero F]
  (h_n : 0 < n) : ∑ i, 1/n * aux_frac B (K B i 0) = aux_frac B (k B) := by
  simp [aux_frac]
  suffices (n : ℚ)⁻¹ * (↑n * B.card - ∑ x, JohnsonBound.K B x 0) = B.card - k B by
    rw [←Finset.mul_sum, ←Finset.sum_div, ←this]
    field_simp
  field_simp [k]; ac_rfl

private lemma aux_sum [Zero F]
  (h_n : 0 < n)
  : n * choose_2 (aux_frac B (k B)) ≤ ∑ i, choose_2 (aux_frac B (K B i 0)) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1:ℚ)/n) i • (fun x ↦ aux_frac B (K B x 0)) i) * ↑n ≤
           ∑ i, choose_2 (JohnsonBound.aux_frac B (JohnsonBound.K B i 0)) by
    rw [←sum_1_over_n_aux_frac_k_i h_n, mul_comm]
    convert this
  transitivity
  apply (mul_le_mul_right (by simp; omega)).2
          (ConvexOn.map_sum_le
             choose_2_convex
             (by simp)
             (by field_simp )
             (by simp))
  rw [Finset.sum_mul]
  field_simp

private lemma le_sum_sum_choose_K [Zero F]
  (h_n : 0 < n)
  (h_B : B.card ≠ 0)
  (h_card : 2 ≤ Fintype.card F)
  :
  n * (choose_2 (k B) + (Fintype.card (α := F) - 1)
    * choose_2 ((B.card - k B) / ((Fintype.card (α := F) - 1))))
  ≤ ∑ i, sum_choose_K_i B i := by
  rw [mul_add]
  transitivity
  apply add_le_add_right (k_choose_2 (n := n) (by omega) h_B)
  transitivity
  apply add_le_add_left (by
    rewrite [←mul_assoc, mul_comm (n : ℚ), mul_assoc]
    transitivity
    apply (mul_le_mul_left (by simp; omega)).2 (aux_sum h_n)
    rfl
  )
  rw [Finset.mul_sum, ←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ ↦ le_sum_choose_K h_card

private def F2i (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = α ∧ x.2 i = α ∧ x.1 ≠ x.2 }

private def Bi (B : Finset (Fin n → F)) (i : Fin n) : Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = x.2 i ∧ x.1 ≠ x.2 }

private lemma Bi_biUnion_F2i :
  Bi B i = Finset.univ.biUnion (F2i B i) := by aesop (add simp [Bi, F2i])

@[simp]
private lemma F2i_disjoint :
  Set.PairwiseDisjoint Set.univ (F2i B i) := by
  simp
    [Set.PairwiseDisjoint
    , Set.Pairwise
    , Disjoint
    , F2i
    , Finset.Nonempty
    , Finset.subset_iff
    ]
  intro _ _ _ _ h1 h2 x₁ x₂ contr
  specialize h1 x₁ x₂ contr
  specialize h2 x₁ x₂ contr
  aesop

private lemma F2i_card {α : F} :
  (F2i B i α).card = 2 * choose_2 (K B i α) := by
  simp [F2i]
  letI Tα := (Fin n → F) × (Fin n → F)
  let S₁ : Finset Tα := {x | (x.1 ∈ B ∧ x.2 ∈ B) ∧ x.1 i = α ∧ x.2 i = α}
  let S₂ : Finset _ := {x | x ∈ S₁ ∧ x.1 ≠ x.2}
  set A := Fi B i α with eqA
  suffices S₂.card = 2 * choose_2 (K B i α) by simp [S₂, S₁, ←this]; congr; ext; tauto
  rw [
    show S₂ = S₁ \ ({x | x ∈ S₁ ∧ x.1 = x.2} : Finset _) by aesop,
    Finset.card_sdiff fun _ _ ↦ by aesop,
    show S₁ = A ×ˢ A by ext; rw [Finset.mem_product]; simp [S₁, Fi, A]; tauto,
    Finset.filter_and
  ]
  simp; rw [Finset.card_prod_self_eq (s := A), Finset.card_product]
  simp [choose_2, K, eqA.symm]
  have : A.card ≤ A.card * A.card := Nat.le_mul_self _
  field_simp [this]; ring

open Finset in
private lemma sum_of_not_equals :
  ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0)
  =
  2 * choose_2 #B - 2 * ∑ α, choose_2 (K B i α)
  := by
  generalize eq₁ : {x ∈ B ×ˢ B | x.1 ≠ x.2} = s₁
  suffices #s₁ - #(Bi B i) = 2 * choose_2 #B - 2 * ∑ α, choose_2 (JohnsonBound.K B i α) by
    rw [
      show (∑ x ∈ s₁, if x.1 i ≠ x.2 i then 1 else 0)
         = (∑ x ∈ s₁, ((1 : ℚ) - if x.1 i = x.2 i then 1 else 0)) by congr; aesop
    ]
    simp; convert this
    ext; simp [←eq₁, Bi]; tauto
  rw [
    show #s₁ = 2 * choose_2 #B by
      rw [
        show s₁ = (B ×ˢ B) \ {x ∈ B ×ˢ B | x.1 = x.2} by ext; simp [eq₁.symm]; tauto,
        card_sdiff (by simp)
      ]
      simp [choose_2]
      zify [Nat.le_mul_self #B]
      ring
  ]
  rw [Bi_biUnion_F2i, Finset.card_biUnion (by simp [F2i_disjoint])]
  simp; simp_rw [F2i_card, mul_sum]

omit [Fintype F] in
private lemma hamming_dist_eq_sum {x y : Fin n → F} :
  Δ₀(x, y) = ∑ i, if x i = y i then 0 else 1 := by
  simp [hammingDist, Finset.sum_ite]

omit [Fintype F] [DecidableEq F] in
private lemma choose_2_card_ne_zero (h : 2 ≤ B.card) : choose_2 ↑B.card ≠ 0 := by
  simp [choose_2, sub_eq_zero]
  aesop (add safe (by omega))

omit [Fintype F] in
private lemma d_eq_sum {B : Finset (Fin n → F)}
  (h_B : 2 ≤ B.card)
  :
  2 * choose_2 B.card * d B =
  ∑ i, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) := by
  field_simp [d, choose_2_card_ne_zero h_B]
  rw [Finset.sum_comm]
  simp_rw [hamming_dist_eq_sum]
  field_simp

private lemma sum_sum_K_i_eq_n_sub_d
  (h_B : 2 ≤ B.card)
  :
  ∑ i, sum_choose_K_i B i = choose_2 B.card * (n - d B) := by
  rw [show
    choose_2 B.card * (n - d B) = choose_2 B.card * n - (2 * choose_2 B.card * d B) / 2 by ring
  ]
  simp_rw [d_eq_sum h_B, sum_of_not_equals]
  field_simp [←Finset.mul_sum, sum_choose_K_i]
  ring

private lemma almost_johnson [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  n * (choose_2 (k B) + (Fintype.card F - 1)
    * choose_2 ((B.card - k B) / (Fintype.card F - 1)))
  ≤
  choose_2 B.card * (n - d B) :=
  le_trans (le_sum_sum_choose_K h_n (by omega) h_card) (sum_sum_K_i_eq_n_sub_d h_B ▸ le_refl _)

private lemma almost_johnson_choose_2_elimed [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ Fintype.card F)
  :
  (k B * (k B - 1)  +
    (B.card - k B) * ((B.card - k B)/(Fintype.card F-1) - 1))
  ≤
  B.card * (B.card - 1) * (n - d B)/n := by
  have h := almost_johnson h_n h_B h_card; simp [choose_2] at h
  set C := (Fintype.card F : ℚ) - 1
  set δ := B.card - k B
  exact le_of_mul_le_mul_left
    (a0 := show 0 < (n : ℚ) * 2⁻¹ by simp [h_n])
    (le_trans (b := ↑n * 2⁻¹ * (k B * (k B - 1) + C * (δ / C) * (δ / C - 1)))
              (by rw [mul_div_cancel₀ _ (by simp [sub_eq_zero, C]; omega)])
              (le_trans
                (b := B.card * (B.card - 1) / 2 * (n - d B))
                (by convert h using 1; field_simp; ring_nf; tauto)
                (by rw [show n * 2⁻¹ * (B.card * (B.card - 1) * (n - d B) / n) =
                             n * (↑n)⁻¹ * 2⁻¹ * (B.card * (B.card - 1) * (n - d B)) by ring]
                    field_simp)))

private lemma almost_johnson_lhs_div_B_card [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  :
  (k B * (k B - 1)  +
    (B.card - k B) * ((B.card - k B)/(Fintype.card F - 1) - 1)) / B.card
  =
  (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 := by
  letI E := (n - e B 0) / n
  generalize eqrhs : (_ + _ - 1 : ℚ) = rhs
  have eqE : E = k B / B.card := by unfold E; rw [k_and_e'] <;> omega
  suffices
    (B.card * E - 1) * E + ((B.card - B.card * E) / (Fintype.card F - 1) - 1) * (1 - E) = rhs by
    rw [eqE, mul_div_cancel₀ _ (by simp only [ne_eq, Rat.natCast_eq_zero]; omega)] at this
    rw [←this]
    field_simp; ring
  rw [←eqrhs, show E = 1 - (e B 0) / n by field_simp [E]]
  ring_nf; field_simp; ring

private lemma johnson_unrefined [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1
  ≤
  (B.card - 1) * (1 - d B/n) := by
  suffices k B * (k B - 1) + (B.card - k B) * ((B.card - k B) / (Fintype.card F - 1) - 1) ≤
           B.card * (B.card - 1) * ((n - d B) / n) by
    rw [
      show (1 - d B / n) = (n - d B) / n by field_simp,
      ←almost_johnson_lhs_div_B_card h_n h_B,
      div_le_iff₀ (by simp only [Nat.cast_pos]; omega)
    ]
    linarith
  exact le_trans (almost_johnson_choose_2_elimed h_n h_B h_card) (by field_simp)

private lemma johnson_unrefined_by_M [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * ((1 - e B 0 / n) ^ 2  + (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  ≤
  d B/n :=
  suffices B.card * ((1 - e B 0 / n) ^ 2 + e B 0 ^ 2 / ((Fintype.card F - 1) * n ^ 2)) -
           B.card * (1 - d B / n) + -1 + B.card * (1 - d B / n) ≤
           (B.card - 1) * (1 - d B / n) by linarith
  le_trans (by ring_nf; field_simp) (johnson_unrefined h_n h_B h_card)

private lemma johnson_unrefined_by_M' [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card * (Fintype.card F / (Fintype.card F - 1)) *
           ((1 - e B 0 / n) ^ 2  + e B 0 ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  ≤
  (Fintype.card F / (Fintype.card F - 1)) * d B/n := by
  rw [mul_comm (B.card : ℚ), mul_assoc, ←mul_div]
  exact (mul_le_mul_left (by field_simp; omega)).2 (johnson_unrefined_by_M h_n h_B h_card)

private lemma johnson_denom [Zero F]
  (h_card : 2 ≤ (Fintype.card F))
  :
  (Fintype.card F / (Fintype.card F - 1)) *
  ((1 - e B 0 / n) ^ 2  + (e B 0) ^ 2 / ((Fintype.card F - 1) * n^2) - 1 + d B/n)
  =
  (1 - ((Fintype.card F) / (Fintype.card F - 1)) *
  (e B 0 / n)) ^ 2 - (1 - ((Fintype.card F) / (Fintype.card F - 1)) * (d B/n))  := by
  set C := Fintype.card F
  set C₁ := (C : ℚ) - 1
  have n₂ : C₁ ≠ 0 := by simp [C₁, C, sub_eq_zero]; omega
  suffices C / C₁ * (d B / n - 2 * e B 0 / n + C / C₁ * e B 0 ^ 2 / n ^ 2) =
           (1 - C / C₁ * (e B 0 / n)) ^ 2 - (1 - C / C₁ * (d B / n)) by
    have eq₂ : C₁ * C₁⁻¹ = 1 := by field_simp
    rw [←this, show C / C₁ = 1 + 1 / C₁ by unfold C₁; field_simp]
    ring_nf
  ring

private lemma johnson_bound₀ [Zero F]
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card *
    ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B 0 / n)) ^ 2
      - (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B/n)))  ≤
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B/n := by
  rw [←johnson_denom h_card, ←mul_assoc]
  exact johnson_unrefined_by_M' h_n h_B h_card

protected lemma johnson_bound_lemma [Field F] {v : Fin n → F}
  (h_n : 0 < n)
  (h_B : 2 ≤ B.card)
  (h_card : 2 ≤ (Fintype.card F))
  :
  B.card *
    ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B v / n)) ^ 2
      - (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B/n)))  ≤
  ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B/n := by
  rw [lin_shift_e (by omega), lin_shift_d h_B, lin_shift_card (v := v)]
  exact johnson_bound₀ h_n (lin_shift_card (B := B) ▸ h_B) h_card

protected lemma a_lemma_im_not_proud_of_OLD {v a : Fin n → F}
  (h_card : 2 ≤ Fintype.card F)
  :
  |(1 : ℚ) - ((1 : ℚ) + (1 : ℚ) / ((Fintype.card F : ℚ) - 1)) * ↑Δ₀(v, a) / ↑n|
   ≤ 1 := by
  simp
  by_cases hn : n = 0 <;> try simp [hn]
  have hn : 0 < n := by omega
  by_cases heq : v = a <;> try simp [heq]
  rw [abs_le]
  apply And.intro
  · simp
    rw [←mul_div]
    apply le_trans (b := (2 : ℚ) * (↑Δ₀(v, a) / ↑n))
    rw [mul_comm, mul_comm (2 : ℚ) _, mul_le_mul_left]
    suffices h : ((Fintype.card F : ℚ) - 1)⁻¹ ≤ 1 by {
      have h' : (2 : ℚ) = 1 + 1 := by ring
      rw [h']
      apply add_le_add
      simp
      assumption
    }
    apply (le_of_mul_le_mul_left (a := (↑(Fintype.card F : ℚ) - 1))) (a0 := by
      {
        simp
        omega
      })
    rw [Field.mul_inv_cancel _ (by {
      intro contr
      have h : (Fintype.card F : ℚ) = 1 := by
        rw [←zero_add (1 :ℚ)]
        rw [←contr]
        simp
      simp at h
      omega
    })]
    simp
    apply le_of_add_le_add_right (a := 1)
    ring_nf
    simp
    · assumption
    field_simp
    · assumption
    ring_nf
    conv =>
      rhs
      rw [←mul_one (2 : ℚ)]
      rfl
    rw [mul_comm]
    apply (mul_le_mul_left (by simp)).2
    have h : (↑Δ₀(v, a) : ℚ) ≤ ↑n := by
      simp [hammingDist]
      apply le_trans (Finset.card_le_univ _)
      simp
    rw [mul_comm]
    apply le_trans
    · apply (mul_le_mul_left (by simp [hn])).2 h
    rw [mul_comm]
    rw [Field.mul_inv_cancel _ (by {
      simp
      omega
    })]
  · simp
    rw [←mul_div, mul_nonneg_iff]
    left
    apply And.intro
    · apply le_trans (b := 1) (by simp)
      simp
      omega
    · rw [Field.div_eq_mul_inv]
      rw [mul_nonneg_iff]
      left
      simp

protected lemma abs_one_sub_div_le_one {v a : Fin n → F}
  (h_card : 2 ≤ Fintype.card F)
  :
  |1 - (1 + 1 / ((Fintype.card F : ℚ) - 1)) * Δ₀(v, a) / n| ≤ 1 := by
  by_cases eq : n = 0 <;> [simp [eq]; skip]
  by_cases heq : v = a <;> [simp [heq]; skip]
  rw [abs_le]
  refine ⟨?p, by simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
                 exact div_nonneg (mul_nonneg (add_nonneg zero_le_one (by simp; omega))
                                              (by simp))
                                  (by linarith)⟩
  set a₁ := (Fintype.card F : ℚ) - 1
  set a₂ := (Δ₀(v, a) : ℚ)
  have ha₂ : a₂ ≤ n := by simp [a₂]; apply (le_trans (Finset.card_le_univ _) (by simp))
  set a₃ := a₂ / n
  have : a₁⁻¹ ≤ 1 := by aesop (add simp [inv_le_one_iff₀, le_sub_iff_add_le])
                              (add safe (by norm_cast))
  suffices (1 + a₁⁻¹) * a₃ ≤ 2 * a₃ ∧ 2 * a₃ ≤ 2 by simp [← mul_div]; linarith
  suffices 1 + a₁⁻¹ ≤ 2 ∧ 0 < a₃ ∧ 2 * a₃ ≤ 2 from
    ⟨(mul_le_mul_right (by field_simp [a₃] at *; tauto)).2 (by linarith), this.2.2⟩
  exact ⟨
    by aesop (add safe (by linarith)),
    by field_simp [a₂, a₃]; exact heq,
    by aesop (add safe [(by rw [div_le_one]), (by omega)])
  ⟩

lemma johnson_hyp_implies_div_ineq {n d e : ℕ}
  (hn : 0 < n)
  (h_dn : d ≤ n)
  (h : (e : ℝ) ≤ n - Real.sqrt (n * (n - d)))
  :
  1 - (d : ℝ) / n ≤ (1 - (e : ℝ) / n) ^ 2 := by
  have h_sqrt_le :
      Real.sqrt ((n * (n - d)) : ℝ) ≤ (n : ℝ) - e := by
    linarith [h]
  have h_sqrt_nonneg :
      (0 : ℝ) ≤ Real.sqrt ((n * (n - d)) : ℝ) := by
    exact Real.sqrt_nonneg _
  have h_nd_nonneg : (0 : ℝ) ≤ (n : ℝ) - d := by
    exact sub_nonneg.mpr (by exact_mod_cast h_dn)
  have h_nnd_nonneg : (0 : ℝ) ≤ (n : ℝ) * (n - d) := by
    exact mul_nonneg (by exact_mod_cast (Nat.cast_nonneg n)) h_nd_nonneg
  have h_sq_le :
      (n * (n - d) : ℝ) ≤ ((n : ℝ) - e) ^ 2 := by
    have h_sq := mul_self_le_mul_self h_sqrt_nonneg h_sqrt_le
    have h_sq' :
        (Real.sqrt (n * (n - d) : ℝ)) ^ 2 ≤ ((n : ℝ) - e) ^ 2 := by
      rw [pow_two, pow_two]
      exact h_sq
    have h_sq'' := h_sq'
    rw [Real.sq_sqrt h_nnd_nonneg] at h_sq''
    exact h_sq''
  have hn_pos_real : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hn_ne_real : (n : ℝ) ≠ 0 := by exact ne_of_gt hn_pos_real
  have h_div :
      (n * (n - d) : ℝ) / n ^ 2 ≤ ((n : ℝ) - e) ^ 2 / n ^ 2 := by
    exact (div_le_div_of_nonneg_right h_sq_le (by nlinarith [hn_pos_real]))
  have h_left :
      (n * (n - d) : ℝ) / n ^ 2 = 1 - (d : ℝ) / n := by
    field_simp [hn_ne_real]
    ring
  have h_right :
      ((n : ℝ) - e) ^ 2 / n ^ 2 = (1 - (e : ℝ) / n) ^ 2 := by
    field_simp [hn_ne_real]
  simpa [h_left, h_right] using h_div

lemma johnson_e_div_ne_J {n d e : ℕ} {q : ℚ}
  (hn_pos : 0 < n)
  (hd_pos : 0 < d)
  (hq : 1 < q)
  (h_muln : ((e : ℚ) / n : ℝ) ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt)
  (h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J' q (d / n))
  (hqx : q / (q - 1) * (d / n) ≤ 1) :
  ((e : ℚ) / n : ℝ) ≠ J' q (d / n) := by
  intro h_eq
  have h_eq' : (1 - ((1 - (d : ℚ) / n) : ℝ).sqrt) = J' q (d / n) := by
    apply le_antisymm
    · exact h_J_bound
    · calc
        J' q (d / n) = ((e : ℚ) / n : ℝ) := by symm; exact h_eq
        _ ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt := h_muln
  set δ : ℚ := d / n
  set frac : ℚ := q / (q - 1)
  have h_eqJ :
      (1 - ((1 - δ) : ℝ).sqrt) =
        (1 / frac) * (1 - Real.sqrt (1 - frac * δ)) := by
    simpa [J', δ, frac] using h_eq'
  have hδ_pos : (0 : ℚ) < δ := by
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd_pos
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn_pos
    simpa [δ] using (div_pos hdq hnq)
  have hδ_ne : (δ : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hδ_pos)
  have hδ_nonneg : (0 : ℚ) ≤ δ := by
    exact le_of_lt hδ_pos
  have hfrac_gt : (1 : ℚ) < frac := by
    have hq1 : (0 : ℚ) < q - 1 := by linarith [hq]
    have hq' : (q - 1) < q := by linarith
    simpa [frac] using (one_lt_div hq1).2 hq'
  have hfrac_ge : (1 : ℚ) ≤ frac := by exact le_of_lt hfrac_gt
  have hfrac_ne1 : (frac : ℝ) ≠ 1 := by
    exact ne_of_gt (by exact_mod_cast hfrac_gt)
  have hfrac_ne0 : (frac : ℝ) ≠ 0 := by
    have hfrac_pos : (0 : ℚ) < frac := by linarith [hfrac_gt]
    exact ne_of_gt (by exact_mod_cast hfrac_pos)
  have hqx' : frac * δ ≤ 1 := by
    simpa [frac, δ] using hqx
  have hδ_le_fracδ : δ ≤ frac * δ := by
    have := mul_le_mul_of_nonneg_right hfrac_ge hδ_nonneg
    simpa [one_mul] using this
  have hδ_le_one : δ ≤ 1 := by exact le_trans hδ_le_fracδ hqx'
  have hpos_left : (0 : ℝ) ≤ 1 - (δ : ℝ) := by
    exact_mod_cast (by linarith [hδ_le_one])
  have hpos_right : (0 : ℝ) ≤ 1 - (frac : ℚ) * δ := by
    exact_mod_cast (by linarith [hqx'])
  have hden_left : (1 : ℝ) + Real.sqrt (1 - (δ : ℝ)) ≠ 0 := by
    have : (0 : ℝ) ≤ Real.sqrt (1 - (δ : ℝ)) := by
      exact Real.sqrt_nonneg _
    linarith
  have hden_right :
      (1 : ℝ) + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) ≠ 0 := by
    have : (0 : ℝ) ≤ Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) := by
      exact Real.sqrt_nonneg _
    linarith
  have h_left :
      1 - Real.sqrt (1 - (δ : ℝ)) =
        (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) := by
    have h :=
      division_by_conjugate' (a := (1 : ℝ)) (b := 1 - (δ : ℝ)) hpos_left hden_left
    calc
      1 - Real.sqrt (1 - (δ : ℝ))
          = ((1 : ℝ)^2 - (1 - (δ : ℝ))) /
              (1 + Real.sqrt (1 - (δ : ℝ))) := by
            simpa using h
      _ = (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) := by
            ring
  have h_right :
      1 - Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
        ((frac : ℝ) * (δ : ℝ)) /
          (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
    have h :=
      division_by_conjugate' (a := (1 : ℝ)) (b := 1 - (frac : ℝ) * (δ : ℝ))
        hpos_right hden_right
    calc
      1 - Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))
          = ((1 : ℝ)^2 - (1 - (frac : ℝ) * (δ : ℝ))) /
              (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
            simpa using h
      _ = ((frac : ℝ) * (δ : ℝ)) /
            (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
            ring
  have h_eq_div := h_eqJ
  simp [h_left, h_right] at h_eq_div
  have h_eq_div' :
      (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) =
        (δ : ℝ) / (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
    simpa [div_eq_mul_inv, hfrac_ne0, mul_comm, mul_left_comm, mul_assoc] using h_eq_div
  have h_eq_mul :
      (δ : ℝ) * (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) =
        (δ : ℝ) * (1 + Real.sqrt (1 - (δ : ℝ))) := by
    exact (div_eq_div_iff hden_left hden_right).1 h_eq_div'
  have h_eq_den :
      1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
        1 + Real.sqrt (1 - (δ : ℝ)) := by
    exact mul_left_cancel₀ hδ_ne h_eq_mul
  have h_sqrt_eq :
      Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
        Real.sqrt (1 - (δ : ℝ)) := by
    exact add_left_cancel h_eq_den
  have h_sq := congrArg (fun x => x^2) h_sqrt_eq
  simp [Real.sq_sqrt hpos_right, Real.sq_sqrt hpos_left] at h_sq
  have h_mul_eq : (frac : ℝ) * (δ : ℝ) = (δ : ℝ) := by
    linarith [h_sq]
  have h_mul_eq' : (frac : ℝ) * (δ : ℝ) = (1 : ℝ) * (δ : ℝ) := by
    simpa using h_mul_eq
  have hfrac_eq : (frac : ℝ) = 1 := by
    exact mul_right_cancel₀ hδ_ne h_mul_eq'
  exact hfrac_ne1 hfrac_eq

lemma johnson_worst_case_bound {n : ℕ} {F : Type*} [DecidableEq F]
  {B : Finset (Fin n → F)} {v : Fin n → F} {d e : ℕ} {frac : ℚ}
  (hn_pos : (0 : ℚ) < n)
  (hd_pos : 0 < d)
  (d_le_n : d ≤ n)
  (h : (e : ℝ) ≤ n - ((n * (n - d)) : ℝ).sqrt)
  (h_d_close_n : frac * (d / n : ℚ) ≤ 1)
  (hfrac_gt1 : (1 : ℚ) < frac)
  (e_ineq : JohnsonBound.e B v ≤ e)
  (d_ineq : (d : ℚ) ≤ JohnsonBound.d B)
  (quad_nonneg : (0 : ℚ) ≤ (d / n : ℚ) - 2 * (e / n : ℚ) + (e / n : ℚ) ^ 2)
  (hden1_pos :
      (0 : ℚ) <
        JohnsonBound.d B / n - 2 * JohnsonBound.e B v / n +
          frac * (JohnsonBound.e B v / n) ^ 2) :
  (JohnsonBound.d B / n) /
      (JohnsonBound.d B / n - 2 * JohnsonBound.e B v / n +
      frac * (JohnsonBound.e B v / n)^2) ≤
      (d / n) / (d / n - 2 * e / n + frac * (e / n)^2) := by
  set D0 : ℚ := d / n
  set E0 : ℚ := e / n
  set D1 : ℚ := JohnsonBound.d B / n
  set E1 : ℚ := JohnsonBound.e B v / n
  have hn_nonneg : (0 : ℚ) ≤ n := by exact le_of_lt hn_pos
  have hfrac_pos : (0 : ℚ) < frac := by linarith [hfrac_gt1]
  have hfrac_ge : (1 : ℚ) ≤ frac := by exact le_of_lt hfrac_gt1
  have hD : D0 ≤ D1 := by
    simpa [D0, D1] using (div_le_div_of_nonneg_right d_ineq hn_nonneg)
  have hE : E1 ≤ E0 := by
    simpa [E1, E0] using (div_le_div_of_nonneg_right e_ineq hn_nonneg)
  have h_sqrt_ge :
      (n : ℝ) - d ≤ Real.sqrt ((n * (n - d)) : ℝ) := by
    have h_nd_nonneg : (0 : ℝ) ≤ (n : ℝ) - d := by
      exact sub_nonneg.mpr (by exact_mod_cast d_le_n)
    have h_nd_le_n : (n : ℝ) - d ≤ (n : ℝ) := by linarith
    have h_sq : ((n : ℝ) - d) ^ 2 ≤ (n : ℝ) * (n - d) := by
      have hmul := mul_le_mul_of_nonneg_right h_nd_le_n h_nd_nonneg
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact Real.le_sqrt_of_sq_le h_sq
  have h_e_le_d_real : (e : ℝ) ≤ d := by
    linarith [h, h_sqrt_ge]
  have h_e_le_d : (e : ℚ) ≤ (d : ℚ) := by
    exact_mod_cast h_e_le_d_real
  have hE0_le_D0 : E0 ≤ D0 := by
    simpa [E0, D0] using (div_le_div_of_nonneg_right h_e_le_d hn_nonneg)
  have hD0_le_one_frac : D0 ≤ 1 / frac := by
    have hmul : D0 * frac ≤ 1 := by
      have h' : frac * (d / n : ℚ) ≤ 1 := by
        exact h_d_close_n
      simpa [D0, mul_comm] using h'
    exact (le_div_iff₀ hfrac_pos).2 (by simpa using hmul)
  have hE0_le_one_frac : E0 ≤ 1 / frac := by
    exact le_trans hE0_le_D0 hD0_le_one_frac
  have hE1_le_one_frac : E1 ≤ 1 / frac := by
    exact le_trans hE hE0_le_one_frac
  have hE0_nonneg : (0 : ℚ) ≤ E0 := by
    have hE0_nonneg_nat : (0 : ℚ) ≤ (e : ℚ) := by
      exact_mod_cast (Nat.zero_le e)
    exact div_nonneg hE0_nonneg_nat hn_nonneg
  have hsum_nonneg :
      (0 : ℚ) ≤ ∑ x ∈ B, (Δ₀(v, x) : ℚ) := by
    refine Finset.sum_nonneg ?_
    intro x hx
    exact_mod_cast (Nat.cast_nonneg (Δ₀(v, x)))
  have hE_nonneg : (0 : ℚ) ≤ JohnsonBound.e B v := by
    have hB_nonneg : (0 : ℚ) ≤ (B.card : ℚ) := by
      exact_mod_cast (Nat.cast_nonneg B.card)
    have hB_inv_nonneg : (0 : ℚ) ≤ (1 : ℚ) / B.card := by
      exact div_nonneg (show (0 : ℚ) ≤ (1 : ℚ) by norm_num) hB_nonneg
    simpa [JohnsonBound.e, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (mul_nonneg hB_inv_nonneg hsum_nonneg)
  have hE1_nonneg : (0 : ℚ) ≤ E1 := by
    exact div_nonneg hE_nonneg hn_nonneg
  have hden1_pos' : (0 : ℚ) < D1 - 2 * E1 + frac * E1 ^ 2 := by
    simpa [D1, E1, mul_div_assoc] using hden1_pos
  have hden0_nonneg :
      (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
    simpa [D0, E0] using quad_nonneg
  have hden0_pos :
      (0 : ℚ) < D0 - 2 * E0 + frac * E0 ^ 2 := by
    have h_expand :
        D0 - 2 * E0 + frac * E0 ^ 2 =
          (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
      ring
    by_cases hE0_zero : E0 = 0
    · have hd_pos_q : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd_pos
      have hD0_pos : (0 : ℚ) < D0 := by
        simpa [D0] using (div_pos hd_pos_q hn_pos)
      simpa [h_expand, hE0_zero] using hD0_pos
    · have hE0_sq_pos : (0 : ℚ) < E0 ^ 2 := by
        have hE0_sq_pos' : (0 : ℚ) < E0 * E0 := by
          exact mul_self_pos.mpr hE0_zero
        simpa [pow_two] using hE0_sq_pos'
      have hfrac1_pos : (0 : ℚ) < frac - 1 := by
        linarith [hfrac_gt1]
      have hterm_pos :
          (0 : ℚ) < (frac - 1) * E0 ^ 2 := by
        exact mul_pos hfrac1_pos hE0_sq_pos
      have hden0_pos' :
          (0 : ℚ) <
            (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
        linarith [hden0_nonneg, hterm_pos]
      simpa [h_expand] using hden0_pos'
  have hE_sum : E0 + E1 ≤ 2 / frac := by
    calc
      E0 + E1 ≤ (1 / frac) + (1 / frac) := by
        linarith [hE0_le_one_frac, hE1_le_one_frac]
      _ = 2 / frac := by ring
  have h_gmono :
      D0 - 2 * E1 + frac * E1 ^ 2 ≥ D0 - 2 * E0 + frac * E0 ^ 2 := by
    have h1 : (0 : ℚ) ≤ E0 - E1 := by linarith [hE]
    have h2 : (0 : ℚ) ≤ 2 - frac * (E0 + E1) := by
      have hmul :
          frac * (E0 + E1) ≤ 2 := by
        have h := mul_le_mul_of_nonneg_left hE_sum (le_of_lt hfrac_pos)
        have hfrac_ne : (frac : ℚ) ≠ 0 := by exact ne_of_gt hfrac_pos
        have hright : frac * (2 / frac) = (2 : ℚ) := by
          field_simp [hfrac_ne]
        simpa [hright] using h
      linarith [hmul]
    have hdiff :
        (0 : ℚ) ≤ (E0 - E1) * (2 - frac * (E0 + E1)) := by
      exact mul_nonneg h1 h2
    have hfactor :
        (D0 - 2 * E1 + frac * E1 ^ 2) - (D0 - 2 * E0 + frac * E0 ^ 2) =
          (E0 - E1) * (2 - frac * (E0 + E1)) := by
      ring
    have hdiff' :
        (0 : ℚ) ≤
          (D0 - 2 * E1 + frac * E1 ^ 2) - (D0 - 2 * E0 + frac * E0 ^ 2) := by
      simpa [hfactor] using hdiff
    linarith [hdiff']
  have hden0_pos' :
      (0 : ℚ) < D0 - 2 * E1 + frac * E1 ^ 2 := by
    exact lt_of_lt_of_le hden0_pos h_gmono
  have hC_nonneg :
      (0 : ℚ) ≤ 2 * E1 - frac * E1 ^ 2 := by
    have hmul :
        frac * E1 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hE1_le_one_frac (le_of_lt hfrac_pos)
      have hfrac_ne : (frac : ℚ) ≠ 0 := by exact ne_of_gt hfrac_pos
      have hright : frac * frac⁻¹ = (1 : ℚ) := by
        field_simp [hfrac_ne]
      simpa [div_eq_mul_inv, hright, mul_assoc] using h
    have h2 : (0 : ℚ) ≤ 2 - frac * E1 := by
      linarith [hmul]
    have hprod : (0 : ℚ) ≤ E1 * (2 - frac * E1) := by
      exact mul_nonneg hE1_nonneg h2
    have hfactor : E1 * (2 - frac * E1) = 2 * E1 - frac * E1 ^ 2 := by
      ring
    simpa [hfactor] using hprod
  have hstep1 :
      D1 / (D1 - 2 * E1 + frac * E1 ^ 2) ≤
      D0 / (D0 - 2 * E1 + frac * E1 ^ 2) := by
    have hmul :
        D1 * (D0 - 2 * E1 + frac * E1 ^ 2) ≤
        D0 * (D1 - 2 * E1 + frac * E1 ^ 2) := by
      have h : (0 : ℚ) ≤ (D1 - D0) := by linarith [hD]
      have h' : (0 : ℚ) ≤ (2 * E1 - frac * E1 ^ 2) := hC_nonneg
      nlinarith [h, h']
    exact (div_le_div_iff₀ hden1_pos' hden0_pos').2 hmul
  have hstep2 :
      D0 / (D0 - 2 * E1 + frac * E1 ^ 2) ≤
      D0 / (D0 - 2 * E0 + frac * E0 ^ 2) := by
    have hmul :
        D0 * (D0 - 2 * E0 + frac * E0 ^ 2) ≤
        D0 * (D0 - 2 * E1 + frac * E1 ^ 2) := by
      have hD0_nonneg : (0 : ℚ) ≤ D0 := by
        have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
        exact div_nonneg hd0 hn_nonneg
      exact mul_le_mul_of_nonneg_left h_gmono hD0_nonneg
    exact (div_le_div_iff₀ hden0_pos' hden0_pos).2 hmul
  have hfinal :
      D1 / (D1 - 2 * E1 + frac * E1 ^ 2) ≤
      D0 / (D0 - 2 * E0 + frac * E0 ^ 2) := by
    exact le_trans hstep1 hstep2
  simpa [D0, D1, E0, E1, mul_div_assoc] using hfinal

lemma johnson_den_ge_frac_d {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} {v : Fin n → F} :
  (1 -
      ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.e B v / n)) ^ 2
      - (1 -
        ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n))
    ≥ ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n) - 1 := by
  have hsq :
      (0 : ℚ) ≤
        (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.e B v / n)) ^ 2 := by
    exact sq_nonneg _
  calc
    (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.e B v / n)) ^ 2
        - (1 -
          ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n))
        =
        (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.e B v / n)) ^ 2
          - 1
          + ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n) := by
      ring
    _ ≥ (-1) + ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n) := by
      linarith [hsq]
    _ = ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n) - 1 := by
      ring

lemma johnson_gap_frac_d_gt_one {n d : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)}
  (q_not_small : (2 : ℚ) ≤ (Fintype.card F : ℚ))
  (n_not_small : (1 : ℕ) ≤ n)
  (h_d_close_n :
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d / n : ℚ) > 1)
  (hd_le_dB : (d : ℚ) ≤ JohnsonBound.d B) :
  (1 : ℚ) / ((n : ℚ) * ((Fintype.card F : ℚ) - 1)) ≤
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B) / n - 1 := by
  set q : ℚ := (Fintype.card F : ℚ)
  set frac : ℚ := q / (q - 1)
  have q_not_small' : (2 : ℚ) ≤ q := by
    simpa [q] using q_not_small
  have h_d_close_n' : frac * (d / n : ℚ) > 1 := by
    simpa [q, frac] using h_d_close_n
  have hgap_q :
      (1 : ℚ) / ((n : ℚ) * (q - 1)) ≤ frac * (JohnsonBound.d B) / n - 1 := by
    have hq1_pos : (0 : ℚ) < q - 1 := by
      linarith [q_not_small']
    have hn_pos : (0 : ℚ) < n := by
      have hn' : (1 : ℚ) ≤ n := by exact_mod_cast n_not_small
      linarith
    have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
    have hn_ne : (n : ℚ) ≠ 0 := by exact ne_of_gt hn_pos
    have hqd_gt : (q - 1) * (n : ℚ) < q * (d : ℚ) := by
      have h' := h_d_close_n'
      field_simp [frac, hq1_ne, hn_ne] at h'
      have hden_pos : (0 : ℚ) < (q - 1) * n := by
        exact mul_pos hq1_pos hn_pos
      have h'' :
          (1 : ℚ) * ((q - 1) * n) < q * (d : ℚ) :=
        (_root_.lt_div_iff₀ hden_pos).1 h'
      simpa [mul_comm, mul_left_comm, mul_assoc] using h''
    have hF2 : (2 : ℕ) ≤ Fintype.card F := by
      exact_mod_cast (by simpa [q] using q_not_small')
    have hF1 : (1 : ℕ) ≤ Fintype.card F := by omega
    have hqd_gt' :
        ((Fintype.card F : ℚ) * (d : ℚ) >
          ((Fintype.card F - 1 : ℕ) : ℚ) * (n : ℚ)) := by
      have hqd_gt'' :
          ((Fintype.card F : ℚ) * (d : ℚ) >
            ((Fintype.card F : ℚ) - 1) * (n : ℚ)) := by
        simpa [q] using hqd_gt
      simpa [Nat.cast_sub hF1] using hqd_gt''
    have hqd_gt_nat :
        (Fintype.card F) * d > (Fintype.card F - 1) * n := by
      exact_mod_cast hqd_gt'
    have hqd_ge_nat :
        (Fintype.card F - 1) * n ≤ (Fintype.card F) * d :=
      Nat.le_of_lt hqd_gt_nat
    have hnum_ge_nat :
        1 ≤ (Fintype.card F) * d - (Fintype.card F - 1) * n := by
      exact (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hqd_gt_nat)
    have hnum_ge_q :
        (1 : ℚ) ≤ q * (d : ℚ) - (q - 1) * (n : ℚ) := by
      have hnum_ge_q' :
          (1 : ℚ) ≤
            ((Fintype.card F) * d - (Fintype.card F - 1) * n : ℚ) := by
        exact_mod_cast hnum_ge_nat
      simpa [q, Nat.cast_sub hF1, Nat.cast_sub hqd_ge_nat, Nat.cast_mul] using hnum_ge_q'
    have hgap_d : (1 : ℚ) / ((n : ℚ) * (q - 1)) ≤ frac * (d : ℚ) / n - 1 := by
      have hden_nonneg : (0 : ℚ) ≤ (q - 1) * n := by
        exact mul_nonneg (le_of_lt hq1_pos) (le_of_lt hn_pos)
      calc
        (1 : ℚ) / ((n : ℚ) * (q - 1))
            = (1 : ℚ) / ((q - 1) * n) := by
                simp [mul_comm]
        _ ≤ (q * (d : ℚ) - (q - 1) * (n : ℚ)) / ((q - 1) * n) := by
                exact div_le_div_of_nonneg_right hnum_ge_q hden_nonneg
        _ = frac * (d : ℚ) / n - 1 := by
                field_simp [frac, hq1_ne, hn_ne]
    have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
    have hfrac_nonneg : (0 : ℚ) ≤ frac := by
      have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small']
      have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small']
      exact div_nonneg hq_nonneg hq1_nonneg
    have h_div_le : (d : ℚ) / n ≤ JohnsonBound.d B / n := by
      exact div_le_div_of_nonneg_right hd_le_dB hn_nonneg
    have h_mul_le' :
        frac * (d / n) ≤ frac * (JohnsonBound.d B / n) := by
      exact mul_le_mul_of_nonneg_left h_div_le hfrac_nonneg
    have h_mul_le :
        frac * (d : ℚ) / n ≤ frac * (JohnsonBound.d B) / n := by
      simpa [mul_div_assoc] using h_mul_le'
    have h_mul_le' :
        frac * (d : ℚ) / n - 1 ≤ frac * (JohnsonBound.d B) / n - 1 := by
      linarith [h_mul_le]
    exact le_trans hgap_d h_mul_le'
  simpa [q, frac] using hgap_q

lemma johnson_den_lb_e_zero {n d : ℕ} {q : ℚ}
  (hn_pos : 0 < n)
  (hq_ge1 : (1 : ℚ) ≤ q)
  (hd_ge1 : (1 : ℚ) ≤ (d : ℚ)) :
  (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (d : ℚ) / n := by
  have hn_pos_q : (0 : ℚ) < n := by exact_mod_cast hn_pos
  have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
  have hn_ge1 : (1 : ℚ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff).2 hn_pos
  have hq_pos : (0 : ℚ) < q := by linarith [hq_ge1]
  have hn2_pos : (0 : ℚ) < (n : ℚ) ^ 2 := by
    exact pow_pos hn_pos_q _
  have hD0_ge : (1 : ℚ) / n ≤ (d : ℚ) / n := by
    exact div_le_div_of_nonneg_right hd_ge1 hn_nonneg
  have hmul : (n : ℚ) ≤ q * (n : ℚ) ^ 2 := by
    calc
      (n : ℚ) ≤ (n : ℚ) * (n : ℚ) := by nlinarith [hn_ge1]
      _ ≤ q * (n : ℚ) * (n : ℚ) := by
        have hnn_nonneg : (0 : ℚ) ≤ (n : ℚ) * (n : ℚ) := by
          exact mul_nonneg (le_of_lt hn_pos_q) (le_of_lt hn_pos_q)
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_right hq_ge1 hnn_nonneg)
      _ = q * (n : ℚ) ^ 2 := by ring
  have hpos1 : (0 : ℚ) < q * (n : ℚ) ^ 2 := by
    exact mul_pos hq_pos hn2_pos
  have hpos2 : (0 : ℚ) < (n : ℚ) := hn_pos_q
  have h1 : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (1 : ℚ) / n := by
    exact (div_le_div_iff₀ hpos1 hpos2).2 (by simpa using hmul)
  exact le_trans h1 hD0_ge

lemma johnson_den_lb_e_pos {n d e : ℕ} {q frac : ℚ}
  (hn_pos : (0 : ℚ) < n)
  (hn_nonneg : (0 : ℚ) ≤ n)
  (hn2_nonneg : (0 : ℚ) ≤ (n : ℚ) ^ 2)
  (hq_ne : (q : ℚ) ≠ 0)
  (one_div_q_le : (1 : ℚ) / q ≤ frac - 1)
  (hfrac1_pos : (0 : ℚ) < frac - 1)
  (hbase_nonneg :
    (0 : ℚ) ≤ (d / n : ℚ) - 2 * (e / n : ℚ) + (e / n : ℚ) ^ 2)
  (he0 : e ≠ 0) :
  (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤
    (d / n : ℚ) - 2 * (e / n : ℚ) + frac * (e / n : ℚ) ^ 2 := by
  set D0 : ℚ := d / n
  set E0 : ℚ := e / n
  set Den : ℚ := D0 - 2 * E0 + frac * E0 ^ 2
  have hbase_nonneg' : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
    simpa [D0, E0] using hbase_nonneg
  have he_pos_nat : 0 < e := Nat.pos_of_ne_zero he0
  have he_pos : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he_pos_nat
  have hE0_pos : (0 : ℚ) < E0 := by exact div_pos he_pos hn_pos
  have hE0_ge : (1 : ℚ) / n ≤ E0 := by
    have he_ge1 : (1 : ℚ) ≤ (e : ℚ) := by
      exact_mod_cast (Nat.succ_le_iff).2 he_pos_nat
    exact (div_le_div_of_nonneg_right he_ge1 hn_nonneg)
  have hE0_sq_ge : (1 : ℚ) / (n : ℚ) ^ 2 ≤ E0 ^ 2 := by
    have h1 : (0 : ℚ) ≤ (1 : ℚ) / n := by
      exact div_nonneg (by norm_num) hn_nonneg
    have h := mul_self_le_mul_self h1 hE0_ge
    simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have h_expand : Den = (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
    ring
  have hden_ge :
      (frac - 1) * E0 ^ 2 ≤ Den := by
    have htmp :
        (frac - 1) * E0 ^ 2 ≤
          (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
      linarith [hbase_nonneg']
    simpa [h_expand] using htmp
  have hden_ge' : (frac - 1) / (n : ℚ) ^ 2 ≤ Den := by
    have h1 :
        (frac - 1) * ((1 : ℚ) / (n : ℚ) ^ 2) ≤
          (frac - 1) * E0 ^ 2 := by
      exact mul_le_mul_of_nonneg_left hE0_sq_ge (le_of_lt hfrac1_pos)
    have h1' :
        (frac - 1) / (n : ℚ) ^ 2 =
          (frac - 1) * ((1 : ℚ) / (n : ℚ) ^ 2) := by
      simp [div_eq_mul_inv]
    exact le_trans (by simpa [h1'] using h1) hden_ge
  have hfrac1_ge' :
      (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (frac - 1) / (n : ℚ) ^ 2 := by
    have h1 := div_le_div_of_nonneg_right one_div_q_le hn2_nonneg
    have h1' : (1 : ℚ) / (q * (n : ℚ) ^ 2) = (1 : ℚ) / q / (n : ℚ) ^ 2 := by
      field_simp [hq_ne]
    simpa [h1'] using h1
  have hfinal : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ Den :=
    le_trans hfrac1_ge' hden_ge'
  simpa [D0, E0, Den] using hfinal

lemma johnson_qdn_ge_two {q : ℚ} {d n : ℕ}
  (hq : (2 : ℚ) ≤ q)
  (hd : (1 : ℕ) ≤ d)
  (hn : (1 : ℕ) ≤ n) :
  (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by
  have hdq : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hdn : (1 : ℚ) ≤ (d : ℚ) * (n : ℚ) := by nlinarith [hdq, hnq]
  have : (2 : ℚ) ≤ q * ((d : ℚ) * (n : ℚ)) := by nlinarith [hq, hdn]
  simpa [mul_assoc] using this

lemma johnson_d_le_n {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} (hB : 2 ≤ B.card) :
  JohnsonBound.d B ≤ (n : ℚ) := by
  classical
  have hB2_card :
      2 * choose_2 (B.card : ℚ) =
        {x ∈ B ×ˢ B | x.1 ≠ x.2}.card := by
    simp
    unfold choose_2
    ring_nf
    have BBcard : (B ×ˢ B).card = B.card ^ 2 := by
      rw [Finset.card_product, sq]
    have BBdiagcard : {x ∈ B ×ˢ B | x.1 = x.2}.card = B.card := by
      simp
    have BBdisjoint :
        {x ∈ B ×ˢ B | x.1 = x.2} ∩ {x ∈ B ×ˢ B | x.1 ≠ x.2} = ∅ := by
      ext x
      simp
      tauto
    have BBunion :
        B ×ˢ B =
          {x ∈ B ×ˢ B | x.1 = x.2} ∪ {x ∈ B ×ˢ B | x.1 ≠ x.2} := by
      ext ⟨a, b⟩
      simp
      tauto
    have BBcount :
        {x ∈ B ×ˢ B | x.1 ≠ x.2}.card
          = (B ×ˢ B).card - {x ∈ B ×ˢ B | x.1 = x.2}.card := by
      rw [BBunion, Finset.card_union, BBdiagcard, BBdisjoint]
      have doubleindex1 :
          {x ∈ {x ∈ B ×ˢ B | x.1 = x.2} ∪
              {x ∈ B ×ˢ B | x.1 ≠ x.2} | x.1 = x.2}
            = {x ∈ B ×ˢ B | x.1 = x.2} := by
        ext x
        simp
        tauto
      have doubleindex2 :
          {x ∈ {x ∈ B ×ˢ B | x.1 = x.2} ∪
              {x ∈ B ×ˢ B | x.1 ≠ x.2} | x.1 ≠ x.2}
            = {x ∈ B ×ˢ B | x.1 ≠ x.2} := by
        ext x
        simp
        tauto
      rw [doubleindex1, BBdiagcard]
      simp
      rw [doubleindex2]
    rw [BBcount, BBcard, BBdiagcard]
    rw [Nat.cast_sub]
    ring_nf
    rfl
    nlinarith [sq_nonneg (B.card - 1)]
  have hdist_le :
      ∀ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2},
        (Δ₀(x.1, x.2) : ℚ) ≤ n := by
    intro x hx
    have : Δ₀(x.1, x.2) ≤ n := by
      simpa using (hammingDist_le_card_fintype (x := x.1) (y := x.2))
    exact_mod_cast this
  have hsum_le :
      ∑ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
        ≤ (n : ℚ) * ({x ∈ B ×ˢ B | x.1 ≠ x.2}.card) := by
    calc
      ∑ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
          ≤ ∑ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2}, (n : ℚ) := by
            exact Finset.sum_le_sum hdist_le
      _ = (n : ℚ) * ({x ∈ B ×ˢ B | x.1 ≠ x.2}.card) := by
            simp [Finset.sum_const, mul_comm]
  have hsum_le' :
      ∑ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
        ≤ (n : ℚ) * (2 * choose_2 (B.card : ℚ)) := by
    simpa [hB2_card, mul_comm, mul_left_comm, mul_assoc] using hsum_le
  have hB_gt : 1 < B.card := by
    omega
  have hS_nonempty :
      {x ∈ B ×ˢ B | x.1 ≠ x.2}.Nonempty := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB_gt
    refine ⟨⟨u, v⟩, ?_⟩
    simp [hu, hv, huv]
  have hden_pos : (0 : ℚ) < 2 * choose_2 (B.card : ℚ) := by
    have hS_pos : (0 : ℚ) < {x ∈ B ×ˢ B | x.1 ≠ x.2}.card := by
      exact_mod_cast (Finset.card_pos.mpr hS_nonempty)
    simpa [hB2_card] using hS_pos
  have hdiv_le :
      (∑ x ∈ {x ∈ B ×ˢ B | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)) /
        (2 * choose_2 (B.card : ℚ)) ≤ (n : ℚ) := by
    exact (_root_.div_le_iff₀ hden_pos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_le')
  simpa [JohnsonBound.d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hdiv_le

end

end JohnsonBound
