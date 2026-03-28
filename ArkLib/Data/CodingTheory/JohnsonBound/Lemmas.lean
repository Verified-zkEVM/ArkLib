/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import Mathlib
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations

namespace JohnsonBound

/-- The function used for `q`-ary Johnson Bound (local copy for lemmas). -/
noncomputable def J' (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - Real.sqrt (1 - frac * δ))

/-- A lemma for proving sqrt_le_J (local copy for lemmas). -/
@[simp, grind]
lemma division_by_conjugate' {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
    a - b.sqrt = (a ^ 2 - b) / (a + b.sqrt) := by
  grind only [usr Real.sq_sqrt', = max_def]

section

variable {n : ℕ}
variable {F : Type*} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {i : Fin n}

private def Fi (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset (Fin n → F) :=
  { x | x ∈ B ∧ x i = α }

private abbrev K (B : Finset (Fin n → F)) (i : Fin n) (α : F) : ℕ :=
  (Fi B i α).card

@[simp, grind]
private lemma Fis_cover_B : B = Finset.univ.biUnion (Fi B i) := by
  aesop (add simp [Fi])

@[simp, grind]
private lemma Fis_pairwise_disjoint : Set.PairwiseDisjoint Set.univ (Fi B i) := by
  unfold Fi
  rintro x - y - h₁ _ h₂ h₃ _ contra
  specialize h₂ contra; specialize h₃ contra; aesop

@[simp]
private lemma sum_K_eq_card : ∑ (α : F), K B i α = B.card := by
  rw (occs := [2]) [Fis_cover_B (B := B) (i := i)]
  rw [Finset.card_biUnion (by simp [Fis_pairwise_disjoint])]

@[simp, grind]
private lemma K_eq_sum {α : F} :
    K B i α = ∑ (x : B), if x.1 i = α then 1 else 0 := by
  simp only [K, Fi, Finset.univ_eq_attach, Finset.sum_boole, Nat.cast_id]
  simp_rw [Finset.card_filter, Finset.sum_attach_eq_sum_dite]
  exact Finset.sum_congr rfl (by aesop)

@[simp]
private lemma K_le_card {α : F} : K B i α ≤ B.card := by
  simp [K, Fi]
  exact Finset.card_le_card fun _ ha ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ha.1

open Finset in
private lemma sum_choose_K' [Zero F] (h_card : 2 ≤ Fintype.card F) :
    (Fintype.card (α := F) - 1) * choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤
    ∑ (α : F) with α ≠ 0, choose_2 (K B i α) := by
  rw [← sum_K_eq_card (i := i), Nat.cast_sum]
  set x1 : ℚ := Fintype.card F - 1
  have hx1 : x1 ≠ 0 := by simp [x1, sub_eq_zero]; omega
  set x2 := K B i
  suffices x1 * choose_2 (∑ x with x ≠ 0, (fun _ ↦ x1⁻¹) x • (Nat.cast (R := ℚ) ∘ x2) x) ≤
      ∑ α with α ≠ 0, choose_2 ↑(x2 α) by
    simp only [ne_eq, Function.comp_apply, smul_eq_mul] at this; convert this
    rw [sum_eq_sum_diff_singleton_add (i := 0) (by simp)]
    ring_nf; rw [sum_mul]
    apply sum_congr (ext _)
    all_goals
      grind only [= mem_filter, = mem_sdiff, ← mem_univ, = mem_singleton]
  simp only [Function.comp_apply, smul_eq_mul]
  have hx1_nonneg : (0 : ℚ) ≤ x1 := by simp [x1, sub_nonneg]; omega
  have jensen := ConvexOn.map_sum_le choose_2_convex
    (t := Finset.univ.filter (· ≠ (0 : F))) (w := fun _ ↦ x1⁻¹) (p := fun α => (x2 α : ℚ))
    (by intro _ _; exact inv_nonneg.mpr hx1_nonneg)
    (by simp [x1]; field_simp; exact div_self hx1) (by simp)
  simp only [smul_eq_mul] at jensen
  exact le_trans (mul_le_mul_of_nonneg_left jensen hx1_nonneg) <|
    le_of_eq <| by
      rw [Finset.mul_sum]; congr 1; ext
      rw [← mul_assoc, mul_inv_cancel₀ hx1, one_mul]

@[simp, grind]
private def sum_choose_K_i (B : Finset (Fin n → F)) (i : Fin n) : ℚ :=
  ∑ (α : F), choose_2 (K B i α)

@[simp, grind]
private lemma le_sum_choose_K [Zero F] (h_card : 2 ≤ Fintype.card F) :
    choose_2 (K B i 0) + (Fintype.card (α := F) - 1) *
    choose_2 ((B.card - K B i 0) / (Fintype.card (α := F) - 1)) ≤ sum_choose_K_i B i := by
  simp only [sum_choose_K_i]
  have : ∑ α, choose_2 ↑(K B i α) =
      choose_2 ↑(K B i 0) + ∑ α with α ≠ 0, choose_2 ↑(K B i α) := by
    rw [Finset.sum_eq_sum_diff_singleton_add (i := (0 : F)) (by simp), add_comm]
    exact congr_arg _ (Finset.sum_congr
      (by ext x; simp [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter])
      (fun _ _ => rfl))
  linarith [sum_choose_K' h_card (B := B) (i := i)]

private def k [Zero F] (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ) / n * ∑ i, K B i 0

omit [Fintype F] in
private lemma hamming_weight_eq_sum [Zero F] {x : Fin n → F} :
    ‖x‖₀ = ∑ i, if x i = 0 then 0 else 1 := by simp [hammingNorm, Finset.sum_ite]

@[simp, grind]
private lemma sum_hamming_weight_sum [Zero F] :
    ∑ x ∈ B, (‖x‖₀ : ℚ) = n * B.card - ∑ i, K B i 0 := by
  simp only [hamming_weight_eq_sum, Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    K_eq_sum, Finset.sum_boole, Nat.cast_id]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, eq_sub_iff_add_eq]
  simp_rw [Nat.cast_sum, Nat.cast_ite]
  conv in Finset.sum _ _ => arg 2; ext; arg 2; ext; rw [← ite_not]
  simp_rw [Finset.univ_eq_attach, Finset.sum_attach_eq_sum_dite]
  simp only [Nat.cast_one, CharP.cast_eq_zero, dite_eq_ite, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]
  simp_all only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]

@[simp, grind]
private lemma k_and_e [Zero F] (h_n : n ≠ 0) (h_B : B.card ≠ 0) :
    k B = B.card * (n - e B 0) / n := by
  simp [e, k, sum_hamming_weight_sum]; field_simp; grind only

@[simp, grind]
private lemma k_and_e' [Zero F] (h_n : n ≠ 0) (h_B : B.card ≠ 0) :
    k B / B.card = (n - e B 0) / n := by
  rw [k_and_e h_n h_B]; field_simp

@[simp, grind]
private lemma k_choose_2 [Zero F] {B : Finset (Fin n → F)} (h_n : n ≠ 0) :
    n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1 : ℚ) / n) i • (fun i ↦ K B i 0) i) * n ≤
      ∑ i, choose_2 (K B i 0) by
    rw [mul_comm]; convert this; simp [k, Finset.mul_sum]
  simp only [one_div, smul_eq_mul]
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero h_n
  have jensen := ConvexOn.map_sum_le choose_2_convex
    (t := Finset.univ (α := Fin n)) (w := fun _ ↦ (n : ℚ)⁻¹) (p := fun i => (K B i 0 : ℚ))
    (by intro _ _; exact inv_nonneg.mpr hn_pos.le) (by simp; field_simp) (by simp)
  simp only [smul_eq_mul] at jensen
  exact le_trans (mul_le_mul_of_nonneg_right jensen hn_pos.le)
    (le_of_eq (by rw [Finset.sum_mul]; congr 1; ext x; field_simp))

@[simp, grind]
private def aux_frac (B : Finset (Fin n → F)) (x : ℚ) : ℚ :=
  (B.card - x) / (Fintype.card F - 1)

@[simp, grind]
private lemma sum_1_over_n_aux_frac_k_i [Zero F] (h_n : 0 < n) :
    ∑ i, 1 / n * aux_frac B (K B i 0) = aux_frac B (k B) := by
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp h_n
  simp only [aux_frac, k, ← Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn_ne]; rw [Nat.cast_sum]

@[simp, grind]
private lemma aux_sum [Zero F] (h_n : 0 < n) :
    n * choose_2 (aux_frac B (k B)) ≤
    ∑ i, choose_2 (aux_frac B (K B i 0)) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1 : ℚ) / n) i •
      (fun x ↦ aux_frac B (K B x 0)) i) * ↑n ≤
      ∑ i, choose_2 (JohnsonBound.aux_frac B (JohnsonBound.K B i 0)) by
    rw [← sum_1_over_n_aux_frac_k_i h_n, mul_comm]; convert this
  simp only [one_div, smul_eq_mul]
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast h_n
  have jensen := ConvexOn.map_sum_le choose_2_convex
    (t := Finset.univ (α := Fin n)) (w := fun _ ↦ (n : ℚ)⁻¹)
    (p := fun i => aux_frac B (K B i 0 : ℚ))
    (by intro _ _; exact inv_nonneg.mpr hn_pos.le) (by simp; field_simp) (by simp)
  simp only [smul_eq_mul] at jensen
  exact le_trans (mul_le_mul_of_nonneg_right jensen hn_pos.le)
    (le_of_eq (by rw [Finset.sum_mul]; congr 1; ext x; field_simp))

@[simp, grind]
private lemma le_sum_sum_choose_K [Zero F]
    (h_n : 0 < n) (_ : B.card ≠ 0) (h_card : 2 ≤ Fintype.card F) :
    n * (choose_2 (k B) + (Fintype.card (α := F) - 1) *
      choose_2 ((B.card - k B) / ((Fintype.card (α := F) - 1)))) ≤
    ∑ i, sum_choose_K_i B i := by
  rw [mul_add]
  transitivity
  · simp_all only [ne_eq, Finset.card_eq_zero]; rfl
  · have h3 : ↑n * ((Fintype.card F - 1 : ℚ) *
        choose_2 ((↑B.card - k B) / (Fintype.card F - 1))) =
      (↑(Fintype.card F) - 1) * (↑n * choose_2 (aux_frac B (k B))) := by
      simp [aux_frac]; ring
    rw [h3]
    apply le_trans (add_le_add (k_choose_2 (by omega))
      (mul_le_mul_of_nonneg_left (aux_sum h_n (B := B)) (by simp [sub_nonneg]; omega)))
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun _ _ ↦ le_sum_choose_K h_card

private def F2i (B : Finset (Fin n → F)) (i : Fin n) (α : F) :
    Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = α ∧ x.2 i = α ∧ x.1 ≠ x.2 }

private def Bi (B : Finset (Fin n → F)) (i : Fin n) :
    Finset ((Fin n → F) × (Fin n → F)) :=
  { x | x ∈ B ×ˢ B ∧ x.1 i = x.2 i ∧ x.1 ≠ x.2 }

private lemma Bi_biUnion_F2i :
    Bi B i = Finset.univ.biUnion (F2i B i) := by aesop (add simp [Bi, F2i])

@[simp]
private lemma F2i_disjoint : Set.PairwiseDisjoint Set.univ (F2i B i) := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Set.mem_univ, ne_eq, Disjoint, F2i,
    Finset.mem_product, Finset.le_eq_subset, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.forall, Finset.bot_eq_empty, Finset.notMem_empty, imp_false, forall_const]
  intro _ _ _ _ h1 h2 x₁ x₂ contr
  specialize h1 x₁ x₂ contr; specialize h2 x₁ x₂ contr; aesop

private lemma F2i_card {α : F} :
    (F2i B i α).card = 2 * choose_2 (K B i α) := by
  set A := Fi B i α with hA
  have h1 : F2i B i α = (A ×ˢ A).filter (fun x ↦ x.1 ≠ x.2) := by
    ext ⟨a, b⟩; simp [F2i, Fi, A, Finset.mem_filter, Finset.mem_product]; tauto
  rw [h1, Finset.filter_not, Finset.card_sdiff]
  · rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
    simp only [Finset.card_product]
    have h2 : ((A ×ˢ A).filter (fun x ↦ x.1 = x.2)).card = A.card := by
      rw [Finset.card_eq_of_equiv]
      exact {
        toFun := fun ⟨⟨a, _⟩, hx⟩ ↦ ⟨a, by
          simp only [Finset.mem_filter, Finset.mem_product] at hx; exact hx.1.1⟩
        invFun := fun ⟨a, ha⟩ ↦ ⟨⟨a, a⟩, by simp [Finset.mem_filter, ha]⟩
        left_inv := by intro ⟨⟨a, b⟩, hx⟩; simp [Finset.mem_filter] at hx; simp [hx.2]
        right_inv := by intro ⟨a, ha⟩; simp }
    rw [h2]
    simp only [hA, K_eq_sum, Finset.univ_eq_attach, Finset.sum_boole, Nat.cast_id, choose_2, K]
    push_cast [Nat.le_mul_self _]
    ring

open Finset in
private lemma sum_of_not_equals :
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) =
    2 * choose_2 #B - 2 * ∑ α, choose_2 (K B i α) := by
  set s₁ := {x ∈ B ×ˢ B | x.1 ≠ x.2} with eq₁
  rw [show ∑ x ∈ s₁, (if x.1 i ≠ x.2 i then (1 : ℚ) else 0) =
      s₁.card - (s₁.filter (fun x ↦ x.1 i = x.2 i)).card by
    rw [Finset.sum_boole, Finset.filter_not, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.filter_subset _ s₁)]
    exact_mod_cast Nat.cast_sub (Finset.card_filter_le _ _)]
  rw [show s₁.filter (fun x ↦ x.1 i = x.2 i) = Bi B i from by
    ext x; simp [eq₁, Bi]; tauto]
  rw [show (s₁.card : ℚ) = 2 * choose_2 (B.card : ℚ) from by
    have : s₁ = (B ×ˢ B) \ {x ∈ B ×ˢ B | x.1 = x.2} := by ext; simp [eq₁]; tauto
    rw [this, Finset.card_sdiff, Finset.inter_eq_left.mpr (by simp)]
    simp only [card_product, card_filter_prod_self_eq, choose_2]
    zify [Nat.le_mul_self #B]
    ring]
  rw [Bi_biUnion_F2i, Finset.card_biUnion (by simp [F2i_disjoint])]
  push_cast; simp_rw [F2i_card]
  simp only [Finset.mul_sum]

omit [Fintype F] in
private lemma hamming_dist_eq_sum {x y : Fin n → F} :
    Δ₀(x, y) = ∑ i, if x i = y i then 0 else 1 := by
  simp [hammingDist, Finset.sum_ite]

omit [Fintype F] [DecidableEq F] in
private lemma choose_2_card_ne_zero (h : 2 ≤ B.card) : choose_2 ↑B.card ≠ 0 := by
  simp [choose_2, sub_eq_zero]; grind only [= Finset.card_empty]

omit [Fintype F] in
private lemma d_eq_sum {B : Finset (Fin n → F)} (h_B : 2 ≤ B.card) :
    2 * choose_2 B.card * d B =
    ∑ i, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) := by
  field_simp [d, choose_2_card_ne_zero h_B]
  rw [Finset.sum_comm]
  simp_rw [fun y : (Fin n → F) × (Fin n → F) =>
    show (∑ x : Fin n, if y.1 x ≠ y.2 x then (1 : ℚ) else 0) = ↑Δ₀(y.1, y.2) by
      rw [hamming_dist_eq_sum]; simp [Nat.cast_sum, Nat.cast_ite]]
  simp only [d]; field_simp [choose_2_card_ne_zero h_B]; simp [Nat.cast_sum]

private lemma sum_sum_K_i_eq_n_sub_d (h_B : 2 ≤ B.card) :
    ∑ i, sum_choose_K_i B i = choose_2 B.card * (n - d B) := by
  have hd_eq_sum : 2 * choose_2 (B.card : ℚ) * d B =
      n * 2 * choose_2 (B.card : ℚ) - 2 * ∑ i, ∑ α, choose_2 (K B i α) := by
    have h_sum : ∑ i, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) =
        2 * choose_2 (B.card : ℚ) * n - 2 * ∑ i, ∑ α, choose_2 (K B i α) := by
      -- Apply the lemma sum_of_not_equals to rewrite the sum.
      have h_sum_rewrite :
        ∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) =
        ∑ i : Fin n, (2 * choose_2 (B.card : ℚ) - 2 * ∑ α : F, choose_2 (K B i α)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply sum_of_not_equals |> Eq.trans <| by ring;
      generalize_proofs at *; (
      rw [ h_sum_rewrite, Finset.sum_sub_distrib, Finset.mul_sum _ _ _, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul ] ; ring!;)
    convert h_sum using 1 <;> ring_nf!;
    convert d_eq_sum h_B using 1
    ring!
  generalize_proofs at *; (
  unfold choose_2 at *; norm_num at *; linarith!;)

private lemma almost_johnson [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    n * (choose_2 (k B) + (Fintype.card F - 1) *
      choose_2 ((B.card - k B) / (Fintype.card F - 1))) ≤
    choose_2 B.card * (n - d B) :=
  le_trans (le_sum_sum_choose_K h_n (by grind only) h_card)
    (sum_sum_K_i_eq_n_sub_d h_B ▸ le_refl _)

private lemma almost_johnson_choose_2_elimed [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    (k B * (k B - 1) +
      (B.card - k B) * ((B.card - k B) / (Fintype.card F - 1) - 1)) ≤
    B.card * (B.card - 1) * (n - d B) / n := by
  have h_expand : (Fintype.card F - 1 : ℚ) ≠ 0 := by
    exact sub_ne_zero_of_ne ( by norm_cast; linarith )
  have h_expand : (2 : ℚ) * choose_2 (k B) + (2 : ℚ) * ((Fintype.card F - 1) : ℚ) *
      choose_2 ((B.card - k B) / (Fintype.card F - 1)) ≤
        (2 : ℚ) * choose_2 B.card * (n - d B) / n := by
    have h_expand : (2 : ℚ) * choose_2 (k B) + (2 : ℚ) * ((Fintype.card F - 1) : ℚ) *
        choose_2 ((B.card - k B) / (Fintype.card F - 1)) ≤
          (2 : ℚ) * choose_2 B.card * (n - d B) / n := by
      have := almost_johnson h_n h_B h_card
      rw [ le_div_iff₀ ] <;> first | positivity | linarith;
    generalize_proofs at *; (convert h_expand using 1)
  generalize_proofs at *; (
  convert h_expand using 1 <;> push_cast [ choose_2 ] <;> ring_nf!;
  grind +ring);

private lemma almost_johnson_lhs_div_B_card [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) :
    (k B * (k B - 1) +
      (B.card - k B) * ((B.card - k B) / (Fintype.card F - 1) - 1)) / B.card =
    (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 /
      ((Fintype.card F - 1) * n ^ 2) - 1 := by
  set E := (n - e B 0) / n
  generalize eqrhs : (_ + _ - 1 : ℚ) = rhs
  have eqE : E = k B / B.card := by grind only [= k_and_e']
  suffices (B.card * E - 1) * E +
      ((B.card - B.card * E) / (Fintype.card F - 1) - 1) * (1 - E) = rhs by
    rw [eqE, mul_div_cancel₀ _ (by simp only [ne_eq, Rat.natCast_eq_zero_iff]; omega)] at this
    rw [← this]; field_simp
  rw [← eqrhs]
  have : E = 1 - (e B 0) / n := by
    simp only [E]; field_simp [show (n : ℚ) ≠ 0 from by exact_mod_cast Nat.pos_iff_ne_zero.mp h_n]
  grind only

private lemma johnson_unrefined [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 /
      ((Fintype.card F - 1) * n ^ 2) - 1 ≤
    (B.card - 1) * (1 - d B / n) := by
  have h_rewrite : (k B * (k B - 1) + (B.card - k B) *
      ((B.card - k B) / (Fintype.card F - 1) - 1)) / B.card ≤ (B.card - 1) *
      (1 - d B / n) := by
    have := almost_johnson_choose_2_elimed h_n h_B h_card; (
    rw [ div_le_iff₀ ] <;> first | positivity | convert this using 1 ; ring_nf;
    simpa [ h_n.ne' ] using by ring;);
  convert h_rewrite using 1;
  convert almost_johnson_lhs_div_B_card h_n h_B |> Eq.symm using 1

private lemma johnson_unrefined_by_M [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    B.card * ((1 - e B 0 / n) ^ 2 + (e B 0) ^ 2 /
      ((Fintype.card F - 1) * n ^ 2) - 1 + d B / n) ≤
    d B / n := by
  suffices B.card * ((1 - e B 0 / n) ^ 2 + e B 0 ^ 2 /
      ((Fintype.card F - 1) * n ^ 2)) - B.card * (1 - d B / n) + -1 +
    B.card * (1 - d B / n) ≤ (B.card - 1) * (1 - d B / n) by linarith
  exact le_trans (le_of_eq (by ring)) (johnson_unrefined h_n h_B h_card)

private lemma johnson_unrefined_by_M' [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    B.card * (Fintype.card F / (Fintype.card F - 1)) *
      ((1 - e B 0 / n) ^ 2 + e B 0 ^ 2 / ((Fintype.card F - 1) * n ^ 2) - 1 + d B / n) ≤
    (Fintype.card F / (Fintype.card F - 1)) * d B / n := by
  rw [mul_comm (B.card : ℚ), mul_assoc, ← mul_div]
  exact mul_le_mul_of_nonneg_left (johnson_unrefined_by_M h_n h_B h_card)
    (le_of_lt (div_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) h_card))
      (by linarith [show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast h_card])))

private lemma johnson_denom [Zero F] (h_card : 2 ≤ Fintype.card F) :
    (Fintype.card F / (Fintype.card F - 1)) *
    ((1 - e B 0 / n) ^ 2 + (e B 0) ^ 2 / ((Fintype.card F - 1) * n ^ 2) - 1 + d B / n) =
    (1 - ((Fintype.card F) / (Fintype.card F - 1)) *
    (e B 0 / n)) ^ 2 - (1 - ((Fintype.card F) / (Fintype.card F - 1)) * (d B / n)) := by
  set c := Fintype.card F; set c1 := (c : ℚ) - 1
  have n₂ : c1 ≠ 0 := by simp [c1, c, sub_eq_zero]; grind only
  suffices c / c1 * (d B / n - 2 * e B 0 / n + c / c1 * e B 0 ^ 2 / n ^ 2) =
      (1 - c / c1 * (e B 0 / n)) ^ 2 - (1 - c / c1 * (d B / n)) by
    rw [← this]; have : c / c1 = 1 + 1 / c1 := by grind only
    grind only [= e.eq_1]
  grind only

private lemma johnson_bound₀ [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    B.card * ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B 0 / n)) ^ 2 -
      (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B / n))) ≤
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B / n := by
  rw [← johnson_denom h_card, ← mul_assoc]
  exact johnson_unrefined_by_M' h_n h_B h_card

protected lemma johnson_bound_lemma [Field F] {v : Fin n → F}
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ Fintype.card F) :
    B.card * ((1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (e B v / n)) ^ 2 -
      (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d B / n))) ≤
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * d B / n := by
  rw [lin_shift_e (by omega), lin_shift_d h_B, lin_shift_card (v := v)]
  exact johnson_bound₀ h_n (lin_shift_card (B := B) ▸ h_B) h_card

protected lemma abs_one_sub_div_le_one {v a : Fin n → F}
    (h_card : 2 ≤ Fintype.card F) :
    |1 - (1 + 1 / ((Fintype.card F : ℚ) - 1)) * Δ₀(v, a) / n| ≤ 1 := by
  -- Since $\Delta₀(v, a) \leq n$, we have $(1 + 1 / (Fintype.card F - 1)) * Δ₀(v, a) / n \leq 2$.
  have h_bound : (1 + 1 / (Fintype.card F - 1) : ℚ) * Δ₀(v, a) / n ≤ 2 := by
    have h_bound : (1 + 1 / (Fintype.card F - 1) : ℚ) ≤ 2 := by
      rw [ one_add_div, div_le_iff₀ ] <;> linarith [ show ( Fintype.card F : ℚ ) ≥ 2 by norm_cast ]
    refine div_le_of_le_mul₀ ?_ ?_ ?_ <;> try linarith;
    refine le_trans ( mul_le_mul_of_nonneg_right h_bound ( Nat.cast_nonneg _ ) ) ?_;
    exact mul_le_mul_of_nonneg_left
      ( mod_cast le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) ) zero_le_two;
  refine abs_le.mpr ⟨ ?_, ?_ ⟩;
  · lia;
  · exact sub_le_self _ ( by exact div_nonneg ( mul_nonneg ( add_nonneg zero_le_one
      ( one_div_nonneg.mpr ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) )
        ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) )

lemma johnson_hyp_implies_div_ineq {n d e : ℕ}
    (hn : 0 < n) (h_dn : d ≤ n)
    (h : (e : ℝ) ≤ n - Real.sqrt (n * (n - d))) :
    1 - (d : ℝ) / n ≤ (1 - (e : ℝ) / n) ^ 2 := by
  -- By multiplying both sides of the inequality by $n^2$, we get $n^2 - n d \leq (n - e)^2$.
  have h_mul : (n^2 - n * d : ℝ) ≤ (n - e)^2 := by
    nlinarith [ Real.sqrt_nonneg ( n * ( n - d ) ),
      Real.mul_self_sqrt ( show 0 ≤ ( n : ℝ ) * ( n - d ) by
        exact mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg_of_le ( mod_cast h_dn ) ) ) ];
  field_simp at *;
  exact_mod_cast h_mul

lemma johnson_e_div_ne_J {n d e : ℕ} {q : ℚ}
    (hn_pos : 0 < n) (hd_pos : 0 < d) (hq : 1 < q)
    (h_muln : ((e : ℚ) / n : ℝ) ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt)
    (h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J' q (d / n))
    (hqx : q / (q - 1) * (d / n) ≤ 1) :
    ((e : ℚ) / n : ℝ) ≠ J' q (d / n) := by
  intro h_eq
  set δ := (d : ℚ) / n
  set frac := q / (q - 1)
  have h_frac_pos : 1 < frac := by
    rw [ lt_div_iff₀ ] <;> linarith;
  -- From h_muln and h_J_bound and h_eq, deduce 1 - sqrt(1-δ) = J'(q,δ).
  have h_sqrt_eq : 1 - Real.sqrt (1 - δ) = (1 / frac) * (1 - Real.sqrt (1 - frac * δ)) := by
    convert h_eq using 1;
    rw [ le_antisymm h_muln ]
    · norm_cast
    · aesop
  have h_frac_eq : 1 - Real.sqrt (1 - δ) = δ / (1 + Real.sqrt (1 - δ)) ∧ (1 / frac) *
      (1 - Real.sqrt (1 - frac * δ)) = δ / (1 + Real.sqrt (1 - frac * δ)) := by
    constructor
    · rw [ eq_div_iff ] <;> ring_nf <;> norm_num;
      · rw [ Real.sq_sqrt ] <;> norm_num;
        exact_mod_cast div_le_one_of_le₀ ( show ( d : ℚ ) ≤ n by
          exact_mod_cast Nat.le_of_lt_succ <| by
            { rw [ ← @Nat.cast_lt ℚ ]
              push_cast
              nlinarith [ show ( 1 : ℚ ) ≤ d by
                exact_mod_cast hd_pos, show ( 1 : ℚ ) ≤ n by
                  exact_mod_cast hn_pos, mul_div_cancel₀ ( d : ℚ ) ( by
                    positivity : ( n : ℚ ) ≠ 0 ), div_mul_cancel₀ ( q : ℚ ) ( by
                      linarith : ( q - 1 : ℚ ) ≠ 0 ) ] } ) ( by positivity );
      · positivity;
    · field_simp [frac] at *;
      linarith [ Real.mul_self_sqrt ( show 0 ≤ 1 - ( frac : ℝ ) * δ by
        exact sub_nonneg_of_le <| mod_cast hqx ) ];
  have h_sqrt_eq' : Real.sqrt (1 - frac * δ) = Real.sqrt (1 - δ) := by
    grind;
  rw [ Real.sqrt_inj ] at h_sqrt_eq' <;> norm_cast at * <;>
    nlinarith [ show ( 0 : ℚ ) < δ by positivity ] ;

lemma johnson_worst_case_bound {n : ℕ} {F : Type*} [DecidableEq F]
    {B : Finset (Fin n → F)} {v : Fin n → F} {d e : ℕ} {frac : ℚ}
    (hn_pos : (0 : ℚ) < n) (hd_pos : 0 < d) (d_le_n : d ≤ n)
    (h : (e : ℝ) ≤ n - ((n * (n - d)) : ℝ).sqrt)
    (h_d_close_n : frac * (d / n : ℚ) ≤ 1)
    (hfrac_gt1 : (1 : ℚ) < frac)
    (e_ineq : JohnsonBound.e B v ≤ e)
    (d_ineq : (d : ℚ) ≤ JohnsonBound.d B)
    (quad_nonneg : (0 : ℚ) ≤ (d / n : ℚ) - 2 * (e / n : ℚ) + (e / n : ℚ) ^ 2)
    (hden1_pos :
      (0 : ℚ) < JohnsonBound.d B / n - 2 * JohnsonBound.e B v / n +
        frac * (JohnsonBound.e B v / n) ^ 2) :
    (JohnsonBound.d B / n) /
      (JohnsonBound.d B / n - 2 * JohnsonBound.e B v / n +
      frac * (JohnsonBound.e B v / n) ^ 2) ≤
    (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2) := by
  -- Apply the lemma `div_le_div_iff₀` to establish the inequality between the fractions.
  have h_frac_ineq : ( JohnsonBound.d B / n : ℚ ) * ( d / n - 2 * ( e / n ) +
      frac * ( e / n ) ^ 2 ) ≤ ( d / n ) * ( JohnsonBound.d B / n - 2 *
        ( JohnsonBound.e B v / n ) + frac * ( JohnsonBound.e B v / n ) ^ 2 ) := by
    have h_frac_ineq : (JohnsonBound.d B / n - d / n) * (2 * (e / n) - frac * (e / n) ^ 2) ≥ 0 ∧
        (e / n - JohnsonBound.e B v / n) * (2 - frac * (e / n + JohnsonBound.e B v / n)) ≥ 0 := by
      refine ⟨ mul_nonneg ?_ ?_, mul_nonneg ?_ ?_ ⟩;
      · exact sub_nonneg_of_le ( by gcongr ) ;
      · have h_frac_le_one : frac * (e / n : ℚ) ≤ 1 := by
          have h_frac_le_one : frac * (d / n : ℚ) ≤ 1 := h_d_close_n
          have h_e_le_d : (e / n : ℚ) ≤ (d / n : ℚ) := by
            have h_e_le_d : (e : ℝ) ≤ n - Real.sqrt (n * (n - d)) := by
              grind
            generalize_proofs at *; (
            -- Since $e \leq n - \sqrt{n(n-d)}$, we have $e \leq d$.
            have h_e_le_d : (e : ℚ) ≤ d := by
              exact_mod_cast ( by nlinarith [
                show (d : ℝ) ≤ n by norm_cast, Real.sqrt_nonneg (n * (n - d)), Real.mul_self_sqrt (
                  show 0 ≤ ( n : ℝ ) * ( n - d ) by
                    nlinarith [ show ( d : ℝ ) ≤ n by norm_cast ] ) ] : ( e : ℝ ) ≤ d ) ;
            generalize_proofs at *; (
            gcongr))
          exact le_trans ( mul_le_mul_of_nonneg_left h_e_le_d ( by positivity ) ) h_frac_le_one
        generalize_proofs at *; (
        nlinarith [ show 0 ≤ ( e : ℚ ) / n by positivity ] ;);
      · exact sub_nonneg_of_le ( by gcongr );
      · have h_frac_e_n_le_1 : frac * (e / n : ℚ) ≤ 1 := by
          refine le_trans ( mul_le_mul_of_nonneg_left ( show ( e : ℚ ) / n ≤ d / n from ?_ )
            ( by positivity ) ) h_d_close_n;
          -- Since $e \leq n - \sqrt{n(n-d)}$, we have $e \leq d$.
          have h_e_le_d : (e : ℚ) ≤ d := by
            exact_mod_cast ( by
              nlinarith [ show ( d : ℝ ) ≤ n by norm_cast,
                Real.sqrt_nonneg ( n * ( n - d ) ),
                Real.mul_self_sqrt ( show 0 ≤ ( n : ℝ ) * ( n - d ) by
                  nlinarith [ show ( d : ℝ ) ≤ n by norm_cast ] ) ] : ( e : ℝ ) ≤ d ) ;
          generalize_proofs at *; (
          gcongr)
        have h_frac_e_B_v_n_le_1 : frac * (JohnsonBound.e B v / n : ℚ) ≤ 1 := by
          exact le_trans ( mul_le_mul_of_nonneg_left
            ( div_le_div_of_nonneg_right ( show ( JohnsonBound.e B v : ℚ ) ≤ e by
              exact_mod_cast e_ineq ) ( Nat.cast_nonneg _ ) ) ( by positivity ) ) h_frac_e_n_le_1;
        linarith;
    nlinarith [ ( by positivity : 0 < ( n : ℚ ) ), mul_div_cancel₀ ( e : ℚ ) ( by
      positivity : ( n : ℚ ) ≠ 0 ), mul_div_cancel₀ ( JohnsonBound.e B v : ℚ ) ( by
        positivity : ( n : ℚ ) ≠ 0 ), mul_div_cancel₀ ( d : ℚ ) ( by positivity : ( n : ℚ ) ≠ 0 ) ]
  rw [ div_le_div_iff₀ ] <;> ring_nf at * <;> try linarith;
  by_cases h_e_zero : e = 0;
  · aesop;
  · have h_frac_pos : (n : ℚ)⁻¹ ^ 2 * e ^ 2 * frac > (n : ℚ)⁻¹ ^ 2 * e ^ 2 := by
      exact lt_mul_of_one_lt_right ( by positivity ) hfrac_gt1;
    nlinarith [ show ( e : ℚ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h_e_zero ]

lemma johnson_den_ge_frac_d {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    {B : Finset (Fin n → F)} {v : Fin n → F} :
    (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.e B v / n)) ^ 2 -
      (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n)) ≥
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B / n) - 1 := by
  nlinarith [sq_nonneg (1 - ((Fintype.card F : ℚ) / (Fintype.card F - 1)) *
    (JohnsonBound.e B v / n))]

lemma johnson_gap_frac_d_gt_one {n d : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    {B : Finset (Fin n → F)}
    (q_not_small : (2 : ℚ) ≤ (Fintype.card F : ℚ))
    (n_not_small : (1 : ℕ) ≤ n)
    (h_d_close_n : ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (d / n : ℚ) > 1)
    (hd_le_dB : (d : ℚ) ≤ JohnsonBound.d B) :
    (1 : ℚ) / ((n : ℚ) * ((Fintype.card F : ℚ) - 1)) ≤
    ((Fintype.card F : ℚ) / (Fintype.card F - 1)) * (JohnsonBound.d B) / n - 1 := by
  -- From h_d_close_n, we have that q*d > (q-1)*n, so q*d ≥ (q-1)*n + 1.
  have h_qd_ge : (Fintype.card F : ℚ) * d ≥ (Fintype.card F - 1) * n + 1 := by
    have h_frac_d_ge_frac_dB : (Fintype.card F : ℚ) * d > (Fintype.card F - 1) * n := by
      rw [ div_mul_div_comm, gt_iff_lt, lt_div_iff₀ ] at h_d_close_n <;>
        nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ n ) ] ;
    generalize_proofs at *; (
    exact_mod_cast h_frac_d_ge_frac_dB);
  field_simp at *;
  rw [ div_sub', div_le_div_iff_of_pos_right ] <;> nlinarith [ show ( Fintype.card F : ℚ ) ≥ 2 by
    exact_mod_cast q_not_small ] ;

lemma johnson_den_lb_e_zero {n d : ℕ} {q : ℚ}
    (hn_pos : 0 < n) (hq_ge1 : (1 : ℚ) ≤ q) (hd_ge1 : (1 : ℚ) ≤ (d : ℚ)) :
    (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (d : ℚ) / n := by
  gcongr ; nlinarith [ show ( n : ℚ ) ≥ 1 by exact_mod_cast hn_pos, show ( q : ℚ ) ≥ 1 by
    exact_mod_cast hq_ge1, show ( d : ℚ ) ≥ 1 by exact_mod_cast hd_ge1 ] ;

lemma johnson_den_lb_e_pos {n d e : ℕ} {q frac : ℚ}
    (hn_pos : (0 : ℚ) < n)
    (hq_ne : (q : ℚ) ≠ 0)
    (one_div_q_le : (1 : ℚ) / q ≤ frac - 1)
    (hfrac1_pos : (0 : ℚ) < frac - 1)
    (hbase_nonneg : (0 : ℚ) ≤ (d / n : ℚ) - 2 * (e / n : ℚ) + (e / n : ℚ) ^ 2)
    (he0 : e ≠ 0) :
    (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤
    (d / n : ℚ) - 2 * (e / n : ℚ) + frac * (e / n : ℚ) ^ 2 := by
  -- Since $e \neq 0$, we have $e / n \geq 1 / n$, thus $(e / n)^2 \geq 1 / n^2$.
  have h_e_div_n_ge : (e / n : ℚ) ^ 2 ≥ 1 / (n : ℚ) ^ 2 := by
    field_simp;
    exact_mod_cast Nat.one_le_pow _ _ ( Nat.pos_of_ne_zero he0 );
  ring_nf at *; nlinarith [ mul_inv_cancel₀ hq_ne ] ;

lemma johnson_qdn_ge_two {q : ℚ} {d n : ℕ}
    (hq : (2 : ℚ) ≤ q) (hd : (1 : ℕ) ≤ d) (hn : (1 : ℕ) ≤ n) :
    (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by
  have : (1 : ℚ) ≤ (d : ℚ) * (n : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  nlinarith

lemma johnson_d_le_n {n : ℕ} {F : Type*} [DecidableEq F]
    {B : Finset (Fin n → F)} (hB : 2 ≤ B.card) :
    JohnsonBound.d B ≤ (n : ℚ) := by
  unfold d;
  field_simp;
  rw [ div_le_iff₀ ];
  · -- Each term in the sum is at most $n$, and there are $2 \binom{|B|}{2}$ terms.
    have h_sum_le :
        ∑ x ∈ B.product B with x.1 ≠ x.2, Δ₀(x.1, x.2) ≤
        ∑ x ∈ B.product B with x.1 ≠ x.2, n :=
      Finset.sum_le_sum fun x _ =>
        le_trans (Finset.card_le_univ _) (by simp)
    refine le_trans (Nat.cast_le.mpr h_sum_le) ?_
    norm_cast
    simp [choose_2]
    ring_nf
    rw [show (Finset.filter (fun x : (Fin n → F) × (Fin n → F) =>
        ¬x.1 = x.2) (B ×ˢ B)) = Finset.offDiag B from by ext; aesop]
    simp only [Finset.offDiag_card, le_neg_add_iff_add_le]; ring_nf
    rw [Nat.cast_sub] <;> push_cast <;> nlinarith only [hB]
  · exact div_pos
      (mul_pos (Nat.cast_pos.mpr (by linarith))
        (sub_pos.mpr (Nat.one_lt_cast.mpr (by linarith))))
      zero_lt_two

end

end JohnsonBound
