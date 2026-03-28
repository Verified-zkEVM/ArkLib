/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations

namespace JohnsonBound

open Real Finset Fintype

/-- The `q`-ary Johnson bound function: `J'(q, δ) = ((q-1)/q) · (1 - √(1 - (q/(q-1)) · δ))`. -/
noncomputable def J' (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - √(1 - frac * δ))

/-- Rationalisation identity `a - √b = (a² - b) / (a + √b)`. -/
lemma division_by_conjugate' {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
    a - b.sqrt = (a ^ 2 - b) / (a + b.sqrt) := by
  grind only [usr sq_sqrt', = max_def]

section

variable {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} {i : Fin n}

/-- `Fi B i α` is the subset of codewords in `B` whose `i`-th coordinate equals `α`. -/
private def Fi (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset (Fin n → F) :=
  {x | x ∈ B ∧ x i = α}

/-- `K B i α` is the cardinality of `Fi B i α`. -/
private abbrev K (B : Finset (Fin n → F)) (i : Fin n) (α : F) : ℕ :=
  (Fi B i α).card

/-- The sets `Fi B i α` partition `B` as `α` ranges over `F`. -/
@[simp]
lemma Fis_cover_B : B = univ.biUnion (Fi B i) := by aesop (add simp [Fi])

/-- The sets `Fi B i α` are pairwise disjoint. -/
@[simp]
lemma Fis_pairwise_disjoint : Set.PairwiseDisjoint Set.univ (Fi B i) := by
  unfold Fi
  rintro x - y - h₁ _ h₂ h₃ _ contra
  specialize h₂ contra; specialize h₃ contra; aesop

/-- The cardinalities `K B i α` sum to `|B|`. -/
@[simp]
lemma sum_K_eq_card : ∑ α : F, K B i α = B.card := by
  rw (occs := [2]) [Fis_cover_B (B := B) (i := i)]
  rw [card_biUnion (by simp [Fis_pairwise_disjoint])]

/-- `K B i α` expressed as a sum of indicators over `B`. -/
@[simp]
lemma K_eq_sum {α : F} :
    K B i α = ∑ x : B, if x.1 i = α then 1 else 0 := by
  simp only [K, Fi, univ_eq_attach, sum_boole, Nat.cast_id]
  simp_rw [card_filter, sum_attach_eq_sum_dite]
  exact sum_congr rfl (by aesop)

/-- Each `K B i α` is at most `|B|`. -/
@[simp]
lemma K_le_card {α : F} : K B i α ≤ B.card := by
  simp [K, Fi]
  exact card_le_card fun _ ha ↦ by
    simp only [mem_filter, mem_univ, true_and] at ha; exact ha.1

/-- Jensen's inequality applied to `choose_2` for nonzero coordinates. -/
lemma sum_choose_K' [Zero F] (h_card : 2 ≤ card F) :
    (card F - 1) * choose_2 ((B.card - K B i 0) / (card F - 1)) ≤
    ∑ α with α ≠ 0, choose_2 (K B i α) := by
  rw [← sum_K_eq_card (i := i), Nat.cast_sum]
  set x1 : ℚ := card F - 1
  have hx1 : x1 ≠ 0 := by simp [x1, sub_eq_zero]; omega
  set x2 := K B i
  suffices x1 * choose_2
      (∑ x with x ≠ 0, (fun _ ↦ x1⁻¹) x • (Nat.cast (R := ℚ) ∘ x2) x) ≤
      ∑ α with α ≠ 0, choose_2 ↑(x2 α) by
    simp only [ne_eq, Function.comp_apply, smul_eq_mul] at this; convert this
    rw [sum_eq_sum_diff_singleton_add (i := 0) (by simp)]
    ring_nf; rw [sum_mul]
    apply Finset.sum_congr (ext _)
    all_goals grind only [= mem_filter, = mem_sdiff, ← mem_univ, = mem_singleton]
  simp only [Function.comp_apply, smul_eq_mul]
  have hx1_nonneg : (0 : ℚ) ≤ x1 := by simp [x1, sub_nonneg]; omega
  have jensen := ConvexOn.map_sum_le choose_2_convex
    (t := univ.filter (· ≠ (0 : F))) (w := fun _ ↦ x1⁻¹) (p := fun α ↦ (x2 α : ℚ))
    (fun _ _ ↦ inv_nonneg.mpr hx1_nonneg)
    (by simp [x1]; field_simp; exact div_self hx1) (by simp)
  simp only [smul_eq_mul] at jensen
  exact le_trans (mul_le_mul_of_nonneg_left jensen hx1_nonneg) <|
    le_of_eq <| by rw [mul_sum]; congr 1; ext; rw [← mul_assoc, mul_inv_cancel₀ hx1, one_mul]

/-- Total `choose_2` over all coordinates at position `i`. -/
@[simp, grind]
private def sum_choose_K_i (B : Finset (Fin n → F)) (i : Fin n) : ℚ :=
  ∑ α : F, choose_2 (K B i α)

/-- Lower bound on `sum_choose_K_i` via convexity. -/
@[simp]
lemma le_sum_choose_K [Zero F] (h_card : 2 ≤ card F) :
    choose_2 (K B i 0) + (card F - 1) *
    choose_2 ((B.card - K B i 0) / (card F - 1)) ≤ sum_choose_K_i B i := by
  simp only [sum_choose_K_i]
  have : ∑ α, choose_2 ↑(K B i α) =
      choose_2 ↑(K B i 0) + ∑ α with α ≠ 0, choose_2 ↑(K B i α) := by
    rw [sum_eq_sum_diff_singleton_add (i := (0 : F)) (by simp), add_comm]
    exact congr_arg _ (sum_congr
      (by ext x; simp [mem_sdiff, mem_singleton, mem_filter]) fun _ _ ↦ rfl)
  linarith [sum_choose_K' h_card (B := B) (i := i)]

/-- Average number of zero coordinates across positions, normalised by `n`. -/
private def k [Zero F] (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ) / n * ∑ i, K B i 0

omit [Fintype F] in
/-- Hamming weight as a sum of coordinate indicators. -/
lemma hamming_weight_eq_sum [Zero F] {x : Fin n → F} :
    ‖x‖₀ = ∑ i, if x i = 0 then 0 else 1 := by simp [hammingNorm, sum_ite]

/-- Sum of Hamming weights equals `n · |B|` minus total zero-coordinate counts. -/
@[simp]
lemma sum_hamming_weight_sum [Zero F] :
    ∑ x ∈ B, (‖x‖₀ : ℚ) = n * B.card - ∑ i, K B i 0 := by
  simp only [hamming_weight_eq_sum, Nat.cast_sum, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
    K_eq_sum, sum_boole, Nat.cast_id]
  simp_rw [card_filter]
  rw [sum_comm, eq_sub_iff_add_eq]
  simp_rw [Nat.cast_sum, Nat.cast_ite]
  conv in Finset.sum _ _ => arg 2; ext; arg 2; ext; rw [← ite_not]
  simp_rw [univ_eq_attach, sum_attach_eq_sum_dite]
  simp only [Nat.cast_one, CharP.cast_eq_zero, dite_eq_ite, Finset.sum_ite_mem, univ_inter]
  rw [← sum_add_distrib]
  simp_rw [← sum_filter, add_comm, sum_filter_add_sum_filter_not]
  simp_all only [sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin]

/-- Relation between `k` and the average radius `e`. -/
@[simp]
lemma k_and_e [Zero F] (h_n : n ≠ 0) (h_B : B.card ≠ 0) :
    k B = B.card * (n - e B 0) / n := by
  simp [e, k, sum_hamming_weight_sum]; field_simp; grind only

/-- `k / |B|` equals `(n - e) / n`. -/
@[simp]
lemma k_and_e' [Zero F] (h_n : n ≠ 0) (h_B : B.card ≠ 0) :
    k B / B.card = (n - e B 0) / n := by rw [k_and_e h_n h_B]; field_simp

/-- Jensen's inequality for `choose_2 ∘ K` at the zero coordinate. -/
@[simp]
lemma k_choose_2 [Zero F] (h_n : n ≠ 0) :
    n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) := by
  suffices choose_2 (∑ i, (fun _ ↦ (1 : ℚ) / n) i • (fun i ↦ K B i 0) i) * n ≤
      ∑ i, choose_2 (K B i 0) by
    rw [mul_comm]; convert this; simp [k, mul_sum]
  simp only [one_div, smul_eq_mul]
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero h_n
  have jensen := ConvexOn.map_sum_le choose_2_convex
    (t := univ (α := Fin n)) (w := fun _ ↦ (n : ℚ)⁻¹) (p := fun i ↦ (K B i 0 : ℚ))
    (fun _ _ ↦ inv_nonneg.mpr hn_pos.le) (by simp; field_simp) (by simp)
  simp only [smul_eq_mul] at jensen
  exact le_trans (mul_le_mul_of_nonneg_right jensen hn_pos.le)
    (le_of_eq (by rw [sum_mul]; congr 1; ext x; field_simp))

/-- Auxiliary fraction `(|B| - x) / (|F| - 1)`. -/
@[simp, grind]
private def aux_frac (B : Finset (Fin n → F)) (x : ℚ) : ℚ :=
  (B.card - x) / (card F - 1)

/-- The average of `aux_frac` over coordinates equals `aux_frac` at `k`. -/
@[simp]
lemma sum_1_over_n_aux_frac_k_i [Zero F] (h_n : 0 < n) :
    (1 : ℚ) / n * ∑ i, aux_frac B (K B i 0) = aux_frac B (k B) := by
  unfold aux_frac k; simp [← sum_div]; field_simp

lemma le_sum_sum_choose_K [Zero F] (h_n : 0 < n) (h_card : 2 ≤ card F) :
    n * (choose_2 (k B) + (card F - 1) *
    choose_2 ((B.card - k B) / (card F - 1))) ≤ ∑ i, sum_choose_K_i B i := by
  have h_ineq1 : n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) :=
    k_choose_2 (Nat.pos_iff_ne_zero.1 h_n)
  have h_ineq2 : n * ((card F - 1 : ℚ) *
      choose_2 ((B.card - k B) / (card F - 1))) ≤
      ∑ i, ((Fintype.card F - 1 : ℚ) *
        choose_2 ((B.card - K B i 0) / (card F - 1))) := by
    rw [show (n : ℚ) * ((card F - 1 : ℚ) *
        choose_2 ((B.card - k B) / (card F - 1)))
        = (card F - 1 : ℚ) *
          (n * choose_2 ((B.card - k B) / (card F - 1))) from by ring]
    have h_card_pos : (0 : ℚ) < card F - 1 := by
      simp only [sub_pos, Nat.one_lt_cast]
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) h_card
    rw [← mul_sum _ _ _]
    gcongr
    have h_jensen : ConvexOn ℚ Set.univ (fun x : ℚ => choose_2 x) := by
      exact choose_2_convex
    have h_jensen : ∑ i : Fin n, (1 / n : ℚ) * choose_2 ((B.card - K B i 0) / (Fintype.card F - 1))
        ≥ choose_2 (∑ i : Fin n, (1 / n : ℚ) * ((B.card - K B i 0) / (Fintype.card F - 1))) := by
      apply ConvexOn.map_sum_le h_jensen
      · exact fun _ _ ↦ by positivity
      · simp [h_n.ne']
      · exact fun _ _ ↦ Set.mem_univ _
    convert mul_le_mul_of_nonneg_left h_jensen (Nat.cast_nonneg n) using 1
    · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_div, k, h_n.ne' ] ; ring_nf
      simp +decide [ h_n.ne' ]
    · simp [← mul_sum _ _ _, h_n.ne']
  have h_combined : ∑ i : Fin n, sum_choose_K_i B i ≥
      ∑ i : Fin n, (choose_2 (K B i 0) +
      (card F - 1) * choose_2 ((B.card - K B i 0) / (card F - 1))) :=
    sum_le_sum fun i _ ↦ le_trans (le_sum_choose_K (show 2 ≤ card F from h_card)) le_rfl
  rw [sum_add_distrib] at h_combined
  nlinarith [show (n : ℚ) ≥ 1 from by exact_mod_cast h_n]

/-- `F2i B i α` is the set of ordered pairs from `B` that agree at position `i` with value `α`. -/
private def F2i (B : Finset (Fin n → F)) (i : Fin n) (α : F) :
    Finset ((Fin n → F) × (Fin n → F)) :=
  {x | x ∈ B ×ˢ B ∧ x.1 ≠ x.2 ∧ x.1 i = α ∧ x.2 i = α}

/-- The sets `F2i B i α` are pairwise disjoint over `α`. -/
lemma F2i_disjoint : Set.PairwiseDisjoint Set.univ (F2i B i) := by
  intros a _ b _ hab
  simp only [disjoint_left, Prod.forall]
  unfold F2i; aesop

/-- `|F2i B i α| = K(α) · (K(α) - 1)`. -/
lemma F2i_card {α : F} : (F2i B i α).card = K B i α * (K B i α - 1) := by
  simp only [F2i, K, Fi, Finset.card_filter, Finset.mem_product]
  simp only [ne_eq, Finset.sum_boole, Nat.cast_id]
  rw [show (Finset.univ.filter (fun x : (Fin n → F) × (Fin n → F) ↦
    (x.1 ∈ B ∧ x.2 ∈ B) ∧ ¬x.1 = x.2 ∧ x.1 i = α ∧ x.2 i = α)) =
      (Finset.univ.filter (fun x : Fin n → F ↦ x ∈ B ∧ x i = α)).offDiag from ?_]
  · simp [mul_tsub, offDiag_card]
  · grind

/-- `Bi B i` is the set of distinct ordered pairs from `B` agreeing at position `i`. -/
private def Bi (B : Finset (Fin n → F)) (i : Fin n) :=
  {x ∈ B ×ˢ B | x.1 ≠ x.2 ∧ x.1 i = x.2 i}

/-- `Bi` decomposes as a disjoint union of `F2i` over all field elements. -/
lemma Bi_biUnion_F2i : Bi B i = univ.biUnion (F2i B i) := by unfold Bi F2i; ext; aesop

/-- `|Bi B i| = ∑ α, K(α) · (K(α) - 1)`. -/
lemma Bi_card : (Bi B i).card = ∑ α : F, K B i α * (K B i α - 1) := by
  rw [Bi_biUnion_F2i, card_biUnion (by simp [F2i_disjoint])]
  simp_rw [F2i_card]

/-- Counting pairs that disagree at position `i` in terms of `choose_2`. -/
lemma sum_of_not_equals :
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) =
    2 * choose_2 #B - 2 * ∑ α, choose_2 (K B i α) := by
  set s₁ := {x ∈ B ×ˢ B | x.1 ≠ x.2} with eq₁
  rw [show ∑ x ∈ s₁, (if x.1 i ≠ x.2 i then (1 : ℚ) else 0) =
      s₁.card - (s₁.filter (fun x ↦ x.1 i = x.2 i)).card by
    rw [sum_boole, filter_not, card_sdiff,
      inter_eq_left.mpr (filter_subset _ s₁)]
    exact_mod_cast Nat.cast_sub (card_filter_le _ _)]
  rw [show s₁.filter (fun x ↦ x.1 i = x.2 i) = Bi B i from by
    ext x; simp [eq₁, Bi]; tauto]
  rw [show (s₁.card : ℚ) = 2 * choose_2 (B.card : ℚ) from by
    have : s₁ = (B ×ˢ B) \ {x ∈ B ×ˢ B | x.1 = x.2} := by ext; simp [eq₁]; tauto
    rw [this, card_sdiff, inter_eq_left.mpr (by simp)]
    simp only [card_product, card_filter_prod_self_eq, choose_2]
    zify [Nat.le_mul_self #B]; ring]
  rw [Bi_biUnion_F2i, card_biUnion (by simp [F2i_disjoint])]
  unfold choose_2 at *; norm_num at *; ring_nf
  rw [sum_mul _ _ _]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [F2i_card]; ring_nf
  cases h : (Finset.univ.filter (fun y : B ↦ (y : Fin n → F) i = x)).card <;> simp_all; ring!

omit [Fintype F] in
/-- Hamming distance as a sum of coordinate indicators. -/
lemma hamming_dist_eq_sum {x y : Fin n → F} :
    Δ₀(x, y) = ∑ i, if x i = y i then 0 else 1 := by
  simp [hammingDist, sum_ite]

omit [Fintype F] [DecidableEq F] in
/-- `choose_2` of a code of size `≥ 2` is nonzero. -/
lemma choose_2_card_ne_zero (h : 2 ≤ B.card) : choose_2 ↑B.card ≠ 0 := by
  simp [choose_2, sub_eq_zero]; grind only [= Finset.card_empty]

omit [Fintype F] in
/-- The average distance `d` expressed as a double sum of coordinate disagreements. -/
lemma d_eq_sum (h_B : 2 ≤ B.card) :
    2 * choose_2 B.card * d B =
    ∑ i, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then 1 else 0) := by
  field_simp [d, choose_2_card_ne_zero h_B]
  rw [sum_comm]
  simp_rw [fun y : (Fin n → F) × (Fin n → F) ↦
    show (∑ x : Fin n, if y.1 x ≠ y.2 x then (1 : ℚ) else 0) = ↑Δ₀(y.1, y.2) by
      rw [hamming_dist_eq_sum]; simp [Nat.cast_sum, Nat.cast_ite]]
  simp only [d]; field_simp [choose_2_card_ne_zero h_B]; simp [Nat.cast_sum]

/-- Total `choose_2` over all coordinates equals `choose_2(|B|) · (n - d)`. -/
lemma sum_sum_K_i_eq_n_sub_d (h_B : 2 ≤ B.card) :
    ∑ i, sum_choose_K_i B i = choose_2 B.card * (n - d B) := by
  have hd_eq_sum : 2 * choose_2 (B.card : ℚ) * d B =
      n * 2 * choose_2 (B.card : ℚ) - 2 * ∑ i, ∑ α, choose_2 (K B i α) := by
    have h_sum : ∑ i, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2,
        (if x.1 i ≠ x.2 i then 1 else 0) =
        2 * choose_2 (B.card : ℚ) * n - 2 * ∑ i, ∑ α, choose_2 (K B i α) := by
      have h_sum_rewrite :
          ∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2,
            (if x.1 i ≠ x.2 i then 1 else 0) =
          ∑ i : Fin n,
            (2 * choose_2 (B.card : ℚ) - 2 * ∑ α : F, choose_2 (K B i α)) :=
        sum_congr rfl fun i _ ↦ sum_of_not_equals |>.trans (by ring)
      rw [h_sum_rewrite, Finset.sum_sub_distrib, mul_sum _ _ _, sum_const,
        Finset.card_fin, nsmul_eq_mul]; ring!
    convert h_sum using 1 <;> ring_nf!
    convert d_eq_sum h_B using 1; ring!
  unfold choose_2 at *; norm_num at *; linarith!

/-- Pre-Johnson bound: convexity yields `n · (C₂(k) + (q-1) · C₂(…)) ≤ C₂(|B|) · (n - d)`. -/
lemma almost_johnson [Zero F] (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    n * (choose_2 (k B) + (card F - 1) *
      choose_2 ((B.card - k B) / (card F - 1))) ≤
    choose_2 B.card * (n - d B) :=
  le_trans (le_sum_sum_choose_K h_n (by grind only))
    (sum_sum_K_i_eq_n_sub_d h_B ▸ le_refl _)

/-- `choose_2`-free form of `almost_johnson`. -/
lemma almost_johnson_choose_2_elimed [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    (k B * (k B - 1) +
      (B.card - k B) * ((B.card - k B) / (card F - 1) - 1)) ≤
    B.card * (B.card - 1) * (n - d B) / n := by
  have h_expand : (card F - 1 : ℚ) ≠ 0 := sub_ne_zero_of_ne (by norm_cast; linarith)
  have h_expand : (2 : ℚ) * choose_2 (k B) + (2 : ℚ) * ((card F - 1) : ℚ) *
      choose_2 ((B.card - k B) / (card F - 1)) ≤
        (2 : ℚ) * choose_2 B.card * (n - d B) / n := by
    have h_expand : (2 : ℚ) * choose_2 (k B) + (2 : ℚ) * ((card F - 1) : ℚ) *
        choose_2 ((B.card - k B) / (card F - 1)) ≤
          (2 : ℚ) * choose_2 B.card * (n - d B) / n := by
      have := almost_johnson h_n h_B h_card
      rw [le_div_iff₀] <;> first | positivity | linarith
    convert h_expand using 1
  convert h_expand using 1 <;> push_cast [choose_2] <;> ring_nf!
  grind +ring

/-- LHS of the almost-Johnson bound divided by `|B|` in terms of `e` and `d`. -/
lemma almost_johnson_lhs_div_B_card [Zero F] (h_n : 0 < n) (h_B : 2 ≤ B.card) :
    (k B * (k B - 1) + (B.card - k B) * ((B.card - k B) / (card F - 1) - 1)) / B.card =
    (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 / ((card F - 1) * n ^ 2) - 1 := by
  set E := (n - e B 0) / n
  generalize eqrhs : (_ + _ - 1 : ℚ) = rhs
  have eqE : E = k B / B.card := by grind only [= k_and_e']
  suffices (B.card * E - 1) * E +
      ((B.card - B.card * E) / (card F - 1) - 1) * (1 - E) = rhs by
    rw [eqE, mul_div_cancel₀ _ (by simp only [ne_eq, Rat.natCast_eq_zero_iff]; omega)] at this
    rw [← this]; field_simp
  rw [← eqrhs]
  have : E = 1 - (e B 0) / n := by
    simp only [E]
    field_simp [show (n : ℚ) ≠ 0 from by exact_mod_cast Nat.pos_iff_ne_zero.mp h_n]
  grind only

/-- Unrefined Johnson bound in terms of `e`, `d`, and `|B|`. -/
lemma johnson_unrefined [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    (1 - e B 0 / n) ^ 2 * B.card + B.card * (e B 0) ^ 2 /
      ((card F - 1) * n ^ 2) - 1 ≤
    (B.card - 1) * (1 - d B / n) := by
  have h_rewrite : (k B * (k B - 1) + (B.card - k B) *
      ((B.card - k B) / (card F - 1) - 1)) / B.card ≤ (B.card - 1) *
      (1 - d B / n) := by
    have := almost_johnson_choose_2_elimed h_n h_B h_card; (
    rw [div_le_iff₀] <;> first | positivity | convert this using 1; ring_nf
    simpa [h_n.ne'] using by ring)
  convert h_rewrite using 1
  convert almost_johnson_lhs_div_B_card h_n h_B |> Eq.symm using 1

/-- Johnson bound multiplied through by `|B|`. -/
lemma johnson_unrefined_by_M [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    B.card * ((1 - e B 0 / n) ^ 2 + (e B 0) ^ 2 /
      ((card F - 1) * n ^ 2) - 1 + d B / n) ≤ d B / n := by
  suffices B.card * ((1 - e B 0 / n) ^ 2 + e B 0 ^ 2 /
      ((card F - 1) * n ^ 2)) - B.card * (1 - d B / n) + -1 +
    B.card * (1 - d B / n) ≤ (B.card - 1) * (1 - d B / n) by linarith
  exact le_trans (le_of_eq (by ring)) (johnson_unrefined h_n h_B h_card)

/-- Johnson bound scaled by `|F| / (|F| - 1)`. -/
lemma johnson_unrefined_by_M' [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    B.card * (card F / (card F - 1)) *
      ((1 - e B 0 / n) ^ 2 + e B 0 ^ 2 /
        ((card F - 1) * n ^ 2) - 1 + d B / n) ≤
    (card F / (card F - 1)) * d B / n := by
  rw [mul_comm (B.card : ℚ), mul_assoc, ← mul_div]
  exact mul_le_mul_of_nonneg_left (johnson_unrefined_by_M h_n h_B h_card)
    (le_of_lt (div_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) h_card)
      (by linarith [show (2 : ℚ) ≤ (card F : ℚ) from by exact_mod_cast h_card])))

/-- Algebraic identity expressing the Johnson LHS as a difference of squares. -/
lemma johnson_denom [Zero F] (h_card : 2 ≤ card F) :
    (card F / (card F - 1)) *
    ((1 - e B 0 / n) ^ 2 + (e B 0) ^ 2 /
      ((card F - 1) * n ^ 2) - 1 + d B / n) =
    (1 - (card F / (card F - 1)) *
    (e B 0 / n)) ^ 2 - (1 - (card F / (card F - 1)) * (d B / n)) := by
  set c := card F; set c1 := (c : ℚ) - 1
  have n₂ : c1 ≠ 0 := by simp [c1, c, sub_eq_zero]; grind only
  suffices c / c1 * (d B / n - 2 * e B 0 / n + c / c1 * e B 0 ^ 2 / n ^ 2) =
      (1 - c / c1 * (e B 0 / n)) ^ 2 - (1 - c / c1 * (d B / n)) by
    rw [← this]; have : c / c1 = 1 + 1 / c1 := by grind only
    grind only [= e.eq_1]
  grind only

/-- Johnson bound in squared-deviation form, at the zero vector. -/
lemma johnson_bound₀ [Zero F]
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    B.card * ((1 - ((card F : ℚ) / (card F - 1)) * (e B 0 / n)) ^ 2 -
      (1 - ((card F : ℚ) / (card F - 1)) * (d B / n))) ≤
    ((card F : ℚ) / (card F - 1)) * d B / n := by
  rw [← johnson_denom h_card, ← mul_assoc]
  exact johnson_unrefined_by_M' h_n h_B h_card

/-- Johnson bound generalised to an arbitrary centre `v` via linear shift. -/
protected lemma johnson_bound_lemma [Field F] {v : Fin n → F}
    (h_n : 0 < n) (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    B.card * ((1 - ((card F : ℚ) / (card F - 1)) * (e B v / n)) ^ 2 -
      (1 - ((card F : ℚ) / (card F - 1)) * (d B / n))) ≤
    ((card F : ℚ) / (card F - 1)) * d B / n := by
  rw [lin_shift_e (by omega), lin_shift_d h_B, lin_shift_card (v := v)]
  exact johnson_bound₀ h_n (lin_shift_card (B := B) ▸ h_B) h_card

/-- The normalised Hamming distance scaled by `q/(q-1)` stays in `[-1, 1]`. -/
protected lemma abs_one_sub_div_le_one {v a : Fin n → F}
    (h_card : 2 ≤ card F) :
    |1 - (1 + 1 / ((card F : ℚ) - 1)) * Δ₀(v, a) / n| ≤ 1 := by
  have h_bound : (1 + 1 / (card F - 1) : ℚ) * Δ₀(v, a) / n ≤ 2 := by
    have h_bound : (1 + 1 / (card F - 1) : ℚ) ≤ 2 := by
      rw [one_add_div, div_le_iff₀] <;>
        linarith [show (card F : ℚ) ≥ 2 by norm_cast]
    refine div_le_of_le_mul₀ ?_ ?_ ?_ <;> try linarith
    refine le_trans (mul_le_mul_of_nonneg_right h_bound (Nat.cast_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left
      (mod_cast le_trans (card_le_univ _) (by simp +decide)) zero_le_two
  refine abs_le.mpr ⟨?_, ?_⟩
  · lia
  · exact sub_le_self _ (div_nonneg (mul_nonneg (add_nonneg zero_le_one
      (one_div_nonneg.mpr (sub_nonneg.mpr (Nat.one_le_cast.mpr (by linarith)))))
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

/-- If `e ≤ n - √(n(n-d))` then `1 - d/n ≤ (1 - e/n)²`. -/
lemma johnson_hyp_implies_div_ineq {n d e : ℕ}
    (hn : 0 < n) (h_dn : d ≤ n)
    (h : (e : ℝ) ≤ n - √(n * (n - d))) :
    1 - (d : ℝ) / n ≤ (1 - (e : ℝ) / n) ^ 2 := by
  have h_mul : (n ^ 2 - n * d : ℝ) ≤ (n - e) ^ 2 := by
    nlinarith [sqrt_nonneg (n * (n - d)),
      mul_self_sqrt (show 0 ≤ (n : ℝ) * (n - d) by
        exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg_of_le (mod_cast h_dn)))]
  field_simp at *
  exact_mod_cast h_mul

/-- The ratio `e/n` cannot equal `J'(q, d/n)` under the Johnson hypothesis. -/
lemma johnson_e_div_ne_J {n d e : ℕ} {q : ℚ}
    (hn_pos : 0 < n) (hd_pos : 0 < d) (hq : 1 < q)
    (h_muln : ((e : ℚ) / n : ℝ) ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt)
    (h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J' q (d / n))
    (hqx : q / (q - 1) * (d / n) ≤ 1) :
    ((e : ℚ) / n : ℝ) ≠ J' q (d / n) := by
  intro h_eq
  set δ := (d : ℚ) / n
  set frac := q / (q - 1)
  have h_frac_pos : 1 < frac := by rw [lt_div_iff₀] <;> linarith
  have h_sqrt_eq : 1 - √(1 - δ) = (1 / frac) * (1 - √(1 - frac * δ)) := by
    convert h_eq using 1
    rw [le_antisymm h_muln]
    · norm_cast
    · aesop
  have h_frac_eq : 1 - √(1 - δ) = δ / (1 + √(1 - δ)) ∧ (1 / frac) *
      (1 - √(1 - frac * δ)) = δ / (1 + √(1 - frac * δ)) := by
    constructor
    · rw [eq_div_iff] <;> ring_nf <;> norm_num
      · rw [sq_sqrt] <;> norm_num
        exact_mod_cast div_le_one_of_le₀ (show (d : ℚ) ≤ n by
          exact_mod_cast Nat.le_of_lt_succ <| by
            rw [← @Nat.cast_lt ℚ]; push_cast
            nlinarith [show (1 : ℚ) ≤ d by exact_mod_cast hd_pos,
              show (1 : ℚ) ≤ n by exact_mod_cast hn_pos,
              mul_div_cancel₀ (d : ℚ) (by positivity : (n : ℚ) ≠ 0),
              div_mul_cancel₀ (q : ℚ) (by linarith : (q - 1 : ℚ) ≠ 0)]) (by positivity)
      · positivity
    · field_simp [frac] at *
      linarith [mul_self_sqrt (show 0 ≤ 1 - (frac : ℝ) * δ by
        exact sub_nonneg_of_le <| mod_cast hqx)]
  have h_sqrt_eq' : √(1 - frac * δ) = √(1 - δ) := by grind
  rw [sqrt_inj] at h_sqrt_eq' <;> norm_cast at * <;>
    nlinarith [show (0 : ℚ) < δ by positivity]

/-- Monotonicity of the worst-case Johnson quotient. -/
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
  have h_frac_ineq : (JohnsonBound.d B / n : ℚ) * (d / n - 2 * (e / n) +
      frac * (e / n) ^ 2) ≤ (d / n) * (JohnsonBound.d B / n - 2 *
        (JohnsonBound.e B v / n) + frac * (JohnsonBound.e B v / n) ^ 2) := by
    have h_frac_ineq :
        (JohnsonBound.d B / n - d / n) * (2 * (e / n) - frac * (e / n) ^ 2) ≥ 0 ∧
        (e / n - JohnsonBound.e B v / n) *
          (2 - frac * (e / n + JohnsonBound.e B v / n)) ≥ 0 := by
      refine ⟨mul_nonneg ?_ ?_, mul_nonneg ?_ ?_⟩
      · exact sub_nonneg_of_le (by gcongr)
      · have h_frac_le_one : frac * (e / n : ℚ) ≤ 1 := by
          have h_e_le_d : (e / n : ℚ) ≤ (d / n : ℚ) := by
            have h_e_le_d : (e : ℝ) ≤ n - √(n * (n - d)) := by grind
            have h_e_le_d : (e : ℚ) ≤ d := by
              exact_mod_cast (by nlinarith [
                show (d : ℝ) ≤ n by norm_cast, sqrt_nonneg (n * (n - d)), mul_self_sqrt (
                  show 0 ≤ (n : ℝ) * (n - d) by
                  nlinarith [show (d : ℝ) ≤ n by norm_cast])] : (e : ℝ) ≤ d)
            gcongr
          exact le_trans (mul_le_mul_of_nonneg_left h_e_le_d (by positivity)) h_d_close_n
        nlinarith [show 0 ≤ (e : ℚ) / n by positivity]
      · exact sub_nonneg_of_le (by gcongr)
      · have h_frac_e_n_le_1 : frac * (e / n : ℚ) ≤ 1 := by
          refine le_trans (mul_le_mul_of_nonneg_left (show (e : ℚ) / n ≤ d / n from ?_)
            (by positivity)) h_d_close_n
          have h_e_le_d : (e : ℚ) ≤ d := by
            exact_mod_cast (by nlinarith [
              show (d : ℝ) ≤ n by norm_cast, sqrt_nonneg (n * (n - d)), mul_self_sqrt (
                show 0 ≤ (n : ℝ) * (n - d) by
                nlinarith [show (d : ℝ) ≤ n by norm_cast])] : (e : ℝ) ≤ d)
          gcongr
        have h_frac_e_B_v_n_le_1 : frac * (JohnsonBound.e B v / n : ℚ) ≤ 1 :=
          le_trans (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (show (JohnsonBound.e B v : ℚ) ≤ e by
              exact_mod_cast e_ineq) (Nat.cast_nonneg _)) (by positivity)) h_frac_e_n_le_1
        linarith
    nlinarith [show (0 : ℚ) < n from hn_pos,
      mul_div_cancel₀ (e : ℚ) (by positivity : (n : ℚ) ≠ 0),
      mul_div_cancel₀ (JohnsonBound.e B v : ℚ) (by positivity : (n : ℚ) ≠ 0),
      mul_div_cancel₀ (d : ℚ) (by positivity : (n : ℚ) ≠ 0)]
  rw [div_le_div_iff₀] <;> ring_nf at * <;> try linarith
  by_cases h_e_zero : e = 0
  · aesop
  · have h_frac_pos : (n : ℚ)⁻¹ ^ 2 * e ^ 2 * frac > (n : ℚ)⁻¹ ^ 2 * e ^ 2 :=
      lt_mul_of_one_lt_right (by positivity) hfrac_gt1
    nlinarith [show (e : ℚ) ≥ 1 from by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h_e_zero]

/-- The Johnson denominator is bounded below by `q/(q-1) · d/n - 1`. -/
lemma johnson_den_ge_frac_d {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    {B : Finset (Fin n → F)} {v : Fin n → F} :
    (1 - ((card F : ℚ) / (card F - 1)) * (JohnsonBound.e B v / n)) ^ 2 -
      (1 - ((card F : ℚ) / (card F - 1)) * (JohnsonBound.d B / n)) ≥
    ((card F : ℚ) / (card F - 1)) * (JohnsonBound.d B / n) - 1 := by
  nlinarith [sq_nonneg (1 - ((card F : ℚ) / (card F - 1)) * (JohnsonBound.e B v / n))]

/-- When `q · d / ((q-1) · n) > 1`, there is a positive gap of size `≥ 1/((q-1)·n)`. -/
lemma johnson_gap_frac_d_gt_one {n d : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    {B : Finset (Fin n → F)}
    (q_not_small : (2 : ℚ) ≤ (card F : ℚ))
    (n_not_small : 1 ≤ n)
    (h_d_close_n : ((card F : ℚ) / (card F - 1)) * (d / n : ℚ) > 1)
    (hd_le_dB : (d : ℚ) ≤ JohnsonBound.d B) :
    (1 : ℚ) / ((n : ℚ) * ((card F : ℚ) - 1)) ≤
    ((card F : ℚ) / (card F - 1)) * (JohnsonBound.d B) / n - 1 := by
  have h_qd_ge : (card F : ℚ) * d ≥ (card F - 1) * n + 1 := by
    have : (card F : ℚ) * d > (card F - 1) * n := by
      rw [div_mul_div_comm, gt_iff_lt, lt_div_iff₀] at h_d_close_n <;>
        nlinarith [(by norm_cast : (1 : ℚ) ≤ n)]
    exact_mod_cast this
  field_simp at *
  rw [div_sub', div_le_div_iff_of_pos_right] <;>
    nlinarith [show (card F : ℚ) ≥ 2 from by exact_mod_cast q_not_small]

/-- Lower bound on `d/n` when `e = 0`. -/
lemma johnson_den_lb_e_zero {n d : ℕ} {q : ℚ}
    (hn_pos : 0 < n) (hq_ge1 : (1 : ℚ) ≤ q) (hd_ge1 : (1 : ℚ) ≤ (d : ℚ)) :
    (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (d : ℚ) / n := by
  gcongr
  nlinarith [show (n : ℚ) ≥ 1 from by exact_mod_cast hn_pos,
    show (q : ℚ) ≥ 1 from by exact_mod_cast hq_ge1,
    show (d : ℚ) ≥ 1 from by exact_mod_cast hd_ge1]

/-- Lower bound on the Johnson denominator when `e > 0`. -/
lemma johnson_den_lb_e_pos {n d e : ℕ} {q frac : ℚ}
    (hn_pos : (0 : ℚ) < n) (hq_ne : (q : ℚ) ≠ 0) (he0 : e ≠ 0)
    (one_div_q_le : (1 : ℚ) / q ≤ frac - 1) (hfrac1_pos : (0 : ℚ) < frac - 1)
    (hbase_nonneg : (0 : ℚ) ≤ (d / n : ℚ) - 2 * (e / n : ℚ) + (e / n : ℚ) ^ 2) :
    (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤
    (d / n : ℚ) - 2 * (e / n : ℚ) + frac * (e / n : ℚ) ^ 2 := by
  have h_e_div_n_ge : (e / n : ℚ) ^ 2 ≥ 1 / (n : ℚ) ^ 2 := by
    field_simp; exact_mod_cast Nat.one_le_pow _ _ (Nat.pos_of_ne_zero he0)
  ring_nf at *; nlinarith [mul_inv_cancel₀ hq_ne]

/-- `q · d · n ≥ 2` when `q ≥ 2`, `d ≥ 1`, `n ≥ 1`. -/
lemma johnson_qdn_ge_two {q : ℚ} {d n : ℕ}
    (hq : (2 : ℚ) ≤ q) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by
  have : (1 : ℚ) ≤ (d : ℚ) * (n : ℚ) :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  nlinarith

/-- The average pairwise distance `d(B)` is at most `n`. -/
lemma johnson_d_le_n {n : ℕ} {F : Type*} [DecidableEq F]
    {B : Finset (Fin n → F)} (hB : 2 ≤ B.card) :
    JohnsonBound.d B ≤ (n : ℚ) := by
  unfold d; field_simp
  rw [div_le_iff₀]
  · have h_sum_le :
        ∑ x ∈ B.product B with x.1 ≠ x.2, Δ₀(x.1, x.2) ≤
        ∑ x ∈ B.product B with x.1 ≠ x.2, n :=
      sum_le_sum fun x _ ↦ le_trans (card_le_univ _) (by simp)
    refine le_trans (Nat.cast_le.mpr h_sum_le) ?_
    norm_cast; simp [choose_2]; ring_nf
    rw [show (filter (fun x : (Fin n → F) × (Fin n → F) ↦
        ¬x.1 = x.2) (B ×ˢ B)) = offDiag B from by ext; aesop]
    simp only [offDiag_card, le_neg_add_iff_add_le]; ring_nf
    rw [Nat.cast_sub] <;> push_cast <;> nlinarith only [hB]
  · exact div_pos
      (mul_pos (Nat.cast_pos.mpr (by linarith))
        (sub_pos.mpr (Nat.one_lt_cast.mpr (by linarith))))
      zero_lt_two

end

end JohnsonBound
