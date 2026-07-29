/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Flat.TorsionFree


/-!
## Main Results

- Lemma 7.1. [BCGM25]: Mutual correlated agreement (MCA) for the affine line generator implies
MCA for the affine space generator.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

namespace AffineMCALemmas

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations LinearCode Affine
open scoped ProbabilityTheory NNReal ENNReal BigOperators


variable {ι : Type}
         {F : Type} [Field F]

/-- The affine line combination `vecMul (1, t) W = W 0 + t • W 1`. -/
lemma line_vecMul (W : Fin 2 → (ι → F)) (t : F) :
  Matrix.vecMul (AffineLineGenerator F t) W = W 0 + t • W 1 := by
  aesop (add simp [AffineLineGenerator, Matrix.vecMul])

/-- If the affine combination restricted to `T` is in a linear code, but
some `U j` restricted to `T` does not lie in the code, then there is a codeword `U (i + 1)` which is
not a codeword in the `T`-projected code. -/
lemma exists_succ_not_mem [Fintype ι] {s : ℕ} (LC : LinearCode ι F) (T : Finset ι)
    (U : Fin (s + 1) → (ι → F)) (x : Fin s → F)
    (hv : projectedWord (affineComb U x) T ∈ projectedCode_submod LC T)
    (hj : ∃ j : Fin (s + 1), projectedWord (U j) T ∉ projectedCode_submod LC T) :
    ∃ i : Fin s, projectedWord (U i.succ) T ∉ projectedCode_submod LC T := by
  contrapose! hj
  intro j
  induction j using Fin.inductionOn
  · have h_aff : affineComb U x = U 0 + linComb U x := by
      ext k; simp [affineComb, linComb, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    have hj' : ∀ i : Fin s, projectedWord (U i.succ) T ∈ projectedCode LC T := by
      simpa using hj
    have h_linComb : projectedWord (linComb U x) T ∈ projectedCode_submod LC T := by
      simp only [mem_projectedCode_submod]
      change projectedWord (∑ i, x i • U i.succ) T ∈ projectedCode LC.carrier T
      exact LinearCode.projectedCode_linearCombination LC T (fun i => U i.succ) x hj'
    have h_split : projectedWord (affineComb U x) T =
        projectedWord (U 0) T + projectedWord (linComb U x) T := by
      rw [h_aff]
      rfl
    have hmem := Submodule.sub_mem _ (h_split ▸ hv) h_linComb
    rwa [add_sub_cancel_right] at hmem
  · exact hj _

/-- The quotient of the projected word space `T → F` by the projected code on `T`, used in the
kernel/rank-nullity argument of Step 2. -/
abbrev projectedQuotient [Fintype ι] (LC : LinearCode ι F) (T : Finset ι) : Type :=
  (T → F) ⧸ LC.projectedCode_submod T

open Classical in
/-- If some direction codeword `w i` does not project into the code on `T`, then the set of
coefficient vectors `l` whose combination `∑ i, l i • w i` projects into the code has cardinality
at most `|F| ^ (s-1)`. -/
lemma proj_lincomb_ker_card_le [Fintype F] [Fintype ι] {s : ℕ}
    (LC : LinearCode ι F) (T : Finset ι) (w : Fin s → (ι → F))
    (hne : ∃ i, projectedWord (w i) T ∉ projectedCode_submod LC T) :
    (Finset.univ.filter (fun l : Fin s → F =>
        projectedWord (∑ i, l i • w i) T ∈ projectedCode_submod LC T)).card
      ≤ (Fintype.card F) ^ (s - 1) := by
  set g : (Fin s → F) →ₗ[F] projectedQuotient LC T :=
    Submodule.mkQ (LC.projectedCode_submod T) ∘ₗ
      LinearMap.funLeft F F (Subtype.val : T → ι) ∘ₗ Fintype.linearCombination F w with hg_def
  have hker : Module.finrank F (LinearMap.ker g) ≤ s - 1 := by
    obtain ⟨i, hi⟩ := hne
    have h_range : LinearMap.range g ≠ ⊥ := by
      have : ∃ x, ¬g x = 0 := ⟨Pi.single i 1, by aesop⟩
      simp_all [Submodule.eq_bot_iff]
    have hrank_null := LinearMap.finrank_range_add_finrank_ker g
    simp_all only [ne_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ge_iff_le]
    exact Nat.le_sub_one_of_lt
      (lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (by aesop))) hrank_null.le)
  have hcard : Fintype.card (LinearMap.ker g) ≤ (Fintype.card F) ^ (s - 1) := by
    rw [Module.card_eq_pow_finrank (K := F)]
    exact pow_le_pow_right₀ (Fintype.card_pos) hker
  aesop (add simp [Fintype.card_subtype])

/-- If a sum of nonnegative integer counts over all `|F|^s` coefficient vectors is bounded by
`|F|^(s-1) * m`, then some coefficient vector achieves a count whose `|F|`-fold is at most `m`. -/
lemma exists_avg_le [Fintype F] {s : ℕ} (hs : 1 ≤ s) (f : (Fin s → F) → ℕ) (m : ℕ)
    (hsum : ∑ l, f l ≤ (Fintype.card F) ^ (s - 1) * m) :
    ∃ l, (Fintype.card F : ℝ) * f l ≤ m := by
  by_contra h_contra
  push Not at h_contra
  norm_cast at *
  have hsum_lt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun l _ => h_contra l
  simp_all only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum _ _ _]
  cases s <;> simp_all [pow_succ', mul_assoc]
  nlinarith

open Classical in
/-- For a fixed direction `d`, some base point `v` makes the line `t ↦ v + t • d` hit the set `B'`
with (normalized) frequency at least the density of `B'`. -/
lemma exists_dir_line_ge [Fintype F] [Nonempty F] {s : ℕ}
    (d : Fin s → F) (B' : Finset (Fin s → F)) :
    ∃ v : Fin s → F,
      ((B'.card : ℝ) / (Fintype.card F) ^ s) ≤
        ((Finset.univ.filter (fun t : F => v + t • d ∈ B')).card : ℝ) / (Fintype.card F) := by
  set q := Fintype.card F
  have h_card_eq : ∀ t : F, Finset.card (Finset.filter (fun v => v + t • d ∈ B') Finset.univ) =
      Finset.card B' := by
    intro t
    have hinj : Function.Injective (fun v : Fin s → F => v + t • d) := fun v w h => by simpa using h
    rw [← Finset.card_image_of_injective _ hinj]
    congr
    ext
    aesop
  have h_inner : ∀ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) = B'.card := by
    intro t
    have := h_card_eq t
    aesop
  have h_swap : ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card =
      ∑ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    aesop
  have h_sum :
      ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card = q * B'.card := by
    rw [h_swap]
    simp only [h_inner, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  contrapose! h_sum
  have hsum_lt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun v _ => h_sum v
  simp_all only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, ne_eq]
  rw [mul_div_cancel₀] at hsum_lt <;> simp_all only [← Finset.sum_div _ _ _, ne_eq,
    pow_eq_zero_iff', Nat.cast_eq_zero, Fintype.card_ne_zero, false_and, not_false_eq_true]
  rw [div_lt_iff₀] at hsum_lt <;> norm_cast at * <;> nlinarith [show q > 0 from Fintype.card_pos]


open Classical in
/-- There is a choice of two line-codewords `W` so that `(1 - 1/|F|)` times the density of
affine-space bad seeds is at most the density of affine-line bad seeds for `W`. -/
lemma exists_line_bound [Fintype F] [Fintype ι] {s : ℕ} (hs : 1 ≤ s)
    (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F)) (γ : unitInterval) :
    ∃ W : Fin 2 → (ι → F),
      (1 - 1 / (Fintype.card F : ℝ)) *
        (((Finset.univ.filter (fun x : Fin s → F =>
            IsMCA (AffineSpaceGenerator F s) LC x U γ)).card : ℝ) / (Fintype.card F) ^ s)
      ≤ ((Finset.univ.filter (fun t : F =>
            IsMCA (AffineLineGenerator F) LC t W γ)).card : ℝ) / (Fintype.card F) := by
  set isB := fun x => IsMCA (AffineSpaceGenerator F s) LC x U γ
  set Bset := Finset.univ.filter isB
  set m := Bset.card
  obtain ⟨T, hT⟩ :
    ∃ T : (Fin s → F) → (Finset ι), ∀ x, isB x → (T x).card ≥ (Fintype.card ι) * (1 - (γ : ℝ)) ∧
      projectedWord (affineComb U x) (T x) ∈ projectedCode_submod LC (T x) ∧
      ∃ j, projectedWord (U j) (T x) ∉ projectedCode_submod LC (T x) := by
    choose! T hT using fun x (hx : isB x) => hx
    use T
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x)
                       ∈ projectedCode_submod LC (T x))).card ≤ m / (Fintype.card F : ℝ) := by
    have h_per_seed_le : ∀ x ∈ Bset, ∑ lam : Fin s → F, (if projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x) then 1 else 0) ≤ (Fintype.card F) ^ (s - 1) := by
      intro x hx
      have h_ker : ∃ i : Fin s, projectedWord (U i.succ) (T x) ∉ projectedCode_submod LC (T x) :=
        exists_succ_not_mem LC (T x) U x (hT x (Finset.mem_filter.mp hx |>.2) |>.2.1)
              (hT x (Finset.mem_filter.mp hx |>.2) |>.2.2)
      have h_proj_bound := proj_lincomb_ker_card_le LC (T x) (fun i => U i.succ) h_ker
      aesop
    have h_sum : ∑ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x) ∈
                  projectedCode_submod LC (T x))).card ≤ m * (Fintype.card F) ^ (s - 1) := by
      convert Finset.sum_le_sum h_per_seed_le using 1
      · rw [Finset.sum_comm, Finset.sum_congr rfl]
        aesop
      · simp +zetaDelta
    have havg := exists_avg_le hs (fun lam => (Bset.filter (fun x => projectedWord (linComb U lam)
          (T x) ∈ LC.projectedCode_submod (T x) ) |> Finset.card)) m ?_
    · exact havg.imp fun x hx => by rwa [le_div_iff₀' (Nat.cast_pos.mpr <| Fintype.card_pos)]
    · linarith
  obtain ⟨v, hv⟩ : ∃ v : Fin s → F, ((Bset.filter (fun x => ¬projectedWord (linComb U lam) (T x) ∈
          projectedCode_submod LC (T x))).card : ℝ) / (Fintype.card F) ^ s ≤
          ((Finset.univ.filter (fun t : F => v + t • lam ∈ Bset ∧
           ¬projectedWord (linComb U lam) (T (v + t • lam)) ∈
           projectedCode_submod LC (T (v + t • lam)))).card : ℝ) / (Fintype.card F) := by
    have hdir := exists_dir_line_ge lam (Bset.filter fun x => ¬projectedWord (linComb U lam) (T x) ∈
            LC.projectedCode_submod (T x))
    aesop
  refine ⟨![affineComb U v, linComb U lam], le_trans ?_ (hv.trans ?_ )⟩
  · convert mul_le_mul_of_nonneg_right
        (show (1 - 1 / (Fintype.card F : ℝ)) * m ≤ (
          Finset.filter (fun x => ¬projectedWord (linComb U lam ) ( T x ) ∈
          LC.projectedCode_submod (T x)) Bset |> Finset.card : ℝ) from ?_)
          (by positivity : 0 ≤ (Fintype.card F : ℝ) ⁻¹ ^ s) using 1
    · ring
    · ring
    · rw [one_sub_div, div_mul_eq_mul_div, div_le_iff₀] <;> norm_cast <;> norm_num
      · rw [le_div_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at hlam
        norm_cast at *
        rw [Int.subNatNat_eq_coe]
        push_cast
        have hcard_gt_one : Fintype.card F > 1 := Fintype.one_lt_card
        have hpartition : Finset.card (Finset.filter
              (fun x => projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset)
            + Finset.card (Finset.filter
              (fun x => ¬projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset) = m := by
          rw [Finset.card_filter_add_card_filter_not]
        aesop (add safe (by nlinarith))
  · gcongr
    intro h
    use T (v + ‹_› • lam)
    simp_all only [ge_iff_le, Finset.mem_univ, line_vecMul, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.exists_fin_two, not_false_eq_true, or_true,
      and_true]
    exact ⟨hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.1,
        by simpa only [affineComb_line] using hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.2.1⟩

end AffineMCALemmas

namespace AffineMCAMain

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations LinearCode AffineMCALemmas
open scoped ProbabilityTheory NNReal ENNReal BigOperators


variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]

/-- Lemma 7.1. [BCGM25].
The affine line generator `F → F²`, `x ↦ (1, x)`, having MCA error `ε_mca` for `LC` implies that
the affine space generator `Fˡ → Fˡ⁺¹`, `x ↦ (1, x)`, has MCA for `LC` with error
`(1 - 1/|F|)⁻¹ • ε_mca`. -/
theorem AffineLine_MCA_AffineSpaceMCA {ℓ : ℕ} (hℓ : ℓ ≥ 2) (ε_mca : I → ℝ) (LC : LinearCode ι F)
    (hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca LC) :
    letI a := (1 - 1 / Fintype.card F : ℝ)
    letI ε_mca' := a⁻¹ • ε_mca
    IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' LC := by
  classical
  intro U γ
  set a : ℝ := (1 - 1 / (Fintype.card F : ℝ))
  have ha : 0 < a := by
    have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hs : 1 ≤ ℓ := by omega
  rw [prob_uniform_eq_ofReal]
  have hcard : (Fintype.card (Fin ℓ → F) : ℝ) = (Fintype.card F : ℝ) ^ ℓ := by
    norm_cast
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨W, hW⟩ := AffineMCALemmas.exists_line_bound hs LC U γ
  have hline := hGMCA W γ
  rw [prob_uniform_eq_ofReal] at hline
  set sp : ℝ :=
    ((Finset.univ.filter (fun x : Fin ℓ → F =>
        IsMCA (AffineSpaceGenerator F ℓ) LC x U γ)).card : ℝ) with hsp
  set ln : ℝ :=
    ((Finset.univ.filter (fun t : F =>
        IsMCA (AffineLineGenerator F) LC t W γ)).card : ℝ) with hln
  have hsp0 : 0 ≤ sp / (Fintype.card F : ℝ) ^ ℓ := by positivity
  have hln0 : 0 ≤ ln / (Fintype.card F : ℝ) := by positivity
  by_cases hε : 0 ≤ ε_mca γ
  · have hlre : ln / (Fintype.card F : ℝ) ≤ ε_mca γ :=
      (ENNReal.ofReal_le_ofReal_iff hε).mp hline
    have hchain : a * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ ε_mca γ := le_trans hW hlre
    have hfin : sp / (Fintype.card F : ℝ) ^ ℓ ≤ a⁻¹ * ε_mca γ := by
      rw [inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
      exact hchain
    exact ENNReal.ofReal_le_ofReal hfin
  · push Not at hε
    have h0 : ENNReal.ofReal (ε_mca γ) = 0 := ENNReal.ofReal_of_nonpos (le_of_lt hε)
    rw [h0] at hline
    have hln_le : ln / (Fintype.card F : ℝ) ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp (le_antisymm hline zero_le)
    have hln_eq : ln / (Fintype.card F : ℝ) = 0 := le_antisymm hln_le hln0
    have hchain : a * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ 0 := by
      rw [← hln_eq]; exact hW
    have hsp_eq : sp / (Fintype.card F : ℝ) ^ ℓ = 0 := by
      by_contra h
      have hpos : 0 < sp / (Fintype.card F : ℝ) ^ ℓ := lt_of_le_of_ne hsp0 (Ne.symm h)
      have : 0 < a * (sp / (Fintype.card F : ℝ) ^ ℓ) := mul_pos ha hpos
      linarith
    rw [hsp_eq]
    simp

end AffineMCAMain
