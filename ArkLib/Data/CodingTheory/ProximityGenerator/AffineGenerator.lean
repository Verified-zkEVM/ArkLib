/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.FieldTheory.Finiteness

/-!
# Mutual correlated agreement for affine space generators

Mutual correlated agreement for the affine line generator `F → F²`, `x ↦ (1, x)`, on a module
code over `F` implies it for the affine space generator `Fˡ → Fˡ⁺¹`, `x ↦ (1, x)`, with the error
scaled by `(1 - 1/|F|)⁻¹`.

The scaling is what passing from lines to spaces costs: the density of bad affine-space seeds is
bounded, up to the factor `(1 - 1/|F|)`, by the density of bad affine-line seeds for a single
well-chosen pair of words, to which the line generator's own error then applies.

The error is valued in `ℝ≥0` rather than `I`, since the scaled error may exceed `1`.

## Main statements

* `AffineMCAMain.isMCAGenerator_affineSpaceGenerator_of_affineLineGenerator` — the implication, at
  the scaled error.
* `AffineMCALemmas.exists_line_bound` — the counting step it rests on.

The correspondence to [BCGM25]'s numbered statements is in
`docs/kb/audits/bcgm25-mca-generators.md`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

namespace AffineMCALemmas

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations LinearCode Affine
open scoped ProbabilityTheory NNReal ENNReal BigOperators


variable {ι : Type}
         {F : Type} [Field F]
         {A : Type} [AddCommGroup A] [Module F A]

/-- The affine line combination `∑ j, (1, t) j • W j = W 0 + t • W 1`. -/
lemma affineLineGenerator_sum_smul (W : Fin 2 → (ι → A)) (t : F) :
    (fun k => ∑ j, AffineLineGenerator F t j • W j k) = W 0 + t • W 1 := by
  ext k
  simp [AffineLineGenerator, Fin.sum_univ_two]

/-- The affine space combination `∑ j, (1, x) j • U j` is `affineComb U x`. -/
lemma affineSpaceGenerator_sum_smul {s : ℕ} (U : Fin (s + 1) → (ι → A)) (x : Fin s → F) :
    (fun k => ∑ j, AffineSpaceGenerator F s x j • U j k) = affineComb U x := by
  ext k
  simp [AffineSpaceGenerator, affineComb, Fin.sum_univ_succ]

/-- If the affine combination restricted to `T` is in a linear code, but
some `U j` restricted to `T` does not lie in the code, then there is a codeword `U (i + 1)` which is
not a codeword in the `T`-projected code. -/
lemma exists_succ_not_mem {s : ℕ} (MC : ModuleCode ι F A) (T : Finset ι)
    (U : Fin (s + 1) → (ι → A)) (x : Fin s → F)
    (hv : projectedWord (affineComb U x) T ∈ projectedCodeSubmod MC T)
    (hj : ∃ j : Fin (s + 1), projectedWord (U j) T ∉ projectedCodeSubmod MC T) :
    ∃ i : Fin s, projectedWord (U i.succ) T ∉ projectedCodeSubmod MC T := by
  contrapose! hj
  intro j
  induction j using Fin.inductionOn
  · have h_aff : affineComb U x = U 0 + linComb U x := rfl
    have hj' : ∀ i : Fin s, projectedWord (U i.succ) T ∈ projectedCode MC.carrier T :=
      fun i => (LinearCode.mem_projectedCodeSubmod_iff MC T _).mp (hj i)
    have h_linComb : projectedWord (linComb U x) T ∈ projectedCodeSubmod MC T := by
      rw [LinearCode.mem_projectedCodeSubmod_iff]
      exact LinearCode.projectedCode_linearCombination MC T (fun i => U i.succ) x hj'
    have h_split : projectedWord (affineComb U x) T =
        projectedWord (U 0) T + projectedWord (linComb U x) T := by
      rw [h_aff]
      rfl
    have hmem := Submodule.sub_mem _ (h_split ▸ hv) h_linComb
    rwa [add_sub_cancel_right] at hmem
  · exact hj _

/-- The quotient of the projected word space `T → A` by the projected code on `T`, used in the
kernel/rank-nullity argument of Step 2. -/
abbrev projectedQuotient (MC : ModuleCode ι F A) (T : Finset ι) : Type :=
  (T → A) ⧸ projectedCodeSubmod MC T

open Classical in
/-- If some direction codeword `w i` does not project into the code on `T`, then the set of
coefficient vectors `l` whose combination `∑ i, l i • w i` projects into the code has cardinality
at most `|F| ^ (s-1)`. -/
lemma proj_lincomb_ker_card_le [Fintype F] {s : ℕ}
    (MC : ModuleCode ι F A) (T : Finset ι) (w : Fin s → (ι → A))
    (hne : ∃ i, projectedWord (w i) T ∉ projectedCodeSubmod MC T) :
    (Finset.univ.filter (fun l : Fin s → F =>
        projectedWord (fun k => ∑ i, l i • w i k) T ∈ projectedCodeSubmod MC T)).card
      ≤ (Fintype.card F) ^ (s - 1) := by
  set g : (Fin s → F) →ₗ[F] projectedQuotient MC T :=
    Submodule.mkQ (projectedCodeSubmod MC T) ∘ₗ
      LinearMap.funLeft F A (Subtype.val : T → ι) ∘ₗ Fintype.linearCombination F w with hg_def
  have hker : Module.finrank F (LinearMap.ker g) ≤ s - 1 := by
    obtain ⟨i, hi⟩ := hne
    have h_range : LinearMap.range g ≠ ⊥ := by
      simp_all only [ne_eq, Submodule.eq_bot_iff, LinearMap.mem_range, LinearMap.coe_comp,
        Function.comp_apply, Submodule.mkQ_apply, forall_exists_index, forall_apply_eq_imp_iff,
        Submodule.Quotient.mk_eq_zero, not_forall]
      exact ⟨Pi.single i 1, by
        simp_all only [Fintype.linearCombination_apply_single, one_smul, g]
        exact hi⟩
    have hrank_null := LinearMap.finrank_range_add_finrank_ker g
    simp_all only [ne_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ge_iff_le]
    exact Nat.le_sub_one_of_lt
      (lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (by aesop))) hrank_null.le)
  have hcard : Fintype.card (LinearMap.ker g) ≤ (Fintype.card F) ^ (s - 1) := by
    rw [Module.card_eq_pow_finrank (K := F)]
    exact pow_le_pow_right₀ (Fintype.card_pos) hker
  convert hcard using 1
  simp only [LinearMap.mem_ker, hg_def, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [Fintype.card_subtype]
  congr
  ext
  simp only [projectedWord, Fintype.linearCombination_apply, map_sum, map_smul]
  congr! 1
  ext
  simp [Finset.sum_apply, LinearMap.funLeft_apply]

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
    (MC : ModuleCode ι F A) (U : Fin (s + 1) → (ι → A)) (γ : ℝ) :
    ∃ W : Fin 2 → (ι → A),
      (1 - 1 / (Fintype.card F : ℝ)) *
        (((Finset.univ.filter (fun x : Fin s → F =>
            IsMCA (AffineSpaceGenerator F s) MC x U γ)).card : ℝ) / (Fintype.card F) ^ s)
      ≤ ((Finset.univ.filter (fun t : F =>
            IsMCA (AffineLineGenerator F) MC t W γ)).card : ℝ) / (Fintype.card F) := by
  set isB := fun x => IsMCA (AffineSpaceGenerator F s) MC x U γ
  set Bset := Finset.univ.filter isB
  set m := Bset.card
  obtain ⟨T, hT⟩ :
    ∃ T : (Fin s → F) → (Finset ι), ∀ x, isB x → (T x).card ≥ (Fintype.card ι) * (1 - (γ : ℝ)) ∧
      projectedWord (affineComb U x) (T x) ∈ projectedCodeSubmod MC (T x) ∧
      ∃ j, projectedWord (U j) (T x) ∉ projectedCodeSubmod MC (T x) := by
    choose! T hT using fun x (hx : isB x) => hx
    exact ⟨T, fun x hx => by rw [← affineSpaceGenerator_sum_smul]; exact hT x hx⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x)
                       ∈ projectedCodeSubmod MC (T x))).card ≤ m / (Fintype.card F : ℝ) := by
    have h_per_seed_le : ∀ x ∈ Bset, ∑ lam : Fin s → F, (if projectedWord (linComb U lam) (T x) ∈
                projectedCodeSubmod MC (T x) then 1 else 0) ≤ (Fintype.card F) ^ (s - 1) := by
      intro x hx
      have h_ker : ∃ i : Fin s, projectedWord (U i.succ) (T x) ∉ projectedCodeSubmod MC (T x) :=
        exists_succ_not_mem MC (T x) U x (hT x (Finset.mem_filter.mp hx |>.2) |>.2.1)
              (hT x (Finset.mem_filter.mp hx |>.2) |>.2.2)
      have h_proj_bound := proj_lincomb_ker_card_le MC (T x) (fun i => U i.succ) h_ker
      aesop
    have h_sum : ∑ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x) ∈
                  projectedCodeSubmod MC (T x))).card ≤ m * (Fintype.card F) ^ (s - 1) := by
      convert Finset.sum_le_sum h_per_seed_le using 1
      · rfl
      · rw [Finset.sum_comm, Finset.sum_congr rfl]
        aesop
      · simp +zetaDelta
    have havg := exists_avg_le hs (fun lam : Fin s → F =>
      (Bset.filter (fun x => projectedWord (linComb U lam) (T x) ∈
        projectedCodeSubmod MC (T x)) |> Finset.card)) m ?_
    · exact havg.imp fun x hx => by rwa [le_div_iff₀' (Nat.cast_pos.mpr <| Fintype.card_pos)]
    · linarith
  obtain ⟨v, hv⟩ : ∃ v : Fin s → F, ((Bset.filter (fun x => ¬projectedWord (linComb U lam) (T x) ∈
          projectedCodeSubmod MC (T x))).card : ℝ) / (Fintype.card F) ^ s ≤
          ((Finset.univ.filter (fun t : F => v + t • lam ∈ Bset ∧
           ¬projectedWord (linComb U lam) (T (v + t • lam)) ∈
           projectedCodeSubmod MC (T (v + t • lam)))).card : ℝ) / (Fintype.card F) := by
    have hdir := exists_dir_line_ge lam (Bset.filter fun x => ¬projectedWord (linComb U lam) (T x) ∈
            projectedCodeSubmod MC (T x))
    aesop
  refine ⟨![affineComb U v, linComb U lam], le_trans ?_ (hv.trans ?_ )⟩
  · convert mul_le_mul_of_nonneg_right
        (show (1 - 1 / (Fintype.card F : ℝ)) * m ≤ (
          Finset.filter (fun x => ¬projectedWord (linComb U lam ) ( T x ) ∈
          projectedCodeSubmod MC (T x)) Bset |> Finset.card : ℝ) from ?_)
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
                projectedCodeSubmod MC (T x)) Bset)
            + Finset.card (Finset.filter
              (fun x => ¬projectedWord (linComb U lam) (T x) ∈
                projectedCodeSubmod MC (T x)) Bset) = m := by
          rw [Finset.card_filter_add_card_filter_not]
        nlinarith [hcard_gt_one, hpartition]
  · gcongr
    intro h
    use T (v + ‹_› • lam)
    simp_all only [ge_iff_le, Finset.mem_univ, affineLineGenerator_sum_smul, Fin.isValue,
      Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.exists_fin_two, not_false_eq_true, or_true,
      and_true]
    exact ⟨hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.1,
        by simpa only [affineComb_line] using hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.2.1⟩

end AffineMCALemmas

namespace AffineMCAMain

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations LinearCode AffineMCALemmas
open scoped ProbabilityTheory NNReal ENNReal BigOperators
open Probability


variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]
         {A : Type} [AddCommMonoid A] [Module F A]

/-- The affine line generator `F → F²`, `x ↦ (1, x)`, having MCA error `ε_mca` for `MC` implies that
the affine space generator `Fˡ → Fˡ⁺¹`, `x ↦ (1, x)`, has MCA for `MC` with error
`(1 - 1/|F|)⁻¹ • ε_mca`.

Only `ℓ ≥ 1` is required: at `ℓ = 1` the affine space generator *is* the affine line generator, so
the conclusion is immediate, and the proof below covers that case uniformly.

The error is valued in `ℝ≥0` rather than `I`, since `(1 - 1/|F|)⁻¹ • ε_mca` may exceed `1`. -/
theorem isMCAGenerator_affineSpaceGenerator_of_affineLineGenerator {ℓ : ℕ} (hℓ : ℓ ≥ 1)
    (ε_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca MC) :
    letI a := (1 - 1 / Fintype.card F : ℝ≥0)
    letI ε_mca' := a⁻¹ • ε_mca
    IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' MC := by
  let := Module.addCommMonoidToAddCommGroup F (M := A)
  classical
  intro γ
  refine iSup_le fun U => ?_
  set a : ℝ≥0 := (1 - 1 / (Fintype.card F : ℝ≥0)) with ha_def
  have hcard1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hinv_le : (1 : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast Fintype.card_pos
  have ha_coe : (a : ℝ) = 1 - 1 / (Fintype.card F : ℝ) := by
    rw [ha_def, NNReal.coe_sub hinv_le]; push_cast; ring
  have ha : 0 < (a : ℝ) := by
    rw [ha_coe, sub_pos, div_lt_one (by linarith)]; linarith
  rw [prob_uniform_eq_ofReal]
  have hcard : (Fintype.card (Fin ℓ → F) : ℝ) = (Fintype.card F : ℝ) ^ ℓ := by
    norm_cast
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨W, hW⟩ := AffineMCALemmas.exists_line_bound hℓ MC U γ
  have hline := hGMCA.prob_le W γ
  rw [prob_uniform_eq_ofReal] at hline
  set sp : ℝ :=
    ((Finset.univ.filter (fun x : Fin ℓ → F =>
        IsMCA (AffineSpaceGenerator F ℓ) MC x U γ)).card : ℝ) with hsp
  set ln : ℝ :=
    ((Finset.univ.filter (fun t : F =>
        IsMCA (AffineLineGenerator F) MC t W γ)).card : ℝ) with hln
  have hlre : ln / (Fintype.card F : ℝ) ≤ (ε_mca γ : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (ε_mca γ).coe_nonneg).mp
      (by rwa [← ENNReal.ofReal_coe_nnreal] at hline)
  have hchain : (a : ℝ) * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ (ε_mca γ : ℝ) :=
    le_trans (ha_coe ▸ hW) hlre
  have hfin : sp / (Fintype.card F : ℝ) ^ ℓ ≤ (a : ℝ)⁻¹ * (ε_mca γ : ℝ) := by
    rw [inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
    exact hchain
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mul, NNReal.coe_inv]
  exact ENNReal.ofReal_le_ofReal hfin

end AffineMCAMain
