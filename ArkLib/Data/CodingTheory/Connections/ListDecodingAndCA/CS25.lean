/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# CS25 integer-radius CA-to-list-size bound

This file proves the integer-grid CA-to-list-size theorem for consecutive Reed--Solomon
dimensions.

## Main result

- `rs_Lambda_extended_le_of_epsCa_int_radius` gives the exact ceiling bound from CS25.

## References

- [CS25] Crites--Stewart, Theorem 2.
-/

-- The proof-term statements below carry unused `Fintype`/`DecidableEq`/section hypotheses
-- (surfaced by the 4.32 linters when these proposition-valued `def`s became `theorem`s);
-- silenced file-wide to match the `CapacityBounds.lean` umbrella, scoped narrowly on revisit.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code CoreDefinitions ProximityGap

section CAImpliesList

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal in
private theorem rs_eps_ca_ne_top (C : Set (ι → F)) (δ_fld δ_int : ℝ≥0) :
    ProximityGap.epsCa (F := F) (A := F) C δ_fld δ_int ≠ ⊤ := by
  classical
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  unfold ProximityGap.epsCa
  refine iSup_le fun u => ?_
  split_ifs
  · exact zero_le_one
  · exact PMF.coe_le_one _ _

private def rs_reciprocal_stack (domain : ι ↪ F) (u : ι → F) (a : F) :
    Code.WordStack F (Fin 2) ι :=
  fun j i => Fin.cases (u i / (domain i - a)) (fun _ => -1 / (domain i - a)) j

private theorem rs_reciprocal_stack_one_apply (domain : ι ↪ F) (u : ι → F) (a : F) (i : ι) :
    rs_reciprocal_stack domain u a 1 i = -1 / (domain i - a) := by
  rfl

private theorem rs_reciprocal_stack_zero_apply (domain : ι ↪ F) (u : ι → F) (a : F) (i : ι) :
    rs_reciprocal_stack domain u a 0 i = u i / (domain i - a) := by
  rfl

open scoped NNReal ProbabilityTheory in
private theorem rs_fold_probability_le_eps_ca_of_not_joint
    (C : Set (ι → F)) (δ_fld δ_int : ℝ≥0) (v : Code.WordStack F (Fin 2) ι)
    (hnot : ¬ Code.jointProximity C (u := v) δ_int) :
    Pr_{let γ ← $ᵖ F}[Code.relDistFromCode (v 0 + γ • v 1) C ≤ δ_fld] ≤
      ProximityGap.epsCa (F := F) (A := F) C δ_fld δ_int := by
  classical
  unfold ProximityGap.epsCa
  have hle := le_iSup
    (fun w : Code.WordStack F (Fin 2) ι =>
      if Code.jointProximity C (u := w) δ_int then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[Code.relDistFromCode (w 0 + γ • w 1) C ≤ δ_fld]) v
  rw [if_neg hnot] at hle
  exact hle

omit [DecidableEq ι] in
/-- Bounds the list size of `RS(k + 1)` at radius `f / n` from the CA error of `RS(k)`
at the same integral radius. -/
theorem rs_Lambda_extended_le_of_epsCa_int_radius
    (domain : ι ↪ F) (k f : ℕ) (ε : ℝ)
    (_hk_pos : 0 < k)
    (_hf_lt : f + k + 1 < Fintype.card ι)
    (_hε_lt : ε < ((Fintype.card F : ℝ) - Fintype.card ι) / (k * Fintype.card F))
    (_hε_ca :
        (epsCa (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((f : ℝ≥0) / Fintype.card ι) ((f : ℝ≥0) / Fintype.card ι)).toReal ≤ ε) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) ((f : ℝ) / Fintype.card ι) ≤
      (Nat.ceil
        (ε * Fintype.card F * ((Fintype.card F : ℝ) - Fintype.card ι)
          / ((Fintype.card F : ℝ) - Fintype.card ι - k * ε * Fintype.card F)) : ℕ∞) := by
  classical
  set n : ℕ := Fintype.card ι with hn
  set q : ℕ := Fintype.card F with hq
  set Ck : Set (ι → F) := (ReedSolomon.code domain k : Set (ι → F)) with hCk
  set Ckp : Set (ι → F) := (ReedSolomon.code domain (k + 1) : Set (ι → F)) with hCkp
  set B : ℝ := ε * q * ((q : ℝ) - n) / ((q : ℝ) - n - k * ε * q) with hB
  have hnpos : 0 < n := by simp [n]
  have hqpos : 0 < q := by simp [q]
  have hε0 : 0 ≤ ε := le_trans ENNReal.toReal_nonneg _hε_ca
  have hnq : n ≤ q := by
    simpa [n, q] using Fintype.card_le_of_injective domain domain.injective
  have hnq_lt : n < q := by
    apply lt_of_le_of_ne hnq
    intro hnqeq
    have hzero : ((q : ℝ) - n) / (k * q) = 0 := by rw [hnqeq]; simp
    rw [hzero] at _hε_lt
    linarith
  have hQpos : (0 : ℝ) < (q : ℝ) - n := by exact_mod_cast Nat.sub_pos_of_lt hnq_lt
  have hkqpos : (0 : ℝ) < (k : ℝ) * q := by positivity
  have hDpos : (0 : ℝ) < (q : ℝ) - n - k * ε * q := by
    have hmul := mul_lt_mul_of_pos_right _hε_lt hkqpos
    rw [div_mul_cancel₀ _ hkqpos.ne'] at hmul
    nlinarith
  change Lambda Ckp ((f : ℝ) / n) ≤ (Nat.ceil B : ℕ∞)
  apply Lambda_le_of_forall_finset_card_le
  intro u T hT
  have hkpn : k + 1 < n := by omega
  have : NeZero k := ⟨_hk_pos.ne'⟩
  have hTcode : ∀ c ∈ T, c ∈ Ckp := by
    intro c hc
    exact (mem_closeCodewordsRel_iff.mp (hT c hc)).1
  let p : (ι → F) → Polynomial F := fun c => Lagrange.interpolate Finset.univ domain c
  have hp_eval (c : ι → F) (i : ι) : (p c).eval (domain i) = c i := by
    simp only [p]
    exact Lagrange.eval_interpolate_at_node c domain.injective.injOn (Finset.mem_univ i)
  have hp_deg : ∀ c ∈ T, (p c).natDegree < k + 1 := by
    intro c hc
    have hmem := ReedSolomon.toPolynomial_mem_lt_deg
      (c := (⟨c, hTcode c hc⟩ : ReedSolomon.code domain (k + 1)))
    have : NeZero (k + 1) := ⟨by omega⟩
    have hdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT hmem
    simpa [p, ReedSolomon.toPolynomial_def] using hdeg
  have hp_inj : Function.Injective p := by
    intro c d hcd
    funext i
    rw [← hp_eval c i, ← hp_eval d i, hcd]
  let A : Finset F := Finset.univ \ Finset.image domain Finset.univ
  have hAsub : Finset.image domain Finset.univ ⊆ (Finset.univ : Finset F) := by simp
  have hAcard : A.card = q - n := by
    rw [show A = Finset.univ \ Finset.image domain Finset.univ by rfl,
      Finset.card_sdiff_of_subset hAsub,
      Finset.card_image_of_injective Finset.univ domain.injective]
    simp [n, q]
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    rw [hAcard]
    exact Nat.sub_pos_of_lt hnq_lt
  have hroot (c : ι → F) (hc : c ∈ T) (d : ι → F) (hd : d ∈ T) (hcd : c ≠ d) :
      (A.filter fun a => (p c).eval a = (p d).eval a).card ≤ k := by
    have hne : p c - p d ≠ 0 := sub_ne_zero.mpr (hp_inj.ne hcd)
    have hsubroots :
        (A.filter fun a => (p c).eval a = (p d).eval a).val ⊆ (p c - p d).roots := by
      intro a ha
      have haeq : (p c).eval a = (p d).eval a := (Finset.mem_filter.mp ha).2
      rw [Polynomial.mem_roots hne]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, haeq, sub_self]
    have hcdeg : (p c).natDegree ≤ k :=
      Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hp_deg c hc)
    have hddeg : (p d).natDegree ≤ k :=
      Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hp_deg d hd)
    calc
      (A.filter fun a => (p c).eval a = (p d).eval a).card
          ≤ (p c - p d).natDegree := Polynomial.card_le_degree_of_subset_roots hsubroots
      _ ≤ max (p c).natDegree (p d).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ k := max_le hcdeg hddeg
  let coll : F → ℕ := fun a =>
    ∑ c ∈ T, ∑ d ∈ T, if (p c).eval a = (p d).eval a then 1 else 0
  have hidcoll : ∑ a ∈ A, coll a =
      ∑ c ∈ T, ∑ d ∈ T, (A.filter fun a => (p c).eval a = (p d).eval a).card := by
    simp only [coll]
    calc
      (∑ a ∈ A, ∑ c ∈ T, ∑ d ∈ T,
          if (p c).eval a = (p d).eval a then 1 else 0)
          = ∑ c ∈ T, ∑ a ∈ A, ∑ d ∈ T,
              if (p c).eval a = (p d).eval a then 1 else 0 := Finset.sum_comm
      _ = ∑ c ∈ T, ∑ d ∈ T, ∑ a ∈ A,
              if (p c).eval a = (p d).eval a then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_comm]
      _ = ∑ c ∈ T, ∑ d ∈ T,
              (A.filter fun a => (p c).eval a = (p d).eval a).card := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro d hd
            exact Finset.sum_boole _ A
  have hrow (c : ι → F) (hc : c ∈ T) :
      ∑ d ∈ T, (A.filter fun a => (p c).eval a = (p d).eval a).card
        ≤ A.card + k * T.card := by
    rw [← Finset.add_sum_erase T
      (fun d => (A.filter fun a => (p c).eval a = (p d).eval a).card) hc]
    have hdiag : (A.filter fun a => (p c).eval a = (p c).eval a).card = A.card := by simp
    rw [hdiag]
    gcongr
    calc
      ∑ d ∈ T.erase c, (A.filter fun a => (p c).eval a = (p d).eval a).card
          ≤ ∑ _d ∈ T.erase c, k := by
            apply Finset.sum_le_sum
            intro d hd
            exact hroot c hc d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd).symm
      _ = k * (T.erase c).card := by simp [Nat.mul_comm]
      _ ≤ k * T.card := Nat.mul_le_mul_left k Finset.card_erase_le
  have hsumcoll : ∑ a ∈ A, coll a ≤ T.card * A.card + k * T.card ^ 2 := by
    rw [hidcoll]
    calc
      (∑ c ∈ T, ∑ d ∈ T, (A.filter fun a => (p c).eval a = (p d).eval a).card)
          ≤ ∑ _c ∈ T, (A.card + k * T.card) := by
            apply Finset.sum_le_sum
            intro c hc
            exact hrow c hc
      _ = T.card * A.card + k * T.card ^ 2 := by
            simp [pow_two]
            ring
  obtain ⟨a, haA, haavg⟩ : ∃ a ∈ A,
      coll a * A.card ≤ T.card * A.card + k * T.card ^ 2 := by
    apply Finset.exists_le_of_sum_le hAne
    calc
      ∑ a ∈ A, coll a * A.card = (∑ a ∈ A, coll a) * A.card := by
        rw [Finset.sum_mul]
      _ ≤ (T.card * A.card + k * T.card ^ 2) * A.card :=
        Nat.mul_le_mul_right A.card hsumcoll
      _ = ∑ _a ∈ A, (T.card * A.card + k * T.card ^ 2) := by
        simp [Nat.mul_comm]
  have hden (i : ι) : domain i - a ≠ 0 := by
    intro hzero
    have heq : domain i = a := sub_eq_zero.mp hzero
    have haimg : a ∈ Finset.image domain Finset.univ :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩
    exact (Finset.mem_sdiff.mp haA).2 haimg
  let v : WordStack F (Fin 2) ι := fun j =>
    Fin.cases (fun i => u i / (domain i - a))
      (fun _ i => -1 / (domain i - a)) j
  have hgdeg (c : ι → F) (hc : c ∈ T) :
      ((p c).divByMonic (Polynomial.X - Polynomial.C a)).natDegree < k := by
    rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a),
      Polynomial.natDegree_X_sub_C]
    have hpc := hp_deg c hc
    omega
  have hfold_eval (c : ι → F) (hc : c ∈ T) (i : ι) (hui : u i = c i) :
      let lam := (p c).eval a
      let g := (p c).divByMonic (Polynomial.X - Polynomial.C a)
      (v 0 + lam • v 1) i = g.eval (domain i) := by
    dsimp
    have hfac := Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic (p c) a
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hfac
    have heval := congrArg (fun r : Polynomial F => r.eval (domain i)) hfac
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    change u i / (domain i - a) + (p c).eval a * (-1 / (domain i - a)) =
      ((p c).divByMonic (Polynomial.X - Polynomial.C a)).eval (domain i)
    rw [hui, ← hp_eval c i]
    calc
      (p c).eval (domain i) / (domain i - a) +
          (p c).eval a * (-1 / (domain i - a))
          = ((p c).eval (domain i) - (p c).eval a) / (domain i - a) := by
              field_simp [hden i]
              ring
      _ = ((p c).divByMonic (Polynomial.X - Polynomial.C a)).eval (domain i) := by
            apply (div_eq_iff (hden i)).2
            rw [← heval]
            ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdist (c : ι → F) (hc : c ∈ T) : Δ₀(u, c) ≤ f := by
    have hr := (mem_closeCodewordsRel_iff.mp (hT c hc)).2
    simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast] at hr
    rw [div_le_iff₀ hnR, div_mul_cancel₀ _ hnR.ne'] at hr
    exact_mod_cast hr
  have hgood (c : ι → F) (hc : c ∈ T) :
      δᵣ(v 0 + (p c).eval a • v 1, Ck) ≤ ((f : ℝ≥0) / n : ℝ≥0) := by
    let g := (p c).divByMonic (Polynomial.X - Polynomial.C a)
    let gw : ι → F := ReedSolomon.evalOnPoints domain g
    have hgw : gw ∈ Ck := by
      rw [hCk]
      exact ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (hgdeg c hc)
    have hpair : Δ₀(v 0 + (p c).eval a • v 1, gw) ≤ Δ₀(u, c) := by
      rw [Code.hammingDist_eq_disagreementCols_card,
        Code.hammingDist_eq_disagreementCols_card]
      apply Finset.card_le_card
      intro i hi
      simp only [Code.mem_disagreementCols] at hi ⊢
      intro hui
      apply hi
      simpa [gw, ReedSolomon.evalOnPoints, g] using hfold_eval c hc i hui
    have hpairE : (Δ₀(v 0 + (p c).eval a • v 1, gw) : ℕ∞) ≤ (f : ℕ∞) := by
      exact_mod_cast hpair.trans (hdist c hc)
    have habs : Δ₀(v 0 + (p c).eval a • v 1, Ck) ≤ f :=
      (Code.distFromCode_le_dist_to_mem _ gw hgw).trans hpairE
    simpa [n] using (Code.distFromCode_le_iff_relDistFromCode_le
      (C := Ck) (v 0 + (p c).eval a • v 1) f).mp habs
  have hrow1 (d : ι → F) (hd : d ∈ Ck) :
      (Finset.univ.filter fun i => v 1 i = d i).card ≤ k := by
    rw [hCk] at hd
    obtain ⟨g, hgdeg', hgeval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hd
    let h : Polynomial F := (Polynomial.X - Polynomial.C a) * g + 1
    have hne : h ≠ 0 := by
      intro hz
      have heval := congrArg (fun r : Polynomial F => r.eval a) hz
      simp [h] at heval
    have hhdeg : h.natDegree ≤ k := by
      calc
        h.natDegree ≤ max ((Polynomial.X - Polynomial.C a) * g).natDegree
            (1 : Polynomial F).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ max ((Polynomial.X - Polynomial.C a).natDegree + g.natDegree) 0 := by
          apply max_le_max
          · exact Polynomial.natDegree_mul_le
          · norm_num
        _ ≤ k := by
          rw [Polynomial.natDegree_X_sub_C]
          omega
    let S := Finset.univ.filter fun i => v 1 i = d i
    have hsub : (S.map domain).val ⊆ h.roots := by
      intro x hx
      obtain ⟨i, hiS, rfl⟩ := Finset.mem_map.mp hx
      rw [Polynomial.mem_roots hne]
      simp only [Polynomial.IsRoot]
      have hiagree : v 1 i = d i := (Finset.mem_filter.mp hiS).2
      have hgi : g.eval (domain i) = d i := hgeval i
      change ((Polynomial.X - Polynomial.C a) * g + 1).eval (domain i) = 0
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
      change (domain i - a) * g.eval (domain i) + 1 = 0
      rw [hgi, ← hiagree]
      change (domain i - a) * (-1 / (domain i - a)) + 1 = 0
      field_simp [hden i]
      ring
    calc
      (Finset.univ.filter fun i => v 1 i = d i).card = (S.map domain).card := by
        simp [S]
      _ ≤ h.natDegree := Polynomial.card_le_degree_of_subset_roots hsub
      _ ≤ k := hhdeg
  have hvnot : ¬ jointProximity (C := Ck) (u := v) ((f : ℝ≥0) / n) := by
    rw [← jointAgreement_iff_jointProximity]
    rintro ⟨S, hS, d, hd⟩
    have hSbound : n - f ≤ S.card := by
      have hcomp := (relDist_floor_bound_iff_complement_bound n S.card
        ((f : ℝ≥0) / n)).2 (by simpa [n] using hS)
      simpa [hnpos.ne'] using hcomp
    have hsub : S ⊆ Finset.univ.filter fun i => v 1 i = d 1 i := by
      intro i hi
      have himem := (hd 1).2 hi
      rw [Finset.mem_filter] at himem ⊢
      exact ⟨Finset.mem_univ _, himem.2.symm⟩
    have hcard := Finset.card_le_card hsub
    have hrow' := hrow1 (d 1) (hd 1).1
    omega
  let Good : Finset F := Finset.univ.filter fun x =>
    δᵣ(v 0 + x • v 1, Ck) ≤ ((f : ℝ≥0) / n : ℝ≥0)
  have hmaps : ∀ c ∈ T, (p c).eval a ∈ Good := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood c hc⟩
  have hprob : ((Good.card : ℝ≥0) / (q : ℝ≥0) : ENNReal) ≤
      epsCa (F := F) (A := F) Ck ((f : ℝ≥0) / n) ((f : ℝ≥0) / n) := by
    unfold epsCa
    refine le_trans ?_ (le_iSup (fun w : WordStack F (Fin 2) ι =>
      if jointProximity (C := Ck) (u := w) ((f : ℝ≥0) / n) then 0 else
        (((do
          let x ← PMF.uniformOfFintype F
          return δᵣ(w 0 + x • w 1, Ck) ≤ ((f : ℝ≥0) / n : ℝ≥0)) True) : ENNReal)) v)
    rw [if_neg hvnot, Probability.prob_uniform_eq_card_filter_div_card]
  have hGoodR : (Good.card : ℝ) ≤ ε * q := by
    have htr := ENNReal.toReal_mono (rs_eps_ca_ne_top Ck _ _) hprob
    have hdiv : (Good.card : ℝ) / q ≤
        (epsCa (F := F) (A := F) Ck ((f : ℝ≥0) / n) ((f : ℝ≥0) / n)).toReal := by
      simpa using htr
    have hdiv' : (Good.card : ℝ) / q ≤ ε := hdiv.trans _hε_ca
    exact (div_le_iff₀ (by exact_mod_cast hqpos)).mp hdiv'
  have hcollfib :
      ∑ z ∈ Good, (T.filter fun c => (p c).eval a = z).card ^ 2 = coll a := by
    have hfib := Finset.sum_fiberwise_of_maps_to'
      (s := T) (t := Good) (g := fun c => (p c).eval a) hmaps
      (fun z => (T.filter fun d => (p d).eval a = z).card)
    simp only [Finset.sum_const, nsmul_eq_mul] at hfib
    calc
      ∑ z ∈ Good, (T.filter fun c => (p c).eval a = z).card ^ 2 =
          ∑ z ∈ Good, (T.filter fun c => (p c).eval a = z).card *
            (T.filter fun c => (p c).eval a = z).card := by simp [pow_two]
      _ = ∑ c ∈ T, (T.filter fun d => (p d).eval a = (p c).eval a).card := hfib
      _ = coll a := by
        simp only [coll]
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro d hd
        simp only [eq_comm]
  have hcardfib : T.card =
      ∑ z ∈ Good, (T.filter fun c => (p c).eval a = z).card := by
    exact Finset.card_eq_sum_card_fiberwise fun c hc => hmaps c hc
  have hCS : (T.card : ℝ) ^ 2 ≤ (Good.card : ℝ) * (coll a : ℝ) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Good) (f := fun z => ((T.filter fun c => (p c).eval a = z).card : ℝ))
    have hcardfibR : (T.card : ℝ) =
        ∑ z ∈ Good, ((T.filter fun c => (p c).eval a = z).card : ℝ) := by
      exact_mod_cast hcardfib
    have hcollfibR :
        ∑ z ∈ Good, ((T.filter fun c => (p c).eval a = z).card : ℝ) ^ 2 =
          (coll a : ℝ) := by
      exact_mod_cast hcollfib
    rwa [← hcardfibR, hcollfibR] at h
  have hmaster : (T.card : ℝ) ^ 2 * A.card ≤
      (Good.card : ℝ) * ((T.card : ℝ) * A.card + k * (T.card : ℝ) ^ 2) := by
    calc
      (T.card : ℝ) ^ 2 * A.card ≤ ((Good.card : ℝ) * (coll a : ℝ)) * A.card := by
        gcongr
      _ = (Good.card : ℝ) * ((coll a : ℝ) * A.card) := by ring
      _ ≤ (Good.card : ℝ) * ((T.card : ℝ) * A.card + k * (T.card : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast haavg
  have hAcardR : (A.card : ℝ) = (q : ℝ) - n := by
    rw [hAcard, Nat.cast_sub hnq]
  by_cases hT0 : T.card = 0
  · simp [hT0]
  have hLpos : (0 : ℝ) < T.card := by exact_mod_cast Nat.pos_of_ne_zero hT0
  have hbracket0 : (0 : ℝ) ≤ (T.card : ℝ) * A.card + k * (T.card : ℝ) ^ 2 := by
    positivity
  have hmaster' : (T.card : ℝ) ^ 2 * ((q : ℝ) - n) ≤
      ε * q * ((T.card : ℝ) * ((q : ℝ) - n) + k * (T.card : ℝ) ^ 2) := by
    calc
      (T.card : ℝ) ^ 2 * ((q : ℝ) - n) = (T.card : ℝ) ^ 2 * A.card := by rw [hAcardR]
      _ ≤ (Good.card : ℝ) * ((T.card : ℝ) * A.card + k * (T.card : ℝ) ^ 2) := hmaster
      _ ≤ ε * q * ((T.card : ℝ) * A.card + k * (T.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hGoodR hbracket0
      _ = ε * q * ((T.card : ℝ) * ((q : ℝ) - n) + k * (T.card : ℝ) ^ 2) := by
        rw [hAcardR]
  have hLD : (T.card : ℝ) * ((q : ℝ) - n - k * ε * q) ≤
      ε * q * ((q : ℝ) - n) := by
    nlinarith
  have hLB : (T.card : ℝ) ≤ B := by
    rw [hB]
    exact (le_div_iff₀ hDpos).2 hLD
  have hceilR : (T.card : ℝ) ≤ (Nat.ceil B : ℝ) := hLB.trans (Nat.le_ceil B)
  exact_mod_cast hceilR

end CAImpliesList

end CodingTheory
