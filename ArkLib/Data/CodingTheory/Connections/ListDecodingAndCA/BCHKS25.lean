/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# BCHKS25 CA-to-list-size bound

This file proves the BCHKS25 implication from a small Reed--Solomon correlated-agreement error
to the field-cardinality list-size bound.

## Main result

- `rs_Lambda_le_card_of_epsCa_lt` proves the source-licensed `Lambda ≤ |F|` conclusion.

## References

- [BCHKS25] Theorem 1.9.
-/

namespace CodingTheory

open scoped NNReal
open Code CoreDefinitions ProximityGap

section CAImpliesList

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- A Reed--Solomon CA error below `1 / (2 * n)` at field radius `δ + 2 / n` bounds
the list size at radius `δ` by the field cardinality. -/
theorem rs_Lambda_le_card_of_epsCa_lt
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (δ_int : ℝ≥0)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (_hδ_int : (δ_int : ℝ) <
      1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι)
    (_hε_ca :
        epsCa (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            δ_int <
          ENNReal.ofReal (1 / (2 * Fintype.card ι))) :
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ ≤ (Fintype.card F : ℕ∞) := by
  classical
  by_contra hΛ
  have hΛlt : (Fintype.card F : ℕ∞) <
      Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ := lt_of_not_ge hΛ
  obtain ⟨c, hcmax⟩ := Code.exists_encard_eq_Lambda_of_finite
    (C := (ReedSolomon.code domain k : Set (ι → F))) δ
  let S := closeCodewordsRel (ReedSolomon.code domain k : Set (ι → F)) c δ
  have hSfin : S.Finite := Set.toFinite S
  let L : Finset (ReedSolomon.code domain k) :=
    Finset.univ.filter fun H => H.1 ∈ S
  have hLcard : Fintype.card F < L.card := by
    have henc : (Fintype.card F : ℕ∞) < S.encard := by
      simpa only [S, hcmax] using hΛlt
    have hScard : Fintype.card F < S.ncard := by
      rw [← hSfin.cast_ncard_eq] at henc
      exact_mod_cast henc
    let e : {H : ReedSolomon.code domain k // H.1 ∈ S} ≃ S :=
      { toFun := fun H => ⟨H.1.1, H.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have heq : L.card = S.ncard := by
      calc
        L.card = Fintype.card {H : ReedSolomon.code domain k // H.1 ∈ S} := by
          rw [Fintype.card_subtype]
        _ = Fintype.card S := Fintype.card_congr e
        _ = S.ncard := by
          rw [Set.ncard_eq_toFinset_card S hSfin]
          exact Fintype.card_of_finset' hSfin.toFinset (fun x => hSfin.mem_toFinset)
    omega
  have hLclose : ∀ H ∈ L, H.1 ∈
      closeCodewordsRel (ReedSolomon.code domain k : Set (ι → F)) c δ := by
    intro H hH
    change H.1 ∈ S
    exact (Finset.mem_filter.mp hH).2
  let n := Fintype.card ι
  let q := Fintype.card F
  have hn : 0 < n := by simp [n]
  have hq : 0 < q := by simp [q]
  have hklt : k < n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    by_contra h
    have hdiv : (1 : ℝ) ≤ (k : ℝ) / n := by
      rw [le_div_iff₀ hnR]
      norm_num only [one_mul]
      exact_mod_cast (show n ≤ k by omega)
    nlinarith [_hδ_pos, _hδ_lt]
  let w : ReedSolomon.code domain k → F → F := fun H a =>
    (ReedSolomon.toPolynomial H).eval a
  have hwmem : ∀ H, w H ∈ ReedSolomon.code (Function.Embedding.refl F) k := by
    intro H
    simpa only [w, ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk,
      Function.Embedding.refl_apply] using
      (ReedSolomon.evalOnPoints_mem_code_of_degree_lt
        (α := Function.Embedding.refl F) (ReedSolomon.toPolynomial_lt_deg H))
  have hwinj : Function.Injective w := by
    intro H H' heq
    apply Subtype.ext
    funext x
    have hx := congrFun heq (domain x)
    simpa only [w, ReedSolomon.toPolynomial_eval_at_domain] using hx
  have hwagree : ∀ H ∈ L, ∀ H' ∈ L, H ≠ H' → Code.agree (w H) (w H') < k := by
    intro H _ H' _ hne
    exact ReedSolomon.agree_lt_of_mem_code (hwmem H) (hwmem H') (hwinj.ne hne)
  have hq1 : q + 1 ≤ L.card := by
    apply Nat.succ_le_iff.mpr
    simpa only [q] using hLcard
  obtain ⟨L0, hL0sub, hL0card⟩ :=
    Finset.exists_subset_card_eq (s := L) (n := q + 1) hq1
  have hkpos : 0 < k := by
    have hq2 : 1 < q := by
      simpa only [q] using Fintype.one_lt_card (α := F)
    have hL02 : 1 < L0.card := by rw [hL0card]; omega
    obtain ⟨H, hH, H', hH', hne⟩ := Finset.one_lt_card.mp hL02
    have ha := hwagree H (hL0sub hH) H' (hL0sub hH') hne
    omega
  let imageAt : F → Finset F := fun a => L0.image fun H => w H a
  let fiber : F → F → Finset (ReedSolomon.code domain k) := fun a z =>
    L0.filter fun H => w H a = z
  let N : F → ℕ := fun a => ∑ H ∈ L0, (fiber a (w H a)).card
  have hmass (a : F) : L0.card = ∑ z ∈ imageAt a, (fiber a z).card := by
    simpa only [imageAt, fiber] using Finset.card_eq_sum_card_image (fun H => w H a) L0
  have hNfiber (a : F) : N a = ∑ z ∈ imageAt a, (fiber a z).card ^ 2 := by
    have hcomp := Finset.sum_comp
      (s := L0) (fun z : F => (fiber a z).card) (fun H => w H a)
    simpa only [N, imageAt, fiber, Nat.nsmul_eq_mul, pow_two] using hcomp
  have hCS (a : F) : (L0.card : ℝ) ^ 2 ≤ (imageAt a).card * (N a : ℝ) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := imageAt a) (f := fun z => ((fiber a z).card : ℝ))
    have hmassR : (L0.card : ℝ) = ∑ z ∈ imageAt a, ((fiber a z).card : ℝ) := by
      exact_mod_cast hmass a
    rw [← hmassR] at h
    rw [hNfiber a]
    simpa only [Nat.cast_sum, Nat.cast_pow] using h
  have hNsum :
      ∑ a : F, N a =
        ∑ H ∈ L0, ∑ H' ∈ L0, Code.agree (w H) (w H') := by
    simp only [N, fiber, Code.agree, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro H hH
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro H' hH'
    apply Finset.sum_congr rfl
    intro a ha
    by_cases heq : w H' a = w H a
    · rw [if_pos heq, if_pos heq.symm]
    · rw [if_neg heq, if_neg (Ne.symm heq)]
  have hrow (H) (hH : H ∈ L0) :
      ∑ H' ∈ L0, Code.agree (w H) (w H') ≤ q + q * k := by
    rw [← Finset.sum_erase_add L0 (fun H' => Code.agree (w H) (w H')) hH]
    have herase : ∑ H' ∈ L0.erase H, Code.agree (w H) (w H') ≤
        (L0.erase H).card * k := by
      apply Finset.sum_le_card_nsmul
      intro H' hH'
      exact (hwagree H (hL0sub hH) H' (hL0sub (Finset.mem_of_mem_erase hH'))
        (Ne.symm (Finset.ne_of_mem_erase hH'))).le
    have hcarderase : (L0.erase H).card = q := by
      rw [Finset.card_erase_of_mem hH, hL0card]
      omega
    rw [hcarderase] at herase
    rw [Code.agree_self]
    simpa only [q, Nat.add_comm] using Nat.add_le_add_right herase (Fintype.card F)
  have hpairs :
      ∑ H ∈ L0, ∑ H' ∈ L0, Code.agree (w H) (w H') ≤
        L0.card * (q + q * k) :=
    Finset.sum_le_card_nsmul L0 _ _ hrow
  have hNupper : ∑ a : F, N a ≤ L0.card * q * n := by
    rw [hNsum]
    calc
      _ ≤ L0.card * (q + q * k) := hpairs
      _ = (L0.card * q) * (k + 1) := by ring
      _ ≤ (L0.card * q) * n := Nat.mul_le_mul_left _ (by omega)
      _ = L0.card * q * n := by ring
  have hspread : ∃ α : F, q ≤ 2 * n * (imageAt α).card := by
    by_contra hall
    push Not at hall
    have hper (a : F) :
        (2 * n * (L0.card : ℝ) ^ 2) < (q : ℝ) * N a := by
      have hbad : 2 * n * (imageAt a).card < q := hall a
      have hbadR : (2 * n * (imageAt a).card : ℝ) < q := by exact_mod_cast hbad
      have hNpos : (0 : ℝ) < N a := by
        have hMpos : (0 : ℝ) < L0.card := by rw [hL0card]; positivity
        nlinarith only [hCS a, hMpos]
      have hmul := mul_lt_mul_of_pos_right hbadR hNpos
      have hscale := mul_le_mul_of_nonneg_left (hCS a)
        (show (0 : ℝ) ≤ 2 * n by positivity)
      calc
        2 * n * (L0.card : ℝ) ^ 2 ≤
            2 * n * ((imageAt a).card * (N a : ℝ)) := hscale
        _ = (2 * n * (imageAt a).card : ℝ) * N a := by ring
        _ < (q : ℝ) * N a := hmul
    have hsum :
        ∑ _a : F, (2 * n * (L0.card : ℝ) ^ 2) <
          ∑ a : F, (q : ℝ) * N a :=
      Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset F))
        Finset.univ_nonempty (fun a _ => hper a)
    have hscaled : (q : ℝ) * (2 * n * (L0.card : ℝ) ^ 2) <
        (q : ℝ) * ((∑ a : F, N a : ℕ) : ℝ) := by
      calc
        (q : ℝ) * (2 * n * (L0.card : ℝ) ^ 2)
            = ∑ _a : F, (2 * n * (L0.card : ℝ) ^ 2) := by
                simp only [Finset.sum_const, Finset.card_univ, q, nsmul_eq_mul]
        _ < ∑ a : F, (q : ℝ) * N a := hsum
        _ = (q : ℝ) * ((∑ a : F, N a : ℕ) : ℝ) := by
          rw [← Finset.mul_sum]
          norm_num only [Nat.cast_sum]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsumlower : 2 * n * (L0.card : ℝ) ^ 2 <
        ((∑ a : F, N a : ℕ) : ℝ) :=
      lt_of_mul_lt_mul_left hscaled hqR.le
    have hupperR : ((∑ a : F, N a : ℕ) : ℝ) ≤ L0.card * q * n := by
      exact_mod_cast hNupper
    have hcomb := hsumlower.trans_le hupperR
    have hL0R : (L0.card : ℝ) = q + 1 := by exact_mod_cast hL0card
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [hL0R] at hcomb
    nlinarith only [hcomb, hnR]
  obtain ⟨α, hspreadα⟩ := hspread
  let Z : Finset F := imageAt α
  let f : ι → F := fun x => c x / (domain x - α)
  let g : ι → F := fun x => -1 / (domain x - α)
  have hcloseZ : ∀ z ∈ Z,
      δᵣ(f + z • g, (ReedSolomon.code domain k : Set (ι → F))) ≤
        (((δ + 2 / Fintype.card ι).toNNReal : NNReal) : ENNReal) := by
    intro z hzZ
    have hzI : z ∈ imageAt α := by simpa only [Z] using hzZ
    obtain ⟨H, hHL0, hzEq⟩ := Finset.mem_image.mp hzI
    have hcloseH := hLclose H (hL0sub hHL0)
    let P : Polynomial F := ReedSolomon.toPolynomial H
    let Q : Polynomial F := (P - Polynomial.C z) / (Polynomial.X - Polynomial.C α)
    have hPeq : P.eval α = z := by simpa only [P, w] using hzEq
    have hroot : (P - Polynomial.C z).IsRoot α := by
      change (P - Polynomial.C z).eval α = 0
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      rw [hPeq]
      exact sub_self z
    have hfac : (Polynomial.X - Polynomial.C α) * Q = P - Polynomial.C z := hroot.mul_div_eq
    have hQdeg : Q.degree < k := by
      calc
        Q.degree ≤ (P - Polynomial.C z).degree := Polynomial.degree_div_le _ _
        _ ≤ max P.degree (Polynomial.C z).degree := Polynomial.degree_sub_le _ _
        _ < k := by
          rw [max_lt_iff]
          exact ⟨ReedSolomon.toPolynomial_lt_deg H,
            lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hkpos)⟩
    let v : ι → F := ReedSolomon.evalOnPoints domain Q
    have hv : v ∈ ReedSolomon.code domain k :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt hQdeg
    have hpoint (x : ι) (hxα : domain x ≠ α) (hxc : H.1 x = c x) :
        v x = (f + z • g) x := by
      have hev := congrArg (fun R : Polynomial F => R.eval (domain x)) hfac
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, P, Q] at hev
      rw [ReedSolomon.toPolynomial_eval_at_domain, hxc] at hev
      have hd : domain x - α ≠ 0 := sub_ne_zero.mpr hxα
      have hquot : Polynomial.eval (domain x) Q = (c x - z) / (domain x - α) := by
        symm
        apply (div_eq_iff hd).2
        simpa only [mul_comm] using hev.symm
      dsimp only [v, ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, f, g]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hquot]
      field_simp [hd]
      ring
    let E : Finset ι := Finset.univ.filter fun x => domain x = α
    have hEcard : E.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      apply domain.injective
      exact ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm
    have hDsub : Code.disagreementCols (f + z • g) v ⊆
        Code.disagreementCols c H.1 ∪ E := by
      intro x hx
      by_contra hnot
      have hxc : H.1 x = c x := by
        have hxnot : x ∉ Code.disagreementCols c H.1 := fun hx' =>
          hnot (Finset.mem_union_left E hx')
        have hcH : c x = H.1 x := by
          simpa only [Code.mem_disagreementCols, not_not] using hxnot
        exact hcH.symm
      have hxα : domain x ≠ α := by
        intro heq
        apply hnot
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, heq⟩)
      exact (Code.mem_disagreementCols.mp hx) (hpoint x hxα hxc).symm
    have hdist : Δ₀(f + z • g, v) ≤ Δ₀(c, H.1) + 1 := by
      rw [Code.hammingDist_eq_disagreementCols_card,
        Code.hammingDist_eq_disagreementCols_card]
      exact (Finset.card_le_card hDsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hEcard _))
    have hrel : (δᵣ(c, H.1) : ℝ) ≤ δ :=
      (Code.mem_closeCodewordsRel_iff.mp hcloseH).2
    rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
    refine ⟨v, hv, ?_⟩
    have hnR : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos (α := ι)
    have hdistR : (Δ₀(f + z • g, v) : ℝ) ≤ (Δ₀(c, H.1) : ℝ) + 1 := by
      exact_mod_cast hdist
    have hreal : (δᵣ(f + z • g, v) : ℝ) ≤
        ((δ + 2 / Fintype.card ι).toNNReal : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity), Code.relHammingDist_coe]
      rw [Code.relHammingDist_coe] at hrel
      have hdiv := div_le_div_of_nonneg_right hdistR hnR.le
      rw [add_div] at hdiv
      have hone : (1 : ℝ) / Fintype.card ι ≤ 2 / Fintype.card ι := by
        gcongr
        norm_num
      linarith
    exact_mod_cast hreal
  let u : WordStack F (Fin 2) ι := fun j => if j = 0 then f else g
  have hu0 : u 0 = f := by simp [u]
  have hu1 : u 1 = g := by simp [u]
  have hfoldclose : ∀ z ∈ Z,
      δᵣ(u 0 + z • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤
        (((δ + 2 / Fintype.card ι).toNNReal : NNReal) : ENNReal) := by
    intro z hz
    rw [hu0, hu1]
    exact hcloseZ z hz
  have hagree_bound : ∀ v : ι → F, v ∈ ReedSolomon.code domain k →
      Code.agree g v ≤ k + 1 := by
    intro v hv
    let V : ReedSolomon.code domain k := ⟨v, hv⟩
    let P : Polynomial F := ReedSolomon.toPolynomial V
    let R : Polynomial F := (Polynomial.X - Polynomial.C α) * P + 1
    have hPnat : P.natDegree < k := by
      by_cases hP0 : P = 0
      · simp only [hP0, Polynomial.natDegree_zero]
        exact hkpos
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).2
          (ReedSolomon.toPolynomial_lt_deg V)
    have hRdeg : R.natDegree ≤ k := by
      calc
        R.natDegree ≤ max ((Polynomial.X - Polynomial.C α) * P).natDegree
            (1 : Polynomial F).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ k := by
          have hm := Polynomial.natDegree_mul_le
            (p := Polynomial.X - Polynomial.C α) (q := P)
          rw [Polynomial.natDegree_X_sub_C] at hm
          simp only [Polynomial.natDegree_one]
          omega
    have hRne : R ≠ 0 := by
      intro h0
      have he := congrArg (fun T : Polynomial F => T.eval α) h0
      simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, zero_mul,
        zero_add, Polynomial.eval_zero] at he
      exact one_ne_zero he
    let A : Finset ι := Finset.univ.filter fun x => g x = v x
    let A0 : Finset ι := A.filter fun x => domain x ≠ α
    let E : Finset ι := Finset.univ.filter fun x => domain x = α
    have hEcard : E.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      apply domain.injective
      exact ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm
    have hAsub : A ⊆ A0 ∪ E := by
      intro x hx
      by_cases hxe : domain x = α
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxe⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxe⟩)
    let rootsFin : Finset F := A0.map domain
    have hrootscard : rootsFin.card = A0.card := Finset.card_map _
    have hroots : rootsFin.val ⊆ R.roots := by
      intro y hy
      have hy' : y ∈ rootsFin := hy
      obtain ⟨x, hxA0, hxy⟩ := Finset.mem_map.mp hy'
      rw [Polynomial.mem_roots hRne]
      change R.eval y = 0
      subst y
      have hxA := (Finset.mem_filter.mp hxA0).1
      have hxne := (Finset.mem_filter.mp hxA0).2
      have hxgv := (Finset.mem_filter.mp hxA).2
      simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
      have hPeval : P.eval (domain x) = v x :=
        ReedSolomon.toPolynomial_eval_at_domain
      rw [hPeval, ← hxgv]
      dsimp only [g]
      have hd : domain x - α ≠ 0 := sub_ne_zero.mpr hxne
      field_simp [hd]
      ring
    have hA0card : A0.card ≤ k := by
      rw [← hrootscard]
      exact (Polynomial.card_le_degree_of_subset_roots hroots).trans hRdeg
    have hAcard : A.card ≤ k + 1 := by
      calc
        A.card ≤ (A0 ∪ E).card := Finset.card_le_card hAsub
        _ ≤ A0.card + E.card := Finset.card_union_le _ _
        _ ≤ k + 1 := Nat.add_le_add hA0card hEcard
    simpa only [Code.agree, A, eq_comm] using hAcard
  have hnotjoint : ¬ jointProximity
      (ReedSolomon.code domain k : Set (ι → F)) (u := u) δ_int := by
    intro hj
    rw [← jointAgreement_iff_jointProximity] at hj
    obtain ⟨T, hTcard, V, hV⟩ := hj
    have hsub : T ⊆ Finset.filter (fun x => V 1 x = g x) Finset.univ := by
      intro x hx
      have hx' := (hV 1).2 hx
      rw [hu1] at hx'
      exact hx'
    have hupper : T.card ≤ k + 1 := by
      calc
        T.card ≤ (Finset.filter (fun x => V 1 x = g x) Finset.univ).card :=
          Finset.card_le_card hsub
        _ = Code.agree g (V 1) := by simp only [Code.agree, eq_comm]
        _ ≤ k + 1 := hagree_bound (V 1) (hV 1).1
    have hnR : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos (α := ι)
    have hδle : δ_int ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / Fintype.card ι := by positivity
      have h10 : (0 : ℝ) ≤ 1 / Fintype.card ι := by positivity
      linarith
    have hlower : (1 - (δ_int : ℝ)) * Fintype.card ι ≤ T.card := by
      have hco := NNReal.coe_le_coe.mpr hTcard
      rw [NNReal.coe_mul, NNReal.coe_sub hδle] at hco
      push_cast at hco
      exact hco
    have hmargin := mul_lt_mul_of_pos_right _hδ_int hnR
    rw [sub_mul, sub_mul, one_mul, div_mul_cancel₀ _ hnR.ne',
      div_mul_cancel₀ _ hnR.ne'] at hmargin
    have hupperR : (T.card : ℝ) ≤ k + 1 := by exact_mod_cast hupper
    nlinarith
  let Pevent : F → Prop := fun z =>
    δᵣ(u 0 + z • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤
      (((δ + 2 / Fintype.card ι).toNNReal : NNReal) : ENNReal)
  have hZsub : Z ⊆ Finset.univ.filter Pevent := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hfoldclose z hz⟩
  have hcard : Z.card ≤ (Finset.univ.filter Pevent).card :=
    Finset.card_le_card hZsub
  have hspread' : Fintype.card F ≤
      2 * Fintype.card ι * (Finset.univ.filter Pevent).card := by
    have hspreadZ : Fintype.card F ≤ 2 * Fintype.card ι * Z.card := by
      simpa only [q, n, Z] using hspreadα
    exact hspreadZ.trans (Nat.mul_le_mul_left _ hcard)
  have hratioR :
      1 / (2 * Fintype.card ι : ℝ) ≤
        ((Finset.univ.filter Pevent).card : ℝ) / Fintype.card F := by
    have hqR : (0 : ℝ) < Fintype.card F := by
      exact_mod_cast Fintype.card_pos (α := F)
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card ι) hqR]
    norm_num only [one_mul]
    rw [mul_comm]
    exact_mod_cast hspread'
  have hlowerprob :
      ENNReal.ofReal (1 / (2 * Fintype.card ι : ℝ)) ≤
        ((((Finset.univ.filter Pevent).card : NNReal) /
          (Fintype.card F : NNReal) : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    exact_mod_cast hratioR
  have hratio_le :
      ((((Finset.univ.filter Pevent).card : NNReal) /
          (Fintype.card F : NNReal) : NNReal) : ENNReal) ≤
        epsCa (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F))
          ((δ + 2 / Fintype.card ι).toNNReal) δ_int := by
    have hqne : (Fintype.card F : NNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := F)).ne'
    rw [ENNReal.coe_div hqne]
    rw [← Probability.prob_uniform_eq_card_filter_div_card Pevent]
    dsimp only [Pevent]
    unfold epsCa
    exact le_iSup_of_le u (by rw [if_neg hnotjoint])
  exact (not_lt_of_ge (hlowerprob.trans hratio_le)) _hε_ca

end CAImpliesList

end CodingTheory
