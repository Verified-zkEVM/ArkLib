/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.GoodCoeffs
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped BigOperators in
open scoped Polynomial.Bivariate in
open Polynomial in
open Polynomial.Bivariate in
open BerlekampWelch in
omit [DecidableEq ι] in
theorem RS_exists_bivariate_AB_of_goodCoeffs_card_gt
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin 2) ι)
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    ∃ A B : F[X][Y],
      A ≠ 0 ∧
      Polynomial.Bivariate.degreeX A ≤ Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.natDegreeY A ≤ Nat.floor (δ * Fintype.card ι) ∧
      Polynomial.Bivariate.degreeX B ≤ Nat.floor (δ * Fintype.card ι) + deg - 1 ∧
      Polynomial.Bivariate.natDegreeY B ≤ Nat.floor (δ * Fintype.card ι) + 1 ∧
      (∀ i : ι,
        Polynomial.Bivariate.evalX (domain i) B =
          (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalX (domain i) A) := by
  classical
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hker :
      ∃ a : Fin (e + 1) → F[X],
        ∃ b : Fin (e + deg) → F[X],
          a ≠ 0 ∧
            (∀ t, (a t).natDegree ≤ e) ∧
              (∀ s, (b s).natDegree ≤ e + 1) ∧
                Matrix.mulVec
                    (BW_homMatrix (ι := ι) e deg
                      (fun i => (Polynomial.C (domain i) : F[X]))
                      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
                    (Fin.append a b) = 0 := by
    simpa [e] using
      (RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt (deg := deg) (domain := domain)
        (δ := δ) u hdeg hδ hS)
  rcases hker with ⟨a, b, ha_ne, ha_deg, hb_deg, hMul⟩
  let A0 : F[X][Y] := ∑ t : Fin (e + 1), Polynomial.monomial t.1 (a t)
  let B0 : F[X][Y] := ∑ s : Fin (e + deg), Polynomial.monomial s.1 (b s)
  let A : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) A0
  let B : F[X][Y] := (Polynomial.Bivariate.swap (R := F)) B0
  have hcoeffA0 : ∀ n : ℕ, ∀ hn : n < e + 1, A0.coeff n = a ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [A0, Polynomial.coeff_monomial]
    have hsum :
        (∑ t : Fin (e + 1), (if t = ⟨n, hn⟩ then a t else (0 : F[X]))) = a ⟨n, hn⟩ := by
      simp
    simpa [Fin.ext_iff] using hsum
  have hcoeffB0 : ∀ n : ℕ, ∀ hn : n < e + deg, B0.coeff n = b ⟨n, hn⟩ := by
    intro n hn
    classical
    simp [B0, Polynomial.coeff_monomial]
    have hsum :
        (∑ t : Fin (e + deg), (if t = ⟨n, hn⟩ then b t else (0 : F[X]))) = b ⟨n, hn⟩ := by
      simp
    simpa [Fin.ext_iff] using hsum
  have hcoeffA0_big : ∀ N : ℕ, e < N → A0.coeff N = 0 := by
    intro N hN
    classical
    have hN' : e + 1 ≤ N := Nat.succ_le_of_lt hN
    have hne : ∀ t : Fin (e + 1), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [A0, Polynomial.coeff_monomial, hne]
  have hcoeffB0_big : ∀ N : ℕ, e + deg - 1 < N → B0.coeff N = 0 := by
    intro N hN
    classical
    have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
    have hpos : 1 ≤ e + deg := Nat.succ_le_of_lt (Nat.add_pos_right e hdegpos)
    have hN' : e + deg ≤ N := by
      have : (e + deg - 1) + 1 ≤ N := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hN
      simpa [Nat.sub_add_cancel hpos, Nat.add_assoc] using this
    have hne : ∀ t : Fin (e + deg), (t : ℕ) ≠ N := by
      intro t
      have ht : (t : ℕ) < N := lt_of_lt_of_le t.2 hN'
      exact Nat.ne_of_lt ht
    simp [B0, Polynomial.coeff_monomial, hne]
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A ≠ 0
    have hex : ∃ t : Fin (e + 1), a t ≠ 0 := by
      by_contra h
      apply ha_ne
      funext t
      have : a t = 0 := by
        by_contra ht
        exact h ⟨t, ht⟩
      simpa using this
    rcases hex with ⟨t0, ht0⟩
    have hcoeff : A0.coeff t0.1 = a t0 := by
      simpa using (hcoeffA0 t0.1 t0.2)
    have hA0 : A0 ≠ 0 := by
      intro hzero
      apply ht0
      have : A0.coeff t0.1 = 0 := by simp [hzero]
      simpa [hcoeff] using this
    intro hzero
    apply hA0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simp [A, hzero])
  · -- degreeX A bound
    have hnatY_A0 : Polynomial.Bivariate.natDegreeY A0 ≤ e := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffA0_big
    have hdegX : Polynomial.Bivariate.degreeX A = Polynomial.Bivariate.natDegreeY A0 := by
      simpa [A] using (ps_degree_x_swap (F := F) (f := A0))
    simpa [hdegX] using hnatY_A0
  · -- natDegreeY A bound
    have hdegX_A0 : Polynomial.Bivariate.degreeX A0 ≤ e := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + 1
      · have : (A0.coeff n).natDegree = (a ⟨n, hnlt⟩).natDegree := by
          simp [hcoeffA0 n hnlt]
        simpa [this] using ha_deg ⟨n, hnlt⟩
      · have hnle : e < n := by
          have : e + 1 ≤ n := Nat.le_of_not_gt hnlt
          exact lt_of_lt_of_le (Nat.lt_succ_self e) this
        have hcoeff0 : A0.coeff n = 0 := hcoeffA0_big n hnle
        have : A0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY A = Polynomial.Bivariate.degreeX A0 := by
      simpa [A] using (ps_nat_degree_y_swap (F := F) (f := A0))
    simpa [hnatY] using hdegX_A0
  · -- degreeX B bound
    have hnatY_B0 : Polynomial.Bivariate.natDegreeY B0 ≤ e + deg - 1 := by
      unfold Polynomial.Bivariate.natDegreeY
      exact (Polynomial.natDegree_le_iff_coeff_eq_zero).2 hcoeffB0_big
    have hdegX : Polynomial.Bivariate.degreeX B = Polynomial.Bivariate.natDegreeY B0 := by
      simpa [B] using (ps_degree_x_swap (F := F) (f := B0))
    simpa [hdegX] using hnatY_B0
  · -- natDegreeY B bound
    have hdegX_B0 : Polynomial.Bivariate.degreeX B0 ≤ e + 1 := by
      classical
      unfold Polynomial.Bivariate.degreeX
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      by_cases hnlt : n < e + deg
      · have : (B0.coeff n).natDegree = (b ⟨n, hnlt⟩).natDegree := by
          simp [hcoeffB0 n hnlt]
        simpa [this] using hb_deg ⟨n, hnlt⟩
      · have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
        have hpos : 0 < e + deg := Nat.add_pos_right e hdegpos
        have hnge : e + deg ≤ n := (Nat.not_lt).1 hnlt
        have hnle : e + deg - 1 < n := Nat.sub_one_lt_of_le hpos hnge
        have hcoeff0 : B0.coeff n = 0 := hcoeffB0_big n hnle
        have : B0.coeff n ≠ 0 := by
          simpa [Polynomial.mem_support_iff] using hn
        exact (this hcoeff0).elim
    have hnatY : Polynomial.Bivariate.natDegreeY B = Polynomial.Bivariate.degreeX B0 := by
      simpa [B] using (ps_nat_degree_y_swap (F := F) (f := B0))
    simpa [hnatY] using hdegX_B0
  · -- main identity
    intro i
    have hEvalX_A :
        Polynomial.Bivariate.evalX (domain i) A =
          Polynomial.Bivariate.evalY (domain i) A0 := by
      simpa [A] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := A0)).symm
    have hEvalX_B :
        Polynomial.Bivariate.evalX (domain i) B =
          Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [B] using (ps_eval_y_eq_eval_x_swap (F := F) (y := domain i) (f := B0)).symm
    rw [hEvalX_B, hEvalX_A]
    have hEq_all :
        ∀ i : ι,
          (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
            = ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
      (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          a b).1 hMul
    have hEvalA :
        Polynomial.Bivariate.evalY (domain i) A0 =
          ∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, A0, Polynomial.eval_finset_sum]
    have hEvalB :
        Polynomial.Bivariate.evalY (domain i) B0 =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 := by
      classical
      simp [Polynomial.Bivariate.evalY, B0, Polynomial.eval_finset_sum]
    have hEq_eval :
        Polynomial.Bivariate.evalY (domain i) A0 *
            (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          = Polynomial.Bivariate.evalY (domain i) B0 := by
      simpa [hEvalA, hEvalB] using (hEq_all i)
    calc
      Polynomial.Bivariate.evalY (domain i) B0
          = Polynomial.Bivariate.evalY (domain i) A0 *
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) := by
              simpa using hEq_eval.symm
      _ = (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalY (domain i) A0 := by
            -- commutativity in `F[X]`
            exact (mul_comm (Polynomial.Bivariate.evalY (domain i) A0)
              (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))


open scoped BigOperators in
open scoped Polynomial.Bivariate in
open Polynomial in
open Polynomial.Bivariate in
open BerlekampWelch in
omit [DecidableEq ι] in
theorem RS_jointAgreement_of_goodCoeffs_card_gt {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin 2) ι)
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)
  set good : Finset F := RS_goodCoeffs (deg := deg) (domain := domain) u δ
  have hn_pos : 0 < n := by
    simp [n]
  have hgood_card : good.card > n := by
    simpa [good, n] using hS
  by_cases hdeg_zero : deg = 0
  · subst hdeg_zero
    let S0 : Finset ι := Finset.univ.filter (fun i => u 0 i = 0 ∧ u 1 i = 0)
    have hcode0_zero : ∀ w ∈ (ReedSolomon.code domain 0 : Set (ι → F)), w = 0 := by
      intro w hw
      rcases hw with ⟨p, hpdeg, hp_eval⟩
      have hp0 : p = 0 := by
        simpa [Polynomial.mem_degreeLT] using hpdeg
      ext i
      simpa [hp0] using (congrArg (fun f => f i) hp_eval).symm
    have hzero_card :
        ∀ z ∈ good,
          n - e ≤ (Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0)).card := by
      intro z hz
      have hz_rel : δᵣ(u 0 + z • u 1, ReedSolomon.code domain 0) ≤ δ := by
        have hz' : z ∈ Finset.filter
            (fun z : F => δᵣ(u 0 + z • u 1, ReedSolomon.code domain 0) ≤ δ)
            Finset.univ := by
          simpa [good, RS_goodCoeffs] using hz
        exact (Finset.mem_filter.mp hz').2
      have hz_zero : δᵣ(u 0 + z • u 1, (0 : ι → F)) ≤ δ := by
        rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist] at hz_rel
        rcases hz_rel with ⟨w, hwmem, hwdist⟩
        simpa [hcode0_zero w hwmem] using hwdist
      obtain ⟨Tz, hTz_card, hTz_agree⟩ :=
        (Code.relCloseToWord_iff_exists_agreementCols
          (u := u 0 + z • u 1) (v := (0 : ι → F)) (δ := δ)).1 hz_zero
      have hTz_sub :
          Tz ⊆ Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0) := by
        intro i hi
        have hi_eq : (u 0 + z • u 1) i = 0 := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hi
        have hi_eq' : u 0 i + z * u 1 i = 0 := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hi_eq
        simp [hi_eq']
      exact le_trans hTz_card (Finset.card_le_card hTz_sub)
    have hsum_lower :
        good.card * (n - e) ≤
          good.sum (fun z => (Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0)).card) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Finset.sum_le_sum fun z hz => hzero_card z hz)
    have hsum_eq :
        good.sum (fun z => (Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0)).card)
          =
        Finset.univ.sum (fun i : ι =>
            (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card) := by
      calc
        good.sum (fun z => (Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0)).card)
            = good.sum (fun z => ∑ i : ι, if u 0 i + z * u 1 i = 0 then 1 else 0) := by
                simp
        _ = ∑ i : ι, good.sum (fun z => if u 0 i + z * u 1 i = 0 then 1 else 0) := by
              rw [Finset.sum_comm]
        _ = ∑ i : ι, (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card := by
              simp
    have hcount_bound :
        ∀ i : ι,
          (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card
            ≤ if i ∈ S0 then good.card else 1 := by
      intro i
      by_cases hcommon : u 0 i = 0 ∧ u 1 i = 0
      · have hiS0 : i ∈ S0 := by
          simp [S0, hcommon]
        simp [hiS0, hcommon]
      · have hiS0 : i ∉ S0 := by
          simp [S0, hcommon]
        have hcard_le_one :
            (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card ≤ 1 := by
          by_cases hu1 : u 1 i = 0
          · have hu0 : u 0 i ≠ 0 := by
              intro hu0
              exact hcommon ⟨hu0, hu1⟩
            have hfilter :
                good.filter (fun z : F => u 0 i + z * u 1 i = 0) = ∅ := by
              ext z
              simp [hu1, hu0]
            simp [hfilter]
          · exact Finset.card_le_one.mpr fun z1 hz1 z2 hz2 => by
              have hz1_eq : u 0 i + z1 * u 1 i = 0 := (Finset.mem_filter.mp hz1).2
              have hz2_eq : u 0 i + z2 * u 1 i = 0 := (Finset.mem_filter.mp hz2).2
              have hmul : (z1 - z2) * u 1 i = 0 := by
                calc
                  (z1 - z2) * u 1 i = (u 0 i + z1 * u 1 i) - (u 0 i + z2 * u 1 i) := by ring
                  _ = 0 := by rw [hz1_eq, hz2_eq]; ring
              rcases mul_eq_zero.mp hmul with hzero | hzero
              · exact sub_eq_zero.mp hzero
              · exact (hu1 hzero).elim
        exact by simpa [hiS0] using hcard_le_one
    have hsum_upper :
        Finset.univ.sum (fun i : ι => (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card)
          ≤ S0.card * good.card + (n - S0.card) := by
      have hbound :
          Finset.univ.sum (fun i : ι =>
              (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card) ≤
            Finset.univ.sum (fun i : ι => if i ∈ S0 then good.card else 1) := by
        exact Finset.sum_le_sum (fun i _ => hcount_bound i)
      have hsum_bound :
          Finset.univ.sum (fun i : ι => if i ∈ S0 then good.card else 1)
            = S0.card * good.card + (n - S0.card) := by
        have hsum_S0 :
            (Finset.univ.filter fun x : ι => x ∈ S0).sum
                (fun x : ι => if x ∈ S0 then good.card else 1)
              = S0.card * good.card := by
          calc
            (Finset.univ.filter fun x : ι => x ∈ S0).sum
                (fun x : ι => if x ∈ S0 then good.card else 1)
              = (Finset.univ.filter fun x : ι => x ∈ S0).sum (fun _ : ι => good.card) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hxS0 : x ∈ S0 := (Finset.mem_filter.mp hx).2
                  simp [hxS0]
            _ = (Finset.univ.filter fun x : ι => x ∈ S0).card * good.card := by
              simp [Nat.mul_comm]
            _ = S0.card * good.card := by
              simp
        have hsum_not :
            (Finset.univ.filter fun x : ι => x ∉ S0).sum
                (fun x : ι => if x ∈ S0 then good.card else 1)
              = (Finset.univ.filter fun x : ι => x ∉ S0).card := by
          calc
            (Finset.univ.filter fun x : ι => x ∉ S0).sum
                (fun x : ι => if x ∈ S0 then good.card else 1)
              = (Finset.univ.filter fun x : ι => x ∉ S0).sum (fun _ : ι => 1) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hxS0 : x ∉ S0 := (Finset.mem_filter.mp hx).2
                  simp [hxS0]
            _ = (Finset.univ.filter fun x : ι => x ∉ S0).card := by
              simp
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun i : ι => i ∈ S0)
          (f := fun i : ι => if i ∈ S0 then good.card else 1)]
        rw [hsum_S0, hsum_not]
        have hcard_split :
            S0.card + (Finset.univ.filter fun x : ι => x ∉ S0).card = n := by
          simpa [n, S0] using
            (Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset ι)) (p := fun i : ι => i ∈ S0))
        have hcard_compl :
            (Finset.univ.filter fun x : ι => x ∉ S0).card = n - S0.card := by
          omega
        rw [hcard_compl]
      exact le_trans hbound (le_of_eq hsum_bound)
    have hS0_card_nat : n - e ≤ S0.card := by
      have hmain :
          good.card * (n - e) ≤ S0.card * good.card + (n - S0.card) := by
        calc
          good.card * (n - e)
              ≤ good.sum (fun z =>
                (Finset.univ.filter (fun i : ι => u 0 i + z * u 1 i = 0)).card) :=
            hsum_lower
          _ = Finset.univ.sum (fun i : ι =>
                (good.filter (fun z : F => u 0 i + z * u 1 i = 0)).card) :=
            hsum_eq
          _ ≤ S0.card * good.card + (n - S0.card) :=
            hsum_upper
      by_contra hS0_small
      have hlt : S0.card < n - e := lt_of_not_ge hS0_small
      have hsucc : S0.card + 1 ≤ n - e := Nat.succ_le_of_lt hlt
      have hupper_lt :
          S0.card * good.card + (n - S0.card) < S0.card * good.card + good.card := by
        refine Nat.add_lt_add_left ?_ (S0.card * good.card)
        exact lt_of_le_of_lt (Nat.sub_le n S0.card) hgood_card
      have hmid_le :
          S0.card * good.card + good.card ≤ good.card * (n - e) := by
        simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using Nat.mul_le_mul_left good.card hsucc
      have hcontra :
          S0.card * good.card + (n - S0.card) < good.card * (n - e) :=
        lt_of_lt_of_le hupper_lt hmid_le
      exact (not_lt_of_ge hmain) hcontra
    have hS0_card :
        (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S0.card : ℝ≥0) := by
      have hnat : n - Nat.floor (δ * n) ≤ S0.card := by
        simpa [n, e] using hS0_card_nat
      simpa [n] using (Code.relDist_floor_bound_iff_complement_bound n S0.card δ).mp hnat
    refine ⟨S0, hS0_card, ?_⟩
    use Code.finMapTwoWords (0 : ι → F) (0 : ι → F)
    intro k
    fin_cases k
    · constructor
      · exact (ReedSolomon.code domain 0).zero_mem
      · intro i hi
        have : u 0 i = 0 := by
          have hi' : i ∈ S0 := hi
          simpa [S0] using (Finset.mem_filter.mp hi').2.1
        simp [Code.finMapTwoWords, this]
    · constructor
      · exact (ReedSolomon.code domain 0).zero_mem
      · intro i hi
        have : u 1 i = 0 := by
          have hi' : i ∈ S0 := hi
          simpa [S0] using (Finset.mem_filter.mp hi').2.2
        simp [Code.finMapTwoWords, this]
  · by_cases hdeg_le : deg ≤ n
    · letI : NeZero deg := ⟨hdeg_zero⟩
      have hBW : 2 * e < n - deg + 1 := by
        simpa [n, e] using
          (RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hdeg_le hδ)
      have hgood_pos : 0 < good.card := lt_trans hn_pos hgood_card
      let P_x : Finset F := Finset.univ.map domain
      let P_y : Finset F := good
      haveI : Nonempty P_x := by
        apply Finset.Nonempty.to_subtype
        simp [P_x]
      haveI : Nonempty P_y := by
        apply Finset.Nonempty.to_subtype
        exact Finset.card_pos.mp hgood_pos
      have evalY_natDegree_le_degreeX (z : F) (f : F[X][Y]) :
          (Polynomial.Bivariate.evalY z f).natDegree ≤ Polynomial.Bivariate.degreeX f := by
        have heval :
            Polynomial.Bivariate.evalY z f =
              ∑ j ∈ f.support, f.coeff j * (Polynomial.C z : F[X]) ^ j := by
          simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
        rw [heval]
        refine
          Polynomial.natDegree_sum_le_of_forall_le
            (s := f.support)
            (f := fun j => f.coeff j * (Polynomial.C z : F[X]) ^ j)
            (n := Polynomial.Bivariate.degreeX f)
            ?_
        intro j hj
        have hj_le :
            (f.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX f :=
          Polynomial.Bivariate.coeff_natDegree_le_degreeX f j
        have hmul :
            (f.coeff j * (Polynomial.C z : F[X]) ^ j).natDegree ≤ (f.coeff j).natDegree := by
          simpa [Polynomial.C_pow] using
            (Polynomial.natDegree_mul_C_le (f := f.coeff j) (a := z ^ j))
        exact le_trans hmul hj_le
      have evalX_eval_eq_evalY_eval (x z : F) (f : F[X][Y]) :
          (Polynomial.Bivariate.evalX x f).eval z = (Polynomial.Bivariate.evalY z f).eval x := by
        calc
          (Polynomial.Bivariate.evalX x f).eval z
              = (f.map (Polynomial.evalRingHom x)).eval z := by
                  simp [ps_eval_x_eq_map]
          _ = f.eval₂ (Polynomial.evalRingHom x) z := by
                simpa using
                  (Polynomial.eval_map (f := Polynomial.evalRingHom x) (p := f) (x := z))
          _ = (Polynomial.eval (Polynomial.C z) f).eval x := by
                simpa [Polynomial.Bivariate.evalY] using
                  (Polynomial.eval₂_at_apply
                    (p := f) (f := Polynomial.evalRingHom x) (r := Polynomial.C z))
          _ = (Polynomial.Bivariate.evalY z f).eval x := by
                simp [Polynomial.Bivariate.evalY]
      obtain ⟨A, B, hA0, hA_degX, hA_degY, hB_degX, hB_degY, hAB⟩ :=
        RS_exists_bivariate_AB_of_goodCoeffs_card_gt
          (deg := deg) (domain := domain) (δ := δ) hdeg_le hδ u hS
      let quot_x : F → F[X] := fun z =>
        if hz : z ∈ good then
          Classical.choose (RS_exists_Pz_of_mem_goodCoeffs
            (deg := deg) (domain := domain) (δ := δ) u (z := z) hz)
        else 0
      let quot_y : F → F[X] := fun x =>
        Polynomial.C (u 0 (Function.invFun domain x)) +
          Polynomial.X * Polynomial.C (u 1 (Function.invFun domain x))
      have h_card_Px : (⟨n, hn_pos⟩ : ℕ+) ≤ P_x.card := by
        simp [P_x, n]
      have h_card_Py : (⟨good.card, hgood_pos⟩ : ℕ+) ≤ P_y.card := by
        simp [P_y]
      have h_quot_x :
          ∀ z ∈ P_y,
            (quot_x z).natDegree ≤ (e + deg - 1) - e ∧
              Polynomial.Bivariate.evalY z B = (quot_x z) * (Polynomial.Bivariate.evalY z A) := by
        intro z hz
        have hz_good : z ∈ good := by simpa [P_y] using hz
        let Pz : F[X] := Classical.choose
          (RS_exists_Pz_of_mem_goodCoeffs (deg := deg)
            (domain := domain) (δ := δ) u (z := z) hz_good)
        have hPz :
            Pz.natDegree < deg ∧
              Δ₀(u 0 + z • u 1, Pz.eval ∘ domain) ≤ e := by
          simpa [Pz, e] using
            (Classical.choose_spec
              (RS_exists_Pz_of_mem_goodCoeffs
                (deg := deg) (domain := domain) (δ := δ) u (z := z) hz_good))
        have hquot_def : quot_x z = Pz := by
          simp [quot_x, hz_good, Pz]
        refine ⟨?_, ?_⟩
        · have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPz.1
          have harith : deg - 1 ≤ (e + deg - 1) - e := by omega
          exact le_trans (by simpa [hquot_def] using hPz_le) harith
        · let Dz : F[X] := Polynomial.Bivariate.evalY z B - Pz * Polynomial.Bivariate.evalY z A
          obtain ⟨Tz, hTz_card, hTz_agree⟩ :=
            (Code.closeToWord_iff_exists_agreementCols
              (u := u 0 + z • u 1) (v := Pz.eval ∘ domain) (e := e)).1 hPz.2
          have hDz_eval :
              ∀ x ∈ Tz.image domain, Dz.eval x = 0 := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨i, hiTz, rfl⟩
            have hi_eq : u 0 i + z * u 1 i = Pz.eval (domain i) := by
              simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hiTz
            have hEq_eval :
                (Polynomial.Bivariate.evalY z B).eval (domain i) =
                  (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
              calc
                (Polynomial.Bivariate.evalY z B).eval (domain i)
                    = (Polynomial.Bivariate.evalX (domain i) B).eval z := by
                        symm
                        exact evalX_eval_eq_evalY_eval (domain i) z B
                _ = (((Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
                      Polynomial.Bivariate.evalX (domain i) A)).eval z := by
                      simpa using congrArg (fun p : F[X] => p.eval z) (hAB i)
                _ = (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)).eval z *
                      (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                        rw [Polynomial.eval_mul]
                _ = ((Polynomial.C (u 0 i)).eval z + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
                      (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                        rw [Polynomial.eval_add]
                _ = (u 0 i + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
                      (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                        simp
                _ = (u 0 i + z * u 1 i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                      rw [Polynomial.eval_mul]
                      simp
                _ = Pz.eval (domain i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                      rw [hi_eq]
                _ = Pz.eval (domain i) * (Polynomial.Bivariate.evalY z A).eval (domain i) := by
                      rw [evalX_eval_eq_evalY_eval]
                _ = (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
                      simp [Polynomial.eval_mul, mul_comm]
            simpa [Dz, sub_eq_zero] using hEq_eval
          have hDz_deg :
              Dz.natDegree ≤ e + deg - 1 := by
            have hB_eval_deg : (Polynomial.Bivariate.evalY z B).natDegree ≤ e + deg - 1 :=
              le_trans (evalY_natDegree_le_degreeX z B) hB_degX
            have hA_eval_deg : (Polynomial.Bivariate.evalY z A).natDegree ≤ e := by
              exact le_trans (evalY_natDegree_le_degreeX z A) hA_degX
            have hprod_deg :
                (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤ e + deg - 1 := by
              have hmul :
                  (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤
                    Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree := by
                exact Polynomial.natDegree_mul_le
                  (p := Pz) (q := Polynomial.Bivariate.evalY z A)
              have hsum :
                  Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree ≤
                    (deg - 1) + e := Nat.add_le_add (Nat.le_pred_of_lt hPz.1) hA_eval_deg
              have hsum' :
                  Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree ≤ e + deg - 1 := by
                omega
              exact le_trans hmul hsum'
            exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hB_eval_deg hprod_deg)
          have hdeg_lt :
              Dz.natDegree < (Tz.image domain).card := by
            have hlt : e + deg - 1 < n - e := by
              omega
            have hcard_lt : e + deg - 1 < Tz.card := lt_of_lt_of_le hlt hTz_card
            have himg :
                (Tz.image domain).card = Tz.card :=
              Finset.card_image_of_injective _ domain.injective
            exact lt_of_le_of_lt hDz_deg (by simpa [himg] using hcard_lt)
          have hDz_zero : Dz = 0 := by
            exact
              Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
                (p := Dz) (s := Tz.image domain) hDz_eval hdeg_lt
          simpa [Dz, hquot_def, sub_eq_zero] using hDz_zero
      have h_quot_y :
          ∀ x ∈ P_x,
            (quot_y x).natDegree ≤ (e + 1) - e ∧
              Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A) := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
        refine ⟨?_, ?_⟩
        · have hconst : (Polynomial.C (u 0 i) : F[X]).natDegree ≤ 1 := by
            simp
          have hlin' : (Polynomial.X * Polynomial.C (u 1 i) : F[X]).natDegree ≤
              (Polynomial.X : F[X]).natDegree := by
            simpa using
              (Polynomial.natDegree_mul_C_le (f := (Polynomial.X : F[X])) (a := u 1 i))
          have hlin : (Polynomial.X * Polynomial.C (u 1 i) : F[X]).natDegree ≤ 1 := by
            simpa using hlin'
          simpa [quot_y, Function.leftInverse_invFun domain.injective i] using
            (le_trans (Polynomial.natDegree_add_le _ _) (max_le hconst hlin))
        · simpa [quot_y, Function.leftInverse_invFun domain.injective i] using hAB i
      have h_le_1 :
          1 >
            ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
              (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ))) := by
        have h2e_deg_le_n : 2 * e + deg ≤ n := by
          omega
        have hnq_pos : (0 : ℚ) < ((⟨n, hn_pos⟩ : ℕ+) : ℚ) := by positivity
        have hfrac_lt :
            (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)) <
              (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
          have hnum_pos : (0 : ℚ) < (((e + 1 : ℕ) : ℚ)) := by positivity
          have hng :
              (((⟨n, hn_pos⟩ : ℕ+) : ℚ)) <
                (((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)) := by
            change (n : ℚ) < (good.card : ℚ)
            exact_mod_cast hgood_card
          exact div_lt_div_of_pos_left hnum_pos hnq_pos hng
        have hsum_lt :
            ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
              (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)))
              <
            (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
          have hsum_lt' :
              ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
                (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)))
                <
              ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
                (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ))) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_lt_add_left hfrac_lt
                ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)))
          have hsum_eq :
              ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
                (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ))) =
              (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
            rw [← add_div]
            congr 1
            exact_mod_cast (by omega : (e + deg - 1) + (e + 1) = 2 * e + deg)
          exact hsum_lt'.trans_eq hsum_eq
        have hle_one : (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) ≤ 1 := by
          rw [div_le_iff₀ hnq_pos]
          simpa using
            (show (((2 * e + deg : ℕ) : ℚ)) ≤ ((⟨n, hn_pos⟩ : ℕ+) : ℚ) by
              exact_mod_cast h2e_deg_le_n)
        exact lt_of_lt_of_le hsum_lt hle_one
      obtain ⟨P, hBA, hP_degX, hP_degY, ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩, _⟩ :=
        polishchuk_spielman
          (a_x := e) (a_y := e) (b_x := e + deg - 1) (b_y := e + 1)
          (n_x := ⟨n, hn_pos⟩) (n_y := ⟨good.card, hgood_pos⟩)
          (h_bx_ge_ax := by omega) (h_by_ge_ay := by omega)
          (A := A) (B := B) hA0 hA_degX hB_degX hA_degY hB_degY
          P_x P_y quot_x quot_y h_card_Px h_card_Py h_quot_x h_quot_y h_le_1
      have hP_degX' : Polynomial.Bivariate.degreeX P ≤ deg - 1 := by
        omega
      let S0 : Finset ι := Q_x.preimage domain domain.injective.injOn
      have hS0_card_nat : n - e ≤ S0.card := by
        have himg : S0.map domain = Q_x := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
            exact Finset.mem_preimage.mp hi
          · intro hx
            rcases Finset.mem_map.mp (hQx_sub hx) with ⟨i, -, rfl⟩
            exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr hx, rfl⟩
        have hcard_eq : S0.card = Q_x.card := by
          calc
            S0.card = (S0.map domain).card := by symm; simp
            _ = Q_x.card := by simp [himg]
        exact by simpa [S0, hcard_eq, n, e] using hQx_card
      have hS0_card :
          (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S0.card : ℝ≥0) := by
        have hnat : n - Nat.floor (δ * n) ≤ S0.card := by
          simpa [n, e] using hS0_card_nat
        simpa [n] using (Code.relDist_floor_bound_iff_complement_bound n S0.card δ).mp hnat
      let v0 : ι → F := (P.coeff 0).eval ∘ domain
      let v1 : ι → F := (P.coeff 1).eval ∘ domain
      have hv_mem (j : ℕ) : ((P.coeff j).eval ∘ domain) ∈ ReedSolomon.code domain deg := by
        have hcoeff_deg_nat : (P.coeff j).natDegree ≤ deg - 1 := by
          exact le_trans (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j) hP_degX'
        have hcoeff_deg : (P.coeff j).degree < deg := by
          have hlt_nat : (P.coeff j).natDegree < deg := by
            exact lt_of_le_of_lt hcoeff_deg_nat (Nat.pred_lt (NeZero.ne deg))
          exact lt_of_le_of_lt (Polynomial.degree_le_natDegree (p := P.coeff j))
            (by exact_mod_cast hlt_nat)
        refine ⟨P.coeff j, ?_, by ext i; rfl⟩
        simpa [Polynomial.mem_degreeLT] using hcoeff_deg
      refine ⟨S0, hS0_card, ?_⟩
      use Code.finMapTwoWords v0 v1
      intro k
      fin_cases k
      · constructor
        · simpa [v0] using hv_mem 0
        · intro i hi
          have hiQ : domain i ∈ Q_x := Finset.mem_preimage.mp hi
          have hEval : Polynomial.Bivariate.evalX (domain i) P = quot_y (domain i) := hQx_eval _ hiQ
          have hcoeff := congrArg (fun p : F[X] => p.coeff 0) hEval
          simpa [v0, quot_y, Polynomial.Bivariate.evalX, Polynomial.coeff,
            Function.leftInverse_invFun domain.injective i] using hcoeff
      · constructor
        · simpa [v1] using hv_mem 1
        · intro i hi
          have hiQ : domain i ∈ Q_x := Finset.mem_preimage.mp hi
          have hEval : Polynomial.Bivariate.evalX (domain i) P = quot_y (domain i) := hQx_eval _ hiQ
          have hcoeff := congrArg (fun p : F[X] => p.coeff 1) hEval
          simpa [v1, quot_y, Polynomial.Bivariate.evalX, Polynomial.coeff,
            Function.leftInverse_invFun domain.injective i] using hcoeff
    · have hdeg_gt : n < deg := Nat.lt_of_not_ge hdeg_le
      let p0 : F[X] := Lagrange.interpolate Finset.univ domain (u 0)
      let p1 : F[X] := Lagrange.interpolate Finset.univ domain (u 1)
      have hp_mem (p : F[X]) (w : ι → F)
          (hp_eval : ∀ i, p.eval (domain i) = w i)
          (hp_deg : p.degree < (Fintype.card ι : WithBot ℕ)) :
          w ∈ ReedSolomon.code domain deg := by
        refine ⟨p, ?_, ?_⟩
        · have hdeg_gt' : (Fintype.card ι : WithBot ℕ) < deg := by
            exact_mod_cast hdeg_gt
          have hp_deg' : p.degree < deg := lt_of_lt_of_le hp_deg (le_of_lt hdeg_gt')
          simpa [Polynomial.mem_degreeLT] using hp_deg'
        · ext i
          exact hp_eval i
      have hp0_deg : p0.degree < (Fintype.card ι : WithBot ℕ) := by
        simpa [p0] using
          (Lagrange.degree_interpolate_lt (s := Finset.univ) (v := domain) (r := u 0)
            (by intro x _ y _ hxy; exact domain.injective hxy))
      have hp1_deg : p1.degree < (Fintype.card ι : WithBot ℕ) := by
        simpa [p1] using
          (Lagrange.degree_interpolate_lt (s := Finset.univ) (v := domain) (r := u 1)
            (by intro x _ y _ hxy; exact domain.injective hxy))
      have hp0_eval : ∀ i, p0.eval (domain i) = u 0 i := by
        intro i
        simpa [p0] using
          (Lagrange.eval_interpolate_at_node (s := Finset.univ)
            (v := domain) (r := u 0)
            (by intro x hx y hy hxy; exact domain.injective hxy)
            (by simp : i ∈ (Finset.univ : Finset ι)))
      have hp1_eval : ∀ i, p1.eval (domain i) = u 1 i := by
        intro i
        simpa [p1] using
          (Lagrange.eval_interpolate_at_node (s := Finset.univ)
            (v := domain) (r := u 1)
            (by intro x hx y hy hxy; exact domain.injective hxy)
            (by simp : i ∈ (Finset.univ : Finset ι)))
      have huniv_card :
          (1 - δ) * (Fintype.card ι : ℝ≥0) ≤
            ((Finset.univ : Finset ι).card : ℝ≥0) := by
        simp
      refine ⟨Finset.univ, huniv_card, ?_⟩
      use Code.finMapTwoWords (u 0) (u 1)
      intro k
      fin_cases k
      · constructor
        · exact hp_mem p0 (u 0) hp0_eval hp0_deg
        · intro i hi
          simp [Code.finMapTwoWords]
      · constructor
        · exact hp_mem p1 (u 1) hp1_eval hp1_deg
        · intro i hi
          simp [Code.finMapTwoWords]

end CoreResults

end ProximityGap
