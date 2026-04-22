/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def RS_goodCoeffs {deg : ℕ} {domain : ι ↪ F}
    (u : WordStack F (Fin 2) ι) (δ : ℝ≥0) : Finset F :=
  Finset.filter (fun z : F => δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ) Finset.univ

open Polynomial in
theorem RS_exists_Pz_of_mem_goodCoeffs {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι) {z : F}
    (hz : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ) :
    ∃ Pz : F[X], Pz.natDegree < deg ∧
      Δ₀(u 0 + z • u 1, Pz.eval ∘ domain) ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  have hz' :
      z ∈
        Finset.filter
          (fun z : F => δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ)
          Finset.univ := by
    simpa [RS_goodCoeffs] using hz
  have hrel : δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ :=
    (Finset.mem_filter.mp hz').2
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hdist :
      Δ₀(u 0 + z • u 1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h :=
      (Code.relDistFromCode_le_iff_distFromCode_le
          (u := u 0 + z • u 1) (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ)).1
        hrel
    simpa [e] using h
  rcases
      (Code.closeToCode_iff_closeToCodeword_of_minDist
            (u := u 0 + z • u 1) (C := (ReedSolomon.code domain deg : Set (ι → F)))
            (e := e)).1
        hdist with
    ⟨v, hvC, hvdist⟩
  rcases hvC with ⟨Pz, hPz, rfl⟩
  refine ⟨Pz, ?_, ?_⟩
  · exact ReedSolomon.natDegree_lt_of_mem_degreeLT (deg := deg) hPz
  · simpa [e] using hvdist

open scoped BigOperators in
open Polynomial in
theorem RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffs
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι) {z : F}
    (hz : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F,
      ∃ b : Fin (e + deg) → F,
        a ≠ 0 ∧
          Matrix.mulVec
              (BW_homMatrix (ι := ι) e deg (fun i => domain i)
                (fun i => u 0 i + z * u 1 i))
              (Fin.append a b) = 0 := by
  classical
  -- Unfold the `let e := ...` in the goal, but avoid changing the quantifier structure
  simp only
  -- Name the error bound (this rewrites occurrences of the floor expression)
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  -- Get the close polynomial `Pz`
  obtain ⟨Pz, hPzdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffs (deg := deg) (domain := domain) (δ := δ) u (z := z) hz
  have hdist' : Δ₀(u 0 + z • u 1, Pz.eval ∘ domain) ≤ e := by
    simpa [he] using hdist
  -- Extract a small set of disagreement coordinates
  obtain ⟨D, hDcard, hAgree⟩ :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols
        (u := u 0 + z • u 1)
        (v := Pz.eval ∘ domain)
        (e := e)).1 hdist'
  -- Error-locator polynomial and the corresponding `Q`
  set E : F[X] := ∏ i ∈ D, (Polynomial.X - Polynomial.C (domain i)) with hE
  set Q : F[X] := E * Pz with hQ
  -- Coefficient vectors (truncated to the required degrees)
  let a : Fin (e + 1) → F := fun t => E.coeff t.1
  let b : Fin (e + deg) → F := fun s => Q.coeff s.1
  have hE_monic : E.Monic := by
    -- `E` is a product of monic linear factors
    simpa [hE] using (Polynomial.monic_prod_X_sub_C (b := fun i : ι => domain i) (s := D))
  have hE_natDegree : E.natDegree = D.card := by
    -- degree of product of monic polynomials is sum of degrees
    have hdeg :=
      Polynomial.natDegree_prod_of_monic (s := D)
        (f := fun i : ι => (Polynomial.X - Polynomial.C (domain i) : F[X]))
        (by
          intro i hi
          simpa using (Polynomial.monic_X_sub_C (domain i)))
    -- simplify the RHS
    convert hdeg using 1
    simp
  have hE_deg_lt : E.natDegree < e + 1 := by
    have : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    simpa [hE_natDegree] using this
  have hQ_deg_lt : Q.natDegree < e + deg := by
    -- `natDegree (E*Pz) ≤ natDegree E + natDegree Pz`
    have hmul : Q.natDegree ≤ E.natDegree + Pz.natDegree := by
      simpa [hQ] using (Polynomial.natDegree_mul_le (p := E) (q := Pz))
    have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPzdeg
    have hE_le : E.natDegree ≤ e := by
      simpa [hE_natDegree] using hDcard
    have hsum_le : E.natDegree + Pz.natDegree ≤ e + (deg - 1) := Nat.add_le_add hE_le hPz_le
    have hle : Q.natDegree ≤ e + (deg - 1) := le_trans hmul (by simpa [Nat.add_assoc] using hsum_le)
    -- turn into a strict inequality
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    have : e + (deg - 1) < e + deg :=
      Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hdegpos)) e
    exact lt_of_le_of_lt hle this
  -- `a` is nonzero because the leading coefficient of `E` is 1
  have ha_ne : a ≠ 0 := by
    have hcard_lt : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    let t0 : Fin (e + 1) := ⟨D.card, hcard_lt⟩
    have hcoeff : E.coeff D.card = 1 := by
      have hlead : E.leadingCoeff = 1 := hE_monic.leadingCoeff
      simpa [Polynomial.leadingCoeff, hE_natDegree] using hlead
    have ht0 : a t0 = 1 := by
      simpa [a, t0] using hcoeff
    intro hzero
    have hz0 : a t0 = 0 := by
      simpa using congrArg (fun f => f t0) hzero
    have h1 : (1 : F) = 0 := by
      rwa [ht0] at hz0
    exact one_ne_zero h1
  refine ⟨a, b, ha_ne, ?_⟩
  -- Show the vector is in the kernel via the characterization lemma
  apply (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (e := e) (k := deg)
      (ωs := fun i => domain i)
      (f := fun i => u 0 i + z * u 1 i)
      (a := a) (b := b)).2
  intro i
  -- Convert the coefficient sums into polynomial evaluations
  have hsum_a : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) = E.eval (domain i) := by
    have hfin : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1)
        = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n := by
      simpa [a] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => E.coeff n * (domain i) ^ n) (n := e + 1))
    have heval : E.eval (domain i) = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := E) (n := e + 1) hE_deg_lt (domain i)
    simpa [hfin] using heval.symm
  have hsum_b : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1) = Q.eval (domain i) := by
    have hfin : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1)
        = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => Q.coeff n * (domain i) ^ n) (n := e + deg))
    have heval : Q.eval (domain i) = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := Q) (n := e + deg) hQ_deg_lt (domain i)
    simpa [hfin] using heval.symm
  -- Reduce to showing `E.eval ω * f = Q.eval ω` and discharge by cases
  by_cases hiD : i ∈ D
  · -- On error positions, `E(ω_i)=0`
    have hE0 : E.eval (domain i) = 0 := by
      -- expand `E` and use that evaluation commutes with products
      rw [hE]
      rw [Polynomial.eval_prod (s := D)
        (p := fun j : ι => (Polynomial.X - Polynomial.C (domain j) : F[X]))
        (x := domain i)]
      refine Finset.prod_eq_zero hiD ?_
      simp
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by rw [hsum_a]
      _ = 0 := by simp [hE0]
      _ = Q.eval (domain i) := by
            have hmul_eval : Q.eval (domain i) = (E.eval (domain i)) * (Pz.eval (domain i)) := by
              rw [hQ, Polynomial.eval_mul]
            simp [hmul_eval, hE0]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]
  · -- On agreement positions, `f_i = Pz(ω_i)`
    have hf_eq : (u 0 i + z * u 1 i) = Pz.eval (domain i) := by
      have := hAgree i hiD
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by rw [hsum_a]
      _ = (E.eval (domain i)) * (Pz.eval (domain i)) := by simp [hf_eq]
      _ = Q.eval (domain i) := by
            rw [hQ, Polynomial.eval_mul]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N ↪ ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
            r id) = 0 := by
  classical
  dsimp
  intro r
  -- Abbreviations for the parameters appearing throughout
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  let N : ℕ := (e + 1) + (e + deg)
  -- The set of "good" coefficients
  let S : Finset F := RS_goodCoeffs (deg := deg) (domain := domain) u δ
  -- Polynomial matrix and its square submatrix
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg
      (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
  let A : Matrix (Fin N) (Fin N) F[X] :=
    Matrix.submatrix M (r : Fin N → ι) (id : Fin N → Fin N)
  -- Degree bound on det(A)
  have hdeg_det : (Matrix.det A).natDegree ≤ e + 1 := by
    simpa [A, M, N, e] using
      (BW_homMatrix_det_submatrix_natDegree_le_e_add_one (ι := ι) (F := F) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i)
        (r := (r : Fin N → ι)))
  -- Bound e+1 ≤ card ι
  have he1_le : e + 1 ≤ Fintype.card ι := by
    simpa [e] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) (hdeg := hdeg) (hδ := hδ))
  -- card ι < card S
  have hS' : Fintype.card ι < S.card := by
    simpa [S] using hS
  have he1_lt : e + 1 < S.card := lt_of_le_of_lt he1_le hS'
  have hdeg_lt : (Matrix.det A).natDegree < S.card := lt_of_le_of_lt hdeg_det he1_lt
  -- det(A) vanishes on all points of S
  have heval : ∀ z ∈ S, (Matrix.det A).eval z = 0 := by
    intro z hz
    have hz' : z ∈ RS_goodCoeffs (deg := deg) (domain := domain) u δ := by
      simpa [S] using hz
    -- Extract a nonzero kernel vector for the evaluated BW matrix
    have hk :=
      RS_exists_kernelVec_BW_homMatrix_eval_of_mem_goodCoeffs (deg := deg) (domain := domain)
        (δ := δ) (u := u) (z := z) hz'
    -- unfold the `let e := ...` in hk
    dsimp at hk
    rcases hk with ⟨a, b, ha0, hmul⟩
    let v : Fin N → F := Fin.append a b
    have hv_ne : v ≠ 0 := by
      intro hv
      apply ha0
      ext i
      have hvi : v (Fin.castAdd (e + deg) i) = (0 : Fin N → F) (Fin.castAdd (e + deg) i) :=
        congrArg (fun f => f (Fin.castAdd (e + deg) i)) hv
      simpa [v, N] using hvi
    let Mz : Matrix ι (Fin N) F :=
      BW_homMatrix (ι := ι) e deg (fun i => domain i) (fun i => u 0 i + z * u 1 i)
    have hmulMz : Mz *ᵥ v = 0 := by
      simpa [Mz, v, N, e] using hmul
    have hmulSub :
        (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v = 0 := by
      ext i
      have hi : (Mz *ᵥ v) (r i) = 0 := by
        simpa using congrArg (fun f => f (r i)) hmulMz
      simpa [Matrix.mulVec, Matrix.submatrix] using hi
    have hdetMz :
        Matrix.det (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) = 0 := by
      have hex : ∃ v' : Fin N → F, v' ≠ 0 ∧
          (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v' = 0 :=
        ⟨v, hv_ne, hmulSub⟩
      exact (Matrix.exists_mulVec_eq_zero_iff
        (M := Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N))).1 hex
    -- Relate evaluation of det(A) to determinant of the evaluated matrix
    have hdet_eval : (Matrix.det A).eval z = Matrix.det (A.map (Polynomial.eval z)) := by
      simpa [Polynomial.coe_evalRingHom] using (RingHom.map_det (Polynomial.evalRingHom z) A)
    -- Identify the mapped matrix with the evaluated BW matrix
    have hAmap : A.map (Polynomial.eval z) =
        Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N) := by
      have hMmap : M.map (Polynomial.eval z) = Mz := by
        simpa [M, Mz, N, e, Polynomial.coe_evalRingHom] using
          (BW_homMatrix_map_evalRingHom (ι := ι) (F := F) e deg (fun i => domain i)
            (fun i => u 0 i) (fun i => u 1 i) z)
      ext i j
      change (M.map (Polynomial.eval z)) (r i) j = Mz (r i) j
      rw [hMmap]
    -- conclude evaluation is zero
    rw [hdet_eval]
    simpa [hAmap] using hdetMz
  -- Root counting: det(A) has too many roots, hence is zero
  have hdetA0 : Matrix.det A = 0 := by
    exact
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p := Matrix.det A) (s := S) heval
        (by simpa using hdeg_lt)
  -- Finish: unfold A and M
  simpa [A, M, N, e] using hdetA0

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt_fun
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    let N : ℕ := (e + 1) + (e + deg)
    ∀ r : Fin N → ι,
      Matrix.det
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e deg
              (fun i => (Polynomial.C (domain i) : F[X]))
              (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
            r id) = 0 := by
  classical
  dsimp
  intro r
  by_cases hinj : Function.Injective r
  · let r' :
        Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)) ↪ ι :=
      ⟨r, hinj⟩
    have h :=
      RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt
        (deg := deg) (domain := domain) (δ := δ) u hdeg hδ hS
    dsimp at h
    exact h r'
  · have hinj' :
        ∃ i j : Fin ((Nat.floor (δ * Fintype.card ι) + 1) + (Nat.floor (δ * Fintype.card ι) + deg)),
        r i = r j ∧ i ≠ j := by
      -- unfold Injective and push negation
      have : ¬ (∀ i j, r i = r j → i = j) := by
        simpa [Function.Injective] using hinj
      push Not at this
      -- `this` is now ∃ i j, r i = r j ∧ i ≠ j
      simpa [and_left_comm, and_assoc, and_comm] using this
    rcases hinj' with ⟨i, j, hij, hne⟩
    have hrow : (Matrix.submatrix
        (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
        r id) i =
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          r id) j := by
      ext k
      simp [Matrix.submatrix, hij]
    -- determinant is zero due to repeated rows
    exact Matrix.det_zero_of_row_eq (M :=
        Matrix.submatrix
          (BW_homMatrix (ι := ι) (Nat.floor (δ * Fintype.card ι)) deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          r id) hne hrow

omit [Nonempty ι] in
theorem card_RS_goodCoeffs_gt_of_prob_gt_n_div_q
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin 2) ι)
    (hprob :
      Pr_{ let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ]
        > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) :
    (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι := by
  classical
  -- predicate defining the good coefficients
  let P : F → Prop := fun z : F =>
    δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ
  -- uniform probability equals (card of filter) / (card of the field)
  have hPr :
      Pr_{ let z ← $ᵖ F }[ P z ] =
        ((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    classical
    -- Expand the probability mass at `True`
    simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply, eq_iff_iff,
      mul_ite, mul_one, mul_zero, ENNReal.coe_natCast]
    simp only [DFunLike.coe, true_iff]
    -- Reduce the infinite sum to the finite support
    rw [
      tsum_eq_sum (α := ENNReal) (β := F)
        (f := fun a => if P a then (↑(Fintype.card F))⁻¹ else 0)
        (s := Finset.filter P Finset.univ)
        (hf := fun b => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hb
          simp only [hb, if_false])
    ]
    -- Evaluate the resulting finite sum
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul']
    rw [mul_comm]
    conv_lhs =>
      rw [← div_eq_mul_inv]
    -- Filtering twice is the same as filtering once
    have h_card_eq : {x ∈ filter P univ | P x} = filter P univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [and_self_iff]
    rw [h_card_eq]
  -- restate the hypothesis using `P`
  have hprobP :
      Pr_{ let z ← $ᵖ F }[ P z ] > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    simpa [P] using hprob
  -- rewrite the probability lower bound as a ratio comparison
  have hprobQ := hprobP
  rw [hPr] at hprobQ
  -- switch to `<` form
  have hlt :
      ((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal)
        <
          (((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) /
            (Fintype.card F : ℝ≥0) : ENNReal) :=
    (gt_iff_lt).1 hprobQ
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top (Fintype.card F)
  have hcard_cast :
      (Fintype.card ι : ENNReal) <
        ((Finset.filter (α := F) P Finset.univ).card : ENNReal) := by
    -- rewrite both sides of `hlt` as ENNReal divisions and cancel
    have hlt' :
        (Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal)
          < ((Finset.filter (α := F) P Finset.univ).card : ENNReal) /
              (Fintype.card F : ENNReal) := by
      have hq0' : (Fintype.card F : ℝ≥0) ≠ 0 := by
        simp [Fintype.card_ne_zero]
      simpa [ENNReal.coe_div (r := (Fintype.card F : ℝ≥0)) hq0', ENNReal.coe_natCast] using hlt
    exact (ENNReal.div_lt_div_iff_left (hc₀ := hq0) (hc := hqtop)).1 hlt'
  have hcard_nat : Fintype.card ι < (Finset.filter (α := F) P Finset.univ).card := by
    exact Nat.cast_lt.mp hcard_cast
  -- identify the filtered finset with `RS_goodCoeffs`
  simpa [RS_goodCoeffs, P, gt_iff_lt] using hcard_nat

open scoped BigOperators in
open Polynomial in
open Matrix in
open BerlekampWelch in
theorem RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
    ∃ a : Fin (e + 1) → F[X],
      ∃ b : Fin (e + deg) → F[X],
        Fin.append a b ≠ 0 ∧
          (∀ t, (a t).natDegree ≤ e) ∧
            (∀ s, (b s).natDegree ≤ e + 1) ∧
              Matrix.mulVec
                  (BW_homMatrix (ι := ι) e deg
                    (fun i => (Polynomial.C (domain i) : F[X]))
                    (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
                  (Fin.append a b) = 0 := by
  classical
  -- unfold the initial `let e := ...`
  dsimp
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  let m : ℕ := e + 1
  let n : ℕ := e + deg
  let N : ℕ := m + n
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
  have hdetM : ∀ r : Fin N → ι, Matrix.det (Matrix.submatrix M r id) = 0 := by
    intro r
    simpa [M, N, m, n, he] using
      (RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt_fun (deg := deg)
        (domain := domain) (δ := δ) (u := u) hdeg hδ hS r)
  have hcard_n : n ≤ Fintype.card ι := by
    simpa [n, e, he] using
      (RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)
  obtain ⟨rB⟩ : Nonempty (Fin n ↪ ι) := by
    classical
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard_n
  let cL : Fin m → Fin N := fun j => Fin.castAdd n j
  let cR : Fin n → Fin N := fun j => Fin.natAdd m j
  let L : Matrix ι (Fin m) F[X] := Matrix.submatrix M id cL
  let R : Matrix ι (Fin n) F[X] := Matrix.submatrix M id cR
  let A21 : Matrix (Fin n) (Fin m) F[X] := Matrix.submatrix M rB cL
  let D : Matrix (Fin n) (Fin n) F[X] := Matrix.submatrix M rB cR
  have hD : D = -Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])) := by
    funext i j
    have hj' : ¬ e + 1 + (j : ℕ) ≤ e := by
      omega
    simp [D, M, BW_homMatrix, cR, Matrix.vandermonde, m, hj']
  have hvB : Function.Injective (fun i : Fin n => domain (rB i)) := by
    intro i1 i2 h
    apply rB.injective
    apply domain.injective
    exact h
  have hdetV : IsUnit
      (Matrix.det
        (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])))) := by
    simpa using
      (RS_isUnit_det_vandermonde_C_of_injective (F := F) n (fun i : Fin n => domain (rB i)) hvB)
  have hdetD : IsUnit (Matrix.det D) := by
    have hunitNeg : IsUnit ((-1 : F[X]) ^ Fintype.card (Fin n)) := by
      simpa using (isUnit_neg_one (α := F[X])).pow (Fintype.card (Fin n))
    have hdetD' :
        Matrix.det D =
          (-1 : F[X]) ^ Fintype.card (Fin n) *
            Matrix.det
              (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X]))) := by
      simp [hD, Matrix.det_neg]
    refine hdetD'.symm ▸ (hunitNeg.mul hdetV)
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D hdetD
  let K0 : Matrix ι (Fin m) F[X] := L - R * (⅟D * A21)
  have hdetK0 : ∀ rA : Fin m → ι, Matrix.det (K0.submatrix rA id) = 0 := by
    intro rA
    let r : Fin N → ι := Fin.append rA rB
    have hdetA : Matrix.det (M.submatrix r id) = 0 := hdetM r
    let eSum : (Fin m ⊕ Fin n) ≃ Fin N := finSumFinEquiv (m := m) (n := n)
    let Ablocks : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) F[X] :=
      (M.submatrix r id).submatrix eSum eSum
    have hdetAblocks : Matrix.det Ablocks = 0 := by
      have hdetEq : Matrix.det Ablocks = Matrix.det (M.submatrix r id) := by
        simpa [Ablocks] using (Matrix.det_submatrix_equiv_self (e := eSum) (M.submatrix r id))
      simpa [hdetEq] using hdetA
    have hAblocks_eq :
        Ablocks = Matrix.fromBlocks (L.submatrix rA id) (R.submatrix rA id) A21 D := by
      funext i j
      cases i <;> cases j <;>
        simp (config := { zeta := true })
          [Ablocks, eSum, L, R, A21, D, r, cL, cR, Matrix.fromBlocks, N, m, n]
    have hmul :
        Matrix.det D *
            Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) =
          0 := by
      have hformula :=
        (Matrix.det_fromBlocks₂₂ (A := L.submatrix rA id) (B := R.submatrix rA id)
          (C := A21) (D := D))
      simpa [hAblocks_eq, hformula, Matrix.mul_assoc] using hdetAblocks
    have hdetSchur :
        Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) = 0 := by
      exact (IsUnit.mul_right_eq_zero (a := Matrix.det D)
        (b := Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)) hdetD).1 hmul
    simpa [K0, Matrix.submatrix_sub, Matrix.submatrix_mul, Matrix.submatrix_submatrix,
      Matrix.mul_assoc, Function.comp, L, R] using hdetSchur
  have hdegL : ∀ i j, (L i j).natDegree ≤ 1 := by
    intro i j
    simpa [L, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cL j))
  have hdegA21 : ∀ i j, (A21 i j).natDegree ≤ 1 := by
    intro i j
    simpa [A21, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) (rB i) (cL j))
  have hdegR0 : ∀ i j, (R i j).natDegree = 0 := by
    intro i j
    have hj : e + 1 ≤ (cR j).1 := by
      simp [cR, m]
    simpa [R, cR, M] using
      (BW_homMatrix_entry_natDegree_eq_zero_of_ge (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cR j) hj)
  have hdegInvD0 : ∀ i j : Fin n, (D⁻¹ i j).natDegree = 0 := by
    intro i j
    simpa [hD] using
      (RS_natDegree_inv_neg_vandermonde_C_eq_zero
        (F := F) n (fun t : Fin n => domain (rB t)) hvB i j)
  have hdegInvDA21 : ∀ i j, ((⅟D * A21) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ((⅟D i k) * (A21 k j)).natDegree ≤ 1 := by
      intro k hk
      have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
      calc
        ((⅟D i k) * (A21 k j)).natDegree ≤ (⅟D i k).natDegree + (A21 k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + (A21 k j).natDegree := by
          simp [Matrix.invOf_eq_nonsing_inv, hInv']
        _ = (A21 k j).natDegree := by simp
        _ ≤ 1 := hdegA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => (⅟D i k) * (A21 k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegRInvDA21 : ∀ i j, ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (R i k * ((⅟D * A21) k j)).natDegree ≤ 1 := by
      intro k hk
      have hR : (R i k).natDegree = 0 := hdegR0 i k
      calc
        (R i k * ((⅟D * A21) k j)).natDegree ≤ (R i k).natDegree + ((⅟D * A21) k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + ((⅟D * A21) k j).natDegree := by simp [hR]
        _ = ((⅟D * A21) k j).natDegree := by simp
        _ ≤ 1 := hdegInvDA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => R i k * ((⅟D * A21) k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegK0 : ∀ i j, (K0 i j).natDegree ≤ 1 := by
    intro i j
    have hsub : (L i j - (R * (⅟D * A21)) i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree :=
      Polynomial.natDegree_sub_le (L i j) ((R * (⅟D * A21)) i j)
    have hmax :
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
      exact max_le_iff.mpr ⟨hdegL i j, hdegRInvDA21 i j⟩
    have : (K0 i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree := by
      simpa [K0] using hsub
    exact le_trans this hmax
  have hcard_m : m ≤ Fintype.card ι := by
    simpa [m, e, he] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) hdeg hδ)
  obtain ⟨a, ha0, ha_deg, haKer⟩ :=
    RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (ι := ι) (F := F) e K0
      (by simpa [m] using hcard_m) hdegK0 (by
        intro rA
        simpa [m, K0] using hdetK0 rA)
  let b : Fin n → F[X] := -(⅟D).mulVec (A21.mulVec a)
  refine ⟨a, b, ?_, ha_deg, ?_, ?_⟩
  · intro happ
    apply ha0
    funext t
    have := congrArg (fun f : Fin N → F[X] => f (Fin.castAdd n t)) happ
    simpa [Fin.append_left, m, n, N, b] using this
  · intro s
    classical
    have hdegA21mulVec : ∀ i : Fin n, ((A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ t ∈ (Finset.univ : Finset (Fin m)),
          (A21 i t * a t).natDegree ≤ e + 1 := by
        intro t ht
        have hA : (A21 i t).natDegree ≤ 1 := hdegA21 i t
        have ha : (a t).natDegree ≤ e := ha_deg t
        have hmul : (A21 i t * a t).natDegree ≤ (A21 i t).natDegree + (a t).natDegree :=
          Polynomial.natDegree_mul_le
        have hadd : (A21 i t).natDegree + (a t).natDegree ≤ 1 + e := Nat.add_le_add hA ha
        have : (A21 i t * a t).natDegree ≤ 1 + e := le_trans hmul hadd
        simpa [Nat.add_comm] using this
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin m)))
          (n := e + 1) (f := fun t : Fin m => A21 i t * a t) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    have hdegInvDmulVec : ∀ i : Fin n, ((⅟D).mulVec (A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤ e + 1 := by
        intro k hk
        have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
        have hA : ((A21.mulVec a) k).natDegree ≤ e + 1 := hdegA21mulVec k
        calc
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤
              (⅟D i k).natDegree + (A21.mulVec a k).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + (A21.mulVec a k).natDegree := by
            simp [Matrix.invOf_eq_nonsing_inv, hInv']
          _ = (A21.mulVec a k).natDegree := by simp
          _ ≤ e + 1 := hA
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
          (n := e + 1) (f := fun k : Fin n => (⅟D i k) * (A21.mulVec a k)) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    simpa [b] using hdegInvDmulVec s
  · -- kernel equation
    have hRb : Matrix.mulVec R b = -Matrix.mulVec (R * (⅟D * A21)) a := by
      ext i
      simp [b, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
    have hLR : Matrix.mulVec L a + Matrix.mulVec R b = 0 := by
      have haKer' : Matrix.mulVec (L - R * (⅟D * A21)) a = 0 := by
        simpa [K0] using haKer
      have haKer'' : Matrix.mulVec L a - Matrix.mulVec (R * (⅟D * A21)) a = 0 := by
        simpa [Matrix.sub_mulVec] using haKer'
      simpa [sub_eq_add_neg, hRb] using haKer''
    have hsplit : Matrix.mulVec M (Fin.append a b) = Matrix.mulVec L a + Matrix.mulVec R b := by
      simpa [L, R, cL, cR, N] using
        (RS_mulVec_append_castAdd_natAdd (ι := ι) (R := F[X]) m n M a b)
    change Matrix.mulVec M (Fin.append a b) = 0
    rw [hsplit]
    exact hLR
open scoped BigOperators in
open Polynomial in
open BerlekampWelch in
theorem RS_exists_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin 2) ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι) :
    let e : ℕ := Nat.floor (δ * Fintype.card ι)
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
  classical
  -- unfold the outer `let e := ...` in the goal
  dsimp
  -- obtain a nonzero kernel vector from the stronger existence lemma
  have h :=
    RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt
      (deg := deg) (domain := domain) (δ := δ) (u := u) hdeg hδ hS
  -- unfold the `let e := ...` in the hypothesis
  dsimp at h
  rcases h with ⟨a, b, happend, ha_deg, hb_deg, hMul⟩
  have hdeg' : Nat.floor (δ * Fintype.card ι) + deg ≤ Fintype.card ι :=
    RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR
      (deg := deg) (domain := domain) (δ := δ) (hdeg := hdeg) (hδ := hδ)
  have ha0 : a ≠ 0 :=
    RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero
      (deg := deg) (domain := domain) (e := Nat.floor (δ * Fintype.card ι))
      (u := u) (a := a) (b := b) hdeg' happend hMul
  refine ⟨a, b, ha0, ha_deg, hb_deg, hMul⟩

end CoreResults

end ProximityGap
