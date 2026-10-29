/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bruce Lee
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Berlekamp–Welch matrices for parameterised curves

Auxiliary results for the proof of [BCIKS20] Theorem 6.1
(`ProximityGap.large_agreement_set_on_curve_implies_correlated_agreement`), which generalise the
affine-line argument of `AffineLines/BWMatrix.lean` and `AffineLines/JointAgreement.lean` to a
curve of degree `l`, i.e. to `l + 1` words.

Write `p_x(Y) = ∑ i, u i x * Y^i` for the polynomial in the curve parameter attached to the
coordinate `x`.

1. At every good parameter `z` the Berlekamp–Welch error locator gives a nonzero solution of a
   linear system whose matrix is the evaluated curve BW matrix.
2. Every `N × N` minor of the symbolic matrix `curveBWMatrix` (entries in `F[Y]`) therefore
   vanishes at all good parameters; its degree is at most `l * (e + 1) ≤ l * n < |S|`, so the
   minors vanish identically.
3. A Schur complement against the constant Vandermonde block gives a kernel vector over `F[Y]`
   with controlled degrees, assembled into bivariate polynomials `A` and `B` satisfying the
   column relations `A (domain x, Y) * p_x(Y) = B (domain x, Y)`.
4. The row relations `B(X, z) = q_z(X) * A(X, z)` follow by degree counting at the agreement
   positions of each good `z`.
5. `polishchuk_spielman` then divides `B` by `A`, which yields correlated agreement.
-/

@[expose] public section

namespace ProximityGap.CurveBW

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code ProximityGap

/-! ## Generic polynomial helpers -/

theorem natDegree_det_le_sum_of_natDegree_le {R : Type} [CommRing R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Polynomial R)) (d : Fin m → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))
    (f := fun σ : Equiv.Perm (Fin m) => Equiv.Perm.sign σ • ∏ i : Fin m, A (σ i) i)
    (n := ∑ j, d j) ?_
  intro σ _
  exact (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) (∏ i : Fin m, A (σ i) i)).trans
    ((Polynomial.natDegree_prod_le (s := Finset.univ) (f := fun i : Fin m => A (σ i) i)).trans
      (Finset.sum_le_sum fun i _ => h _ _))

theorem natDegree_det_le_of_entry_natDegree_le {R : Type} [CommRing R] {m d : ℕ}
    (A : Matrix (Fin m) (Fin m) (Polynomial R)) (h : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.natDegree ≤ m * d := by
  refine (natDegree_det_le_sum_of_natDegree_le A (fun _ => d) h).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

variable {F : Type} [Field F] {n : ℕ}

/-- The polynomial in the curve parameter attached to the coordinate `x`:
`p_x(Y) = ∑ i, u i x * Y^i`. Its value at `z` is the `x`-th coordinate of the curve point. -/
noncomputable def curveParamPoly {l : ℕ} (u : Fin (l + 1) → Fin n → F) (x : Fin n) :
    Polynomial F :=
  ∑ i : Fin (l + 1), Polynomial.C (u i x) * Polynomial.X ^ (i : ℕ)

lemma curveParamPoly_eval {l : ℕ} (u : Fin (l + 1) → Fin n → F) (x : Fin n) (z : F) :
    (curveParamPoly u x).eval z =
      Curve.polynomialCurveEval (F := F) (A := F) u z x := by
  rw [curveParamPoly, Curve.polynomialCurveEval, Polynomial.eval_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

lemma curveParamPoly_natDegree_le {l : ℕ} (u : Fin (l + 1) → Fin n → F) (x : Fin n) :
    (curveParamPoly u x).natDegree ≤ l := by
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin (l + 1))))
    (f := fun i : Fin (l + 1) => Polynomial.C (u i x) * Polynomial.X ^ (i : ℕ)) (n := l) ?_
  intro i _
  rw [mul_comm (Polynomial.C (u i x))]
  exact (Polynomial.natDegree_mul_C_le (Polynomial.X ^ (i : ℕ)) (u i x)).trans
    ((Polynomial.natDegree_X_pow (R := F) (n := (i : ℕ))).trans_le (Nat.lt_succ_iff.1 i.isLt))

/-! ## The curve Berlekamp–Welch matrix -/

/-- The "curve Berlekamp–Welch matrix": its first `e + 1` columns carry `p_x` times powers of the
evaluation point, its remaining `e + deg` columns carry the negative powers. The entries live in
`F[Y]`; evaluating `Y` at a good parameter `z` produces the classical BW matrix for the word
`u(z)`. -/
noncomputable def curveBWMatrix {l : ℕ} (e deg : ℕ) (domain : Fin n ↪ F)
    (u : Fin (l + 1) → Fin n → F) : Matrix (Fin n) (Fin ((e + 1) + (e + deg))) (Polynomial F) :=
  Matrix.of fun x j =>
    if (j : ℕ) < e + 1 then curveParamPoly u x * (Polynomial.C (domain x)) ^ (j : ℕ)
    else - (Polynomial.C (domain x)) ^ ((j : ℕ) - (e + 1))

lemma curveBWMatrix_entry_natDegree_le {l : ℕ} (e deg : ℕ) (domain : Fin n ↪ F)
    (u : Fin (l + 1) → Fin n → F) (x : Fin n) (j : Fin ((e + 1) + (e + deg))) :
    (curveBWMatrix e deg domain u x j).natDegree ≤ if (j : ℕ) ≤ e then l else 0 := by
  classical
  rw [curveBWMatrix, Matrix.of_apply]
  by_cases hj : (j : ℕ) < e + 1
  · rw [ite_eq_left hj, ite_eq_left (by omega)]
    rw [← Polynomial.C_pow]
    exact (Polynomial.natDegree_mul_C_le (curveParamPoly u x) (domain x ^ (j : ℕ))).trans
      (curveParamPoly_natDegree_le u x)
  · rw [ite_eq_right hj, ite_eq_right (by omega)]
    simp

lemma curveBWMatrix_map_eval {l : ℕ} (e deg : ℕ) (domain : Fin n ↪ F)
    (u : Fin (l + 1) → Fin n → F) (z : F) :
    (curveBWMatrix e deg domain u).map (Polynomial.evalRingHom z) =
      BW_homMatrix (ι := Fin n) e deg (fun x => domain x)
        (fun x => (curveParamPoly u x).eval z) := by
  classical
  ext x j
  simp only [Matrix.map_apply, curveBWMatrix, BW_homMatrix, Matrix.of_apply]
  by_cases hj : (j : ℕ) < e + 1 <;> simp only [hj, ↓reduceIte, Polynomial.coe_evalRingHom,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C]

lemma curveBWMatrix_det_submatrix_natDegree_le {l : ℕ} (e deg : ℕ) (domain : Fin n ↪ F)
    (u : Fin (l + 1) → Fin n → F) (r : Fin ((e + 1) + (e + deg)) → Fin n) :
    (Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)).natDegree ≤ l * (e + 1) := by
  classical
  have h := natDegree_det_le_sum_of_natDegree_le
    ((curveBWMatrix e deg domain u).submatrix r id) (fun j => if (j : ℕ) ≤ e then l else 0)
    (fun i j => curveBWMatrix_entry_natDegree_le e deg domain u (r i) j)
  refine h.trans_eq ?_
  have hsum : (∑ j : Fin ((e + 1) + (e + deg)), (if (j : ℕ) ≤ e then l else 0)) =
      l * (e + 1) := by
    have h1 : (∑ j : Fin ((e + 1) + (e + deg)), (if (j : ℕ) ≤ e then l else 0))
        = ∑ _j ∈ (Finset.univ.filter (fun j : Fin ((e + 1) + (e + deg)) => (j : ℕ) ≤ e)), l := by
      rw [Finset.sum_filter]
    rw [h1, Finset.sum_const, Fin_sum_ite_lt_e_add_one, smul_eq_mul, mul_comm]
  rw [hsum]

/-! ## Local data at a good parameter -/

/-- A word that is `δ`-close to a Reed–Solomon code is given by a polynomial of degree `< deg`
except on at most `⌊δ * n⌋` positions. -/
lemma exists_close_poly [NeZero n] [DecidableEq F] {deg : ℕ} [NeZero deg] {domain : Fin n ↪ F}
    {δ : ℝ≥0} {w : Fin n → F}
    (hw : δᵣ(w, (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ) :
    ∃ (q : Polynomial F) (B : Finset (Fin n)), q.natDegree < deg ∧
      B.card ≤ Nat.floor (δ * n) ∧ ∀ x, x ∉ B → w x = q.eval (domain x) := by
  classical
  obtain ⟨v, hv, hvw⟩ :=
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (u := w)
      (C := (ReedSolomon.code domain deg : Set (Fin n → F))) (δ := δ)).1 hw
  obtain ⟨q, hq, hqv⟩ := hv
  obtain ⟨B, hBcard, hBagree⟩ :=
    (Code.relCloseToWord_iff_exists_possibleDisagreeCols (u := w) (v := v) (δ := δ)).1 hvw
  refine ⟨q, B, ReedSolomon.natDegree_lt_of_mem_degreeLT hq, ?_, ?_⟩
  · simpa using hBcard
  · intro x hx
    rw [hBagree x hx]
    have := congrFun hqv x
    simpa [ReedSolomon.evalOnPoints] using this.symm

/-- The Berlekamp–Welch error locator at a good parameter: a nonzero solution of the curve BW
system. -/
lemma exists_local_kernel [NeZero n] [DecidableEq F] {l deg : ℕ} [NeZero deg] (hdeg : 0 < deg)
    {domain : Fin n ↪ F}
    {δ : ℝ≥0} {u : Fin (l + 1) → Fin n → F} {z : F}
    (hz : δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
      (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ) :
    ∃ (a : Fin (Nat.floor (δ * n) + 1) → F) (b : Fin (Nat.floor (δ * n) + deg) → F),
      a ≠ 0 ∧
        Matrix.mulVec
          (BW_homMatrix (ι := Fin n) (Nat.floor (δ * n)) deg (fun x => domain x)
            (fun x => (curveParamPoly u x).eval z)) (Fin.append a b) = 0 := by
  classical
  set e : ℕ := Nat.floor (δ * n) with he
  obtain ⟨q, B, hqdeg, hBcard, hBagree⟩ := exists_close_poly (deg := deg) (domain := domain) hz
  have hBcard' : B.card ≤ e := by simpa [he] using hBcard
  set E : Polynomial F := ∏ x ∈ B, (Polynomial.X - Polynomial.C (domain x)) with hE
  set Q : Polynomial F := E * q with hQ
  have hE_ne : E ≠ 0 := by
    rw [hE]
    exact Finset.prod_ne_zero_iff.2 fun x _ => (Polynomial.monic_X_sub_C (domain x)).ne_zero
  have hE_natDegree : E.natDegree = B.card := by
    rw [hE, Polynomial.natDegree_prod_of_monic (s := B)
      (f := fun x : Fin n => (Polynomial.X - Polynomial.C (domain x) : Polynomial F))
      (fun x _ => Polynomial.monic_X_sub_C (domain x))]
    simp
  have hE_le : E.natDegree ≤ e := by rw [hE_natDegree]; exact hBcard'
  have hQ_natDegree : Q.natDegree < e + deg := by
    have h1 : Q.natDegree ≤ E.natDegree + q.natDegree := Polynomial.natDegree_mul_le
    have h2 : q.natDegree ≤ deg - 1 := by omega
    omega
  have hE_eval_mem : ∀ x ∈ B, E.eval (domain x) = 0 := by
    intro x hx
    rw [hE]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have hE_eval_notmem : ∀ x, x ∉ B → E.eval (domain x) ≠ 0 := by
    intro x hx
    rw [hE]
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun y hy => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro hxy
    exact hx (by rwa [← domain.injective hxy] at hy)
  refine ⟨fun t => E.coeff (t : ℕ), fun s => Q.coeff (s : ℕ), ?_, ?_⟩
  · intro ha
    have hEc : E = 0 := by
      ext k
      by_cases hk : k < e + 1
      · have := congrFun ha ⟨k, hk⟩
        simpa using this
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show E.natDegree < k by omega)]
        simp
    exact hE_ne hEc
  · refine (BW_homMatrix_mulVec_eq_zero_iff (ι := Fin n) (R := F) e deg (fun x => domain x)
      (fun x => (curveParamPoly u x).eval z) _ _).2 ?_
    intro x
    have ha_eval : (∑ t : Fin (e + 1), E.coeff (t : ℕ) * (domain x) ^ (t : ℕ)) =
        E.eval (domain x) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => E.coeff k * (domain x) ^ k) (e + 1)]
      exact (Polynomial.eval_eq_sum_range' (p := E) (by omega) (domain x)).symm
    have hb_eval : (∑ s : Fin (e + deg), Q.coeff (s : ℕ) * (domain x) ^ (s : ℕ)) =
        Q.eval (domain x) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => Q.coeff k * (domain x) ^ k) (e + deg)]
      exact (Polynomial.eval_eq_sum_range' (p := Q) hQ_natDegree (domain x)).symm
    rw [ha_eval, hb_eval, hQ, Polynomial.eval_mul]
    rw [curveParamPoly_eval]
    by_cases hxB : x ∈ B
    · rw [hE_eval_mem x hxB, zero_mul, zero_mul]
    · rw [hBagree x hxB]

/-! ## Vanishing of all maximal minors of the symbolic matrix -/

/-- At a good parameter the evaluated BW matrix has a nonzero kernel vector, hence every maximal
minor of the symbolic matrix vanishes there. Root counting then makes every maximal minor vanish
identically, since its degree `l * (e + 1)` is smaller than `|S|`. -/
lemma curveBWMatrix_det_submatrix_eq_zero [NeZero n] [DecidableEq F] {l deg : ℕ} [NeZero deg]
    (hdeg : 0 < deg)
    {domain : Fin n ↪ F} {δ : ℝ≥0} {u : Fin (l + 1) → Fin n → F} {S : Finset F}
    (he1 : Nat.floor (δ * n) + 1 ≤ n) (hScard : l * n < S.card)
    (hSgood : ∀ z ∈ S, δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
      (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ) :
    ∀ r : Fin ((Nat.floor (δ * n) + 1) + (Nat.floor (δ * n) + deg)) → Fin n,
      Matrix.det ((curveBWMatrix (Nat.floor (δ * n)) deg domain u).submatrix r id) = 0 := by
  classical
  set e : ℕ := Nat.floor (δ * n) with he
  intro r
  have hdeg_le : (Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)).natDegree ≤
      l * (e + 1) := curveBWMatrix_det_submatrix_natDegree_le e deg domain u r
  have hvan : ∀ z ∈ S, (Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)).eval z = 0 := by
    intro z hz
    have hmapdet : (Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)).eval z =
        Matrix.det
          (((curveBWMatrix e deg domain u).submatrix r id).map (Polynomial.evalRingHom z)) :=
      RingHom.map_det (Polynomial.evalRingHom z) _
    rw [hmapdet]
    rw [← Matrix.submatrix_map]
    by_cases hinj : Function.Injective r
    · obtain ⟨a, b, ha, hmul⟩ :=
        exists_local_kernel (l := l) (deg := deg) hdeg (domain := domain) (u := u) (z := z)
          (by simpa [he] using hSgood z hz)
      have hmul' : Matrix.mulVec
          ((curveBWMatrix e deg domain u).map (Polynomial.evalRingHom z)) (Fin.append a b) = 0 := by
        rw [curveBWMatrix_map_eval]
        exact hmul
      set v : Fin ((e + 1) + (e + deg)) → F := Fin.append a b with hv
      have hvne : v ≠ 0 := by
        intro h0
        apply ha
        funext t
        have := congrFun h0 (Fin.castAdd (e + deg) t)
        simpa [v] using this
      have hker :
          (((curveBWMatrix e deg domain u).map (Polynomial.evalRingHom z)).submatrix r id).mulVec v
            = 0 := by
        funext i
        have := congrFun hmul' (r i)
        simpa [v, Matrix.mulVec, Matrix.submatrix, dotProduct] using this
      exact (Matrix.exists_mulVec_eq_zero_iff
        (M := ((curveBWMatrix e deg domain u).map (Polynomial.evalRingHom z)).submatrix r id)).1
        ⟨v, hvne, hker⟩
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hinj
      have hrow :
          (((curveBWMatrix e deg domain u).submatrix r id).map (Polynomial.evalRingHom z)) i =
          (((curveBWMatrix e deg domain u).submatrix r id).map (Polynomial.evalRingHom z)) j := by
        funext k
        simp [Matrix.submatrix, Matrix.map_apply, hij]
      exact Matrix.det_zero_of_row_eq hne hrow
  have hcard : (Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)).natDegree < S.card := by
    have h1 : l * (e + 1) ≤ l * n := Nat.mul_le_mul_left l he1
    omega
  have hmain := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (p := Matrix.det ((curveBWMatrix e deg domain u).submatrix r id)) (s := S) hvan hcard
  simpa only [e] using hmain

/-! ## A kernel vector with degree bounds -/

/-- If all maximal minors of an `ι × (e+1)` polynomial matrix vanish and its entries have degree at
most `d`, then it has a nonzero kernel vector of degree at most `d * e`. -/
theorem exists_nonzero_kernelVec_of_det_submatrix_eq_zero {ι : Type*} [Fintype ι]
    (e d : ℕ) (K : Matrix ι (Fin (e + 1)) (Polynomial F))
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ d)
    (hdet : ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → Polynomial F,
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ d * e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ (0 : Polynomial F)
  let : DecidablePred P := Classical.decPred _
  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0
  rcases Pr with ⟨I, J, hdetIJ⟩
  have hnotPn : ¬ P n := by
    intro hPn
    rcases hPn with ⟨I0, J0, hdet0⟩
    let A : Matrix (Fin n) (Fin n) (Polynomial F) := K.submatrix I0 id
    have hdetA : Matrix.det A = 0 := by
      simpa [A] using hdet I0
    have hdet_sub : Matrix.det (A.submatrix (Function.Embedding.refl _) J0) = 0 :=
      RS_det_submatrix_eq_zero_of_det_eq_zero n A hdetA (Function.Embedding.refl _) J0
    have hdetK : Matrix.det (K.submatrix I0 J0) = 0 := by
      have hmatrix : K.submatrix I0 J0 = A.submatrix (Function.Embedding.refl _) J0 := by
        ext i j
        rfl
      rw [hmatrix]
      exact hdet_sub
    exact hdet0 hdetK
  have hrle : r ≤ n := Nat.findGreatest_le (P := P) n
  have hrne : r ≠ n := by
    intro hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hre |>.2.1
    exact hnotPn (hcond (Nat.succ_ne_zero e))
  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := Nat.lt_succ_iff.mp hrlt
  have hrltcard : r < Fintype.card ι := lt_of_lt_of_le hrlt (by simpa [n] using hcard)
  -- pick `i0 ∉ range I`
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    rw [Finset.card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    exact hrltcard
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    exact hi0_notmem (Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩)
  -- pick `j0 ∉ range J`
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    exact hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    exact hj0_notmem (Finset.mem_map.2 ⟨j, Finset.mem_univ _, rfl⟩)
  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial F) := K.submatrix I' J'
  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := Nat.lt_succ_self _
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb
  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    exact hnotPr1 ⟨I', J', hne⟩
  let u : Fin (r + 1) → Polynomial F := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 :=
    RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i j
    simp only [B, I', J', Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc]
  have hu_last : u (Fin.last r) =
      (-1 : Polynomial F) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) :=
    RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
  have hu_last_ne : u (Fin.last r) ≠ (0 : Polynomial F) := by
    have hsign : (-1 : Polynomial F) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : Polynomial F) :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : Polynomial F) := by
      rw [hsub_cast]
      exact hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ r * d := by
    intro t
    have hu_t : u t =
        (-1 : Polynomial F) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) :=
      RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r * d :=
      natDegree_det_le_of_entry_natDegree_le (m := r)
        (B.submatrix Fin.castSucc t.succAbove) fun i j =>
          hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdeg_sign : ((-1 : Polynomial F) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow, Polynomial.natDegree_C]
    rw [hu_t]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [hdeg_sign, zero_add]
    exact hdeg_det
  let a : Fin n → Polynomial F := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := fun t =>
    J'.injective.extend_apply u (fun _ => 0) t
  have ha_off : ∀ j : Fin n, (¬∃ t : Fin (r + 1), J' t = j) → a j = 0 := fun j hj =>
    Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0) j hj
  have ha_ne : a ≠ 0 := fun ha0 =>
    hu_last_ne ((ha_on (Fin.last r)).symm.trans (congrFun ha0 (J' (Fin.last r))))
  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ d * e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      rw [ha_on t]
      exact (hdeg_u t).trans (by
        rw [Nat.mul_comm (r) d]
        exact Nat.mul_le_mul_left d hrle_e)
    · rw [ha_off j hj, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        rw [ha_off j hj, mul_zero]
      · intro t
        rw [ha_on t]
    change (∑ j, K i j * a j) = ∑ t, K i (J' t) * u t
    exact hsum.symm
  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (∑ x, B (Fin.castSucc t) x * u x) = 0 := congrFun hBu (Fin.castSucc t)
      simp only [B, I', Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc] at hrow
      exact (hmul_formula (I t)).trans hrow
    · have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        exact hnotPr1 ⟨Ii, J', hne⟩
      let b : Fin (r + 1) → Polynomial F := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · simp only [Matrix.updateRow_apply, ite_eq_left, b, Matrix.submatrix_apply, Ii,
            Fin.Embedding.snoc_last]
        · intro x
          simp only [Matrix.updateRow_apply, Fin.castSucc_ne_last, ite_false, B, I', Ii,
            Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc]
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        rw [hupdate]
        exact hdetBi
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 :=
        (det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)).symm.trans
          hdet_update
      exact (hmul_formula i).trans hsum0
  exact ⟨a, ha_ne, hdeg_a, hmulVec⟩

/-! ## The Schur complement: a kernel vector over `F[Y]` with degree bounds -/

open Matrix in
/-- The curve BW matrix has a nonzero kernel vector over `F[Y]` whose first block has degree at
most `l * e` and whose second block has degree at most `l * (e + 1)`.

The proof eliminates the constant Vandermonde block `D` (the second block restricted to `e + deg`
rows), which is invertible over `F[Y]` because its entries are constants and its determinant is a
product of distinct differences. -/
lemma exists_kernelVec_curveBWMatrix {l deg : ℕ} [NeZero deg] {domain : Fin n ↪ F}
    {u : Fin (l + 1) → Fin n → F} (e : ℕ)
    (hcardn : e + deg ≤ n) (hcardm : e + 1 ≤ n)
    (hdets : ∀ r : Fin ((e + 1) + (e + deg)) → Fin n,
      Matrix.det ((curveBWMatrix (l := l) e deg domain u).submatrix r id) = 0) :
    ∃ (a : Fin (e + 1) → Polynomial F) (b : Fin (e + deg) → Polynomial F),
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ l * e) ∧ (∀ s, (b s).natDegree ≤ l * (e + 1)) ∧
      Matrix.mulVec (curveBWMatrix (l := l) e deg domain u) (Fin.append a b) = 0 := by
  classical
  let M : Matrix (Fin n) (Fin ((e + 1) + (e + deg))) (Polynomial F) :=
    curveBWMatrix e deg domain u
  have hdetM : ∀ r : Fin ((e + 1) + (e + deg)) → Fin n, Matrix.det (M.submatrix r id) = 0 :=
    fun r => hdets r
  have hcard_n₂ : e + deg ≤ Fintype.card (Fin n) := by simpa using hcardn
  obtain ⟨rB⟩ : Nonempty (Fin (e + deg) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcardn)
  let cL : Fin (e + 1) → Fin ((e + 1) + (e + deg)) := fun j => Fin.castAdd (e + deg) j
  let cR : Fin (e + deg) → Fin ((e + 1) + (e + deg)) := fun j => Fin.natAdd (e + 1) j
  let L : Matrix (Fin n) (Fin (e + 1)) (Polynomial F) := M.submatrix id cL
  let R : Matrix (Fin n) (Fin (e + deg)) (Polynomial F) := M.submatrix id cR
  let A21 : Matrix (Fin (e + deg)) (Fin (e + 1)) (Polynomial F) := M.submatrix rB cL
  let D : Matrix (Fin (e + deg)) (Fin (e + deg)) (Polynomial F) := M.submatrix rB cR
  have hD : D = -Matrix.vandermonde
      (fun i : Fin (e + deg) => (Polynomial.C (domain (rB i)) : Polynomial F)) := by
    funext i j
    have hj' : ¬ e + 1 + (j : ℕ) ≤ e := by omega
    simp [D, M, curveBWMatrix, cR, Matrix.vandermonde, hj', Matrix.of_apply]
  have hvB : Function.Injective (fun i : Fin (e + deg) => domain (rB i)) := by
    intro i₁ i₂ hi
    exact rB.injective (domain.injective hi)
  have hdetD : IsUnit (Matrix.det D) := by
    have hunitNeg : IsUnit ((-1 : Polynomial F) ^ Fintype.card (Fin (e + deg))) :=
      (isUnit_neg_one).pow _
    have hdetD' : Matrix.det D = (-1 : Polynomial F) ^ Fintype.card (Fin (e + deg)) *
        Matrix.det (Matrix.vandermonde
          (fun i : Fin (e + deg) => (Polynomial.C (domain (rB i)) : Polynomial F))) := by
      rw [hD, Matrix.det_neg]
    rw [hdetD']
    exact hunitNeg.mul (RS_isUnit_det_vandermonde_C_of_injective (e + deg)
      (fun i => domain (rB i)) hvB)
  let : Invertible D := Matrix.invertibleOfIsUnitDet D hdetD
  let K0 : Matrix (Fin n) (Fin (e + 1)) (Polynomial F) := L - R * (⅟D * A21)
  have hdetK0 : ∀ rA : Fin (e + 1) → Fin n, Matrix.det (K0.submatrix rA id) = 0 := by
    intro rA
    let r : Fin ((e + 1) + (e + deg)) → Fin n := Fin.append rA rB
    have hdetA : Matrix.det (M.submatrix r id) = 0 := hdetM r
    let eSum : (Fin (e + 1) ⊕ Fin (e + deg)) ≃ Fin ((e + 1) + (e + deg)) :=
      finSumFinEquiv (m := e + 1) (n := e + deg)
    let Ablocks : Matrix (Fin (e + 1) ⊕ Fin (e + deg)) (Fin (e + 1) ⊕ Fin (e + deg))
        (Polynomial F) := (M.submatrix r id).submatrix eSum eSum
    have hdetAblocks : Matrix.det Ablocks = 0 := by
      have hdetEq : Matrix.det Ablocks = Matrix.det (M.submatrix r id) := by
        simpa [Ablocks] using (Matrix.det_submatrix_equiv_self (e := eSum) (M.submatrix r id))
      simpa [hdetEq] using hdetA
    have hAblocks_eq :
        Ablocks = Matrix.fromBlocks (L.submatrix rA id) (R.submatrix rA id) A21 D := by
      funext i j
      cases i <;> cases j <;>
        simp (config := { zeta := true })
          [Ablocks, eSum, L, R, A21, D, r, cL, cR, Matrix.fromBlocks, M, curveBWMatrix,
            Matrix.submatrix, Fin.append]
    have hmul : Matrix.det D * Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)
        = 0 := by
      have hformula := (Matrix.det_fromBlocks₂₂ (A := L.submatrix rA id) (B := R.submatrix rA id)
        (C := A21) (D := D))
      simpa [hAblocks_eq, hformula, Matrix.mul_assoc] using hdetAblocks
    have hdetSchur : Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) = 0 :=
      (IsUnit.mul_right_eq_zero (a := Matrix.det D)
        (b := Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)) hdetD).1 hmul
    change ((L - R * (⅟D * A21)).submatrix rA id).det = 0
    have hmatrix : (L - R * (⅟D * A21)).submatrix rA id =
        L.submatrix rA id - R.submatrix rA id * (⅟D * A21) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hmatrix]
    simpa only [Matrix.mul_assoc] using hdetSchur
  have hdegL : ∀ i j, (L i j).natDegree ≤ l := by
    intro i j
    have h := curveBWMatrix_entry_natDegree_le (l := l) e deg domain u i (cL j)
    rw [ite_eq_left (show (cL j : ℕ) ≤ e by simpa [cL] using Nat.lt_succ_iff.1 j.isLt)] at h
    simpa [L, M] using h
  have hdegA21 : ∀ i j, (A21 i j).natDegree ≤ l := by
    intro i j
    have h := curveBWMatrix_entry_natDegree_le (l := l) e deg domain u (rB i) (cL j)
    rw [ite_eq_left (show (cL j : ℕ) ≤ e by simpa [cL] using Nat.lt_succ_iff.1 j.isLt)] at h
    simpa [A21, M] using h
  have hdegR0 : ∀ i j, (R i j).natDegree = 0 := by
    intro i j
    have hval : ((Fin.natAdd (e + 1) (j : Fin (e + deg))) : ℕ) = e + 1 + (j : ℕ) := rfl
    have hR : R i j = - (Polynomial.C (domain i)) ^ (j : ℕ) := by
      simp only [R, M, curveBWMatrix, Matrix.submatrix_apply, id_eq, Matrix.of_apply, cR, hval]
      rw [ite_eq_right (show ¬ (e + 1 + (j : ℕ) < e + 1) by omega)]
      rw [Nat.add_sub_cancel_left]
    rw [hR]
    simp
  have hdegInvD0 : ∀ i j : Fin (e + deg), ((D⁻¹) i j).natDegree = 0 := by
    intro i j
    simpa [hD] using RS_natDegree_inv_neg_vandermonde_C_eq_zero (e + deg)
      (fun i => domain (rB i)) hvB i j
  have hdegInvDA21 : ∀ i j, ((⅟D * A21) i j).natDegree ≤ l := by
    intro i j
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (e + deg))),
        ((⅟D i k) * (A21 k j)).natDegree ≤ l := by
      intro k _
      have hInv' : ((D⁻¹) i k).natDegree = 0 := hdegInvD0 i k
      have hinv : (⅟D i k).natDegree = 0 := by
        rw [Matrix.invOf_eq_nonsing_inv]
        exact hInv'
      calc ((⅟D i k) * (A21 k j)).natDegree
          ≤ (⅟D i k).natDegree + (A21 k j).natDegree := Polynomial.natDegree_mul_le
        _ = (A21 k j).natDegree := by rw [hinv, Nat.zero_add]
        _ ≤ l := hdegA21 k j
    have hsum := Polynomial.natDegree_sum_le_of_forall_le
      (s := (Finset.univ : Finset (Fin (e + deg)))) (n := l)
      (f := fun k : Fin (e + deg) => (⅟D i k) * (A21 k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegRInvDA21 : ∀ i j, ((R * (⅟D * A21)) i j).natDegree ≤ l := by
    intro i j
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (e + deg))),
        (R i k * ((⅟D * A21) k j)).natDegree ≤ l := by
      intro k _
      have hR : (R i k).natDegree = 0 := hdegR0 i k
      calc (R i k * ((⅟D * A21) k j)).natDegree
          ≤ (R i k).natDegree + ((⅟D * A21) k j).natDegree := Polynomial.natDegree_mul_le
        _ = ((⅟D * A21) k j).natDegree := by rw [hR, Nat.zero_add]
        _ ≤ l := hdegInvDA21 k j
    have hsum := Polynomial.natDegree_sum_le_of_forall_le
      (s := (Finset.univ : Finset (Fin (e + deg)))) (n := l)
      (f := fun k : Fin (e + deg) => R i k * ((⅟D * A21) k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegK0 : ∀ i j, (K0 i j).natDegree ≤ l := by
    intro i j
    have h := Polynomial.natDegree_sub_le (L i j) ((R * (⅟D * A21)) i j)
    exact h.trans (max_le (hdegL i j) (hdegRInvDA21 i j))
  obtain ⟨a, ha0, ha_deg, haKer⟩ :=
    exists_nonzero_kernelVec_of_det_submatrix_eq_zero (e := e) (d := l) K0
      (by simpa using hcardm) hdegK0 (by intro rA; simpa [K0] using hdetK0 rA)
  let b : Fin (e + deg) → Polynomial F := -(⅟D).mulVec (A21.mulVec a)
  have hdegA21mulVec : ∀ i : Fin (e + deg), ((A21.mulVec a) i).natDegree ≤ l * e + l := by
    intro i
    have hterm : ∀ t ∈ (Finset.univ : Finset (Fin (e + 1))),
        (A21 i t * a t).natDegree ≤ l * e + l := by
      intro t _
      have hA : (A21 i t).natDegree ≤ l := hdegA21 i t
      have ha : (a t).natDegree ≤ l * e := ha_deg t
      calc (A21 i t * a t).natDegree
          ≤ (A21 i t).natDegree + (a t).natDegree := Polynomial.natDegree_mul_le
        _ ≤ l + l * e := Nat.add_le_add hA ha
        _ = l * e + l := by rw [Nat.add_comm]
    have hsum := Polynomial.natDegree_sum_le_of_forall_le
      (s := (Finset.univ : Finset (Fin (e + 1)))) (n := l * e + l)
      (f := fun t : Fin (e + 1) => A21 i t * a t) hterm
    simpa [Matrix.mulVec, dotProduct] using hsum
  have hdegb : ∀ s : Fin (e + deg), (b s).natDegree ≤ l * (e + 1) := by
    intro s
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (e + deg))),
        ((⅟D s k) * (A21.mulVec a k)).natDegree ≤ l * e + l := by
      intro k _
      have hInv' : ((D⁻¹) s k).natDegree = 0 := hdegInvD0 s k
      have hinv : (⅟D s k).natDegree = 0 := by
        rw [Matrix.invOf_eq_nonsing_inv]
        exact hInv'
      calc ((⅟D s k) * (A21.mulVec a k)).natDegree
          ≤ (⅟D s k).natDegree + (A21.mulVec a k).natDegree := Polynomial.natDegree_mul_le
        _ = (A21.mulVec a k).natDegree := by rw [hinv, Nat.zero_add]
        _ ≤ l * e + l := hdegA21mulVec k
    have hsum : (∑ k : Fin (e + deg), (⅟D s k) * (A21.mulVec a k)).natDegree ≤ l * e + l :=
      Polynomial.natDegree_sum_le_of_forall_le
        (s := (Finset.univ : Finset (Fin (e + deg)))) (n := l * e + l)
        (f := fun k : Fin (e + deg) => (⅟D s k) * (A21.mulVec a k)) hterm
    have hb : b s = -(∑ k : Fin (e + deg), (⅟D s k) * (A21.mulVec a k)) := rfl
    rw [hb, Polynomial.natDegree_neg]
    refine hsum.trans_eq ?_
    rw [Nat.mul_add, Nat.mul_one]
  have hRb : Matrix.mulVec R b = -Matrix.mulVec (R * (⅟D * A21)) a := by
    ext i
    simp only [b, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Pi.neg_apply]
  have hLR : Matrix.mulVec L a + Matrix.mulVec R b = 0 := by
    have haKer' : Matrix.mulVec (L - R * (⅟D * A21)) a = 0 := by
      simpa [K0] using haKer
    have haKer'' : Matrix.mulVec L a - Matrix.mulVec (R * (⅟D * A21)) a = 0 := by
      simpa [Matrix.sub_mulVec] using haKer'
    rw [hRb]
    simpa [sub_eq_add_neg, add_comm] using haKer''
  refine ⟨a, b, ha0, ha_deg, hdegb, ?_⟩
  have hsplit : Matrix.mulVec M (Fin.append a b) = Matrix.mulVec L a + Matrix.mulVec R b := by
    simpa [L, R, cL, cR] using
      (RS_mulVec_append_castAdd_natAdd (ι := Fin n) (R := Polynomial F) (e + 1) (e + deg) M a b)
  rw [hsplit]
  exact hLR

/-! ## Assembling the bivariate polynomials -/

/-- The bivariate polynomial `A(X, Y) = ∑ t, a t (Y) * X^t` attached to a vector of coefficient
polynomials in the curve parameter. -/
noncomputable def bivariateOf {m : ℕ} (a : Fin m → Polynomial F) : Polynomial (Polynomial F) :=
  Polynomial.Bivariate.swap (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t))

lemma coeff_sum_monomial {m : ℕ} (a : Fin m → Polynomial F) (k : ℕ) :
    (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t)).coeff k =
      if h : k < m then a ⟨k, h⟩ else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < m
  · have hsingle : ∀ t ∈ (Finset.univ : Finset (Fin m)), t ≠ ⟨k, hk⟩ →
        (Polynomial.monomial (t : ℕ) (a t)).coeff k = 0 := by
      intro t _ ht
      simp only [Polynomial.coeff_monomial]
      rw [ite_eq_right]
      intro h
      exact ht (Fin.ext h)
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin m) hsingle (by simp), dite_eq_left hk]
    simp
  · rw [dite_eq_right hk]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [Polynomial.coeff_monomial]
    rw [ite_eq_right]
    intro h
    exact hk (h ▸ t.isLt)

lemma natDegree_sum_monomial_le {m : ℕ} (a : Fin m → Polynomial F) :
    (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t)).natDegree ≤ m - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := m - 1)
    (f := fun t : Fin m => Polynomial.monomial (t : ℕ) (a t)) ?_
  intro t _
  exact (Polynomial.natDegree_monomial_le (a t)).trans (by omega)

lemma degreeX_bivariateOf_le {m : ℕ} (a : Fin m → Polynomial F) :
    Polynomial.Bivariate.degreeX (bivariateOf a) ≤ m - 1 := by
  rw [bivariateOf, Polynomial.Bivariate.degreeX_swap, Polynomial.Bivariate.natDegreeY]
  exact natDegree_sum_monomial_le a

lemma natDegreeY_bivariateOf_le {m d : ℕ} (a : Fin m → Polynomial F)
    (h : ∀ t, (a t).natDegree ≤ d) :
    Polynomial.Bivariate.natDegreeY (bivariateOf a) ≤ d := by
  rw [bivariateOf, Polynomial.Bivariate.natDegreeY_swap, Polynomial.Bivariate.degreeX]
  refine Finset.sup_le fun k _ => ?_
  rw [coeff_sum_monomial]
  split_ifs with hk
  · exact h _
  · simp

lemma Bivariate_swap_swap (f : Polynomial (Polynomial F)) :
    Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f) = f := by
  simpa using (Polynomial.Bivariate.swap (R := F)).left_inv f

lemma bivariateOf_ne_zero {m : ℕ} {a : Fin m → Polynomial F} (ha : a ≠ 0) :
    bivariateOf a ≠ 0 := by
  intro h
  apply ha
  funext t
  have hsw : Polynomial.Bivariate.swap (∑ s : Fin m, Polynomial.monomial (s : ℕ) (a s)) = 0 := by
    have h2 : bivariateOf a = 0 := h
    rwa [bivariateOf] at h2
  have hA0 : (∑ s : Fin m, Polynomial.monomial (s : ℕ) (a s)) = 0 := by
    calc (∑ s : Fin m, Polynomial.monomial (s : ℕ) (a s))
        = Polynomial.Bivariate.swap
            (Polynomial.Bivariate.swap (∑ s : Fin m, Polynomial.monomial (s : ℕ) (a s))) :=
          (Bivariate_swap_swap _).symm
      _ = Polynomial.Bivariate.swap 0 := by rw [hsw]
      _ = 0 := by simp
  have hcoeff := congrArg (fun f : Polynomial (Polynomial F) => f.coeff (t : ℕ)) hA0
  rw [coeff_sum_monomial, dite_eq_left t.isLt] at hcoeff
  simpa using hcoeff

lemma evalX_bivariateOf {m : ℕ} (a : Fin m → Polynomial F) (x : F) :
    Polynomial.Bivariate.evalX x (bivariateOf a) =
      ∑ t : Fin m, a t * (Polynomial.C x) ^ (t : ℕ) := by
  have h1 : Polynomial.Bivariate.evalX x (bivariateOf a) =
      Polynomial.Bivariate.evalY x (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t)) := by
    rw [bivariateOf]
    exact (Polynomial.Bivariate.evalY_eq_evalX_swap x _).symm
  rw [h1, Polynomial.Bivariate.evalY, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun t _ => Polynomial.eval_monomial

lemma evalY_bivariateOf {m : ℕ} (a : Fin m → Polynomial F) (z : F) :
    Polynomial.Bivariate.evalY z (bivariateOf a) =
      ∑ t : Fin m, Polynomial.C ((a t).eval z) * Polynomial.X ^ (t : ℕ) := by
  have hss : Polynomial.Bivariate.swap
      (Polynomial.Bivariate.swap (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t)))
      = ∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t) := by
    simpa using (Polynomial.Bivariate.swap (R := F)).left_inv
      (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t))
  have h1 : Polynomial.Bivariate.evalY z (bivariateOf a) =
      Polynomial.Bivariate.evalX z (∑ t : Fin m, Polynomial.monomial (t : ℕ) (a t)) := by
    rw [bivariateOf, Polynomial.Bivariate.evalY_eq_evalX_swap, hss]
  rw [h1, Polynomial.Bivariate.evalX_eq_map, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, Polynomial.C_mul_X_pow_eq_monomial]

lemma evalX_eval_eq_evalY_eval (x z : F) (f : Polynomial (Polynomial F)) :
    (Polynomial.Bivariate.evalX x f).eval z = (Polynomial.Bivariate.evalY z f).eval x := by
  calc (Polynomial.Bivariate.evalX x f).eval z
      = (f.map (Polynomial.evalRingHom x)).eval z := by
          rw [Polynomial.Bivariate.evalX_eq_map]
    _ = f.eval₂ (Polynomial.evalRingHom x) z := by
          simpa using (Polynomial.eval_map (f := Polynomial.evalRingHom x) (p := f) (x := z))
    _ = (Polynomial.eval (Polynomial.C z) f).eval x := by
          simpa [Polynomial.Bivariate.evalY] using
            (Polynomial.eval₂_at_apply (p := f) (f := Polynomial.evalRingHom x)
              (r := Polynomial.C z))
    _ = (Polynomial.Bivariate.evalY z f).eval x := by simp [Polynomial.Bivariate.evalY]

/-! ## The kernel identity in coordinate form -/

lemma mulVec_curveBWMatrix_eq_zero_iff {l : ℕ} (e deg : ℕ) (domain : Fin n ↪ F)
    (u : Fin (l + 1) → Fin n → F) (a : Fin (e + 1) → Polynomial F)
    (b : Fin (e + deg) → Polynomial F) :
    Matrix.mulVec (curveBWMatrix (l := l) e deg domain u) (Fin.append a b) = 0 ↔
      ∀ x : Fin n,
        (∑ t : Fin (e + 1), a t * (Polynomial.C (domain x)) ^ (t : ℕ)) * curveParamPoly u x =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain x)) ^ (s : ℕ) := by
  have h : curveBWMatrix (l := l) e deg domain u =
      BW_homMatrix (ι := Fin n) e deg (fun x => Polynomial.C (domain x))
        (fun x => curveParamPoly u x) := rfl
  rw [h]
  exact BW_homMatrix_mulVec_eq_zero_iff (ι := Fin n) (R := Polynomial F) e deg
    (fun x => Polynomial.C (domain x)) (fun x => curveParamPoly u x) a b

/-! ## Column and row relations -/

lemma curveBivariate_column {l e deg : ℕ} {domain : Fin n ↪ F} {u : Fin (l + 1) → Fin n → F}
    {a : Fin (e + 1) → Polynomial F} {b : Fin (e + deg) → Polynomial F}
    (hker : ∀ x : Fin n,
      (∑ t : Fin (e + 1), a t * (Polynomial.C (domain x)) ^ (t : ℕ)) * curveParamPoly u x =
        ∑ s : Fin (e + deg), b s * (Polynomial.C (domain x)) ^ (s : ℕ)) :
    ∀ x : Fin n, Polynomial.Bivariate.evalX (domain x) (bivariateOf b) =
      curveParamPoly u x * Polynomial.Bivariate.evalX (domain x) (bivariateOf a) := by
  intro x
  rw [evalX_bivariateOf, evalX_bivariateOf, mul_comm (curveParamPoly u x), hker x]

lemma curveBivariate_row {l e deg : ℕ} (hdeg : 0 < deg) {domain : Fin n ↪ F}
    {u : Fin (l + 1) → Fin n → F} {a : Fin (e + 1) → Polynomial F}
    {b : Fin (e + deg) → Polynomial F}
    (hcol : ∀ x : Fin n, Polynomial.Bivariate.evalX (domain x) (bivariateOf b) =
      curveParamPoly u x * Polynomial.Bivariate.evalX (domain x) (bivariateOf a))
    {z : F} {q : Polynomial F} {B : Finset (Fin n)} (hqdeg : q.natDegree < deg)
    (hBcard : B.card ≤ e) (he2 : 2 * e + deg ≤ n)
    (hagree : ∀ x, x ∉ B → (curveParamPoly u x).eval z = q.eval (domain x)) :
    Polynomial.Bivariate.evalY z (bivariateOf b) =
      q * Polynomial.Bivariate.evalY z (bivariateOf a) := by
  classical
  have hAdeg : (Polynomial.Bivariate.evalY z (bivariateOf a)).natDegree ≤ e := by
    rw [evalY_bivariateOf]
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := e)
      (f := fun t : Fin (e + 1) => Polynomial.C ((a t).eval z) * Polynomial.X ^ (t : ℕ)) ?_
    intro t _
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact (Polynomial.natDegree_monomial_le ((a t).eval z)).trans (Nat.lt_succ_iff.1 t.isLt)
  have hBdeg : (Polynomial.Bivariate.evalY z (bivariateOf b)).natDegree ≤ e + deg - 1 := by
    rw [evalY_bivariateOf]
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ) (n := e + deg - 1)
      (f := fun s : Fin (e + deg) => Polynomial.C ((b s).eval z) * Polynomial.X ^ (s : ℕ)) ?_
    intro s _
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact (Polynomial.natDegree_monomial_le ((b s).eval z)).trans (by omega)
  have hDdeg : (Polynomial.Bivariate.evalY z (bivariateOf b) -
      q * Polynomial.Bivariate.evalY z (bivariateOf a)).natDegree ≤ e + deg - 1 := by
    have h2 : (q * Polynomial.Bivariate.evalY z (bivariateOf a)).natDegree ≤ e + deg - 1 := by
      have h3 : q.natDegree + (Polynomial.Bivariate.evalY z (bivariateOf a)).natDegree ≤
          e + deg - 1 := by omega
      exact Polynomial.natDegree_mul_le.trans h3
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hBdeg h2)
  have hD_eval : ∀ x : Fin n, x ∉ B →
      (Polynomial.Bivariate.evalY z (bivariateOf b) -
        q * Polynomial.Bivariate.evalY z (bivariateOf a)).eval (domain x) = 0 := by
    intro x hx
    have h1 : (Polynomial.Bivariate.evalY z (bivariateOf b)).eval (domain x) =
        (Polynomial.Bivariate.evalX (domain x) (bivariateOf b)).eval z :=
      (evalX_eval_eq_evalY_eval (domain x) z (bivariateOf b)).symm
    have h2 : (Polynomial.Bivariate.evalY z (bivariateOf a)).eval (domain x) =
        (Polynomial.Bivariate.evalX (domain x) (bivariateOf a)).eval z :=
      (evalX_eval_eq_evalY_eval (domain x) z (bivariateOf a)).symm
    rw [Polynomial.eval_sub, Polynomial.eval_mul, h1, h2, hcol x, Polynomial.eval_mul,
      hagree x hx, sub_self]
  have hzero : (Polynomial.Bivariate.evalY z (bivariateOf b) -
      q * Polynomial.Bivariate.evalY z (bivariateOf a)) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (p := Polynomial.Bivariate.evalY z (bivariateOf b) -
        q * Polynomial.Bivariate.evalY z (bivariateOf a))
      (s := ((Finset.univ : Finset (Fin n)) \ B).image domain) ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hD_eval x (Finset.mem_sdiff.1 hx).2
    · rw [Finset.card_image_of_injective _ domain.injective, Finset.card_sdiff,
        Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have h1 : n - e ≤ n - B.card := Nat.sub_le_sub_left hBcard n
      omega
  exact sub_eq_zero.1 hzero

end ProximityGap.CurveBW
