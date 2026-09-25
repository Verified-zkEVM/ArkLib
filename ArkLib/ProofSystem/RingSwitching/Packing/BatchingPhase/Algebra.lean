/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.CoordinateLaws

/-!
# Algebraic correctness of tensor packing and batching

The coordinate identities are explicit proved conditions, separate from profile data.
-/

@[expose] public section

noncomputable section

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial Module TensorProduct
open Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
private lemma rows_add_apply (hCoord : CoordinateLaws P) (x y : P.A)
    (u : Fin κ → Fin 2) :
    P.decomposeRows (x+y) u = P.decomposeRows x u + P.decomposeRows y u :=
  congrFun (hCoord.rows_add x y) u

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
private lemma columns_add_apply (hCoord : CoordinateLaws P) (x y : P.A)
    (u : Fin κ → Fin 2) :
    P.decomposeColumns (x+y) u = P.decomposeColumns x u + P.decomposeColumns y u :=
  congrFun (hCoord.columns_add x y) u

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
private lemma rows_mul_apply (hCoord : CoordinateLaws P) (x y : L)
    (u : Fin κ → Fin 2) :
    P.decomposeRows (P.φ₀ x * P.φ₁ y) u = P.basis.repr x u • y := by
  simpa [Algebra.smul_def] using congrFun (hCoord.rows_mul x y) u

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
private lemma columns_mul_apply (hCoord : CoordinateLaws P) (x y : L)
    (u : Fin κ → Fin 2) :
    P.decomposeColumns (P.φ₀ x * P.φ₁ y) u = P.basis.repr y u • x := by
  simpa [Algebra.smul_def, mul_comm] using congrFun (hCoord.columns_mul x y) u


omit [NeZero κ] [NeZero ℓ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K]
  [NeZero ℓ'] in
/-- Unpacking a packed polynomial recovers the original multilinear polynomial. -/
private lemma unpack_pack_id [IsDomain K] (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ) :
    unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t) = t := by
  apply Subtype.ext
  apply (MvPolynomial.is_multilinear_eq_iff_eq_evals_zeroOne
    (p := (unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t)).val)
    (q := t.val)
    (hp := (unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t)).property)
    (hq := t.property)).2
  funext p
  unfold unpackMLE packMLE
  simp only [MvPolynomial.toEvalsZeroOne, MvPolynomial.MLE_eval_zeroOne,
    Basis.equivFun_symm_apply]
  rw [Basis.repr_sum_self]
  apply congrArg (fun x => MvPolynomial.eval x t.val)
  funext i
  by_cases h : i.val < κ
  · simp [h]
  · simp only [Fin.eta, dite_eq_right h]
    have hk : κ ≤ i.val := Nat.le_of_not_lt h
    have h_idx : (⟨i.val - κ + κ, by omega⟩ : Fin ℓ) = i := by
      apply Fin.ext
      exact Nat.sub_add_cancel hk
    rw [h_idx]

/-- Split a Boolean point into its prefix and suffix. -/
private def splitBoolPointEquiv :
    ((Fin κ → Fin 2) × (Fin ℓ' → Fin 2)) ≃ (Fin ℓ → Fin 2) where
  toFun vw := fun i =>
    if h : i.val < κ then
      vw.1 ⟨i.val, h⟩
    else
      vw.2 ⟨i.val - κ, by omega⟩
  invFun p :=
    (fun i => p ⟨i.val, by omega⟩,
      fun i => p ⟨i.val + κ, by
        rw [h_l]
        omega⟩)
  left_inv := by
    intro vw
    rcases vw with ⟨v, w⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      have hi : ¬ i.val + κ < κ := by
        omega
      simp [hi]
  right_inv := by
    intro p
    funext i
    by_cases hi : i.val < κ
    · simp [hi]
    · have hge : κ ≤ i.val := Nat.le_of_not_lt hi
      have hidx : (⟨i.val - κ + κ, by omega⟩ : Fin ℓ) = i := by
        apply Fin.ext
        exact Nat.sub_add_cancel hge
      simp [hi, hidx]

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
private lemma splitBoolPointEquiv_apply
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin ℓ) :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w) i =
      if h : i.val < κ then
        v ⟨i.val, h⟩
      else
        w ⟨i.val - κ, by omega⟩ := rfl

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
private lemma splitBoolPointEquiv_prefix
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin κ) :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)
      ⟨i.val, by omega⟩ = v i := by
  rw [splitBoolPointEquiv_apply (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v := v) (w := w)]
  simp

omit [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
private lemma splitBoolPointEquiv_suffix
    (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) (i : Fin ℓ') :
    splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)
      ⟨i.val + κ, by
        rw [h_l]
        omega⟩ = w i := by
  rw [splitBoolPointEquiv_apply (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v := v) (w := w)]
  have hi : ¬ i.val + κ < κ := by
    omega
  simp [hi]


section EmbeddedSum
variable {A' : Type*} [CommRing A'] (φ : L →+* A')

-- The current multilinear-uniqueness library theorem requires a domain.
-- These proofs therefore cover the field instantiation, not arbitrary quotient rings.
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
private lemma map_ringHom_eq_MLE [IsDomain L] (t' : MultilinearPoly L ℓ') :
    MvPolynomial.map φ t'.val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 =>
        φ (MvPolynomial.eval (w : Fin ℓ' → L) t'.val)) := by
  have h_mle : t'.val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 => MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
    symm
    exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t'.val)).mp t'.property
  conv_lhs => rw [h_mle]
  rw [MvPolynomial.MLE, MvPolynomial.MLE]
  simp_rw [map_sum, map_mul, MvPolynomial.map_C]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MvPolynomial.eqPolynomial_zeroOne (R := L) (r := w)]
  rw [MvPolynomial.eqPolynomial_zeroOne (R := A') (r := w)]
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi, map_sub, map_one]
  · have hwi1 : w i = 1 := by omega
    simp [hwi1]

omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
private lemma zeroOneCoe_eq_ringHom (w : Fin ℓ' → Fin 2) :
    (fun i => ((w i : Fin 2) : A')) = fun i => φ (((w i : Fin 2) : L)) := by
  funext i
  have hi : w i = 0 ∨ w i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi]
  · simp [hi]

omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
private lemma map_eqPolynomial_ringHom (r : Fin ℓ' → L) :
    MvPolynomial.map φ (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      (MvPolynomial.eqPolynomial (fun i => φ (r i)) : MvPolynomial (Fin ℓ') A') := by
  rw [MvPolynomial.eqPolynomial_expanded, MvPolynomial.eqPolynomial_expanded]
  simp

omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
/-- `map φ` of the (multilinear) `eqPolynomial r` is its own MLE, indexed by the zero-one
evaluations `φ(eqTilde(r, w))`. Specialization of `map_ringHom_eq_MLE` to `eqPolynomial`. -/
private lemma map_ringHom_eq_MLE_eqPolynomial [IsDomain L] (r : Fin ℓ' → L) :
    MvPolynomial.map φ (MvPolynomial.eqPolynomial r : MvPolynomial (Fin ℓ') L) =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 =>
        φ (eqTilde r (w : Fin ℓ' → L))) := by
  have h := map_ringHom_eq_MLE (L := L) (ℓ' := ℓ') (φ := φ)
    (t' := ⟨MvPolynomial.eqPolynomial r, MvPolynomial.eqPolynomial_mem_restrictDegree r⟩)
  simpa only [MvPolynomial.eqTilde] using h

end EmbeddedSum

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] in
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
/-- Expand the embedded evaluation as the weighted sum of Boolean evaluations. -/
private lemma embedded_MLP_eval_eq_sum [IsDomain L] (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        P.φ₀ (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) *
          P.φ₁ (MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
  let r_suffix : Fin ℓ' → L := fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  unfold embedded_MLP_eval componentWise_embed_MLE
  change MvPolynomial.eval (fun i => P.φ₀ (r_suffix i)) (MvPolynomial.map P.φ₁ t'.val) = _
  rw [map_ringHom_eq_MLE (L := L) (ℓ' := ℓ') (φ := P.φ₁) (t' := t')]
  unfold MvPolynomial.MLE
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro w hw
  have h_eval :
      MvPolynomial.eval (fun i => ((w i : Fin 2) : P.A))
        (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i))) =
      P.φ₀ (eqTilde r_suffix (w : Fin ℓ' → L)) := by
    rw [show (MvPolynomial.eqPolynomial (fun i => P.φ₀ (r_suffix i)) :
        MvPolynomial (Fin ℓ') P.A) = MvPolynomial.map P.φ₀ (MvPolynomial.eqPolynomial r_suffix) from
      (map_eqPolynomial_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₀) (r := r_suffix)).symm]
    rw [zeroOneCoe_eq_ringHom (L := L) (ℓ' := ℓ') (φ := P.φ₀) (w := w)]
    rw [MvPolynomial.eval_map, MvPolynomial.eqTilde]
    exact (MvPolynomial.eval₂_comp (f := P.φ₀) (g := (w : Fin ℓ' → L))
      (p := MvPolynomial.eqPolynomial r_suffix)).symm
  rw [MvPolynomial.eqPolynomial_symm]
  rw [h_eval]

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] in
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
/-- Row coordinates of the embedded evaluation, using the explicit coordinate laws. -/
private lemma decompose_embedded_MLP_eval_rows (hCoord : CoordinateLaws P) [IsDomain L]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (v : Fin κ → Fin 2) :
    P.decomposeRows (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) v =
      ∑ w : Fin ℓ' → Fin 2,
        (P.basis.repr
          (eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L)) v)
          • MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (P := P) (t' := t') (r := r)]
  have hzero : P.decomposeRows 0 v = 0 := by
    have h := rows_add_apply (κ := κ) (L := L) (K := K) (P := P) hCoord 0 0 v; simpa using h
  have hsum : ∀ (s : Finset (Fin ℓ' → Fin 2)) (f : (Fin ℓ' → Fin 2) → P.A),
      P.decomposeRows (∑ w ∈ s, f w) v = ∑ w ∈ s, P.decomposeRows (f w) v := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp only [Finset.sum_empty, hzero]
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        rows_add_apply (κ := κ) (L := L) (K := K) (P := P) hCoord, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [rows_mul_apply (κ := κ) (L := L) (K := K) (P := P) hCoord]

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] in
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
/-- Column coordinates of the embedded evaluation, using the explicit coordinate laws. -/
private lemma decompose_embedded_MLP_eval_columns (hCoord : CoordinateLaws P) [IsDomain L]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (u : Fin κ → Fin 2) :
    P.decomposeColumns (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) u =
      ∑ w : Fin ℓ' → Fin 2,
        (P.basis.repr (MvPolynomial.eval (w : Fin ℓ' → L) t'.val) u)
          • eqTilde (fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩) (w : Fin ℓ' → L) := by
  rw [embedded_MLP_eval_eq_sum (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (P := P) (t' := t') (r := r)]
  have hzero : P.decomposeColumns 0 u = 0 := by
    have h := columns_add_apply (κ := κ) (L := L) (K := K) (P := P) hCoord 0 0 u; simpa using h
  have hsum : ∀ (s : Finset (Fin ℓ' → Fin 2)) (f : (Fin ℓ' → Fin 2) → P.A),
      P.decomposeColumns (∑ w ∈ s, f w) u = ∑ w ∈ s, P.decomposeColumns (f w) u := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => simp only [Finset.sum_empty, hzero]
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        columns_add_apply (κ := κ) (L := L) (K := K) (P := P) hCoord, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [columns_mul_apply (κ := κ) (L := L) (K := K) (P := P) hCoord]


omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] [NeZero ℓ]
  [NeZero ℓ'] in
private lemma repr_packMLE_eval (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ)
    (w : Fin ℓ' → Fin 2)
    (v : Fin κ → Fin 2) :
    β.repr (MvPolynomial.eval (w : Fin ℓ' → L) (packMLE κ L K ℓ ℓ' h_l β t).val) v =
      MvPolynomial.eval
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))
        t.val := by
  unfold packMLE
  simp only [MvPolynomial.MLE_eval_zeroOne, Basis.equivFun_symm_apply, Basis.repr_sum_self]
  apply congrArg (fun x => MvPolynomial.eval x t.val)
  funext i
  by_cases h : i.val < κ
  · simp [h]
  · simp [h]

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
private lemma eval₂_eqPolynomial_concat
    (eval_point : Fin ℓ → L)
    (v : Fin κ → Fin 2)
    (w : Fin ℓ' → Fin 2) :
    MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.eqPolynomial
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
      eqTilde (v : Fin κ → L) (fun i => eval_point ⟨i.val, by omega⟩) *
        eqTilde (fun i => eval_point ⟨i.val + κ, by
          rw [h_l]
          omega⟩) (w : Fin ℓ' → L) := by
  have h_eq : ℓ = κ + ℓ' := by
    omega
  let eval_point' : Fin (κ + ℓ') → L := eval_point ∘ Fin.cast h_eq.symm
  have hmain :
      MvPolynomial.eval₂ (algebraMap K L) eval_point'
        (MvPolynomial.eqPolynomial
          (fun i : Fin (κ + ℓ') =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
        eqTilde (v : Fin κ → L) (fun i => eval_point' (Fin.castAdd ℓ' i)) *
          eqTilde (fun i => eval_point' (Fin.natAdd κ i)) (w : Fin ℓ' → L) := by
    unfold MvPolynomial.eqTilde eval_point'
    simp_rw [MvPolynomial.eqPolynomial_expanded]
    rw [MvPolynomial.eval₂_prod, Fin.prod_univ_add, MvPolynomial.eval_prod, MvPolynomial.eval_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp
    · apply Finset.prod_congr rfl
      intro i hi
      simp
      ring_nf
  have hcast_poly :
      MvPolynomial.eval₂ (algebraMap K L) eval_point
        (MvPolynomial.eqPolynomial
          (fun i : Fin ℓ =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) =
      MvPolynomial.eval₂ (algebraMap K L) eval_point'
        (MvPolynomial.eqPolynomial
          (fun i : Fin (κ + ℓ') =>
            if h : i.val < κ then
              ((v ⟨i.val, h⟩ : Fin 2) : K)
            else
              ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))) := by
    subst h_eq
    rfl
  rw [hcast_poly, hmain]
  unfold MvPolynomial.eqTilde eval_point'
  congr 1
  apply congrArg (fun x => MvPolynomial.eval (w : Fin ℓ' → L) (MvPolynomial.eqPolynomial x))
  funext i
  have hidx : Fin.cast h_eq.symm (Fin.natAdd κ i) = ⟨i.val + κ, by
      rw [h_l]
      omega⟩ := by
    apply Fin.ext
    simp [Nat.add_comm]
  change eval_point (Fin.cast h_eq.symm (Fin.natAdd κ i)) = eval_point ⟨i.val + κ, by
      rw [h_l]
      omega⟩
  rw [hidx]

private def batchingCheckSummand (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L)
    (p : Fin ℓ → Fin 2) : L :=
  MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.eqPolynomial (fun i => ((p i : Fin 2) : K))) *
    (algebraMap K L)
      ((β.repr
        (MvPolynomial.eval
          (fun i => ((p ⟨i.val + κ, by
            rw [h_l]
            omega⟩ : Fin 2) : L))
          (packMLE κ L K ℓ ℓ' h_l β t).val))
        (fun i => p ⟨i.val, by omega⟩))

omit [NeZero κ] [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
private lemma batchingCheckSummand_split (β : Basis (Fin κ → Fin 2) K L)
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L)
    (v : Fin κ → Fin 2)
    (w : Fin ℓ' → Fin 2) :
    batchingCheckSummand κ L K ℓ ℓ' h_l β t eval_point
      (splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (v, w)) =
      (eqTilde (fun i => if (v i == 1) then 1 else 0) fun i => eval_point ⟨i.val, by omega⟩) *
        (β.repr (MvPolynomial.eval (w : Fin ℓ' → L) (packMLE κ L K ℓ ℓ' h_l β t).val)) v •
          eqTilde (fun i => eval_point ⟨i.val + κ, by
            rw [h_l]
            omega⟩) (w : Fin ℓ' → L) := by
  unfold batchingCheckSummand
  simp only [splitBoolPointEquiv_apply]
  have hpoly :
      (fun i : Fin ℓ =>
        (((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩) : Fin 2) : K)) =
      (fun i : Fin ℓ =>
        if h : i.val < κ then
          ((v ⟨i.val, h⟩ : Fin 2) : K)
        else
          ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) := by
    funext i
    by_cases h : i.val < κ
    · simp [h]
    · simp [h]
  have hsuffix :
      (fun i : Fin ℓ' =>
        (((if h : i.val + κ < κ then v ⟨i.val + κ, h⟩ else w ⟨i.val + κ - κ, by omega⟩) :
          Fin 2) : L)) = (w : Fin ℓ' → L) := by
    funext i
    have hi : ¬ i.val + κ < κ := by
      omega
    simp [hi]
  have hprefix :
      (fun i : Fin κ =>
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩) = v := by
    funext i
    simp
  rw [show MvPolynomial.eqPolynomial
      (fun i : Fin ℓ =>
        (((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩) : Fin 2) : K)) =
      MvPolynomial.eqPolynomial
        (fun i : Fin ℓ =>
          if h : i.val < κ then
            ((v ⟨i.val, h⟩ : Fin 2) : K)
          else
            ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) by
    rw [hpoly]]
  rw [show (fun i : Fin ℓ' =>
      (((if h : i.val + κ < κ then v ⟨i.val + κ, h⟩ else w ⟨i.val + κ - κ, by omega⟩) :
        Fin 2) : L)) = (w : Fin ℓ' → L) by
    exact hsuffix]
  rw [show (fun i : Fin κ =>
      if h : i.val < κ then
        v ⟨i.val, h⟩
      else
        w ⟨i.val - κ, by omega⟩) = v by
    exact hprefix]
  rw [eval₂_eqPolynomial_concat (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (eval_point := eval_point) (v := v) (w := w)]
  rw [repr_packMLE_eval (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t := t) (w := w) (v := v)]
  have hvL : (fun i => if (v i == 1) then (1 : L) else 0) = (v : Fin κ → L) := by
    funext i
    have hi : v i = 0 ∨ v i = 1 := by
      omega
    rcases hi with hi | hi
    · simp [hi]
    · simp [hi]
  rw [show (fun i => if (v i == 1) then (1 : L) else 0) = (v : Fin κ → L) by
    exact hvL]
  rw [Algebra.smul_def]
  let A : L := eqTilde (v : Fin κ → L) (fun i => eval_point ⟨i.val, by omega⟩)
  let B : L := eqTilde (fun i : Fin ℓ' => eval_point ⟨i.val + κ, by
    rw [h_l]
    omega⟩) (w : Fin ℓ' → L)
  let C : L := algebraMap K L (MvPolynomial.eval
    (fun i : Fin ℓ =>
      if h : i.val < κ then
        ((v ⟨i.val, h⟩ : Fin 2) : K)
      else
        ((w ⟨i.val - κ, by omega⟩ : Fin 2) : K))
    t.val)
  change (A * B) * C = A * (C * B)
  rw [mul_assoc]
  congr 1
  rw [mul_comm]

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
/-- The honest packed evaluation satisfies the verifier's original-evaluation check. -/
lemma batching_check_correctness (hCoord : CoordinateLaws P) [IsDomain K] [IsDomain L]
    (t : MultilinearPoly K ℓ)
    (eval_point : Fin ℓ → L) :
  performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
    (t.val.aeval eval_point)
    (r := eval_point) (s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l
      (packMLE κ L K ℓ ℓ' h_l P.basis t) eval_point) = true := by
  unfold performCheckOriginalEvaluation eqWeightedCoordSum
  simp only [decide_eq_true_eq]
  simp_rw [decompose_embedded_MLP_eval_columns (hCoord := hCoord) (κ := κ) (L := L)
    (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (t' := packMLE κ L K ℓ ℓ' h_l P.basis t) (r := eval_point)]
  conv_lhs =>
    rw [← unpack_pack_id (κ := κ) (L := L) (K := K) (β := P.basis) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (t := t)]
  unfold unpackMLE
  rw [MvPolynomial.aeval_def]
  change MvPolynomial.eval₂ (algebraMap K L) eval_point
      (MvPolynomial.MLE
        (fun p : Fin ℓ → Fin 2 =>
          let v : Fin κ → Fin 2 := fun i => p ⟨i.val, by omega⟩
          let w : Fin ℓ' → Fin 2 := fun i => p ⟨i.val + κ, by
            rw [h_l]
            omega⟩
          (P.basis.repr (MvPolynomial.eval (w : Fin ℓ' → L)
            (packMLE κ L K ℓ ℓ' h_l P.basis t).val)) v)) = _
  rw [MvPolynomial.MLE]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  change ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point p = _
  have hsplit :
      ∑ p : Fin ℓ → Fin 2, batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point p =
        ∑ vw : (Fin κ → Fin 2) × (Fin ℓ' → Fin 2),
          batchingCheckSummand κ L K ℓ ℓ' h_l P.basis t eval_point
            ((splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)) vw) := by
    symm
    exact Fintype.sum_equiv (splitBoolPointEquiv (κ := κ) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l))
      _ _ (fun vw => rfl)
  rw [hsplit]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [batchingCheckSummand_split (κ := κ) (L := L) (K := K) (β := P.basis) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (t := t) (eval_point := eval_point) (v := v) (w := w)]


omit [Fintype L] [DecidableEq L] in
private lemma zeroOnePoint_eq_coe {n : ℕ} (x : Fin n → Fin 2) :
    (fun i => if x i == 1 then (1 : L) else 0) = (x : Fin n → L) := by
  funext i
  have hi : x i = 0 ∨ x i = 1 := by omega
  rcases hi with hi | hi
  · simp [hi]
  · simp [hi]


-- Identify the batching multiplier through the honest row decomposition at Boolean points.
omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] in
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
private lemma compute_s0_embedded_MLP_eval_eq_sum (hCoord : CoordinateLaws P) [IsDomain L]
    (t' : MultilinearPoly L ℓ')
    (r_eval : Fin ℓ → L)
    (r''_batching : Fin κ → L) :
    compute_s0 κ L K P
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r_eval) r''_batching =
    ∑ w : Fin ℓ' → Fin 2,
      MvPolynomial.eval (w : Fin ℓ' → L)
          (compute_A_MLE κ L K P ℓ'
            (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
        MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
  rw [compute_s0, eqWeightedCoordSum]
  simp_rw [decompose_embedded_MLP_eval_rows (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r := r_eval)]
  calc
    ∑ u : Fin κ → Fin 2,
        eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
          ∑ w : Fin ℓ' → Fin 2,
            (P.basis.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              MvPolynomial.eval (w : Fin ℓ' → L) t'.val
      = ∑ w : Fin ℓ' → Fin 2,
          ∑ u : Fin κ → Fin 2,
            eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
              ((P.basis.repr
                  (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                    (w : Fin ℓ' → L)) u) •
                MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
            calc
              _ = ∑ u : Fin κ → Fin 2,
                  ∑ w : Fin ℓ' → Fin 2,
                    eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                      ((P.basis.repr
                          (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                            (w : Fin ℓ' → L)) u) •
                        MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
                    apply Finset.sum_congr rfl
                    intro u hu
                    rw [Finset.mul_sum]
              _ = _ := by
                    rw [Finset.sum_comm]
    _ = ∑ w : Fin ℓ' → Fin 2,
          (∑ u : Fin κ → Fin 2,
            (P.basis.repr
                (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                  (w : Fin ℓ' → L)) u) •
              eqTilde (u : Fin κ → L) r''_batching) *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            calc
              ∑ u : Fin κ → Fin 2,
                  eqTilde (fun i => if u i == 1 then 1 else 0) r''_batching *
                    ((P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      MvPolynomial.eval (w : Fin ℓ' → L) t'.val)
                = ∑ u : Fin κ → Fin 2,
                    ((P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      eqTilde (u : Fin κ → L) r''_batching) *
                        MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
                      apply Finset.sum_congr rfl
                      intro u hu
                      rw [zeroOnePoint_eq_coe (L := L) (x := u)]
                      rw [Algebra.smul_def, Algebra.smul_def]
                      ring_nf
              _ = _ := by
                    rw [← Finset.sum_mul]
    _ = ∑ w : Fin ℓ' → Fin 2,
          MvPolynomial.eval (w : Fin ℓ' → L)
              (compute_A_MLE κ L K P ℓ'
                (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val *
            MvPolynomial.eval (w : Fin ℓ' → L) t'.val := by
            apply Finset.sum_congr rfl
            intro w hw
            have h_mEq_w :
                MvPolynomial.eval (w : Fin ℓ' → L)
                    (compute_A_MLE κ L K P ℓ'
                      (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval) r''_batching).val =
                  ∑ u : Fin κ → Fin 2,
                    (P.basis.repr
                        (eqTilde (getEvaluationPointSuffix κ L ℓ ℓ' h_l r_eval)
                          (w : Fin ℓ' → L)) u) •
                      eqTilde (u : Fin κ → L) r''_batching := by
                  simp only [compute_A_MLE, MvPolynomial.MLE_eval_zeroOne]
                  unfold compute_A_func
                  dsimp
                  rw [zeroOnePoint_eq_coe (L := L) (x := w)]
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [zeroOnePoint_eq_coe (L := L) (x := u)]
            rw [h_mEq_w]

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] in
omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
/-- The honest batching target equals the Boolean sum of the round-zero polynomial. -/
lemma batching_target_consistency (hCoord : CoordinateLaws P) [IsDomain L]
    (t' : MultilinearPoly L ℓ')
    (msg0 : P.A)
    (ctx : RingSwitchingBaseContext κ L K ℓ P)
    (h_msg0 : msg0 = embedded_MLP_eval κ L K P ℓ ℓ' h_l t' ctx.t_eval_point) :
  let s₀ := compute_s0 κ L K P msg0 ctx.r_batching
  let H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) (ctx := ctx) (t := t') (i := 0)
    (challenges := Fin.elim0)
  sumcheckConsistencyProp (boolDomain L _) s₀ H := by
  classical
  let : DecidableEq L := Classical.decEq L
  subst h_msg0
  intro s₀ H
  rw [sumcheckConsistencyProp]
  change s₀ = ∑ x ∈ (boolDomain L ℓ').cube, H.val.eval x
  -- `H.val = fixFirstVariablesOfMQP 0 (computeRoundPoly) = computeRoundPoly.val = A.val * t'.val`
  have h_Hval :
      H.val = (compute_A_MLE κ L K P ℓ'
          (getEvaluationPointSuffix κ L ℓ ℓ' h_l ctx.t_eval_point) ctx.r_batching).val *
        t'.val := by
    have hH1 : H.val = MvPolynomial.fixFirstVariablesOfMQP ℓ'
        (0 : Fin (ℓ' + 1))
        (computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t').val
        Fin.elim0 := rfl
    rw [hH1, MvPolynomial.fixFirstVariablesOfMQP_zero_eq (ℓ := ℓ')
      (H := (computeRoundPoly (L := L) (ℓ := ℓ')
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t').val)]
    unfold computeRoundPoly RingSwitching_SumcheckMultParam
    simp only [Polynomial.aeval_X]
    rfl
  rw [h_Hval]
  have h_cube_eq : (boolDomain L ℓ').cube =
      (Finset.univ : Finset (Fin ℓ' → Fin 2)).image
        (fun b : Fin ℓ' → Fin 2 => fun i => boolEmbedding L (b i)) := by
    rw [show (boolDomain L ℓ').cube =
        Fintype.piFinset (fun _ : Fin ℓ' => Finset.univ.map (boolEmbedding L)) from rfl]
    have h_pi' := Fintype.piFinset_image
      (f := fun _ : Fin ℓ' => boolEmbedding L)
      (s := fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)))
    rw [Fintype.piFinset_univ] at h_pi'
    simp only [Finset.map_eq_image]
    exact h_pi'
  rw [h_cube_eq, Finset.sum_image
    (fun x hx y hy hxy => by funext i; exact (boolEmbedding L).injective (congrFun hxy i))]
  simp only [MvPolynomial.eval_mul]
  have hcoe : ∀ w : Fin ℓ' → Fin 2, (fun i => boolEmbedding L (w i)) = (w : Fin ℓ' → L) := by
    intro w; funext i
    have hi : w i = 0 ∨ w i = 1 := by omega
    rcases hi with hi | hi <;> simp [hi]
  simp_rw [hcoe]
  exact compute_s0_embedded_MLP_eval_eq_sum (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t' := t') (r_eval := ctx.t_eval_point)
    (r''_batching := ctx.r_batching)


end RingSwitching
