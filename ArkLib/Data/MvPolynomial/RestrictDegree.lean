/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.Data.MvPolynomial.Degrees
public import ArkLib.Data.MvPolynomial.RestrictDegreeVar
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Operations preserving `MvPolynomial.restrictDegree`

This file collects lemmas about how the basic `MvPolynomial` operations interact with
`MvPolynomial.restrictDegree`, plus a "fix first `v` variables" helper. Fixing the first `v`
variables is the substitution `fixFirstVariablesSubst` (`fixFirstVariablesOfMQP_eq_bind₁`), with
evaluation form `eval_fixFirstVariablesOfMQP` and one-step composition
`fixFirstVariablesOfMQP_succ`.

The contents were originally housed in `Binius.BinaryBasefold.Prelude`. They are fully
generic (no binary-tower or characteristic dependencies) and have been promoted here so
that the structured (witness-mode) sumcheck — see
`ArkLib.ProofSystem.Sumcheck.Structured` — and any future ring-switching protocol can
import them without depending on `Binius.BinaryBasefold.*`.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {L : Type*} [CommSemiring L] (ℓ : ℕ)

/-- The original index of a variable that survives after fixing the first `v` variables. -/
def fixFirstVariablesOfMQP_survivingIndex (v : Fin (ℓ + 1)) : Fin (ℓ - v) → Fin ℓ :=
  fun i => ⟨v + i, by
    have hi := i.2
    have hv := v.2
    omega⟩

/-- Fixes the **first** `v` variables of a `ℓ`-variate multivariate polynomial, leaving variables
`v, ..., ℓ-1` as `Fin (ℓ-v)`. Used by the structured sumcheck via
`fixFirstVariablesOfMQP_degreeLE` / the prismalinear analog
`fixFirstVariablesOfMQP_degreeVarLE`. -/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = v + (ℓ - v) := (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)], with the surviving suffix
  -- variables on `Sum.inl` and the fixed prefix variables on `Sum.inr`.
  let finEquiv := (finSumFinEquiv (m := v) (n := ℓ - v)).symm.trans (Equiv.sumComm _ _)
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

/-- Fixing an empty prefix preserves the polynomial, including its variable indices. -/
theorem fixFirstVariablesOfMQP_zero (p : MvPolynomial (Fin ℓ) L) :
    fixFirstVariablesOfMQP ℓ 0 p Fin.elim0 = p := by
  unfold fixFirstVariablesOfMQP
  change map (eval (σ := Fin 0) Fin.elim0)
    (sumAlgEquiv L (Fin ℓ) (Fin 0) (rename _ p)) = p
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [map_mul] at hp ⊢
    rw [hp]
    congr 1
    have hi : finSumFinEquiv.symm (Fin.cast (show ℓ = 0 + (ℓ - 0) by omega) i) =
        Sum.inr i := by
      apply finSumFinEquiv.injective
      simp
    -- `erw`: the prefix length is `↑(0 : Fin (ℓ + 1))`, only definitionally `0`
    erw [rename_X]
    simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply]
    erw [hi]
    simp

section Substitution

variable {ℓ}

/-- The substitution performed by `fixFirstVariablesOfMQP`: the first `v` variables become the
fixed constants and the remaining ones are shifted down by `v`. -/
noncomputable def fixFirstVariablesSubst (v : Fin (ℓ + 1)) (challenges : Fin v → L) :
    Fin ℓ → MvPolynomial (Fin (ℓ - v)) L := fun j =>
  if hj : j.val < v.val then C (challenges ⟨j.val, hj⟩)
  else X ⟨j.val - v, by omega⟩

/-- Fixing the first `v` variables is the substitution `fixFirstVariablesSubst`. -/
theorem fixFirstVariablesOfMQP_eq_bind₁ (v : Fin (ℓ + 1)) (H : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP ℓ v H challenges = bind₁ (fixFirstVariablesSubst v challenges) H := by
  have hX : ∀ j : Fin ℓ, fixFirstVariablesOfMQP ℓ v (X j) challenges =
      fixFirstVariablesSubst v challenges j := by
    intro j
    unfold fixFirstVariablesOfMQP fixFirstVariablesSubst
    dsimp only
    rw [rename_X]
    by_cases hj : j.val < v.val
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ - ↑v)).symm (Fin.cast (by omega) j) =
          Sum.inl (⟨j.val, hj⟩ : Fin ↑v) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
        exact Fin.ext rfl
      simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inl,
        sumAlgEquiv_X_inr, map_C, eval_X, hj, ↓reduceDIte]
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ - ↑v)).symm (Fin.cast (by omega) j) =
          Sum.inr (⟨j.val - v, by omega⟩ : Fin (ℓ - ↑v)) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_right]
        apply Fin.ext
        simp only [Fin.natAdd_mk, Fin.val_cast]
        omega
      simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inr,
        sumAlgEquiv_X_inl, map_X, hj, ↓reduceDIte]
  induction H using MvPolynomial.induction_on with
  | C a =>
    unfold fixFirstVariablesOfMQP
    simp only [rename_C, sumAlgEquiv_C_inl, map_C, eval_C, bind₁_C_right]
  | add p q hp hq =>
    have h_add : fixFirstVariablesOfMQP ℓ v (p + q) challenges =
        fixFirstVariablesOfMQP ℓ v p challenges + fixFirstVariablesOfMQP ℓ v q challenges := by
      unfold fixFirstVariablesOfMQP
      simp only [map_add]
    rw [h_add, hp, hq, map_add]
  | mul_X p j hp =>
    have h_mul : fixFirstVariablesOfMQP ℓ v (p * X j) challenges =
        fixFirstVariablesOfMQP ℓ v p challenges * fixFirstVariablesOfMQP ℓ v (X j) challenges := by
      unfold fixFirstVariablesOfMQP
      simp only [map_mul]
    rw [h_mul, hp, hX, map_mul, bind₁_X_right]

/-- Evaluating a polynomial with its first `v` variables fixed is evaluating the original at the
concatenation of the fixed values and the evaluation point. -/
theorem eval_fixFirstVariablesOfMQP (v : Fin (ℓ + 1)) (H : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) (x : Fin (ℓ - v) → L) :
    eval x (fixFirstVariablesOfMQP ℓ v H challenges) =
      eval (fun j => if hj : j.val < v.val then challenges ⟨j.val, hj⟩
        else x ⟨j.val - v, by omega⟩) H := by
  rw [fixFirstVariablesOfMQP_eq_bind₁]
  change eval₂Hom (RingHom.id L) x _ = _
  rw [eval₂Hom_bind₁]
  refine congrArg (fun f => eval₂Hom (RingHom.id L) f H) (funext fun j => ?_)
  change eval x _ = _
  unfold fixFirstVariablesSubst
  split_ifs <;> simp

/-- Fixing every variable leaves evaluation at the fixed point. -/
theorem eval_fixFirstVariablesOfMQP_last (H : MvPolynomial (Fin ℓ) L)
    (challenges : Fin (Fin.last ℓ : Fin (ℓ + 1)) → L)
    (x : Fin (ℓ - (Fin.last ℓ : Fin (ℓ + 1))) → L) :
    eval x (fixFirstVariablesOfMQP ℓ (Fin.last ℓ) H challenges) = eval challenges H := by
  rw [eval_fixFirstVariablesOfMQP]
  refine congrArg (fun f => eval f H) (funext fun j => ?_)
  simp only [Fin.val_last, j.isLt, ↓reduceDIte]

/-- A cast between polynomial rings on equal numbers of variables is a renaming along
`Fin.cast`. -/
theorem cast_eq_rename_finCast {a b : ℕ} (hab : a = b)
    (h : MvPolynomial (Fin a) L = MvPolynomial (Fin b) L) (p : MvPolynomial (Fin a) L) :
    cast h p = rename (Fin.cast hab) p := by
  subst hab
  rw [cast_eq, show (Fin.cast (rfl : a = a)) = id from funext fun _ => rfl, rename_id_apply]

/-- Fixing one more variable after a prefix of length `i` is fixing the prefix of length `i + 1`
extended by the new value. The renaming identifies `ℓ - i - 1` with `ℓ - (i + 1)`. -/
theorem fixFirstVariablesOfMQP_succ (i : Fin ℓ) (H : MvPolynomial (Fin ℓ) L)
    (challenges : Fin i → L) (c : L) (h : ℓ - i - 1 = ℓ - (i + 1)) :
    rename (Fin.cast h) (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ ⟨i, by omega⟩ H challenges) (fun _ => c)) =
      fixFirstVariablesOfMQP ℓ ⟨i + 1, by omega⟩ H (Fin.snoc challenges c) := by
  simp only [fixFirstVariablesOfMQP_eq_bind₁, bind₁_bind₁, rename_bind₁]
  refine congrArg (fun f => bind₁ f H) (funext fun j => ?_)
  unfold fixFirstVariablesSubst
  by_cases hj : j.val < i.val
  · have hj' : j.val < i.val + 1 := by omega
    simp only [hj, hj', ↓reduceDIte, bind₁_C_right]
    congr 1
    have : (⟨j.val, hj'⟩ : Fin (i.val + 1)) = Fin.castSucc ⟨j.val, hj⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · by_cases hji : j.val = i.val
    · have hj' : j.val < i.val + 1 := by omega
      have h0 : (⟨j.val - i.val, by omega⟩ : Fin (ℓ - i)) = ⟨0, by omega⟩ := Fin.ext (by
        simp only; omega)
      simp only [hj, hj', ↓reduceDIte, bind₁_X_right, h0, Nat.lt_one_iff, rename_C]
      congr 1
      have : (⟨j.val, hj'⟩ : Fin (i.val + 1)) = Fin.last i.val := Fin.ext hji
      rw [this, Fin.snoc_last]
    · have hj' : ¬ j.val < i.val + 1 := by omega
      have hpos : ¬ j.val - i.val < 1 := by omega
      simp only [hj, hj', ↓reduceDIte, bind₁_X_right, hpos, rename_X]
      congr 1

end Substitution

/-- The per-variable / prismalinear degree-survival lemma: if a polynomial respects a per-variable
degree bound `b : Fin ℓ → ℕ`, then fixing the first `v` variables to scalars produces a polynomial
whose surviving `Fin (ℓ-v)` variables respect `b` restricted to their original suffix indices.
Needed for SWIRL-style sumchecks where the multiplier has degree `|D|-1` in the skip coord and
`≤ 1` in the remaining Boolean coords. The uniform `fixFirstVariablesOfMQP_degreeLE` below is the
constant-`b` corollary. -/
theorem fixFirstVariablesOfMQP_degreeVarLE
    {b : Fin ℓ → ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : MvPolynomial (Fin ℓ) L}
    (hp : poly ∈ restrictDegreeVar (Fin ℓ) L b) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈
      restrictDegreeVar (Fin (ℓ - v)) L (b ∘ fixFirstVariablesOfMQP_survivingIndex ℓ v) := by
  rw [MvPolynomial.mem_restrictDegreeVar]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  have h_l_eq : ℓ = v + (ℓ - v) := (Nat.add_sub_of_le v.is_le).symm
  set finEquiv := (finSumFinEquiv (m := v) (n := ℓ - v)).symm.trans (Equiv.sumComm _ _)
  set e : Fin ℓ ≃ Fin (ℓ - v) ⊕ Fin v := (finCongr h_l_eq).trans finEquiv with he
  set H_sum := MvPolynomial.rename (f := e) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeVarLE :
      H_grouped ∈ restrictDegreeVar (Fin (ℓ - v)) (L[X Fin ↑v]) ((b ∘ e.symm) ∘ Sum.inl) :=
    sumAlgEquiv_mem_restrictDegreeVar H_sum
      (rename_equiv_mem_restrictDegreeVar e poly hp)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support :=
    MvPolynomial.support_map_subset _ _ h_term_in_support
  have h_bound : term i ≤ (b ∘ e.symm) (Sum.inl i) :=
    (MvPolynomial.mem_restrictDegreeVar H_grouped).mp h_Hgrouped_degreeVarLE
      term h_term_in_Hgrouped_support i
  -- Bound-equality: (b ∘ e.symm) (Sum.inl i) is the original suffix variable `v + i`.
  have h_eq : e.symm (Sum.inl i) = fixFirstVariablesOfMQP_survivingIndex ℓ v i := by
    apply Fin.ext
    simp [he, finEquiv, fixFirstVariablesOfMQP_survivingIndex]
  change term i ≤ b (fixFirstVariablesOfMQP_survivingIndex ℓ v i)
  rw [← h_eq]
  exact h_bound

/-- Uniform corollary of `fixFirstVariablesOfMQP_degreeVarLE`: the constant per-variable case
`b = fun _ => deg`, where `restrictDegreeVar` collapses to `restrictDegree` definitionally via
`restrictDegreeVar_const`. Used by the structured sumcheck to bound the round polynomial. -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] :=
  fixFirstVariablesOfMQP_degreeVarLE ℓ (b := fun _ => deg) v hp

/-- For a multilinear `t` (each variable has `degreeOf ≤ 1`), substituting `t` into a univariate
`Q : L[X]` via `Polynomial.aeval` yields a multivariate polynomial whose degree in each variable is
bounded by `Q.natDegree`. Used by the structured sumcheck to bound the degree of `Q(witness)` in
the round polynomial `H = P · Q(t)`. -/
theorem degreeOf_aeval_le {L : Type*} [CommSemiring L] {σ : Type*} (i : σ)
    (Q : Polynomial L) (t : MvPolynomial σ L) (ht : degreeOf i t ≤ 1) :
    degreeOf i (Polynomial.aeval t Q) ≤ Q.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine le_trans (degreeOf_sum_le i Q.support _) ?_
  refine Finset.sup_le fun e he => ?_
  calc degreeOf i (algebraMap L (MvPolynomial σ L) (Q.coeff e) * t ^ e)
      ≤ degreeOf i (algebraMap L (MvPolynomial σ L) (Q.coeff e)) + degreeOf i (t ^ e) :=
        degreeOf_mul_le i _ _
    _ = degreeOf i (t ^ e) := by rw [MvPolynomial.algebraMap_eq, degreeOf_C, zero_add]
    _ ≤ e * degreeOf i t := degreeOf_pow_le i t e
    _ ≤ e * 1 := by gcongr
    _ = e := mul_one e
    _ ≤ Q.natDegree := Polynomial.le_natDegree_of_mem_supp e he

end MvPolynomial
