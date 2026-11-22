/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors, Elias Judin, Stefano Rocca, Aristotle (Harmonic),
  Pablo Martín Vinuelas

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)
-/
module

public import ArkLib.Data.Fin.BigOperators
public import ArkLib.Data.MvPolynomial.RestrictDegree
public import CompPoly.ToMathlib.MvPolynomial.Equiv

/-! # Restriction to coordinate lines

This file defines substitution of every coordinate except a selected one, and proves
evaluation, product-domain summation, and selected-coordinate degree bounds.
The coefficient-substitution identity incorporates ArkLib PR #1128 (derived from Leanth
PR #16, revision `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`) and Hachi's representation proof.
-/

@[expose] public section

namespace Fin

/-- Inserting the free coordinate between a prefix and suffix extends the prefix by `snoc`. -/
theorem insertNth_append_cast {R : Type*} {n l : ℕ} (i : Fin (n + 1))
    (c : Fin i → R) (x : Fin l → R) (r : R) (h : n = i + l) :
    Fin.insertNth i r (Fin.append c x ∘ Fin.cast (by omega)) =
      Fin.append (Fin.snoc c r) x ∘ Fin.cast (by omega) := by
  funext j
  rcases lt_trichotomy j i with hj | hj | hj
  · rw [Fin.insertNth_apply_below hj]
    simp [Fin.append, Fin.addCases, Fin.snoc,
      show j.val < i.val by exact hj, le_of_lt hj]
    congr 1
  · subst j
    simp [Fin.append, Fin.addCases, Fin.snoc]
  · rw [Fin.insertNth_apply_above hj]
    simp only [Fin.append, Function.comp_apply,
      Fin.addCases, Fin.val_cast, Fin.val_pred, show ¬j.val - 1 < i.val by omega,
      ↓reduceDIte, Fin.cast_cast, eq_rec_constant, show ¬j.val < i.val + 1 by omega]
    congr 1
    apply Fin.ext
    simp
    omega

end Fin

namespace MvPolynomial

open Finset

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Mapping coefficients of the selected-coordinate representation is direct substitution. -/
theorem map_finSuccEquivNth_eq_eval₂_insertNth
    (k : Fin (n + 1)) (s : Fin n → R) (p : MvPolynomial (Fin (n + 1)) R) :
    Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth R k p) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.insertNth k Polynomial.X (fun j => Polynomial.C (s j))) p := by
  rw [MvPolynomial.finSuccEquivNth_apply, MvPolynomial.coe_eval₂Hom]
  change (Polynomial.mapRingHom (MvPolynomial.eval s)) (MvPolynomial.eval₂ _ _ p) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext j
    refine Fin.succAboveCases k ?_ ?_ j
    · simp [Fin.insertNth_apply_same]
    · intro l
      simp [Fin.insertNth_apply_succAbove]

/-- Evaluate every coordinate except `k` at `s`, leaving a univariate polynomial in coordinate `k`
(the restriction of `p` to the coordinate line through `s` in direction `k`). -/
noncomputable def evalExcept {m : ℕ} (k : Fin m) (s : Fin (m - 1) → R)
    (p : MvPolynomial (Fin m) R) : Polynomial R :=
  match m with
  | 0 => k.elim0
  | _ + 1 => Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth R k p)

/-- Coordinate-line restriction is direct substitution into univariate polynomials. -/
theorem evalExcept_eq_eval₂_insertNth (k : Fin (n + 1)) (s : Fin n → R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    p.evalExcept k s = MvPolynomial.eval₂ Polynomial.C
      (Fin.insertNth k Polynomial.X (fun j => Polynomial.C (s j))) p :=
  map_finSuccEquivNth_eq_eval₂_insertNth k s p

/-- Evaluation of a coordinate-line restriction fixes the remaining coordinate. -/
@[simp]
theorem eval_evalExcept (k : Fin (n + 1)) (s : Fin n → R)
    (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (p.evalExcept k s).eval r = p.eval (Fin.insertNth k r s) := by
  simp only [evalExcept, ← eval_eq_eval_mv_eval_finSuccEquivNth]

/-- Evaluation with assignments assembled from a prefix and suffix. -/
theorem eval_evalExcept_append {l : ℕ} (i : Fin (n + 1))
    (c : Fin i → R) (x : Fin l → R) (h : n = i + l)
    (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (p.evalExcept i (Fin.append c x ∘ Fin.cast h)).eval r =
      p.eval (Fin.append (Fin.snoc c r) x ∘ Fin.cast (by omega)) := by
  rw [eval_evalExcept, Fin.insertNth_append_cast i c x r h]

/-- Evaluation with a suffix indexed by the successor-prefix dimension. -/
theorem eval_evalExcept_append_uniform (i : Fin (n + 1))
    (c : Fin i → R) (x : Fin (n + 1 - (i + 1)) → R)
    (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (p.evalExcept i (Fin.append c x ∘ Fin.cast (by omega))).eval r =
      p.eval (Fin.append (Fin.snoc c r) x ∘ Fin.cast (by omega)) :=
  eval_evalExcept_append i c x (by omega) p r

/-- Summing restrictions over the free coordinate and suffix gives the full product sum. -/
theorem sum_eval_evalExcept_append {l : ℕ} (i : Fin (n + 1))
    (c : Fin i → R) (S : Fin (l + 1) → Finset R) (h : n = i + l)
    (p : MvPolynomial (Fin (n + 1)) R) :
    ∑ a ∈ S 0, ∑ x ∈ Fintype.piFinset (Fin.tail S),
      (p.evalExcept i (Fin.append c x ∘ Fin.cast h)).eval a =
      ∑ x ∈ Fintype.piFinset S, p.eval (Fin.append c x ∘ Fin.cast (by omega)) := by
  rw [Fin.sum_piFinset_cons]
  simp_rw [eval_evalExcept_append i c _ h]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [Fin.append_left_snoc]
  simp only [Function.comp_def, Fin.cast_cast]

/-- Restriction cannot increase the degree in the selected coordinate. -/
theorem natDegree_evalExcept_le {m : ℕ} (k : Fin m) (s : Fin (m - 1) → R)
    (p : MvPolynomial (Fin m) R) :
    (p.evalExcept k s).natDegree ≤ p.degreeOf k := by
  cases m with
  | zero => exact k.elim0
  | succ n =>
    exact Polynomial.natDegree_map_le.trans (le_of_eq (natDegree_finSuccEquivNth _))

/-- A global individual-degree cap specializes the coordinate bound. -/
theorem evalExcept_mem_degreeLE {m : ℕ} (k : Fin m) (s : Fin (m - 1) → R)
    {p : MvPolynomial (Fin m) R} {d : ℕ} (hp : p ∈ restrictDegree (Fin m) R d) :
    p.evalExcept k s ∈ Polynomial.degreeLE R d := by
  apply Polynomial.mem_degreeLE.mpr
  apply Polynomial.natDegree_le_iff_degree_le.mp
  exact (natDegree_evalExcept_le k s p).trans
    (degreeOf_le_iff.mpr fun m a => hp a k)

/-- Summing first-coordinate restrictions recovers the heterogeneous product sum. -/
theorem sum_eval_evalExcept_zero (S : Fin (n + 1) → Finset R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    ∑ a ∈ S 0, ∑ x ∈ Fintype.piFinset (Fin.tail S), (p.evalExcept 0 x).eval a =
      ∑ x ∈ Fintype.piFinset S, p.eval x := by
  simp_rw [eval_evalExcept, Fin.insertNth_zero]
  exact (Fin.sum_piFinset_cons S (fun x => p.eval x)).symm

/-- First-coordinate evaluation with an arity equation. Only the assignment indices need
transport; the source polynomial stays in its original ring. -/
theorem eval_evalExcept_first {m l : ℕ} (h : l = m + 1)
    (x : Fin m → R) (p : MvPolynomial (Fin l) R) (r : R) :
    (p.evalExcept ⟨0, by omega⟩ (x ∘ Fin.cast (by omega))).eval r =
      p.eval (Fin.cons r x ∘ Fin.cast h) := by
  subst l
  simp only [eval_evalExcept, Fin.mk_zero', Fin.insertNth_zero, Fin.cast_refl,
    Function.comp_id, cast_eq]

/-- Summing first-coordinate restrictions with an arity equation gives the product sum. -/
theorem sum_eval_evalExcept_first {m l : ℕ} (h : l = m + 1) (S : Finset R)
    (p : MvPolynomial (Fin l) R) :
    ∑ a ∈ S, ∑ x ∈ Fintype.piFinset (fun _ : Fin m => S),
      (p.evalExcept ⟨0, by omega⟩ (x ∘ Fin.cast (by omega))).eval a =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin l => S), p.eval x := by
  subst l
  exact sum_eval_evalExcept_zero (fun _ => S) p

end MvPolynomial
