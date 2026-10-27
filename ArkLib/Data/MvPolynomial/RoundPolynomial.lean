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

/-! # Round polynomials over arbitrary finite domains

This file owns finite sums of selected-coordinate projections: direct substitution,
evaluation, the domain-sum identity, and the bound by the selected coordinate's degree.
The summation indices and assignments are arbitrary, so heterogeneous coordinate domains,
Boolean enumerations, and degree-bounded carriers all specialize the same algebra.
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

/-- Sum selected-coordinate projections over any finite family of assignments. -/
noncomputable def sumRoundPolynomial {m : ℕ} {ι : Type*} (S : Finset ι)
    (s : ι → Fin (m - 1) → R) (k : Fin m) (p : MvPolynomial (Fin m) R) : Polynomial R :=
  match m with
  | 0 => k.elim0
  | _ + 1 => ∑ x ∈ S, Polynomial.map (MvPolynomial.eval (s x)) (finSuccEquivNth R k p)

/-- Evaluation of a round polynomial is the residual sum with the free coordinate fixed. -/
theorem sumRoundPolynomial_eval {ι : Type*} (S : Finset ι) (s : ι → Fin n → R)
    (k : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (sumRoundPolynomial S s k p).eval r =
      ∑ x ∈ S, p.eval (Fin.insertNth k r (s x)) := by
  simp only [sumRoundPolynomial, Polynomial.eval_finsetSum,
    ← eval_eq_eval_mv_eval_finSuccEquivNth]

/-- Prefix form of residual evaluation, with an arbitrary finite suffix domain. -/
theorem sumRoundPolynomial_eval_prefix {l : ℕ} (i : Fin (n + 1))
    (c : Fin i → R) (S : Finset (Fin l → R)) (h : n = i + l)
    (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (sumRoundPolynomial (m := n + 1) S (fun x => Fin.append c x ∘ Fin.cast h) i p).eval r =
      ∑ x ∈ S, p.eval (Fin.append (Fin.snoc c r) x ∘ Fin.cast (by omega)) := by
  rw [sumRoundPolynomial_eval]
  simp only [Fin.insertNth_append_cast i c _ r h]

/-- Uniform-domain residual evaluation with the successor-prefix dimension. -/
theorem sumRoundPolynomial_eval_prefix_uniform (i : Fin (n + 1))
    (c : Fin i → R) (S : Finset R) (p : MvPolynomial (Fin (n + 1)) R) (r : R) :
    (sumRoundPolynomial (Fintype.piFinset (fun _ : Fin (n - i) => S))
      (fun x => Fin.append c x ∘ Fin.cast (by omega)) i p).eval r =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin (n + 1 - (i + 1)) => S),
        p.eval (Fin.append (Fin.snoc c r) x ∘ Fin.cast (by omega)) := by
  rw [sumRoundPolynomial_eval_prefix i c _ (by omega)]
  rw [Fin.sum_piFinset_cast S (show n + 1 - (i + 1) = n - i by omega)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [Fin.append_cast_right]
  rfl

/-- Summing the round polynomial over the current domain recovers the previous residual sum. -/
theorem sumRoundPolynomial_sum_prefix {l : ℕ} (i : Fin (n + 1))
    (c : Fin i → R) (S : Fin (l + 1) → Finset R) (h : n = i + l)
    (p : MvPolynomial (Fin (n + 1)) R) :
    ∑ a ∈ S 0,
      (sumRoundPolynomial (m := n + 1) (Fintype.piFinset (Fin.tail S))
        (fun x => Fin.append c x ∘ Fin.cast h) i p).eval a =
      ∑ x ∈ Fintype.piFinset S, p.eval (Fin.append c x ∘ Fin.cast (by omega)) := by
  rw [Fin.sum_piFinset_cons]
  simp_rw [sumRoundPolynomial_eval_prefix i c _ h]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [Fin.append_left_snoc]
  simp only [Function.comp_def, Fin.cast_cast]

/-- The degree of a round sum is bounded by the source's degree in the free coordinate. -/
theorem sumRoundPolynomial_natDegree_le {m : ℕ} {ι : Type*} (S : Finset ι)
    (s : ι → Fin (m - 1) → R) (k : Fin m) (p : MvPolynomial (Fin m) R) :
    (sumRoundPolynomial S s k p).natDegree ≤ p.degreeOf k := by
  cases m with
  | zero => exact k.elim0
  | succ n =>
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro x _
    exact Polynomial.natDegree_map_le.trans (le_of_eq (natDegree_finSuccEquivNth _))

/-- A global individual-degree cap specializes the coordinate bound. -/
theorem sumRoundPolynomial_mem_degreeLE {m : ℕ} {ι : Type*} (S : Finset ι)
    (s : ι → Fin (m - 1) → R) (k : Fin m) {p : MvPolynomial (Fin m) R} {d : ℕ}
    (hp : p ∈ restrictDegree (Fin m) R d) :
    sumRoundPolynomial S s k p ∈ Polynomial.degreeLE R d := by
  apply Polynomial.mem_degreeLE.mpr
  apply Polynomial.natDegree_le_iff_degree_le.mp
  exact (sumRoundPolynomial_natDegree_le S s k p).trans
    (degreeOf_le_iff.mpr fun m a => hp a k)

/-- Summing a first-coordinate round over its domain recovers the heterogeneous product sum. -/
theorem sum_sumRoundPolynomial (S : Fin (n + 1) → Finset R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    ∑ a ∈ S 0,
      (sumRoundPolynomial (Fintype.piFinset (Fin.tail S)) id 0 p).eval a =
        ∑ x ∈ Fintype.piFinset S, p.eval x := by
  simp_rw [sumRoundPolynomial_eval, id_eq, Fin.insertNth_zero]
  exact (Fin.sum_piFinset_cons S (fun x => p.eval x)).symm

/-- First-coordinate evaluation with an arity equation. Only the assignment indices need
transport; the source polynomial stays in its original ring. -/
theorem sumRoundPolynomial_eval_first {m l : ℕ} (h : l = m + 1)
    (S : Finset (Fin m → R)) (p : MvPolynomial (Fin l) R) (r : R) :
    (sumRoundPolynomial (m := l) S (fun x => x ∘ Fin.cast (by omega))
      ⟨0, by omega⟩ p).eval r =
      ∑ x ∈ S, p.eval (Fin.cons r x ∘ Fin.cast h) := by
  subst l
  simp only [sumRoundPolynomial_eval, Fin.mk_zero', Fin.insertNth_zero, Fin.cast_refl,
    Function.comp_id, cast_eq]

/-- Summing a first-coordinate round with an arity equation recovers the original cube sum. -/
theorem sum_sumRoundPolynomial_first {m l : ℕ} (h : l = m + 1) (S : Finset R)
    (p : MvPolynomial (Fin l) R) :
    ∑ a ∈ S, (sumRoundPolynomial (m := l) (Fintype.piFinset (fun _ : Fin m => S))
      (fun x => x ∘ Fin.cast (by omega)) ⟨0, by omega⟩ p).eval a =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin l => S), p.eval x := by
  subst l
  exact sum_sumRoundPolynomial (fun _ => S) p

end MvPolynomial
