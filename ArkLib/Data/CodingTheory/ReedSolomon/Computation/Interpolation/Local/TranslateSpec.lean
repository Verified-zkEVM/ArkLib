/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.Translate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SourceMonomial
public import Mathlib.Algebra.Polynomial.Inductions
/-!
# Polynomial meaning of the truncated translation stage

The represented list is the existing translated local truncation, before rewriting U and
projecting low contact. The final localConstraintAt bridge retains that pending enlarged map.
All polynomial expressions below are proof-only representations of materialized scalar terms.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Local exponent pair with an arbitrary fixed higher-jet exponent attached. -/
def exponent (h : LocalVariable d →₀ ℕ) (t u : ℕ) : LocalVariable d →₀ ℕ :=
  Finsupp.single (localT d) t + Finsupp.single (localU d) u + h

/-- Meaning of a single scalar term; h is fixed metadata, not an executed polynomial value. -/
def atom (h : LocalVariable d →₀ ℕ) (t u : ℕ) (c : F) : LocalPolynomial F d :=
  monomial (exponent h t u) c

/-- Duplicate terms add as ordinary polynomial coefficients. -/
def represented (h : LocalVariable d →₀ ℕ) : List (Term F) → LocalPolynomial F d
  | [] => 0
  | t :: ts => atom h t.t t.u t.coefficient + represented h ts

theorem represented_append (h : LocalVariable d →₀ ℕ) (ts us : List (Term F)) :
    represented h (ts ++ us) = represented h ts + represented h us := by
  induction ts with
  | nil => simp [represented]
  | cons t ts ih => simp [represented, ih, add_assoc]

/-- A double coefficient sum is the mathematical form of the executed pair traversal. -/
def sumSpec (h : LocalVariable d →₀ ℕ) (m : ℕ) (P R : Polynomial F) : LocalPolynomial F d :=
  ∑ i ∈ Finset.range m, ∑ k ∈ Finset.range m,
    if i + k < m then atom h (i + k) k (P.coeff i * R.coeff k) else 0

private theorem atom_add (h : LocalVariable d →₀ ℕ) (t u : ℕ) (a b : F) :
    atom h t u (a + b) = atom h t u a + atom h t u b := map_add _ _ _

private theorem sumSpec_add_left (h : LocalVariable d →₀ ℕ) (m : ℕ)
    (P Q R : Polynomial F) : sumSpec h m (P + Q) R = sumSpec h m P R + sumSpec h m Q R := by
  unfold sumSpec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [Polynomial.coeff_add, add_mul, atom_add]

private theorem sumSpec_add_right (h : LocalVariable d →₀ ℕ) (m : ℕ)
    (P Q R : Polynomial F) : sumSpec h m P (Q + R) = sumSpec h m P Q + sumSpec h m P R := by
  unfold sumSpec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [Polynomial.coeff_add, mul_add, atom_add]

private theorem truncate_monomial (m : ℕ) (e : LocalVariable d →₀ ℕ) (c : F) :
    truncateLocalT m (monomial e c) = if e (localT d) < m then monomial e c else 0 := by
  classical
  ext v
  simp only [truncateLocalT, coeff_filterLocalMonomials]
  by_cases he : e = v
  · subst v
    split_ifs <;> simp
  · split_ifs <;> simp [coeff_monomial, he]

private theorem atom_factor (h : LocalVariable d →₀ ℕ) (i k : ℕ) (a b : F) :
    C a * X (localT d) ^ i * (C b * (X (localT d) * X (localU d)) ^ k) * monomial h 1 =
      atom h (i + k) k (a * b) := by
  simp only [mul_pow, X_pow_eq_monomial, C_mul_monomial, monomial_mul, mul_one,
    atom, exponent, Finsupp.single_add]
  congr 1
  abel_nf

private theorem sumSpec_monomial (h : LocalVariable d →₀ ℕ) (m i k : ℕ) (a b : F) :
    sumSpec h m (Polynomial.monomial i a) (Polynomial.monomial k b) =
      if i + k < m then atom h (i + k) k (a * b) else 0 := by
  classical
  unfold sumSpec
  have hz (t u : ℕ) : atom h t u (0 : F) = 0 := map_zero _
  simp_rw [Polynomial.coeff_monomial, ite_mul, mul_ite, zero_mul, mul_zero,
    apply_ite (atom h _ _), hz]
  by_cases hi : i < m
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · intro hk
        have hk' : m ≤ k := by simpa using hk
        simp [show ¬ i + k < m by omega]
    · intro j hj hji
      simp [Ne.symm hji]
    · simp [hi]
  · have hsum : ∀ j ∈ Finset.range m, i ≠ j := by
      intro j hj he
      subst j
      exact hi (Finset.mem_range.mp hj)
    rw [if_neg (by omega : ¬ i + k < m)]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro l _
    simp [hsum j hj]

/-- Exact low-T projection of the full translated product, with no degree assumptions on P,R. -/
theorem sumSpec_eq_truncate (h : LocalVariable d →₀ ℕ) (hT : h (localT d) = 0)
    (m : ℕ) (P R : Polynomial F) :
    sumSpec h m P R = truncateLocalT m
      (P.eval₂ C (X (localT d)) * R.eval₂ C (X (localT d) * X (localU d)) * monomial h 1) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    rw [sumSpec_add_left, Polynomial.eval₂_add, add_mul, add_mul, map_add, hp, hq]
  | monomial i a =>
    induction R using Polynomial.induction_on' with
    | add R S hr hs =>
      rw [sumSpec_add_right, Polynomial.eval₂_add, mul_add, add_mul, map_add, hr, hs]
    | monomial k b =>
      rw [sumSpec_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, atom_factor]
      rw [atom, truncate_monomial]
      have hz : h none = 0 := hT
      simp [exponent, localT, localU, localAux, hz]


/-- The inner cursor realizes a finite coefficient sum, with the strict T cutoff retained. -/
theorem represented_row (h : LocalVariable d →₀ ℕ) (m i start N : ℕ) (a : F)
    (R : Polynomial F) :
    represented h (rowSpec m i a start
      (Polynomial.AffinePowerTruncationMachine.coefficients R N start)) =
      ∑ k ∈ Finset.range N, if i + (start + k) < m then
        atom h (i + (start + k)) (start + k) (a * R.coeff (start + k)) else 0 := by
  induction N generalizing start with
  | zero => simp [Polynomial.AffinePowerTruncationMachine.coefficients, rowSpec, represented]
  | succ N ih =>
    rw [Polynomial.AffinePowerTruncationMachine.coefficients, rowSpec,
      Finset.sum_range_succ']
    by_cases hc : i + start < m
    · simp [hc, represented, ih, Nat.add_left_comm, add_comm]
    · simp [hc, ih, Nat.add_comm, Nat.add_left_comm]

/-- Both materialized coefficient cursors realize the double sum. -/
theorem represented_pairs (h : LocalVariable d →₀ ℕ) (m start N K : ℕ)
    (P R : Polynomial F) :
    represented h (pairsSpec m
      (Polynomial.AffinePowerTruncationMachine.coefficients R K 0) start
      (Polynomial.AffinePowerTruncationMachine.coefficients P N start)) =
      ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range K, if (start + i) + k < m then
        atom h ((start + i) + k) k (P.coeff (start + i) * R.coeff k) else 0 := by
  induction N generalizing start with
  | zero => simp [Polynomial.AffinePowerTruncationMachine.coefficients, pairsSpec, represented]
  | succ N ih =>
    rw [Polynomial.AffinePowerTruncationMachine.coefficients, pairsSpec,
      represented_append, represented_row, ih, Finset.sum_range_succ']
    simp [Nat.add_left_comm, add_comm]

/-- The emitted scalar list represents the T-truncated translated column factors. -/
theorem represented_column (h : LocalVariable d →₀ ℕ) (hT : h (localT d) = 0)
    (a y : F) (x b m : ℕ) :
    represented h (columnSpec a y x b m) = truncateLocalT m
      ((C a + X (localT d)) ^ x * (C y + X (localT d) * X (localU d)) ^ b *
        monomial h 1) := by
  have hs : represented h (columnSpec a y x b m) =
      sumSpec h m ((Polynomial.C a + Polynomial.X)^x)
        ((Polynomial.C y + Polynomial.X)^b) := by
    simpa only [columnSpec, sumSpec, Nat.zero_add] using
      represented_pairs h m 0 m m ((Polynomial.C a + Polynomial.X)^x)
        ((Polynomial.C y + Polynomial.X)^b)
  rw [hs, sumSpec_eq_truncate h hT]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X]

/-- Fixed visible-jet exponent metadata for one interpolation column. -/
def higherExponent (higher : Fin d → ℕ) : LocalVariable d →₀ ℕ :=
  ∑ j, Finsupp.single (localY j) (higher j)

private theorem higherExponent_T (higher : Fin d → ℕ) :
    higherExponent higher (localT d) = 0 := by
  simp [higherExponent, localT, localY]

private theorem higher_factor (higher : Fin d → ℕ) :
    (∏ j, X (localY j) ^ higher j : LocalPolynomial F d) = monomial (higherExponent higher) 1 := by
  classical
  unfold higherExponent
  have h (s : Finset (Fin d)) :
      (∏ j ∈ s, X (localY j) ^ higher j : LocalPolynomial F d) =
        monomial (∑ j ∈ s, Finsupp.single (localY j) (higher j)) 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, X_pow_eq_monomial, monomial_mul]
      simp
  exact h Finset.univ

/-- Exact existing-map refinement, including an arbitrary visible-jet column factor. -/
theorem represented_eq_translatedLocalTruncation (a y : F) (x b m : ℕ)
    (higher : Fin d → ℕ) :
    represented (higherExponent higher) (columnSpec a y x b m) =
      translatedLocalTruncation m a y (sourceMonomial (F := F) x b higher) := by
  rw [represented_column _ (higherExponent_T higher)]
  simp only [translatedLocalTruncation, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    sourceMonomial, map_mul, map_pow, map_prod]
  simp only [translateToU, bind₁_X_right, Fin.cases_zero, Fin.cases_succ]
  rw [higher_factor]

/-- The final local map is the existing enlarged map on this materialized representation.
This equality does not execute the pending U rewrite or low-contact projection. -/
theorem localConstraintAt_eq_enlarged_represented (a y : F) (x b m : ℕ)
    (higher : Fin d → ℕ) :
    localConstraintAt m a y (sourceMonomial (F := F) x b higher) =
      enlargedLocalConstraintMap m
        (represented (higherExponent higher) (columnSpec a y x b m)) := by
  rw [localConstraintAt_apply_eq_enlarged_translated, represented_eq_translatedLocalTruncation]


/-- Distinct exponent pairs remain distinct after attaching the same higher-jet metadata. -/
theorem exponent_injective (h : LocalVariable d →₀ ℕ) (t u i k : ℕ) :
    exponent h t u = exponent h i k ↔ t = i ∧ u = k := by
  constructor
  · intro he
    have ht := congrArg (fun e => e (localT d)) he
    have hu := congrArg (fun e => e (localU d)) he
    simp only [exponent, Finsupp.add_apply, Finsupp.single_eq_same, localT, localU,
      localAux, Finsupp.single_apply, reduceCtorEq, if_false, add_zero, zero_add] at ht hu
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The scalar coordinate sum is the actual coefficient of the represented polynomial. -/
theorem coeff_represented (h : LocalVariable d →₀ ℕ) (t u : ℕ) (ts : List (Term F)) :
    coeff (exponent h t u) (represented h ts) = coordinate t u ts := by
  classical
  induction ts with
  | nil => simp [represented, coordinate]
  | cons entry ts ih =>
    simp only [represented, coeff_add, atom, coeff_monomial, exponent_injective, ih,
      coordinate, List.map_cons, List.sum_cons]

/-- Executed lookup sums all duplicates at a genuine polynomial coordinate. -/
theorem lookup_eq_coefficient (h : LocalVariable d →₀ ℕ) (t u : ℕ) (ts : List (Term F)) :
    lookup t u ts = (coeff (exponent h t u) (represented h ts), 32 * (ts.length + 1)) := by
  rw [coeff_represented, lookup_correct]

/-- The closed program constructs the existing translated local column with a polynomial charge.
Higher-jet coordinates are fixed metadata; this stage performs no U-to-E rewrite. -/
theorem translate_refines (a y : F) (x b m : ℕ) (higher : Fin d → ℕ) :
    ∃ ts c, translate a y x b m = (.done ts, c) ∧
      represented (higherExponent higher) ts =
        translatedLocalTruncation m a y (sourceMonomial (F := F) x b higher) ∧
      ts.length ≤ m * m ∧ c ≤ 288 * (x + b + m + 2) * (m + 1) := by
  obtain ⟨c, hr, hc⟩ := construction_correct a y x b m
  refine ⟨columnSpec a y x b m, c, hr,
    represented_eq_translatedLocalTruncation a y x b m higher, ?_, ?_⟩
  · simpa only [columnSpec, Polynomial.AffinePowerTruncationMachine.coefficients_length]
      using pairsSpec_length_le m 0
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C a + Polynomial.X)^x) m 0)
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C y + Polynomial.X)^b) m 0)
  · have hf := Nat.mul_le_mul_left 36 (fuel_le x b m)
    nlinarith

end
end ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine
