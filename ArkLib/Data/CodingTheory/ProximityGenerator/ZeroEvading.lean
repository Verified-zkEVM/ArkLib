/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.MultilinearBasic
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Zero evasion for batching generators

Powers, affine coordinates, and tensor products of affine lines have zero-evasion errors
`(k - 1) / |F|`, `1 / |F|`, and `m / |F|`, respectively. The probability bounds hold even when
the displayed ratio exceeds one; the unit-interval certificates cap these bounds at one.
-/

@[expose] public section

namespace CoreDefinitions

open scoped ProbabilityTheory ENNReal NNReal BigOperators
open ProbabilityTheory Probability unitInterval

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

omit [Fintype F] [SampleableType F] in
/-- Zero evasion bounds the failure probability at each fixed nonzero vector. -/
theorem IsZeroEvadingGenerator.prob_le {S ℓ : Type} [Fintype S] [Nonempty S]
    [SampleableType S] [Fintype ℓ] {G : Generator S ℓ F} {ε : I}
    (hG : IsZeroEvadingGenerator G ε) (v : ℓ → F) (hv : v ≠ 0) :
    Pr{let s ← $ᵗ S}[dotProduct (G s) v = 0] ≤ ENNReal.ofReal ε := by
  apply le_trans (le_sSup ?_) hG
  exact ⟨v, hv, rfl⟩

/-- Restrict the powers curve to exactly `k` coordinates, including the empty family. -/
abbrev powerBatchGenerator (F : Type) [Field F] (k : ℕ) : Generator F (Fin k) F :=
  fun a i => univariatePowersGenerator F k a i.castSucc

/-- A nonzero vector annihilates a uniformly sampled powers curve with probability at most
`(k - 1) / |F|`. -/
theorem prob_dotProduct_powerBatchGenerator_eq_zero_le {k : ℕ} (v : Fin k → F) (hv : v ≠ 0) :
    Pr{let a ← $ᵗ F}[dotProduct (powerBatchGenerator F k a) v = 0] ≤
      ((k - 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  have hp : Polynomial.ofFn k v ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa [i.isLt] using congrArg (fun p : Polynomial F => p.coeff i.val) h
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    exact hv (Subsingleton.elim _ _)
  have hd := Nat.le_pred_of_lt (Polynomial.ofFn_natDegree_lt hk v)
  simpa [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, dotProduct, powerBatchGenerator, univariatePowersGenerator,
    mul_comm] using prob_polynomial_eval_eq_le hp hd
      (show (0 : Polynomial F).natDegree ≤ k - 1 by simp)

/-- Turn a nonnegative probability bound into a unit-interval error. -/
def cappedError (ε : ℝ≥0) : I :=
  ⟨min 1 (ε : ℝ), by constructor <;> simp⟩

omit [Fintype F] [SampleableType F] in
/-- Pointwise bounds on all nonzero vectors give zero evasion, capped at probability one. -/
theorem isZeroEvadingGenerator_of_prob_le {S ℓ : Type} [Fintype S] [Nonempty S]
    [SampleableType S] [Fintype ℓ] (G : Generator S ℓ F) (ε : ℝ≥0)
    (hG : ∀ v : ℓ → F, v ≠ 0 →
      Pr{let s ← $ᵗ S}[dotProduct (G s) v = 0] ≤ (ε : ℝ≥0∞)) :
    IsZeroEvadingGenerator G (cappedError ε) := by
  classical
  unfold IsZeroEvadingGenerator
  refine sSup_le ?_
  rintro y ⟨v, hv, rfl⟩
  change _ ≤ ENNReal.ofReal (min 1 (ε : ℝ))
  rw [ENNReal.ofReal_min]
  simpa using le_min (prEvent_le_one _) (hG v hv)

/-- The powers curve has zero-evasion error `(k - 1) / |F|`, capped at one. -/
theorem isZeroEvadingGenerator_powerBatchGenerator (k : ℕ) :
    IsZeroEvadingGenerator (powerBatchGenerator F k)
      (cappedError ((k - 1 : ℕ) / Fintype.card F : ℝ≥0)) := by
  apply isZeroEvadingGenerator_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero :
    (Fintype.card F : ℝ≥0) ≠ 0), ENNReal.coe_natCast] using
    prob_dotProduct_powerBatchGenerator_eq_zero_le v hv

/-- Monomials with distinct exponent vectors form a zero-evading polynomial generator. -/
theorem prob_dotProduct_monomialGenerator_eq_zero_le {s d : ℕ} {ℓ : Type} [Fintype ℓ]
    (e : ℓ → (Fin s →₀ ℕ)) (he : Function.Injective e)
    (hd : ∀ i, (e i).sum (fun _ n => n) ≤ d) (v : ℓ → F) (hv : v ≠ 0) :
    Pr{let r ← $ᵗ (Fin s → F)}[
      dotProduct (fun i => MvPolynomial.eval r (MvPolynomial.monomial (e i) (1 : F))) v = 0] ≤
      (d : ℝ≥0∞) / Fintype.card F := by
  classical
  let p : MvPolynomial (Fin s) F := ∑ i, MvPolynomial.monomial (e i) (v i)
  have hp : p ≠ 0 := by
    intro h
    apply hv
    funext i
    have hc := congrArg (fun q : MvPolynomial (Fin s) F => q.coeff (e i)) h
    simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff] using hc
  have hpd : p.totalDegree ≤ d := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    exact Finset.sup_le fun i _ => (MvPolynomial.totalDegree_monomial_le _ _).trans (hd i)
  have heval (r : Fin s → F) :
      dotProduct (fun i => MvPolynomial.eval r (MvPolynomial.monomial (e i) (1 : F))) v =
        MvPolynomial.eval r p := by
    simp [p, dotProduct, MvPolynomial.eval_monomial, mul_comm]
  simpa only [heval] using prob_eval_zero_univ_le_div p hp hpd

/-- Exponents for the constant monomial followed by the individual variables. -/
noncomputable def affineExponents (n : ℕ) : Fin (n + 1) → (Fin n →₀ ℕ) :=
  Fin.cases 0 (fun i => Finsupp.single i 1)

lemma affineExponents_injective (n : ℕ) : Function.Injective (affineExponents n) := by
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · intro _; rfl
  · intro h
    have hh := congrArg (fun e : Fin n →₀ ℕ => e b) h
    simp [affineExponents] at hh
  · intro h
    have hh := congrArg (fun e : Fin n →₀ ℕ => e a) h
    simp [affineExponents] at hh
  · simp only [affineExponents, Fin.cases_succ, Finsupp.single_eq_single_iff]
    intro h
    exact congrArg Fin.succ (h.resolve_right (by simp)).1

/-- A nonzero affine form vanishes with probability at most `1 / |F|`. -/
theorem prob_dotProduct_affineSpaceGenerator_eq_zero_le (n : ℕ)
    (v : Fin (n + 1) → F) (hv : v ≠ 0) :
    Pr{let r ← $ᵗ (Fin n → F)}[dotProduct (AffineSpaceGenerator F n r) v = 0] ≤
      (1 : ℝ≥0∞) / Fintype.card F := by
  have heval (r : Fin n → F) (i : Fin (n + 1)) :
      MvPolynomial.eval r (MvPolynomial.monomial (affineExponents n i) (1 : F)) =
        AffineSpaceGenerator F n r i := by
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [affineExponents, AffineSpaceGenerator, MvPolynomial.eval_monomial]
  have hd (i : Fin (n + 1)) : (affineExponents n i).sum (fun _ a => a) ≤ 1 := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [affineExponents]
  simpa only [heval, Nat.cast_one] using
    prob_dotProduct_monomialGenerator_eq_zero_le (affineExponents n)
      (affineExponents_injective n) hd v hv

/-- Affine coordinates have zero-evasion error `1 / |F|`. -/
theorem isZeroEvadingGenerator_affineSpaceGenerator (n : ℕ) :
    IsZeroEvadingGenerator (AffineSpaceGenerator F n)
      (cappedError (1 / Fintype.card F : ℝ≥0)) := by
  apply isZeroEvadingGenerator_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero :
    (Fintype.card F : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_natCast] using
    prob_dotProduct_affineSpaceGenerator_eq_zero_le n v hv

/-- The recursive monomial ordering as binary exponent vectors. -/
def multilinearBinaryIndex : (m : ℕ) → Fin (2 ^ m) ≃ (Fin m → Fin 2)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => 0
      left_inv := fun i => (Fin.eq_zero i).symm
      right_inv := fun _ => Subsingleton.elim _ _ }
  | m + 1 => ((multilinearIndex m).symm.trans
      ((Equiv.refl (Fin 2)).prodCongr (multilinearBinaryIndex m))).trans
        (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2))

omit [Fintype F] [SampleableType F] in
/-- Each tensor coordinate is the squarefree monomial indexed by its binary vector. -/
theorem multilinearGenerator_eq_prod (m : ℕ) (r : Fin m → F) (i : Fin (2 ^ m)) :
    multilinearGenerator F m r i = ∏ j, r j ^ (multilinearBinaryIndex m i j).val := by
  induction m with
  | zero => simp [multilinearGenerator]
  | succ m ih =>
    rw [Fin.prod_univ_succ]
    change AffineLineGenerator F (r 0) ((multilinearIndex m).symm i).1 *
      multilinearGenerator F m (fun j => r j.succ) ((multilinearIndex m).symm i).2 = _
    rw [ih]
    change AffineLineGenerator F (r 0) ((multilinearIndex m).symm i).1 * _ =
      r 0 ^ ((multilinearIndex m).symm i).1.val * _
    congr 1
    generalize ((multilinearIndex m).symm i).1 = a
    fin_cases a <;> simp [AffineLineGenerator]

/-- The exponent vector of a binary monomial. This is a mathematical polynomial index. -/
noncomputable def binaryExponents {m : ℕ} (b : Fin m → Fin 2) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (b j).val)

lemma binaryExponents_injective (m : ℕ) :
    Function.Injective (binaryExponents : (Fin m → Fin 2) → (Fin m →₀ ℕ)) := by
  intro a b h
  funext j
  apply Fin.ext
  exact congrArg (fun e : Fin m →₀ ℕ => e j) h

/-- A nonzero multilinear form in `m` seeds vanishes with probability at most `m / |F|`. -/
theorem prob_dotProduct_multilinearGenerator_eq_zero_le (m : ℕ)
    (v : Fin (2 ^ m) → F) (hv : v ≠ 0) :
    Pr{let r ← $ᵗ (Fin m → F)}[dotProduct (multilinearGenerator F m r) v = 0] ≤
      (m : ℝ≥0∞) / Fintype.card F := by
  classical
  let e : Fin (2 ^ m) → (Fin m →₀ ℕ) := fun i =>
    binaryExponents (multilinearBinaryIndex m i)
  have he : Function.Injective e :=
    (binaryExponents_injective m).comp (multilinearBinaryIndex m).injective
  have hd (i : Fin (2 ^ m)) : (e i).sum (fun _ a => a) ≤ m := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ j : Fin m, (multilinearBinaryIndex m i j).val) ≤ m
    calc _ ≤ ∑ _j : Fin m, 1 :=
          Finset.sum_le_sum fun j _ => Nat.le_of_lt_succ (multilinearBinaryIndex m i j).isLt
      _ = m := by simp
  have heval (r : Fin m → F) (i : Fin (2 ^ m)) :
      MvPolynomial.eval r (MvPolynomial.monomial (e i) (1 : F)) =
        multilinearGenerator F m r i := by
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    exact (multilinearGenerator_eq_prod _ _ _).symm
  simpa only [heval] using prob_dotProduct_monomialGenerator_eq_zero_le e he hd v hv

/-- Tensor products of affine lines have zero-evasion error `m / |F|`, capped at one. -/
theorem isZeroEvadingGenerator_multilinearGenerator (m : ℕ) :
    IsZeroEvadingGenerator (multilinearGenerator F m)
      (cappedError (m / Fintype.card F : ℝ≥0)) := by
  apply isZeroEvadingGenerator_of_prob_le
  intro v hv
  simpa only [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero :
    (Fintype.card F : ℝ≥0) ≠ 0), ENNReal.coe_natCast] using
    prob_dotProduct_multilinearGenerator_eq_zero_le m v hv

end CoreDefinitions
