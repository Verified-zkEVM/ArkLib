/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Mirco Richter (Least Authority), Aristotle (Harmonic)
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.Nat.BitSum
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Binary encoding of univariate and multilinear polynomials

`linearMvExtension` sends a univariate polynomial of degree below `2^m` to a multilinear
polynomial in `m` variables by expanding each exponent into binary digits.
`powAlgHom` substitutes `Xᵢ ↦ X^(2^i)` in the other direction.

For multilinear polynomials, `coeff_powAlgHom_bitsValue` recovers each coefficient after
substitution, `powAlgHom_injOn` proves injectivity, and `natDegree_powAlgHom_le` bounds the
resulting degree by `2^m - 1`. These facts hold over a commutative semiring.

`bitExpo` and `bitsValue` are executable. The polynomial-valued mathematical views
`linearMvExtension` and `linearMvExtensionLMap` use Mathlib's noncomputable polynomial
addition; `partialEval` uses its noncomputable polynomial constructors. `powAlgHom` and
`powContraction` use the noncomputable `Polynomial` semiring instance. Executable polynomial
transformations require a computational representation, with agreement proved against these views.
-/

@[expose] public section

namespace LinearMvExtension

open MvPolynomial

variable {F : Type*} [CommSemiring F] {m : ℕ}

/-- The exponent vector consisting of the lowest `m` binary digits of `i`. -/
def bitExpo (i : ℕ) : (Fin m) →₀ ℕ :=
  { support := Finset.univ.filter fun j => Nat.testBit i j.1
    toFun := fun j => if Nat.testBit i j.1 then 1 else 0
    mem_support_toFun := by intro j; simp }

/-- Expand each exponent of a univariate polynomial of degree below `2^m` into binary digits,
sending `aᵢ Xⁱ` to `aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`. -/
noncomputable def linearMvExtension (p : Polynomial.degreeLT F (2 ^ m)) : MvPolynomial (Fin m) F :=
  p.val.sum fun i a ↦ monomial (bitExpo i) a

/-- Binary exponent expansion preserves addition. -/
@[simp]
lemma linearMvExtension_add {p q : Polynomial.degreeLT F (2 ^ m)} :
    linearMvExtension (p + q) = linearMvExtension p + linearMvExtension q := by
  simp [linearMvExtension, Polynomial.sum_add_index]

/-- Binary exponent expansion preserves scalar multiplication. -/
@[simp]
lemma linearMvExtension_smul {c : F} {p : Polynomial.degreeLT F (2 ^ m)} :
    linearMvExtension (c • p) = c • linearMvExtension p := by
  simp only [linearMvExtension, SetLike.val_smul]
  rw [Polynomial.sum_smul_index _ _ _ (by simp)]
  aesop
    (add simp
      [smul_monomial,
        Polynomial.sum,
        Finset.smul_sum])

lemma bitExpo_apply (i : ℕ) (j : Fin m) :
    (bitExpo i : Fin m →₀ ℕ) j = if Nat.testBit i j.1 then 1 else 0 := by
  rfl

lemma bitExpo_le_one (i : ℕ) (j : Fin m) :
    (bitExpo i : Fin m →₀ ℕ) j ≤ 1 := by aesop (add simp [bitExpo_apply])

/-- Every variable has degree at most one after binary exponent expansion. -/
lemma degreeOf_linearMvExtension_le {p : Polynomial.degreeLT F (2 ^ m)} {i : Fin m} :
    MvPolynomial.degreeOf i (linearMvExtension p) ≤ 1 := by
  have h_monomial_degrees {x} (hx : x ∈ p.val.support) :
      (degreeOf i (monomial (bitExpo x) (p.val.coeff x))) ≤ 1 := by
    aesop (add simp [degreeOf_eq_sup, bitExpo_le_one])
  have h_sum_degrees :
    (degreeOf i (p.val.sum fun i a ↦ monomial (bitExpo i) a)) ≤
      (Finset.sup p.val.support
        (fun x ↦ degreeOf i (monomial (bitExpo x) (p.val.coeff x)))) := by
    change degreeOf i (∑ x ∈ p.val.support,
      monomial (bitExpo x) (p.val.coeff x)) ≤ _
    exact MvPolynomial.degreeOf_sum_le _ _ _
  exact h_sum_degrees.trans (Finset.sup_le @h_monomial_degrees)


/-- The linear map sending `X^i`, for `i < 2^m`, to the monomial with exponent vector `bitExpo i`.
-/
noncomputable def linearMvExtensionLMap :
    Polynomial.degreeLT F (2^m) →ₗ[F] MvPolynomial (Fin m) F where
    -- p(X) = aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
    toFun p := linearMvExtension p
    map_add' := by simp
    map_smul' := by simp

@[simp]
lemma linearMvExtensionLMap_apply (p : Polynomial.degreeLT F (2 ^ m)) :
    linearMvExtensionLMap p = linearMvExtension p := rfl

/-- Evaluate the first `k` variables of an `m`-variable polynomial at `α`, leaving a polynomial
in the remaining `m - k` variables. -/
noncomputable def partialEval {k : ℕ} (f : MvPolynomial (Fin m) F) (α : Fin k → F) (h : k ≤ m) :
    MvPolynomial (Fin (m - k)) F :=
  let φ : Fin m → MvPolynomial (Fin (m - k)) F := fun i =>
    if h' : i.val < k then
      C (α ⟨i.val, h'⟩)
    else
      let j := i.val - k
      let j' : Fin (m - k) := ⟨j, by omega⟩
      X j'
  eval₂ C φ f

/-- The algebra homomorphism substituting `Xᵢ ↦ X^(2^i)` in an `m`-variable polynomial. -/
noncomputable def powAlgHom :
    MvPolynomial (Fin m) F →ₐ[F] Polynomial F :=
   aeval fun j => Polynomial.X ^ (2 ^ (j : ℕ))

lemma powAlgHom_of_restrict_degree_natDegree {p : MvPolynomial.restrictDegree (Fin m) F 1} :
    (powAlgHom p.1).natDegree ≤ (2 ^ m - 1) := by
  have h_monomial_deg : ∀ d ∈ p.val.support, (∑ j : Fin m, d j * 2 ^ j.val) ≤ 2 ^ m - 1 := by
    have h_deg {d} (hd : d ∈ p.val.support) :
      (∑ j : Fin m, d j * 2 ^ j.val) ≤ ∑ j : Fin m, 2 ^ j.val := by
      have h_deg {j : Fin m} : d j ≤ 1 := by
        have := p.2
        simp_all only [restrictDegree, mem_support_iff, ne_eq, ge_iff_le]
        have := p.2
        rw [mem_restrictDegree] at this
        exact this d (by aesop) j
      exact Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (Nat.zero_le _) h_deg
    convert (fun d hd ↦ h_deg (d := d) hd) using 3
    exact Nat.sub_eq_of_eq_add
      (by exact Nat.recOn m (by norm_num) fun n ih ↦
        by simp [Fin.sum_univ_castSucc, pow_succ'] at *; linarith)
  exact le_trans (Polynomial.natDegree_sum_le _ _) <| Finset.sup_le <| fun d hd ↦ by
    specialize h_monomial_deg d hd
    simp_all only [Finsupp.mem_support_iff, ne_eq, Polynomial.algebraMap_eq, Finsupp.prod_pow,
      Function.comp_apply, Polynomial.natDegree_le_iff_coeff_eq_zero, Polynomial.coeff_C_mul]
    simp_all only [←pow_mul', Finset.prod_pow_eq_pow_sum, Polynomial.coeff_X_pow, mul_ite, mul_one,
      mul_zero, ite_eq_right_iff, imp_false]
    exact fun N hN ↦ ne_of_gt (lt_of_le_of_lt h_monomial_deg hN)

lemma powAlgHom_natDegree {p : MvPolynomial (Fin m) F} :
    (powAlgHom p).natDegree ≤ p.totalDegree * (2 ^ m - 1) := by
  have h_deg {d} (hd : d ∈ p.support) :
    (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree ≤
        d.sum (fun i k => 2^i.val * k) := by
    simp only [
      powAlgHom,
      aeval_def,
      Polynomial.algebraMap_eq,
      eval₂_monomial,
      Finsupp.prod]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) <| by
      exact le_trans (Polynomial.natDegree_prod_le _ _) <| by
        simp only [←pow_mul, Finsupp.sum]
        exact Finset.sum_le_sum fun i _ ↦ Polynomial.natDegree_X_pow_le _
  have h_le {d} (hd : d ∈ p.support) :
    (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree ≤ p.totalDegree * (2^m - 1) := by
    have h_sum : d.sum (fun i k ↦ 2^i.val * k) ≤
      p.totalDegree * (2^m - 1) := by
      have h_sum : d.sum (fun i k ↦ 2^i.val * k) ≤
        d.sum (fun _ k => k) * (2^m - 1) := by
        rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul _ _ _]
        exact Finset.sum_le_sum fun i hi ↦ by
          rw [mul_comm]
          exact Nat.mul_le_mul_left _
            (Nat.le_sub_one_of_lt (pow_lt_pow_right₀ (by decide) (Fin.is_lt i)))
      exact h_sum.trans
        (Nat.mul_le_mul_right _ (Finset.le_sup (f := fun s ↦ s.sum fun x k ↦ k) hd))
    exact le_trans (h_deg hd) h_sum
  have h_sum_le : (powAlgHom p).natDegree ≤
    Finset.sup p.support (fun d ↦ (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree) := by
    have h_sum : powAlgHom p =
      ∑ d ∈ p.support, powAlgHom (MvPolynomial.monomial d (p.coeff d)) := by
      rw [MvPolynomial.as_sum p, map_sum]
      simp [MvPolynomial.support_sum_monomial_coeff]
    exact h_sum.symm ▸ Polynomial.natDegree_sum_le _ _
  exact h_sum_le.trans (Finset.sup_le (fun d hd ↦ h_le hd))

lemma powAlgHom_degree {p : MvPolynomial (Fin m) F} :
    (powAlgHom p).degree ≤ ↑(p.totalDegree * (2 ^ m - 1)) := by
  rw [←Polynomial.natDegree_le_iff_degree_le]
  exact powAlgHom_natDegree

/-- A multilinear polynomial in `m` variables is sent by `powAlgHom` to a polynomial of degree at
most `2 ^ m - 1`. -/
theorem natDegree_powAlgHom_le {P : MvPolynomial (Fin m) F}
    (hP : P ∈ restrictDegree (Fin m) F 1) : (powAlgHom P).natDegree ≤ 2 ^ m - 1 :=
  powAlgHom_of_restrict_degree_natDegree (p := ⟨P, hP⟩)

/-- Evaluating `powAlgHom P` at `ζ` is evaluating `P` at `(ζ, ζ², ζ⁴, …, ζ^(2 ^ (m - 1)))`. -/
theorem eval_powAlgHom (P : MvPolynomial (Fin m) F) (ζ : F) :
    (powAlgHom P).eval ζ = MvPolynomial.eval (fun i : Fin m => ζ ^ (2 ^ (i : ℕ))) P := by
  rw [powAlgHom, ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval,
    ← MvPolynomial.coe_aeval_eq_eval]
  simp

/-- The weighted exponent sum `∑ᵢ 2 ^ i * sᵢ`, the binary encoding when every `sᵢ ≤ 1`. -/
def bitsValue (s : Fin m →₀ ℕ) : ℕ := ∑ i : Fin m, 2 ^ (i : ℕ) * s i

/-- The binary weighted sum is injective on exponent vectors whose entries are at most one. -/
theorem bitsValue_injOn : Set.InjOn (bitsValue (m := m)) {s | ∀ i, s i ≤ 1} :=
  fun _ hs _ ht h => Finsupp.ext (congrFun (Nat.eq_of_sum_pow_two_mul_eq _ _ hs ht h))

/-- Expand `powAlgHom P` as the sum of `C (P.coeff s) * X ^ bitsValue s` over `P.support`. -/
theorem powAlgHom_eq_sum (P : MvPolynomial (Fin m) F) :
    powAlgHom P =
      ∑ s ∈ P.support, Polynomial.C (P.coeff s) * Polynomial.X ^ bitsValue s := by
  unfold powAlgHom
  rw [aeval_def, eval₂, Finsupp.sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), bitsValue, ← Finset.prod_pow_eq_pow_sum]
  simp [pow_mul]

/-- **Coefficient recovery.** For a multilinear `P` and a binary exponent vector `s`, the
coefficient of `X ^ bitsValue s` in `powAlgHom P` is the coefficient of `∏ᵢ Xᵢ ^ sᵢ` in `P`:
distinct multilinear monomials get distinct powers of `X`, so no coefficients merge. -/
theorem coeff_powAlgHom_bitsValue {P : MvPolynomial (Fin m) F}
    (hP : P ∈ restrictDegree (Fin m) F 1) (s : Fin m →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    (powAlgHom P).coeff (bitsValue s) = P.coeff s := by
  classical
  have hdeg := (mem_restrictDegree (Fin m) P 1).1 hP
  simp only [powAlgHom_eq_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t ht hts
    exact ite_eq_right_iff.2 (fun h => (hts (bitsValue_injOn hs (hdeg t ht) h).symm).elim)
  · intro hnot
    simp only [mem_support_iff, not_not] at hnot
    simp [hnot]

/-- `powAlgHom` is injective on multilinear polynomials, over any commutative semiring: the
coefficients of `P` are recovered from those of `powAlgHom P` at the binary exponents
(`coeff_powAlgHom_bitsValue`), and all other coefficients of a multilinear `P` vanish. -/
theorem powAlgHom_injOn :
    Set.InjOn (powAlgHom (F := F) (m := m)) (restrictDegree (Fin m) F 1) := by
  intro P hP Q hQ hpq
  ext s
  by_cases hs : ∀ i, s i ≤ 1
  · rw [← coeff_powAlgHom_bitsValue hP s hs, ← coeff_powAlgHom_bitsValue hQ s hs, hpq]
  · have hcoeff : ∀ T : MvPolynomial (Fin m) F,
        T ∈ restrictDegree (Fin m) F 1 → T.coeff s = 0 := by
      intro T hT
      by_contra h
      exact hs ((mem_restrictDegree (Fin m) T 1).1 hT s (mem_support_iff.2 h))
    rw [hcoeff P hP, hcoeff Q hQ]

/-- Substitution by `Xᵢ ↦ X^(2^i)` preserves nonzero multilinear polynomials. -/
theorem powAlgHom_ne_zero {P : MvPolynomial (Fin m) F}
    (hP : P ∈ restrictDegree (Fin m) F 1) (h0 : P ≠ 0) : powAlgHom P ≠ 0 := by
  intro h
  exact h0 (powAlgHom_injOn hP (zero_mem _) (by simpa using h))

/-- The linear map underlying the substitution `Xᵢ ↦ X^(2^i)`. -/
noncomputable def powContraction :
    MvPolynomial (Fin m) F →ₗ[F] Polynomial F :=
  powAlgHom.toLinearMap

@[simp]
lemma powContraction_apply (p : MvPolynomial (Fin m) F) :
    powContraction p = powAlgHom p := rfl

private lemma binary_repr_sum (m i : ℕ) (hi : i < 2 ^ m) :
    ∑ j ∈ Finset.range m, (if Nat.testBit i j then 2 ^ j else 0) = i := by
  induction m generalizing i with
  | zero => simp_all
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_zero, pow_zero, decide_eq_true_eq]
    have key : ∑ x ∈ Finset.range m,
        (if i.testBit (x + 1) then 2 ^ (x + 1) else 0) =
      2 * ∑ x ∈ Finset.range m,
        (if (i / 2).testBit x then 2 ^ x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [Nat.testBit_add_one, pow_succ]
      ring_nf
    have hi2 : i / 2 < 2 ^ m := by rw [pow_succ] at hi; omega
    rw [key, ih (i / 2) hi2]
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] <;> omega

/-- Substitution after binary exponent expansion recovers a univariate polynomial of degree
below `2^m`. -/
lemma powContraction_linearMvExtensionLMap
    (p : Polynomial.degreeLT F (2 ^ m)) :
    powContraction.comp linearMvExtensionLMap p = p := by
  have hnat : (p : Polynomial F).natDegree < 2 ^ m := by
    have hdeg := Polynomial.mem_degreeLT.mp p.2
    by_cases hp : (p : Polynomial F) = 0
    · simp [hp]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
  have h_comp : powContraction (linearMvExtensionLMap p) =
      ∑ i ∈ Finset.range (2 ^ m), p.val.coeff i • Polynomial.X ^ i := by
    rw [powContraction_apply, linearMvExtensionLMap_apply]
    unfold linearMvExtension powAlgHom
    rw [MvPolynomial.aeval_def]
    have h_sum_range :
        (p : Polynomial F).sum (fun i a => MvPolynomial.monomial (bitExpo (m := m) i) a) =
          ∑ i ∈ Finset.range (2 ^ m),
            MvPolynomial.monomial (bitExpo (m := m) i) ((p : Polynomial F).coeff i) := by
      exact Polynomial.sum_over_range' (p : Polynomial F) (by intro n; simp) (2 ^ m) hnat
    rw [h_sum_range, MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp +decide only [Polynomial.algebraMap_eq, eval₂_monomial, Finsupp.prod_pow]
    have h_sum : ∑ x : Fin m, 2 ^ (x : ℕ) * (bitExpo i) x = i := by
      convert binary_repr_sum m i (Finset.mem_range.mp hi) using 1
      rw [Finset.sum_range]
      simp only [bitExpo_apply]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, h_sum]
    simp [Polynomial.smul_eq_C_mul]
  change powContraction (linearMvExtensionLMap p) = (p : Polynomial F)
  rw [h_comp]
  convert (Polynomial.as_sum_range' p.val (2 ^ m) hnat).symm using 1
  simp +decide [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial]

/-- Binary exponent expansion followed by substitution recovers a polynomial of degree
below `2^m`. -/
lemma powAlgHom_linearMvExtension
    (p : Polynomial.degreeLT F (2 ^ m)) :
    powAlgHom (linearMvExtension p) = p := by
  exact powContraction_linearMvExtensionLMap p

end LinearMvExtension
