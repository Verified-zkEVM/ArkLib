/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.Nat.Bitwise
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian

/-!
# Frobenius polynomial identities

This file establishes fundamental identities involving the Frobenius endomorphism for polynomials
over finite fields. The main results include factorization identities, Frobenius polynomial
identities, and divisibility conditions for irreducible polynomials.

## Main Definitions and Theorems

1. **Field Vanishing Polynomial Equality:**
   - `prod_X_sub_C_eq_X_pow_card_sub_X`: The identity `∏_{c ∈ Fq} (X - c) = X^q - X` in `Fq[X]`
   - `prod_X_sub_C_eq_X_pow_card_sub_X_in_L`: Lifted version for field extensions `L[X]`
   - `prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L`: General version
     `∏_{c ∈ Fq} (p - c) = p^q - p` for any polynomial `p` in `L[X]`

2. **Frobenius Polynomial Identity:**
   - `frobenius_identity_in_ground_field`: `(f + g)^q = f^q + g^q` in `Fq[X]` (Freshman's Dream)
   - `frobenius_identity_in_algebra`: Lifted version for `Fq`-algebras `L[X]`
   - `aeval_pow_card_eq_aeval_pow_card`: `(aeval x f)^q = aeval (x^q) f` for polynomial evaluation
   - `aeval_pow_card_pow_eq_aeval_pow_card_pow`: Iterated version
     `(aeval x f)^(q^n) = aeval (x^(q^n)) f`

3. **Frobenius Polynomial Divisibility:**
   - `X_pow_sub_one_dvd_X_pow_sub_one_of_dvd`: If `k ∣ n`, then `X^k - 1 ∣ X^n - 1`
   - `X_pow_card_pow_dvd_X_pow_card_pow_of_dvd`: If `d ∣ n`, then `X^(q^d) - X ∣ X^(q^n) - X`
   - `irreducible_dvd_X_pow_card_pow_sub_X`: An irreducible polynomial `p` of degree `d` divides
     `X^(q^d) - X`
   - `degree_dvd_of_irreducible_dvd_X_pow_card_pow_sub_X`: If irreducible `p` divides `X^(q^n) - X`,
     then `deg(p) ∣ n`
   - `irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd`: Fundamental theorem:
     `p ∣ X^(q^n) - X ↔ deg(p) ∣ n`

## TODOs
- potentially generalize the Frobenius theorems to generic algebras?
-/

variable {Fq : Type*} [Field Fq] [Fintype Fq]

instance instExpCharOfAlgebra {K : Type*} [Field K] [Algebra Fq K]
  {h_ringChar_Fq_pos : (ringChar Fq) ≠ 0} : ExpChar K (ringChar Fq) := by
  let p := ringChar Fq
  letI charP_Fq_p: CharP Fq p := ringChar.charP Fq
  haveI : CharP K p := by
    have h_inj : Function.Injective (algebraMap Fq K) :=
      RingHom.injective (algebraMap Fq K)
    exact (RingHom.charP_iff (A := K) (f := algebraMap Fq K) (H := h_inj) p).mp charP_Fq_p
  have h_ringExpChar_K : ringExpChar K = p := by
    rw [ringExpChar, ringChar.eq K p]; simp only [sup_eq_left];
    exact Nat.one_le_iff_ne_zero.mpr h_ringChar_Fq_pos
  letI inst_expChar_K_p : ExpChar K p := ringExpChar.of_eq h_ringExpChar_K
  exact inst_expChar_K_p

namespace Polynomial
section FieldVanishingPolynomialEquality
-- NOTE : We lift `∏_{c ∈ Fq} (X - c) = X^q - X` from `Fq[X]` to `L[X]`,
-- then achieve a generic version `∏_{c ∈ Fq} (p - c) = p^q - p` for any `p` in `L[X]`

/--
The polynomial `X^q - X` factors into the product of `(X - c)` ∀ `c` ∈ `Fq`,
i.e. `∏_{c ∈ Fq} (X - c) = X^q - X`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X :
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  set P : Fq[X] := ∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)
  set Q : Fq[X] := Polynomial.X^(Fintype.card Fq) - Polynomial.X

  -- We will prove P = Q by showing they are both monic and have the same roots.
  have hP_monic : P.Monic := by
    apply Polynomial.monic_prod_of_monic
    intro c _
    exact Polynomial.monic_X_sub_C c

  have hQ_monic : Q.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast (by exact Fintype.one_lt_card)

  have h_roots_P : P.roots = (Finset.univ : Finset Fq).val := by
    apply Polynomial.roots_prod_X_sub_C
  -- The roots of Q are, by Fermat's Little Theorem, also all elements of Fq.
  have h_roots_Q : Q.roots = (Finset.univ : Finset Fq).val := by
    exact FiniteField.roots_X_pow_card_sub_X Fq

  -- Step 3 : Prove P and Q have the same set of roots.
  have h_roots_eq : P.roots = Q.roots := by
    rw [h_roots_P, h_roots_Q]

  have hP_splits : P.Splits := by
    apply Polynomial.Splits.prod
    intro c _
    apply Polynomial.Splits.X_sub_C

  have hQ_card_roots : Q.roots.card = Fintype.card Fq := by
    rw [h_roots_Q]
    exact rfl

  have natDegree_Q : Q.natDegree = Fintype.card Fq := by
    unfold Q
    have degLt : (X : Fq[X]).natDegree < ((X : Fq[X]) ^ Fintype.card Fq).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_X]
      exact Fintype.one_lt_card
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt degLt]
    rw [Polynomial.natDegree_X_pow]

  have hQ_splits : Q.Splits := by
    unfold Q
    apply Polynomial.splits_iff_card_roots.mpr
    rw [hQ_card_roots]
    rw [natDegree_Q]

  -- Since P and Q are monic, split, and have the same roots, they are equal.
  have hP_eq_prod : P = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) P.roots).prod := by
    apply Polynomial.Splits.eq_prod_roots_of_monic hP_splits hP_monic
  have hQ_eq_prod : Q = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) Q.roots).prod := by
    apply Polynomial.Splits.eq_prod_roots_of_monic hQ_splits hQ_monic
  rw [hP_eq_prod, hQ_eq_prod, h_roots_eq]

variable {L : Type*} [CommRing L] [Algebra Fq L]
/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X_in_L :
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (algebraMap Fq L c))) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  let f := algebraMap Fq L

  -- The goal is an equality in L[X]. We will show that this equality is just
  -- the "mapped" version of the equality in Fq[X], which we already proved.
  have h_lhs_map : (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (f c))) =
      Polynomial.map f (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) := by
    rw [Polynomial.map_prod]
    congr! with c
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have h_rhs_map : (Polynomial.X^(Fintype.card Fq) - Polynomial.X) =
      Polynomial.map f (Polynomial.X^(Fintype.card Fq) - Polynomial.X) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  rw [h_lhs_map, h_rhs_map]
  -- The goal is now `map f (LHS_base) = map f (RHS_base)`.
  -- This is true if `LHS_base = RHS_base`, which is exactly our previous theorem.
  rw [prod_X_sub_C_eq_X_pow_card_sub_X]

/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L
  (p : L[X]) :
  (∏ c ∈ (Finset.univ : Finset Fq), (p - Polynomial.C (algebraMap Fq L c))) =
    p^(Fintype.card Fq) - p := by

  -- The strategy is to take the known identity for the polynomial X and substitute
  -- X with the arbitrary polynomial p. This substitution is formally known as
  -- polynomial composition (`Polynomial.comp`).

  let q := Fintype.card Fq
  let base_identity := prod_X_sub_C_eq_X_pow_card_sub_X_in_L (L := L) (Fq:=Fq)

  -- APPROACH : f = g => f.comp(p) = g.comp(p)
  have h_composed_eq : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p
    = ((X:L[X])^q - X).comp p := by
    rw [base_identity]

  have h_lhs_simp : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p =
                     ∏ c ∈ (Finset.univ : Finset Fq), (p - C (algebraMap Fq L c)) := by
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro c _
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]

  have h_rhs_simp : ((X:L[X])^q - X).comp p = p^q - p := by
    rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp]
  rw [h_lhs_simp, h_rhs_simp] at h_composed_eq
  exact h_composed_eq
end FieldVanishingPolynomialEquality

section FrobeniusPolynomialIdentity
-- NOTE : We lift the Frobenius identity from `Fq[X]` to `L[X]`
/--
The Frobenius identity for polynomials in `Fq[X]`.
The `q`-th power of a sum of polynomials is the sum of their `q`-th powers.
-/
theorem frobenius_identity_in_ground_field
  [Fact (Nat.Prime (ringChar Fq))] (f g : Fq[X]) :
    (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The Freshman's Dream `(a+b)^e = a^e + b^e` holds if `e` is a power of the characteristic.
  let p := ringChar Fq
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p
  rw [hn]
  haveI : CharP Fq[X] p := Polynomial.charP
  exact add_pow_expChar_pow f g p ↑n

variable {L : Type*} [CommRing L] [Algebra Fq L] [Nontrivial L]

/--
The lifted Frobenius identity for polynomials in `L[X]`, where `L` is an `Fq`-algebra.
The exponent `q` is the cardinality of the base field `Fq`.
-/
theorem frobenius_identity_in_algebra [Fact (Nat.Prime (ringChar Fq))]
  (f g : L[X]) : (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The logic is identical. The key is that `L` inherits the characteristic of `Fq`.
  let p := ringChar Fq
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p
  rw [hn]
  have h_charP_Fq : CharP Fq p := by
    simp only [p]
    exact ringChar.charP Fq

  have h_charP_L : CharP L p := by
    have h_inj : Function.Injective (algebraMap Fq L) := by
      exact RingHom.injective (algebraMap Fq L)
    have h_charP_L := (RingHom.charP_iff (A := L) (f := algebraMap Fq L)
      (H := h_inj) p).mp h_charP_Fq
    exact h_charP_L
  have h_charP_L_X : CharP L[X] p := Polynomial.charP
  exact add_pow_expChar_pow f g p ↑n

omit [Fintype Fq] [Nontrivial L] in
/-- Restricting a linear map on polynomial composition to a linear map on polynomial evaluation.
-/
theorem linear_map_of_comp_to_linear_map_of_eval (f : L[X])
  (h_f_linear : IsLinearMap (R := Fq) (M := L[X]) (M₂ := L[X])
    (f := fun inner_p ↦ f.comp inner_p)) :
    IsLinearMap (R := Fq) (M := L) (M₂ := L) (f := fun x ↦ f.eval x) := by
  constructor
  · intro x y
    have h_comp_add := h_f_linear.map_add
    have h_spec := h_comp_add (C x) (C y)
    have h_lhs_simp : f.comp (C x + C y) = C (f.eval (x + y)) := by
      rw [←Polynomial.C_add, Polynomial.comp_C]
    have h_rhs_simp : f.comp (C x) + f.comp (C y) = C (f.eval x + f.eval y) := by
      rw [Polynomial.comp_C, Polynomial.comp_C, Polynomial.C_add]
    rw [h_lhs_simp, h_rhs_simp] at h_spec
    exact (Polynomial.C_injective) h_spec
  · intro k x
    have h_comp_smul := h_f_linear.map_smul
    have h_spec := h_comp_smul k (C x)
    have h_lhs_simp : f.comp (k • C x) = C (f.eval (k • x)) := by
      rw [Polynomial.smul_C, Polynomial.comp_C]
    have h_rhs_simp : k • f.comp (C x) = C (k • f.eval x) := by
      rw [Polynomial.comp_C, Polynomial.smul_C]
    rw [h_lhs_simp, h_rhs_simp] at h_spec
    exact (Polynomial.C_injective) h_spec

/--
Frobenius endomorphism interaction with polynomial evaluation.
(aeval x f)^|Fq| = aeval (x^|Fq|) f
-/
theorem aeval_pow_card_eq_aeval_pow_card {Fq K : Type*} [Field Fq] [Fintype Fq]
    [CommRing K] [Algebra Fq K] [Fact (Nat.Prime (ringChar Fq))] [ExpChar K (ringChar Fq)]
    (f : Fq[X]) (x : K) :
    (aeval x f) ^ (Fintype.card Fq) = aeval (x ^ (Fintype.card Fq)) f := by
  let p := ringChar Fq
  let q := Fintype.card Fq
  obtain ⟨k, hp_k, hk⟩ := FiniteField.card Fq p
  have h_q_eq : q = p ^ (k : ℕ) := hk
  -- Prove by polynomial induction on f
  induction f using Polynomial.induction_on with
  | C r =>
    simp only [aeval_C]
    have h_r_pow_q : (r : Fq) ^ q = r := FiniteField.pow_card r
    rw [← map_pow, h_r_pow_q]
  | add pPoly qPoly hpPoly hqPoly =>
    simp only [map_add]
    change (aeval x pPoly + aeval x qPoly) ^ q = aeval (x ^ q) pPoly + aeval (x ^ q) qPoly
    rw [h_q_eq]
    rw [add_pow_expChar_pow (x := aeval x pPoly) (y := aeval x qPoly) (p := p) (n := k)]
    rw [←h_q_eq, hpPoly, hqPoly]
  | monomial n r =>
    simp only [map_mul, aeval_C, map_pow, aeval_X]
    have h_r_pow_q : (r : Fq) ^ q = r := FiniteField.pow_card r
    rw [mul_pow]
    rw [←map_pow, h_r_pow_q, ← pow_mul, ←pow_mul, mul_comm (n + 1) q]

/--
Iterated Frobenius endomorphism interaction with polynomial evaluation.
(aeval x f)^(|Fq|^n) = aeval (x^|Fq|^n) f
-/
theorem aeval_pow_card_pow_eq_aeval_pow_card_pow {Fq K : Type*} [Field Fq] [Fintype Fq]
    [CommRing K] [Algebra Fq K] [Fact (Nat.Prime (ringChar Fq))] [ExpChar K (ringChar Fq)]
    (f : Fq[X]) (x : K) (n : ℕ) :
    (aeval x f) ^ ((Fintype.card Fq) ^ n) = aeval (x ^ ((Fintype.card Fq) ^ n)) f := by
  let q := Fintype.card Fq
  induction n with
  | zero =>
    simp only [pow_zero, pow_one]
  | succ m ih =>
    calc (aeval x f) ^ (q ^ (m + 1))
      _ = (aeval x f) ^ (q ^ m * q) := by
        rw [pow_succ, mul_comm]
      _ = ((aeval x f) ^ (q ^ m)) ^ q := by rw [pow_mul]
      _ = (aeval (x ^ (q ^ m)) f) ^ q := by rw [ih]
      _ = aeval ((x ^ (q ^ m)) ^ q) f := by
        exact aeval_pow_card_eq_aeval_pow_card f (x ^ (q ^ m))
      _ = aeval (x ^ (q ^ m * q)) f := by rw [pow_mul]
      _ = aeval (x ^ (q ^ (m + 1))) f := by
        rw [pow_succ]

end FrobeniusPolynomialIdentity

section FrobeniusPolynomialDivisibility
omit [Fintype Fq] in
/-- **Lemma 1: Polynomial Divisibility of Powers**
If `k` divides `n`, then `X^k - 1` divides `X^n - 1`.
This is the polynomial version of `a | b => x^a - 1 | x^b - 1`.
-/
theorem X_pow_sub_one_dvd_X_pow_sub_one_of_dvd (k n : ℕ) (h_dvd : k ∣ n) :
    (X ^ k - 1 : Fq[X]) ∣ (X ^ n - 1) := by
  obtain ⟨r, rfl⟩ := h_dvd
  rw [pow_mul]
  exact sub_one_dvd_pow_sub_one (X ^ k) r

/--
**Lemma 2: Frobenius Divisibility Transitivity**
If `d` divides `n`, then `X^(q^d) - X` divides `X^(q^n) - X`.
This allows us to say: "If a poly divides the small Frobenius, it divides the big one."
-/
theorem X_pow_card_pow_dvd_X_pow_card_pow_of_dvd (d n : ℕ) (h_dvd : d ∣ n) :
    let q := Fintype.card Fq
    (X ^ (q ^ d) - X : Fq[X]) ∣ (X ^ (q ^ n) - X) := by
  let q := Fintype.card Fq
  have h_q_gt_1 : 1 < q := Fintype.one_lt_card
  have h_exp_dvd : q ^ d - 1 ∣ q ^ n - 1 := by
    obtain ⟨k, rfl⟩ := h_dvd
    rw [pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one _ _

  have h_poly_div : (X ^ (q ^ d - 1) - 1) ∣ (X ^ (q ^ n - 1) - 1 : Fq[X]) :=
    X_pow_sub_one_dvd_X_pow_sub_one_of_dvd (q ^ d - 1) (q ^ n - 1) h_exp_dvd

  have h_mul_X : X * (X ^ (q ^ d - 1) - 1) ∣ X * (X ^ (q ^ n - 1) - 1 : Fq[X]) :=
    mul_dvd_mul_left X h_poly_div
  have h_qd_pos : 0 < q ^ d := by
    have h_res := Nat.one_le_pow (m := q) (n := d) (h := by omega)
    omega
  have h_qn_pos : 0 < q ^ n := by
    have h_res := Nat.one_le_pow (m := q) (n := n) (h := by omega)
    omega

  conv_lhs at h_mul_X =>
    rw [mul_sub, mul_one, mul_comm, ←pow_succ]; simp only [Nat.sub_add_cancel h_qd_pos]
  conv_rhs at h_mul_X =>
    rw [mul_sub, mul_one, mul_comm, ←pow_succ]; simp only [Nat.sub_add_cancel h_qn_pos]
  exact h_mul_X

/--
**Lemma 3: Irreducible Divides Own Frobenius (The Base Case)**
An irreducible polynomial `p` of degree `d` divides `X^(q^d) - X`.
Proof:
1. Consider the extension `K = Fq[x]/(p)`.
2. The group of units `K*` has order `q^d - 1`.
3. So every element `α` satisfies `α^(q^d - 1) = 1` (if `α ≠ 0`).
4. Thus `α^(q^d) = α` for all `α`.
5. `X^(q^d) - X` has `root p` as a root.
6. Since `p` is the minimal polynomial of its root, `p` divides the target.
-/
theorem irreducible_dvd_X_pow_card_pow_sub_X (p : Fq[X]) (hp_irr : Irreducible p) :
    let q := Fintype.card Fq
    let d := p.natDegree
    p ∣ (X ^ (q ^ d) - X) := by
  let q := Fintype.card Fq
  let d := p.natDegree

  -- 1. Construct the field extension K = Fq[X]/(p)
  let K := AdjoinRoot p
  letI : Fintype K := by
    dsimp only [K]
    have hp_ne_zero : p ≠ 0 := Irreducible.ne_zero hp_irr
    let pb := AdjoinRoot.powerBasis hp_ne_zero
    letI : Module.Finite Fq (AdjoinRoot p) := PowerBasis.finite pb
    haveI : Finite (AdjoinRoot p) := by
      have : Module.finrank Fq (AdjoinRoot p) = pb.dim := PowerBasis.finrank pb
      exact Finite.of_equiv (Fin pb.dim →₀ Fq) (pb.basis.repr.toEquiv.symm)
    exact Fintype.ofFinite (AdjoinRoot p)
  haveI : Fact (Irreducible p) := ⟨hp_irr⟩

  -- 2. The size of K is q^d
  have h_card_K : Fintype.card K = q ^ d := by
    dsimp only [K]
    rw [Module.card_eq_pow_finrank (K := Fq) (V := AdjoinRoot p)]
    have hp_ne_zero : p ≠ 0 := Irreducible.ne_zero hp_irr
    let pb := AdjoinRoot.powerBasis hp_ne_zero
    rw [PowerBasis.finrank pb]
    rfl
  -- 3. Let α be the root of p in K
  let α := AdjoinRoot.root p
  -- 4. Show α is a root of (X^(q^d) - X)
  have h_alpha_is_root : eval₂ (algebraMap Fq K) α (X ^ (q ^ d) - X) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_X]
    have h_pow_card_eq_self (x : K) : x ^ (Fintype.card K) = x :=
      FiniteField.pow_card x
    rw [h_card_K] at h_pow_card_eq_self
    rw [h_pow_card_eq_self α, sub_self]
  -- 5. Conclusion: p is the minimal polynomial of α, so it divides any poly having α as root.
  have hp_ne_zero : p ≠ 0 := Irreducible.ne_zero hp_irr
  have h_minpoly_dvd : minpoly Fq α ∣ X ^ (q ^ d) - X :=
    minpoly.dvd Fq α h_alpha_is_root
  have h_minpoly_eq : minpoly Fq α = p * (C p.leadingCoeff⁻¹) := by
    rw [AdjoinRoot.minpoly_root hp_ne_zero]
  rw [h_minpoly_eq] at h_minpoly_dvd
  exact dvd_trans (dvd_mul_right p (C p.leadingCoeff⁻¹)) h_minpoly_dvd

/--
**Theorem: The Rabin Condition (One Direction)**
If `p` is irreducible, and `p` divides `X^(q^n) - X`, then `deg(p)` divides `n`.
-/
theorem degree_dvd_of_irreducible_dvd_X_pow_card_pow_sub_X
    [Fact (Nat.Prime (ringChar Fq))]
    (p : Fq[X]) (hp_irr : Irreducible p) (n : ℕ)
    (h_dvd : p ∣ (X ^ ((Fintype.card Fq) ^ n) - X)) :
    p.natDegree ∣ n := by
  let q := Fintype.card Fq
  let d := p.natDegree

  -- 1. Construct extension K
  let K := AdjoinRoot p
  haveI : Fact (Irreducible p) := ⟨hp_irr⟩
  -- Establish that K is a Fintype (needed for group order arguments)
  letI : Fintype K := by
    dsimp only [K]
    have hp_ne_zero : p ≠ 0 := Irreducible.ne_zero hp_irr
    let pb := AdjoinRoot.powerBasis hp_ne_zero
    letI : Module.Finite Fq (AdjoinRoot p) := PowerBasis.finite pb
    haveI : Finite (AdjoinRoot p) := by
      exact Finite.of_equiv (Fin pb.dim →₀ Fq) (pb.basis.repr.toEquiv.symm)
    exact Fintype.ofFinite (AdjoinRoot p)
  -- The size of K is q^d
  have h_card_K : Fintype.card K = q ^ d := by
    dsimp only [K]
    rw [Module.card_eq_pow_finrank (K := Fq) (V := AdjoinRoot p)]
    have hp_ne_zero : p ≠ 0 := Irreducible.ne_zero hp_irr
    let pb := AdjoinRoot.powerBasis hp_ne_zero
    rw [PowerBasis.finrank pb]
    rfl

  -- 2. α (root of p) must satisfy α^(q^n) = α
  let α := AdjoinRoot.root p
  have h_root : eval₂ (algebraMap Fq K) α (X ^ (q ^ n) - X) = 0 :=
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (f := algebraMap Fq K) (h := h_dvd)
      (h0 := AdjoinRoot.eval₂_root p)

  rw [eval₂_sub, eval₂_X_pow, eval₂_X, sub_eq_zero] at h_root

  -- 3. If α^(q^n) = α, then x^(q^n) = x for ALL x ∈ K.

  have h_fixes_all (x : K) : x ^ (q ^ n) = x := by
    induction x using AdjoinRoot.induction_on with
    | ih f =>
      rw [← AdjoinRoot.aeval_eq f]
      letI : ExpChar K (ringChar Fq) := by
        apply instExpCharOfAlgebra (h_ringChar_Fq_pos := by
          exact CharP.ringChar_ne_zero_of_finite Fq)
      have h_iterated := aeval_pow_card_pow_eq_aeval_pow_card_pow (Fq := Fq) (K := K) f (x := α) n
      rw [h_iterated, h_root]

  -- 4. If x^(q^n) = x for all x ∈ K, then (q^d - 1) | (q^n - 1).
  have h_group_order : q ^ d - 1 ∣ q ^ n - 1 := by
    have h_units_pow_eq_one : ∀ u : Kˣ, u ^ (q ^ n - 1) = 1 := by
      intro u
      have h_u_pow : (u : K) ^ (q ^ n) = (u : K) := h_fixes_all u
      rw [← Units.val_one]
      have h_ne_zero : (u : K) ≠ 0 := Units.ne_zero u
      have h_mul_right_inj := mul_right_inj (a := u) (b := u ^ (q ^ n - ↑1)) (c := 1)
      simp only [Units.val_one]
      rw [←h_mul_right_inj, mul_comm, ←pow_succ, Nat.sub_one_add_one (h := by
        exact Ne.symm (NeZero.ne' (q ^ n)))]
      simp only [mul_one]
      simp only at h_u_pow
      rw [←Units.val_pow_eq_pow_val] at h_u_pow
      exact Units.ext h_u_pow
    have h_exponent_dvd : Monoid.exponent Kˣ ∣ q ^ n - 1 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one h_units_pow_eq_one
    have h_order_K : Fintype.card Kˣ = q ^ d - 1 := by
      rw [Fintype.card_units, h_card_K]
    have h_exp_eq_order : Monoid.exponent Kˣ = Fintype.card Kˣ := by
      rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card]
    rw [h_exp_eq_order, h_order_K] at h_exponent_dvd
    exact h_exponent_dvd
  -- 5. (q^d - 1) | (q^n - 1) implies d | n.
  apply Nat.dvd_of_pow_sub_one_dvd_pow_sub_one (hq := Fintype.one_lt_card) (h_dvd := h_group_order)

/--
**Fundamental Theorem of Irreducible Polynomials over Finite Fields:**
For an irreducible polynomial q over a finite field R:
`q | X^(|R|^n) - X`  ↔  `deg(q) | n`. -/
lemma irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd {R : Type*} [Field R]
    [Fact (Nat.Prime (ringChar R))]
    [Fintype R] (n : ℕ) (q : Polynomial R) (hq_irr : Irreducible q) :
    q ∣ (X ^ ((Fintype.card R) ^ n) - X) ↔ q.natDegree ∣ n := by
  constructor
  · intro h_dvd
    apply degree_dvd_of_irreducible_dvd_X_pow_card_pow_sub_X q hq_irr n h_dvd

  · intro h_deg_dvd
    have h_base := irreducible_dvd_X_pow_card_pow_sub_X q hq_irr
    apply dvd_trans h_base
    apply X_pow_card_pow_dvd_X_pow_card_pow_of_dvd q.natDegree n h_deg_dvd

end FrobeniusPolynomialDivisibility
end Polynomial
