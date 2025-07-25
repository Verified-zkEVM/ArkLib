/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian

/-!
# Frobenius polynomial identities
-/

namespace Polynomial

section FinFieldPolyHelper
variable {Fq : Type*} [Field Fq] [Fintype Fq]

section FieldVanishingPolynomialEquality
-- NOTE : We lift `∏_{c ∈ Fq} (X - c) = X^q - X` from `Fq[X]` to `L[X]`,
-- then achieve a generic version `∏_{c ∈ Fq} (p - c) = p^q - p` for any `p` in `L[X]`

/--
The polynomial `X^q - X` factors into the product of `(X - c)` ∀ `c` ∈ `Fq`,
i.e. `∏_{c ∈ Fq} (X - c) = X^q - X`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X (h_Fq_card_gt_1 : Fintype.card Fq > 1):
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  -- Step 1 : Setup - Define P and Q for clarity.
  set P : Fq[X] := ∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)
  set Q : Fq[X] := Polynomial.X^(Fintype.card Fq) - Polynomial.X

  -- We will prove P = Q by showing they are both monic and have the same roots.

  -- Step 2 : Prove P and Q are monic.
  have hP_monic : P.Monic := by
    apply Polynomial.monic_prod_of_monic
    intro c _
    exact Polynomial.monic_X_sub_C c

  have hQ_monic : Q.Monic := by
    apply Polynomial.monic_X_pow_sub
    -- The condition is that degree(X) < Fintype.card Fq
    rw [Polynomial.degree_X]
    exact_mod_cast h_Fq_card_gt_1

  have h_roots_P : P.roots = (Finset.univ : Finset Fq).val := by
    apply Polynomial.roots_prod_X_sub_C
  -- The roots of Q are, by Fermat's Little Theorem, also all elements of Fq.
  have h_roots_Q : Q.roots = (Finset.univ : Finset Fq).val := by
    exact FiniteField.roots_X_pow_card_sub_X Fq

  -- Step 3 : Prove P and Q have the same set of roots.
  -- We show that both root sets are equal to `Finset.univ`.
  have h_roots_eq : P.roots = Q.roots := by
    rw [h_roots_P, h_roots_Q]

  have hP_splits : P.Splits (RingHom.id Fq) := by
    -- ⊢ Splits (RingHom.id Fq) (∏ c ∈ Finset.univ, X - C c)
    apply Polynomial.splits_prod
    intro c _
    apply Polynomial.splits_X_sub_C

  have hQ_card_roots : Q.roots.card = Fintype.card Fq := by
    rw [h_roots_Q]
    exact rfl

  have natDegree_Q : Q.natDegree = Fintype.card Fq := by
    unfold Q
    have degLt : (X : Fq[X]).natDegree < ((X : Fq[X]) ^ Fintype.card Fq).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_X]
      exact h_Fq_card_gt_1
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt degLt]
    rw [Polynomial.natDegree_X_pow]

  have hQ_splits : Q.Splits (RingHom.id Fq) := by
    unfold Q
    apply Polynomial.splits_iff_card_roots.mpr
    -- ⊢ (X ^ Fintype.card Fq - X).roots.card = (X ^ Fintype.card Fq - X).natDegree
    rw [hQ_card_roots]
    rw [natDegree_Q]

  -- 4. CONCLUSION : Since P and Q are monic, split, and have the same roots, they are equal.
  have hP_eq_prod : P = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) P.roots).prod := by
    apply Polynomial.eq_prod_roots_of_monic_of_splits_id hP_monic hP_splits
  have hQ_eq_prod : Q = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) Q.roots).prod := by
    apply Polynomial.eq_prod_roots_of_monic_of_splits_id hQ_monic hQ_splits
  rw [hP_eq_prod, hQ_eq_prod, h_roots_eq]

variable {L : Type*} [CommRing L] [Algebra Fq L]
/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X_in_L
  (h_Fq_card_gt_1 : Fintype.card Fq > 1):
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (algebraMap Fq L c))) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  -- Let `f` be the ring homomorphism from `Fq` to `L`.
  let f := algebraMap Fq L

  -- The goal is an equality in L[X]. We will show that this equality is just
  -- the "mapped" version of the equality in Fq[X], which we already proved.

  -- First, show the LHS of our goal is the mapped version of the LHS of the base theorem.
  have h_lhs_map : (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (f c))) =
      Polynomial.map f (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) := by
    -- `map` is a ring homomorphism, so it distributes over products, subtraction, X, and C.
    rw [Polynomial.map_prod]
    congr! with c
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

  -- Next, show the RHS of our goal is the mapped version of the RHS of the base theorem.
  have h_rhs_map : (Polynomial.X^(Fintype.card Fq) - Polynomial.X) =
      Polynomial.map f (Polynomial.X^(Fintype.card Fq) - Polynomial.X) := by
    -- `map` also distributes over powers.
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]

  -- Now, we can rewrite our goal using these facts.
  rw [h_lhs_map, h_rhs_map]
  -- ⊢ map f (∏ c, (X - C c)) = map f (X ^ Fintype.card Fq - X)

  -- The goal is now `map f (LHS_base) = map f (RHS_base)`.
  -- This is true if `LHS_base = RHS_base`, which is exactly our previous theorem.
  rw [prod_X_sub_C_eq_X_pow_card_sub_X h_Fq_card_gt_1]

/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L
  (h_Fq_card_gt_1 : Fintype.card Fq > 1) (p : L[X]):
  (∏ c ∈ (Finset.univ : Finset Fq), (p - Polynomial.C (algebraMap Fq L c))) =
    p^(Fintype.card Fq) - p := by

  -- The strategy is to take the known identity for the polynomial X and substitute
  -- X with the arbitrary polynomial p. This substitution is formally known as
  -- polynomial composition (`Polynomial.comp`).

  -- Let `q` be the cardinality of the field Fq for brevity.
  let q := Fintype.card Fq

  -- From the previous theorem, we have the base identity in L[X]:
  -- `(∏ c, (X - C c)) = X^q - X`
  let base_identity := prod_X_sub_C_eq_X_pow_card_sub_X_in_L (L := L) h_Fq_card_gt_1

  -- `APPROACH : f = g => f.comp(p) = g.comp(p)`
  have h_composed_eq : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p
    = ((X:L[X])^q - X).comp p := by
    rw [base_identity]

  -- Now, we simplify the left-hand side (LHS) and right-hand side (RHS) of `h_composed_eq`
  -- to show they match the goal.

  -- First, simplify the LHS : `(∏ c, (X - C c)).comp(p)`
  have h_lhs_simp : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p =
                     ∏ c ∈ (Finset.univ : Finset Fq), (p - C (algebraMap Fq L c)) := by
    -- Use the theorem that composition distributes over products
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro c _
    --⊢ (X - C ((algebraMap Fq L) c)).comp p = p - C ((algebraMap Fq L) c)
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]

  -- Next, simplify the RHS : `(X^q - X).comp(p)`
  have h_rhs_simp : ((X:L[X])^q - X).comp p = p^q - p := by
    -- Composition distributes over subtraction and powers.
    rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp]

  -- By substituting our simplified LHS and RHS back into `h_composed_eq`,
  -- we arrive at the desired goal.
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
  {h_Fq_char_prime : Fact (Nat.Prime (ringChar Fq))} (f g : Fq[X]) :
    (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The Freshman's Dream `(a+b)^e = a^e + b^e` holds if `e` is a power of the characteristic.
  -- First, we establish that `q = p^n` where `p` is the characteristic of `Fq`.
  let p := ringChar Fq
  have h_p_prime : Fact p.Prime := h_Fq_char_prime
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p
  rw [hn]
  -- The polynomial ring `Fq[X]` also has characteristic `p`.
  haveI : CharP Fq[X] p := Polynomial.charP
  -- Apply the general "Freshman's Dream" theorem for prime powers.
  exact add_pow_expChar_pow f g p ↑n

variable {L : Type*} [CommRing L] [Algebra Fq L] [Nontrivial L]

/--
The lifted Frobenius identity for polynomials in `L[X]`, where `L` is an `Fq`-algebra.
The exponent `q` is the cardinality of the base field `Fq`.
-/
theorem frobenius_identity_in_algebra {h_Fq_char_prime : Fact (Nat.Prime (ringChar Fq))}
  (f g : L[X]) : (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The logic is identical. The key is that `L` inherits the characteristic of `Fq`.
  let p := ringChar Fq
  haveI : Fact p.Prime := h_Fq_char_prime
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p

  -- Rewrite the goal using `q = p^n`.
  rw [hn]

  -- Since `L` is an `Fq`-algebra, it must have the same characteristic `p`.
  have h_charP_Fq : CharP Fq p := by
    simp only [p]
    exact ringChar.charP Fq

  have h_charP_L : CharP L p := by
    have h_inj : Function.Injective (algebraMap Fq L) := by
      exact RingHom.injective (algebraMap Fq L) -- L must be nontrivial
    have h_charP_L := (RingHom.charP_iff (A := L) (f := algebraMap Fq L)
      (H := h_inj) p).mp h_charP_Fq
    exact h_charP_L
  -- The polynomial ring `L[X]` also has characteristic `p`.
  have h_charP_L_X : CharP L[X] p := by
    exact Polynomial.charP
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
    -- ⊢ eval (x + y) f = eval x f + eval y f
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
end FrobeniusPolynomialIdentity

end FinFieldPolyHelper

end Polynomial
