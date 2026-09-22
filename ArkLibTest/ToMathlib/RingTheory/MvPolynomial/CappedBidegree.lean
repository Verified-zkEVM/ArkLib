/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree

/-!
# Acceptance tests for polynomials of bounded bidegree with a capped variable

The examples state the point statements for the bidegree map as instances of those for monomial
maps, count capped exponents and compute a dimension, check that the cap is no condition when it
exceeds the bound on the degree, and show that the count on `Fin 2` needs `c ≤ b` and that
surjectivity of the monomial map needs a positive cap.
-/

open MvPolynomial

namespace CappedBidegreeTest

section BidegreePoints

variable {σ k E : Type*} [Field k] [Field E] [Algebra k E] {a b : ℕ}

/-- The coordinate of the point of monomial values at an exponent `m` is the value of the monomial
of exponent `m`. -/
example (x : Option σ → E) (m : bidegreeExponents σ a b) :
    monomialPoint _ x m = aeval x (monomial m.1 (1 : k)) := by
  rw [monomialPoint_apply, aeval_monomial, map_one, one_mul]

/-- Evaluation at the point of monomial values is evaluation after the bidegree map. -/
example (x : Option σ → E) (P : MvPolynomial (bidegreeExponents σ a b) k) :
    aeval (monomialPoint _ x) P = aeval x (bidegreeMap σ k a b P) :=
  aeval_monomialPoint x P

/-- The linear lift of a polynomial of bidegree at most `(a, b)` vanishes at the point of monomial
values of `x` exactly when the polynomial vanishes at `x`. -/
example (x : Option σ → E) (q : MvPolynomial (Option σ) k) (hq : q ∈ restrictBidegree σ k a b) :
    aeval (monomialPoint _ x) (bidegreeLift q hq) = 0 ↔ aeval x q = 0 := by
  rw [aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, bidegreeMap_bidegreeLift]

/-- For positive `a` and `b`, the point of monomial values of `x` lies on the pullback of the
hypersurface `g = 0` along the bidegree map exactly when `g` vanishes at `x`. -/
example (ha : 0 < a) (hb : 0 < b) (g : MvPolynomial (Option σ) k) (x : Option σ → E) :
    monomialPoint _ x ∈ zeroLocus E ((Ideal.span {g}).comap (bidegreeMap σ k a b)) ↔
      aeval x g = 0 := by
  rw [bidegreeMap_eq_monomialMap,
    monomialPoint_mem_zeroLocus_comap_iff (single_mem_bidegreeExponents ha hb), zeroLocus_span]
  simp

/-- For positive `a` and `b`, every point of the zero locus of the kernel of the bidegree map is a
point of monomial values. -/
example (ha : 0 < a) (hb : 0 < b) (z : bidegreeExponents σ a b → E)
    (hz : z ∈ zeroLocus E (RingHom.ker (bidegreeMap σ k a b))) :
    ∃ x : Option σ → E, monomialPoint _ x = z :=
  exists_monomialPoint_eq_of_mem_zeroLocus_ker (single_mem_bidegreeExponents ha hb) hz

/-- For positive `a` and `b`, a point is determined by its point of monomial values. -/
example (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (monomialPoint (E := E) (bidegreeExponents σ a b)) :=
  monomialPoint_injective (single_mem_bidegreeExponents ha hb)

end BidegreePoints

/-- In two further variables with cap `1` on the second, there are `2 * 5 = 10` exponents with
`none`-coordinate at most `1` and degree at most `2`. -/
example : (cappedBidegreeExponents (Fin 2) 1 1 2 1).ncard = 10 := by
  have h := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le 2 1 (by norm_num)
  rw [ncard_cappedBidegreeExponents]
  omega

/-- The corresponding polynomials form a space of dimension `10`. -/
example : Module.finrank ℚ (restrictCappedBidegree (Fin 2) ℚ 1 1 2 1) = 10 := by
  have h := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le 2 1 (by norm_num)
  rw [finrank_restrictCappedBidegree]
  omega

/-- A cap at least the bound on the degree is no condition. -/
example {σ : Type*} (i : σ) (a b : ℕ) :
    cappedBidegreeExponents σ i a b (b + 1) = bidegreeExponents σ a b :=
  cappedBidegreeExponents_eq_bidegreeExponents (Nat.le_succ b)

/-- The bounds of a product of capped polynomials add. -/
example {P Q : MvPolynomial (Option (Fin 2)) ℚ} (hP : P ∈ restrictCappedBidegree (Fin 2) ℚ 1 1 2 1)
    (hQ : Q ∈ restrictCappedBidegree (Fin 2) ℚ 1 0 1 1) :
    P * Q ∈ restrictCappedBidegree (Fin 2) ℚ 1 1 3 2 :=
  mul_mem_restrictCappedBidegree hP hQ

/-- `Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le` needs `c ≤ b`: for `b = 1` and
`c = 3` the cap is no condition, so there are `3` exponents, while `(c + 1) * (2 * b + 2 - c) = 4`
is not `2 * 3`. -/
example : 2 * {e : Fin 2 →₀ ℕ | e.degree ≤ 1 ∧ e 1 ≤ 3}.ncard ≠ (3 + 1) * (2 * 1 + 2 - 3) := by
  have hset : {e : Fin 2 →₀ ℕ | e.degree ≤ 1 ∧ e 1 ≤ 3} = {e | e.degree ≤ 1} :=
    Set.ext fun e ↦
      ⟨And.left, fun he ↦ ⟨he, (Finsupp.le_degree 1 e).trans he |>.trans (by norm_num)⟩⟩
  rw [hset, Finsupp.ncard_setOf_degree_le, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- `monomialMap_cappedBidegreeExponents_surjective` needs `0 < c`: with cap `0` no exponent
involves `some 1`, so the points `0` and `Pi.single (some 1) 1` have the same point of monomial
values, and `X (some 1)` is not in the image. -/
example : ¬Function.Surjective
    (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 1 0)) := by
  intro h
  obtain ⟨P, hP⟩ := h (X (some 1))
  have hpt : monomialPoint (cappedBidegreeExponents (Fin 2) 1 1 1 0) (0 : Option (Fin 2) → ℚ) =
      monomialPoint _ (Pi.single (some 1) 1) := funext fun m ↦ by
    rw [monomialPoint_apply, monomialPoint_apply]
    refine Finsupp.prod_congr fun v hv ↦ ?_
    have hv1 : v ≠ some 1 := by
      rintro rfl
      exact Finsupp.mem_support_iff.mp hv (Nat.le_zero.mp m.2.2.2)
    rw [Pi.single_eq_of_ne hv1, Pi.zero_apply]
  have h0 := aeval_monomialPoint (R := ℚ) (0 : Option (Fin 2) → ℚ) P
  have h1 := aeval_monomialPoint (R := ℚ) (Pi.single (some 1) (1 : ℚ)) P
  rw [hP, aeval_X] at h0 h1
  rw [hpt, h1] at h0
  simp at h0

end CappedBidegreeTest
