/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree

/-!
# Acceptance tests for polynomials of bounded bidegree with a capped variable

The examples state the point statements for the bidegree map and the capped monomial map as
instances of those for monomial maps, count capped exponents and compute a dimension, check that
the cap is no condition when it exceeds the bound on the degree, and show that surjectivity of the
monomial map needs a positive cap. The mixed volume examples compute a small value, write the
mixed volume as `h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))`, compute the mixed volume
of a prism with itself, and show that the closed form needs `c ≤ b`.
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

section CappedBidegreePoints

variable {σ k E : Type*} [Field k] [Field E] [Algebra k E] {i : σ} {a b c : ℕ}

/-- The coordinate of the point of monomial values at a capped exponent `m` is the value of the
monomial of exponent `m`. -/
example (x : Option σ → E) (m : cappedBidegreeExponents σ i a b c) :
    monomialPoint _ x m = aeval x (monomial m.1 (1 : k)) := by
  rw [monomialPoint_apply, aeval_monomial, map_one, one_mul]

/-- Evaluation at the point of monomial values is evaluation after the capped monomial map. -/
example (x : Option σ → E) (P : MvPolynomial (cappedBidegreeExponents σ i a b c) k) :
    aeval (monomialPoint _ x) P = aeval x (monomialMap k _ P) :=
  aeval_monomialPoint x P

/-- The linear lift of a capped polynomial vanishes at the point of monomial values of `x` exactly
when the polynomial vanishes at `x`. -/
example (x : Option σ → E) (q : MvPolynomial (Option σ) k)
    (hq : q ∈ restrictCappedBidegree σ k i a b c) :
    aeval (monomialPoint _ x) (monomialLift (S := cappedBidegreeExponents σ i a b c) q hq) = 0 ↔
      aeval x q = 0 := by
  have hlift := monomialMap_monomialLift (R := k) (S := cappedBidegreeExponents σ i a b c) q hq
  rw [aeval_monomialPoint, hlift]

/-- For positive bounds, the point of monomial values of `x` lies on the pullback of the
hypersurface `g = 0` along the capped monomial map exactly when `g` vanishes at `x`. -/
example (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Option σ) k)
    (x : Option σ → E) :
    monomialPoint _ x ∈ zeroLocus E
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents σ i a b c))) ↔
      aeval x g = 0 := by
  rw [monomialPoint_mem_zeroLocus_comap_iff (single_mem_cappedBidegreeExponents ha hb hc),
    zeroLocus_span]
  simp

/-- For positive bounds, every point of the zero locus of the kernel of the capped monomial map is
a point of monomial values. -/
example (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (z : cappedBidegreeExponents σ i a b c → E)
    (hz : z ∈ zeroLocus E (RingHom.ker (monomialMap k (cappedBidegreeExponents σ i a b c)))) :
    ∃ x : Option σ → E, monomialPoint _ x = z :=
  exists_monomialPoint_eq_of_mem_zeroLocus_ker (single_mem_cappedBidegreeExponents ha hb hc) hz

/-- For positive bounds, a point is determined by its point of capped monomial values. -/
example (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (monomialPoint (E := E) (cappedBidegreeExponents σ i a b c)) :=
  monomialPoint_injective (single_mem_cappedBidegreeExponents ha hb hc)

end CappedBidegreePoints

/-- In two further variables with cap `1` on the second, there are `2 * 5 = 10` exponents with
`none`-coordinate at most `1` and degree at most `2`. -/
example : (cappedBidegreeExponents (Fin 2) 1 1 2 1).ncard = 10 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  rw [ncard_cappedBidegreeExponents]
  omega

/-- The corresponding polynomials form a space of dimension `10`. -/
example : Module.finrank ℚ (restrictCappedBidegree (Fin 2) ℚ 1 1 2 1) = 10 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
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

section MixedVolume

/-- The mixed volume of the prism for `(1, 1, 0)` and two prisms for `(1, 2, 1)` is
`1 * 3 + 2 * 1 * (1 * 1 + 0 * 1) = 5`. -/
example : cappedBidegreeMixedVolume 1 1 0 1 2 1 = 5 := rfl

/-- For `c ≤ b`, the mixed volume is `h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))`. -/
example {h j r a b c : ℕ} (hcb : c ≤ b) :
    cappedBidegreeMixedVolume h j r a b c =
      h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c)) := by
  rw [cappedBidegreeMixedVolume_eq hcb, mul_assoc h, Nat.mul_sub, sq, mul_comm c (2 * b)]

/-- The mixed volume of a prism with itself is `3!` times its volume `a * c * (2 * b - c) / 2`. -/
example {a b c : ℕ} (hcb : c ≤ b) :
    cappedBidegreeMixedVolume a b c a b c = 3 * (a * c * (2 * b - c)) := by
  rw [cappedBidegreeMixedVolume, cappedDegreeMixedVolume_self hcb]
  ring

/-- `cappedBidegreeMixedVolume_eq` needs `c ≤ b`: for `(b, c) = (1, 3)` the mixed volume of the
prism for `(1, 0, 0)` and two prisms for `(1, 1, 3)` is `3`, while the closed form gives `0`. -/
example :
    cappedBidegreeMixedVolume 1 0 0 1 1 3 ≠ 1 * 3 * (2 * 1 - 3) + 2 * 1 * (0 * 3 + 0 * 0) := by
  decide

end MixedVolume

end CappedBidegreeTest
