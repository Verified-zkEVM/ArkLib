/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.BinaryField.BF128Ghash.XPowTwoPowGcdCertificate

/-!
# BinaryField128Ghash

Define `GF(2^128)` as a single field extension over `GF(2)` using the GHASH polynomial
from AES-GCM: `P(X) = X^128 + X^7 + X^2 + X + 1`.

## Main Definitions

- `ghashPoly`: The defining polynomial `X^128 + X^7 + X^2 + X + 1` over `GF(2)`
- `BF128Ghash`: The field `GF(2^128)` defined as `GF(2)[X]/(ghashPoly)`
- `ghashPoly_irreducible`: The irreducibility of the GHASH polynomial
- `irreducible_of_rabin_128_passed_over_GF2`: The lemma that if the two Rabin conditions
    hold for a degree 128 polynomial, it MUST be irreducible.

## Proof Strategy (Rabin's Irreducibility Test)

For a polynomial `P` of degree `n` over `GF(q)`, `P` is irreducible iff:
1. `P` divides `X^(q^n) - X`
2. `EuclideanDomain.gcd(P, X^(q^(n/l)) - X) = 1` for all prime factors `l` of `n`.

For GHASH (`n=128`, `q=2`), the only prime factor of `128` is `2`.
Thus, we only need to check:
1. `P | (X^(2^128) + X)`   (Note: `-X = +X` in `GF(2)`)
2. `EuclideanDomain.gcd(P, X^(2^64) + X) = 1`

## References
* [NIST-SP-800-38D] Dworkin, M. Recommendation for Block Cipher Modes of Operation:
  Galois/Counter Mode (GCM) and GMAC. NIST Special Publication 800-38D.
  https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

* [Rabin80] Michael O. Rabin. Probabilistic Algorithms in Finite Fields.
  SIAM Journal on Computing, 9(2):273-280, 1980. https://doi.org/10.1137/0209024

-/

namespace BF128Ghash
open Polynomial AdjoinRoot
noncomputable section

/--
**Rabin's Irreducibility Test (Specialized for Degree 128)**

This lemma proves that if the two Rabin conditions hold for a degree 128 polynomial,
it MUST be irreducible. It formalizes Lemma 1 from Rabin's paper.

Hypotheses:
1. `h_deg`: P has degree 128.
2. `h_trace`: P divides X^(2^128) - X (in GF(2), +X and -X are the same).
3. `h_gcd`: EuclideanDomain.gcd(P, X^(2^64) - X) = 1.
-/
lemma irreducible_of_rabin_128_passed_over_GF2 (P : Polynomial (ZMod 2))
    (h_deg : P.natDegree = 128)
    (h_trace : P ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 128) + X))
    (h_gcd : EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 64) + X) P = 1) :
    Irreducible P := by
  have h_ringCharZmod2 : ringChar (ZMod 2) = 2 := by exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by exact Fact.mk (by
    rw [h_ringCharZmod2]; exact Nat.prime_two)

  -- Proof by Contradiction: Assume P is reducible.
  by_contra h_red

  -- 1. Use our new helper lemma: There exists a factor q with deg(q) ≤ 64
  rcases exists_factor_le_64_of_reducible P h_deg h_red
    with ⟨q, h_q_irr, h_q_dvd_P, h_q_deg_le⟩

  -- 2. Transitivity: q | P and P | (X^(2^128) + X) implies q | (X^(2^128) + X).
  have h_q_dvd_trace : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 128) + X) :=
    dvd_trans h_q_dvd_P h_trace

  -- 3. In Finite Fields, if irreducible q | (X^(p^n) - X), then deg(q) | n.
  -- The standard theorem is `irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd`.
  -- Since we are in ZMod 2, we rewrite (X^(2^128) + X) to (X^(2^128) - X).
  rw [←CharTwo.sub_eq_add] at h_q_dvd_trace

  -- Apply the theorem: q | (X^(2^128) - X) -> deg(q) | 128
  have h_deg_dvd_128 : q.natDegree ∣ 128 := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd (R := ZMod 2)
      (n := 128) (q := q) (hq_irr := h_q_irr).mp h_q_dvd_trace

  -- 4. Arithmetic Logic: deg(q) ≤ 64 and deg(q) | 128 implies deg(q) | 64.
  have h_deg_dvd_64 : q.natDegree ∣ 64 := by
    -- 128 = 64 * 2. If d | 64*2 and d <= 64, then d | 64.
    have h_eq : 128 = 64 * 2 := by norm_num
    rw [h_eq] at h_deg_dvd_128
    have h_128 : 128 = 2^7 := by norm_num
    rw [← h_eq, h_128] at h_deg_dvd_128
    -- 1. Use the fact that 2 is prime to characterize divisors of 2^7
    have h_prime_two : Nat.Prime 2 := Nat.prime_two
    -- 2. Since q.natDegree | 2^7, q.natDegree must be of the form 2^k
    --    (requires import Mathlib.Data.Nat.Prime)
    obtain ⟨k, ⟨h_k_le_7, hk_eq⟩⟩ := (Nat.dvd_prime_pow h_prime_two).mp h_deg_dvd_128
    -- 3. Substitute q.natDegree = 2^k into the inequality q.natDegree ≤ 64
    rw [hk_eq] at h_q_deg_le
    -- 4. Recognize 64 as 2^6
    have h_64_eq : 64 = 2^6 := by rfl
    rw [h_64_eq] at h_q_deg_le ⊢
    -- 5. From 2^k ≤ 2^6, implies k ≤ 6 (monotonicity of pow)
    --    Note: We need 2 > 1 for this implication, which is true.
    have h_k_le_6 : k ≤ 6 := by
      rwa [Nat.pow_le_pow_iff_right (Nat.one_lt_two)] at h_q_deg_le
    -- 6. If k ≤ 6, then 2^k divides 2^6
    rw [hk_eq]
    exact Nat.pow_dvd_pow 2 h_k_le_6

  -- 5. Applying the theorem in reverse:
  -- Since deg(q) | 64, q must divide (X^(2^64) - X).
  have h_q_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 64) - X) := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd (R := ZMod 2) (n := 64)
      (q := q) (hq_irr := h_q_irr).mpr h_deg_dvd_64
  -- 6. Contradiction.
  -- q divides P (from hypothesis).
  -- q divides (X^(2^64) + X) (rewriting -X back to +X).
  rw [CharTwo.sub_eq_add] at h_q_dvd_check
  -- Therefore q divides their GCD.
  have h_q_dvd_gcd : q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 64) + X) P :=
    EuclideanDomain.dvd_gcd h_q_dvd_check h_q_dvd_P
  -- But the GCD is 1 (by hypothesis `h_gcd`).
  rw [h_gcd] at h_q_dvd_gcd
  -- So q | 1. Irreducible polynomials cannot divide 1 (they are not units).
  -- This provides the final False.
  exact (irreducible_iff.mp h_q_irr).1 (isUnit_of_dvd_one h_q_dvd_gcd)

/-- `ghashPoly` is irreducible, using Rabin's Irreducibility Test:
- `X_pow_2_pow_128_eq`: X^(2^128) = X (mod ghashPoly)
- `rabin_gcd_condition_gHashPoly`: EuclideanDomain.gcd(X^(2^64) + X, ghashPoly) = 1 -/
theorem ghashPoly_irreducible : Irreducible ghashPoly := by
  letI : GCDMonoid (Polynomial (ZMod 2)) := by apply EuclideanDomain.gcdMonoid
  apply irreducible_of_rabin_128_passed_over_GF2
  · exact ghashPoly_natDegree
  · -- Trace Condition: ghashPoly | X^(2^128) + X
    have h_ghashPoly_monic : ghashPoly.Monic := by exact ghashPoly_monic
    rw [← EuclideanDomain.mod_eq_zero]
    -- (A + B) % P = 0 ↔ (A % P + B % P) % P = 0
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
    have h_X_mod_ghashPoly_eq_X : X % ghashPoly = X := by
      rw [Polynomial.mod_eq_self_iff (hq0 := by exact ghashPoly_ne_zero)]
      · simp only [degree_X, ghashPoly_degree, Nat.one_lt_ofNat]
    -- Simplify X % P -> X (since deg(X) = 1 < 128)
    rw [X_pow_2_pow_128_eq, add_comm]
    rw [X_mod_ghashPoly]
    simp only [CharTwo.add_self_eq_zero, EuclideanDomain.zero_mod]
  · -- GCD Condition: ⊢ EuclideanDomain.gcd (X ^ 2 ^ 64 + X) ghashPoly = 1
    apply rabin_gcd_condition_gHashPoly

-- Register the Fact instance so other files can use it automatically
instance : Fact (Irreducible ghashPoly) := ⟨ghashPoly_irreducible⟩

set_option linter.dupNamespace false in
/-- GF(2^128) as the quotient field GF(2)[X]/(P(X)) where P is the GHASH polynomial. -/
abbrev BF128Ghash : Type := AdjoinRoot ghashPoly

/-- BF128Ghash is a field. -/
instance instFieldBF128Ghash : Field BF128Ghash := AdjoinRoot.instField

/-- BF128Ghash is a commutative ring. -/
instance instCommRingBF128Ghash : CommRing BF128Ghash := inferInstance

/-- BF128Ghash is nontrivial. -/
instance instNontrivialBF128Ghash : Nontrivial BF128Ghash := inferInstance

/-- BF128Ghash is inhabited. -/
instance : Inhabited BF128Ghash := ⟨0⟩

/-- BF128Ghash is an algebra over GF(2). -/
instance : Algebra (ZMod 2) BF128Ghash := AdjoinRoot.instAlgebra ghashPoly

/-- BF128Ghash has characteristic 2. -/
instance : CharP BF128Ghash 2 := by
  haveI : CharP (ZMod 2) 2 := inferInstance
  apply charP_of_injective_algebraMap' (ZMod 2) 2

/-- The canonical embedding of GF(2) into BF128Ghash. -/
def ofGF2 : ZMod 2 →+* BF128Ghash := algebraMap (ZMod 2) BF128Ghash

/-- The generator of the field (root of the GHASH polynomial). -/
def root : BF128Ghash := AdjoinRoot.root ghashPoly

/-- The root satisfies the GHASH polynomial equation:
    root^128 + root^7 + root^2 + root + 1 = 0 -/
theorem root_satisfies_poly : root^128 + root^7 + root^2 + root + 1 = 0 := by
  unfold root ghashPoly
  have h := AdjoinRoot.eval₂_root ghashPoly
  simp only [ghashPoly, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  exact h

/-- BF128Ghash is a finite type. -/
instance : Fintype BF128Ghash := by
  have h_ghashPoly_ne_zero : ghashPoly ≠ 0 := Irreducible.ne_zero ghashPoly_irreducible
  let pb := AdjoinRoot.powerBasis h_ghashPoly_ne_zero
  letI : Module.Finite (ZMod 2) BF128Ghash := PowerBasis.finite pb
  haveI : Finite BF128Ghash := by
    have : Module.finrank (ZMod 2) BF128Ghash = pb.dim := PowerBasis.finrank pb
    exact Finite.of_equiv (Fin pb.dim →₀ ZMod 2) (pb.basis.repr.toEquiv.symm)
  exact Fintype.ofFinite BF128Ghash

/-- The cardinality of BF128Ghash is 2^128. -/
theorem BF128Ghash_card : Fintype.card BF128Ghash = 2^128 := by
  -- Use the fact that AdjoinRoot of an irreducible polynomial of degree d
  -- over a field of size q has cardinality q^d
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := BF128Ghash)]
  -- The finrank is equal to the degree of the polynomial
  have h_ghashPoly_ne_zero : ghashPoly ≠ 0 := Irreducible.ne_zero ghashPoly_irreducible
  let pb := AdjoinRoot.powerBasis h_ghashPoly_ne_zero
  rw [PowerBasis.finrank pb]
  -- pb.dim = ghashPoly.natDegree by definition of AdjoinRoot.powerBasis
  -- We need to show pb.dim = 128
  have h_pb_dim : pb.dim = ghashPoly.natDegree := by
    -- This follows from the definition of AdjoinRoot.powerBasis
    rfl
  rw [h_pb_dim, ghashPoly_natDegree]
  -- Fintype.card (ZMod 2) = 2
  norm_num

end
end BF128Ghash
