/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SquarefreeSupport

/-!
# Certified inverse-Frobenius contraction

The executable contraction takes its coefficient operation explicitly. It never
reads a field cardinality or enumerates field elements. Correctness assumes that
the supplied operation inverts the characteristic power. This is the descent
kernel for recursive multiplicity decomposition, not the recursive algorithm.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Divide exponents by `p` and apply the supplied executable inverse Frobenius
to the retained coefficients. No cardinality metadata is consulted. -/
def contractWith (p : ℕ) (inverse : F → F) (f : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray <| Array.ofFn fun i : Fin (f.natDegree / p + 1) =>
    inverse (f.coeff (i * p))

/-- Coefficient specification of the concrete array contraction. -/
theorem coeff_contractWith (p : ℕ) (inverse : F → F) (f : CPolynomial F) (i : ℕ) :
    (contractWith p inverse f).coeff i =
      if i < f.natDegree / p + 1 then inverse (f.coeff (i * p)) else 0 := by
  rw [contractWith, CPolynomial.coeff_ofArray]
  simp only [Array.getD, Array.size_ofFn]
  split <;> simp_all

variable (p : ℕ) [Fact p.Prime] [CharP F p]

omit [BEq F] [LawfulBEq F] in
/-- An explicit inverse-power certificate supplies the mathematical perfect-ring
instance used in proofs. Its construction is erased from executable contraction. -/
private theorem frobenius_surjective (inverse : F → F)
    (hinverse : ∀ a, inverse a ^ p = a) : Function.Surjective (frobenius F p) := by
  intro a
  exact ⟨inverse a, hinverse a⟩

/-- The supplied coefficient operation gives exact reconstruction whenever the
input derivative is zero. No finite-type or cardinality assumption is required. -/
theorem contractWith_pow_eq (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hderiv : f.derivative = 0) :
    contractWith p inverse f ^ p = f := by
  let : PerfectRing F p := PerfectRing.ofSurjective F p (frobenius_surjective p inverse hinverse)
  have heq (a : F) : inverse a = (frobeniusEquiv F p).symm a := by
    apply (frobeniusEquiv F p).injective
    rw [RingEquiv.apply_symm_apply, frobeniusEquiv_def, hinverse]
  have hpoly : (contractWith p inverse f).toPoly =
      (Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom := by
    ext i
    rw [← CPolynomial.coeff_toPoly, coeff_contractWith,
      Polynomial.coeff_map, Polynomial.coeff_contract (Fact.out : Nat.Prime p).ne_zero]
    split_ifs with hi
    · rw [← CPolynomial.coeff_toPoly]
      exact heq _
    · have hp : 0 < p := (Fact.out : Nat.Prime p).pos
      have hdegree : f.toPoly.natDegree < i * p := by
        apply (Nat.div_lt_iff_lt_mul hp).mp
        rw [← CPolynomial.natDegree_toPoly]
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
      simp
  apply toPoly_injective
  rw [toPoly_pow, hpoly]
  have hmap :
      ((Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom).map
          (frobenius F p) = Polynomial.contract p f.toPoly := by
    rw [Polynomial.map_map]
    ext i
    simp
  rw [← Polynomial.map_frobenius_expand, Polynomial.map_expand, hmap]
  apply Polynomial.expand_contract p
  · simpa only [derivative_toPoly, toPoly_zero] using congrArg CPolynomial.toPoly hderiv
  · exact (Fact.out : Nat.Prime p).ne_zero

/-- Every nonconstant derivative-zero input strictly decreases degree under
certified contraction, supplying the recursive termination measure. -/
theorem natDegree_contractWith_lt (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hdegree : 0 < f.natDegree) (hderiv : f.derivative = 0) :
    (contractWith p inverse f).natDegree < f.natDegree := by
  have hpow := congrArg (CPolynomial.toPoly (R := F))
    (contractWith_pow_eq p inverse hinverse f hderiv)
  rw [toPoly_pow] at hpow
  have hd := congrArg Polynomial.natDegree hpow
  rw [Polynomial.natDegree_pow, ← natDegree_toPoly, ← natDegree_toPoly] at hd
  have hpTwo : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  by_cases hc : (contractWith p inverse f).natDegree = 0
  · simpa [hc] using hdegree
  · calc
      (contractWith p inverse f).natDegree < 2 * (contractWith p inverse f).natDegree := by omega
      _ ≤ p * (contractWith p inverse f).natDegree := Nat.mul_le_mul_right _ hpTwo
      _ = f.natDegree := hd

/-- Prime fields use the identity coefficient operation. -/
def primeContract (f : CPolynomial (ZMod p)) : CPolynomial (ZMod p) :=
  contractWith p id f

/-- Prime-field contraction reconstructs the original derivative-zero input. -/
theorem primeContract_pow_eq (f : CPolynomial (ZMod p)) (hderiv : f.derivative = 0) :
    primeContract p f ^ p = f :=
  contractWith_pow_eq p id (fun a => ZMod.pow_card a) f hderiv

/-- Prime-field contraction strictly descends on nonconstant derivative-zero inputs. -/
theorem natDegree_primeContract_lt (f : CPolynomial (ZMod p))
    (hdegree : 0 < f.natDegree) (hderiv : f.derivative = 0) :
    (primeContract p f).natDegree < f.natDegree :=
  natDegree_contractWith_lt p id (fun a => ZMod.pow_card a) f hdegree hderiv

end CompPoly.CPolynomial.FullSquarefreeDecomposition
