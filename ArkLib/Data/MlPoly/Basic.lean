/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.Nat.Bitwise
import Mathlib.RingTheory.MvPolynomial.Basic
import ToMathlib.General
import ArkLib.Data.Fin.BigOperators
import ArkLib.Data.List.Lemmas
import ArkLib.Data.Vector.Basic

/-!
  # Multilinear Polynomials

  This file defines computable representations of **multilinear polynomials**.

  The first representation is by their coefficients, and the second representation is by their
  evaluations over the Boolean hypercube `{0,1}^n`. Both representations are defined as `Vector`s of
  length `2^n`, where `n` is the number of variables. We will define operations on these
  representations, and prove equivalence between them, and with the standard Mathlib definition of
  multilinear polynomials, which is the type `R⦃≤ 1⦄[X Fin n]` (notation for
  `MvPolynomial.restrictDegree (Fin n) R 1`).

  ## TODOs
  - The abstract formula for `monoToLagrange` (zeta formula) and `lagrangeToMono` (mobius formula)
-/


/-- `MlPoly n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its monomial coefficients as a `Vector` of length `2^n`.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def MlPoly (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of monomial basis
def MlPoly.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : MlPoly R n := v

/-- `MlPolyEval n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its evaluations over the Boolean hypercube `{0,1}^n`,
  i.e. Lagrange basis coefficients.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def MlPolyEval (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of Lagrange basis
def MlPolyEval.mk {R : Type*} (n : ℕ) (v : Vector R (2 ^ n)) : MlPolyEval R n := v

variable {R : Type*} {n : ℕ}

-- Note: `finFunctionFinEquiv` maps `i : Fin (2 ^ n)` to its bit-vector in little‑endian order,
-- with bit 0 the least significant bit. For example, `6 : Fin 8` maps to `[0, 1, 1]`.
-- #check finFunctionFinEquiv

-- #check Pi.single

namespace MlPoly

section MlPolyInstances

instance inhabited [Inhabited R] : Inhabited (MlPoly R n) := by simp [MlPoly]; infer_instance

/-- Conform a list of coefficients to a `MlPoly` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : MlPoly R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : MlPoly R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

/-- Add two `MlPoly`s -/
@[inline]
def add [Add R] (p q : MlPoly R n) : MlPoly R n := Vector.zipWith (· + ·) p q

/-- Negation of a `MlPoly` -/
@[inline]
def neg [Neg R] (p : MlPoly R n) : MlPoly R n := p.map (fun a => -a)

/-- Scalar multiplication of a `MlPoly` -/
@[inline]
def smul [Mul R] (r : R) (p : MlPoly R n) : MlPoly R n := p.map (fun a => r * a)

/-- Scalar multiplication of a `MlPoly` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : MlPoly R n) : MlPoly R n := p.map (fun a => m • a)

/-- Scalar multiplication of a `MlPoly` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : MlPoly R n) : MlPoly R n := p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (MlPoly R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (MlPoly R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp
end MlPolyInstances

section MlPolyMonomialBasisAndEvaluations

variable [CommRing R]
variable {S : Type*} [CommRing S]

/-
Monomial-basis evaluations at point `w`.

Returns the length-`2^n` vector whose index `i : Fin (2^n)` encodes a Boolean vector in
little‑endian order (bit 0 is the least significant bit). The entry at `i` is
`∏_{j < n} (if the j-th bit of i is 1 then w[j] else 1)`.
-/
def monomialBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1)

@[simp]
theorem monomialBasis_zero {w : Vector R 0} : monomialBasis w = #v[1] := by rfl

-- #eval monomialBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval Nat.digits 2 8

/-- The `i`-th element of `monomialBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1` if the `j`-th bit of `i` is 0. -/
theorem monomialBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (monomialBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 := by
  rw [monomialBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

variable {S : Type*} [CommRing S]

def map (f : R →+* S) (p : MlPoly R n) : MlPoly S n :=
  Vector.map (fun a => f a) p

/-- Evaluate a `MlPoly` at a point -/
def eval (p : MlPoly R n) (x : Vector R n) : R :=
  Vector.dotProduct p (monomialBasis x)

def eval₂ (p : MlPoly R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x
end MlPolyMonomialBasisAndEvaluations

end MlPoly

namespace MlPolyEval

section MlPolyEvalInstances

instance inhabited [Inhabited R] : Inhabited (MlPolyEval R n) := by
  simp only [MlPolyEval]; infer_instance

/-- Conform a list of coefficients to a `MlPolyEval` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ) : MlPolyEval R n :=
  .ofFn (fun i => if h : i.1 < coeffs.size then coeffs[i] else 0)
  -- ⟨((coeffs.take (2 ^ n)).rightpad (2 ^ n) 0 : Array R), by simp⟩
  -- Not sure which is better performance wise?

-- Create a zero polynomial over n variables
@[inline]
def zero [Zero R] : MlPolyEval R n := Vector.replicate (2 ^ n) 0

lemma zero_def [Zero R] : zero = Vector.replicate (2 ^ n) 0 := rfl

/-- Add two `MlPolyEval`s -/
@[inline]
def add [Add R] (p q : MlPolyEval R n) : MlPolyEval R n := Vector.zipWith (· + ·) p q

/-- Negation of a `MlPolyEval` -/
@[inline]
def neg [Neg R] (p : MlPolyEval R n) : MlPolyEval R n := p.map (fun a => -a)

/-- Scalar multiplication of a `MlPolyEval` -/
@[inline]
def smul [Mul R] (r : R) (p : MlPolyEval R n) : MlPolyEval R n := p.map (fun a => r * a)

/-- Scalar multiplication of a `MlPolyEval` by a natural number -/
@[inline]
def nsmul [SMul ℕ R] (m : ℕ) (p : MlPolyEval R n) : MlPolyEval R n := p.map (fun a => m • a)

/-- Scalar multiplication of a `MlPolyEval` by an integer -/
@[inline]
def zsmul [SMul ℤ R] (m : ℤ) (p : MlPolyEval R n) : MlPolyEval R n := p.map (fun a => m • a)

instance [AddCommMonoid R] : AddCommMonoid (MlPolyEval R n) where
  add := add
  add_assoc a b c := by
    change Vector.zipWith (· + ·) (Vector.zipWith (· + ·) a b) c =
      Vector.zipWith (· + ·) a (Vector.zipWith (· + ·) b c)
    ext; simp [add_assoc]
  add_comm a b := by
    change Vector.zipWith (· + ·) a b = Vector.zipWith (· + ·) b a
    ext; simp [add_comm]
  zero := zero
  zero_add a := by
    change Vector.zipWith (· + ·) (Vector.replicate (2 ^ n) 0) a = a
    ext; simp
  add_zero a := by
    change Vector.zipWith (· + ·) a (Vector.replicate (2 ^ n) 0) = a
    ext; simp
  nsmul := nsmul
  nsmul_zero a := by
    change Vector.map (fun a ↦ 0 • a) a = Vector.replicate (2 ^ n) 0
    ext; simp
  nsmul_succ n a := by
    change a.map (fun a ↦ (n + 1) • a) = Vector.zipWith (· + ·) (Vector.map (fun a ↦ n • a) a) a
    ext i; simp; exact AddMonoid.nsmul_succ n a[i]

instance [Semiring R] : Module R (MlPolyEval R n) where
  smul := smul
  one_smul a := by
    change Vector.map (fun a ↦ 1 * a) a = a
    ext; simp
  mul_smul r s a := by
    simp [HSMul.hSMul, smul]
  smul_zero a := by
    change Vector.map (fun a_1 ↦ a * a_1) (Vector.replicate (2 ^ n) 0) = Vector.replicate (2 ^ n) 0
    ext; simp
  smul_add r a b := by
    change Vector.map (fun a ↦ r * a) (Vector.zipWith (· + ·) a b) =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ r * a) b)
    ext; simp [left_distrib]
  add_smul r s a := by
    change Vector.map (fun a ↦ (r + s) * a) a =
      Vector.zipWith (· + ·) (Vector.map (fun a ↦ r * a) a) (Vector.map (fun a ↦ s * a) a)
    ext; simp [right_distrib]
  zero_smul a := by
    change Vector.map (fun a ↦ 0 * a) a = Vector.replicate (2 ^ n) 0
    ext; simp

end MlPolyEvalInstances

section MlPolyLagrangeBasisAndEvaluations

variable [CommRing R]
variable {S : Type*} [CommRing S]

/-- Lagrange (hypercube) basis at point `w`.

Returns the length-`2^n` vector `v` such that for any `x ∈ {0,1}^n`, letting
`i = ∑_{j=0}^{n-1} x_j · 2^j` (little‑endian indexing), we have
`v[i] = ∏_{j < n} (x_j · w[j] + (1 - x_j) · (1 - w[j]))`.
Equivalently, for `i : Fin (2^n)`,
`v[i] = ∏_{j < n}, (if the j-th bit of i is 1 then w[j] else 1 - w[j])`.
-/
def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])

@[simp]
theorem lagrangeBasis_zero {w : Vector R 0} : lagrangeBasis w = #v[1] := by rfl

-- #eval lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval Nat.digits 2 8

/-- The `i`-th element of `lagrangeBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1 - w[j]` if the `j`-th bit of `i` is 0. -/
theorem lagrangeBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j] := by
  rw [lagrangeBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

variable {S : Type*} [CommRing S]

/-- Map a ring homomorphism over a `MlPolyEval` -/
def map (f : R →+* S) (p : MlPolyEval R n) : MlPolyEval S n :=
  Vector.map (fun a => f a) p

/-- Evaluate a `MlPolyEval` at a point -/
def eval (p : MlPolyEval R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)

/-- Evaluate a `MlPolyEval` at a point using a ring homomorphism -/
def eval₂ (p : MlPolyEval R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

-- Theorems about evaluations

end MlPolyLagrangeBasisAndEvaluations

end MlPolyEval

namespace MlPoly

-- Conversion between the coefficient (i.e. monomial) and evaluation (on the Boolean hypercube)
-- representations.

variable {R : Type*} [AddCommGroup R]

/-- **One level** of the zeta‑transform.

If the `j`‑th least significant bit of the index `i` is `1`, we replace `v[i]` with
`v[i] + v[i with bit j cleared]`; otherwise we leave it unchanged. -/
@[inline] def monoToLagrangeLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] + v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full transform**: coefficients → evaluations. -/
@[inline] def monoToLagrange (n : ℕ) : MlPoly R n → MlPolyEval R n :=
  (List.finRange n).foldl (fun acc level => monoToLagrangeLevel level acc)

/-- **One level** of the inverse zeta‑transform.

If the `j`‑th least significant bit of the index `i` is `1`, we replace `v[i]` with
`v[i] - v[i with bit j cleared]`; otherwise we leave it unchanged. -/
@[inline] def lagrangeToMonoLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    let stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] - v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full inverse transform**: evaluations → coefficients. -/
@[inline]
def lagrangeToMono (n : ℕ) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldr (fun h acc => lagrangeToMonoLevel h acc)

/-- The O(n^3) computable version of the Mobius Transform, serving as the spec.

TODO: prove equivalence between `lagrangeToMono` and `lagrangeToMonoSpec` -/
def lagrangeToMonoSpec (p : MlPolyEval R n) : MlPolyEval R n :=
  -- We define the output vector by specifying the value for each entry `i`.
  Vector.ofFn (fun i =>
    -- For each output entry `i`, we compute a sum over all possible input indices `j`.
    Finset.sum Finset.univ (fun j =>
      -- The sum is only over `j` that are bitwise subsets of `i`.
      if (i.val &&& j.val = j.val) then
        -- The term is added or subtracted based on the parity of the difference
        -- in the number of set bits (Hamming weight).
        if (i.val.popCount - j.val.popCount) % 2 = 0 then
          p.get j -- Add if the difference is even
        else
          -p.get j -- Subtract if the difference is odd
      else
        0 -- If j is not a subset of i, the term is zero.
    )
  )

-- #eval lagrangeToMono 2 #v[(78 : ℤ), 3, 4, 100]
-- #eval lagrangeToMonoSpec (n:=2) #v[(78 : ℤ), 3, 4, 100]

def forwardRange (n : ℕ) (r : Fin (n)) (l : Fin (r.val + 1)) : List (Fin n) :=
  let len := r.val - l.val + 1
  List.ofFn (fun (k : Fin len) =>
    let val := l.val + k.val
    have h_bound : val < n := by omega
    ⟨val, h_bound⟩
  )

lemma forwardRange_length (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    (forwardRange n r l).length = r.val - l.val + 1 := by
  unfold forwardRange
  simp only [List.length_ofFn]

lemma forwardRange_eq_of_r_eq (n : ℕ) (r1 r2 : Fin n) (h_r_eq : r1 = r2) (l : Fin (r1.val + 1)) :
  forwardRange n r1 l = forwardRange n r2 ⟨l, by omega⟩ := by
  subst h_r_eq
  rfl

lemma forwardRange_getElem (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (k : Fin (r.val - l.val + 1)) :
    (forwardRange n r l).get ⟨k, by
      rw [forwardRange]; simp only [List.length_ofFn]; omega⟩ = ⟨l.val + k, by omega⟩ := by
  unfold forwardRange
  simp only [List.get_eq_getElem]
  simp only [List.getElem_ofFn]

lemma forwardRange_succ_right_ne_empty (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
  forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_pred_le_ne_empty (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (h_l_gt_0 : l.val > 0) : forwardRange n r ⟨l.val - 1, by omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_dropLast (n : ℕ) (r : Fin (n - 1)) (l : Fin (r.val + 1)) :
    (forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩).dropLast
    = forwardRange n ⟨r, by omega⟩ ⟨l, by simp only [Fin.is_lt]⟩ := by
  apply List.ext_getElem
  · rw [List.length_dropLast, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_dropLast, forwardRange_length, add_tsub_cancel_right, Fin.eta] at h₁ h₂
    simp only [List.getElem_dropLast, Fin.eta]
    have hleft := forwardRange_getElem n
      ⟨r.val + 1, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    have hright := forwardRange_getElem n
      ⟨r.val, by omega⟩ ⟨l, by simp only; omega⟩ (k:=⟨i, by simp only; omega⟩)
    simp only [List.get_eq_getElem, Fin.eta] at hleft hright
    rw [hleft, hright]

lemma forwardRange_tail (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (h_l_gt_0 : l.val > 0) :
  (forwardRange n r ⟨l.val - 1, by omega⟩).tail = forwardRange n r l := by
  apply List.ext_getElem
  · rw [List.length_tail, forwardRange_length, forwardRange_length]
    simp only [add_tsub_cancel_right]
    omega
  · intro i h₁ h₂
    simp only [List.length_tail, forwardRange_length, add_tsub_cancel_right] at h₁ h₂
    simp only [List.getElem_tail]
    have hleft := forwardRange_getElem n r ⟨l.val - 1, by omega⟩ (k:=⟨i + 1, by simp only; omega⟩)
    have hright := forwardRange_getElem n r l (k:=⟨i, by omega⟩)
    simp only [List.get_eq_getElem] at hleft hright
    rw [hleft, hright]
    rw [Fin.mk.injEq, Nat.add_comm i 1, ←Nat.add_assoc, Nat.sub_one_add_one (a:=l.val) (by omega)]

lemma forwardRange_0_eq_finRange (n : ℕ) [NeZero n] : forwardRange n ⟨n - 1, by
    have h_ne := NeZero.ne n
    omega
  ⟩ 0 = List.finRange n := by
  have h_ne := NeZero.ne n
  stop
  refine
    Array.ext.extAux
      (forwardRange n
        ⟨n - 1,
          have h_ne := NeZero.ne n;
          Decidable.byContradiction fun a ↦ forwardRange_0_eq_finRange._proof_1 n h_ne a⟩
        0)
      (List.finRange n) ?_ ?_
  · rw [forwardRange_length]; simp only [List.length_finRange, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    tsub_zero];
    rw [Nat.sub_one_add_one (by exact Ne.symm (NeZero.ne' n))]
  · intro i hi hi₂
    simp only [List.getElem_finRange, Fin.cast_mk]
    have h := forwardRange_getElem (n:=n) (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) (k:=⟨i, by
      simp only [tsub_zero];
      rw [Nat.sub_one_add_one (by exact Ne.symm (NeZero.ne' n))]
      convert hi
      rw [forwardRange_length]
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero]
      rw [Nat.sub_one_add_one (by exact Ne.symm (NeZero.ne' n))]
    ⟩)
    simp only [Fin.zero_eta, List.get_eq_getElem, zero_add] at h
    rw [h]

/- 0 ≤ l ≤ r < n - where n is the number of bits -/
def monoToLagrange_segment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  let range := forwardRange n r l
  (range.foldl (fun acc h => monoToLagrangeLevel h acc))

/- 0 ≤ l ≤ r < n - where n is the number of bits -/
def lagrangeToMono_segment (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  let range := forwardRange n r l
  (range.foldr (fun h acc => lagrangeToMonoLevel h acc))

lemma monoToLagrange_eq_monoToLagrange_segment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  monoToLagrange n v = monoToLagrange_segment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold monoToLagrange monoToLagrange_segment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma lagrangeToMono_eq_lagrangeToMono_segment (n : ℕ) [NeZero n] (v : Vector R (2 ^ n)) :
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  lagrangeToMono n v = lagrangeToMono_segment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold lagrangeToMono lagrangeToMono_segment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma testBit_of_sub_two_pow_of_bit_1 {n i : ℕ} (h_testBit_eq_1 : (n).testBit i = true) :
  (n - 2^i).testBit i = false := by
  have h := Nat.testBit_false_eq_getBit_eq_0 (n:=n - 2^i) (k:=i)
  rw [h]
  have h_getBit_eq_0: Nat.getBit i (n - 2^i) = 0 := by
    rw [Nat.getBit_of_sub_two_pow_of_bit_1]
    simp only [↓reduceIte]
    rw [Nat.testBit_true_eq_getBit_eq_1] at h_testBit_eq_1
    exact h_testBit_eq_1
  exact h_getBit_eq_0

theorem lagrangeToMonoLevel_monoToLagrangeLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
  lagrangeToMonoLevel i (monoToLagrangeLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    have h_as_assoc := add_sub_assoc (a:=v[i1]'(by omega))
      (b:=v[i1 - 2 ^ i.val]'(h_id_lt)) (c:=v[i1 - 2 ^ i.val]'(h_id_lt))
    rw [h_as_assoc, sub_self, add_zero]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem monoToLagrangeLevel_lagrangeToMonoLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
  monoToLagrangeLevel i (lagrangeToMonoLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1 i1_isLt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have hi1_lt : i1 < 2 ^ n := by
      simpa using i1_isLt
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      exact Nat.sub_lt_of_lt hi1_lt
    rw [sub_add_cancel]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem mobius_apply_zeta_apply_eq_id (n : ℕ) [NeZero n] (r : Fin n) (l : Fin (r.val + 1))
    (v : Vector R (2 ^ n)) : lagrangeToMono_segment n r l (monoToLagrange_segment n r l v) = v := by
  induction r using Fin.succRecOnSameFinType with
  | zero =>
    rw [lagrangeToMono_segment, monoToLagrange_segment, forwardRange]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_eq_zero, tsub_self, zero_add,
      List.ofFn_succ, Fin.isValue, Fin.cast_zero, Nat.mod_succ, add_zero, Fin.mk_zero',
      Fin.cast_succ_eq, Fin.val_succ, Fin.coe_cast, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
      List.foldr_cons, List.foldr_nil]
    exact lagrangeToMonoLevel_monoToLagrangeLevel_id v 0
  | succ r1 r1_lt_n h_r1 =>
    unfold lagrangeToMono_segment monoToLagrange_segment
    if h_l_eq_r: l.val = (r1 + 1).val then
      rw [forwardRange]
      simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ,
        List.foldl_cons, List.foldr_cons]
      simp_rw [h_l_eq_r]
      simp only [Fin.eta, tsub_self, List.ofFn_zero, List.foldl_nil, List.foldr_nil]
      exact lagrangeToMonoLevel_monoToLagrangeLevel_id v (r1 + 1)
    else
      have h_l_lt_r: l.val < (r1 + 1).val := by omega
      have h_r1_add_1_val: (r1 + 1).val = r1.val + 1 := by
        rw [Fin.val_add_one']; omega
      have h_range_ne_empty: forwardRange n (r1 + 1) l ≠ [] := by
        have h:= forwardRange_succ_right_ne_empty n
          (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [ne_eq] at h
        have h_r1_add_1: r1 + 1 = ⟨r1.val + 1, by omega⟩ := by
          exact Fin.eq_mk_iff_val_eq.mpr h_r1_add_1_val
        rw [forwardRange_eq_of_r_eq (r1:=r1 + 1) (r2:=⟨r1.val + 1, by omega⟩) (h_r_eq:=h_r1_add_1)]
        exact h
      rw [List.foldr_split_inner (h:=h_range_ne_empty)]
      rw [List.foldl_split_outer (h:=h_range_ne_empty)]
      rw [lagrangeToMonoLevel_monoToLagrangeLevel_id]
      have h_inductive := h_r1 (l := ⟨l, by exact Nat.lt_of_lt_of_eq h_l_lt_r h_r1_add_1_val⟩)
      rw [lagrangeToMono_segment, monoToLagrange_segment] at h_inductive
      simp only at h_inductive
      have h_range_droplast: (forwardRange n (r1 + 1) l).dropLast
        = forwardRange n r1 ⟨↑l, by omega⟩ := by
        have h := forwardRange_dropLast n (r:=⟨r1, by omega⟩) (l:=⟨l, by simp only; omega⟩)
        simp only [Fin.eta] at h
        convert h
      convert h_inductive

def zeta_apply_mobius_apply_eq_id (n : ℕ) (r : Fin n) (l : Fin (r.val + 1)) (v : Vector R (2 ^ n)) :
  monoToLagrange_segment n r l (lagrangeToMono_segment n r l v) = v := by
  induction l using Fin.predRecOnSameFinType with
  | last =>
    rw [lagrangeToMono_segment, monoToLagrange_segment, forwardRange]
    simp only [add_tsub_cancel_right, tsub_self, zero_add, List.ofFn_succ, Nat.add_one_sub_one,
      Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, Nat.mod_succ, add_zero, Fin.eta,
      Fin.cast_succ_eq, Fin.val_succ, Fin.coe_cast, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      List.foldl_cons, List.foldl_nil]
    exact monoToLagrangeLevel_lagrangeToMonoLevel_id v r
  | succ l1 l1_gt_0 h_l1 =>
    unfold lagrangeToMono_segment monoToLagrange_segment
    have h_l1_sub_1_lt_r: (⟨l1.val - 1, by omega⟩: Fin (r.val + 1)).val < r.val := by
      simp only
      have h_l1 := l1.isLt
      apply Nat.lt_of_add_lt_add_right (n:=1)
      rw [Nat.sub_one_add_one (by omega)]
      omega
    have h_range_ne_empty: forwardRange n r ⟨l1.val - 1, by omega⟩ ≠ [] := by
      have h:= forwardRange_pred_le_ne_empty n
        (r:=⟨r, by omega⟩) (l:=⟨l1, by simp only; omega⟩) (by omega)
      simp only [ne_eq, h, not_false_eq_true]
    rw [List.foldr_split_outer (h:=h_range_ne_empty)]
    rw [List.foldl_split_inner (h:=h_range_ne_empty)]
    rw [monoToLagrangeLevel_lagrangeToMonoLevel_id]
    have h_inductive := h_l1
    rw [lagrangeToMono_segment, monoToLagrange_segment] at h_inductive
    simp only at h_inductive
    have h_range_tail: (forwardRange n r ⟨l1.val - 1, by omega⟩).tail = forwardRange n r l1 := by
      have h := forwardRange_tail n (r:=r) (l:=l1) (by omega)
      convert h
    convert h_inductive

def equivMonomialLagrangeRepr : MlPoly R n ≃ MlPolyEval R n where
  toFun := monoToLagrange n
  invFun := lagrangeToMono n
  left_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      letI: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMono_segment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrange_segment (n:=n)]
      simp only [Fin.zero_eta]
      exact
        mobius_apply_zeta_apply_eq_id n
          ⟨n - 1,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrange_segment._proof_1 n (NeZero.ne n) a⟩
          0 v
  right_inv v := by
    if h_n_eq_0: n = 0 then
      subst h_n_eq_0; rfl
    else
      have h_n_ne_zero: n ≠ 0 := by omega
      letI: NeZero n := by exact { out := h_n_eq_0 }
      rw [lagrangeToMono_eq_lagrangeToMono_segment (n:=n)]
      rw [monoToLagrange_eq_monoToLagrange_segment (n:=n)]
      exact
        zeta_apply_mobius_apply_eq_id n
          ⟨n - 1,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrange_segment._proof_1 n (NeZero.ne n) a⟩
          ⟨0,
            Decidable.byContradiction fun a ↦
              monoToLagrange_eq_monoToLagrange_segment._proof_2 n (NeZero.ne n) a⟩
          v

end MlPoly

/-! ### #eval Tests

This section contains tests to verify the functionality of multilinear polynomial operations.
-/

section Tests

-- #eval MlPoly.zero (n := 2) (R := ℤ)
-- #eval MlPoly.add #v[1, 2, 3, 4] #v[5, 6, 7, 8] (n := 2) (R := ℤ)
-- #eval MlPoly.smul 2 #v[1, 2, 3, 4] (n := 2) (R := ℤ)
-- #eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
-- #eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2] (n := 2)
-- #eval MlPolyEval.eval #v[1, 2, 3, 4] #v[(1 : ℤ), 2] (n := 2)
-- #eval MlPoly.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4]
-- #eval MlPoly.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10]
-- #eval MlPoly.lagrangeToMono 2 (MlPoly.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4])
-- #eval MlPoly.monoToLagrange 2 (MlPoly.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10])
-- #eval MlPoly.monoToLagrange 1 #v[(1 : ℤ), 2]
-- #eval MlPoly.monoToLagrange 3 #v[(1 : ℤ), 2, 3, 4, 5, 6, 7, 8]
-- #eval MlPolyEval.lagrangeBasis #v[(1 : ℤ)] (n := 1)
-- #eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2, 3, 4] (n := 4)
-- #eval (MlPoly.mk 2 #v[1, 2, 3, 4]) + (MlPoly.mk 2 #v[5, 6, 7, 8])
-- #eval ((4: ℤ) • (MlPoly.mk 2 #v[(1: ℤ), 2, 3, 4]))

end Tests
