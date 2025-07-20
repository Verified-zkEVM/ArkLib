/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

-- import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.MvPolynomial.Basic
import ToMathlib.General

/-!
  # Multilinear Polynomials

  This file defines computable representations of **multilinear polynomials**.

  The first representation is by their coefficients, and the second representation is by their
  evaluations over the Boolean hypercube `{0,1}^n`. Both representations are defined as `Array`s of
  size `2^n`, where `n` is the number of variables. We will define operations on these
  representations, and prove equivalence between them, and with the standard Mathlib definition of
  multilinear polynomials, which is the type `R⦃≤ 1⦄[X Fin n]` (notation for
  `MvPolynomial.restrictDegree (Fin n) R 1`).
-/

namespace Vector

-- TODO: deprecate `nil` and `cons`, and use existing `Vector` definitions (like `insertIdx`)

def nil {α} : Vector α 0 := ⟨#[], rfl⟩

def cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : Vector α (n + 1) :=
  ⟨⟨hd :: tl.toArray.toList⟩, by simp⟩

variable {R : Type*} [Mul R] [AddCommMonoid R] {n : ℕ}

/-- Inner product between two vectors of the same size. Should be faster than `_root_.dotProduct`
    due to efficient operations on `Array`s. -/
def dotProduct (a b : Vector R n) : R :=
  a.zipWith (· * ·) b |>.foldl (· + ·) 0

scoped notation:80 a " *ᵥ " b => dotProduct a b

def dotProduct_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
  dotProduct (cons a b) (cons c d) = a * c + dotProduct b d := by
  simp [dotProduct, cons, foldl]
  -- rw [← Array.foldl_toList]
  sorry

def dotProduct_root_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
    _root_.dotProduct (cons a b).get (cons c d).get = a * c + _root_.dotProduct b.get d.get := by
  sorry

-- theorem dotProduct_eq_matrix_dotProduct (a b : Vector R n) :
--     dotProduct a b = _root_.dotProduct a.get b.get := by
--   refine Vector.induction₂ ?_ (fun hd tl hd' tl' ih => ?_) a b
--   · simp [nil, dotProduct, _root_.dotProduct]
--   · rw [dotProduct_cons, dotProduct_root_cons, ih]

end Vector

/-- `MlPoly n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its coefficients as an `Array` of size `2^n`.

  The indexing is **big-endian** (i.e. the most significant bit is the first bit). -/
@[reducible]
def MlPoly (R : Type*) (n : ℕ) := Vector R (2 ^ n)

/-- `MlPolyEval n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its evaluations over the Boolean hypercube `{0,1}^n`.

  The indexing is **big-endian** (i.e. the most significant bit is the first bit). -/
@[reducible]
def MlPolyEval (R : Type*) (n : ℕ) := Vector R (2 ^ n)

variable {R : Type*} {n : ℕ}

-- Note: `finFunctionFinEquiv` gives a big-endian mapping from `Fin (2 ^ n)` to `Fin n → Fin 2`
-- i.e. `6 : Fin 8` is mapped to `[0, 1, 1]`
#check finFunctionFinEquiv

#check Pi.single

namespace MlPoly

/-! ### TODO: define `add`, `smul`, `nsmul`, `zsmul`, `eval₂`, `eval` -/

instance inhabited [Inhabited R] : Inhabited (MlPoly R n) := by simp [MlPoly]; infer_instance

/-- Conform a list of coefficients to a `MlPoly` with a given number of variables.
    May either pad with zeros or truncate. -/
@[inline]
def ofArray [Zero R] (coeffs : Array R) (n : ℕ): MlPoly R n :=
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

variable [CommRing R]

@[inline, specialize]
def lagrangeBasisAux (w : Vector R n) (i : ℕ) (h : i ≤ n) (currentBasis : Vector R (2 ^ i)) :
    Vector R (2^n) :=
  if h_eq : i = n then
    -- We've processed all variables, currentBasis now has size 2^n
    Vector.cast (by rw [h_eq]) currentBasis
  else
    let w_i := w[i]
    letI newBasis : Vector R (2 ^ (i + 1)) :=
      currentBasis.flatMap (fun c => let cw := c * w_i; #v[c - cw, cw])
    lagrangeBasisAux w (i + 1) (by omega) newBasis

/--
Computes the Lagrange basis polynomials for multilinear extension.

Given a point `w ∈ R^n`, this function returns a vector `v` of size `2^n` such that:
`v[nat(x)] = eq(w, x)` for all `x ∈ {0,1}^n`

where:
- `nat(x)` converts the binary vector `x = [x₀, x₁, ..., xₙ₋₁]` to its natural number representation
  `nat(x) = x₀ · 2^(n-1) + x₁ · 2^(n-2) + ... + xₙ₋₁ · 2^0` (x₀ is the most significant bit)
- `eq(w, x) = ∏ᵢ (wᵢ · xᵢ + (1 - wᵢ) · (1 - xᵢ))` is the multilinear extension
  of the equality function

This is used in the evaluation of multilinear polynomials via their Lagrange interpolation.
-/
@[inline, specialize]
def lagrangeBasis (w : Vector R n) : Vector R (2^n) :=
  lagrangeBasisAux w 0 (by omega) #v[1]

@[simp]
theorem lagrangeBasis_zero {w : Vector R 0} : lagrangeBasis w = #v[1] := by
  simp [lagrangeBasis, lagrangeBasisAux]

-- Relate basis for n with basis for n+1
-- @[simp]
-- theorem lagrangeBasis_succ {w : Vector R (n + 1)} (i : Fin (2 ^ (n + 1))) :
--     lagrangeBasis w[i] = ∏ j : Fin n, (if i.val.testBit j then w[j] else 1 - w[j]) := by
--   sorry

/--
Example: `lagrangeBasis #v[(1 : ℤ), 2, 3]` should return `[0, 0, 0, 0, 2, -3, -4, 6]`

- `x = [0,0,0]` (index 0):
    `eq([1,2,3], [0,0,0]) = (1·0 + 0·1)·(2·0 + (-1)·1)·(3·0 + (-2)·1) = 0·(-1)·(-2) = 0`
- `x = [0,0,1]` (index 1):
    `eq([1,2,3], [0,0,1]) = (1·0 + 0·1)·(2·0 + (-1)·1)·(3·1 + (-2)·0) = 0·(-1)·3 = 0`
- `x = [0,1,0]` (index 2):
    `eq([1,2,3], [0,1,0]) = (1·0 + 0·1)·(2·1 + (-1)·0)·(3·0 + (-2)·1) = 0·2·(-2) = 0`
- `x = [0,1,1]` (index 3):
    `eq([1,2,3], [0,1,1]) = (1·0 + 0·1)·(2·1 + (-1)·0)·(3·1 + (-2)·0) = 0·2·3 = 0`
- `x = [1,0,0]` (index 4):
    `eq([1,2,3], [1,0,0]) = (1·1 + 0·0)·(2·0 + (-1)·1)·(3·0 + (-2)·1) = 1·(-1)·(-2) = 2`
- `x = [1,0,1]` (index 5):
    `eq([1,2,3], [1,0,1]) = (1·1 + 0·0)·(2·0 + (-1)·1)·(3·1 + (-2)·0) = 1·(-1)·3 = -3`
- `x = [1,1,0]` (index 6):
    `eq([1,2,3], [1,1,0]) = (1·1 + 0·0)·(2·1 + (-1)·0)·(3·0 + (-2)·1) = 1·2·(-2) = -4`
- `x = [1,1,1]` (index 7):
    `eq([1,2,3], [1,1,1]) = (1·1 + 0·0)·(2·1 + (-1)·0)·(3·1 + (-2)·0) = 1·2·3 = 6`
-/
example : lagrangeBasis #v[(1 : ℤ), 2, 3] = #v[0, 0, 0, 0, 2, -3, -4, 6] := by
  simp [lagrangeBasis, lagrangeBasisAux]

/-- The `i`-th element of `lagrangeBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1 - w[j]` if the `j`-th bit of `i` is 0. -/
theorem lagrangeBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j] := by
  sorry

variable {S : Type*} [CommRing S]

def map (f : R →+* S) (p : MlPoly R n) : MlPoly S n :=
  Vector.map (fun a => f a) p

/-- Evaluate a `MlPoly` at a point -/
def eval (p : MlPoly R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)

def eval₂ (p : MlPoly R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

-- Theorems about evaluations

-- Evaluation at a point in the Boolean hypercube is equal to the corresponding evaluation in the
-- array
-- theorem eval_eq_eval_array (p : MlPoly R) (x : Array Bool) (h : x.size = p.nVars): eval p
-- x.map (fun b => b) = p.evals.get! (x.foldl (fun i elt => i * 2 + elt) 0) := by unfold eval unfold
-- dotProduct simp [↓reduceIte, h] sorry

end MlPoly

namespace MlPoly

-- Conversion between the coefficient (i.e. monomial) and evaluation (on the Boolean hypercube)
-- representations.

variable {R : Type*} [Add R] [Sub R]

/-- **One level** of the zeta‑transform.

If the `j`‑th least significant bit of the index `i` is `1`, we replace `v[i]` with
`v[i] + v[i with bit j cleared]`; otherwise we leave it unchanged. -/
@[inline] def coeffToEvalLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    letI stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] + v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full transform**: coefficients → evaluations. -/
@[inline] def coeffToEval (n : ℕ) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldl (fun acc level => coeffToEvalLevel level acc)

-- Example:
-- p(X_1, X_0) = 1 + 2X_0 + 3X_1 + 4X_0X_1
-- p(0, 0) = 1
-- p(0, 1) = 3
-- p(1, 0) = 4
-- p(1, 1) = 10
#eval coeffToEval 2 #v[1, 2, 3, 4]
-- { toArray := #[1, 3, 4, 10], size_toArray := _ }

/-- **One level** of the inverse zeta‑transform.

If the `j`‑th least significant bit of the index `i` is `1`, we replace `v[i]` with
`v[i] - v[i with bit j cleared]`; otherwise we leave it unchanged. -/
@[inline] def evalToCoeffLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    letI stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
    Vector.ofFn (fun i : Fin (2 ^ n) =>
      if (BitVec.ofFin i).getLsb j then
        v[i] - v[i - stride]'(Nat.sub_lt_of_lt i.isLt)
      else
        v[i])

/-- **Full inverse transform**: evaluations → coefficients. -/
@[inline]
def evalToCoeff (n : ℕ) :
    Vector R (2 ^ n) → Vector R (2 ^ n) :=
  (List.finRange n).foldr (fun h acc => evalToCoeffLevel h acc)

#eval evalToCoeff 2 #v[1, 3, 4, 10]

-- Example: verifying that evalToCoeff is the inverse of coeffToEval
-- Starting with coefficients [1, 2, 3, 4], transform to evaluations, then back to coefficients
#eval evalToCoeff 2 (coeffToEval 2 #v[1, 2, 3, 4])
-- Should return: { toArray := #[1, 2, 3, 4], size_toArray := _ }

def equivMonomialEval : MlPoly R n ≃ MlPolyEval R n where
  toFun := coeffToEval n
  invFun := evalToCoeff n
  left_inv := sorry
  right_inv := sorry

end MlPoly
