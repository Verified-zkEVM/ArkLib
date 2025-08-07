/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

-- import Mathlib.Data.Matrix.Mul
import ArkLib.Data.Nat.Bitwise
import Mathlib.RingTheory.MvPolynomial.Basic
import ToMathlib.General
import ArkLib.Data.Fin.BigOperators

/-!
  # Multilinear Polynomials

  This file defines computable representations of **multilinear polynomials**.

  The first representation is by their coefficients, and the second representation is by their
  evaluations over the Boolean hypercube `{0,1}^n`. Both representations are defined as `Array`s of
  size `2^n`, where `n` is the number of variables. We will define operations on these
  representations, and prove equivalence between them, and with the standard Mathlib definition of
  multilinear polynomials, which is the type `R⦃≤ 1⦄[X Fin n]` (notation for
  `MvPolynomial.restrictDegree (Fin n) R 1`).

  ## TODOs
  - The abstract formula for `monoToLagrange` (zeta formula) and `lagrangeToMono` (mobius formula)
-/

namespace Vector

-- TODO: deprecate `nil` and `cons`, and use existing `Vector` definitions (like `insertIdx`)

def nil {α} : Vector α 0 := ⟨#[], rfl⟩ -- Vector.emptyWithCapacity 0

def cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : Vector α (n + 1) :=
  tl.insertIdx 0 hd

theorem head_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).head = hd := by
  simp only [head, cons, insertIdx_zero, getElem_cast, zero_lt_one, getElem_append_left, getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero]

lemma cons_get_eq {α} {n : ℕ} (hd : α) (tl : Vector α n) (i : Fin (n+1)) :
    (cons hd tl).get i =
      if hi: i.val == 0 then hd else tl.get (⟨i.val - 1, by
        simp only [beq_iff_eq, Fin.val_eq_zero_iff] at hi
        apply Nat.sub_lt_left_of_lt_add
        · by_contra hi_ne_gt_1
          simp only [not_le, Nat.lt_one_iff, Fin.val_eq_zero_iff] at hi_ne_gt_1
          contradiction
        · have hi_lt:= i.isLt; omega
      ⟩) := by
  if h_i_val: i.val = 0 then
    have h_i: i = 0 := by exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h_i_val)))
    subst h_i
    simp only [h_i_val, beq_iff_eq, ↓reduceDIte]
    simp only [cons, get, insertIdx] -- unfold everything
    simp only [Array.insertIdx_zero, Fin.coe_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      List.size_toArray, List.length_cons, List.length_nil, zero_add, zero_lt_one,
      Array.getElem_append_left, List.getElem_toArray, List.getElem_cons_zero]
  else
    simp only [h_i_val, beq_iff_eq, ↓reduceDIte]
    simp only [cons, get, insertIdx] -- unfold everything
    simp only [Array.insertIdx_zero, Fin.coe_cast, Fin.cast_mk, getElem_toArray]
    apply Array.getElem_append_right -- key counterpart for cons_get_eq in `Array` realm
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    omega

lemma cons_empty_tail_eq_nil {α} (hd : α) (tl : Vector α 0) :
    cons hd tl = ⟨#[hd], rfl⟩ := by
  apply Vector.toArray_inj.mp
  simp only [Nat.reduceAdd]
  rw [cons]
  simp only [insertIdx_size_self, toArray_push]
  have hl_toArray: tl.toArray = #[] := by
    simp only [toArray_eq_empty_iff]
  rw [hl_toArray]
  simp only [Array.push_empty]

theorem tail_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).tail = tl := by
  rw [cons, Vector.insertIdx]
  simp only [Nat.add_one_sub_one, Array.insertIdx_zero, tail_eq_cast_extract, extract_mk,
    Array.extract_append, List.extract_toArray, List.extract_eq_drop_take, add_tsub_cancel_right,
    List.drop_succ_cons, List.drop_nil, List.take_nil, List.size_toArray, List.length_cons,
    List.length_nil, zero_add, tsub_self, Array.take_eq_extract, Array.empty_append, cast_mk, mk_eq,
    Array.extract_eq_self_iff, size_toArray, le_refl, and_self, or_true]

theorem cons_toList_eq_List_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) :
    (cons hd tl).toList = hd :: tl.toList := by
  simp only [toList, cons, insertIdx]
  rw [Array.toList_insertIdx]
  simp only [List.insertIdx_zero]

theorem foldl_succ
 {α β} {n : ℕ} [NeZero n] (f : β → α → β) (init : β) (v : Vector α n) :
  v.foldl (f:=f) (b:=init) = v.tail.foldl (f:=f) (b:=f init v.head) := by
  simp_rw [Vector.foldl] -- get
  simp only [size_toArray]
  have hl_foldl_eq_toList_foldl := Array.foldl_toList (f:=f) (init:=init) (xs:=v.toArray)
  have hl_foldl_eq: Array.foldl f init v.toArray 0 n = Array.foldl f init v.toArray := by
    simp only [size_toArray]
  conv_lhs =>
    rw [hl_foldl_eq, hl_foldl_eq_toList_foldl.symm]
  have hr_foldl_eq_toList_foldl_tail := Array.foldl_toList (f:=f) (init:=f init v.head)
    (xs:=(v.tail.toArray))
  have hr_foldl_eq: Array.foldl f (f init v.head) v.tail.toArray 0 (n - 1)
    = Array.foldl f (f init v.head) v.tail.toArray := by
    simp only [size_toArray] -- Array.foldl_congr
  conv_rhs =>
    rw [hr_foldl_eq, hr_foldl_eq_toList_foldl_tail.symm]
  rw [Vector.head]
  have h_v_toList_length: 0 < v.toList.length := by
    simp only [length_toList]
    exact Nat.pos_of_neZero n
  rw [←Vector.getElem_toList (h:=h_v_toList_length)]
  have h_toList_eq: v.toArray.toList = v.toList := rfl
  rw [Vector.tail]
  simp only [toArray_cast, toArray_extract, Array.toList_extract, List.extract_eq_drop_take,
    List.drop_one]
  simp_rw [h_toList_eq]
  -- ⊢ List.foldl f init v.toList
  -- = List.foldl f (f init v.toList[0]) (List.take (n - 1) v.toList.tail)
  have hTakeTail: List.take (n - 1) v.toList.tail = v.toList.tail := by
    simp only [List.take_eq_self_iff, List.length_tail, length_toList, le_refl]
  rw [hTakeTail]
  have h_v_eq_cons: v.toList = v.head :: (v.toList.tail) := by
    cases h_list : v.toList with
    | nil =>
      have h_len : v.toList.length = 0 := by rw [h_list, List.length_nil]
      omega
    | cons hd tl =>
      have h_v_head: v.head = v.toList[0] := rfl
      simp_rw [h_v_head]
      have h_hd: hd = v.toList[0] := by simp only [h_list, List.getElem_cons_zero]
      simp only [List.tail_cons, List.cons.injEq, and_true]
      simp_rw [h_hd]
  conv_lhs => rw [h_v_eq_cons]
  rw [List.foldl_cons]
  rfl

theorem foldl_eq_toList_foldl {α β} {n : ℕ} (f : β → α → β) (init : β) (v : Vector α n) :
  v.foldl (f:=f) (b:=init) = v.toList.foldl (f:=f) (init:=init) := by
  rw [Vector.foldl]
  rw [←Array.foldl_toList]
  rfl

#eval cons (hd:=6) (tl:=⟨#[2, 3], rfl⟩)

variable {R : Type*} [Mul R] [AddCommMonoid R] {n : ℕ}

/-- Inner product between two vectors of the same size. Should be faster than `_root_.dotProduct`
    due to efficient operations on `Array`s. -/
def dotProduct (a b : Vector R n) : R :=
  a.zipWith (· * ·) b |>.foldl (· + ·) 0

theorem zipWith_cons {α β γ} {n : ℕ} (f : α → β → γ)
    (a : α) (b : Vector α n) (c : β) (d : Vector β n) :
    zipWith f (cons a b) (cons c d) = cons (f a c) (zipWith f b d) := by
  apply Vector.toList_inj.mp
  conv_lhs => simp only [toList_zipWith]
  simp_rw [cons_toList_eq_List_cons]
  rw [List.zipWith_cons_cons]
  conv_rhs => rw [toList_zipWith]

scoped notation:80 a " *ᵥ " b => dotProduct a b

def dotProduct_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
  dotProduct (cons a b) (cons c d) = a * c + dotProduct b d := by
  unfold dotProduct
  rw [zipWith_cons]
  simp_rw [foldl_eq_toList_foldl]
  rw [cons_toList_eq_List_cons]
  rw [List.foldl_eq_of_comm' (hf:=by exact fun a b c ↦ add_right_comm a b c)]
  rw [add_comm]

def dotProduct_root_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
    _root_.dotProduct (cons a b).get (cons c d).get = a * c + _root_.dotProduct b.get d.get := by
  unfold _root_.dotProduct
  if h_n: n = 0 then
    subst h_n
    simp only [cons_empty_tail_eq_nil]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rfl
  else
    -- ⊢ ∑ i, (cons a b).get i * (cons c d).get i = a * c + ∑ i, b.get i * d.get i
    rw [Fin.sum_univ_succ]
    rw [cons_get_eq, cons_get_eq]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, BEq.rfl, ↓reduceDIte]
    congr
    funext i
    simp_rw [cons_get_eq]
    simp only [Fin.val_succ, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceDIte,
      add_tsub_cancel_right, Fin.eta]

-- theorem dotProduct_eq_matrix_dotProduct (a b : Vector R n) :
--     dotProduct a b = _root_.dotProduct a.get b.get := by
--   refine Vector.induction₂ ?_ (fun hd tl hd' tl' ih => ?_) a b
--   · simp [nil, dotProduct, _root_.dotProduct]
--   · rw [dotProduct_cons, dotProduct_root_cons, ih]

end Vector

/-- `MlPoly n R` is the type of multilinear polynomials in `n` variables over a ring `R`. It is
  represented by its monomial coefficients as an `Array` of size `2^n`.
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

-- Note: `finFunctionFinEquiv` gives a big-endian mapping from `Fin (2 ^ n)` to `Fin n → Fin 2`
-- i.e. `6 : Fin 8` is mapped to `[0, 1, 1]`
#check finFunctionFinEquiv

#check Pi.single

namespace MlPoly

section MlPolyInstances

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
end MlPolyInstances

section MlPolyMonomialBasisAndEvaluations

variable [CommRing R]
variable {S : Type*} [CommRing S]

def monomialBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1)

@[simp]
theorem monomialBasis_zero {w : Vector R 0} : monomialBasis w = #v[1] := by rfl

#eval monomialBasis #v[(1 : ℤ), 2, 3] (n := 3)
#eval Nat.digits 2 8

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
def ofArray [Zero R] (coeffs : Array R) (n : ℕ): MlPolyEval R n :=
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

-- /--
-- Computes the Lagrange basis polynomials for multilinear extension.

-- Given a point `w ∈ R^n`, this function returns a vector `v` of size `2^n` such that:
-- `v[nat(x)] = eq(w, x)` for all `x ∈ {0,1}^n`

-- where:
-- - `nat(x)` converts the binary vector `x = [x₀, x₁, ..., xₙ₋₁]` to its ℕ representation
--   `nat(x) = x₀ · 2^0 + x₁ · 2^1 + ... + xₙ₋₁ · 2^(n-1)` (x₀ is the least significant bit)
-- - `eq(w, x) = ∏ᵢ (wᵢ · xᵢ + (1 - wᵢ) · (1 - xᵢ))` is the multilinear extension
--   of the equality function

def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])

@[simp]
theorem lagrangeBasis_zero {w : Vector R 0} : lagrangeBasis w = #v[1] := by rfl

#eval lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
#eval Nat.digits 2 8

/-- The `i`-th element of `lagrangeBasis w` is the product of `w[j]` if the `j`-th bit of `i` is 1,
    and `1 - w[j]` if the `j`-th bit of `i` is 0. -/
theorem lagrangeBasis_getElem {w : Vector R n} (i : Fin (2 ^ n)) :
    (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j] := by
  rw [lagrangeBasis]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]

variable {S : Type*} [CommRing S]

def map (f : R →+* S) (p : MlPolyEval R n) : MlPolyEval S n :=
  Vector.map (fun a => f a) p

/-- Evaluate a `MlPolyEval` at a point -/
def eval (p : MlPolyEval R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)

def eval₂ (p : MlPolyEval R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

-- Theorems about evaluations

-- Evaluation at a point in the Boolean hypercube is equal to the corresponding evaluation in the
-- array
-- theorem eval_eq_eval_array (p : MlPoly R) (x : Array Bool) (h : x.size = p.nVars): eval p
-- x.map (fun b => b) = p.evals.get! (x.foldl (fun i elt => i * 2 + elt) 0) := by unfold eval unfold
-- dotProduct simp [↓reduceIte, h] sorry
end MlPolyLagrangeBasisAndEvaluations
end MlPolyEval

section ListFoldLemmas
universe u v

theorem List.append_getLast_dropLast {α : Type u} (l : List α) (h : l ≠ []) :
  l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil =>
    contradiction
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp [List.dropLast, List.getLast]
    | cons hd' tl' =>
      simp only [List.dropLast_cons₂, List.getLast]
      simp only [List.cons_append, List.cons.injEq, true_and]
      apply ih

theorem List.foldl_split_outer {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): List.foldl (f:=f) (init:=init) (l)
    = f (List.foldl (f:=f) (init:=init) (l.dropLast)) (l.getLast (by omega)) := by
  conv_lhs => rw [← List.append_getLast_dropLast l h]
  rw [List.foldl_append]
  rfl

theorem List.foldl_split_inner {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) (h : l ≠ []): List.foldl (f:=f) (init:=init) (l)
    = List.foldl (f:=f) (init:=f (init) (l.head (by omega))) (l.tail) := by
  have h_l_eq: l = List.cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (List.head_cons_tail l h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [List.foldl_cons]

theorem List.foldr_split_outer {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): List.foldr (f:=f) (init:=init) (l)
    = f (l.head (by omega)) (List.foldr (f:=f) (init:=init) (l.tail)) := by
  have h_l_eq: l = List.cons (l.head (by omega)) (l.tail) := by
    exact Eq.symm (List.head_cons_tail l h)
  conv_lhs => enter [3]; rw [h_l_eq]
  rw [List.foldr_cons]

theorem List.foldr_split_inner {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (l : List α) (h : l ≠ []): List.foldr (f:=f) (init:=init) (l)
    = List.foldr (f:=f) (init:=f (l.getLast (by omega)) (init)) (l.dropLast) := by
  conv_lhs => rw [← List.append_getLast_dropLast l h]
  rw [List.foldr_append]
  rfl
end ListFoldLemmas

namespace MlPoly

-- Conversion between the coefficient (i.e. monomial) and evaluation (on the Boolean hypercube)
-- representations.

variable {R : Type*} [AddCommGroup R]

/-- **One level** of the zeta‑transform.

If the `j`‑th least significant bit of the index `i` is `1`, we replace `v[i]` with
`v[i] + v[i with bit j cleared]`; otherwise we leave it unchanged. -/
@[inline] def monoToLagrangeLevel {n : ℕ} (j : Fin n) : Vector R (2 ^ n) → Vector R (2 ^ n) :=
  fun v =>
    letI stride : ℕ := 2 ^ j.val    -- distance to the "partner" index
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
    letI stride : ℕ := 2 ^ j.val  -- distance to the "partner" index
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

/-- The O(n^3) computable version of the Mobius Transform -/
def lagrangeToMono_computable (p : MlPolyEval R n) : MlPolyEval R n :=
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

#eval lagrangeToMono 2 #v[(78 : ℤ), 3, 4, 100]
#eval lagrangeToMono_computable (n:=2) #v[(78 : ℤ), 3, 4, 100]

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

lemma forwardRange_succ_right_ne_empty (n : ℕ) (r : Fin (n-1)) (l : Fin (r.val + 1)) :
  forwardRange n ⟨r + 1, by omega⟩ ⟨l, by simp only; omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_pred_le_ne_empty (n : ℕ) (r : Fin n) (l : Fin (r.val + 1))
    (h_l_gt_0 : l.val > 0) : forwardRange n r ⟨l.val - 1, by omega⟩ ≠ [] := by
  rw [forwardRange]
  simp only [List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ, ne_eq,
    reduceCtorEq, not_false_eq_true]

lemma forwardRange_dropLast (n : ℕ) (r : Fin (n-1)) (l : Fin (r.val + 1)) :
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

lemma monoToLagrange_eq_monoToLagrange_segment (n: ℕ) [NeZero n] (v: Vector R (2 ^ n)) :
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  monoToLagrange n v = monoToLagrange_segment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold monoToLagrange monoToLagrange_segment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma lagrangeToMono_eq_lagrangeToMono_segment (n: ℕ) [NeZero n] (v: Vector R (2 ^ n)) :
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  lagrangeToMono n v = lagrangeToMono_segment n (r:=⟨n - 1, by omega⟩) (l:=⟨0, by omega⟩) v := by
  have h_n_ne_zero: n ≠ 0 := by exact NeZero.ne n
  unfold lagrangeToMono lagrangeToMono_segment
  simp only [Fin.zero_eta]
  congr
  exact Eq.symm (forwardRange_0_eq_finRange n)

lemma testBit_of_sub_two_pow_of_bit_1 {n i: ℕ} (h_testBit_eq_1: (n).testBit i = true) :
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
  ext i1
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      (expose_names; exact Nat.sub_lt_of_lt h)
    have h_as_assoc := add_sub_assoc (a:=v[i1]'(by omega))
      (b:=v[i1 - 2 ^ i.val]'(h_id_lt)) (c:=v[i1 - 2 ^ i.val]'(h_id_lt))
    rw [h_as_assoc, sub_self, add_zero]
  else
    simp only [h_i1_testBit, Bool.false_eq_true, ↓reduceIte]

theorem monoToLagrangeLevel_lagrangeToMonoLevel_id (v : Vector R (2 ^ n)) (i : Fin n) :
  monoToLagrangeLevel i (lagrangeToMonoLevel i v) = v := by
  unfold lagrangeToMonoLevel monoToLagrangeLevel
  simp only [Vector.getElem_ofFn]
  ext i1
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.getElem_ofFn]
  if h_i1_testBit: i1.testBit i.val = true then
    simp only [h_i1_testBit, ↓reduceIte]
    have h_testBit_sub_two_pow := testBit_of_sub_two_pow_of_bit_1 h_i1_testBit
    simp only [h_testBit_sub_two_pow, Bool.false_eq_true, ↓reduceIte]
    have h_id_lt: i1 - 2 ^ i.val < 2 ^ n := by
      (expose_names; exact Nat.sub_lt_of_lt h)
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

#eval MlPoly.zero (n := 2) (R := ℤ)
#eval MlPoly.add #v[1, 2, 3, 4] #v[5, 6, 7, 8] (n := 2) (R := ℤ)
#eval MlPoly.smul 2 #v[1, 2, 3, 4] (n := 2) (R := ℤ)
#eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2, 3] (n := 3)
#eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2] (n := 2)
#eval MlPolyEval.eval #v[1, 2, 3, 4] #v[(1 : ℤ), 2] (n := 2)
#eval MlPoly.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4]
#eval MlPoly.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10]
#eval MlPoly.lagrangeToMono 2 (MlPoly.monoToLagrange 2 #v[(1 : ℤ), 2, 3, 4])
#eval MlPoly.monoToLagrange 2 (MlPoly.lagrangeToMono 2 #v[(1 : ℤ), 3, 4, 10])
#eval MlPoly.monoToLagrange 1 #v[(1 : ℤ), 2]
#eval MlPoly.monoToLagrange 3 #v[(1 : ℤ), 2, 3, 4, 5, 6, 7, 8]
#eval MlPolyEval.lagrangeBasis #v[(1 : ℤ)] (n := 1)
#eval MlPolyEval.lagrangeBasis #v[(1 : ℤ), 2, 3, 4] (n := 4)
#eval (MlPoly.mk 2 #v[1, 2, 3, 4]) + (MlPoly.mk 2 #v[5, 6, 7, 8])
#eval ((4: ℤ) • (MlPoly.mk 2 #v[(1: ℤ), 2, 3, 4]))

end Tests
