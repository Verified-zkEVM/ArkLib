/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationCost
public import ArkLib.ToCompPoly.Univariate.ArithmeticConvolutionCost
public import ArkLib.ToCompPoly.Univariate.Size

import all CompPoly.Univariate.Lagrange
public import Mathlib.Tactic.Linarith

/-!
# Cubic bounds for measured interpolation

The bounds follow the raw convolution and trim recurrences. They include cached-array and
coefficient requests, equality tests, and designated control ticks for arbitrary input arrays.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
variable {F : Type} [Field F] [DecidableEq F]

private theorem basisDivisor_size_le (x y : F) :
    (CPolynomial.CLagrange.basisDivisor x y).val.size ≤ 2 := by
  rw [← CPolynomial.mem_degreeLT_iff_size_le, CPolynomial.degreeLT_toPoly,
    Polynomial.mem_degreeLT, CPolynomial.CLagrange.cbasisDivisor_eq_basisDivisor]
  by_cases h : x = y
  · subst y
    rw [Lagrange.degree_basisDivisor_self]
    exact WithBot.bot_lt_coe 2
  · rw [Lagrange.degree_basisDivisor_of_ne h]
    norm_num

private theorem basisListRaw_size_le {m : ℕ} (nodes : Array F)
    (i : Fin m) (l : List (Fin m)) :
    (CPolynomial.CLagrange.basisListRaw (fun j : Fin m ↦ nodes[j.val]?.getD 0) i l).size ≤
      l.length + 1 := by
  induction l with
  | nil => simp [CPolynomial.CLagrange.basisListRaw]
  | cons j l ih =>
    have h := CPolynomial.Raw.size_mulRaw_le
      (CPolynomial.CLagrange.basisDivisor (nodes[i.val]?.getD 0) (nodes[j.val]?.getD 0)).val
      (CPolynomial.CLagrange.basisListRaw (fun j : Fin m ↦ nodes[j.val]?.getD 0) i l)
    have hb := basisDivisor_size_le (nodes[i.val]?.getD 0) (nodes[j.val]?.getD 0)
    change _ ≤ (l.length + 1) + 1
    exact h.trans (by omega)

omit [Field F] [DecidableEq F] in
private theorem finRange_val (m : ℕ) :
    (Finset.univ : Finset (Fin m)).val = (List.finRange m : Multiset (Fin m)) := by
  have h : (List.finRange m).toFinset = Finset.univ := by ext i; simp
  rw [← h, List.toFinset_val, List.dedup_eq_self.mpr (List.nodup_finRange m)]

private theorem basis_size_le {m : ℕ} (nodes : Array F) (i : Fin m) :
    (CPolynomial.CLagrange.basis Finset.univ
      (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val.size ≤ m := by
  unfold CPolynomial.CLagrange.basis
  rw [Finset.erase_val, finRange_val, Multiset.coe_erase]
  refine (CPolynomial.Raw.Trim.size_le_size _).trans ?_
  have h := basisListRaw_size_le nodes i ((List.finRange m).erase i)
  have hlen : ((List.finRange m).erase i).length = m - 1 := by
    simp [List.length_erase_of_mem (by simp : i ∈ List.finRange m)]
  rw [hlen] at h
  have hpos : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  simpa [Nat.sub_add_cancel hpos] using h

private theorem interpolateListRaw_size_le {m : ℕ} (nodes values : Array F)
    (l : List (Fin m)) :
    (CPolynomial.CLagrange.interpolateListRaw Finset.univ
      (fun j : Fin m ↦ nodes[j.val]?.getD 0) (fun j ↦ values[j.val]?.getD 0) l).size ≤ m := by
  induction l with
  | nil => simp [CPolynomial.CLagrange.interpolateListRaw]
  | cons i l ih =>
    have ht := CPolynomial.Raw.size_mulRaw_le (CPolynomial.Raw.C (values[i.val]?.getD 0))
      (CPolynomial.CLagrange.basis Finset.univ
        (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val
    have hb := basis_size_le nodes i
    have hterm : (CPolynomial.Raw.mulRaw (CPolynomial.Raw.C (values[i.val]?.getD 0))
        (CPolynomial.CLagrange.basis Finset.univ
          (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val).size ≤ m := by
      simp only [CPolynomial.Raw.size_C] at ht
      omega
    simpa only [CPolynomial.CLagrange.interpolateListRaw, List.foldr_cons,
      CPolynomial.Raw.add_size] using max_le hterm ih

/-- A Lagrange divisor charges both constants, canonical subtraction, and canonical product. -/
theorem profileArithmetic_basisDivisor (x y : F) :
    (profileArithmetic (basisDivisor x y)).2 =
      arithmeticCost (.sub x y) + arithmeticCost (.inv (x - y)) +
      (profileArithmetic (constant (x - y)⁻¹)).2 +
      (profileArithmetic (constant y)).2 +
      (profileArithmetic (subPolynomial CPolynomial.X (CPolynomial.C y))).2 +
      (profileArithmetic (mulPolynomial (CPolynomial.C (x - y)⁻¹)
        (CPolynomial.X - CPolynomial.C y))).2 := by
  funext kind
  simp [basisDivisor, Nat.add_assoc]

private def divisorBound (kind : ArithmeticCostKind) : ℕ :=
  match kind with
  | .add => 4
  | .sub => 2
  | .mul => 2
  | .inv => 1
  | .eq => 6
  | .coefficientRead => 18
  | .metadata => 23
  | .nodeRead | .valueRead => 0

private theorem profileArithmetic_mulPolynomial_le_one_two (p q : CPolynomial F)
    (hp : p.val.size ≤ 1) (hq : q.val.size ≤ 2) (kind : ArithmeticCostKind) :
    (profileArithmetic (mulPolynomial p q)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .eq then 2
      else if kind = .coefficientRead then 9
      else if kind = .metadata then 11 else 0 := by
  have hm := profileArithmetic_mulRaw_le_of_size_le_one p.val q.val hp kind
  have ht := profileArithmetic_trimRaw_le (CPolynomial.Raw.mulRaw p.val q.val) kind
  have hs := CPolynomial.Raw.size_mulRaw_le p.val q.val
  cases kind <;> simp [profileArithmetic_mulPolynomial] at hm ht ⊢ <;> omega

private theorem profileArithmetic_basisDivisor_le (x y : F) (kind : ArithmeticCostKind) :
    (profileArithmetic (basisDivisor x y)).2 kind ≤ divisorBound kind := by
  have hC := profileArithmetic_constant_le (x - y)⁻¹ kind
  have hD := profileArithmetic_constant_le y kind
  have hS := profileArithmetic_subPolynomial_le
    (CPolynomial.X : CPolynomial F) (CPolynomial.C y) kind
  have hM := profileArithmetic_mulPolynomial_le_one_two (CPolynomial.C (x - y)⁻¹)
    (CPolynomial.X - CPolynomial.C y)
    (CPolynomial.size_C_le _) (CPolynomial.size_X_sub_C_le _) kind
  have hnode := CPolynomial.size_C_le y
  have hX : (CPolynomial.X : CPolynomial F).val.size = 2 := CPolynomial.size_X
  cases kind <;>
    simp [profileArithmetic_basisDivisor, divisorBound, arithmeticCost,
      ArithmeticOp.costKind, hX, max_eq_left (show (CPolynomial.C y).val.size ≤ 2 by omega)]
      at hC hD hS hM ⊢ <;> omega

private def basisListRawBound (t : ℕ) (kind : ArithmeticCostKind) : ℕ :=
  match kind with
  | .add => t ^ 2 + 6 * t
  | .sub => 2 * t
  | .mul => t ^ 2 + 3 * t
  | .inv => t
  | .eq => 6 * t
  | .coefficientRead => 3 * t ^ 2 + 25 * t
  | .metadata => 2 * t ^ 2 + 34 * t + 1
  | .nodeRead => 2 * t
  | .valueRead => 0

private def basisBound (t : ℕ) (kind : ArithmeticCostKind) : ℕ :=
  match kind with
  | .add => t ^ 2 + 6 * t
  | .sub => 2 * t
  | .mul => t ^ 2 + 3 * t
  | .inv => t
  | .eq => 7 * t + 1
  | .coefficientRead => 3 * t ^ 2 + 26 * t + 1
  | .metadata => 2 * t ^ 2 + 35 * t + 3
  | .nodeRead => 2 * t
  | .valueRead => 0

private theorem profileArithmetic_basisListRaw_le (nodes : Array F) {m : ℕ}
    (i : Fin m) (l : List (Fin m)) (kind : ArithmeticCostKind) :
    (profileArithmetic (basisListRaw nodes i l)).2 kind ≤ basisListRawBound l.length kind := by
  induction l with
  | nil =>
    cases kind <;>
      simp [basisListRaw, certifiedFoldr, basisListRawBound, arithmeticCost, ArithmeticOp.costKind]
  | cons j l ih =>
    have hd := profileArithmetic_basisDivisor_le
      (nodes[i.val]?.getD 0) (nodes[j.val]?.getD 0) kind
    have hs := basisListRaw_size_le nodes i l
    have hm := profileArithmetic_mulRaw_le_of_size_le_two
      (CPolynomial.CLagrange.basisDivisor (nodes[i.val]?.getD 0) (nodes[j.val]?.getD 0)).val
      (CPolynomial.CLagrange.basisListRaw (fun j : Fin m ↦ nodes[j.val]?.getD 0) i l)
      (basisDivisor_size_le _ _) kind
    dsimp only [CPolynomial.CLagrange.basisListRaw] at hm hs
    simp only [basisListRaw, profileArithmetic_bind_certified, profileArithmetic_pure,
      add_zero] at ih ⊢
    rw [profileArithmetic_certifiedFoldr_cons]
    cases kind <;>
      simp_all [basisListRawBound, divisorBound, arithmeticCost,
        ArithmeticOp.costKind, pow_two] <;> nlinarith

private theorem profileArithmetic_basis_le (nodes : Array F) {m : ℕ} (i : Fin m)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (basis nodes i)).2 kind ≤ basisBound (m - 1) kind := by
  let l := (List.finRange m).erase i
  have hlen : l.length = m - 1 := by
    simp [l, List.length_erase_of_mem (by simp : i ∈ List.finRange m)]
  have hb := profileArithmetic_basisListRaw_le nodes i l kind
  have hs := basisListRaw_size_le nodes i l
  have ht := profileArithmetic_trimRaw_le
    (CPolynomial.CLagrange.basisListRaw (fun j : Fin m ↦ nodes[j.val]?.getD 0) i l) kind
  rw [hlen] at hb hs
  cases kind <;>
    simp_all [basis, profileArithmetic_canonicalRaw, basisBound, basisListRawBound, l, pow_two] <;>
      nlinarith

private def interpolationCellBound (m : ℕ) (kind : ArithmeticCostKind) : ℕ :=
  basisBound (m - 1) kind +
    match kind with
    | .add => 2 * m
    | .mul => m
    | .coefficientRead => 5 * m + 1
    | .metadata => 3 * m + 5
    | .valueRead => 1
    | _ => 0

/-- Uniform bounds for the interpolation program's primitive coordinates. -/
def interpolationProfileBound (m : ℕ) (kind : ArithmeticCostKind) : ℕ :=
  let t := m - 1
  match kind with
  | .add => m * (t ^ 2 + 6 * t + 2 * m)
  | .sub => 2 * m * t
  | .mul => m * (t ^ 2 + 3 * t + m)
  | .inv => m * t
  | .eq => m * (7 * t + 1) + m
  | .coefficientRead => m * (3 * t ^ 2 + 26 * t + 5 * m + 2) + m
  | .metadata => m * (2 * t ^ 2 + 35 * t + 3 * m + 8) + 2 * m + 2
  | .nodeRead => 2 * m * t
  | .valueRead => m

/-- The executed interpolation program satisfies the uniform primitive-profile envelope. -/
theorem profileArithmetic_interpolate_le (nodes values : Array F) (m : ℕ)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (interpolate nodes values m)).2 kind ≤ interpolationProfileBound m kind := by
  let f (i : Fin m) (acc : CPolynomial.Raw F) := CPolynomial.Raw.addRaw
    (CPolynomial.Raw.mulRaw (CPolynomial.Raw.C (values[i.val]?.getD 0))
      (CPolynomial.CLagrange.basis Finset.univ
        (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val) acc
  let step (i : Fin m) (acc : CPolynomial.Raw F) :
      OracleComp (ArithmeticSpec F) {r : CPolynomial.Raw F // r = f i acc} := do
    let y ← valueRead values i.val
    let b ← basis nodes i
    let p ← mulRaw (CPolynomial.Raw.C y.val) b.val.val
    let q ← addRaw p.val acc
    pure ⟨q.val, by rw [q.property, p.property, b.property, y.property]⟩
  have hstep (i : Fin m) (ys : List (Fin m)) :
      (profileArithmetic (step i (ys.foldr f #[]))).2 kind ≤ interpolationCellBound m kind := by
    have hb := profileArithmetic_basis_le nodes i kind
    have hs := basis_size_le nodes i
    have hm := profileArithmetic_mulRaw_le_of_size_le_one
      (CPolynomial.Raw.C (values[i.val]?.getD 0))
      (CPolynomial.CLagrange.basis Finset.univ
        (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val (by simp) kind
    have hterm := CPolynomial.Raw.size_mulRaw_le (CPolynomial.Raw.C (values[i.val]?.getD 0))
      (CPolynomial.CLagrange.basis Finset.univ
        (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val
    simp only [CPolynomial.Raw.size_C] at hterm
    have ht := interpolateListRaw_size_le nodes values ys
    change (ys.foldr f (#[] : CPolynomial.Raw F)).size ≤ m at ht
    have hmax : max (CPolynomial.Raw.mulRaw (CPolynomial.Raw.C (values[i.val]?.getD 0))
        (CPolynomial.CLagrange.basis Finset.univ
          (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val).size
        (ys.foldr f #[]).size ≤ m := by
      exact max_le (by omega) ht
    cases kind <;>
      simp [step, interpolationCellBound, basisBound, profileArithmetic_addRaw, arithmeticCost,
        ArithmeticOp.costKind] at hb hm ⊢ <;> omega
  have hf := profileArithmetic_certifiedFoldr_le f step (List.finRange m) #[] kind
    (interpolationCellBound m kind) hstep
  have hs := interpolateListRaw_size_le nodes values (List.finRange m)
  have ht := profileArithmetic_trimRaw_le ((List.finRange m).foldr f #[]) kind
  change ((List.finRange m).foldr f (#[] : CPolynomial.Raw F)).size ≤ m at hs
  simp only [interpolate, profileArithmetic_bind_certified, profileArithmetic_pure,
    profileArithmetic_canonicalRaw, Pi.add_apply, add_zero]
  change (profileArithmetic (certifiedFoldr f step (List.finRange m) #[])).2 kind +
    (profileArithmetic (trimRaw ((List.finRange m).foldr f #[]))).2 kind ≤ _
  cases kind <;>
    simp [interpolationProfileBound, interpolationCellBound, basisBound] at hf ht ⊢ <;>
    nlinarith

/-- Every coordinate of the interpolation envelope satisfies the cubic budget. -/
theorem interpolationProfileBound_le (m : ℕ) (kind : ArithmeticCostKind) :
    interpolationProfileBound m kind ≤ 100 * (m + 1) ^ 3 := by
  have ht := Nat.sub_le m 1
  have hsquare := Nat.mul_self_le_mul_self ht
  have hcube := Nat.mul_le_mul_left m hsquare
  have hprod := Nat.mul_le_mul_left m ht
  cases kind <;> simp only [interpolationProfileBound] <;> nlinarith

/-- Addition and subtraction together satisfy the same cubic budget. -/
theorem interpolationProfileBound_add_sub_le (m : ℕ) :
    interpolationProfileBound m .add + interpolationProfileBound m .sub ≤
      100 * (m + 1) ^ 3 := by
  have ht := Nat.sub_le m 1
  have hsquare := Nat.mul_self_le_mul_self ht
  have hcube := Nat.mul_le_mul_left m hsquare
  have hprod := Nat.mul_le_mul_left m ht
  simp only [interpolationProfileBound]
  nlinarith

/-- Every interpolation coordinate satisfies a cubic primitive budget. -/
theorem profileArithmetic_interpolate_cubic_le (nodes values : Array F) (m : ℕ)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (interpolate nodes values m)).2 kind ≤ 100 * (m + 1) ^ 3 :=
  (profileArithmetic_interpolate_le nodes values m kind).trans (interpolationProfileBound_le m kind)

/-- The combined addition and subtraction count satisfies one cubic budget. -/
theorem profileArithmetic_interpolate_add_sub_le (nodes values : Array F) (m : ℕ) :
    (profileArithmetic (interpolate nodes values m)).2 .add +
      (profileArithmetic (interpolate nodes values m)).2 .sub ≤ 100 * (m + 1) ^ 3 :=
  (Nat.add_le_add (profileArithmetic_interpolate_le nodes values m .add)
    (profileArithmetic_interpolate_le nodes values m .sub)).trans
    (interpolationProfileBound_add_sub_le m)

end CompPoly.Arithmetic

namespace CompPoly.CPolynomial.CLagrange

/-- Interpolation on `Fin m` has at most `m` coefficients, allowing repeated nodes. -/
theorem size_interpolate_univ_le {F : Type} [Field F] [DecidableEq F] {m : ℕ}
    (x y : Fin m → F) :
    (interpolate Finset.univ x y).val.size ≤ m := by
  let nodes := Array.ofFn x
  let values := Array.ofFn y
  have hraw := Arithmetic.interpolateListRaw_size_le nodes values (List.finRange m)
  have hsize : (interpolate Finset.univ
      (fun j : Fin m ↦ nodes[j.val]?.getD 0) (fun j ↦ values[j.val]?.getD 0)).val.size ≤ m := by
    change (interpolateRaw Finset.univ _ _).val.size ≤ m
    unfold interpolateRaw
    rw [Arithmetic.finRange_val]
    exact (Raw.Trim.size_le_size _).trans hraw
  simpa [nodes, values] using hsize

end CompPoly.CPolynomial.CLagrange
