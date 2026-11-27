/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolation
public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationBound
public import CompPoly.Univariate.CoefficientInterpolation
public import CompPoly.Univariate.ToPoly.RingHom

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Measured interpolation with a shared nodal polynomial

Build the nodal polynomial once. Each interpolation term uses a synthetic quotient
and Horner evaluation of that quotient at the node.
-/

@[expose] public section

namespace CompPoly.Arithmetic

open OracleComp OracleSpec
open CPolynomial (Raw)

variable {F : Type} [Field F] [DecidableEq F]

private def hornerStep (p : Raw F) (x : F) (i : Fin p.size) (a : F) : F :=
  a * x + p[i.val]?.getD 0

private def hornerCell (p : Raw F) (x : F) (i : Fin p.size) (a : F) :
    OracleComp (ArithmeticSpec F) {r : F // r = hornerStep p x i a} := do
  let c ← coefficientRead p i.val
  let m ← mul a x
  let r ← add m.val c.val
  pure ⟨r.val, by rw [r.property, m.property, c.property]; rfl⟩

omit [DecidableEq F] in
private theorem coeffList_eq (p : Raw F) :
    (List.finRange p.size).map (fun i ↦ p[i.val]?.getD 0) = p.toList := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [List.getElem_finRange]

/-- Evaluate a raw coefficient array by Horner's method with explicit reads and field operations. -/
private def evalRawHorner (p : Raw F) (x : F) :
    OracleComp (ArithmeticSpec F) {r : F // r = Raw.eval x p} := do
  let r ← certifiedFoldr (hornerStep p x) (hornerCell p x) (List.finRange p.size) 0
  pure ⟨r.val, by
    rw [r.property, ← Raw.evalHorner_eq_eval, Raw.evalHorner, Raw.eval₂Horner,
      ← Array.foldr_toList, ← coeffList_eq, List.foldr_map]
    rfl⟩

private def syntheticStep (p : CPolynomial F) (x : F) (i : ℕ) (a : F × List F) :
    F × List F :=
  let q := p.coeff (i + 1) + x * a.1
  (q, q :: a.2)

private def syntheticCell (p : CPolynomial F) (x : F) (i : ℕ) (a : F × List F) :
    OracleComp (ArithmeticSpec F) {r : F × List F // r = syntheticStep p x i a} := do
  let c ← coefficientRead p.val (i + 1)
  let m ← mul x a.1
  let q ← add c.val m.val
  pure ⟨(q.val, q.val :: a.2), by
    rw [q.property, m.property, c.property]
    simp [syntheticStep, CPolynomial.coeff, Raw.coeff, Array.getD_eq_getD_getElem?]⟩

private def syntheticFold (p : CPolynomial F) (x : F) : F × List F :=
  (List.range (p.val.size - 1)).foldr (syntheticStep p x) (0, [])

omit [DecidableEq F] in
private theorem syntheticFold_size (p : CPolynomial F) (x : F) :
    (syntheticFold p x).2.length = p.val.size - 1 := by
  have h (l : List ℕ) :
      (l.foldr (syntheticStep p x) (0, [])).2.length = l.length := by
    induction l with
    | nil => rfl
    | cons i l ih => simpa [syntheticStep] using congrArg Nat.succ ih
  simp [syntheticFold, h]

omit [DecidableEq F] in
private theorem syntheticFold_toPoly (p : CPolynomial F) (x : F) :
    Raw.toPoly (syntheticFold p x).2.toArray =
      p.toPoly /ₘ (Polynomial.X - Polynomial.C x) := by
  classical
  have hfactor : (CPolynomial.linearFactor x).toPoly =
      Polynomial.X - Polynomial.C x := by
    rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
      CPolynomial.C_toPoly, Polynomial.C_neg]
    ring
  have hmonic : (CPolynomial.linearFactor x).monic := by
    rw [CPolynomial.monic_toPoly_iff, hfactor]
    exact Polynomial.monic_X_sub_C x
  rw [← hfactor, ← CPolynomial.divByMonic_toPoly_eq_divByMonic p _ hmonic,
    ← CPolynomial.divByLinearFactor_eq_divByMonic, CPolynomial.divByLinearFactor,
    List.foldl_reverse, CPolynomial.ofArray_toPoly]
  rfl

private def nodalStep {m : ℕ} (nodes : Array F) (i : Fin m) (p : Raw F) : Raw F :=
  Raw.mulRaw #[-(nodes[i.val]?.getD 0), 1] p

private def nodalCell {m : ℕ} (nodes : Array F) (i : Fin m) (p : Raw F) :
    OracleComp (ArithmeticSpec F) {q : Raw F // q = nodalStep nodes i p} := do
  let x ← nodeRead nodes i.val
  let negX ← sub 0 x.val
  let q ← mulRaw #[negX.val, 1] p
  pure ⟨q.val, by rw [q.property, negX.property, x.property, zero_sub]; rfl⟩

private def nodalRaw {m : ℕ} (nodes : Array F) (is : List (Fin m)) : Raw F :=
  is.foldr (nodalStep nodes) #[1]

omit [DecidableEq F] in
private theorem linear_toPoly (x : F) : Raw.toPoly #[-x, 1] =
    Polynomial.X - Polynomial.C x := by
  ext i
  rw [Raw.coeff_toPoly]
  rcases i with _ | _ | i <;> simp [Raw.coeff, Polynomial.coeff_X]

omit [DecidableEq F] in
private theorem rawMul_toPoly (p q : Raw F) :
    (Raw.mulRaw p q).toPoly = p.toPoly * q.toPoly := by
  classical
  rw [← Raw.toPoly_trim]
  exact Raw.toPoly_mul p q

omit [DecidableEq F] in
private theorem nodalRaw_toPoly {m : ℕ} (nodes : Array F) (is : List (Fin m)) :
    (nodalRaw nodes is).toPoly =
      (is.map fun i ↦ Polynomial.X - Polynomial.C (nodes[i.val]?.getD 0)).prod := by
  induction is with
  | nil => change (Raw.C (1 : F)).toPoly = 1; simp
  | cons i is ih =>
    change (Raw.mulRaw #[-(nodes[i.val]?.getD 0), 1] (nodalRaw nodes is)).toPoly = _
    rw [rawMul_toPoly, linear_toPoly, ih]
    rfl

omit [DecidableEq F] in
private theorem nodalRaw_finRange_toPoly (nodes : Array F) (m : ℕ) :
    (nodalRaw nodes (List.finRange m)).toPoly =
      Lagrange.nodal Finset.univ (fun i : Fin m ↦ nodes[i.val]?.getD 0) := by
  rw [nodalRaw_toPoly, Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, Finset.val_univ_fin,
    Multiset.map_coe, Multiset.prod_coe]

private def termStep {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (i : Fin m) (sum : Raw F) : Raw F :=
  let x := nodes[i.val]?.getD 0
  let y := values[i.val]?.getD 0
  let q := (syntheticFold p x).2.toArray
  Raw.addRaw (Raw.mulRaw (Raw.C (y * (Raw.eval x q)⁻¹)) q) sum

private def termCell {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (i : Fin m) (sum : Raw F) : OracleComp (ArithmeticSpec F)
      {r : Raw F // r = termStep p nodes values i sum} := do
  let x ← nodeRead nodes i.val
  let y ← valueRead values i.val
  let coeffs ← certifiedFoldr (syntheticStep p x.val) (syntheticCell p x.val)
    (List.range (p.val.size - 1)) (0, [])
  let q : Raw F := coeffs.val.2.toArray
  let weightDenominator ← evalRawHorner q x.val
  let weight ← inv weightDenominator.val
  let c ← mul y.val weight.val
  let t ← mulRaw (Raw.C c.val) q
  let r ← addRaw t.val sum
  pure ⟨r.val, by
    rw [r.property, t.property, c.property, weight.property, weightDenominator.property,
      y.property]
    unfold q
    rw [coeffs.property, x.property]
    rfl⟩

omit [DecidableEq F] in
private theorem termStep_toPoly {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (hp : p.toPoly = Lagrange.nodal Finset.univ (fun i : Fin m ↦ nodes[i.val]?.getD 0))
    (i : Fin m) (sum : Raw F) :
    (termStep p nodes values i sum).toPoly =
        Polynomial.C (values[i.val]?.getD 0) *
          Lagrange.basis Finset.univ (fun j : Fin m ↦ nodes[j.val]?.getD 0) i + sum.toPoly := by
  let x := fun j : Fin m ↦ nodes[j.val]?.getD 0
  let q : Raw F := (syntheticFold p (x i)).2.toArray
  have hq : q.toPoly = Lagrange.nodal ((Finset.univ : Finset (Fin m)).erase i) x := by
    unfold q
    rw [syntheticFold_toPoly, hp, Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
    exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)
  change (Raw.addRaw (Raw.mulRaw (Raw.C (values[i.val]?.getD 0 * (Raw.eval (x i) q)⁻¹)) q)
    sum).toPoly = _
  rw [Raw.toPoly_addRaw, rawMul_toPoly, Raw.toPoly_C, ← Raw.eval_toPoly_eq_eval, hq,
    ← Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Polynomial.C_mul,
    Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i), mul_assoc]

omit [DecidableEq F] in
private theorem terms_toPoly {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (hp : p.toPoly = Lagrange.nodal Finset.univ (fun i : Fin m ↦ nodes[i.val]?.getD 0))
    (is : List (Fin m)) :
    (is.foldr (termStep p nodes values) #[]).toPoly =
      (is.map fun i ↦ Polynomial.C (values[i.val]?.getD 0) *
        Lagrange.basis Finset.univ (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).sum := by
  induction is with
  | nil => exact Raw.toPoly_zero
  | cons i is ih => rw [List.foldr_cons, termStep_toPoly _ _ _ hp, ih, List.map_cons, List.sum_cons]

/-- Interpolate cached nodes and values using one shared nodal polynomial.
The result type fixes the same value as `interpolate`. This holds also for repeated nodes and
for reads past the end of an array, which default to zero. -/
@[no_expose] def interpolateQuadratic (nodes values : Array F) (m : ℕ) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial F // p =
      CPolynomial.CLagrange.interpolate (Finset.univ : Finset (Fin m))
        (fun i ↦ nodes[i.val]?.getD 0) (fun i ↦ values[i.val]?.getD 0)} := do
  let nodal ← certifiedFoldr (nodalStep nodes) (nodalCell nodes) (List.finRange m) #[1]
  let p ← canonicalRaw nodal.val
  let terms ← certifiedFoldr (termStep p.val nodes values) (termCell p.val nodes values)
    (List.finRange m) #[]
  let q ← canonicalRaw terms.val
  pure ⟨q.val, by
    apply CPolynomial.toPoly_injective
    rw [q.property, CPolynomial.ofArray_toPoly, terms.property, terms_toPoly,
      CPolynomial.CLagrange.cinterpolate_eq_interpolate, Lagrange.interpolate_apply,
      Finset.sum_eq_multiset_sum, Finset.val_univ_fin, Multiset.map_coe, Multiset.sum_coe]
    rw [p.property, CPolynomial.ofArray_toPoly, nodal.property]
    exact nodalRaw_finRange_toPoly nodes m⟩

private def linearPassProfile (n : ℕ) : ArithmeticCostKind → ℕ
  | .add | .mul | .coefficientRead => n
  | .metadata => n + 1
  | _ => 0

/-- Horner evaluation charges one coefficient read, multiplication, and addition per slot. -/
private theorem profileArithmetic_evalRawHorner (p : Raw F) (x : F) (kind : ArithmeticCostKind) :
    (profileArithmetic (evalRawHorner p x)).2 kind = linearPassProfile p.size kind := by
  have h (i : Fin p.size) (a : F) : (profileArithmetic (hornerCell p x i a)).2 kind =
      (if kind = .add ∨ kind = .mul ∨ kind = .coefficientRead then 1 else 0) := by
    cases kind <;> simp [hornerCell, arithmeticCost,
      ArithmeticOp.costKind]
  simp only [evalRawHorner, profileArithmetic_bind, profileArithmetic_pure, add_zero]
  rw [profileArithmetic_certifiedFoldr_of_constant _ _ _ _ _ _ h]
  cases kind <;> simp [linearPassProfile]

private theorem profile_syntheticFold (p : CPolynomial F) (x : F) (kind : ArithmeticCostKind) :
    (profileArithmetic (certifiedFoldr (syntheticStep p x) (syntheticCell p x)
      (List.range (p.val.size - 1)) (0, []))).2 kind =
        linearPassProfile (p.val.size - 1) kind := by
  have h (i : ℕ) (a : F × List F) : (profileArithmetic (syntheticCell p x i a)).2 kind =
      (if kind = .add ∨ kind = .mul ∨ kind = .coefficientRead then 1 else 0) := by
    cases kind <;> simp [syntheticCell, arithmeticCost,
      ArithmeticOp.costKind]
  rw [profileArithmetic_certifiedFoldr_of_constant _ _ _ _ _ _ h]
  cases kind <;> simp [linearPassProfile]

omit [DecidableEq F] in
private theorem nodalRaw_size {m : ℕ} (nodes : Array F) (is : List (Fin m)) :
    (nodalRaw nodes is).size = is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (Raw.mulRaw #[-(nodes[i.val]?.getD 0), 1] (nodalRaw nodes is)).size = _
    simp [Raw.size_mulRaw, ih]

private def nodalFoldBound (n : ℕ) : ArithmeticCostKind → ℕ
  | .add | .mul => n * (n + 1)
  | .sub | .nodeRead => n
  | .coefficientRead => 2 * (n * (n + 1))
  | .metadata => 2 * n ^ 2 + 4 * n + 1
  | _ => 0

private theorem profile_nodalCell {m : ℕ} (nodes : Array F) (i : Fin m) (p : Raw F)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (nodalCell nodes i p)).2 kind =
      match kind with
      | .add | .mul => 2 * p.size
      | .sub | .nodeRead => 1
      | .coefficientRead => 4 * p.size
      | .metadata => 3 * p.size + 2
      | _ => 0 := by
  cases kind <;> simp [nodalCell, profileArithmetic_mulRaw, arithmeticCost,
    ArithmeticOp.costKind] <;> omega

private theorem profile_nodalFold_le {m : ℕ} (nodes : Array F) (is : List (Fin m))
    (kind : ArithmeticCostKind) :
    (profileArithmetic (certifiedFoldr (nodalStep nodes) (nodalCell nodes) is #[1])).2 kind ≤
      nodalFoldBound is.length kind := by
  induction is with
  | nil =>
    cases kind <;> simp [certifiedFoldr, nodalFoldBound, arithmeticCost, ArithmeticOp.costKind]
  | cons i is ih =>
    rw [profileArithmetic_certifiedFoldr_cons]
    simp only [Pi.add_apply, profile_nodalCell,
      show (is.foldr (nodalStep nodes) #[1]).size = is.length + 1 from nodalRaw_size nodes is]
    cases kind <;> simp [nodalFoldBound, arithmeticCost, ArithmeticOp.costKind] at ih ⊢ <;>
      nlinarith

private def termCellBound (n : ℕ) : ArithmeticCostKind → ℕ
  | .add => 4 * n
  | .mul => 3 * n + 1
  | .inv | .nodeRead | .valueRead => 1
  | .coefficientRead => 6 * n
  | .metadata => 5 * n + 4
  | _ => 0

private theorem profile_termCell_le {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (i : Fin m) (acc : Raw F) (hacc : acc.size ≤ p.val.size - 1) (kind : ArithmeticCostKind) :
    (profileArithmetic (termCell p nodes values i acc)).2 kind ≤
      termCellBound (p.val.size - 1) kind := by
  have hsize (x : F) : (syntheticFold p x).2.toArray.size = p.val.size - 1 := by
    simpa only [List.size_toArray] using syntheticFold_size p x
  simp only [syntheticFold] at hsize
  cases kind <;> simp [termCell, profile_syntheticFold,
    profileArithmetic_evalRawHorner, profileArithmetic_mulRaw, profileArithmetic_addRaw,
    Raw.size_mulRaw, Raw.size_C, hsize, max_eq_left hacc,
    arithmeticCost, ArithmeticOp.costKind, linearPassProfile, termCellBound] <;> omega

omit [DecidableEq F] in
private theorem terms_size_le {m : ℕ} (p : CPolynomial F) (nodes values : Array F)
    (is : List (Fin m)) : (is.foldr (termStep p nodes values) #[]).size ≤ p.val.size - 1 := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simpa [termStep, Raw.size_addRaw, Raw.size_mulRaw, Raw.size_C, syntheticFold_size]
      using ih

/-- Per-kind budget for interpolation with a shared nodal polynomial. -/
def quadraticInterpolationProfileBound (m : ℕ) : ArithmeticCostKind → ℕ
  | .add => 5 * m ^ 2 + m
  | .sub | .inv | .valueRead => m
  | .mul => 4 * m ^ 2 + 2 * m
  | .eq => 2 * m + 1
  | .coefficientRead => 8 * m ^ 2 + 4 * m + 1
  | .nodeRead => 2 * m
  | .metadata => 7 * m ^ 2 + 11 * m + 5

/-- The measured interpolation program fits its quadratic budget on every pair of arrays. -/
theorem profileArithmetic_interpolateQuadratic_le (nodes values : Array F) (m : ℕ)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (interpolateQuadratic nodes values m)).2 kind ≤
      quadraticInterpolationProfileBound m kind := by
  let is := List.finRange m
  let p := CPolynomial.ofArray (nodalRaw nodes is)
  let ts := is.foldr (termStep p nodes values) #[]
  have hN := profile_nodalFold_le nodes is kind
  have hs : (nodalRaw nodes is).size = m + 1 := by simp [nodalRaw_size, is]
  have hp : p.val.size ≤ m + 1 := by
    change (nodalRaw nodes is).trim.size ≤ m + 1
    rw [← hs]
    exact CPolynomial.Raw.Trim.size_le_size _
  have hT := profileArithmetic_certifiedFoldr_le (termStep p nodes values)
    (termCell p nodes values) is #[] kind (termCellBound (p.val.size - 1) kind)
    (fun i js ↦ profile_termCell_le p nodes values i _ (terms_size_le p nodes values js) kind)
  have ht : ts.size ≤ p.val.size - 1 := terms_size_le p nodes values is
  have htrimN := profileArithmetic_trimRaw_le (nodalRaw nodes is) kind
  have htrimT := profileArithmetic_trimRaw_le ts kind
  unfold interpolateQuadratic
  rw [profileArithmetic_bind]
  dsimp only
  rw [profileArithmetic_certified_fst, profileArithmetic_bind]
  dsimp only
  rw [profileArithmetic_certified_fst, profileArithmetic_bind]
  dsimp only
  rw [profileArithmetic_certified_fst, profileArithmetic_bind]
  simp only [profileArithmetic_pure, add_zero, profileArithmetic_canonicalRaw, Pi.add_apply]
  change (profileArithmetic (certifiedFoldr (nodalStep nodes) (nodalCell nodes) is #[1])).2 kind +
    ((profileArithmetic (trimRaw (nodalRaw nodes is))).2 kind +
    ((profileArithmetic (certifiedFoldr (termStep p nodes values)
      (termCell p nodes values) is #[])).2 kind + (profileArithmetic (trimRaw ts)).2 kind)) ≤ _
  have hsize : p.val.size - 1 ≤ m := by omega
  have ht' := ht.trans hsize
  have hcell : termCellBound (p.val.size - 1) kind ≤ termCellBound m kind := by
    cases kind <;> simp [termCellBound] <;> omega
  have hT' := hT.trans (Nat.add_le_add_right (Nat.mul_le_mul_left is.length hcell) _)
  cases kind <;>
    simp only [is, List.length_finRange, hs, nodalFoldBound, termCellBound,
      quadraticInterpolationProfileBound, reduceCtorEq, true_or, false_or, ite_true, ite_false,
      Nat.mul_add, Nat.mul_zero, Nat.mul_one, Nat.add_zero, pow_two] at hN hT' htrimN htrimT ⊢ <;>
    first | omega | nlinarith only [hN, hT', htrimN, htrimT, ht']

/-- From four nodes onward, `quadraticInterpolationProfileBound` is at most
`interpolationProfileBound` in every coordinate. -/
theorem quadraticInterpolationProfileBound_le (m : ℕ) (hm : 4 ≤ m)
    (kind : ArithmeticCostKind) :
    quadraticInterpolationProfileBound m kind ≤ interpolationProfileBound m kind := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : 4 + k - 1 = k + 3 := by omega
  cases kind <;> simp only [quadraticInterpolationProfileBound, interpolationProfileBound, hk] <;>
    nlinarith only [Nat.zero_le k, Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]

/-- Interpolate cached samples with `interpolate` below four nodes and with
`interpolateQuadratic` from four nodes onward. Both branches return the same value. -/
def interpolateForReconstruction (nodes values : Array F) (m : ℕ) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial F // p =
      CPolynomial.CLagrange.interpolate (Finset.univ : Finset (Fin m))
        (fun i ↦ nodes[i.val]?.getD 0) (fun i ↦ values[i.val]?.getD 0)} :=
  if m < 4 then interpolate nodes values m else interpolateQuadratic nodes values m

/-- Budget for witness reconstruction, including the small-instance branch. -/
def reconstructionInterpolationProfileBound (m : ℕ) (kind : ArithmeticCostKind) : ℕ :=
  if m < 4 then interpolationProfileBound m kind else quadraticInterpolationProfileBound m kind

/-- `reconstructionInterpolationProfileBound` is at most `interpolationProfileBound` at every
size. -/
theorem reconstructionInterpolationProfileBound_le (m : ℕ) (kind : ArithmeticCostKind) :
    reconstructionInterpolationProfileBound m kind ≤ interpolationProfileBound m kind := by
  unfold reconstructionInterpolationProfileBound
  split
  · rfl
  · exact quadraticInterpolationProfileBound_le m (by omega) kind

/-- The reconstruction routine fits its per-kind budget at every size. -/
theorem profileArithmetic_interpolateForReconstruction_le (nodes values : Array F) (m : ℕ)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (interpolateForReconstruction nodes values m)).2 kind ≤
      reconstructionInterpolationProfileBound m kind := by
  by_cases hm : m < 4
  · simpa only [interpolateForReconstruction, reconstructionInterpolationProfileBound,
      ite_eq_left hm]
      using profileArithmetic_interpolate_le nodes values m kind
  · simpa only [interpolateForReconstruction, reconstructionInterpolationProfileBound,
      ite_eq_right hm]
      using profileArithmetic_interpolateQuadratic_le nodes values m kind

end CompPoly.Arithmetic
