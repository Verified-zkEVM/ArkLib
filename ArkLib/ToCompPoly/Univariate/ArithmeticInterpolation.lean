/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomial
public import CompPoly.Univariate.Lagrange

import all CompPoly.Univariate.Lagrange

/-!
# Measured Lagrange interpolation

Cached node and value arrays supply every field input to interpolation. Basis products and
the interpolation sum retain the raw-array folds and deferred trims of `CLagrange`.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
variable {F : Type} [Field F] [DecidableEq F]

/-- Compute one Lagrange divisor with all canonicalization operations charged. -/
def basisDivisor (xi xj : F) :
    OracleComp (ArithmeticSpec F)
      {r : CPolynomial F // r = CPolynomial.CLagrange.basisDivisor xi xj} := do
  let d ← sub xi xj
  let dInv ← inv d.val
  let scalar ← constant dInv.val
  let node ← constant xj
  let factor ← subPolynomial CPolynomial.X node.val
  let r ← mulPolynomial scalar.val factor.val
  pure ⟨r.val, by
    rw [r.property, scalar.property, factor.property, node.property,
      dInv.property, d.property]
    rfl⟩

omit [Field F] [DecidableEq F] in
private theorem finRange_val (m : ℕ) :
    (Finset.univ : Finset (Fin m)).val = (List.finRange m : Multiset (Fin m)) := by
  have h : (List.finRange m).toFinset = Finset.univ := by ext i; simp
  rw [← h, List.toFinset_val, List.dedup_eq_self.mpr (List.nodup_finRange m)]

/-- Multiply an explicit list of Lagrange divisors without intermediate trimming. -/
def basisListRaw (nodes : Array F) {m : ℕ} (i : Fin m) (l : List (Fin m)) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial.Raw F // p =
      CPolynomial.CLagrange.basisListRaw (fun j : Fin m ↦ nodes[j.val]?.getD 0) i l} := do
  let p ← certifiedFoldr (F := F) (A := Fin m) (B := CPolynomial.Raw F)
    (fun j acc ↦ CPolynomial.Raw.mulRaw
      (CPolynomial.CLagrange.basisDivisor
        (nodes[i.val]?.getD 0) (nodes[j.val]?.getD 0)).val acc)
    (fun j acc ↦ do
      let xi ← nodeRead nodes i.val
      let xj ← nodeRead nodes j.val
      let factor ← basisDivisor xi.val xj.val
      let p ← mulRaw factor.val.val acc
      pure ⟨p.val, by rw [p.property, factor.property, xi.property, xj.property]⟩)
    l (CPolynomial.Raw.C 1)
  pure ⟨p.val, by simpa only [CPolynomial.CLagrange.basisListRaw] using p.property⟩

/-- Form a Lagrange basis polynomial using the cached node array. -/
def basis (nodes : Array F) {m : ℕ} (i : Fin m) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial F // p =
      CPolynomial.CLagrange.basis Finset.univ
        (fun j : Fin m ↦ nodes[j.val]?.getD 0) i} := do
  let p ← basisListRaw nodes i ((List.finRange m).erase i)
  let q ← canonicalRaw p.val
  pure ⟨q.val, by
    rw [q.property, p.property]
    unfold CPolynomial.CLagrange.basis
    rw [Finset.erase_val, finRange_val, Multiset.coe_erase]
    rfl⟩

/-- Interpolate explicit cached nodes and values in their finite index order. -/
def interpolate (nodes values : Array F) (m : ℕ) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial F // p =
      CPolynomial.CLagrange.interpolate (Finset.univ : Finset (Fin m))
        (fun i ↦ nodes[i.val]?.getD 0) (fun i ↦ values[i.val]?.getD 0)} := do
  let p ← certifiedFoldr (F := F) (A := Fin m) (B := CPolynomial.Raw F)
    (fun (i : Fin m) acc ↦ CPolynomial.Raw.addRaw
      (CPolynomial.Raw.mulRaw (CPolynomial.Raw.C (values[i.val]?.getD 0))
        (CPolynomial.CLagrange.basis Finset.univ
          (fun j : Fin m ↦ nodes[j.val]?.getD 0) i).val) acc)
    (fun i acc ↦ do
      let y ← valueRead values i.val
      let b ← basis nodes i
      let p ← mulRaw (CPolynomial.Raw.C y.val) b.val.val
      let q ← addRaw p.val acc
      pure ⟨q.val, by rw [q.property, p.property, b.property, y.property]⟩)
    (List.finRange m) #[]
  let q ← canonicalRaw p.val
  pure ⟨q.val, by
    rw [q.property, p.property]
    change _ = CPolynomial.CLagrange.interpolateRaw (Finset.univ : Finset (Fin m))
      (fun i ↦ nodes[i.val]?.getD 0) (fun i ↦ values[i.val]?.getD 0)
    unfold CPolynomial.CLagrange.interpolateRaw
    rw [finRange_val]
    rfl⟩
end CompPoly.Arithmetic
