/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Fraction
public import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Operation-parametric scalar reconstruction

The scalar circuit consumes already bound values, weights and helper answers. Each nonempty
fraction group starts from its first numerator and linear denominator, avoiding arithmetic with
an unused neutral pair. Coordinate equality factors use the affine expression
`(1-z)+(z+z-1)*x`; their product also starts from its first factor. Empty products retain one.
The circuit streams the helper sum and batched residual sum without division or polynomial data.

The Id interpretation agrees with the canonical coordinate equality kernel and the unnormalized
fraction-pair expression over every commutative ring. In particular this agreement requires no
nonzero denominators, characteristic bound or finite-field evaluation argument. Other arithmetic
interpretations share this same executable control; their request profiles belong to a companion
owner.
-/

@[expose] public section

open scoped BigOperators
namespace Logup.Reconstruction
universe u v
variable {R : Type u} {m : Type u → Type v} [Monad m] [Zero R] [One R]
variable {n T K : Nat}

/-- Add one weighted linear denominator to an accumulated unnormalized fraction. -/
def fractionStepM (add sub mul : R → R → m R) (alpha : R)
    (value weight : Fin T → R) (acc : FractionPair R) (i : Fin T) : m (FractionPair R) := do
  let d ← sub alpha (value i)
  let left ← mul acc.numerator d
  let right ← mul (weight i) acc.denominator
  let numerator ← add left right
  let denominator ← mul acc.denominator d
  pure ⟨numerator, denominator⟩

/-- Fold one group, seeding a nonempty group from its first fraction. -/
def fractionM (add sub mul : R → R → m R) (alpha : R) (value weight : Fin T → R) :
    List (Fin T) → m (FractionPair R)
  | [] => pure ⟨0, 1⟩
  | first :: rest => do
    let d ← sub alpha (value first)
    rest.foldlM (fractionStepM add sub mul alpha value weight) ⟨weight first, d⟩

/-- Evaluate one coordinate equality factor using one multiplication and two additions. -/
def factorM (add sub mul : R → R → m R) (z x : R) : m R := do
  let base ← sub 1 z
  let twice ← add z z
  let slope ← sub twice 1
  let term ← mul slope x
  add base term

/-- Multiply coordinate factors without multiplying the first factor by one. -/
def kernelM (add sub mul : R → R → m R) (z x : Fin n → R) : m R :=
  match List.finRange n with
  | [] => pure 1
  | first :: rest => do
    let firstFactor ← factorM add sub mul (z first) (x first)
    rest.foldlM (fun acc i => do
      let factor ← factorM add sub mul (z i) (x i)
      mul acc factor) firstFactor

/-- Bind one helper once and compute its batched denominator-cleared residual. -/
def contributionM (add sub mul : R → R → m R) (groups : Vector (List (Fin T)) K)
    (alpha : R) (lambda : Fin K → R) (value weight : Fin T → R) (helper : Fin K → R)
    (k : Fin K) : m (R × R) := do
  let h := helper k
  let fraction ← fractionM add sub mul alpha value weight (groups.get k)
  let product ← mul h fraction.denominator
  let residual ← sub product fraction.numerator
  let term ← mul (lambda k) residual
  pure (h, term)

/-- Stream the helper and residual sums and apply the coordinate equality product. -/
def reconstructM (add sub mul : R → R → m R) (groups : Vector (List (Fin T)) K)
    (alpha : R) (z : Fin n → R) (lambda : Fin K → R) (x : Fin n → R)
    (value weight : Fin T → R) (helper : Fin K → R) : m R := do
  let kernel ← kernelM add sub mul z x
  let sums ← (List.finRange K).foldlM (fun (acc : R × R) k => do
    let contribution ← contributionM add sub mul groups alpha lambda value weight helper k
    let helperSum ← add acc.1 contribution.1
    let batchSum ← add acc.2 contribution.2
    pure (helperSum, batchSum)) (0, 0)
  let batch ← mul kernel sums.2
  add sums.1 batch

section Algebra
variable {R : Type u} [CommRing R]

/-- The affine coordinate formula is the canonical equality factor in every ring. -/
theorem factorM_id (z x : R) :
    factorM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) z x = z * x + (1 - z) * (1 - x) := by
  change (1 - z) + (z + z - 1) * x = _
  ring

/-- Ordinary arithmetic performs the existing unnormalized fraction addition. -/
theorem fractionStepM_id (alpha : R) (value weight : Fin T → R)
    (acc : FractionPair R) (i : Fin T) :
    fractionStepM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) alpha value weight acc i =
      FractionPair.combine acc ⟨weight i, alpha - value i⟩ := rfl

private theorem fold_fraction_id (group : List (Fin T)) (alpha : R) (value weight : Fin T → R)
    (acc : FractionPair R) :
    (group.foldlM (fractionStepM (m := Id) (fun a b => pure (a + b))
      (fun a b => pure (a - b)) (fun a b => pure (a * b)) alpha value weight) acc :
        Id (FractionPair R)) =
      FractionPair.combine acc
        (FractionPair.sum (group.map fun i => ⟨weight i, alpha - value i⟩)) := by
  induction group generalizing acc with
  | nil => exact (FractionPair.combine_unit acc).symm
  | cons i group ih =>
    simp only [List.foldlM_cons, fractionStepM_id]
    change group.foldlM (fractionStepM (m := Id) (fun a b => pure (a + b))
      (fun a b => pure (a - b)) (fun a b => pure (a * b)) alpha value weight)
        (FractionPair.combine acc ⟨weight i, alpha - value i⟩) = FractionPair.combine acc
      (FractionPair.combine ⟨weight i, alpha - value i⟩
        (FractionPair.sum (group.map fun i => ⟨weight i, alpha - value i⟩)))
    rw [ih, FractionPair.combine_assoc]

/-- The seeded group fold has exactly the existing fraction-pair sum. -/
theorem fractionM_id (group : List (Fin T)) (alpha : R) (value weight : Fin T → R) :
    fractionM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) alpha value weight group =
      FractionPair.sum (group.map fun i => ⟨weight i, alpha - value i⟩) := by
  cases group with
  | nil => rfl
  | cons first rest =>
    change rest.foldlM (fractionStepM (m := Id) (fun a b => pure (a + b))
      (fun a b => pure (a - b)) (fun a b => pure (a * b)) alpha value weight)
        (⟨weight first, alpha - value first⟩ : FractionPair R) = _
    rw [fold_fraction_id, List.map_cons, FractionPair.sum_cons]

private theorem fold_mul_id (indices : List (Fin n)) (f : Fin n → R) (acc : R) :
    (indices.foldlM (fun acc i => pure (acc * f i)) acc : Id R) =
      acc * (indices.map f).prod := by
  induction indices generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, List.map_nil, List.prod_nil, mul_one]
    rfl
  | cons i indices ih =>
    change (indices.foldlM (fun acc i => pure (acc * f i)) (acc * f i) : Id R) =
      acc * (f i * (indices.map f).prod)
    rw [ih, mul_assoc]

/-- Ordinary arithmetic returns the canonical coordinate equality kernel. -/
theorem kernelM_id (z x : Fin n → R) :
    kernelM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) z x = MvPolynomial.eqTilde z x := by
  rw [MvPolynomial.eqTilde_eq_prod, Fin.prod_univ_def]
  unfold kernelM
  generalize List.finRange n = indices
  cases indices with
  | nil => rfl
  | cons first rest =>
    simp only [factorM_id]
    change (rest.foldlM (fun acc i => pure
      (acc * (z i * x i + (1 - z i) * (1 - x i))))
        (z first * x first + (1 - z first) * (1 - x first)) : Id R) = _
    rw [fold_mul_id, List.map_cons, List.prod_cons]

/-- Ordinary arithmetic returns one helper and its weighted cleared residual. -/
theorem contributionM_id (groups : Vector (List (Fin T)) K) (alpha : R)
    (lambda : Fin K → R) (value weight : Fin T → R) (helper : Fin K → R) (k : Fin K) :
    contributionM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) groups alpha lambda value weight helper k =
      let fraction := FractionPair.sum
        ((groups.get k).map fun i => ⟨weight i, alpha - value i⟩)
      (helper k, lambda k * (helper k * fraction.denominator - fraction.numerator)) := by
  simp only [contributionM, fractionM_id]
  rfl

private theorem fold_sum_pair_id (indices : List (Fin K)) (h t : Fin K → R) (acc : R × R) :
    (indices.foldlM (fun acc k => pure (acc.1 + h k, acc.2 + t k)) acc : Id (R × R)) =
      (acc.1 + (indices.map h).sum, acc.2 + (indices.map t).sum) := by
  induction indices generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, List.map_nil, List.sum_nil, add_zero]
    rfl
  | cons i indices ih =>
    change (indices.foldlM (fun acc k => pure (acc.1 + h k, acc.2 + t k))
      (acc.1 + h i, acc.2 + t i) : Id (R × R)) =
      (acc.1 + (h i + (indices.map h).sum), acc.2 + (t i + (indices.map t).sum))
    rw [ih]
    simp only [add_assoc]

/-- Ordinary arithmetic agrees with the complete scalar fraction expression. -/
theorem reconstructM_id (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R) (x : Fin n → R)
    (value weight : Fin T → R) (helper : Fin K → R) :
    reconstructM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
      (fun a b => pure (a * b)) groups alpha z lambda x value weight helper =
      (∑ k, helper k) + MvPolynomial.eqTilde z x * ∑ k,
        let fraction := FractionPair.sum
          ((groups.get k).map fun i => ⟨weight i, alpha - value i⟩)
        lambda k * (helper k * fraction.denominator - fraction.numerator) := by
  simp only [reconstructM, kernelM_id, contributionM_id]
  let term (k : Fin K) :=
    let fraction := FractionPair.sum
      ((groups.get k).map fun i => ⟨weight i, alpha - value i⟩)
    lambda k * (helper k * fraction.denominator - fraction.numerator)
  change (let sums := ((List.finRange K).foldlM
      (fun acc k => pure (acc.1 + helper k, acc.2 + term k)) (0, 0) : Id (R × R))
    sums.1 + MvPolynomial.eqTilde z x * sums.2) = _
  rw [fold_sum_pair_id]
  simp only [zero_add, ← Fin.sum_univ_def]
  rfl

end Algebra

end Logup.Reconstruction
