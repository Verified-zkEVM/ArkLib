/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Algebra.Grouped
public import ArkLib.ToCompPoly.Univariate.ArithmeticCost

/-!
# Exact arithmetic requests of scalar reconstruction

The measured interpretation selects the same operation-parametric driver as ordinary scalar
reconstruction. Fractions and the equality product start from their first entries. A coordinate
factor requests one multiplication and two additions/subtractions, so the complete kernel uses
`n+(n-1)` multiplications and `2n` additions/subtractions, with neutral one and no requests at n=0.

Let S be the sum of group lengths and A the sum of each truncated length minus one. The complete
circuit requests A+2K+2n+1 additions, S+K+2n subtractions and 3A+2K+n+(n-1)+1 multiplications.
Every other ArithmeticCost coordinate is zero. In particular no inversion or inverse law is used;
the existing ArithmeticSpec carrier still requires Inv and DecidableEq instances.

Inputs are already bound scalar answers. Source openings, supplied getter work, public sampling,
index/control work, primitive implementations and allocations are not priced by these profiles.
No polynomial construction, dense table evaluation, or finite-field evaluation uniqueness runs
in either interpretation.
-/

@[expose] public section

open OracleComp OracleSpec CompPoly
open scoped BigOperators
namespace Logup.Reconstruction
variable {R : Type} [CommRing R] [Inv R] [DecidableEq R] {n T K : Nat}

/-- Request a certified addition and retain its ordinary scalar result. -/
def addRequest (a b : R) : OracleComp (ArithmeticSpec R) R :=
  Subtype.val <$> Arithmetic.add a b
/-- Request a certified subtraction and retain its ordinary scalar result. -/
def subRequest (a b : R) : OracleComp (ArithmeticSpec R) R :=
  Subtype.val <$> Arithmetic.sub a b
/-- Request a certified multiplication and retain its ordinary scalar result. -/
def mulRequest (a b : R) : OracleComp (ArithmeticSpec R) R :=
  Subtype.val <$> Arithmetic.mul a b

/-- The scalar addition charges precisely one addition request. -/
theorem profile_addRequest (a b : R) : profileArithmetic (addRequest a b) =
    (a + b, arithmeticCost (.add a b)) := by
  simp only [addRequest, profileArithmetic_map, profileArithmetic_add]

/-- The scalar subtraction charges precisely one subtraction request. -/
theorem profile_subRequest (a b : R) : profileArithmetic (subRequest a b) =
    (a - b, arithmeticCost (.sub a b)) := by
  simp only [subRequest, profileArithmetic_map, profileArithmetic_sub]

/-- The scalar multiplication charges precisely one multiplication request. -/
theorem profile_mulRequest (a b : R) : profileArithmetic (mulRequest a b) =
    (a * b, arithmeticCost (.mul a b)) := by
  simp only [mulRequest, profileArithmetic_map, profileArithmetic_mul]

/-- The exact request profile of one affine equality factor. -/
def factorCost : ArithmeticCost
  | .add | .sub => 2
  | .mul => 1
  | _ => 0

/-- Interpret the shared affine factor with certified scalar requests. -/
def factorProgram (z x : R) : OracleComp (ArithmeticSpec R) R :=
  factorM addRequest subRequest mulRequest z x

/-- The measured factor has the exact ring value and request profile. -/
theorem profile_factorProgram (z x : R) : profileArithmetic (factorProgram z x) =
    (z * x + (1 - z) * (1 - x), factorCost) := by
  simp only [factorProgram, factorM, profileArithmetic_bind, profile_subRequest,
    profile_addRequest, profile_mulRequest]
  apply Prod.ext
  · ring
  · funext kind
    cases kind <;> simp [factorCost, arithmeticCost, ArithmeticOp.costKind]

/-- The exact profile of one additional weighted fraction. -/
def fractionStepCost : ArithmeticCost
  | .add | .sub => 1
  | .mul => 3
  | _ => 0

/-- Interpret one step of the shared weighted fraction fold. -/
def fractionStepProgram (alpha : R) (value weight : Fin T → R)
    (acc : FractionPair R) (i : Fin T) : OracleComp (ArithmeticSpec R) (FractionPair R) :=
  fractionStepM addRequest subRequest mulRequest alpha value weight acc i

/-- One measured step agrees with unnormalized fraction addition. -/
theorem profile_fractionStepProgram (alpha : R) (value weight : Fin T → R)
    (acc : FractionPair R) (i : Fin T) :
    profileArithmetic (fractionStepProgram alpha value weight acc i) =
      (FractionPair.combine acc ⟨weight i, alpha - value i⟩, fractionStepCost) := by
  simp only [fractionStepProgram, fractionStepM, profileArithmetic_bind, profile_subRequest,
    profile_mulRequest, profile_addRequest, profileArithmetic_pure]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [fractionStepCost, arithmeticCost, ArithmeticOp.costKind]

private def fractionSuffixCost (length : Nat) : ArithmeticCost
  | .add | .sub => length
  | .mul => 3 * length
  | _ => 0

private theorem profile_fractionFold (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → R) (acc : FractionPair R) :
    profileArithmetic (group.foldlM (fractionStepProgram alpha value weight) acc) =
      (FractionPair.combine acc
        (FractionPair.sum (group.map fun i => ⟨weight i, alpha - value i⟩)),
        fractionSuffixCost group.length) := by
  induction group generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, profileArithmetic_pure, List.map_nil, FractionPair.sum_nil,
      FractionPair.combine_unit, List.length_nil]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> rfl
  | cons i group ih =>
    simp only [List.foldlM_cons, profileArithmetic_bind, profile_fractionStepProgram]
    rw [ih]
    apply Prod.ext
    · simp only [List.map_cons, FractionPair.sum_cons, FractionPair.combine_assoc]
    · funext kind
      cases kind <;> simp [fractionStepCost, fractionSuffixCost]
      <;> omega

/-- The exact profile of a first-seeded group of the given length. -/
def fractionCost (length : Nat) : ArithmeticCost
  | .add => length - 1
  | .sub => length
  | .mul => 3 * (length - 1)
  | _ => 0

/-- Interpret the shared seeded fraction group with certified scalar requests. -/
def fractionProgram (group : List (Fin T)) (alpha : R) (value weight : Fin T → R) :
    OracleComp (ArithmeticSpec R) (FractionPair R) :=
  fractionM addRequest subRequest mulRequest alpha value weight group

/-- Each group has the exact fraction sum and seeded request profile. -/
theorem profile_fractionProgram (group : List (Fin T)) (alpha : R) (value weight : Fin T → R) :
    profileArithmetic (fractionProgram group alpha value weight) =
      (FractionPair.sum (group.map fun i => ⟨weight i, alpha - value i⟩),
        fractionCost group.length) := by
  cases group with
  | nil =>
    simp only [fractionProgram, fractionM, profileArithmetic_pure, List.map_nil,
      FractionPair.sum_nil, List.length_nil]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> rfl
  | cons first rest =>
    change profileArithmetic (do
      let d ← subRequest alpha (value first)
      rest.foldlM (fractionStepProgram alpha value weight) ⟨weight first, d⟩) = _
    simp only [profileArithmetic_bind, profile_subRequest, profile_fractionFold]
    apply Prod.ext
    · simp only [List.map_cons, FractionPair.sum_cons]
    · funext kind
      cases kind <;> simp [fractionCost, fractionSuffixCost, arithmeticCost, ArithmeticOp.costKind,
        Nat.add_comm]

private def kernelStepProgram (z x : Fin n → R) (acc : R) (i : Fin n) :
    OracleComp (ArithmeticSpec R) R := do
  let factor ← factorProgram (z i) (x i)
  mulRequest acc factor

private def kernelSuffixCost (length : Nat) : ArithmeticCost
  | .add | .sub | .mul => 2 * length
  | _ => 0

private theorem profile_kernelFold (indices : List (Fin n)) (z x : Fin n → R) (acc : R) :
    profileArithmetic (indices.foldlM (kernelStepProgram z x) acc) =
      (acc * (indices.map fun i => z i * x i + (1 - z i) * (1 - x i)).prod,
        kernelSuffixCost indices.length) := by
  induction indices generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, profileArithmetic_pure, List.map_nil, List.prod_nil,
      mul_one, List.length_nil]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> rfl
  | cons i indices ih =>
    simp only [List.foldlM_cons, kernelStepProgram, profileArithmetic_bind,
      profile_factorProgram, profile_mulRequest]
    rw [ih]
    apply Prod.ext
    · simp only [List.map_cons, List.prod_cons, mul_assoc]
    · funext kind
      cases kind <;> simp [factorCost, kernelSuffixCost, arithmeticCost, ArithmeticOp.costKind]
      <;> omega

/-- The exact equality-product profile, including the zero-coordinate case. -/
def kernelCost (n : Nat) : ArithmeticCost
  | .add | .sub => 2 * n
  | .mul => n + (n - 1)
  | _ => 0

/-- Interpret the shared first-seeded coordinate equality product. -/
def kernelProgram (z x : Fin n → R) : OracleComp (ArithmeticSpec R) R :=
  kernelM addRequest subRequest mulRequest z x

/-- The measured product is the canonical kernel with its exact profile. -/
theorem profile_kernelProgram (z x : Fin n → R) : profileArithmetic (kernelProgram z x) =
    (MvPolynomial.eqTilde z x, kernelCost n) := by
  have hlength := List.length_finRange (n := n)
  unfold kernelProgram kernelM
  cases h : List.finRange n with
  | nil =>
    have hn : n = 0 := by simpa only [h, List.length_nil] using hlength.symm
    simp only [profileArithmetic_pure]
    apply Prod.ext
    · rw [MvPolynomial.eqTilde_eq_prod, Fin.prod_univ_def, h]
      rfl
    · funext kind
      cases kind <;> simp [kernelCost, hn]
  | cons first rest =>
    have hlen : rest.length + 1 = n := by
      simpa only [h, List.length_cons] using hlength
    change profileArithmetic (do
      let factor ← factorProgram (z first) (x first)
      rest.foldlM (kernelStepProgram z x) factor) = _
    simp only [profileArithmetic_bind, profile_factorProgram, profile_kernelFold]
    apply Prod.ext
    · rw [MvPolynomial.eqTilde_eq_prod, Fin.prod_univ_def, h, List.map_cons, List.prod_cons]
    · funext kind
      cases kind <;> simp [factorCost, kernelSuffixCost, kernelCost]
      <;> omega

/-- The exact profile of one helper and batched cleared residual. -/
def contributionCost (length : Nat) : ArithmeticCost
  | .add => length - 1
  | .sub => length + 1
  | .mul => 3 * (length - 1) + 2
  | _ => 0

/-- Interpret the shared helper and residual contribution. -/
def contributionProgram (groups : Vector (List (Fin T)) K) (alpha : R)
    (lambda : Fin K → R) (value weight : Fin T → R) (helper : Fin K → R) (k : Fin K) :
    OracleComp (ArithmeticSpec R) (R × R) :=
  contributionM addRequest subRequest mulRequest groups alpha lambda value weight helper k

/-- A contribution has the exact scalar residual and request profile. -/
theorem profile_contributionProgram (groups : Vector (List (Fin T)) K) (alpha : R)
    (lambda : Fin K → R) (value weight : Fin T → R) (helper : Fin K → R) (k : Fin K) :
    profileArithmetic (contributionProgram groups alpha lambda value weight helper k) =
      (let fraction := FractionPair.sum
        ((groups.get k).map fun i => ⟨weight i, alpha - value i⟩)
       (helper k, lambda k * (helper k * fraction.denominator - fraction.numerator)),
        contributionCost (groups.get k).length) := by
  change profileArithmetic (do
    let fraction ← fractionProgram (groups.get k) alpha value weight
    let product ← mulRequest (helper k) fraction.denominator
    let residual ← subRequest product fraction.numerator
    let term ← mulRequest (lambda k) residual
    pure (helper k, term)) = _
  simp only [profileArithmetic_bind, profile_fractionProgram, profile_mulRequest,
    profile_subRequest, profileArithmetic_pure]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [contributionCost, fractionCost, arithmeticCost, ArithmeticOp.costKind]

private def residualTerm (groups : Vector (List (Fin T)) K) (alpha : R)
    (lambda : Fin K → R) (value weight : Fin T → R) (helper : Fin K → R) (k : Fin K) : R :=
  let fraction := FractionPair.sum ((groups.get k).map fun i => ⟨weight i, alpha - value i⟩)
  lambda k * (helper k * fraction.denominator - fraction.numerator)

private def sumLoopCost (groups : Vector (List (Fin T)) K) (indices : List (Fin K)) :
    ArithmeticCost
  | .add => (indices.map fun k => (groups.get k).length - 1).sum + 2 * indices.length
  | .sub => (indices.map fun k => (groups.get k).length).sum + indices.length
  | .mul => 3 * (indices.map fun k => (groups.get k).length - 1).sum + 2 * indices.length
  | _ => 0

private theorem profile_sumFold (indices : List (Fin K))
    (groups : Vector (List (Fin T)) K) (alpha : R) (lambda : Fin K → R)
    (value weight : Fin T → R) (helper : Fin K → R) (acc : R × R) :
    profileArithmetic (indices.foldlM (fun acc k => do
      let contribution ← contributionProgram groups alpha lambda value weight helper k
      let helperSum ← addRequest acc.1 contribution.1
      let batchSum ← addRequest acc.2 contribution.2
      pure (helperSum, batchSum)) acc) =
      ((acc.1 + (indices.map helper).sum,
        acc.2 + (indices.map (residualTerm groups alpha lambda value weight helper)).sum),
        sumLoopCost groups indices) := by
  induction indices generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, profileArithmetic_pure, List.map_nil, List.sum_nil, add_zero]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> rfl
  | cons k indices ih =>
    simp only [List.foldlM_cons, profileArithmetic_bind, profile_contributionProgram,
      profile_addRequest, profileArithmetic_pure]
    rw [ih]
    apply Prod.ext
    · simp only [List.map_cons, List.sum_cons, residualTerm, add_assoc]
    · funext kind
      cases kind <;> simp [sumLoopCost, contributionCost, arithmeticCost, ArithmeticOp.costKind]
      <;> omega

/-- All nine exact request coordinates of the complete scalar circuit. -/
def cost (groups : Vector (List (Fin T)) K) (n : Nat) : ArithmeticCost
  | .add => (∑ k : Fin K, ((groups.get k).length - 1)) + 2 * K + 2 * n + 1
  | .sub => (∑ k : Fin K, (groups.get k).length) + K + 2 * n
  | .mul => 3 * (∑ k : Fin K, ((groups.get k).length - 1)) + 2 * K + n + (n - 1) + 1
  | _ => 0

/-- Interpret the complete shared scalar driver with certified arithmetic requests. -/
def program (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R) (helper : Fin K → R) :
    OracleComp (ArithmeticSpec R) R :=
  reconstructM addRequest subRequest mulRequest groups alpha z lambda x value weight helper

/-- The shared driver returns its ordinary value and exact request profile. -/
theorem profile_program (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R) (helper : Fin K → R) :
    profileArithmetic (program groups alpha z lambda x value weight helper) =
      (reconstructM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
        (fun a b => pure (a * b)) groups alpha z lambda x value weight helper, cost groups n) := by
  change profileArithmetic (do
    let kernel ← kernelProgram z x
    let sums ← (List.finRange K).foldlM (fun acc k => do
      let contribution ← contributionProgram groups alpha lambda value weight helper k
      let helperSum ← addRequest acc.1 contribution.1
      let batchSum ← addRequest acc.2 contribution.2
      pure (helperSum, batchSum)) (0, 0)
    let batch ← mulRequest kernel sums.2
    addRequest sums.1 batch) = _
  simp only [profileArithmetic_bind, profile_kernelProgram, profile_sumFold,
    profile_mulRequest, profile_addRequest]
  apply Prod.ext
  · rw [reconstructM_id]
    simp only [zero_add, ← Fin.sum_univ_def, residualTerm]
  · funext kind
    cases kind <;> simp [cost, kernelCost, sumLoopCost, arithmeticCost, ArithmeticOp.costKind,
      ← Fin.sum_univ_def]
    <;> omega

/-- Erasing the profile executes the same ordinary scalar driver. -/
theorem simulate_program (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R) (helper : Fin K → R) :
    simulateQ arithmeticAnswer (program groups alpha z lambda x value weight helper) =
      reconstructM (m := Id) (fun a b => pure (a + b)) (fun a b => pure (a - b))
        (fun a b => pure (a * b)) groups alpha z lambda x value weight helper := by
  exact (profileArithmetic_fst _).symm.trans (congrArg Prod.fst
    (profile_program groups alpha z lambda x value weight helper))

/-- The measured interpretation returns the scalar function selected by the source interface. -/
theorem profile_program_reconstruct (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) :
    profileArithmetic (program groups alpha z lambda x value weight helper) =
      (reconstruct groups alpha z lambda x value weight helper, cost groups n) :=
  profile_program groups alpha z lambda x value weight helper

/-- The measured and ordinary selections erase to the same shared scalar driver. -/
theorem simulate_program_reconstruct (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) :
    simulateQ arithmeticAnswer (program groups alpha z lambda x value weight helper) =
      pure (reconstruct groups alpha z lambda x value weight helper) :=
  simulate_program groups alpha z lambda x value weight helper

/-- Scalar reconstruction issues no inversion request over any permitted carrier. -/
theorem program_inv_zero (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R) (helper : Fin K → R) :
    (profileArithmetic (program groups alpha z lambda x value weight helper)).2 .inv = 0 := by
  rw [profile_program]
  rfl

end Logup.Reconstruction
