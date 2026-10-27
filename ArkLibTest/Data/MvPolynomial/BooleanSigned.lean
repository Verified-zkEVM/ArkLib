/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.MvPolynomial.BooleanSigned
import ArkLib.ToCompPoly.Multilinear.Basic
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Formal signed-kernel normalization and executable coordinate transport -/

open MvPolynomial
open scoped BigOperators
open Lean Elab Command

namespace BooleanSignedTest
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
theorem two_ne_zero : (2 : F) ≠ 0 := by decide
theorem inverse_two : (2 : F)⁻¹ = 9 := by
  apply inv_eq_of_mul_eq_one_right
  decide
theorem inverse_four : (4 : F)⁻¹ = 13 := by
  apply inv_eq_of_mul_eq_one_right
  decide

def s : Fin 2 → F := ![2, 3]
def t : Fin 2 → F := ![5, 7]
def crossedS : Fin 2 → F := ![3, 2]
def normalizedKernel (s t : Fin 2 → F) : F :=
  ((2 : F) ^ 2)⁻¹ * ∏ i, (1 + s i * t i)
def rawKernel (s t : Fin 2 → F) : F := ∏ i, (1 + s i * t i)
def actualKernel (s t : Fin 2 → F) : F := eqTilde (signedToBoolean s) (signedToBoolean t)

theorem actualKernel_eq (s t : Fin 2 → F) : actualKernel s t = normalizedKernel s t := by
  exact eqTilde_signedToBoolean two_ne_zero s t

def cubeForward : Fin 2 → F :=
  (signedCubeEquiv (σ := Fin 2) two_ne_zero ![(0 : Fin 2), 1]).val
def cubeBack : Fin 2 → Fin 2 :=
  (signedCubeEquiv (σ := Fin 2) two_ne_zero).symm
    ⟨![-1, 1], by intro i; fin_cases i <;> simp⟩

noncomputable def formalKernel : MvPolynomial (Fin 1) F :=
  bind₁ (halfShift (F := F)) (eqPolynomial (signedToBoolean (fun _ ↦ (5 : F))))

/-- This is a formal polynomial identity, not inference from finitely many field evaluations. -/
theorem formalKernel_eq : formalKernel = C 9 * (1 + C 5 * X 0) := by
  rw [formalKernel, bind₁_eqPolynomial_halfShift two_ne_zero]
  simp only [Fintype.card_fin, pow_one, Fin.prod_univ_one, inverse_two]

theorem formal_constant : formalKernel.coeff 0 = 9 := by
  rw [formalKernel_eq]
  simp [coeff_C_mul]

theorem formal_linear : formalKernel.coeff (Finsupp.single (0 : Fin 1) 1) = 11 := by
  have hm : (0 : Fin 1 →₀ Nat) ≠ Finsupp.single (0 : Fin 1) 1 :=
    Ne.symm (Finsupp.single_ne_zero.mpr Nat.one_ne_zero)
  calc
    _ = (9 : F) * 5 := by rw [formalKernel_eq]; simp [coeff_C_mul, coeff_one, hm]
    _ = 11 := by decide

def table : CompPoly.CMlPolynomialEval F 2 := #v[0, 3, 7, 15]
def rho (u : Fin 2 → Fin 2) : F := table.get (finFunctionFinEquiv u)

/-- Every coefficient of the transformed table is fixed by this formal substitution identity. -/
theorem table_substitution :
    bind₁ (halfShift (F := F)) (MLE rho) =
      ∑ u : Fin 2 → Fin 2, C 13 *
        (∏ i : Fin 2, (1 + C (booleanToSigned (u : Fin 2 → F) i) * X i)) * C (rho u) := by
  have h := bind₁_MLE_halfShift two_ne_zero rho
  simpa only [Fintype.card_fin, show (2 : F) ^ 2 = 4 by ring, inverse_four] using h

theorem table_degree (i : Fin 2) : degreeOf i (bind₁ (halfShift (F := F)) (MLE rho)) ≤ 1 :=
  degreeOf_bind₁_MLE_halfShift_le two_ne_zero rho i

theorem table_values (u : Fin 2 → Fin 2) :
    eval (booleanToSigned (u : Fin 2 → F)) (bind₁ (halfShift (F := F)) (MLE rho)) = rho u :=
  eval_bind₁_halfShift_MLE_signed two_ne_zero rho u

/-- The actual existing table backend evaluates the transformed mathematical polynomial. -/
def runtimeTablePoint : F := CompPoly.CMlPolynomialEval.eval₂Mle table (RingHom.id F)
  (Vector.ofFn (signedToBoolean s))
theorem runtimeTablePoint_realizes :
    runtimeTablePoint = eval s (bind₁ (halfShift (F := F)) (MLE rho)) := by
  rw [eval_bind₁_halfShift]
  exact CompPoly.CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE table (RingHom.id F)
    (signedToBoolean s)

-- The empty cube has kernel1 even in characteristic two; no inverse premise is needed here.
example {E : Type*} [Field E] : eqTilde (Fin.elim0 : Fin 0 → E) Fin.elim0 = 1 := by
  simp [eqTilde]
example {E : Type*} [Field E] :
    bind₁ (halfShift (F := E)) (eqPolynomial' (R := E) (σ := Fin 0)) = 1 := by
  simp [eqPolynomial']

-- Neither the scalar field nor the coordinate cube needs a finite ambient field.
example (s t : Fin 2 → ℚ) :
    eqTilde (signedToBoolean s) (signedToBoolean t) =
      (1 / 4 : ℚ) * ∏ i, (1 + s i * t i) := by
  convert eqTilde_signedToBoolean (by norm_num : (2 : ℚ) ≠ 0) s t using 1
  norm_num

namespace CharacteristicTwo
abbrev F := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem labels_collapse :
    booleanToSigned (fun _ : Fin 1 ↦ (0 : F)) = booleanToSigned (fun _ ↦ (1 : F)) := by
  funext i
  simp [booleanToSigned, show (2 : F) = 0 by decide]

theorem inverse_fails :
    signedToBoolean (booleanToSigned (fun _ : Fin 1 ↦ (1 : F))) ≠ (fun _ ↦ 1) := by
  intro h
  have hzero : (0 : F) = 1 := by
    simpa [signedToBoolean, booleanToSigned, show (2 : F) = 0 by decide] using congrFun h 0
  exact zero_ne_one hzero

theorem kernel_one :
    eqTilde (signedToBoolean (fun _ : Fin 1 ↦ (0 : F)))
      (signedToBoolean (fun _ ↦ (0 : F))) = 1 := by
  simp [eqTilde, signedToBoolean, show (2 : F) = 0 by decide]

theorem purported_normalized_kernel_zero :
    ((2 : F) ^ Fintype.card (Fin 1))⁻¹ * ∏ _ : Fin 1, (1 + (0 : F) * 0) = 0 := by
  simp [show (2 : F) = 0 by decide]
end CharacteristicTwo

run_cmd do
  unless actualKernel s t == 1 do throwError "signed kernel normalization/orientation changed"
  unless normalizedKernel s t == 1 do throwError "normalized product does not match actual kernel"
  unless rawKernel s t == 4 do throwError "omitted-normalization counterexample changed"
  unless actualKernel crossedS t == 9 do throwError "crossed-coordinate counterexample changed"
  unless cubeForward 0 == -1 && cubeForward 1 == 1 do
    throwError "Boolean row labels do not map to the expected signed coordinates"
  unless cubeBack 0 == 0 && cubeBack 1 == 1 do
    throwError "executable signed-cube inverse changed the row labels"
  unless runtimeTablePoint == 8 do
    throwError "actual little-endian table backend disagrees with signed coordinate transport"

run_cmd do
  for name in #[``booleanToSigned, ``signedToBoolean, ``signedCubeEquiv, ``actualKernel,
      ``normalizedKernel, ``rawKernel, ``cubeForward, ``cubeBack, ``runtimeTablePoint] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing signed coordinate executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``signedToBoolean_booleanToSigned, ``booleanToSigned_signedToBoolean,
      ``bind₁_eqPolynomial'_halfShift, ``eqTilde_signedToBoolean,
      ``bind₁_eqPolynomial_halfShift,
      ``bind₁_MLE_halfShift, ``eval_bind₁_halfShift, ``eval_bind₁_halfShift_MLE_signed,
      ``MLE_eval_signedToBoolean, ``degreeOf_bind₁_MLE_halfShift_le,
      ``actualKernel_eq, ``formalKernel_eq, ``formal_constant, ``formal_linear,
      ``table_substitution, ``table_degree, ``table_values, ``runtimeTablePoint_realizes,
      ``CharacteristicTwo.labels_collapse, ``CharacteristicTwo.inverse_fails,
      ``CharacteristicTwo.kernel_one, ``CharacteristicTwo.purported_normalized_kernel_zero] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "signed coordinate proof has an unexpected axiom: {name}"

end BooleanSignedTest
