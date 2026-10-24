/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.Multilinear
import Lean.Compiler.IR

/-! # Executable equality-kernel acceptance checks -/

namespace MvPolynomial.EqualityKernelTest

/-- An external caller with an explicitly supplied finite coordinate representation. -/
def kernelCaller {σ R : Type*} [Fintype σ] [CommRing R] (x y : σ → R) : R :=
  MvPolynomial.eqTilde x y

/-- Finite point callers use the canonical product evaluator. -/
def finKernelCaller {R : Type*} [CommRing R] (n : ℕ) (x y : Fin n → R) : R :=
  kernelCaller x y

example : finKernelCaller 2 ![(2 : ℤ), 3] ![5, 7] = 462 := by decide
example : finKernelCaller 0 (Fin.elim0 : Fin 0 → ℤ) Fin.elim0 = 1 := by decide
example : finKernelCaller 2 ![(0 : ℤ), 1] ![0, 1] = 1 := by decide
example : finKernelCaller 2 ![(0 : ℤ), 1] ![1, 1] = 0 := by decide

/-- The executed scalar agrees with the established polynomial interpretation. -/
example {σ R : Type*} [Fintype σ] [CommRing R] (x y : σ → R) :
    kernelCaller x y = MvPolynomial.eval y (MvPolynomial.eqPolynomial x) :=
  MvPolynomial.eqTilde_eq_eval x y

#eval finKernelCaller 2 ![(2 : ℤ), 3] ![5, 7]
#eval finKernelCaller 0 (Fin.elim0 : Fin 0 → ℤ) Fin.elim0

-- This point evaluation must not enumerate a Boolean table of size2^n.
#eval finKernelCaller 100000 (fun _ ↦ (0 : ℤ)) (fun _ ↦ 0)

open Lean Elab Command

run_cmd do
  for name in #[``MvPolynomial.eqTilde, ``kernelCaller, ``finKernelCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``MvPolynomial.eqTilde_eq_prod, ``MvPolynomial.eqTilde_eq_eval,
      ``MvPolynomial.eqTilde_symm, ``MvPolynomial.eqTilde_append,
      ``MvPolynomial.map_eqTilde, ``MvPolynomial.eqTilde_cons, ``MvPolynomial.MLE_eval] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end MvPolynomial.EqualityKernelTest
