/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.StdBasis

/-!
# Generalized Tensor Algebra and Dual View

This file develops the algebraic theory of the tensor product algebra `A := R ⊗[K] C`
for arbitrary field extensions `R/K` and `C/K`, upon the existing `TensorProduct` module.

## Main Definitions

- `Basis.baseChangeRight` : the lift of a basis of `Left` to an `Right`-basis
  of the base change `Left ⊗[K] Right`.

## TODOs
- multilinear bases of tensor algebra over binary tower subfields
- Proximity Gap for Tensor Algebras

## References

* [Lang, S., *Algebra*][Lan02]
* [Diamond, B.E. and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary Towers*][DP24]
* [Diamond, B.E. and Posen, J., *Succinct arguments over towers of binary fields*][DP23]
-/
open TensorProduct

section DualView
-- This section formalizes the dual view for any finite field extensions.

variable {K : Type*} {Left : Type*} {Right : Type*} {ι : Type*}
  [CommSemiring K] [CommSemiring Left] [CommSemiring Right]
  [Algebra K Left] [Algebra K Right]

noncomputable instance : CommSemiring (Left ⊗[K] Right) := Algebra.TensorProduct.instCommSemiring
noncomputable instance : Algebra K (Left ⊗[K] Right) := Algebra.TensorProduct.instAlgebra
noncomputable instance : Algebra Left (Left ⊗[K] Right) := Algebra.TensorProduct.leftAlgebra
noncomputable instance : Algebra Right (Left ⊗[K] Right) := Algebra.TensorProduct.rightAlgebra

-- Let's create a local notation `e` for the equivalence to make the code more readable.
local notation "e" => Algebra.TensorProduct.comm K Right Left

-- The lemma with the completed proof.
lemma comm_map_smul_tmul (s s' : Right) (m : Left) :
    e (s • (s' ⊗ₜ[K] m)) = s • (e (s' ⊗ₜ[K] m)) := by
  -- Unfold the scalar multiplication on both sides using its fundamental definition.
  -- `r • x` is defined as `algebraMap K A r * x`.
  rw [Algebra.smul_def, Algebra.smul_def]
  -- Now that `algebraMap` is exposed, we can specify which algebra instance to use.
  -- On the LHS, the instance is `leftAlgebra`.
  rw [show algebraMap Right (Right ⊗[K] Left) =
    (Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap Right Right) by rfl]
  -- On the RHS, we need to specify the `rightAlgebra` instance for `Left ⊗[K] Right`.
  -- We must first apply `comm` to get the expression into the right form.
  rw [Algebra.TensorProduct.comm_tmul]
  -- Now the term is `(algebraMap Right (Left ⊗[K] Right) s) * (m ⊗ₜ[K] s')`.
  -- We specify the algebraMap for the `rightAlgebra`.
  rw [show algebraMap Right (Left ⊗[K] Right) =
    (Algebra.TensorProduct.includeRight).toRingHom.comp (algebraMap Right Right) by rfl]
  -- Now, simplify all the compositions and applications.
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_eq,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]

lemma comm_map_smul_add (s : Right) (x y : Right ⊗[K] Left)
    (hx : e (s • x) = s • (e x)) (hy : e (s • y) = s • (e y)) :
    e (s • x) + e (s • y) = s • e x + s • e y := by
  -- This follows from the fact that `smul` and `e` are both additive homomorphisms.
  simp only [hx, hy]

/--
A helper definition to package `Algebra.TensorProduct.comm` as an `Right`-linear equivalence.
It takes the existing K-algebra equivalence and adds a proof that it is also Right-linear.
We make the types explicit arguments to avoid type inference issues.
-/
noncomputable def commSEquiv : Right ⊗[K] Left ≃ₗ[Right] Left ⊗[K] Right :=
  { Algebra.TensorProduct.comm K Right Left with
    map_smul' := fun s x => by
      -- The proof that the commutativity map respects the Right-scalar action.
      induction x using TensorProduct.induction_on with
      | zero =>
        simp only [AlgEquiv.toEquiv_eq_coe, smul_zero, Equiv.toFun_as_coe, EquivLike.coe_coe,
          map_zero, RingHom.id_apply];
      | tmul s' m =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.id_apply,
          Algebra.TensorProduct.comm_tmul];
          -- ⊢ e (s • s' ⊗ₜ[K] m) = s • m ⊗ₜ[K] s'
          exact comm_map_smul_tmul (Right:=Right) (Left:=Left) s s' m
      | add x y hx hy =>
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.id_apply,
          smul_add,
          map_add] at *
        exact comm_map_smul_add (Right:=Right) (Left:=Left) s x y hx hy
   }

open Module
/--
The lift of an `K`-basis of `Left` to an `Right`-basis of the base change `Left ⊗[K] Right`.
This is the right-sided counterpart to `Basis.baseChange`.
-/
noncomputable def Basis.baseChangeRight (b : Basis ι K Left) : Basis ι Right (Left ⊗[K] Right) := by
  -- We now call our helper with explicit arguments.
  exact (b.baseChange Right).map (commSEquiv (Right:=Right) (Left:=Left))

lemma Basis.baseChangeRight_repr_tmul (b : Basis ι K Left) (x y i) :
    (Basis.baseChangeRight (b:=b) (Right:=Right)).repr (x ⊗ₜ y) i = b.repr x i • y := by
  rw [Basis.baseChangeRight]
  rw [Basis.map_repr] -- rewrite the Basis mapped via the AlgEquiv (commSEquiv Right Left)
  simp only [commSEquiv, AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm, Algebra.TensorProduct.comm_symm,
    LinearEquiv.trans_apply, LinearEquiv.coe_symm_mk, Algebra.TensorProduct.comm_tmul,
    Basis.baseChange_repr_tmul]

@[simp]
lemma Basis.baseChangeRight_apply (b : Basis ι K Left) (i : ι) :
    (Basis.baseChangeRight (b:=b) (Right:=Right)) i = b i ⊗ₜ[K] 1 := by
  simp only [baseChangeRight, Basis.baseChange, commSEquiv, AlgEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
    Basis.map_apply, Basis.coe_reindex, Function.comp_apply, Equiv.punitProd_symm_apply,
    Basis.tensorProduct_apply, Basis.singleton_apply, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Algebra.TensorProduct.comm_tmul]
end DualView
