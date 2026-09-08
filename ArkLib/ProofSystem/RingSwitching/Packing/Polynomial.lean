/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.RingSwitching.Packing.Coordinates
import ArkLib.ProofSystem.RingSwitching.Transport.Coeffs

/-!
# Packing multilinear polynomials and public equality weights

Packing combines a family of base-ring multilinears using a finite basis. Unpacking reads
the basis coordinates of each coefficient. Both round trips hold over commutative rings,
without interpolation over a field. The public multiplier is specified by its Boolean table;
an efficient branching-program evaluator can subsequently refine this specification.
-/

noncomputable section

namespace RingSwitching.Packing.PackingData

open Module MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B)

/-- Pack a family of base-ring multilinears into one polynomial over the packing algebra. -/
def packedMLE {m : ℕ} (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) : data.P⦃≤ 1⦄[X Fin m] :=
  ∑ i, data.packBasis i • embedCoeffs (algebraMap B data.P) (ps i)

/-- Coefficient-level description of polynomial packing. -/
theorem packedMLE_val {m : ℕ} (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    (data.packedMLE ps).val =
      ∑ i, data.packBasis i • MvPolynomial.map (algebraMap B data.P) (ps i).val := by
  rw [packedMLE, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul]
  rfl

/-- Packing at an arbitrary packing-algebra point uses algebra evaluation of each component. -/
theorem packedMLE_eval {m : ℕ} (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) (x : Fin m → data.P) :
    (data.packedMLE ps).val.eval x =
      ∑ i, data.packBasis i * MvPolynomial.aeval x (ps i).val := by
  rw [packedMLE_val, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eval, MvPolynomial.eval_map, MvPolynomial.aeval_def]

/-- At a base-ring point, packing reassembles the transported component evaluations. -/
theorem packedMLE_eval_embedded {m : ℕ} (ps : data.ιP → B⦃≤ 1⦄[X Fin m])
    (x : Fin m → B) :
    (data.packedMLE ps).val.eval (fun j => algebraMap B data.P (x j)) =
      ∑ i, algebraMap B data.P ((ps i).val.eval x) * data.packBasis i := by
  rw [packedMLE_val, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eval]
  change data.packBasis i * (embedCoeffs (algebraMap B data.P) (ps i)).val.eval
    (fun j => algebraMap B data.P (x j)) = _
  rw [embedCoeffs_eval, mul_comm]

/-- Unpack each polynomial coefficient into its base-ring basis coordinates. -/
def unpack {m : ℕ} (p : data.P⦃≤ 1⦄[X Fin m]) : data.ιP → B⦃≤ 1⦄[X Fin m] :=
  fun i =>
    ⟨∑ d ∈ p.val.support, MvPolynomial.monomial d (data.packBasis.repr (p.val.coeff d) i), by
      classical
      rw [MvPolynomial.mem_restrictDegree]
      intro s hs j
      have hsub : (∑ d ∈ p.val.support,
            MvPolynomial.monomial d (data.packBasis.repr (p.val.coeff d) i)).support
          ⊆ p.val.support :=
        MvPolynomial.support_sum.trans (Finset.biUnion_subset.mpr fun d hd =>
          MvPolynomial.support_monomial_subset.trans (Finset.singleton_subset_iff.mpr hd))
      exact (MvPolynomial.mem_restrictDegree _ _ _).mp p.property s (hsub hs) j⟩

/-- The coefficients of an unpacked component are the corresponding basis coordinates. -/
theorem unpack_coeff {m : ℕ} (p : data.P⦃≤ 1⦄[X Fin m]) (i : data.ιP) (d : Fin m →₀ ℕ) :
    (data.unpack p i).val.coeff d = data.packBasis.repr (p.val.coeff d) i := by
  classical
  simp only [unpack, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' p.val.support d]
  split_ifs with hd
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

/-- Packing recovers every unpacked polynomial. -/
@[simp]
theorem packedMLE_unpack {m : ℕ} (p : data.P⦃≤ 1⦄[X Fin m]) :
    data.packedMLE (data.unpack p) = p := by
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [packedMLE_val, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, unpack_coeff, smul_eq_mul]
  calc
    ∑ i, data.packBasis i * algebraMap B data.P (data.packBasis.repr (p.val.coeff d) i)
        = ∑ i, data.packBasis.repr (p.val.coeff d) i • data.packBasis i :=
      Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    _ = p.val.coeff d := data.packBasis.sum_repr _

/-- Unpacking recovers every original component family. -/
@[simp]
theorem unpack_packedMLE {m : ℕ} (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    data.unpack (data.packedMLE ps) = ps := by
  funext i
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [unpack_coeff]
  have hcoeff : (data.packedMLE ps).val.coeff d =
      ∑ j, (ps j).val.coeff d • data.packBasis j := by
    rw [packedMLE_val, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
  rw [hcoeff]
  exact congrFun (data.packBasis.repr_sum_self fun j => (ps j).val.coeff d) i

/-- Packing is a bijection with coefficient-wise unpacking as inverse. -/
def polynomialEquiv (m : ℕ) : (data.ιP → B⦃≤ 1⦄[X Fin m]) ≃ data.P⦃≤ 1⦄[X Fin m] where
  toFun := data.packedMLE
  invFun := data.unpack
  left_inv := data.unpack_packedMLE
  right_inv := data.packedMLE_unpack

/-- Boolean values of an unpacked component are coordinates of the packed Boolean values. -/
theorem unpack_eval_zeroOne {m : ℕ} (p : data.P⦃≤ 1⦄[X Fin m]) (i : data.ιP)
    (y : Fin m → Fin 2) :
    (data.unpack p i).val.eval (y : Fin m → B) =
      data.packBasis.repr (p.val.eval (y : Fin m → data.P)) i := by
  have hpt : (y : Fin m → data.P) = fun j => algebraMap B data.P ((y : Fin m → B) j) :=
    funext fun j => (map_natCast (algebraMap B data.P) _).symm
  conv_rhs => rw [← data.packedMLE_unpack p, hpt, packedMLE_eval_embedded]
  simp_rw [← Algebra.smul_def]
  exact (congrFun (data.packBasis.repr_sum_self
    fun j => (data.unpack p j).val.eval (y : Fin m → B)) i).symm

/-- Opening-basis coordinates of a public Boolean equality weight. -/
def eqCoord {m : ℕ} (r : Fin m → data.E) (y : Fin m → Fin 2) (u : data.ιE) : B :=
  data.openBasis.repr (eqTilde r (y : Fin m → data.E)) u

/-- The public multilinear multiplier, specified by its Boolean values in a B-algebra C. -/
def multiplier {C : Type*} [CommRing C] [Algebra B C] {m : ℕ}
    (r : Fin m → data.E) (weight : data.ιE → C) : C⦃≤ 1⦄[X Fin m] :=
  ⟨MLE (fun y : Fin m → Fin 2 => data.bridge weight (eqTilde r (y : Fin m → data.E))),
    MLE_mem_restrictDegree _⟩

/-- The multiplier agrees with the weighted equality coordinates on the Boolean cube. -/
theorem multiplier_eval_zeroOne {C : Type*} [CommRing C] [Algebra B C] {m : ℕ}
    (r : Fin m → data.E) (weight : data.ιE → C) (y : Fin m → Fin 2) :
    (data.multiplier r weight).val.eval (y : Fin m → C) =
      ∑ u, data.eqCoord r y u • weight u := by
  rw [multiplier, MLE_eval_zeroOne, data.bridge_apply]
  rfl

end RingSwitching.Packing.PackingData

end
