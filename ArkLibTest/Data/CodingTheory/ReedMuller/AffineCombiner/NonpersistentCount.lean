/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.NonpersistentCount
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance cases for the nonpersistent count of the Reed–Muller affine combiner

The grid is `𝔽₂²` (`q₀ = 2`, `k = 2`, `n = 4`), identified with `𝔽₄` by trace coordinates.
The received words take values in `F = 𝔽₂`.
The chart field is the algebraic closure `E` of `𝔽₂`, with `𝔽₄` embedded as a local algebra.
So `e = n / q₀ = 2`.
-/

open FiniteField ReedMuller Polynomial Finset

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

private noncomputable instance : DecidableEq (GaloisField 2 2) := Classical.decEq _

/-- The algebraic closure of `𝔽₂`. -/
private abbrev E := AlgebraicClosure (ZMod 2)

private noncomputable instance : DecidableEq E := Classical.decEq _

/-- An embedding of `𝔽₄` into the algebraic closure of `𝔽₂`. -/
private noncomputable def ι : GaloisField 2 2 →ₐ[ZMod 2] E := IsAlgClosed.lift

private noncomputable instance : Algebra (GaloisField 2 2) E := ι.toRingHom.toAlgebra

private instance : IsScalarTower (ZMod 2) (GaloisField 2 2) E := IsScalarTower.of_algHom ι

private theorem finrank_eq : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 :=
  GaloisField.finrank 2 (by norm_num)

private noncomputable def b : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  Module.finBasisOfFinrankEq _ _ finrank_eq

/-- The interpolant hypothesis for `d = 1` (so `d e = 2`) and multipliers of degree `e = 2`. -/
private abbrev IsInterpolant (f g : (Fin 2 → ZMod 2) → ZMod 2) (A m D M : ℕ)
    (Q : MvPolynomial ReedSolomon.AffineVar E) : Prop :=
  ReedSolomon.IsMultiplierInterpolant (ReedSolomon.algebraMapDomain (GaloisField 2 2) E)
    (fun x ↦ algebraMap (ZMod 2) E (f (traceCoordinateEquiv (ZMod 2) b x)))
    (fun x ↦ algebraMap (ZMod 2) E (g (traceCoordinateEquiv (ZMod 2) b x)))
    (Fintype.card (ZMod 2) ^ (2 - 1)) (1 * Fintype.card (ZMod 2) ^ (2 - 1)) A m D M Q

-- The hypotheses are consistent: at `A = 5 > n`, the constant `1` is an interpolant.
example (f g : (Fin 2 → ZMod 2) → ZMod 2) : ∃ Q, IsInterpolant f g 5 1 0 0 Q := by
  refine ⟨1, one_ne_zero, ?_, ?_, by simp, fun L P _ _ hA ↦ absurd hA ?_⟩
  · rw [← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
    norm_num
  · rw [← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
  · refine not_le.mpr ((card_le_univ _).trans_lt ?_)
    simp [Module.card_fintype b]

-- Every interpolant vanishes along the transported candidate `X₀` for `L_α = X₁`.
-- With `f(z) = z₀` and `g = 1`, the candidate has `2` agreements, the threshold here.
example (Q : MvPolynomial ReedSolomon.AffineVar E) {m D M : ℕ}
    (hQ : IsInterpolant (fun z ↦ z 0) (fun _ ↦ 1) 2 m D M Q) :
    ReedSolomon.multiplierEval
      (ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap (ZMod 2) E ∘ ![0, 0, 1]))
      (traceSubstitution b ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 2)).map
        (algebraMap (ZMod 2) E))) Q = 0 := by
  refine multiplierEval_traceSubstitution_eq_zero b (fun z ↦ z 0) (fun _ ↦ 1) (d := 1) hQ _
    (by simp) ?_
  simp only [agreementSet, MvPolynomial.eval_X, gridPoint_apply, Algebra.algebraMap_self,
    RingHom.id_apply, combinedWord, mul_one, eval_affineMultiplier, Fin.sum_univ_two]
  decide

-- With `d = 1`, `B = 1` and `A = 4`: `v = n / (A - B - e + 1) = 2` and `ρ n = 2`.
-- At most `D² + (2 · 2 · M · 2)³ D⁴ = D² + 512 M³ D⁴` vectors are left out.
example (f g : (Fin 2 → ZMod 2) → ZMod 2) (Q : MvPolynomial ReedSolomon.AffineVar E)
    {m D M : ℕ} (hQ : IsInterpolant f g 4 m D M Q) :
    ∃ Ex : Finset (Fin 3 → ZMod 2), (#Ex : ℝ) ≤ D ^ 2 + 512 * M ^ 3 * D ^ 4 ∧
      ∀ α ∉ Ex, ∀ P : MvPolynomial (Fin 2) (ZMod 2), P.totalDegree ≤ 1 →
        4 ≤ #(agreementSet (combinedWord f g (affineMultiplier α)) P) →
        IsAffinePersistent f g 1 1 α P := by
  obtain ⟨Ex, hEx, hgood⟩ := exists_finset_card_le_isAffinePersistent (B := 1) b f g hQ le_rfl
    (by simp [ZMod.card]) (by simp [ZMod.card])
  refine ⟨Ex, hEx.trans_eq ?_, hgood⟩
  simp only [ZMod.card]
  norm_num
  left
  ring

/-- info: 'ReedMuller.isAffinePersistent_of_mem_chartExcluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.isAffinePersistent_of_mem_chartExcluded

/-- info: 'ReedMuller.exists_finset_card_le_isAffinePersistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_finset_card_le_isAffinePersistent
