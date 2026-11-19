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

The grid is `𝔽₅²` (`q₀ = 5`, `k = 2`, `n = 25`), identified with `𝔽₂₅` by trace coordinates.
The received words take values in `F = 𝔽₂₅`, and `L = 𝔽₂₅` as well.
The chart field is the algebraic closure `E` of `𝔽₂₅`.
So `e = n / q₀ = 5`, and candidates of total degree `d = 1` become univariate of degree `5`.
-/

open FiniteField ReedMuller Polynomial Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The field `𝔽₂₅`. -/
private abbrev F25 := GaloisField 5 2

private noncomputable instance : Fintype F25 := Fintype.ofFinite _

private noncomputable instance : DecidableEq F25 := Classical.decEq _

/-- The algebraic closure of `𝔽₂₅`. -/
private abbrev E25 := AlgebraicClosure F25

private noncomputable instance : DecidableEq E25 := Classical.decEq _

private noncomputable def b : Module.Basis (Fin 2) (ZMod 5) F25 :=
  Module.finBasisOfFinrankEq _ _ (GaloisField.finrank 5 (by norm_num))

private theorem card_F25 : Fintype.card F25 = 25 := by
  rw [Module.card_fintype b]
  simp [ZMod.card]

/-- The interpolant hypothesis for `d = 1` (so `d e = 5`) and multipliers of degree `e = 5`. -/
private abbrev IsInterpolant (f g : (Fin 2 → ZMod 5) → F25) (A m D M : ℕ)
    (Q : MvPolynomial ReedSolomon.AffineVar E25) : Prop :=
  ReedSolomon.IsMultiplierInterpolant (ReedSolomon.algebraMapDomain F25 E25)
    (fun x ↦ algebraMap F25 E25 (f (traceCoordinateEquiv (ZMod 5) b x)))
    (fun x ↦ algebraMap F25 E25 (g (traceCoordinateEquiv (ZMod 5) b x)))
    (Fintype.card (ZMod 5) ^ (2 - 1)) (1 * Fintype.card (ZMod 5) ^ (2 - 1)) A m D M Q

open Polynomial.SymbolicInterpolation in
/-- At `A = 25` and `m = D = M = 1`, the monomials outnumber the constraints on `𝔽₂₅`. -/
private theorem exists_interpolant (f g : (Fin 2 → ZMod 5) → F25) :
    ∃ Q, IsInterpolant f g 25 1 1 1 Q :=
  ReedSolomon.exists_isMultiplierInterpolant _ _ _ (by
    simp only [ZMod.card, card_F25]
    norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ])

/-- With `f = 0` and `g = 1`, the candidate `X₀` agrees with `f + L_α g` everywhere.
Here `α = (0, 1, 0)`, so `L_α = X₀`. -/
private theorem card_agreementSet_X :
    #(agreementSet (combinedWord (0 : (Fin 2 → ZMod 5) → F25) 1
      (affineMultiplier ![0, 1, 0])) (MvPolynomial.X 0)) = 25 := by
  rw [show agreementSet _ _ = univ by
    ext z
    simp [Fin.sum_univ_two]]
  simp [ZMod.card]

-- Such an interpolant exists, so the next example is not vacuous.
example : ∃ Q, IsInterpolant 0 1 25 1 1 1 Q :=
  exists_interpolant _ _

-- Every such interpolant vanishes along `L̃_α` and the transported candidate `X̃₀`.
example (Q : MvPolynomial ReedSolomon.AffineVar E25) (hQ : IsInterpolant 0 1 25 1 1 1 Q) :
    ReedSolomon.multiplierEval
      (ReedSolomon.familyMultiplier (traceFamily E25 b) (algebraMap F25 E25 ∘ ![0, 1, 0]))
      (traceSubstitution b ((MvPolynomial.X 0 : MvPolynomial (Fin 2) F25).map
        (algebraMap F25 E25))) Q = 0 :=
  multiplierEval_traceSubstitution_eq_zero b 0 1 (d := 1) hQ _ (by simp)
    card_agreementSet_X.ge

-- With `d = 1`, `B = 1` and `A = 25`: `ρ n = d e = 5` and `v = n / (A - B - e + 1) = 25 / 20`.
-- The bound is `1 + (2 · 5 · 1 · 25 / 20)³ = 1954.125`, out of `25³ = 15625` vectors.
example (f g : (Fin 2 → ZMod 5) → F25) :
    ∃ Ex : Finset (Fin 3 → F25), (#Ex : ℝ) ≤ 1955 ∧
      ∀ α ∉ Ex, ∀ P : MvPolynomial (Fin 2) F25, P.totalDegree ≤ 1 →
        25 ≤ #(agreementSet (combinedWord f g (affineMultiplier α)) P) →
        IsAffinePersistent f g 1 1 α P := by
  obtain ⟨Q, hQ⟩ := exists_interpolant f g
  obtain ⟨Ex, hEx, hgood⟩ := exists_finset_card_le_isAffinePersistent (B := 1) b f g hQ le_rfl
    (by simp [ZMod.card]) (by simp [ZMod.card])
  refine ⟨Ex, hEx.trans ?_, hgood⟩
  simp only [ZMod.card]
  norm_num

/-- info: 'ReedMuller.isAffinePersistent_of_mem_chartExcluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.isAffinePersistent_of_mem_chartExcluded

/-- info: 'ReedMuller.exists_finset_card_le_isAffinePersistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_finset_card_le_isAffinePersistent
