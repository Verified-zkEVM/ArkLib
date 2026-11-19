/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.TraceChart
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance cases for Reed–Muller candidates in the univariate chart count

The grid is `𝔽₂²` (`q₀ = 2`, `k = 2`, `n = 4`), identified with `𝔽₄` by trace coordinates.
The received words take values in `F = 𝔽₂`.
The chart field is the algebraic closure `E` of `𝔽₂`, with `𝔽₄` embedded as a local algebra.
-/

open FiniteField ReedMuller Polynomial Finset

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

private noncomputable instance : DecidableEq (GaloisField 2 2) := Classical.decEq _

/-- The algebraic closure of `𝔽₂`. -/
private abbrev E := AlgebraicClosure (ZMod 2)

/-- An embedding of `𝔽₄` into the algebraic closure of `𝔽₂`. -/
private noncomputable def ι : GaloisField 2 2 →ₐ[ZMod 2] E := IsAlgClosed.lift

private noncomputable instance : Algebra (GaloisField 2 2) E := ι.toRingHom.toAlgebra

private instance : IsScalarTower (ZMod 2) (GaloisField 2 2) E := IsScalarTower.of_algHom ι

private theorem finrank_eq : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 :=
  GaloisField.finrank 2 (by norm_num)

private noncomputable def b : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  Module.finBasisOfFinrankEq _ _ finrank_eq

-- The `2³ = 8` coefficient vectors over `𝔽₂` give `8` distinct multipliers over `E`.
example : Function.Injective fun α : Fin 3 → ZMod 2 ↦
    ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap (ZMod 2) E ∘ α) :=
  familyMultiplier_traceFamily_injective b

-- The multiplier `L̃_α` is the trace substitution of `L_α`.
example (α : Fin 3 → ZMod 2) :
    traceSubstitution b ((affineMultiplier α).map (algebraMap (ZMod 2) E)) =
      ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap (ZMod 2) E ∘ α) :=
  traceSubstitution_map_affineMultiplier_eq_familyMultiplier b α

-- An inverse Frobenius power maps `L̃_α` to the mapped family at the mapped coefficients.
example (r : ℕ) (c : Fin 3 → E) :
    (ReedSolomon.familyMultiplier (traceFamily E b) c).map
        ((iterateFrobeniusEquiv E 2 r).symm : E →+* E) =
      ReedSolomon.familyMultiplier
        (fun j ↦ (traceFamily E b j).map ((iterateFrobeniusEquiv E 2 r).symm : E →+* E))
        (((iterateFrobeniusEquiv E 2 r).symm : E →+* E) ∘ c) :=
  map_familyMultiplier_traceFamily b _ c

-- At `x ∈ 𝔽₄`, `L̃_c(x)` is `c₀ + c₁ ψ₁(x) + c₂ ψ₂(x)` at the grid point `ψ(x)`.
example (c : Fin 3 → E) (x : GaloisField 2 2) :
    (ReedSolomon.familyMultiplier (traceFamily E b) c).eval (algebraMap _ E x) =
      c 0 + c 1 * algebraMap (ZMod 2) E (traceCoordinateEquiv (ZMod 2) b x 0) +
        c 2 * algebraMap (ZMod 2) E (traceCoordinateEquiv (ZMod 2) b x 1) := by
  rw [eval_familyMultiplier_traceFamily]
  simp [Fin.sum_univ_two, add_assoc]

-- The chart target at exponent `s = 2` has degree at most `2`.
example (f g : (Fin 2 → ZMod 2) → ZMod 2) (x : GaloisField 2 2) :
    (traceChartTarget E b f g 2 x).totalDegree ≤ 2 :=
  totalDegree_traceChartTarget_le b f g 2 x

-- At the square roots of `c`, the target at exponent `2` is `f(ψ x) + L̃_c(x) g(ψ x)`.
example (f g : (Fin 2 → ZMod 2) → ZMod 2) (x : GaloisField 2 2) (a : Fin 3 → E) :
    MvPolynomial.aeval a (traceChartTarget E b f g 2 x) =
      algebraMap (ZMod 2) E (f (traceCoordinateEquiv (ZMod 2) b x)) +
        (ReedSolomon.familyMultiplier (traceFamily E b) fun j ↦ a j ^ 2).eval (algebraMap _ E x) *
          algebraMap (ZMod 2) E (g (traceCoordinateEquiv (ZMod 2) b x)) :=
  aeval_traceChartTarget b f g 2 x a

-- Over `𝔽₂`, take `f(z) = z₀`, `g(z) = 1`, `α = (0, 0, 1)` and `P = X₀`.
-- The combined word is `z₀ + z₁`, and `P` agrees with it exactly where `z₁ = 0`.
-- So the transported candidate `P̃` has `2` agreements on `𝔽₄`.
example : {x : GaloisField 2 2 |
      (traceSubstitution b ((MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 2)).map
        (algebraMap (ZMod 2) E))).eval (algebraMap _ E x) =
        algebraMap (ZMod 2) E (traceCoordinateEquiv (ZMod 2) b x 0) +
          (ReedSolomon.familyMultiplier (traceFamily E b)
            (algebraMap (ZMod 2) E ∘ ![0, 0, 1])).eval (algebraMap _ E x) *
            algebraMap (ZMod 2) E 1}.ncard = 2 := by
  rw [ncard_eval_traceSubstitution_eq b (fun z ↦ z 0) (fun _ ↦ 1) ![0, 0, 1]]
  simp only [agreementSet, MvPolynomial.eval_X, gridPoint_apply, Algebra.algebraMap_self,
    RingHom.id_apply, combinedWord, mul_one, eval_affineMultiplier, Fin.sum_univ_two]
  decide

-- Functionals cutting out the substituted polynomials of total degree at most one exist.
example : ∃ cuts : List (E[X] →ₗ[E] E), IsTraceImageCuts b 1 cuts :=
  exists_isTraceImageCuts E b 1

-- Every such list kills the substitution `T_{b₁}` of `X₁`.
example (cuts : List (E[X] →ₗ[E] E)) (h : IsTraceImageCuts b 1 cuts) :
    ∀ Λ ∈ cuts, Λ ((tracePolynomial (ZMod 2) (b 0)).map (algebraMap _ E)) = 0 := by
  simpa using h.apply_traceSubstitution_eq_zero (MvPolynomial.X 0) (by simp)

-- With `d·e = 2`, three evaluations on `𝔽₄` determine the polynomials of degree at most `2`.
-- This holds whatever the high cuts are.
example (cuts : List (E[X] →ₗ[E] E)) :
    ReedSolomon.SeparatesDegree cuts (fun x : GaloisField 2 2 ↦ leval (algebraMap _ E x)) 2 3 :=
  ReedSolomon.separatesDegree_leval (x := algebraMap (GaloisField 2 2) E)
    (algebraMap (GaloisField 2 2) E).injective (by norm_num)

section Proper

/-! Over `𝔽₃ ⊆ 𝔽₉` with `d = 1`, the image misses `X²`, so the cuts are not all zero there. -/

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private noncomputable instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

/-- The algebraic closure of `𝔽₃`. -/
private abbrev E₃ := AlgebraicClosure (ZMod 3)

/-- An embedding of `𝔽₉` into the algebraic closure of `𝔽₃`. -/
private noncomputable def ι₃ : GaloisField 3 2 →ₐ[ZMod 3] E₃ := IsAlgClosed.lift

private noncomputable instance : Algebra (GaloisField 3 2) E₃ := ι₃.toRingHom.toAlgebra

private noncomputable def b₃ : Module.Basis (Fin 2) (ZMod 3) (GaloisField 3 2) :=
  Module.finBasisOfFinrankEq _ _ (GaloisField.finrank 3 (by norm_num))

/-- A trace polynomial over `𝔽₉` has no `X²` term: its exponents are `1` and `3`. -/
private theorem coeff_two_tracePolynomial (c : GaloisField 3 2) :
    (tracePolynomial (ZMod 3) c).coeff 2 = 0 := by
  rw [tracePolynomial, finsetSum_coeff, GaloisField.finrank 3 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_C_mul_X_pow, ZMod.card]
  norm_num

-- Such cuts exist here too, so the next example is not vacuous.
example : ∃ cuts : List (E₃[X] →ₗ[E₃] E₃), IsTraceImageCuts b₃ 1 cuts :=
  exists_isTraceImageCuts E₃ b₃ 1

-- The substitution of a polynomial of total degree at most one has no `X²` term.
-- So `X²`, of degree `2 ≤ d·e = 3`, is outside the image, and some cut is nonzero on it.
example (cuts : List (E₃[X] →ₗ[E₃] E₃)) (h : IsTraceImageCuts b₃ 1 cuts) :
    ∃ Λ ∈ cuts, Λ (X ^ 2) ≠ 0 := by
  by_contra! hall
  obtain ⟨P, hP, hPX⟩ := h.exists_traceSubstitution_eq (X ^ 2) (by norm_num [ZMod.card]) hall
  have h2 : (traceSubstitution b₃ P).coeff 2 = 0 := by
    rw [P.as_sum, map_sum, finsetSum_coeff]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    have hm1 : m.degree ≤ 1 := (MvPolynomial.le_totalDegree hm).trans hP
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm1 with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff m).mp h0]
      simp [traceSubstitution]
    · obtain ⟨i, rfl⟩ : ∃ i, Finsupp.single i 1 = m := by
        rw [← Set.mem_range, Finsupp.range_single_one]
        exact h1
      simp [traceSubstitution, MvPolynomial.aeval_monomial, coeff_C_mul, coeff_map,
        coeff_two_tracePolynomial]
  rw [hPX] at h2
  simp at h2

end Proper

/-- info: 'ReedMuller.familyMultiplier_traceFamily' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.familyMultiplier_traceFamily

/-- info: 'ReedMuller.map_familyMultiplier_traceFamily' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.map_familyMultiplier_traceFamily

/-- info: 'ReedMuller.traceSubstitution_map_affineMultiplier_eq_familyMultiplier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_map_affineMultiplier_eq_familyMultiplier

/-- info: 'ReedMuller.familyMultiplier_traceFamily_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.familyMultiplier_traceFamily_injective

/-- info: 'ReedMuller.eval_familyMultiplier_traceFamily' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.eval_familyMultiplier_traceFamily

/-- info: 'ReedMuller.totalDegree_traceChartTarget_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.totalDegree_traceChartTarget_le

/-- info: 'ReedMuller.aeval_traceChartTarget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.aeval_traceChartTarget

/-- info: 'ReedMuller.ncard_eval_traceSubstitution_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.ncard_eval_traceSubstitution_eq

/-- info: 'ReedMuller.multiplierEval_traceSubstitution_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.multiplierEval_traceSubstitution_eq_zero

/-- info: 'ReedMuller.exists_isTraceImageCuts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_isTraceImageCuts
