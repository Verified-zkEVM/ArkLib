/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LineEvaluation
public import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.ToMathlib.MvPolynomial.CurriedDegree
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor

/-!
# The Taylor chart of a root along an affine challenge line

At a center where the derivative in `Z` is nonzero, a root `P` of
`R(X, a + b X, Z)` is determined by its initial value and the challenge `(a, b)`.
For each positive order `l`, its Taylor coefficient is a rational function
`N_l / S ^ (2l - 1)` of the chart point `(y₀, a, b)`.
The numerator has joint degree at most `1 + (2l - 1)(h - 1)`, where `h` bounds the
`(Y, Z)`-degree and `S` is the nonzero separant at the center.

The chart maps and reconstructions are noncomputable mathematical views of polynomial
rings and rational Taylor coefficients.

## Main definitions

* `ReedSolomon.affineChartEquation` and `ReedSolomon.affineChartSeparant`: the hypersurface
  polynomial and its derivative in the initial value.
* `ReedSolomon.affineChartNumerator` and `ReedSolomon.affineChartCoefficient`: Taylor coefficients.
* `ReedSolomon.affineChartPolynomial`: the polynomial reconstruction.
* `ReedSolomon.affineChartCut`: a cleared agreement equation.

## Main statements

* `ReedSolomon.pderiv_affineChartEquation`: the `y₀`-derivative of the chart equation is the
  chart separant.
* `ReedSolomon.affineChartCut_eq_zero_iff`: a cleared cut says the reconstruction takes a value.
* `ReedSolomon.degree_affineChartPolynomial_le` and
  `ReedSolomon.eval_affineChartPolynomial_center`: the reconstruction has degree at most `d` and
  starts at `y₀`.
* `ReedSolomon.affineChartPolynomial_point`: recover `P` when `expand (p^e) P` is a
  regular root along the line.
* `ReedSolomon.aeval_affineChartEquation_point` and `ReedSolomon.aeval_affineChartSeparant_point`:
  the chart equation and separant at the point of a root.
* `ReedSolomon.totalDegree_affineChartEquation_le`,
  `ReedSolomon.totalDegree_affineChartNumerator_le` and
  `ReedSolomon.totalDegree_affineChartCut_le`: the joint degree bounds.

The coefficient formulas and the polynomial-root reconstruction specialize Lemma 3.11.
The existence and uniqueness of its formal power series are not stated by these declarations.
The reconstruction map, cleared cuts, and their degree budget implement the map and hyperplanes
used in Claim 4.9.
`ReedSolomon.totalDegree_affineChartNumerator_le_of_pos` also covers `h = 0`.
Truncated subtraction in `ℕ` prevents deriving that case from the coarser bound.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Lemma 3.11 and Claim 4.9.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial PolynomialDifferential

variable {E : Type*} [Field E]

/-- The chart variables: `inl 0` is the initial value `y₀`, `inr 0` is `a` and `inr 1` is `b`. -/
abbrev AffineChartVar : Type := Fin 1 ⊕ Fin 2

/-- The equation `R(X, a + b X, Y₀)` as an order-zero differential equation over `E[a, b]`. -/
noncomputable def affineLineEquation (R : MvPolynomial AffineVar E) :
    DifferentialPolynomial (MvPolynomial (Fin 2) E) 0 :=
  aeval (fun v ↦ v.elim (X (some 0)) ![X none, C (X 0) + C (X 1) * X none]) R

/-- Polynomials in `y₀` over `E[a, b]` read as polynomials in the three chart variables. -/
noncomputable def affineChartFlatten :
    MvPolynomial (Fin 1) (MvPolynomial (Fin 2) E) ≃ₐ[E] MvPolynomial AffineChartVar E :=
  (sumAlgEquiv E (Fin 1) (Fin 2)).symm

/-- The chart substitution `Z ↦ y₀`, `X ↦ c`, `Y ↦ a + c b`. -/
noncomputable def affineChartSubstitution (c : E) : AffineVar → MvPolynomial AffineChartVar E :=
  fun v ↦ v.elim (X (.inl 0)) ![C c, X (.inr 0) + C c * X (.inr 1)]

/-- The polynomial defining the chart hypersurface `R(c, a + c b, y₀) = 0`. -/
noncomputable def affineChartEquation (c : E) (R : MvPolynomial AffineVar E) :
    MvPolynomial AffineChartVar E :=
  affineChartFlatten (initialJetEquation (C c) (affineLineEquation R))

/-- The chart separant `R_Z(c, a + c b, y₀)`. -/
noncomputable def affineChartSeparant (c : E) (R : MvPolynomial AffineVar E) :
    MvPolynomial AffineChartVar E :=
  affineChartFlatten (initialJetSeparant (C c) (affineLineEquation R))

/-- The Taylor numerator at order `l` and center `c`, padded to separant exponent `τ`.

It represents the coefficient over `S ^ τ` when `2l - 1 ≤ τ` and the separant `S` is nonzero. -/
noncomputable def affineChartNumerator (c : E) (R : MvPolynomial AffineVar E) (τ l : ℕ) :
    MvPolynomial AffineChartVar E :=
  affineChartFlatten (commonTaylorNumeratorOver E (C c) (affineLineEquation R) τ l)

/-- The polynomial obtained by clearing `S ^ τ` in the reconstruction discrepancy at `x`.

When `S ≠ 0` and `2 s d - 1 ≤ τ`, it vanishes exactly when the reconstruction takes the
value `u + (a ^ s + x b ^ s) v` at `x`. -/
noncomputable def affineChartCut (c : E) (R : MvPolynomial AffineVar E) (s d τ : ℕ) (x u v : E) :
    MvPolynomial AffineChartVar E :=
  (∑ j ∈ Finset.range (d + 1), C ((x - c ^ s) ^ j) * affineChartNumerator c R τ (s * j)) -
    (C u + (X (.inr 0) ^ s + C x * X (.inr 1) ^ s) * C v) * affineChartSeparant c R ^ τ

/-- The line equation with the challenge specialized to `(ab 0, ab 1)`. -/
noncomputable def affineSpecializedLine (R : MvPolynomial AffineVar E) (ab : Fin 2 → E) :
    DifferentialPolynomial E 0 :=
  map (aeval ab).toRingHom (affineLineEquation R)

/-- The rational Taylor coefficient `c_l` at center `c` of the chart point `pt`. -/
noncomputable def affineChartCoefficient (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) (l : ℕ) : E :=
  rationalTaylorCoefficient c (affineSpecializedLine R (pt ∘ Sum.inr)) (pt ∘ Sum.inl) l

/-- The reconstruction `∑_{j ≤ d} c_{s j}(pt) (X - c ^ s) ^ j`. -/
noncomputable def affineChartPolynomial (c : E) (R : MvPolynomial AffineVar E) (s d : ℕ)
    (pt : AffineChartVar → E) : Polynomial E :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (affineChartCoefficient c R pt (s * j)) *
    (Polynomial.X - Polynomial.C (c ^ s)) ^ j

/-- The chart point `(P(c ^ s), a, b)` of a root `expand s P` on the line `(a, b)`. -/
noncomputable def affineChartPoint (c : E) (s : ℕ) (a b : E) (P : Polynomial E) :
    AffineChartVar → E :=
  Sum.elim (fun _ ↦ (Polynomial.expand E s P).eval c) ![a, b]

/-! ### Flattening and evaluation -/

/-- A coefficient flattens to the same polynomial in the challenge variables. -/
theorem affineChartFlatten_C (a : MvPolynomial (Fin 2) E) :
    affineChartFlatten (C a) = rename Sum.inr a := by
  induction a using MvPolynomial.induction_on with
  | C e => simp [affineChartFlatten]
  | add p q hp hq => rw [C_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [C_mul, map_mul, hp, map_mul, rename_X]; simp [affineChartFlatten]

/-- The initial-value variable flattens to `y₀`. -/
@[simp] theorem affineChartFlatten_X (i : Fin 1) :
    affineChartFlatten (X i : MvPolynomial (Fin 1) (MvPolynomial (Fin 2) E)) = X (.inl i) := by
  simp [affineChartFlatten]

/-- Evaluating a flattened polynomial specializes the challenge first, then the initial value. -/
theorem aeval_affineChartFlatten (pt : AffineChartVar → E)
    (P : MvPolynomial (Fin 1) (MvPolynomial (Fin 2) E)) :
    aeval pt (affineChartFlatten P) =
      aeval (pt ∘ Sum.inl) (map (aeval (pt ∘ Sum.inr)).toRingHom P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [affineChartFlatten_C, aeval_rename]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, affineChartFlatten_X, map_X, aeval_X,
      Function.comp_apply]

/-- The partial derivative in `Y₀` of the line equation is the line equation of `R_Z`. -/
theorem pderiv_affineLineEquation (R : MvPolynomial AffineVar E) :
    pderiv (some 0) (affineLineEquation R) = affineLineEquation (pderiv none R) := by
  unfold affineLineEquation
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, aeval_X]
    rcases v with _ | ⟨i⟩
    · simp [pderiv_X]
    · fin_cases i <;> simp [pderiv_X]

/-- The chart equation is `R(c, a + c b, y₀)`. -/
theorem affineChartEquation_eq (c : E) (R : MvPolynomial AffineVar E) :
    affineChartEquation c R = aeval (affineChartSubstitution c) R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [affineChartEquation, affineLineEquation, initialJetEquation, affineChartFlatten]
  | add p q hp hq =>
    simp only [affineChartEquation, affineLineEquation, initialJetEquation, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [affineChartEquation, affineLineEquation, initialJetEquation, map_mul] at hp ⊢
    rw [hp]
    congr 1
    rcases v with _ | ⟨i⟩
    · simp [affineChartFlatten, affineChartSubstitution]
    · fin_cases i <;> simp [affineChartFlatten, affineChartSubstitution, mul_comm]

/-- The chart separant is `R_Z(c, a + c b, y₀)`. -/
theorem affineChartSeparant_eq (c : E) (R : MvPolynomial AffineVar E) :
    affineChartSeparant c R = aeval (affineChartSubstitution c) (pderiv none R) := by
  rw [← affineChartEquation_eq, affineChartSeparant, affineChartEquation, initialJetSeparant,
    separant, Fin.last_zero, pderiv_affineLineEquation]
  rfl

/-- The derivative of the chart equation in `y₀` is the chart separant. -/
theorem pderiv_affineChartEquation (c : E) (R : MvPolynomial AffineVar E) :
    pderiv (.inl 0) (affineChartEquation c R) = affineChartSeparant c R := by
  rw [affineChartSeparant_eq, affineChartEquation_eq]
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, aeval_X]
    rcases v with _ | ⟨i⟩
    · simp [affineChartSubstitution, pderiv_X]
    · fin_cases i <;> simp [affineChartSubstitution, pderiv_X]

/-- The chart equation at `pt` is `R(c, a + b c, y₀)`. -/
theorem aeval_affineChartEquation (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) :
    aeval pt (affineChartEquation c R) =
      aeval (fun v ↦ v.elim (pt (.inl 0)) ![c, pt (.inr 0) + pt (.inr 1) * c]) R := by
  rw [affineChartEquation_eq, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp [affineChartSubstitution]
  · fin_cases i <;> simp [affineChartSubstitution, mul_comm]

/-- The chart separant at `pt` is `R_Z(c, a + b c, y₀)`. -/
theorem aeval_affineChartSeparant (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) :
    aeval pt (affineChartSeparant c R) =
      aeval (fun v ↦ v.elim (pt (.inl 0)) ![c, pt (.inr 0) + pt (.inr 1) * c])
        (pderiv none R) := by
  rw [affineChartSeparant_eq, ← affineChartEquation_eq, aeval_affineChartEquation]

/-- Evaluating a line evaluation at `c` evaluates `R` at `(c, α + β c, P(c))`. -/
theorem eval_affineLineEval (c α β : E) (P : Polynomial E) (R : MvPolynomial AffineVar E) :
    (affineLineEval α β P R).eval c =
      aeval (fun v ↦ v.elim (P.eval c) ![c, α + β * c]) R := by
  rw [← Polynomial.coe_aeval_eq_eval, affineLineEval, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp [affineMultiplier]

/-- At the point of a root, the chart equation is the line evaluation at `c`. -/
theorem aeval_affineChartEquation_point (c : E) (R : MvPolynomial AffineVar E) (s : ℕ)
    (a b : E) (P : Polynomial E) :
    aeval (affineChartPoint c s a b P) (affineChartEquation c R) =
      (affineLineEval a b (Polynomial.expand E s P) R).eval c := by
  rw [aeval_affineChartEquation, eval_affineLineEval]
  rfl

/-- At the point of a root, the chart separant is the line evaluation of `R_Z` at `c`. -/
theorem aeval_affineChartSeparant_point (c : E) (R : MvPolynomial AffineVar E) (s : ℕ)
    (a b : E) (P : Polynomial E) :
    aeval (affineChartPoint c s a b P) (affineChartSeparant c R) =
      (affineLineEval a b (Polynomial.expand E s P) (pderiv none R)).eval c := by
  rw [aeval_affineChartSeparant, eval_affineLineEval]
  rfl

/-- The specialized line equation along `P` is `R(X, a + b X, P)`. -/
theorem differentialSpecialization_affineSpecializedLine (R : MvPolynomial AffineVar E)
    (ab : Fin 2 → E) (P : Polynomial E) :
    differentialSpecialization (affineSpecializedLine R ab) P =
      affineLineEval (ab 0) (ab 1) P R := by
  unfold affineSpecializedLine affineLineEquation differentialSpecialization
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with _ | ⟨i⟩
    · simp [differentialSpecializationHom]
    · fin_cases i <;> simp [differentialSpecializationHom, affineMultiplier]

/-- Specializing the challenge commutes with the chart separant. -/
theorem aeval_affineChartSeparant_eq (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) :
    aeval pt (affineChartSeparant c R) =
      aeval (pt ∘ Sum.inl) (initialJetSeparant c (affineSpecializedLine R (pt ∘ Sum.inr))) := by
  rw [affineChartSeparant, aeval_affineChartFlatten, map_initialJetSeparant]
  simp [affineSpecializedLine]

/-- On `S ≠ 0`, the numerator at `pt` is `S ^ τ` times the coefficient `c_l`. -/
theorem aeval_affineChartNumerator (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) {τ l : ℕ} (hl : 2 * l - 1 ≤ τ)
    (hS : aeval pt (affineChartSeparant c R) ≠ 0) :
    aeval pt (affineChartNumerator c R τ l) =
      aeval pt (affineChartSeparant c R) ^ τ * affineChartCoefficient c R pt l := by
  rw [aeval_affineChartSeparant_eq] at hS ⊢
  rw [affineChartNumerator, aeval_affineChartFlatten, map_commonTaylorNumeratorOver_eq]
  simp only [AlgHom.toRingHom_eq_coe, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact aeval_commonTaylorNumerator c _ _ (by simpa using hl) hS

/-! ### The reconstruction and the cuts -/

/-- The coefficient `c_0` is the initial value `y₀`. -/
@[simp] theorem affineChartCoefficient_zero (c : E) (R : MvPolynomial AffineVar E)
    (pt : AffineChartVar → E) : affineChartCoefficient c R pt 0 = pt (.inl 0) :=
  rationalTaylorCoefficient_initial c _ (pt ∘ Sum.inl) 0

/-- The reconstruction has degree at most `d`. -/
theorem degree_affineChartPolynomial_le (c : E) (R : MvPolynomial AffineVar E) (s d : ℕ)
    (pt : AffineChartVar → E) : (affineChartPolynomial c R s d pt).degree ≤ d := by
  refine Polynomial.degree_le_of_natDegree_le
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- The reconstruction takes the value `y₀` at `c ^ s`. -/
theorem eval_affineChartPolynomial_center (c : E) (R : MvPolynomial AffineVar E) (s d : ℕ)
    (pt : AffineChartVar → E) : (affineChartPolynomial c R s d pt).eval (c ^ s) = pt (.inl 0) := by
  rw [affineChartPolynomial, Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The reconstruction at `x` is `∑_{j ≤ d} c_{s j} (x - c ^ s) ^ j`. -/
theorem eval_affineChartPolynomial (c : E) (R : MvPolynomial AffineVar E) (s d : ℕ)
    (pt : AffineChartVar → E) (x : E) :
    (affineChartPolynomial c R s d pt).eval x =
      ∑ j ∈ Finset.range (d + 1), affineChartCoefficient c R pt (s * j) * (x - c ^ s) ^ j := by
  simp [affineChartPolynomial, Polynomial.eval_finsetSum]

/-- On `S ≠ 0`, the cut at `pt` is `S ^ τ` times the discrepancy of the reconstruction. -/
theorem aeval_affineChartCut (c : E) (R : MvPolynomial AffineVar E) {s d τ : ℕ}
    (hτ : 2 * s * d - 1 ≤ τ) (x u v : E) (pt : AffineChartVar → E)
    (hS : aeval pt (affineChartSeparant c R) ≠ 0) :
    aeval pt (affineChartCut c R s d τ x u v) = aeval pt (affineChartSeparant c R) ^ τ *
      ((affineChartPolynomial c R s d pt).eval x -
        (u + (pt (.inr 0) ^ s + x * pt (.inr 1) ^ s) * v)) := by
  rw [affineChartCut, map_sub, map_sum, eval_affineChartPolynomial, mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : 2 * (s * j) - 1 ≤ τ := by
      have := Finset.mem_range.mp hj
      have : s * j ≤ s * d := Nat.mul_le_mul_left _ (by omega)
      have : 2 * s * d = 2 * (s * d) := Nat.mul_assoc _ _ _
      omega
    rw [map_mul, aeval_affineChartNumerator c R pt hj' hS]
    simp only [aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  · simp only [map_mul, map_add, map_pow, aeval_C, aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply]
    ring

/-- On `S ≠ 0`, the cut vanishes iff the reconstruction is `u + (a ^ s + x b ^ s) v` at `x`. -/
theorem affineChartCut_eq_zero_iff (c : E) (R : MvPolynomial AffineVar E) {s d τ : ℕ}
    (hτ : 2 * s * d - 1 ≤ τ) (x u v : E) (pt : AffineChartVar → E)
    (hS : aeval pt (affineChartSeparant c R) ≠ 0) :
    aeval pt (affineChartCut c R s d τ x u v) = 0 ↔
      (affineChartPolynomial c R s d pt).eval x =
        u + (pt (.inr 0) ^ s + x * pt (.inr 1) ^ s) * v := by
  rw [aeval_affineChartCut c R hτ x u v pt hS, mul_eq_zero, or_iff_right (pow_ne_zero _ hS),
    sub_eq_zero]

/-- Let `s = p ^ e` and let `expand s P` be a root of `R(X, a + b X, Z)` with `R_Z ≠ 0` at `c`.

If `deg P ≤ d`, the reconstruction at the point of the root is `P`. -/
theorem affineChartPolynomial_point (c : E) (R : MvPolynomial AffineVar E) {p e s d : ℕ}
    [ExpChar E p] (hs : s = p ^ e) {a b : E} {P : Polynomial E} (hP : P.degree ≤ d)
    (hroot : affineLineEval a b (Polynomial.expand E s P) R = 0)
    (hsep : (affineLineEval a b (Polynomial.expand E s P) (pderiv none R)).eval c ≠ 0) :
    affineChartPolynomial c R s d (affineChartPoint c s a b P) = P := by
  set pt := affineChartPoint c s a b P
  have hab : pt ∘ Sum.inr = ![a, b] := rfl
  have hsol : differentialSpecialization (affineSpecializedLine R ![a, b])
      (Polynomial.expand E s P) = 0 := by
    rw [differentialSpecialization_affineSpecializedLine]
    simpa using hroot
  have hsepJ : jetEvaluation (separant (affineSpecializedLine R ![a, b]) (Fin.last 0)) c
      (polynomialJet c (Polynomial.expand E s P)) ≠ 0 := by
    rw [← eval_differentialSpecialization, separant, Fin.last_zero, affineSpecializedLine,
      pderiv_map, pderiv_affineLineEquation, ← affineSpecializedLine,
      differentialSpecialization_affineSpecializedLine]
    simpa using hsep
  have hjet : pt ∘ Sum.inl = polynomialJet c (Polynomial.expand E s P) := by
    funext i
    rw [Fin.fin_one_eq_zero i, polynomialJet, Polynomial.hasseJet_eq_taylor_coeff,
      Fin.val_zero, Polynomial.taylor_coeff_zero]
    rfl
  have hcoef : ∀ j,
      affineChartCoefficient c R pt (s * j) = (Polynomial.taylor (c ^ s) P).coeff j := by
    intro j
    rw [affineChartCoefficient, hab, hjet,
      rationalTaylorCoefficient_eq_solution c _ _ hsol hsepJ _ (fun i _ _ ↦ by simp), hs,
      Polynomial.coeff_taylor_expand_expChar_pow_mul, Polynomial.taylor_coeff]
  have hdeg : (Polynomial.taylor (c ^ s) P).natDegree < d + 1 := by
    rw [Polynomial.natDegree_taylor]
    exact Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hP)
  conv_rhs => rw [← Polynomial.sum_taylor_eq P (c ^ s)]
  rw [Polynomial.sum_over_range' _ (fun _ ↦ by simp) _ hdeg, affineChartPolynomial]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoef]

/-! ### Joint degree bounds -/

/-- The chart substitution does not raise the `(Y, Z)`-degree. -/
theorem totalDegree_aeval_affineChartSubstitution_le (c : E) (P : MvPolynomial AffineVar E) :
    (aeval (affineChartSubstitution c) P).totalDegree ≤ P.weightedTotalDegree affineYZWeight := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le
  intro v
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  rcases v with _ | ⟨i⟩
  · exact X_mem_restrictWeightedDegree _ _ _ le_rfl
  · fin_cases i
    · exact C_mem_restrictWeightedDegree _ _ _
    · apply Submodule.add_mem _ (X_mem_restrictWeightedDegree _ _ _ le_rfl)
      simpa using mul_mem_restrictWeightedDegree (C_mem_restrictWeightedDegree _ 0 c)
        (X_mem_restrictWeightedDegree (1 : AffineChartVar → ℕ) 1 (.inr 1) le_rfl)

/-- The chart equation has degree at most the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_affineChartEquation_le (c : E) {R : MvPolynomial AffineVar E} {h : ℕ}
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (affineChartEquation c R).totalDegree ≤ h := by
  rw [affineChartEquation_eq]
  exact (totalDegree_aeval_affineChartSubstitution_le c R).trans hR

/-- If `R` has `(Y, Z)`-degree at most `h`, the chart separant has degree at most `h - 1`. -/
theorem totalDegree_affineChartSeparant_le (c : E) {R : MvPolynomial AffineVar E} {h : ℕ}
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (affineChartSeparant c R).totalDegree ≤ h - 1 := by
  rw [affineChartSeparant_eq]
  refine (totalDegree_aeval_affineChartSubstitution_le c _).trans ?_
  refine (weightedTotalDegree_pderiv_le_sub affineYZWeight none R).trans ?_
  simp only [affineYZWeight_none]
  omega

/-- With `(Y, Z)`-degree `0`, the chart separant vanishes. -/
theorem affineChartSeparant_eq_zero (c : E) {R : MvPolynomial AffineVar E}
    (hR : R.weightedTotalDegree affineYZWeight ≤ 0) : affineChartSeparant c R = 0 := by
  rw [affineChartSeparant_eq,
    pderiv_eq_zero_of_weightedTotalDegree_lt affineYZWeight none R (by simp; omega), map_zero]

/-- A polynomial with constant coefficients over `E[a, b]` flattens to its renaming. -/
private theorem sumAlgEquiv_symm_map_algebraMap {S : Type*} (P : MvPolynomial S E) :
    (sumAlgEquiv E S (Fin 2)).symm (map (algebraMap E (MvPolynomial (Fin 2) E)) P) =
      rename Sum.inl P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, map_X, rename_X, sumAlgEquiv_symm_X]

/-- Each residual monomial, with its coefficient degree added, has degree at most `h`. -/
private theorem totalDegree_residual_coeff_add_degree_le (c : E)
    {R : MvPolynomial AffineVar E} {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (l t : ℕ) (m : Fin l →₀ ℕ) (hm : m ∈ ((optionEquivLeft (MvPolynomial (Fin 2) E) (Fin l)
      (universalTaylorResidual l (C c) (affineLineEquation R))).coeff t).support) :
    (((optionEquivLeft (MvPolynomial (Fin 2) E) (Fin l)
      (universalTaylorResidual l (C c) (affineLineEquation R))).coeff t).coeff m).totalDegree +
        m.degree ≤ h := by
  set w : Option (Fin l) → ℕ := fun i ↦ i.elim 0 fun _ ↦ 1
  set Res := universalTaylorResidual l (C c) (affineLineEquation R)
  rw [mem_support_iff, optionEquivLeft_coeff_coeff] at hm
  rw [optionEquivLeft_coeff_coeff, ← MvPolynomial.weight_optionElim_zero_one m t]
  refine (totalDegree_coeff_add_weight_le_weightedTotalDegree_sumAlgEquiv_symm
    w Res (mem_support_iff.mpr hm)).trans ?_
  set flat := (sumAlgEquiv E (Option (Fin l)) (Fin 2)).symm
  have hflat : flat Res = aeval (fun v ↦ flat (aeval
      (fun i : Option (Fin (0 + 1)) ↦ i.elim (C (C c) + X none)
        fun j ↦ universalTaylorJet (F := MvPolynomial (Fin 2) E) l j.val)
      ((fun v : AffineVar ↦
        v.elim (X (some 0) : DifferentialPolynomial (MvPolynomial (Fin 2) E) 0)
          ![X none, C (X 0) + C (X 1) * X none]) v))) R := by
    have := DFunLike.congr_fun (comp_aeval (R := E) (f := fun v : AffineVar ↦
      v.elim (X (some 0) : DifferentialPolynomial (MvPolynomial (Fin 2) E) 0)
        ![X none, C (X 0) + C (X 1) * X none])
      (flat.toAlgHom.comp ((aeval (fun i : Option (Fin (0 + 1)) ↦
        i.elim (C (C c) + X none) fun j ↦ universalTaylorJet (F := MvPolynomial (Fin 2) E)
          l j.val)).restrictScalars E))) R
    simpa [Res, universalTaylorResidual, affineLineEquation] using this
  rw [hflat]
  refine (weightedTotalDegree_aeval_le_of_le affineYZWeight _ _ R fun v ↦ ?_).trans hR
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  rcases v with _ | ⟨i⟩
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    simp only [Option.elim_none, aeval_X, Option.elim_some, Fin.val_zero]
    rw [← map_universalTaylorJet (algebraMap E (MvPolynomial (Fin 2) E)),
      sumAlgEquiv_symm_map_algebraMap,
      weightedTotalDegree_rename_of_injective Sum.inl_injective]
    exact weightedTotalDegree_universalTaylorJet_le l 0
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, affineYZWeight_X, Nat.reduceAdd, Fin.val_eq_zero,
        aeval_eq_bind₁, Option.elim_some, Matrix.cons_val_zero, bind₁_X_right, Option.elim_none,
        map_add, flat, sumAlgEquiv_symm_C_C, sumAlgEquiv_symm_X]
      apply Submodule.add_mem
      · exact C_mem_restrictWeightedDegree (Sum.elim w 1) 0 c
      · exact X_mem_restrictWeightedDegree (Sum.elim w 1) 0 (.inl none) le_rfl
    · simp only [Fin.mk_one, Fin.isValue, affineYZWeight_Y, Nat.reduceAdd, Fin.val_eq_zero,
        aeval_eq_bind₁, Option.elim_some, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add,
        algHom_C, algebraMap_eq, map_mul, bind₁_X_right, Option.elim_none, flat,
        sumAlgEquiv_symm_C_C, sumAlgEquiv_symm_X, sumAlgEquiv_symm_C_X]
      apply Submodule.add_mem
      · exact X_mem_restrictWeightedDegree (Sum.elim w (1 : Fin 2 → ℕ)) 1 (.inr 0) le_rfl
      · have h1 := X_mem_restrictWeightedDegree (R := E)
          (Sum.elim w (1 : Fin 2 → ℕ)) 1 (.inr 1) le_rfl
        have h0 : (C c + X (R := E) (Sum.inl none : Option (Fin l) ⊕ Fin 2) :
            MvPolynomial (Option (Fin l) ⊕ Fin 2) E) ∈
            restrictWeightedDegree (Sum.elim w 1) 0 :=
          Submodule.add_mem _ (C_mem_restrictWeightedDegree _ 0 c)
            (X_mem_restrictWeightedDegree _ 0 _ le_rfl)
        exact mul_mem_restrictWeightedDegree (d := 1) (e := 0) h1 h0

/-- The flattening map satisfies the hypotheses of the joint numerator bound. -/
private theorem affineChartFlatten_numerator_hypotheses (c : E) {R : MvPolynomial AffineVar E}
    {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (∀ i, (affineChartFlatten.toAlgHom (X i : MvPolynomial (Fin 1) (MvPolynomial (Fin 2) E))
      ).totalDegree ≤ 1) ∧
    (affineChartFlatten.toAlgHom (initialJetSeparant (C c) (affineLineEquation R))).totalDegree ≤
      h - 1 ∧
    ∀ l, 0 < l → ∀ m ∈ ((optionEquivLeft (MvPolynomial (Fin 2) E) (Fin l)
      (universalTaylorResidual l (C c) (affineLineEquation R))).coeff (l - 0)).support,
      (affineChartFlatten.toAlgHom (C (((optionEquivLeft (MvPolynomial (Fin 2) E) (Fin l)
        (universalTaylorResidual l (C c) (affineLineEquation R))).coeff (l - 0)).coeff m))
          ).totalDegree + m.degree ≤ h := by
  refine ⟨fun i ↦ ?_, totalDegree_affineChartSeparant_le c hR, fun l _ m hm ↦ ?_⟩
  · simp [totalDegree_X]
  · have hle := totalDegree_residual_coeff_add_degree_le c hR l (l - 0) m hm
    change (affineChartFlatten (C _)).totalDegree + _ ≤ _
    rw [affineChartFlatten_C]
    exact (Nat.add_le_add_right (totalDegree_rename_le _ _) _).trans hle

/-- If `2l - 1 ≤ τ`, the numerator of `c_l` has degree at most `1 + τ (h - 1)`.

Here `h` bounds the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_affineChartNumerator_le (c : E) {R : MvPolynomial AffineVar E}
    {h τ l : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) (hl : 2 * l - 1 ≤ τ) :
    (affineChartNumerator c R τ l).totalDegree ≤ 1 + τ * (h - 1) := by
  obtain ⟨hX, hS, hres⟩ := affineChartFlatten_numerator_hypotheses c hR
  exact totalDegree_algHom_commonTaylorNumeratorOver_le affineChartFlatten.toAlgHom (C c)
    (affineLineEquation R) (h - 1) h (by omega) hX hS hres (by simpa using hl)

/-- For `l > 0` and `2l - 1 ≤ τ`, the numerator has degree at most `(τ - 1)(h - 1) + h`,
where `h` bounds the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_affineChartNumerator_le_of_pos (c : E) {R : MvPolynomial AffineVar E}
    {h τ l : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) (hl0 : 0 < l)
    (hl : 2 * l - 1 ≤ τ) :
    (affineChartNumerator c R τ l).totalDegree ≤ (τ - 1) * (h - 1) + h := by
  obtain ⟨hX, hS, hres⟩ := affineChartFlatten_numerator_hypotheses c hR
  exact totalDegree_algHom_commonTaylorNumeratorOver_le_of_lt affineChartFlatten.toAlgHom
    (C c) (affineLineEquation R) (h - 1) h (by omega) hX hS hres hl0 (by simpa using hl)

/-- For positive `s` and `d`, the cut with `τ = 2 s d - 1` has degree at most `2 s d h`,
where `h` bounds the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_affineChartCut_le (c : E) {R : MvPolynomial AffineVar E} {s d h : ℕ}
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (hd : 1 ≤ d) (hs : 1 ≤ s) (x u v : E) :
    (affineChartCut c R s d (2 * s * d - 1) x u v).totalDegree ≤ 2 * s * d * h := by
  have hsd : 1 ≤ s * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 2 * s * d = 2 * (s * d) := Nat.mul_assoc _ _ _
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hS := affineChartSeparant_eq_zero c hR
    rw [affineChartCut, hS, zero_pow (by omega), mul_zero, sub_zero]
    refine totalDegree_finsetSum_le fun j hj ↦ (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, Nat.mul_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.mul_zero, affineChartNumerator, commonTaylorNumeratorOver, map_mul, map_pow]
      change (affineChartFlatten _ * affineChartSeparant c R ^ _).totalDegree ≤ 0
      rw [hS, zero_pow (by omega), mul_zero, totalDegree_zero]
    · have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have := totalDegree_affineChartNumerator_le_of_pos c hR (τ := 2 * s * d - 1)
        (l := s * j) (Nat.mul_pos (by omega) hj0) (by have := Nat.mul_le_mul_left s hjd; omega)
      simpa using this
  · have hτ : (2 * s * d - 1) * (h - 1) + 2 * s * d ≤ 2 * s * d * h := by
      have : (2 * s * d - 1) * (h - 1) ≤ 2 * s * d * (h - 1) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have : 2 * s * d * (h - 1) + 2 * s * d = 2 * s * d * h := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine totalDegree_finsetSum_le fun j hj ↦ (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have := totalDegree_affineChartNumerator_le c hR (τ := 2 * s * d - 1) (l := s * j)
        (by have := Nat.mul_le_mul_left s hjd; omega)
      omega
    · refine (totalDegree_mul _ _).trans ?_
      have hpow := (totalDegree_pow (affineChartSeparant c R) (2 * s * d - 1)).trans
        (Nat.mul_le_mul_left _ (totalDegree_affineChartSeparant_le c hR))
      have hlin : (C u +
          (X (R := E) (Sum.inr (0 : Fin 2) : AffineChartVar) ^ s +
            C x * X (R := E) (Sum.inr (1 : Fin 2) : AffineChartVar) ^ s) * C v :
          MvPolynomial AffineChartVar E).totalDegree ≤ s := by
        refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, Nat.add_zero]
        refine (totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
        · refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, zero_add]
          exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
      have : s ≤ 2 * s * d := by nlinarith
      omega

end ReedSolomon
