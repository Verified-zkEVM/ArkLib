/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for the incidence of regular high-cut jets

* The high-cut list for `k = 1` and `K = 3` is `[N₁, N₂]`; for `K ≤ k` it is empty and the
  high-cut prime family is the initial prime family.
* For `y' = 2x`, written as `Y₁ - 2X`, at center `0`, the initial prime family is nonempty and
  each member has dimension `1`.
* The hypothesis `r < K` of `card_le_of_highTaylorCuts_of_agreement` is needed: for `y'' = 0`
  with `K = 1`, the agreement equation only sees `c₀`, so the two regular jets `(0, 0, 0)` and
  `(0, 1, 0)` both agree with the value `0` at `0`, while the bound is `1`.
* The hypothesis `A - k + 1 ≤ #ι` is needed: for `y' = 2x` with `K = 2`, `k = 0`, no agreement
  points and `A = 0`, the zero jet is a regular high-cut jet, while the bound is `0`.

The file also derives the statement for the default exponent `τ = 2K`, with agreement points
given by an embedding `Fin n ↪ F`, `0 < k`, `A ≤ n`, the high cuts indexed by
`{l : Fin K // k ≤ l}`, and agreement counted by a filter.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped Finset

/-! ### The high-cut list and family -/

/-- For `k = 1` and `K = 3`, the high cuts are the common numerators of `c₁` and `c₂`. -/
example {F : Type*} [Field F] {r : ℕ} (center : F) (Q : DifferentialPolynomial F r) (τ : ℕ) :
    highTaylorCutList center Q 3 1 τ =
      [commonTaylorNumerator center Q τ 1, commonTaylorNumerator center Q τ 2] :=
  rfl

/-- For `K ≤ k` there are no high cuts, and the high-cut prime family is the initial prime
family. -/
example {F : Type*} [Field F] {r : ℕ} (center : F) (Q : DifferentialPolynomial F r)
    {K k : ℕ} (τ : ℕ) (hKk : K ≤ k) :
    highTaylorPrimeFamily center Q K k τ = initialJetPrimeFamily center Q := by
  rw [highTaylorPrimeFamily, highTaylorCutList, Nat.sub_eq_zero_of_le hKk, List.range'_zero,
    List.map_nil, Ideal.iteratedRetainedCutFamily_nil]

/-- The equation `y' = 2x`, as the differential polynomial `Y₁ - 2X`. -/
private abbrev linearEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - 2 * X none

/-- The initial separant of `Y₁ - 2X` evaluates to `1` at every jet. -/
private theorem aeval_initialJetSeparant_linearEquation (F : Type*) [Field F]
    (jet : Fin 2 → F) :
    aeval jet (initialJetSeparant 0 (linearEquation F)) = 1 := by
  simp [aeval_initialJetSeparant, separant, jetEvaluation, linearEquation, pderiv_X, Fin.last]

/-- The initial equation of `Y₁ - 2X` at center `0` evaluates to the coordinate `Y₁`. -/
private theorem aeval_initialJetEquation_linearEquation (F : Type*) [Field F]
    (jet : Fin 2 → F) :
    aeval jet (initialJetEquation 0 (linearEquation F)) = jet 1 := by
  simp [aeval_initialJetEquation, jetEvaluation, linearEquation]

/-- For `y' = 2x` over `ℚ` at center `0`, the initial prime family is nonempty and each member
has dimension `1`. -/
example : (initialJetPrimeFamily 0 (linearEquation ℚ)).Nonempty ∧
    ∀ P ∈ initialJetPrimeFamily 0 (linearEquation ℚ),
      (affineHilbertPolynomial P).natDegree = 1 := by
  refine ⟨?_, fun P hP ↦ natDegree_affineHilbertPolynomial_of_mem_initialJetPrimeFamily hP⟩
  obtain ⟨P, hP, -⟩ := exists_mem_initialJetPrimeFamily_of_regular (E := ℚ) 0
    (linearEquation ℚ) 0 (by rw [aeval_initialJetEquation_linearEquation]; rfl)
    (by rw [aeval_initialJetSeparant_linearEquation]; exact one_ne_zero)
  exact ⟨P, hP⟩

/-! ### Boundary cases of the incidence bound -/

/-- The equation `y'' = 0`, as the differential polynomial `Y₂`. -/
private abbrev secondDerivative (F : Type*) [CommRing F] : DifferentialPolynomial F 2 :=
  X (some 2)

/-- The hypothesis `r < K` of `card_le_of_highTaylorCuts_of_agreement` is needed. For `y'' = 0`
at center `0` with `K = k = 1` and exponent `0`, the jets `(0, 0, 0)` and `(0, 1, 0)` are regular
zeros of the initial equation `Y₂`, there are no high cuts, and both satisfy the agreement
equation `c₀ = 0` at the single point `0`. The bound with `A = 1` would be
`jetTotalDegree Y₂ * (1 * 1 / 1) ^ 2 = 1`. -/
example : ∃ S : Finset (Fin 3 → AlgebraicClosure ℚ),
    (∀ jet ∈ S, aeval jet (initialJetEquation 0 (secondDerivative (AlgebraicClosure ℚ))) = 0 ∧
      aeval jet (initialJetSeparant 0 (secondDerivative (AlgebraicClosure ℚ))) ≠ 0 ∧
      ∀ l, 1 ≤ l → l < 1 →
        aeval jet (commonTaylorNumerator 0 (secondDerivative (AlgebraicClosure ℚ)) 0 l) = 0) ∧
    (∀ jet ∈ S, 1 ≤
      {i : Fin 1 | aeval jet (taylorAgreementEquation 0 (secondDerivative (AlgebraicClosure ℚ)) 1 0
        ((fun _ ↦ 0) i) ((fun _ ↦ 0) i)) = 0}.ncard) ∧
    ¬ (#S : ℚ) ≤ jetTotalDegree (secondDerivative (AlgebraicClosure ℚ)) *
      (((Fintype.card (Fin 1) * rationalTaylorCutDegreeBound
        (secondDerivative (AlgebraicClosure ℚ)) 0 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ)) ^ 2 := by
  classical
  set F := AlgebraicClosure ℚ
  have hS : ∀ jet : Fin 3 → F, aeval jet (initialJetSeparant 0 (secondDerivative F)) = 1 := by
    intro jet
    simp [aeval_initialJetSeparant, separant, jetEvaluation, secondDerivative, pderiv_X,
      Fin.last]
  have hdeg : jetTotalDegree (secondDerivative F) = 1 := by
    simp [jetTotalDegree, secondDerivative, weightedTotalDegree, support_X, Finsupp.weight_single,
      jetDegreeWeight_some]
  refine ⟨{![0, 0, 0], ![0, 1, 0]}, fun jet hjet ↦ ?_, fun jet hjet ↦ ?_, ?_⟩
  · refine ⟨?_, by rw [hS]; exact one_ne_zero, fun l h1 h2 ↦ absurd h2 (by omega)⟩
    rw [aeval_initialJetEquation]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjet
    rcases hjet with rfl | rfl <;> simp [jetEvaluation, secondDerivative]
  · have hzero : aeval jet (taylorAgreementEquation 0 (secondDerivative F) 1 0 0 0) = 0 := by
      rw [taylorAgreementEquation_eq_zero_iff 0 _ (fun l ↦ by have := l.isLt; omega) _
        (by rw [hS]; exact one_ne_zero), eval_rationalTaylorPolynomial, Fin.sum_univ_one]
      have h0 : rationalTaylorCoefficient (0 : F) (secondDerivative F) jet 0 = jet 0 :=
        rationalTaylorCoefficient_initial (0 : F) (secondDerivative F) jet 0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjet
      rcases hjet with rfl | rfl <;> simp [h0]
    change 1 ≤ {i : Fin 1 |
      aeval jet (taylorAgreementEquation 0 (secondDerivative F) 1 0 0 0) = 0}.ncard
    rw [hzero]
    simp
  · have hne : (![0, 0, 0] : Fin 3 → F) ≠ ![0, 1, 0] := fun h ↦ by simpa using congrFun h 1
    rw [hdeg, rationalTaylorCutDegreeBound, Finset.card_pair hne]
    norm_num

/-- The hypothesis `A - k + 1 ≤ #ι` of `card_le_of_highTaylorCuts_of_agreement` is needed. For
`y' = 2x` at center `0` with `K = 2`, `k = 0`, exponent `4`, no agreement points and `A = 0`, the
zero jet is a regular zero of the initial equation and of the high cuts, while the bound is
`jetTotalDegree Q * (0 * B / 1) ^ 1 = 0`. -/
example : ∃ S : Finset (Fin 2 → AlgebraicClosure ℚ),
    (∀ jet ∈ S, aeval jet (initialJetEquation 0 (linearEquation (AlgebraicClosure ℚ))) = 0 ∧
      aeval jet (initialJetSeparant 0 (linearEquation (AlgebraicClosure ℚ))) ≠ 0 ∧
      ∀ l, 0 ≤ l → l < 2 →
        aeval jet (commonTaylorNumerator 0 (linearEquation (AlgebraicClosure ℚ)) 4 l) = 0) ∧
    ¬ (#S : ℚ) ≤ jetTotalDegree (linearEquation (AlgebraicClosure ℚ)) *
      (((Fintype.card Empty * rationalTaylorCutDegreeBound
        (linearEquation (AlgebraicClosure ℚ)) 4 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) ^ 1 := by
  set F := AlgebraicClosure ℚ
  refine ⟨{0}, fun jet hjet ↦ ?_, by simp⟩
  rw [Finset.mem_singleton] at hjet
  subst hjet
  refine ⟨by rw [aeval_initialJetEquation_linearEquation]; rfl,
    by rw [aeval_initialJetSeparant_linearEquation]; exact one_ne_zero, fun l _ hl ↦ ?_⟩
  rw [aeval_commonTaylorNumerator 0 _ 0 (taylorExponentSufficient_two_mul 1 2 ⟨l, hl⟩)
    (by rw [aeval_initialJetSeparant_linearEquation]; exact one_ne_zero)]
  exact mul_eq_zero_of_right _
    (rationalTaylorCoefficient_initial (0 : F) (linearEquation F) 0 ⟨l, hl⟩)

/-! ### The default-exponent form -/

section DefaultExponent

variable {F : Type*} [Field F] {r : ℕ}

/-- With the default exponent `τ = 2K`, agreement points given by an embedding `Fin n ↪ F`,
`0 < k ≤ A ≤ n`, the high cuts indexed by `{l : Fin K // k ≤ l}` and agreement counted by a
filter, a finite set of regular high-cut jets has at most
`jetTotalDegree Q * (n * B / (A - k + 1)) ^ r` elements. -/
example [IsAlgClosed F] [DecidableEq F] (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (hK : r < K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (hk : 0 < k) (hkA : k ≤ A)
    (hAn : A ≤ n) (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q (2 * K) l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤ #(Finset.univ.filter fun i ↦
      aeval jet (taylorAgreementEquation center Q K (2 * K) (domain i) (received i)) = 0)) :
    (#S : ℚ) ≤ jetTotalDegree Q *
      (((n * rationalTaylorCutDegreeBound Q (2 * K) : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ r := by
  have h := card_le_of_highTaylorCuts_of_agreement center Q
    (taylorExponentSufficient_two_mul r K) hK domain received domain.injective hkA
    (by rw [Fintype.card_fin]; omega) S
    (fun jet hjet ↦ ⟨(hS jet hjet).1, (hS jet hjet).2.1,
      fun l hkl hlK ↦ (hS jet hjet).2.2 ⟨⟨l, hlK⟩, hkl⟩⟩)
    (fun jet hjet ↦ by
      have h := hA jet hjet
      rw [← Set.ncard_coe_finset, Finset.coe_filter] at h
      simpa using h)
  rwa [Fintype.card_fin] at h

end DefaultExponent

end

end PolynomialDifferential
