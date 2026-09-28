/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Quang Dao, Natasha Klaus, Pietro Monticone, Devon Tuma, Ilia Vlasov
-/

module

public import Mathlib.LinearAlgebra.Lagrange
public import ArkLib.Data.Polynomial.SplitFold
public import ArkLib.Data.CodingTheory.ProximityGap.Folding
public import CompPoly.Univariate.Lagrange
public import CompPoly.Univariate.ToPoly.Impl

/-!
# FRI Round Consistency

Defines the round consistency check for FRI and proves its completeness. The check verifies that
the Lagrange interpolant through evaluation points at scaled roots of unity equals the polynomial
fold at the challenge point.

For soundness, `roundConsistencyCheck_eq_foldValue` identifies the executable check with
ArkLib's word-folding operation on an arbitrary oracle word, without an honesty assumption.
-/

@[expose] public section

open Polynomial

namespace RoundConsistency

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/--
The generalized round consistency check: checks that the Lagrange-interpolating polynomial through
`pts` evaluates to `β` at the challenge `γ`. Used in FRI to verify that the next-round value equals
the fold evaluated at the challenge.

Implemented via `CompPoly.CPolynomial`'s computable Lagrange interpolation, so the check itself is
computable.
-/
def roundConsistencyCheck
    {n : ℕ} (γ : 𝔽) (pts : Fin n → 𝔽 × 𝔽) (β : 𝔽) : Bool :=
  let p := CompPoly.CPolynomial.CLagrange.interpolate
    (Finset.univ : Finset (Fin n)) (fun i => (pts i).1) (fun i => (pts i).2)
  p.eval γ == β

/-- Mapping a list of query answers before interpolation is just reindexing its points. -/
theorem roundConsistencyCheck_map_get {A : Type} (γ β : 𝔽) (xs : List A)
    (f : A → 𝔽 × 𝔽) :
    roundConsistencyCheck γ (xs.map f).get β =
      roundConsistencyCheck γ (fun j ↦ f (xs.get j)) β := by
  refine congr_heq
    (f := fun pts : Fin (xs.map f).length → 𝔽 × 𝔽 ↦ roundConsistencyCheck γ pts β)
    (g := fun pts : Fin xs.length → 𝔽 × 𝔽 ↦ roundConsistencyCheck γ pts β)
    (congr_arg_heq (fun m ↦ fun pts : Fin m → 𝔽 × 𝔽 ↦
      roundConsistencyCheck γ pts β) (List.length_map f)) ?_
  apply Function.hfunext (congrArg Fin (List.length_map f))
  intro a b hab
  have hab' : a.val = b.val := (Fin.heq_ext_iff (List.length_map f)).mp hab
  apply heq_of_eq
  simp only [List.get_eq_getElem, List.getElem_map, hab']

/-- The executable check evaluates the mathematical Lagrange interpolant. -/
theorem roundConsistencyCheck_eq_true_iff
    {m : ℕ} (γ : 𝔽) (pts : Fin m → 𝔽 × 𝔽) (β : 𝔽) :
    roundConsistencyCheck γ pts β = true ↔
      (Lagrange.interpolate Finset.univ (fun i ↦ (pts i).1)
        (fun i ↦ (pts i).2)).eval γ = β := by
  simp [roundConsistencyCheck, CompPoly.CPolynomial.eval_toPoly,
    CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate]

/-- A local query check is exactly ArkLib's word-folding check when the queried points
enumerate a folding block. This applies to arbitrary words, including dishonest oracles. -/
theorem roundConsistencyCheck_eq_foldValue {n k : ℕ}
    (domain : Domain.SmoothCosetFftDomain n 𝔽) (f : Fin (2 ^ n) → 𝔽)
    (points : Fin (2 ^ k) ↪ Fin (2 ^ n)) (x γ β : 𝔽)
    (hpoints : ∀ j, domain (points j) ^ (2 ^ k) = x) :
    roundConsistencyCheck γ (fun j ↦ (domain (points j), f (points j))) β = true ↔
      ProximityGap.foldValue domain f k γ x = β := by
  rw [roundConsistencyCheck_eq_true_iff]
  have hinj : Set.InjOn (fun j ↦ domain (points j))
      (↑(Finset.univ : Finset (Fin (2 ^ k)))) :=
    (Domain.CosetFftDomain.injective.comp points.injective).injOn
  have heq : ProximityGap.foldWordAux domain f k x =
      Lagrange.interpolate Finset.univ (fun j ↦ domain (points j))
        (fun j ↦ f (points j)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hinj
    · simp
    · intro j _
      exact Lagrange.eval_interpolate_at_node f Domain.CosetFftDomain.injOn
        (by simpa [Domain.CosetFftDomainClass.mem_blockIdx] using hpoints j)
  rw [← heq]
  rfl

/-- The same local-check bridge for the subtype-valued points used by the executable
specification. Reindexing uses the domain's canonical equivalence with its elements. -/
theorem roundConsistencyCheck_eq_foldValue_of_domainPoints {n k m : ℕ}
    (domain : Domain.SmoothCosetFftDomain n 𝔽) (f : domain.toFinset → 𝔽)
    (hm : m = 2 ^ k) (points : Fin m → domain.toFinset)
    (hinj : Function.Injective points) (x γ β : 𝔽)
    (hpoints : ∀ j, (points j).val ^ (2 ^ k) = x) :
    roundConsistencyCheck γ (fun j ↦ ((points j).val, f (points j))) β = true ↔
      ProximityGap.foldValue domain (fun i ↦ f ⟨domain i, by simp⟩) k γ x = β := by
  subst m
  let e := domain.equivToFinset
  let indices : Fin (2 ^ k) ↪ Fin (2 ^ n) :=
    ⟨fun j ↦ e.symm (points j), e.symm.injective.comp hinj⟩
  have heval (j : Fin (2 ^ k)) : domain (indices j) = (points j).val :=
    domain.equivToFinset_symm_apply (points j)
  convert roundConsistencyCheck_eq_foldValue domain (fun i ↦ f ⟨domain i, by simp⟩)
    indices x γ β (fun j ↦ by rw [heval]; exact hpoints j) using 1
  simp only [heval]

/--
Completeness of the round consistency check.

Given a polynomial `f`, challenge `γ`, and `n`-th roots of unity `ω`, when `f` is honestly
evaluated at the scaled points `{ω i * s₀}`, the round consistency check succeeds with the
value `(foldNth n f γ).eval (s₀^n)`. This establishes that the Lagrange interpolant through
the evaluation points matches the n-way folding operation at the challenge point.
-/
lemma generalised_round_consistency_completeness
    {f : Polynomial 𝔽}
    {n : ℕ} [inst : NeZero n]
    {γ : 𝔽}
    {s₀ : 𝔽}
    {ω : Fin n ↪ 𝔽}
    (h : ∀ i, (ω i) ^ n = 1)
    (h₁ : s₀ ≠ 0) :
    roundConsistencyCheck
      γ
      (fun i => (ω i * s₀, f.eval (ω i * s₀)))
      ((FoldingPolynomial.polyFold f n γ).eval (s₀ ^ n)) = true := by
  unfold roundConsistencyCheck
  simp only [beq_iff_eq]
  rw [CompPoly.CPolynomial.eval_toPoly,
      CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate]
  have eval_eval₂_pow_eq_eval_pow {s : 𝔽} (i) :
    eval s (eval₂ C (Polynomial.X ^ n) (splitNth f n i)) =
      (splitNth f n i).eval (s ^ n) := by
    rw [eval₂_eq_sum]
    unfold Polynomial.eval
    rw [Polynomial.eval₂_sum, eval₂_eq_sum]
    congr
    ext e a
    rw [←eval]
    simp
  simp only [polyFold_eq_sum_of_splitNth, map_pow]
  rw [eval_finsetSum]
  conv =>
    rhs
    rhs
    ext i
    rw [eval_mul]
    simp
  apply Eq.trans (b := eval γ <|
    ∑ i : Fin n, Polynomial.X ^ (↑i : ℕ) * C (eval (s₀ ^ n) (f.splitNth n i)))
  · rw [Lagrange.eq_interpolate (ι := Fin n)
        (v := fun i => ω i * s₀)
        (s := Finset.univ)
        (f := (∑ i : Fin n, Polynomial.X ^ (↑i : ℕ) *
          C (eval (s₀ ^ n) (f.splitNth n i)))) (by {
    simp only [Finset.coe_univ, Set.injOn_univ]
    intro x y hxy
    simp at hxy
    tauto
  }) (by {
      simp only [X_pow_mul_C, Finset.card_univ, Fintype.card_fin]
      apply lt_of_le_of_lt
      · apply Polynomial.degree_sum_le
      · simp only [WithBot.bot_lt_natCast, Finset.sup_lt_iff]
        intro b _
        simp only [degree_mul, degree_pow, degree_X, nsmul_eq_mul, mul_one]
        by_cases heq: eval (s₀ ^ n) (f.splitNth n b) = 0
        · rw [heq,]
          simp
        · rw [degree_C]
          · simp only [zero_add, Nat.cast_lt, Fin.is_lt]
          · tauto
    })]
    congr
    ext i
    conv =>
      lhs
      rw [eq_sum_splitNth n f]
    rw [eval_finsetSum, eval_finsetSum]
    conv =>
      lhs
      rhs
      ext j
      rw [eval_mul, eval_eval₂_pow_eq_eval_pow]
      simp
    conv =>
      rhs
      rhs
      ext j
      rw [eval_mul]
      simp only [eval_pow, eval_X, eval_C]
      rw [←one_mul (s₀ ^ n), ←h i]
    rw [mul_pow]
  · rw [eval_finsetSum]
    conv =>
      lhs
      rhs
      ext i
      rw [eval_mul]
      simp

end RoundConsistency
