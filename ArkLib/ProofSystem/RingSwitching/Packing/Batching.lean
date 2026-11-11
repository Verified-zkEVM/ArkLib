/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.Probability.Instances
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Separation laws for batching a family of claims

A rule supplies sampled challenges and linear weights. A strategy adds a proved collision bound.
Power and equality strategies require no zero divisors; their operational rules are available
without this separation hypothesis. Singleton batching is deterministic over any commutative ring.

`BatchingStrategy.separates_finset_le_card_filter_mul` charges only incorrect candidates.
`BatchingStrategy.separates_finset` separates a bounded candidate list. A list of at most `L`
families, fixed before the challenge, contains a family that differs from the true one yet has the
same batched value with probability at most `L` times the strategy error. It instantiates the
union bound `prEvent_exists_finset_le_card_mul` of `VCVio.EvalDist.ProbabilityBounds`;
the true family itself contributes probability zero. This does not cover lists chosen after the
challenge, nor adaptive joint-list invariants or extraction.
-/

@[expose] public section

noncomputable section

namespace RingSwitching.Packing

open MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal

/-- A sampled challenge and the linear weights it assigns to a value family. -/
structure BatchingRule (C W : Type) where
  /-- Verifier challenge type. -/
  Challenge : Type
  [sampleC : SampleableType Challenge]
  /-- Weight of each claim at the sampled challenge. -/
  weight : Challenge → W → C

attribute [instance] BatchingRule.sampleC

namespace BatchingRule

/-- Power weights with exponents `0, …, e − 1`. -/
def gammaPowers (C : Type) [Monoid C] [SampleableType C] (e : ℕ) :
    BatchingRule C (Fin e) where
  Challenge := C
  weight γ u := γ ^ (u : ℕ)

/-- Equality-kernel weights at a fresh multilinear point. -/
def eqFold (C : Type) [CommRing C] [SampleableType C] (κ : ℕ) :
    BatchingRule C (Fin κ → Fin 2) where
  Challenge := Fin κ → C
  weight c u := eqTilde (u : Fin κ → C) c

end BatchingRule

/-- A batching rule with a bound on collisions between distinct value families. -/
structure BatchingStrategy (C : Type) [CommRing C] (W : Type) [Fintype W]
    extends BatchingRule C W where
  /-- Upper bound on the collision probability. -/
  error : ℝ≥0
  /-- Distinct families collide with probability at most `error`. -/
  separates : ∀ s s' : W → C, s ≠ s' →
    Pr{let c ← $ᵗ Challenge}[∑ u, weight c u * s u = ∑ u, weight c u * s' u] ≤
      (error : ℝ≥0∞)

namespace BatchingStrategy

/-- Injective coefficient transport preserves the separation bound in a challenge algebra. -/
theorem separates_map {P C W : Type} [CommRing P] [CommRing C] [Fintype W]
    (bat : BatchingStrategy C W) (f : P →+* C) (hf : Function.Injective f)
    (s s' : W → P) (hne : s ≠ s') :
    Pr{let c ← $ᵗ bat.Challenge}[
      ∑ u, bat.weight c u * f (s u) = ∑ u, bat.weight c u * f (s' u)] ≤
      (bat.error : ℝ≥0∞) :=
  bat.separates (f ∘ s) (f ∘ s') fun h => hne (funext fun u => hf (congrFun h u))

open Classical in
/-- A fixed candidate list is charged only for families different from `s`.
The true family contributes no collision event. -/
theorem separates_finset_le_card_filter_mul {C W : Type} [CommRing C] [Fintype W]
    (bat : BatchingStrategy C W) (s : W → C) (S : Finset (W → C)) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ s' ∈ S, s' ≠ s ∧
      ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u] ≤
      (S.filter (· ≠ s)).card * (bat.error : ℝ≥0∞) := by
  calc
    _ = Pr{let c ← $ᵗ bat.Challenge}[∃ s' ∈ S.filter (· ≠ s),
        ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u] := by
      apply prEvent_congr
      intro c
      simp only [Finset.mem_filter, and_assoc]
    _ ≤ _ := prEvent_exists_finset_le_card_mul _ _ _ (ε := bat.error)
      fun s' hs' => bat.separates s' s (Finset.mem_filter.mp hs').2

/-- **Bounded candidate-list separation for a batching strategy.** Against the true family `s`,
some family of a list `S` of at most `L` candidates, fixed before the challenge, differs from `s`
but has the same batched value with probability at most `L` times the strategy error. -/
theorem separates_finset {C W : Type} [CommRing C] [Fintype W] (bat : BatchingStrategy C W)
    (s : W → C) (S : Finset (W → C)) {L : ℕ} (hS : S.card ≤ L) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ s' ∈ S, s' ≠ s ∧
      ∑ u, bat.weight c u * s' u = ∑ u, bat.weight c u * s u] ≤ L * (bat.error : ℝ≥0∞) := by
  classical
  refine (bat.separates_finset_le_card_filter_mul s S).trans ?_
  have hcard : (S.filter (· ≠ s)).card ≤ L := (Finset.card_filter_le _ _).trans hS
  gcongr

/-- A single claim needs no randomness or algebraic root bound. -/
def singleton (C W : Type) [CommRing C] [Fintype W] [Unique W] :
    BatchingStrategy C W where
  Challenge := Unit
  weight _ _ := 1
  error := 0
  separates s s' hne := by
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_not
    intro _ h
    apply hne
    have hd : s default = s' default := by simpa using h
    funext u
    simpa only [Subsingleton.elim u default] using hd

/-- Transport a batching strategy along an equivalence of claim indices. -/
def reindex {C : Type} [CommRing C] {W : Type} [Fintype W] (bat : BatchingStrategy C W)
    {W' : Type} [Fintype W'] (e : W' ≃ W) : BatchingStrategy C W' where
  Challenge := bat.Challenge
  sampleC := bat.sampleC
  weight c u' := bat.weight c (e u')
  error := bat.error
  separates s s' hne := by
    have key : ∀ (c : bat.Challenge) (t : W' → C),
        ∑ u' : W', bat.weight c (e u') * t u' = ∑ u : W, bat.weight c u * (t ∘ e.symm) u :=
      fun c t => Fintype.sum_equiv e _ _ (fun u' => by simp)
    have hne' : s ∘ e.symm ≠ s' ∘ e.symm := fun hcontra =>
      hne (funext fun u' => by simpa using congrFun hcontra (e u'))
    refine (prEvent_congr _ _ _ fun c => ?_).trans_le
      (bat.separates (s ∘ e.symm) (s' ∘ e.symm) hne')
    rw [key c s, key c s']

variable (C : Type) [CommRing C] [NoZeroDivisors C] [Fintype C] [SampleableType C]

/-- Power batching with exponents `0, …, e − 1`: distinct families collide at a uniform
challenge with probability at most `(e − 1)/|C|`. -/
def gammaPowers (e : ℕ) : BatchingStrategy C (Fin e) where
  toBatchingRule := BatchingRule.gammaPowers C e
  error := ((e - 1 : ℕ) : ℝ≥0) / (Fintype.card C : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    have : Nontrivial C := ⟨⟨s u₀, s' u₀, hu₀⟩⟩
    -- the univariate difference polynomial `∑ᵤ (s u − s' u)·Xᵘ`
    set f : MvPolynomial (Fin 1) C :=
      ∑ u : Fin e, MvPolynomial.C (s u - s' u) * X 0 ^ (u : ℕ) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge
    have hev : ∀ γ : C,
        ((∑ u : Fin e, γ ^ (u : ℕ) * s u = ∑ u : Fin e, γ ^ (u : ℕ) * s' u) ↔
          MvPolynomial.eval (fun _ : Fin 1 => γ) f = 0) := by
      intro γ
      have hcalc : MvPolynomial.eval (fun _ : Fin 1 => γ) f
          = (∑ u : Fin e, γ ^ (u : ℕ) * s u) - ∑ u : Fin e, γ ^ (u : ℕ) * s' u := by
        rw [hf, map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by
          simp only [map_mul, eval_C, map_pow, eval_X]; ring
      rw [hcalc, sub_eq_zero]
    -- `f ≠ 0`: its `X^{u₀}` coefficient is `s u₀ − s' u₀ ≠ 0`
    have hcoeff : f.coeff (Finsupp.single 0 (u₀ : ℕ)) = s u₀ - s' u₀ := by
      rw [hf, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single u₀]
      · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
        simp
      · intro u _ hu
        have hne' : Finsupp.single (0 : Fin 1) (u : ℕ) ≠ Finsupp.single 0 (u₀ : ℕ) :=
          fun h => hu (Fin.val_injective (Finsupp.single_injective _ h))
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow, ite_eq_right hne', mul_zero]
      · simp
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by rw [← hcoeff, h0]; simp)
    -- degree bound `e − 1`
    have hdeg : f.totalDegree ≤ e - 1 := by
      rw [hf]
      refine totalDegree_finsetSum_le fun u _ => ?_
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C (s u - s' u) : MvPolynomial (Fin 1) C).totalDegree = 0 :=
        totalDegree_C _
      have h2 : (X (0 : Fin 1) ^ (u : ℕ) : MvPolynomial (Fin 1) C).totalDegree ≤ (u : ℕ) :=
        le_trans (totalDegree_pow _ _) (by simp [totalDegree_X])
      have : (u : ℕ) ≤ e - 1 := Nat.le_sub_one_of_lt u.isLt
      omega
    exact (prEvent_congr _ _ _ hev).trans_le
      ((prob_schwartz_zippel_single_variable f hf_ne hdeg).trans_eq
        (ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm)

/-- Boolean-coordinate batching with a fresh multilinear point and loss `κ/|C|`. -/
def eqFold (κ : ℕ) : BatchingStrategy C (Fin κ → Fin 2) where
  toBatchingRule := BatchingRule.eqFold C κ
  error := (κ : ℝ≥0) / (Fintype.card C : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    have : Nontrivial C := ⟨⟨s u₀, s' u₀, hu₀⟩⟩
    have : IsDomain C := NoZeroDivisors.to_isDomain C
    -- the multilinear difference polynomial `MLE (s − s')`
    set f : MvPolynomial (Fin κ) C := MLE (fun u => s u - s' u) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge (MLE eq-expansion)
    have hev : ∀ c : Fin κ → C,
        ((∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → C) c * s u
            = ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → C) c * s' u) ↔
          MvPolynomial.eval c f = 0) := by
      intro c
      have hcalc : MvPolynomial.eval c f
          = (∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → C) c * s u)
            - ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → C) c * s' u := by
        rw [hf, MLE_eval, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
      rw [hcalc, sub_eq_zero]
    -- `f ≠ 0`: it interpolates `s − s'`, which is nonzero at `u₀`
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by
      have h := MLE_eval_zeroOne (R := C) u₀ (fun u => s u - s' u)
      rw [← hf, h0, map_zero] at h
      exact h.symm)
    -- degree bound: multilinear in `κ` variables
    have hdeg : f.totalDegree ≤ κ := by
      rw [hf]
      simpa using totalDegree_le_card_mul_of_mem_restrictDegree
        (MLE (fun u => s u - s' u)) 1 (MLE_mem_restrictDegree _)
    exact (prEvent_congr _ _ _ hev).trans_le
      ((prob_schwartz_zippel_mv_polynomial f hf_ne hdeg).trans_eq
        (ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm)

end BatchingStrategy

end RingSwitching.Packing

end
