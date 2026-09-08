/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.Probability.Instances

/-!
# Separation laws for batching a family of claims

A strategy supplies uniform challenges, weights, and a proved collision bound. The interface
is open to further strategies; the field/domain assumptions belong to the power and equality
instances, not to the record. Singleton batching is deterministic over any commutative ring.
-/

noncomputable section

namespace RingSwitching.Packing

open MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal

/-- Uniform batching together with its separation bound for distinct value families. -/
structure BatchingStrategy (P : Type) [CommRing P] (W : Type) [Fintype W] where
  /-- Verifier challenge type. -/
  Challenge : Type
  [ftC : Fintype Challenge]
  [neC : Nonempty Challenge]
  /-- Weight of each claim for a given challenge. -/
  weight : Challenge → W → P
  /-- Upper bound on the collision probability. -/
  error : ℝ≥0
  /-- Distinct families coincide after weighting with probability at most `error`. -/
  separates : ∀ s s' : W → P, s ≠ s' →
    Pr_{ let c ←$ᵖ Challenge }[∑ u, weight c u * s u = ∑ u, weight c u * s' u] ≤
      (error : ℝ≥0∞)

attribute [instance] BatchingStrategy.ftC BatchingStrategy.neC

namespace BatchingStrategy

/-- Injective coefficient transport preserves the separation bound in a challenge algebra. -/
theorem separates_map {P C W : Type} [CommRing P] [CommRing C] [Fintype W]
    (bat : BatchingStrategy C W) (f : P →+* C) (hf : Function.Injective f)
    (s s' : W → P) (hne : s ≠ s') :
    Pr_{ let c ←$ᵖ bat.Challenge }[
      ∑ u, bat.weight c u * f (s u) = ∑ u, bat.weight c u * f (s' u)] ≤
      (bat.error : ℝ≥0∞) :=
  bat.separates (f ∘ s) (f ∘ s') fun h => hne (funext fun u => hf (congrFun h u))

/-- A single claim needs no randomness or algebraic root bound. -/
def singleton (P W : Type) [CommRing P] [Fintype W] [Unique W] :
    BatchingStrategy P W where
  Challenge := Unit
  weight _ _ := 1
  error := 0
  separates s s' hne := by
    apply le_of_eq
    apply prob_eq_zero_of_forall_not
    intro _ h
    apply hne
    have hd : s default = s' default := by simpa using h
    funext u
    simpa only [Subsingleton.elim u default] using hd

/-- Transport a batching strategy along an equivalence of claim indices. -/
def reindex {P : Type} [CommRing P] {W : Type} [Fintype W] (bat : BatchingStrategy P W)
    {W' : Type} [Fintype W'] (e : W' ≃ W) : BatchingStrategy P W' where
  Challenge := bat.Challenge
  weight c u' := bat.weight c (e u')
  error := bat.error
  separates s s' hne := by
    have key : ∀ (c : bat.Challenge) (t : W' → P),
        ∑ u' : W', bat.weight c (e u') * t u' = ∑ u : W, bat.weight c u * (t ∘ e.symm) u :=
      fun c t => Fintype.sum_equiv e _ _ (fun u' => by simp)
    have hne' : s ∘ e.symm ≠ s' ∘ e.symm := fun hcontra =>
      hne (funext fun u' => by simpa using congrFun hcontra (e u'))
    refine (Pr_congr fun c => ?_).trans_le (bat.separates (s ∘ e.symm) (s' ∘ e.symm) hne')
    rw [key c s, key c s']

variable (P : Type) [CommRing P] [IsDomain P] [Fintype P]


/-- Zero-based power batching with degree bound `e−1`. The generalized note instead starts
at exponent one; its looser `e/|P|` bound describes a distinct challenge event at zero. -/
def gammaPowers (e : ℕ) : BatchingStrategy P (Fin e) where
  Challenge := P
  weight γ u := γ ^ (u : ℕ)
  error := ((e - 1 : ℕ) : ℝ≥0) / (Fintype.card P : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    -- the univariate difference polynomial `∑ᵤ (s u − s' u)·Xᵘ`
    set f : MvPolynomial (Fin 1) P := ∑ u : Fin e, C (s u - s' u) * X 0 ^ (u : ℕ) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge
    have hev : ∀ γ : P,
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
    have hcoeff : MvPolynomial.coeff (Finsupp.single 0 (u₀ : ℕ)) f = s u₀ - s' u₀ := by
      rw [hf, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single u₀]
      · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
        simp
      · intro u _ hu
        have hne' : Finsupp.single (0 : Fin 1) (u : ℕ) ≠ Finsupp.single 0 (u₀ : ℕ) :=
          fun h => hu (Fin.val_injective (Finsupp.single_injective _ h))
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow, if_neg hne', mul_zero]
      · simp
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by rw [← hcoeff, h0]; simp)
    -- degree bound `e − 1`
    have hdeg : f.totalDegree ≤ e - 1 := by
      rw [hf]
      refine totalDegree_finsetSum_le fun u _ => ?_
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 : (C (s u - s' u) : MvPolynomial (Fin 1) P).totalDegree = 0 := totalDegree_C _
      have h2 : (X (0 : Fin 1) ^ (u : ℕ) : MvPolynomial (Fin 1) P).totalDegree ≤ (u : ℕ) :=
        le_trans (totalDegree_pow _ _) (by simp [totalDegree_X])
      have : (u : ℕ) ≤ e - 1 := Nat.le_sub_one_of_lt u.isLt
      omega
    exact (Pr_congr hev).trans_le
      ((prob_schwartz_zippel_single_variable f (e - 1) hf_ne hdeg).trans_eq
        (ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm)


/-- Boolean-coordinate batching with a fresh multilinear point and loss `κ/|P|`. -/
def eqFold (κ : ℕ) : BatchingStrategy P (Fin κ → Fin 2) where
  Challenge := Fin κ → P
  weight c u := eqTilde (u : Fin κ → P) c
  error := (κ : ℝ≥0) / (Fintype.card P : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    -- the multilinear difference polynomial `MLE (s − s')`
    set f : MvPolynomial (Fin κ) P := MLE (fun u => s u - s' u) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge (MLE eq-expansion)
    have hev : ∀ c : Fin κ → P,
        ((∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s u
            = ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s' u) ↔
          MvPolynomial.eval c f = 0) := by
      intro c
      have hcalc : MvPolynomial.eval c f
          = (∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s u)
            - ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s' u := by
        rw [hf, MLE_eval, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
      rw [hcalc, sub_eq_zero]
    -- `f ≠ 0`: it interpolates `s − s'`, which is nonzero at `u₀`
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by
      have h := MLE_eval_zeroOne (R := P) u₀ (fun u => s u - s' u)
      rw [← hf, h0, map_zero] at h
      exact h.symm)
    -- degree bound: multilinear in `κ` variables
    have hdeg : f.totalDegree ≤ κ := by
      rw [hf]
      simpa using totalDegree_le_card_mul_of_mem_restrictDegree
        (MLE (fun u => s u - s' u)) 1 (MLE_mem_restrictDegree _)
    exact (Pr_congr hev).trans_le
      ((prob_schwartz_zippel_mv_polynomial f hf_ne hdeg).trans_eq
        (ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm)


end BatchingStrategy

end RingSwitching.Packing

end
