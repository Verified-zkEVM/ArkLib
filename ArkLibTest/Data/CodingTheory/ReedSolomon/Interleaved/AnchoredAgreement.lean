/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Anchored agreement clients

These clients

* put the tuple `(X)` in the candidate set of its own evaluation on `{0, 1, 2}` over `ℚ`;
* show that `K ≤ |ι|` is needed for injectivity of evaluation: `X` and `0` agree on the domain
  `{0}`;
* count the anchor sample space of `ZMod 5` outside a domain of size two, and show it is empty
  for a domain of size four, where `|ι| + 1 < |F|` fails;
* derive the collision bound from a list bound at the capacity radius
  `1 - (T + 3) / n - delta` and the agreement threshold `T + 3 + ⌈delta * n⌉ ≤ A`, with the rate
  `choose L 2 * ((T + 2) / (q - n - 1)) ^ 2`;
* derive the trace selection `exists_selectedTrace_before_later` by `Option.map`.
-/

namespace AnchoredAgreementTest

open Polynomial Code ReedSolomon ReedSolomon.AnchoredAgreement
open scoped ProbabilityTheory

noncomputable section

/-- The domain `{0, 1, 2} ⊆ ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ (i : ℚ), fun a b h ↦ Fin.ext (by simpa using h)⟩

-- `(X)` is a candidate of degree below `2` with `3` agreements with its own evaluation.
example : ![X] ∈ candidateSet domain3 (evalTuple domain3 ![X]) 2 3 := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · fin_cases j
    rw [Fin.zero_eta, Matrix.cons_val_fin_one, degree_X]
    exact_mod_cast (by norm_num : 1 < 2)
  · simp [agree]

/-- The one-point domain `{0} ⊆ ℚ`. -/
def domain1 : Unit ↪ ℚ := ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

theorem domain1_apply (i : Unit) : domain1 i = 0 := rfl

-- `K ≤ |ι|` is needed: on the one-point domain `{0}`, `X` and `0` have degree below `2` and the
-- same evaluation.
example : ¬ Set.InjOn (evalTuple (domain1 : Unit → ℚ))
    {Q : Fin 1 → ℚ[X] | ∀ j, (Q j).degree < 2} := by
  intro h
  have hX : ![(X : ℚ[X])] ∈ {Q : Fin 1 → ℚ[X] | ∀ j, (Q j).degree < 2} := fun j ↦ by
    fin_cases j
    rw [Fin.zero_eta, Matrix.cons_val_fin_one, degree_X]
    exact_mod_cast (by norm_num : 1 < 2)
  have h0 : ![(0 : ℚ[X])] ∈ {Q : Fin 1 → ℚ[X] | ∀ j, (Q j).degree < 2} := fun j ↦ by
    fin_cases j
    rw [Fin.zero_eta, Matrix.cons_val_fin_one, degree_zero]
    exact WithBot.bot_lt_coe 2
  have := h hX h0 (by funext i j; fin_cases j; simp [domain1_apply])
  have := congrArg (eval 1) (congrFun this 0)
  norm_num at this

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Outside the domain `{0, 1}` of `ZMod 5` there are `3 * 2` ordered distinct anchor pairs.
example (domain : Fin 2 ↪ ZMod 5) : ((Finset.univ.map domain)ᶜ.offDiag).card = 6 := by
  rw [card_offDiag_compl_map]
  simp [ZMod.card]

-- For a domain of size four in `ZMod 5`, there is no pair of distinct anchors outside it.
example (domain : Fin 4 ↪ ZMod 5) : ((Finset.univ.map domain)ᶜ.offDiag).card = 0 := by
  rw [card_offDiag_compl_map]
  simp [ZMod.card]

/-- **Collision bound at the capacity radius.** Given a list bound `L` at the capacity radius
`1 - (T + 3) / n - delta`, the agreement threshold `T + 3 + ⌈delta * n⌉ ≤ A`, and
`n + 1 < |F|`, the collision event over ordered distinct anchors outside the domain has
probability at most `choose L 2 * ((T + 2) / (q - n - 1)) ^ 2`. Here `delta` is any real number. -/
theorem prob_not_injOn_candidateSet_le_of_capacityRadius {F : Type} [Field F] [Fintype F]
    [DecidableEq F]
    {n w T A L : ℕ} (domain : Fin n ↪ F) (received : Fin n → Fin w → F) (delta : ℝ)
    (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : T + 3 + ⌈delta * n⌉₊ ≤ A)
    (hLambda : Lambda (interleavedCodeSet (κ := Fin w) (code domain (T + 3) : Set (Fin n → F)))
      (1 - ((T + 3 : ℕ) : ℝ) / n - delta) ≤ L)
    (hSpace : n + 1 < Fintype.card F) [Nonempty ((Finset.univ.map domain)ᶜ.offDiag)] :
    Pr{let p ← $ᵗ ((Finset.univ.map domain)ᶜ.offDiag)}[
        ¬ Set.InjOn (evalTuple ![p.1.1, p.1.2]) (candidateSet domain received (T + 3) A)] ≤
      ENNReal.ofReal ((L.choose 2 : ℝ) *
        (((T + 2 : ℕ) : ℝ) / ((Fintype.card F - n - 1 : ℕ) : ℝ)) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hLength
  have hceil := Nat.le_ceil (delta * n)
  have hA : ((T + 3 : ℕ) : ℝ) + delta * n ≤ A := by
    have : ((T + 3 + ⌈delta * n⌉₊ : ℕ) : ℝ) ≤ A := by exact_mod_cast hThreshold
    push_cast at this ⊢
    linarith
  have hrad : 1 - (A : ℝ) / Fintype.card (Fin n) ≤ 1 - ((T + 3 : ℕ) : ℝ) / n - delta := by
    rw [Fintype.card_fin, sub_sub, sub_le_sub_iff_left, div_add' _ _ _ hnR.ne']
    exact div_le_div_of_nonneg_right hA hnR.le
  have h := prob_not_injOn_candidateSet_offDiag_le domain received
    (by simpa using hDimension) ((Lambda_mono hrad).trans hLambda)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F - n - 1 = m + 1 := ⟨Fintype.card F - n - 2, by omega⟩
  have hqn : Fintype.card F - Fintype.card (Fin n) = m + 2 := by
    rw [Fintype.card_fin]
    omega
  have hT : T + 3 - 1 = T + 2 := by omega
  rw [hqn, hT, hm, show m + 2 - 1 = m + 1 by omega]
  push_cast
  rw [div_pow, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_) (by positivity)
  nlinarith

/-- **Trace selection.** Mapping the reduction modulo `X ^ T - 1` over the option chosen by
`exists_selectedCandidate_before_later` gives the trace of every later reconstruction. -/
theorem exists_selectedTrace_before_later {F ι κ : Type*} [Field F] [DecidableEq F] [Fintype ι]
    [Fintype κ]
    (domain : ι ↪ F) (received : ι → κ → F) {T a : ℕ} {s₁ s₂ : F}
    (hgood : Set.InjOn (evalTuple ![s₁, s₂]) (candidateSet domain received (T + 3) a))
    (c₁ c₂ : κ → F) :
    ∃ selected : Option (κ → F[X]),
      ∀ (z : F) (q I : κ → F[X]), (∀ j, (q j).degree < T) → (∀ j, (I j).degree < 3) →
        (∀ j, (I j).eval s₁ = c₁ j) → (∀ j, (I j).eval s₂ = c₂ j) →
        a ≤ agree (fun i j ↦ (cubicAnchorDivisor s₁ s₂ z).eval (domain i) * (q j).eval (domain i))
          (fun i j ↦ received i j - (I j).eval (domain i)) →
        selected.map (fun Q j ↦ Q j %ₘ (X ^ T - C 1)) =
          some (fun j ↦ cubicAnchorReconstruct s₁ s₂ z (q j) (I j) %ₘ (X ^ T - C 1)) := by
  obtain ⟨o, -, hlater⟩ := exists_selectedCandidate_before_later domain received hgood c₁ c₂
  exact ⟨o, fun z q I hq hI h₁ h₂ hagree ↦ by rw [hlater z q I hq hI h₁ h₂ hagree]; rfl⟩

-- The selected trace has degree below `T` and the values of the reconstruction on the trace
-- domain `{x | x ^ T = 1}`.
example {F : Type*} [Field F] {T : ℕ} (hT : 0 < T) (Q : F[X]) {x : F} (hx : x ^ T = 1) :
    (Q %ₘ (X ^ T - C 1)).degree < T ∧ (Q %ₘ (X ^ T - C 1)).eval x = Q.eval x :=
  ⟨traceRemainder_degree_lt T hT 1 Q, traceRemainder_eval_eq T 1 Q hx⟩

end

end AnchoredAgreementTest
