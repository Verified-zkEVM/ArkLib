/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputablePool
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.Cardinality
/-!
# Sizes of the computed square-system family

The paper uses degree D ≤ max{μ, 1+2K(μ-1)} and at most (2n)^r systems before calling the sparse
solver. These bounds apply to the literal family returned by squareSystemsFromEquation.
The initial row has degree at most μ; agreement and tail rows inherit the common Taylor numerator
bound. These are degree/cardinality bounds, not an arithmetic-cost theorem for solving the systems.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems
open PolynomialDifferential CPoly CPoly.CMvPolynomial

private theorem all_rows_of_mem_enumerate {P ι : Type*} [DecidableEq P] [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) (property : P → Prop)
    (hinitial : property initial) (hpool : ∀ j, property (pool j))
    (rows : Fin (r + 1) → P) (hrows : rows ∈ enumerateSquareSystems r initial pool) :
    ∀ i, property (rows i) := by
  obtain ⟨selected, _, rfl⟩ := Finset.mem_image.mp hrows
  intro i
  exact Fin.cases hinitial (fun j => hpool _) i

variable {F : Type*} [Field F] [DecidableEq F] {r : ℕ}

local instance sumFinOrderForBounds (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- Every emitted row has degree at most max{μ, 1+τ(μ-1)}. Positivity is the active-jet
condition used by the Taylor degree bound. -/
theorem computedSquareSystems_degree_le (center : F) (Q : CMvPolynomial (r + 2) F)
    (K τ k n μ : ℕ) (hk : k ≤ K) (hτ : TaylorExponentSufficient r K τ)
    (hpositive : 0 < (semanticEquation Q).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hdegree : (semanticEquation Q).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ μ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (rows : Fin (r + 1) → CMvPolynomial (r + 1) F)
    (hrows : rows ∈ squareSystemsFromEquation center Q K τ k n hk domain received) :
    ∀ i, (fromCMvPolynomial (rows i)).totalDegree ≤ max μ (1 + τ * (μ - 1)) := by
  apply all_rows_of_mem_enumerate r _ _
    (fun row => (fromCMvPolynomial row).totalDegree ≤ max μ (1 + τ * (μ - 1)))
    ?_ ?_ rows hrows
  · rw [fromCMvPolynomial_computableInitialJetEquation]
    exact (totalDegree_initialJetEquation_le center (semanticEquation Q)).trans
      (hdegree.trans (Nat.le_max_left _ _))
  · intro j
    rw [computableFullPool_semantics center (semanticEquation Q) _ _ τ k n hk domain received
      (fun l => by
        rw [computableRationalTaylorTable_get center Q K l.val l.isLt]
        exact fromCMvPolynomial_computableRationalTaylorNumerator center Q l.val)
      (fromCMvPolynomial_computableInitialJetSeparant center Q)]
    have hbound :
        1 + τ * ((semanticEquation Q).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) - 1) ≤
          max μ (1 + τ * (μ - 1)) := by
      apply (Nat.add_le_add_left (Nat.mul_le_mul_left τ (Nat.sub_le_sub_right hdegree 1)) 1).trans
      exact Nat.le_max_right _ _
    cases j with
    | inl j =>
        exact (totalDegree_taylorAgreementEquation_le_of_exponent center (semanticEquation Q)
          hpositive K τ hτ _ _).trans hbound
    | inr j =>
        exact (totalDegree_commonTaylorNumerator_le_of_exponent center (semanticEquation Q)
          hpositive K τ hτ _).trans hbound

/-- The concrete producer satisfies the paper's (2n)^r family bound when K≤n. -/
theorem computedSquareSystems_card_le (center : F) (Q : CMvPolynomial (r + 2) F)
    (K τ k n : ℕ) (hk : k ≤ K) (hK : K ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F) :
    (squareSystemsFromEquation center Q K τ k n hk domain received).card ≤ (2 * n) ^ r := by
  exact card_fullPoolSystems_le r n K k hK _ _

/-- Specialize to the common exponent 2K printed in the decoder construction. -/
theorem computedSquareSystems_paper_degree_le (center : F) (Q : CMvPolynomial (r + 2) F)
    (K k n μ : ℕ) (hk : k ≤ K)
    (hpositive : 0 < (semanticEquation Q).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hdegree : (semanticEquation Q).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ μ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (rows : Fin (r + 1) → CMvPolynomial (r + 1) F)
    (hrows : rows ∈ squareSystemsFromEquation center Q K (2 * K) k n hk domain received) :
    ∀ i, (fromCMvPolynomial (rows i)).totalDegree ≤ max μ (1 + 2 * K * (μ - 1)) :=
  computedSquareSystems_degree_le center Q K (2 * K) k n μ hk
    (taylorExponentSufficient_two_mul r K) hpositive hdegree domain received rows hrows

end ReedSolomon.HiddenDerivative.SquareSystems
