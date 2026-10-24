/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Config
public import ArkLib.ProofSystem.Logup.Interaction.Source
public import ArkLib.ProofSystem.Sumcheck.Domain
public import ArkLib.Data.MvPolynomial.BatchingProbability

/-!
# Analysis of the initial scalar LogUp relation

The cleared balance polynomial depends only on the original input tables, before either scalar
challenge or helper message. Off its roots, pole-safe regrouping exhibits a nonzero helper total
or one nonzero residual table. The next independent joint draw then makes the actual native
initial relation true with probability at most `n/|E| + 1/|E|`, for every fixed helper message.

This is initial-relation analysis, not a whole-program security theorem. Original source
realization is reduced through the existing retained Q source law. No helper honesty, denominator
nonvanishing, malicious losslessness, or desired execution equality is assumed. The residual
table's multilinear extension is distinguished from its generally higher-degree residual
polynomial. The cleared polynomial is an individually noncomputable mathematical view because
it uses Mathlib's sparse polynomial operations; the table residual and helper total are executable.
-/

@[expose] public section

namespace Logup.Interaction

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators ProbabilityTheory ENNReal

variable {B E : Type} {n T ell : ℕ}

/-- Sum all entries of the retained helper tables over their Boolean rows. -/
def helperTotal [AddCommMonoid E] {K : ℕ}
    (helpers : Vector (CMlPolynomialEval E n) K) : E :=
  ∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers[k.val].get (finFunctionFinEquiv u)

variable [CommRing B] [Field E]

/-- The fixed-data cleared numerator; neither scalar challenges nor helper messages occur here. -/
noncomputable def clearedBalancePolynomial (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) : Polynomial E :=
  PartialFractions.clearedNumerator
    ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T)))
    (fun p ↦ f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
    (fun p ↦ f ((data (1, p.2)).get (finFunctionFinEquiv p.1)))

/-- Vanishing of the fixed numerator is exactly field-valued balance AFTER the scalar map.
No injectivity of that map, or equivalence with base-field balance, is silently assumed. -/
theorem clearedBalancePolynomial_eq_zero_iff [DecidableEq E] (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    clearedBalancePolynomial f data = 0 ↔ ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p ↦ f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p ↦ f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0 :=
  PartialFractions.clearedNumerator_eq_zero_iff _ _ _

/-- The fixed numerator has degree at most one less than the total occurrence count. -/
theorem natDegree_clearedBalancePolynomial_le (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    (clearedBalancePolynomial f data).natDegree ≤ T * 2 ^ n - 1 := by
  have hcard : ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin T))).card = T * 2 ^ n := by
    change ((Finset.univ : Finset (Fin n → Fin 2)) ×ˢ
      (Finset.univ : Finset (Fin T))).card = T * 2 ^ n
    rw [Finset.card_product]
    simp [Nat.mul_comm]
  have h := PartialFractions.natDegree_clearedNumerator_le
    ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T)))
    (fun p ↦ f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
    (fun p ↦ f ((data (1, p.2)).get (finFunctionFinEquiv p.1)))
  rw [hcard] at h
  exact h

/-- The actual grouped residual at one Boolean row of an arbitrary retained helper message. -/
def residualTable (cfg : Config n T ell) (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell))
    (k : Fin (T ⌈/⌉ ell)) (u : Fin n → Fin 2) : E :=
  Logup.groupResidual cfg.groups[k.val] alpha
    (fun i ↦ f ((data (0, i)).get (finFunctionFinEquiv u)))
    (fun i ↦ f ((data (1, i)).get (finFunctionFinEquiv u)))
    (helpers[k.val].get (finFunctionFinEquiv u))

/-- Away from the fixed numerator's roots, some helper total or residual-table entry is nonzero.
The implication remains valid when individual denominators vanish. -/
theorem total_or_residual_ne_zero (cfg : Config n T ell) (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E)
    (halpha : (clearedBalancePolynomial f data).eval alpha ≠ 0)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell)) :
    helperTotal helpers ≠ 0 ∨ ∃ k u, residualTable cfg f alpha data helpers k u ≠ 0 := by
  classical
  by_cases htotal : helperTotal helpers = 0
  · right
    by_contra hres
    apply halpha
    apply Logup.eval_clearedNumerator_eq_zero_of_groupResidual_eq_zero cfg.groups alpha
      (Finset.univ : Finset (Fin n → Fin 2))
      (fun i u ↦ f ((data (0, i)).get (finFunctionFinEquiv u)))
      (fun i u ↦ f ((data (1, i)).get (finFunctionFinEquiv u)))
      (fun k u ↦ helpers[k.val].get (finFunctionFinEquiv u))
      (List.Perm.of_eq cfg.flatten_groups)
    · intro u _ k
      by_contra hne
      exact hres ⟨k, u, hne⟩
    · exact htotal
  · exact Or.inl htotal

/-- Boolean summation of the actual Q realization uses the MLE of the residual TABLE. -/
theorem sum_qPolynomial (cfg : Config n T ell) (f : B →+* E) (alpha : E)
    (z : Fin n → E) (lambda : Fin (T ⌈/⌉ ell) → E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell)) :
    (∑ u : Fin n → Fin 2, MvPolynomial.eval (u : Fin n → E)
      (qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell
        cfg.length_group_le data helpers).val) =
      helperTotal helpers + ∑ k, lambda k *
        MvPolynomial.eval z (MvPolynomial.MLE (residualTable cfg f alpha data helpers k)) := by
  change (∑ u : Fin n → Fin 2, MvPolynomial.eval (u : Fin n → E)
    (Logup.batchedPolynomial cfg.groups alpha z lambda
      (fun i ↦ (tablePolynomial f n (data (0, i))).val)
      (fun i ↦ (tablePolynomial f n (data (1, i))).val)
      (fun k ↦ (tablePolynomial (RingHom.id E) n helpers[k.val]).val))) = _
  rw [Logup.sum_eval_batchedPolynomial]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro k _
    simp [tablePolynomial, MvPolynomial.MLE_eval_zeroOne]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply congrArg (fun rho ↦ MvPolynomial.eval z (MvPolynomial.MLE rho))
    funext u
    rw [Logup.eval_residualPolynomial]
    simp only [tablePolynomial, MvPolynomial.MLE_eval_zeroOne, RingHom.id_apply]
    rfl

/-- The native initial relation is exactly the affine batch of residual-table MLEs for the
same retained input handler and arbitrary helper message. -/
theorem initial_relation_iff (cfg : Config n T ell) (f : B →+* E) (alpha : E)
    (z : Fin n → E) (lambda : Fin (T ⌈/⌉ ell) → E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell)) :
    Sumcheck.Interaction.MultivariateRound.closedRelation E n (ell + 2) (boolEmbedding E) 0
      ⟨⟨0, Fin.elim0⟩,
        (qView f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers)⟩ ↔
      helperTotal helpers + ∑ k, lambda k *
        MvPolynomial.eval z (MvPolynomial.MLE (residualTable cfg f alpha data helpers k)) = 0 := by
  rw [qView_realizes f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell
    cfg.length_group_le A inputView impl data hinput helpers]
  unfold Sumcheck.Interaction.MultivariateRound.closedRelation
  change (∑ x ∈ (boolDomain E n).cube, MvPolynomial.eval
    (Fin.append (Fin.elim0 : Fin 0 → E) x ∘ Fin.cast (by omega))
    (qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell
      cfg.length_group_le data helpers).val) = 0 ↔ _
  simp only [Fin.elim0_append, Function.comp_def, Fin.cast_cast, Fin.cast_eq_self]
  rw [sum_cube_boolDomain, sum_qPolynomial]

variable [Fintype E] [SampleableType E]

/-- For fixed scalar challenge and arbitrary fixed helpers, off the fixed numerator roots the
next independent joint draw makes the actual native initial relation true with error n/q+1/q. -/
theorem prob_initial_relation_le (cfg : Config n T ell) (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E)
    (halpha : (clearedBalancePolynomial f data).eval alpha ≠ 0)
    (A : PFunctor.{0, 0}) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell)) :
    Pr{let joint ← $ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))}[
      Sumcheck.Interaction.MultivariateRound.closedRelation E n (ell + 2) (boolEmbedding E) 0
        ⟨⟨0, Fin.elim0⟩,
          (qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
            (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers)⟩] ≤
      (n : ℝ≥0∞) / Fintype.card E + (Fintype.card E : ℝ≥0∞)⁻¹ := by
  have hdichotomy := total_or_residual_ne_zero cfg f data alpha halpha helpers
  simpa only [initial_relation_iff cfg f alpha _ _ A inputView impl data hinput helpers,
    mul_comm] using Probability.prob_MLE_affine_batch_eq_zero_le (helperTotal helpers)
      (residualTable cfg f alpha data helpers) hdichotomy

end Logup.Interaction
