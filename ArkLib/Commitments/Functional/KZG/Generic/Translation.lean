/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Generic.Adversary

/-!
# Certified algebraic translation of generic KZG adversaries

The FKL translation preserves the real execution, hence both existing KZG binding games.
It needs no source-generator surjectivity assumption.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace KZG.Generic

variable {F G₁ G₂ Gₜ D : Type}

/-- Remove the empty game summand, retaining the uniform coin requests. -/
def relabel : QueryImpl
    (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery Empty) (CoinReply (fun _ => Unit)))
    (OracleComp (explainedSpec F (AGM.Group G₁ G₂) ℕ (fun k => Fin (k + 1))))
  | ⟨⟨.inl q, _⟩, _⟩ => q.elim
  | ⟨⟨.inr n, gs⟩, cs⟩ =>
      (explainedSpec F (AGM.Group G₁ G₂) ℕ (fun k => Fin (k + 1))).query ⟨⟨n, gs⟩, cs⟩

theorem relabel_isAlgebraic [Zero F]
    [AddMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    (p : OracleComp
      (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery Empty) (CoinReply (fun _ => Unit)))
      (Explained F D (AGM.Group G₁ G₂)))
    (gs : Groups (AGM.Group G₁ G₂)) (hp : IsAlgebraic gs p) :
    IsAlgebraic gs (simulateQ relabel p) := by
  induction p using OracleComp.inductionOn generalizing gs with
  | pure out => simpa using hp
  | query_bind q next ih =>
      rcases q with ⟨⟨q | n, qs⟩, cs⟩
      · exact q.elim
      · simp only [simulateQ_bind, simulateQ_spec_query, relabel]
        exact ⟨hp.1, fun reply => ih reply _ (hp.2 reply)⟩

variable [Field F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]

/-- Certify all source outputs over the chronological key basis. -/
def Adversary.toAlgebraic (A : Adversary F D) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) :
    AGM.Adversary F G₁ G₂ D where
  main input := simulateQ relabel ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).main input)
  algebraic input := relabel_isAlgebraic _ _
    ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).algebraic input)

def sourceOracle :
    QueryImpl (plainSpec (AGM.Group G₁ G₂) Empty (fun _ => Unit)) ProbComp :=
  fun q => q.data.elim

omit [DecidableEq G₁] [DecidableEq G₂] [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] in
theorem relabel_run
    (p : OracleComp
      (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery Empty) (CoinReply (fun _ => Unit)))
      (Explained F D (AGM.Group G₁ G₂))) :
    simulateQ (fun q => AGM.oracle q.value) (simulateQ relabel p) =
      simulateQ (fun q => withCoins (QueryImpl.ofLift unifSpec ProbComp)
        sourceOracle q.value) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro ⟨⟨q | n, gs⟩, cs⟩
  · exact q.elim
  · have h := simulateQ_spec_query
      (spec := explainedSpec F (AGM.Group G₁ G₂) ℕ (fun k => Fin (k + 1)))
      (fun q => AGM.oracle (G₁ := G₁) (G₂ := G₂) q.value)
      (⟨⟨n, gs⟩, cs⟩ : Explained F ℕ (AGM.Group G₁ G₂))
    refine h.trans ?_
    have he : AGM.groupInputs ([] : List G₁) ([] : List G₂) = fun _ => [] := by
      funext b
      cases b <;> rfl
    simp only [AGM.oracle, he, withCoins_apply_inr]
    rfl

/-- Forgetting the translation equals real execution, as an equality of programs. -/
theorem Adversary.toAlgebraic_run (A : Adversary F D) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    {n : ℕ} (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    Explained.value <$> AGM.run (A.toAlgebraic e) ck vk = A.run e ck vk := by
  have h := Pairing.toExplained_run (G := AGM.Group G₁ G₂) e A
    (QueryImpl.ofLift unifSpec ProbComp) sourceOracle (AGM.initialInput ck vk)
  unfold Interaction.Adversary.run at h
  rw [run_value] at h
  have hg : Pairing.game (T := Gₜ) (sourceOracle (G₁ := G₁) (G₂ := G₂)) = emptyOracle := by
    funext q
    exact q.data.elim
  rw [hg] at h
  simpa only [AGM.run, Adversary.toAlgebraic, relabel_run, Adversary.run] using h

/-- The translation preserves the existing evaluation-binding adversary exactly. -/
theorem Adversary.toAlgebraic_evalBinding
    (A : Adversary F (F × F × F)) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) {n : ℕ} :
    AGM.toEvalBindingAdversary (n := n) (A.toAlgebraic e) = A.toEvalBindingAdversary e := by
  funext ck vk
  rw [Adversary.toEvalBindingAdversary, ← A.toAlgebraic_run e ck vk]
  simp only [AGM.toEvalBindingAdversary, Functor.map_map, AGM.point]

/-- The translation preserves the existing function-binding adversary exactly. -/
theorem Adversary.toAlgebraic_functionBinding
    (A : Adversary F (List (F × F))) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) {n : ℕ} :
    AGM.toFunctionBindingAdversary (n := n) (A.toAlgebraic e) =
      A.toFunctionBindingAdversary e := by
  funext ck vk
  rw [Adversary.toFunctionBindingAdversary, ← A.toAlgebraic_run e ck vk]
  simp only [AGM.toFunctionBindingAdversary, Functor.map_map, AGM.openings, AGM.point,
    id_eq]

end KZG.Generic
