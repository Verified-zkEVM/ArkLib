/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.OneMessage
public import ArkLib.Commitments.Functional.KZG.Correctness
public import ArkLib.Commitments.Functional.KZG.Security

/-!
# KZG as a functional commitment

This file presents the KZG polynomial commitment [KZG10] as a functional commitment on the
interaction layer. The data is a coefficient vector `c : Fin (n + 1) → F`, a query is a point
`q : F`, and the answer is the evaluation `evaluate c q` (`KZG.oracleInterface`). Setup runs
`keygen`, commit and the opening proof are deterministic, and the verifier runs `verifyOpening`.
KZG uses no shared oracle, so the ambient oracle is the empty specification `emptySpec0`.

`KZG.functionalCommitment` builds the scheme with `FunctionalCommitment.oneMessage`.

## Main statements

* `KZG.correctness_functionalCommitment` gives adaptive correctness with error `0`
  ([KZG10] Definition 5, evaluation clause).
* `KZG.fixedClaimBindingAdvantage_eq` equates the fixed-claim binding advantage of `A`
  with the probability that `toKZGAdversary A` wins `KZG.functionBindingExperiment`.
* `KZG.fixedClaimBindingAdvantage_le_arsdh` bounds the fixed-claim binding advantage of `A`
  by the ARSDH advantage of `functionBindingAdversary pts (toKZGAdversary A)` when
  `e g₁ g₂ ≠ 0` and `g₁` generates `G₁`.

KZG openings have one message and no challenges. The adversary fixes all claims and provers
before any opening runs, as in [CGKY25] Definition 3.17. The
`ArkLib.Commitments.Functional.KZG.FunctionalCommitmentBounds` module transfers the algebraic
and generic group model bounds to this interface.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I.,
  *Constant-Size Commitments to Polynomials and Their Applications*][KZG10]
* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open OracleComp OracleSpec Interaction FunctionalCommitment
open scoped ENNReal

namespace FunctionalCommitment

/-! ### Games without a shared oracle -/

/-- Interpret a program over `unifSpec + emptySpec0` in `ProbComp`: coin queries pass through,
and the empty specification has no queries. -/
def coinsImpl : QueryImpl (unifSpec + emptySpec0) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + (fun t => PEmpty.elim t : QueryImpl emptySpec0 ProbComp)

/-- Without a shared oracle, interpreting a program with `ambientImpl impl` from any state gives
the program run on coins alone. -/
theorem run'_simulateQ_ambientImpl_emptySpec0 {σ α : Type}
    (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
    (program : OracleComp (unifSpec + emptySpec0) α) (s : σ) :
    (simulateQ (ambientImpl impl) program).run' s = simulateQ coinsImpl program := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with t | t
    · simp only [ambientImpl, QueryImpl.ofLift_eq_id', add_apply_inl, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
        PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.id'_apply, id_map,
        StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        bind_map_left, _root_.map_bind, coinsImpl]
      exact bind_congr fun u => ih u s
    · exact t.elim

/-- Without a shared oracle, a game runs `init` and then the program on coins alone. -/
theorem runGame_emptySpec0 {σ α : Type} (init : ProbComp σ)
    (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
    (program : OracleComp (unifSpec + emptySpec0) α) :
    runGame init impl program = init >>= fun _ => simulateQ coinsImpl program := by
  simp only [runGame, run'_simulateQ_ambientImpl_emptySpec0]

end FunctionalCommitment

namespace KZG

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
variable {n : ℕ}

/-- The evaluation interface of a coefficient vector: a query is a point, and the answer is the
value of the polynomial at that point. -/
@[reducible]
def oracleInterface (F : Type) [Field F] [DecidableEq F] (n : ℕ) :
    OracleInterface (Fin (n + 1) → F) where
  Query := F
  spec := F →ₒ F
  answer c q := evaluate c q

/-- KZG as a functional commitment. The public parameters are the committer key and the verifier
key, the commitment is a group element, and the opening proof at `q` is the group element
`generateOpening ck c q`. It is reducible so that lemmas about `oneMessage` apply to it. -/
noncomputable abbrev functionalCommitment (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (n : ℕ) : FunctionalCommitment emptySpec0 (Fin (n + 1) → F) (oracleInterface F n) :=
  oneMessage (PP := (Fin (n + 1) → G₁) × (Fin 2 → G₂)) (Cm := G₁) (Aux := PUnit)
    (Proof := fun _ => G₁)
    (liftComp (keygen (F := F) g₁ g₂ n) (unifSpec + emptySpec0))
    (fun pp (c : Fin (n + 1) → F) => pure (commit pp.1 c, ⟨⟩))
    (fun pp _ (c : Fin (n + 1) → F) _ (q : F) => pure (generateOpening pp.1 c q))
    (fun pp cm (q : F) (r : F) π => pure (verifyOpening e g₁ pp.2 cm q r π))

variable (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)

/-- KZG satisfies adaptive correctness with error `0` for every initial state computation,
ambient implementation, challenge sampler and set of data choosers ([KZG10] Definition 5,
evaluation clause). -/
theorem correctness_functionalCommitment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
    (chal : (functionalCommitment e g₁ g₂ n).ChallengeSampler)
    (Adv : Set (functionalCommitment e g₁ g₂ n).DataChooser) :
    (functionalCommitment e g₁ g₂ n).Correctness init impl chal Adv 0 := by
  refine correctness_oneMessage _ _ _ _ ?_ init impl chal Adv
  intro pp hpp d ca hca q π hπ b hb
  simp only [keygen, support_liftComp, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hpp hca hπ hb
  obtain ⟨τ, -, rfl⟩ := hpp
  subst hca hπ hb
  exact verifyOpening_generateOpening e g₁ g₂ τ d q

/-- The projected KZG adversary runs `toPlainAdversary A` on the keys and returns the commitment
and the claims as a list of openings. -/
noncomputable def toKZGAdversary {L : ℕ}
    (A : OneMessageAdversary emptySpec0 ((Fin (n + 1) → G₁) × (Fin 2 → G₂)) G₁
      (I := oracleInterface F n) (fun _ => G₁) L) :
    (Fin (n + 1) → G₁) → (Fin 2 → G₂) → ProbComp (G₁ × List (FunctionBinding.Opening F G₁)) :=
  fun ck vk =>
    (fun out => (out.1, List.ofFn fun i => ((out.2 i).1, (out.2 i).2.1, (out.2 i).2.2))) <$>
      simulateQ coinsImpl (toPlainAdversary A (ck, vk))

/-- The fixed-claim binding advantage of `A` against the functional commitment equals the
probability that `toKZGAdversary A` wins `KZG.functionBindingExperiment`. -/
theorem fixedClaimBindingAdvantage_eq {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
    (chal : (functionalCommitment e g₁ g₂ n).ChallengeSampler) (L : ℕ)
    (A : (functionalCommitment e g₁ g₂ n).FixedClaimAdversary L) :
    (functionalCommitment e g₁ g₂ n).fixedClaimBindingAdvantage init impl chal L A =
      Pr{let b ← functionBindingExperiment e g₁ g₂ (toKZGAdversary A)}[b = true] := by
  rw [fixedClaimBindingAdvantage_oneMessage, plainFixedClaimBindingAdvantage,
    runGame_emptySpec0, _root_.map_bind, OracleComp.prEvent_bind_const]
  congr 2
  simp only [plainFixedClaimBindingGame, functionBindingExperiment, toKZGAdversary, keygen,
    liftComp_pure, Fin.mOfFn_pure, LawfulMonad.pure_bind, simulateQ_bind, simulateQ_pure,
    coinsImpl, QueryImpl.simulateQ_add_liftComp_left, simulateQ_ofLift_eq_self, bind_assoc,
    bind_map_left, liftComp_bind]
  refine bind_congr fun τ => bind_congr fun out => congrArg pure ?_
  rw [functionBindingWins]
  congr 1
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
    simp
  · rw [Bool.eq_iff_iff, noConsistentData_eq_true_iff, decide_eq_true_iff]
    simp only [List.forall_mem_ofFn_iff]
    rfl

/-- If `e g₁ g₂ ≠ 0` and `g₁` generates `G₁`, the fixed-claim binding advantage of every
adversary `A` against KZG is at most the ARSDH advantage of
`functionBindingAdversary pts (toKZGAdversary A)`. The bound holds for every ambient
implementation, challenge sampler and choice of `n + 2` distinct points `pts`. -/
theorem fixedClaimBindingAdvantage_le_arsdh [DecidableEq G₁] [DecidableEq G₂] (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (pts : Fin (n + 2) ↪ F) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
    (chal : (functionalCommitment e g₁ g₂ n).ChallengeSampler) (L : ℕ)
    (A : (functionalCommitment e g₁ g₂ n).FixedClaimAdversary L) :
    (functionalCommitment e g₁ g₂ n).fixedClaimBindingAdvantage init impl chal L A ≤
      Pr{let b ← ARSDH.experiment g₁ g₂ (functionBindingAdversary pts (toKZGAdversary A))}[
        b = true] := by
  rw [fixedClaimBindingAdvantage_eq]
  exact functionBinding_le_arsdh he hg₁ pts _

end KZG
