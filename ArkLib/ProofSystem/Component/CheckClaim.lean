/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SeqCompose

/-!
  # Simple (Oracle) Reduction: Check if a predicate / claim on a statement is satisfied

  This is a zero-round (oracle) reduction. There is no witness.

  1. Reduction version: the input relation becomes a predicate on the statement. Verifier checks
     this predicate, and returns the same statement if successful.

  2. Oracle reduction version: the input relation becomes an oracle computation having as oracles
     the oracle statements, and taking in the (non-oracle) statement as an input (i.e. via
     `ReaderT`), and returning a `Prop`. Verifier performs this oracle computation, and returns the
     same statement & oracle statement if successful.

  In both cases, the output relation is trivial (since the input relation has been checked by the
  verifier).

  Note: after the refactor (to disallow failure in `OracleComp`), this may become a special case
  of `ReduceClaim`.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

/-- The prover for the `CheckClaim` reduction. -/
@[inline, specialize]
def prover : Prover oSpec Statement Unit Statement Unit !p[] where
  PrvState := fun _ => Statement
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

/-- The verifier for the `CheckClaim` reduction. -/
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => do guard (pred stmt); return stmt

/-- The reduction for the `CheckClaim` reduction. -/
@[inline, specialize]
def reduction : Reduction oSpec Statement Unit Statement Unit !p[] where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

@[reducible, simp]
def relIn : Set (Statement × Unit) := { ⟨stmt, _⟩ | pred stmt }

@[reducible, simp]
def relOut : Set (Statement × Unit) := Set.univ

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the
  input relation, and the output relation being always true. -/
@[simp]
theorem reduction_completeness [Nonempty σ] [DecidableEq Statement] :
    (reduction oSpec Statement pred).perfectCompleteness init impl
    (relIn Statement pred) (relOut Statement) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro stmt () valid
  simp only [relIn, Set.mem_setOf_eq] at valid
  -- valid : pred stmt
  -- First simplify the reduction run
  have hrun : (reduction oSpec Statement pred).run stmt () =
      (pure ((default, stmt, ()), stmt) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
          Prover.runToRound, guard, if_pos valid]; rfl
  simp only [hrun]
  -- Now identical to id_perfectCompleteness pattern
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    -- Unfold OptionT.run on pure, then simulateQ_pure, then StateT
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    simp [relOut]

/-- The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier
  template `Verifier.KnowledgeStateFunction.id`: at round `0` the state simply records that the
  input is in `relIn`. -/
def knowledgeStateFunction :
    (verifier oSpec Statement pred).KnowledgeStateFunction
      init impl (relIn Statement pred) (relOut Statement)
      (Extractor.RoundByRound.id (Witness := Unit)) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => (stmtIn, witIn) ∈ relIn Statement pred
  toFun_empty := fun _ _ => by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmtIn tr _ h => by
    -- Reduce the dependent-pattern goal to `pred stmtIn`.
    change pred stmtIn
    by_contra hpred
    -- If `pred stmtIn` is false then `guard` fails and the OptionT computation always returns
    -- `none`, so no probability event can be positive.
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, _⟩ := h
    rw [OptionT.mem_support_iff] at hx
    -- Reduce the failing verifier by unfolding the `guard` branch.
    have hverify : (verifier oSpec Statement pred).run stmtIn tr =
        (OptionT.mk (pure none) : OptionT (OracleComp oSpec) Statement) := by
      simp only [Verifier.run, verifier]
      change (do guard (pred stmtIn); return stmtIn :
        OptionT (OracleComp oSpec) Statement) = _
      simp [guard, hpred]
      rfl
    rw [hverify] at hx
    -- Now `simulateQ impl (OptionT.mk (pure none))` has empty support.
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    rw [show ((OptionT.mk (pure none) : OptionT (OracleComp oSpec) Statement)) =
        ((pure none : OracleComp oSpec (Option Statement)) : _) from rfl] at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx

/-- The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness. -/
theorem verifier_rbr_knowledge_soundness :
    (verifier oSpec Statement pred).rbrKnowledgeSoundness init impl
      (relIn Statement pred) (relOut Statement) 0 := by
  refine ⟨_, _, knowledgeStateFunction oSpec Statement pred (init := init) (impl := impl), ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `CheckClaim` oracle reduction: it forwards the statement and all
oracle statements unchanged (there is no message and no witness). -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

/-- The oracle verifier for the `CheckClaim` oracle reduction is a **pure pass-through**: it
returns the statement and all oracle statements unchanged. The predicate
being checked is *not* run as an effectful `guard`/oracle computation here; instead it lives in the
output relation `oracleRelOut`. This keeps the verifier `IsPure` (so it can be a left factor in a
CWSS composition) and sidesteps the unfinished no-failure `OracleComp` refactor. (The `guard`-based
plain-reduction variant above is retained as a rightmost-only factor.) -/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => pure stmt
  embed := Function.Embedding.inl
  hEq := fun _ => rfl

/-- The oracle reduction for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement

variable {Statement} {OStatement}

/-- The pure pass-through oracle verifier's underlying non-oracle verifier returns the combined
input statement unchanged. -/
theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (!p[] : ProtocolSpec 0).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, oStmt⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  rw [show simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
        (pure stmt : OptionT (OracleComp _) Statement)
      = (pure stmt : OptionT (OracleComp oSpec) Statement) from rfl, pure_bind]
  congr 1

/-- The `CheckClaim` oracle verifier is pure: its underlying verifier deterministically returns the
combined statement, which discharges the deterministic-left hypothesis of the CWSS binary append. -/
instance instIsPure : (oracleVerifier oSpec Statement OStatement).toVerifier.IsPure :=
  ⟨fun p _ => p, fun ⟨_, _⟩ _ => oracleVerifier_toVerifier_run (oSpec := oSpec)⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Statement → (∀ i, OStatement i) → Prop)
  (relIn : Set ((Statement × ∀ i, OStatement i) × Unit))

/-- The output relation of the pure-pass-through `CheckClaim`: the input relation intersected with
the checked predicate `P` on the combined statement. Because the verifier is a pure pass-through,
"acceptance" is exactly membership in `oracleRelOut.language`, i.e. `P` holding — so the check is
enforced by the relation rather than by a runtime `guard`. -/
@[reducible, simp]
def oracleRelOut : Set ((Statement × ∀ i, OStatement i) × Unit) :=
  relIn ∩ {x | P x.1.1 x.1.2}

/-- **Coordinate-wise special soundness of `CheckClaim`.** The verifier is a pure pass-through with
no challenge rounds, so CWSS collapses (via the oracle no-challenge bridge
`coordinateWiseSpecialSound_of_isEmpty_challengeIdx`) to a transcript-level obligation. The
extractor is trivial (`e := fun _ _ => ()`, there is no witness); since the pass-through output
equals the input and `oracleRelOut P relIn ⊆ relIn`, accepting into `oracleRelOut.language` forces
the input into `relIn`. Holds for any coordinate-wise structure `D`. -/
theorem oracleVerifier_coordinateWiseSpecialSound (D : CWSSStructure (!p[] : ProtocolSpec 0)) :
    (oracleVerifier oSpec Statement OStatement).coordinateWiseSpecialSound init impl D relIn
      (oracleRelOut P relIn) := by
  refine OracleVerifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx init impl D
    (oracleVerifier oSpec Statement OStatement) relIn (oracleRelOut P relIn) (fun _ _ => ()) ?_
  rintro ⟨stmt, oStmt⟩ tr hAcc
  have hmem := Verifier.mem_of_pure_accepting init impl
    (oracleVerifier oSpec Statement OStatement).toVerifier ⟨stmt, oStmt⟩ tr
    (oracleRelOut P relIn).language _ (oracleVerifier_toVerifier_run (oSpec := oSpec)) hAcc
  obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
  exact hu.1

end OracleReduction

end CheckClaim
