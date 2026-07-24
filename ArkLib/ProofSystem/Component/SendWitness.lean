/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SeqCompose
import Mathlib.Data.FinEnum

/-!
# Simple Oracle Reduction - SendWitness

This file contains the (oracle) reduction for the trivial one-message protocol where the prover
sends the (entire) witness to the verifier. There are two variants:

1. For oracle reduction: the witness is an indexed family of types, and sent in a single oracle
  message to the verifier (using the derived indexed product instance for oracle interface).

  We also define a simpler variant, `SendSingleWitness`, where one sends a single witness (converted
  to be indexed by `Fin 1`).

2. For reduction (`SendWitness`, no oracle statements): the witness is a type, and sent as a
  statement to the verifier.

## Security

The verifier of each variant is **pure** (`Verifier.IsPure` / `OracleVerifier.toVerifier.IsPure`)
and has no challenge rounds, so it is **coordinate-wise special sound** for any `CWSSStructure`
(`verifier_coordinateWiseSpecialSound` and, for the oracle variant,
`SendSingleWitness.oracleVerifier_coordinateWiseSpecialSound`), via the no-challenge bridge
`Verifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx`. The extractor takes the witness to be
the prover's single message (`e := fun _ tr => tr 0`) — the canonical "open in the clear" base case.
These results are `sorryAx`-free. The indexed-family oracle variant (`section OracleReduction`) is
deferred; see the note there.
-/

open OracleSpec OracleComp OracleQuery ProtocolSpec Function Equiv

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

namespace SendWitness

/-!
  First, the reduction version (no oracle statements)
-/

section Reduction

variable (Witness : Type)

@[reducible, simp]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

instance : ∀ i, VCVCompatible ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

/-- The `SendWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This is
what makes its (coordinate-wise) special soundness reduce to the no-challenge bridge. -/
instance instIsEmptyChallengeIdx : IsEmpty (pSpec Witness).ChallengeIdx := ⟨fun ⟨0, h⟩ => nomatch h⟩

@[inline, specialize]
def prover : Prover oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => pure (⟨stmt, wit⟩, ())

@[inline, specialize]
def verifier : Verifier oSpec Statement (Statement × Witness) (pSpec Witness) where
  verify := fun stmt transcript => pure ⟨stmt, transcript 0⟩

@[inline, specialize]
def reduction : Reduction oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement Witness

variable {Statement} {Witness}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

@[reducible, simp]
def toRelOut : Set ((Statement × Witness) × Unit) :=
  Prod.fst ⁻¹' relIn

/-- The `SendWitness` verifier is pure: it deterministically returns `⟨stmt, transcript 0⟩`. This
discharges the deterministic-left hypothesis of the CWSS/tree-soundness binary append, so the
component can appear as a left factor in a sequential composition. -/
instance instIsPure : (verifier oSpec Statement Witness).IsPure :=
  ⟨fun stmt tr => ⟨stmt, tr 0⟩, fun _ _ => rfl⟩

open Classical in
/-- The `SendWitness` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness init impl relIn (toRelOut relIn) := by
  unfold Reduction.perfectCompleteness Reduction.completeness
  intro stmtIn witIn hIn
  sorry

/-- **Coordinate-wise special soundness of `SendWitness`.** The verifier has no challenge rounds, so
CWSS collapses (via the no-challenge bridge `coordinateWiseSpecialSound_of_isEmpty_challengeIdx`) to
a transcript-level extraction obligation. The extractor is `e := fun _ tr => tr 0`: the witness *is*
the (single) prover message. Since the verifier is pure with output `⟨stmt, tr 0⟩` and
`relOut = Prod.fst ⁻¹' relIn`, acceptance into `relOut.language` forces `⟨stmt, tr 0⟩ ∈ relIn`,
which is exactly the extracted witness. This is the canonical "open in the clear" CWSS base case,
and holds for *any* coordinate-wise structure `D`. -/
theorem verifier_coordinateWiseSpecialSound (D : CWSSStructure (pSpec Witness)) :
    (verifier oSpec Statement Witness).coordinateWiseSpecialSound init impl D relIn
      (toRelOut relIn) := by
  refine Verifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx init impl D
    (verifier oSpec Statement Witness) relIn (toRelOut relIn) (fun _ tr => tr 0) ?_
  intro stmtIn tr hAcc
  have hmem : (⟨stmtIn, tr 0⟩ : Statement × Witness) ∈ (toRelOut relIn).language :=
    Verifier.mem_of_pure_accepting init impl (verifier oSpec Statement Witness) stmtIn tr
      (toRelOut relIn).language ⟨stmtIn, tr 0⟩ rfl hAcc
  obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
  exact hu

end Reduction

/-!
  Now, the oracle reduction version.

  **Status: deferred.** This indexed-family variant is currently only a prover skeleton (the oracle
  verifier and reduction below are left commented out). Finishing it *as sketched* is blocked by the
  current `OracleVerifier` interface: the prover sends the whole family as a **single** product
  message `∀ i, Witness i` (`oraclePSpec` has one round), yet the intended output oracle statements
  `OStatement ⊕ᵥ Witness` and the commented `embed` (via `FinEnum.equiv`) expect **per-index**
  oracles. Under `embed`/`hEq` an output oracle can only *select* an existing source oracle, not
  decompose a product; this is exactly the `simOStmt` refactor noted in `OracleReduction/Basic`.
  Two coherent designs resolve it — (a) keep the single product message and output it as one product
  oracle (which is `SendSingleWitness` at `Witness := ∀ i, Witness i`), or (b) rewrite `oraclePSpec`
  as a `FinEnum.card ιw`-round protocol so each witness is its own message (per-index oracles then
  come from per-message sources). Both are out of scope for the CWSS work; the pure-verifier ⟹ CWSS
  pattern is already validated end-to-end by the reduction version above and by `SendSingleWitness`
  below (each with `IsPure` + `coordinateWiseSpecialSound`, all `sorryAx`-free).
-/

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  {ιw : Type} [FinEnum ιw] (Witness : ιw → Type) [∀ i, OracleInterface (Witness i)]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[∀ i, Witness i]⟩

-- instance : IsEmpty (oraclePSpec Witness).ChallengeIdx where
--   false := by aesop
-- instance : ∀ i, OracleInterface ((oraclePSpec Witness).Message i)
--   | ⟨0, _⟩ => OracleInterface.instForall _
-- instance : ∀ i, VCVCompatible ((oraclePSpec Witness).Challenge i)
--   | ⟨0, _⟩ => by aesop

/-- The oracle prover for the `SendWitness` oracle reduction.

For each round `i : Fin (FinEnum.card ιw)`, the prover sends the witness
`wit (FinEnum.equiv.symm i)` to the verifier.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement (∀ i, Witness i)
    Statement (OStatement ⊕ᵥ Witness) Unit
    (oraclePSpec Witness) where
  PrvState := fun _ => (Statement × (∀ i, OStatement i)) × (∀ i, Witness i)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  -- No challenge is sent to the prover
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ => pure (⟨stmt, Sum.rec oStmt wit⟩, ())

-- /-- The oracle verifier for the `SendWitness` oracle reduction.

-- It receives the input statement `stmt` and returns it, and also specifying the combination of
-- `OStatement` and `Witness` as the output oracle statements.
-- -/
-- @[inline, specialize]
-- def oracleVerifier : OracleVerifier (oraclePSpec Witness) oSpec
--     Statement Statement OStatement (OStatement ⊕ᵥ Witness) where
--   verify := fun stmt _ => pure stmt
--   -- ιₛ ⊕ ιw ↪ ιₛ ⊕ (oraclePSpec Witness).MessageIdx
--   embed := Embedding.sumMap (.refl _)
--     -- ιw ↪ (oraclePSpec Witness).MessageIdx
--     (Equiv.toEmbedding
--       -- ιw ≃ (oraclePSpec Witness).MessageIdx
--       -- after unfolding : ιw ≃ { i : Fin (FinEnum.card ιw) // True }
--       (.trans FinEnum.equiv -- ιw ≃ Fin (FinEnum.card ιw)
--         <| .symm -- { i : Fin (FinEnum.card ιw) // True } ≃ Fin (FinEnum.card ιw)
--         <| .subtypeUnivEquiv (by simp)))
--   hEq := by intro i; rcases i <;> simp

-- @[inline, specialize]
-- def oracleReduction : OracleReduction (oraclePSpec Witness) oSpec
--     Statement (∀ i, Witness i) Statement Unit
--     OStatement (OStatement ⊕ᵥ Witness) where
--   prover := oracleProver oSpec Statement OStatement Witness
--   verifier := oracleVerifier oSpec Statement OStatement Witness

-- variable {Statement} {OStatement} {Witness} [oSpec.Fintype]
--   (oRelIn : Statement × (∀ i, OStatement i) → (∀ i, Witness i) → Prop)

-- @[reducible, simp]
-- def toORelOut : Statement × (∀ i, (OStatement ⊕ᵥ Witness) i) → Unit → Prop :=
--   fun ⟨stmt, oStmtAndWit⟩ _ =>
--     oRelIn ⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩ (fun i => oStmtAndWit (Sum.inr i))

-- /-- Running the oracle prover returns the expected result: `(stmt, Sum.rec oStmt wit)`. -/
-- theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : ∀ i, Witness i} :
--     (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
--       pure ((stmt, Sum.rec oStmt wit), (), fun i => wit (FinEnum.equiv.symm i)) := by
--   simp [Prover.run, Prover.runToRound, Prover.processRound, oracleProver]
--   sorry

-- /-- The `SendWitness` oracle reduction satisfies perfect completeness. -/
-- @[simp]
-- theorem oracleReduction_completeness :
--     (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness oRelIn
--     (toORelOut oRelIn) := by
--   simp [OracleReduction.perfectCompleteness, OracleReduction.toReduction,
--     OracleVerifier.toVerifier]
--   intro stmt oStmt wit hRelIn
--   unfold Reduction.run
--   sorry

-- theorem oracleReduction_rbr_knowledge_soundness : True := sorry

end OracleReduction

end SendWitness

namespace SendSingleWitness

/-!
  A special case of `SendWitness` oracle reduction where there is only one witness. We implicitly
  convert to `fun _ : Fin 1 => Witness`.
-/

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type) [OracleInterface Witness]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

/-- The `SendSingleWitness` protocol is a single `P_to_V` message, so it has no challenge rounds.
This is what makes its coordinate-wise special soundness reduce to the no-challenge bridge. -/
instance instIsEmptyChallengeIdx : IsEmpty (oraclePSpec Witness).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- The oracle prover for the `SendSingleWitness` oracle reduction.

The prover sends the witness `wit` to the verifier as the only oracle message.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) where
  PrvState := fun _ => (Statement × (∀ i, OStatement i)) × Witness
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ => pure (⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ())

/-- The oracle verifier for the `SendSingleWitness` oracle reduction.

The verifier receives the input statement `stmt` and returns it, and also specifying the oracle
message as the output oracle statement.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness))
    (oraclePSpec Witness) where
  verify := fun stmt _ => pure stmt
  embed := .sumMap (.refl _)
    <| Equiv.toEmbedding
    <|.symm (subtypeUnivEquiv (by aesop))
  hEq := by
    intro i; rcases i with j | j
    · rfl
    · fin_cases j; rfl

@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) where
  prover := oracleProver oSpec Statement OStatement Witness
  verifier := oracleVerifier oSpec Statement OStatement Witness

variable {Statement} {OStatement} {Witness}

omit [(i : ιₛ) → OracleInterface (OStatement i)] [OracleInterface Witness] in
theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : Witness} :
    (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
      pure (fun i => by aesop, ⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ()) := by
  simp only [oraclePSpec, Fin.vcons_fin_zero, Nat.reduceAdd, ChallengeIdx, Challenge,
    Fin.isValue, id_eq]
  change (pure _ : OracleComp _ _) = pure _
  congr 1; dsimp; congr 1; funext i; fin_cases i; rfl

theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (oraclePSpec Witness).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, Sum.rec oStmt (fun i => match i with | 0 => tr 0)⟩ := by
  -- The oracle verifier's `verify` is `pure stmt`, so after `simulateQ_pure` reduces the simulated
  -- pure and `pure_bind` collapses the bind, `toVerifier.run` is `pure` of the pair
  -- `⟨stmt, oStmtOut⟩`, where `oStmtOut` reads the output oracle statements off `embed`. It remains
  -- to identify `oStmtOut` with the explicit `Sum.rec` form, which we do coordinate-by-coordinate.
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  rw [show simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
        (pure stmt : OptionT (OracleComp _) Statement)
      = (pure stmt : OptionT (OracleComp oSpec) Statement) from rfl, pure_bind]
  congr 1
  congr 1
  funext idx
  rcases idx with j | j
  · rfl
  · fin_cases j; rfl

/-- The `SendSingleWitness` oracle verifier is pure: its underlying (non-oracle) verifier
deterministically returns the statement together with the output oracle statements read off the
transcript. This discharges the deterministic-left hypothesis of the CWSS binary append. -/
instance instIsPure :
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.IsPure :=
  ⟨fun p tr => ⟨p.1, Sum.rec p.2 (fun i => match i with | 0 => tr 0)⟩,
   fun ⟨_, _⟩ _ => oracleVerifier_toVerifier_run (oSpec := oSpec)⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (oRelIn : Set ((Statement × (∀ i, OStatement i)) × Witness))

@[reducible, simp]
def toORelOut :
    Set ((Statement × (∀ i, (Sum.elim OStatement fun _ : Fin 1 => Witness) i)) × Unit) :=
  setOf (fun ⟨⟨stmt, oStmtAndWit⟩, _⟩ =>
    oRelIn ⟨⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩, (oStmtAndWit (Sum.inr 0))⟩)

/-- The `SendSingleWitness` oracle reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness (h : NeverFail init) :
    (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness init impl oRelIn
    (toORelOut oRelIn) := by
  sorry
  -- TODO: clean up this proof
  -- simp only [OracleReduction.perfectCompleteness, oraclePSpec, toORelOut, Fin.isValue,
  --   OracleReduction.toReduction, MessageIdx, Reduction.perfectCompleteness_eq_prob_one,
  --   ChallengeIdx, StateT.run'_eq, Set.mem_setOf_eq, probEvent_eq_one_iff,
  --   probFailure_eq_zero_iff, neverFails_bind_iff, neverFails_map_iff, support_bind,
  --   support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right,
  --   exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq]
  -- simp_rw [h, Reduction.run, oracleReduction, oracleVerifier_toVerifier_run, oracleProver_run]
  -- simp only [ChallengeIdx, oraclePSpec, id_eq, liftM_eq_liftComp,
  --   liftComp_pure, bind_pure_comp, map_pure, simulateQ_pure, StateT.run_pure,
  --   neverFails_pure, implies_true, and_self, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
  --   and_true, Fin.isValue, and_imp, forall_const, true_and]
  -- aesop

/-- **Coordinate-wise special soundness of `SendSingleWitness`.** The oracle verifier has no
challenge rounds, so CWSS collapses (via the oracle no-challenge bridge
`coordinateWiseSpecialSound_of_isEmpty_challengeIdx`) to a transcript-level extraction obligation on
the combined statement `Statement × (∀ i, OStatement i)`. The extractor is `e := fun _ tr => tr 0`:
the extracted witness *is* the single oracle message. Since the verifier is pure with output
`⟨stmt, oStmtOut⟩` (where `oStmtOut` exposes the old oracle statements together with the message),
acceptance into `(toORelOut oRelIn).language` unfolds to exactly `⟨⟨stmt, oStmt⟩, tr 0⟩ ∈ oRelIn`.
Holds for *any* coordinate-wise structure `D`. -/
theorem oracleVerifier_coordinateWiseSpecialSound (D : CWSSStructure (oraclePSpec Witness)) :
    (oracleVerifier oSpec Statement OStatement Witness).coordinateWiseSpecialSound init impl D
      oRelIn (toORelOut oRelIn) := by
  refine OracleVerifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx init impl D
    (oracleVerifier oSpec Statement OStatement Witness) oRelIn (toORelOut oRelIn)
    (fun _ tr => tr 0) ?_
  rintro ⟨stmt, oStmt⟩ tr hAcc
  have hmem := Verifier.mem_of_pure_accepting init impl
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier ⟨stmt, oStmt⟩ tr
    (toORelOut oRelIn).language _ (oracleVerifier_toVerifier_run (oSpec := oSpec)) hAcc
  obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
  exact hu

end SendSingleWitness
