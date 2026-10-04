/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedFinite
public import ArkLib.OracleReduction.FiatShamir.Legacy.KnowledgeGames

/-!
# Native certificate data for the canonical legacy SR knowledge game

The legacy game uses a fixed input-witness carrier and expects an extractor that receives the
entire transcript and two ordered logs. A native backward extractor instead returns a witness in
the selected input's knowledge state. The pure adapter below transports that named result through
an explicit witness map. It consumes no further oracle answers and ignores the two logs; the
event lemma identifies its failure with the native relation event pointwise. The full game
correspondence additionally needs the finite key and transcript conversions.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W WitIn StmtOut : Type} {rounds : List Round}

/-- Initialize the legacy eager challenge oracle by uniformly sampling one finite native table
and transporting its cells to the legacy dependent query interface. The transport itself is
supplied by the proved key/fibre equivalence of the common fragment. -/
noncomputable def nativeFiniteLegacyInit (rounds : List Round)
    [Finite Input] [Finite Salt]
    {n : ℕ} (pSpec : ProtocolSpec n)
    (tableToImpl : Table Input Salt rounds →
      QueryImpl (srChallengeOracle Input pSpec) Id) :
    ProbComp (QueryImpl (srChallengeOracle Input pSpec) Id) :=
  letI := finiteTableSampler (Input := Input) (Salt := Salt) rounds
  tableToImpl <$> ($ᵗ (Table Input Salt rounds))

/-- A pure legacy verifier whose accepted output is computed from the concrete native path. -/
def nativeLegacyVerifier {ι : Type} (oSpec : OracleSpec ι)
    {n : ℕ} (pSpec : ProtocolSpec n)
    (decode : pSpec.FullTranscript → (protocol rounds).tree.ExecutionPath)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut) :
    _root_.Verifier oSpec Input StmtOut pSpec where
  verify := fun z transcript => OptionT.mk (pure (observe z (decode transcript)))

/-- The concrete verifier performs no base-oracle query and returns precisely its observation. -/
theorem nativeLegacyVerifier_run {ι : Type} (oSpec : OracleSpec ι)
    {n : ℕ} (pSpec : ProtocolSpec n)
    (decode : pSpec.FullTranscript → (protocol rounds).tree.ExecutionPath)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (z : Input) (transcript : pSpec.FullTranscript) :
    ((nativeLegacyVerifier oSpec pSpec decode observe).run z transcript).run =
      (pure (observe z (decode transcript)) : OracleComp oSpec (Option StmtOut)) := rfl

/-- The canonical legacy extractor instantiated by the named native backward map. The legacy
input witness type may differ from the native input-dependent witness carrier; `toLegacyWitness`
is the explicit transport. This extractor performs no oracle queries after verification. -/
def nativeBackwardLegacyExtractor {ι : Type} (oSpec : OracleSpec ι)
    {n : ℕ} (pSpec : ProtocolSpec n)
    (decode : pSpec.FullTranscript → (protocol rounds).tree.ExecutionPath)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (toLegacyWitness : (z : Input) → (state z).Witness → WitIn) :
    _root_.Extractor.StateRestoration oSpec Input WitIn W pSpec :=
  fun z witness transcript _ _ =>
    pure (toLegacyWitness z
      ((extractor z).extractWitness (decode transcript)
        (terminalWitness z (decode transcript) witness)))

/-- The canonical legacy extractor returns the named native witness without querying either
the base oracle or the private-coin oracle. Its two logged inputs are retained by the interface. -/
theorem nativeBackwardLegacyExtractor_run {ι : Type} (oSpec : OracleSpec ι)
    {n : ℕ} (pSpec : ProtocolSpec n)
    (decode : pSpec.FullTranscript → (protocol rounds).tree.ExecutionPath)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (toLegacyWitness : (z : Input) → (state z).Witness → WitIn)
    (z : Input) (witness : W) (transcript : pSpec.FullTranscript)
    (sourceLog : QueryLog (oSpec + srChallengeOracle Input pSpec))
    (verifierLog : QueryLog oSpec) :
    ((nativeBackwardLegacyExtractor oSpec pSpec decode state extractor terminalWitness
      toLegacyWitness z witness transcript sourceLog verifierLog).run) =
      (pure (some (toLegacyWitness z
        ((extractor z).extractWitness (decode transcript)
          (terminalWitness z (decode transcript) witness)))) :
          OracleComp oSpec (Option WitIn)) := rfl

/-- The relation on native input witnesses induced by the legacy input relation. -/
def legacyInputRelation
    (state : Input → KnowledgeState.{w})
    (toLegacyWitness : (z : Input) → (state z).Witness → WitIn)
    (relIn : Set (Input × WitIn)) (z : Input) (witness : (state z).Witness) : Prop :=
  (z, toLegacyWitness z witness) ∈ relIn

/-- Accepted native output with a legacy output-relation witness. -/
def legacyOutputRelation
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relOut : Set (StmtOut × W))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) : Prop :=
  ∃ output, observe z path = some output ∧ (output, witness) ∈ relOut

/-- Once the pure verifier and named extractor receive the matching concrete path, the
canonical legacy extraction-failure event is exactly the native relation failure event. -/
theorem legacyFailure_eq_badStoppedRelation
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (toLegacyWitness : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) :
    relationKSFailEvent relIn relOut
      (z,
        some (toLegacyWitness z
          ((extractor z).extractWitness path (terminalWitness z path witness))),
        observe z path, witness) ↔
    badStoppedRelation state extractor
      (legacyInputRelation state toLegacyWitness relIn)
      (legacyOutputRelation observe relOut)
      terminalWitness Set.univ (some (z, path, witness)) := by
  cases houtput : observe z path with
  | none =>
      simp [relationKSFailEvent, badStoppedRelation, legacyOutputRelation, houtput]
  | some output =>
      simp [relationKSFailEvent, badStoppedRelation, legacyInputRelation,
        legacyOutputRelation, houtput]

/-- The native certificate bounds the eager full-table event expressed using the legacy
relations and the pure verifier/extractor observations. This is the security side of the
legacy game correspondence; the oracle and transcript transport is supplied separately. -/
theorem eagerNative_legacyFailure_bound
    (rounds : List Round)
    [DecidableEq Input] [DecidableEq Salt] [Finite Input] [Finite Salt]
    [SampleableType (Table Input Salt rounds)]
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (preserving : ∀ z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (toLegacyWitness : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (inputLaw : ∀ z witness, (state z).holds witness ↔
      legacyInputRelation state toLegacyWitness relIn z witness)
    (outputLaw : ∀ z path witness,
      legacyOutputRelation observe relOut z path witness →
        ((extractor z).terminalState path).holds (terminalWitness z path witness)) :
    Pr{let joint ← (($ᵗ (Table Input Salt rounds)) >>= fun table =>
      fixedTableLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state toLegacyWitness relIn)
        (legacyOutputRelation observe relOut) terminalWitness Set.univ joint.1.1.1] ≤
    Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
      ∑ j, errors j := by
  exact eagerRestored_knowledge_soundness rounds errors adversary state extractor
    Set.univ (by simpa using preserving) (by simpa using bounded)
    (legacyInputRelation state toLegacyWitness relIn)
    (legacyOutputRelation observe relOut) terminalWitness inputLaw outputLaw

end Interaction.Oracle.Security.StateRestoration
