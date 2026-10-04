/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationLegacySecurity
public import ArkLib.Interaction.Oracle.FiatShamir.LegacyQueryBound
public import ArkLib.OracleReduction.FiatShamir.Legacy.SingleSalt

/-!
# Canonical Fiat–Shamir knowledge soundness from native certificates

The finite public-coin fragment is transported to the canonical legacy compiler. Its
state-restoration premise is proved from native local knowledge bounds, then the canonical
single-salt theorem supplies a single extractor for every hash-query budget. The prover can
make adaptive random-oracle queries and draw private uniform coins.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec Interaction.Oracle Interaction.TwoParty
open Interaction.Oracle.TypeTree
open scoped ProbabilityTheory

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

universe w

@[instance_reducible] private noncomputable def legacyChallengeCompatible (rounds : List Round) :
    ∀ i : (legacySpec rounds).ChallengeIdx, VCVCompatible ((legacySpec rounds).Challenge i) := by
  classical
  intro i
  letI := legacyChallengeSampleable rounds i
  letI : Fintype ((legacySpec rounds).Challenge i) := Fintype.ofFinite _
  letI : Inhabited ((legacySpec rounds).Challenge i) :=
    Classical.inhabited_of_nonempty inferInstance
  exact {}

/-- Native all-prefix knowledge certificates imply canonical single-salt Fiat–Shamir
knowledge soundness. One named backward extractor works for every structural query budget.
The verifier observes the unsalted statement; the certificate may depend on the public salt.
The bound charges all hash calls in the adversary budget and no private-coin calls. -/
theorem singleSalt_knowledgeSoundness_of_nativeCertificate
    {Statement Salt WitIn Output : Type} [Finite Statement] [VCVCompatible Salt]
    (rounds : List Round)
    (state : (Statement × Salt) → KnowledgeState.{w})
    (extractor : (z : Statement × Salt) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Statement × Salt) → (path : (protocol rounds).tree.ExecutionPath) →
      Unit → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Statement × Salt) → (state z).Witness → WitIn)
    (observe : Statement → (protocol rounds).tree.ExecutionPath → Option Output)
    (relIn : Set (Statement × WitIn)) (langOut : Set Output)
    (errors : RoundErrors rounds)
    (preserving : ∀ z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z, RoundExtractor.IsLocallyBounded (extractor z)
      (protocol rounds).roles (roundErrorSchedule rounds errors))
    (inputLaw : ∀ z witness, (state z).holds witness ↔
      legacyInputRelation state witnessMap (relInSalted relIn) z witness)
    (outputLaw : ∀ z path witness,
      legacyOutputRelation (fun z path => observe z.1 path)
        (unitOutputRelation langOut) z path witness →
        ((extractor z).terminalState path).holds (seed z path witness)) :
    letI := legacyChallengeSampleable rounds
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins
      (nativeFiniteLegacyInit (Input := Statement × Salt) (Salt := PUnit) rounds
        (legacySpec rounds) (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
      ((emptyLegacyImpl (Input := Statement × Salt) rounds).addLift
        (srChallengeQueryImpl' (Statement := Statement × Salt) (pSpec := legacySpec rounds)))
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (Verifier.singleSaltFiatShamir (Salt := Salt)
        (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
          (legacyToRestorationPath rounds) observe))
      relIn langOut
      (fun Q prover => prover.IsQueryBoundP (fun query => query.isLeft) Q)
      (fun Q => Q * Finset.univ.sup errors + ∑ i, errors i) := by
  classical
  let _ := legacyChallengeSampleable rounds
  let _ := legacyChallengeCompatible rounds
  apply single_salt_fiat_shamir_knowledge_soundness
    unifSpec (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
    unifSpec (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
    (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
      (legacyToRestorationPath rounds) observe)
    relIn langOut
    (nativeFiniteLegacyInit (Input := Statement × Salt) (Salt := PUnit) rounds
        (legacySpec rounds) (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
    (emptyLegacyImpl (Input := Statement × Salt) rounds)
    (fun Q prover => prover.IsQueryBoundP (fun query => query.isLeft) Q)
    (fun Q prover => prover.IsQueryBoundP (fun query => query.isLeft) Q)
    (fun Q prover h => by simpa only [srInducedProverKS_eq_map, isQueryBoundP_map_iff] using h)
    (fun Q => Q * Finset.univ.sup errors + ∑ i, errors i)
  refine ⟨nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
    (legacyToRestorationPath rounds) state extractor seed witnessMap, ?_⟩
  intro Q prover hQ
  have h := coinKSExperimentProb_nativeCertificate_bound rounds errors prover
    state extractor preserving bounded seed witnessMap (fun z path => observe z.1 path)
    (relInSalted relIn) (unitOutputRelation langOut) inputLaw outputLaw
  change Verifier.StateRestoration.coinKSExperimentProb _ _ _ _ _ _
    (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
      (legacyToRestorationPath rounds) (fun z path => observe z.1 path)) prover ≤ _
  calc
    _ ≤ Finset.univ.sup errors * expectedAdversaryFreshKeys rounds
          (simulateLegacyProver rounds prover) + ∑ i, errors i := h
    _ ≤ Finset.univ.sup errors * Q + ∑ i, errors i := by
      gcongr
      exact simulateLegacyProver_expectedKeys_le rounds prover Q hQ
    _ = _ := by rw [mul_comm]

end Interaction.Oracle.FiatShamir
