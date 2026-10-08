/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Alexander Hicks, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.StateRestoration
public import ArkLib.OracleReduction.FiatShamir.Legacy.QueryLog

/-!
# Logged knowledge-security experiments for the legacy Fiat–Shamir bridge

Narrow adaptation of ArkLib PR #848, commit
`1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb`. Prover-private randomness is separated
from the random oracle. Extraction continues in the same oracle state and receives both logs.
One extractor is chosen before the budget family. These are semantic security definitions,
with no running-time or deterministic prover-log-only extraction claim.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

noncomputable section

/-- Run a non-interactive verifier and record its base-oracle queries, including on rejection. -/
abbrev runVerifierWithLog {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn Proof StmtOut : Type}
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (x : StmtIn) (π : Proof) : OracleComp oSpec (Option StmtOut × QueryLog oSpec) :=
  withQueryLog (verifier.verify x (Fin.cons π (fun i => i.elim0))).run


/-- **CO25 Def 3.6 extraction-failure event** on the NARG-KS experiment output
`StmtIn × Option WitIn × Option StmtOut`: the verifier accepted into `langOut` yet the extracted
input witness misses `relIn` (or none was produced). No output witness is supplied by the malicious
NARG prover: Definition 3.6 quantifies over the same proof-only `(x, π)` adversaries as Definition
3.5. -/
def nargKSFailEvent {StmtIn WitIn StmtOut : Type}
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut) :
    StmtIn × Option WitIn × Option StmtOut → Prop
  | (x, some witIn, some stmtOut) => stmtOut ∈ langOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut) => stmtOut ∈ langOut
  | _ => False

/-- Extraction-failure event for ArkLib's relation-valued reduction and state-restoration
interfaces. Unlike the paper's NARG event, these interfaces genuinely carry an output witness. -/
def relationKSFailEvent {StmtIn WitIn StmtOut WitOut : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) :
    StmtIn × Option WitIn × Option StmtOut × WitOut → Prop
  | (x, some witIn, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut
  | _ => False


/-- Knowledge-soundness experiment with prover-private coins.
The prover and verifier run first; extraction
then continues in their final oracle state. Extractor helper queries use `auxImplE`, while its
base queries use the same `impl` as the prover and verifier. Prover private-coin queries are
excluded from the supplied log. The extractor may inspect fresh base-oracle answers correlated
with the preceding execution. -/
def adaptiveNARGKnowledgeSoundnessExpWithCoins
    {ι κ κE : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp)
    (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + auxSpecE)) WitIn)
    (P : OracleComp (oSpec + auxSpec) (StmtIn × Proof)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut) := do
  StateT.run' (do
    let ⟨x, π, tr, stmtOut?, tr_V⟩ ←
      simulateQ (impl.addLift auxImpl) (do
        let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
        let ⟨stmtOut?, tr_V⟩ ←
          liftComp (runVerifierWithLog verifier x π) (oSpec + auxSpec)
        pure (x, π, tr, stmtOut?, tr_V))
    let witIn? ← simulateQ (impl.addLift auxImplE) (extractor x π tr.fst tr_V).run
    pure (x, witIn?, stmtOut?)) (← init)

/-- A base-only extractor can be executed inside the original prover/verifier interpreter.
No purity assumption is needed: its fresh queries use the continuing shared state. -/
theorem adaptiveNARGKnowledgeSoundnessExpWithCoins_base
    {ι κ κE : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp) (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp oSpec) WitIn)
    (P : OracleComp (oSpec + auxSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExpWithCoins init impl auxImpl auxImplE
      verifier (fun x π tr tr_V => OptionT.mk (liftComp (extractor x π tr tr_V).run
        (oSpec + auxSpecE))) P =
    (do StateT.run' (simulateQ (impl.addLift auxImpl) (do
      let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
      let ⟨stmtOut?, tr_V⟩ ← liftComp (runVerifierWithLog verifier x π) (oSpec + auxSpec)
      let w ← liftComp (extractor x π tr.fst tr_V).run (oSpec + auxSpec)
      pure (x, w, stmtOut?))) (← init)) := by
  unfold adaptiveNARGKnowledgeSoundnessExpWithCoins
  simp only [OptionT.run_mk, simulateQ_bind, simulateQ_pure,
    QueryImpl.addLift, QueryImpl.simulateQ_add_liftComp_left, bind_assoc, pure_bind]

/-- Fixed-extractor knowledge soundness with shared base-oracle access during extraction.
The extractor is supplied before the prover bound and error, and its helper oracle does not
expose the prover's private-coin interface. -/
def Verifier.adaptiveNARGKnowledgeSoundnessWithCoinsWithExtractor
    {ι κ κE : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp) (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + auxSpecE)) WitIn)
    (bound : OracleComp (oSpec + auxSpec) (StmtIn × Proof) → Prop)
    (error : ENNReal) : Prop :=
  ∀ P, bound P →
    Pr{let result ← adaptiveNARGKnowledgeSoundnessExpWithCoins
        init impl auxImpl auxImplE verifier extractor P}[
      nargKSFailEvent relIn langOut result] ≤ error



/-- One extractor for every budget against provers with private coins. This is the
uniform existential closure of the fixed-extractor predicate, with extraction continuing
in the prover/verifier's final oracle state. -/
def Verifier.adaptiveNARGKnowledgeSoundnessWithCoins
    {ι κ κE B : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ}
    {auxSpecE : OracleSpec κE} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp) (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (bound : B → OracleComp (oSpec + auxSpec) (StmtIn × Proof) → Prop)
    (error : B → ENNReal) : Prop :=
  ∃ extractor, ∀ b, Verifier.adaptiveNARGKnowledgeSoundnessWithCoinsWithExtractor
    init impl auxImpl auxImplE verifier relIn langOut extractor (bound b) (error b)


namespace Prover.StateRestoration

/-- A restoration prover with a separate private-randomness oracle. -/
abbrev KnowledgeSoundnessWithCoins {ι κ : Type} (oSpec : OracleSpec ι)
    (StmtIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) (auxSpec : OracleSpec κ) :=
  OracleComp ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec)
    (StmtIn × pSpec.Messages × WitOut)

end Prover.StateRestoration

namespace Verifier.StateRestoration

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
  (impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))

/-- Coin-bearing SR knowledge-soundness experiment for a *fixed* extractor and coin-bearing prover.
The prover uses `(oSpec + chal) + auxSpec` (coins answered by `auxImpl`,
appended to the standard SR handler); the verifier lives over **base** `oSpec` (it makes no coin
queries) and is `liftComp`-ed into the game spec.

The experiment logs the prover's run and the verifier's run, and hands the *trace-based*
extractor (CO25 Def 3.14) the full transcript, the `oSpec + chal` projection of the prover's log
(the state-restoration move-response trace — the prover's private-coin queries are excluded),
and the verifier's `oSpec`-query log. -/
def coinKSExperimentProb {κ : Type} {auxSpec : OracleSpec κ}
    (auxImpl : QueryImpl auxSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec
      auxSpec) : ENNReal :=
  Pr{let result ← do (simulateQ (((impl.addLift srChallengeQueryImpl' :
              QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
                (StateT
                  (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)).addLift auxImpl) :
            QueryImpl _ (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)) <| (do
          let ⟨⟨stmtIn, messages, witOut⟩, tr⟩ ← (simulateQ loggingOracle srProver).run
          let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
            ((oSpec + fsChallengeOracle StmtIn pSpec) + auxSpec)
          let ⟨stmtOut, tr_V⟩ ←
            liftComp (simulateQ loggingOracle (verifier.run stmtIn transcript).run).run _
          let witIn? ← liftComp (srExtractor stmtIn witOut transcript tr.fst tr_V).run _
          return (stmtIn, witIn?,
            stmtOut, witOut))).run' (← init)}[relationKSFailEvent relIn relOut result]

/-- State-restoration KS for one supplied extractor. Quantify this extractor before a
budget family to express uniform security; the underlying experiment is unchanged. -/
def knowledgeSoundnessWithCoinsWithExtractor {κ : Type} (auxSpec : OracleSpec κ)
    (auxImpl : QueryImpl auxSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (bound : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec
      auxSpec → Prop)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec
      auxSpec,
    bound srProver →
    coinKSExperimentProb (init := init) (impl := impl) auxImpl srExtractor relIn relOut verifier
      srProver ≤ srKnowledgeSoundnessError

/-- One SR extractor for an entire bound/error family, chosen before its budget index. -/
def knowledgeSoundnessWithCoins {κ B : Type} (auxSpec : OracleSpec κ)
    (auxImpl : QueryImpl auxSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (bound : B → Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut
      pSpec auxSpec → Prop)
    (error : B → ENNReal) : Prop :=
  ∃ extractor, ∀ b, knowledgeSoundnessWithCoinsWithExtractor init impl auxSpec auxImpl
    relIn relOut verifier extractor (bound b) (error b)

end Verifier.StateRestoration
