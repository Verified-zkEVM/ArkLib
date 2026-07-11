/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Continuation

namespace Interaction

open TwoParty

namespace OracleDecoration

/-- Build the verifier-side counterpart for an oracle state chain while
threading the accumulated sender-message oracle spec stage by stage. -/
private def stateChainVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Stage : Nat → Type} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s))
    {VerifierState : (i : Nat) → Stage i → Type}
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    (verifierStep : {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      (i : Nat) → (st : Stage i) → VerifierState i st →
      Spec.Counterpart.withMonads (spec i st) (roles i st)
        (toMonadDecoration oSpec OStmtIn (spec i st) (roles i st) (od i st) accSpec)
        (fun tr => VerifierState (i + 1) (advance i st tr))) :
    (n : Nat) → (i : Nat) → (st : Stage i) → VerifierState i st →
    Spec.Counterpart.withMonads (Spec.stateChain Stage spec advance n i st)
      (Spec.Decoration.stateChain roles n i st)
      (toMonadDecoration oSpec OStmtIn (Spec.stateChain Stage spec advance n i st)
        (Spec.Decoration.stateChain roles n i st) (Role.Refine.stateChain od n i st) accSpec)
      (PFunctor.FreeM.Path.stateChainFamily VerifierState n i st)
  | 0, _, _, b => b
  | n + 1, i, st, b => by
      simpa [Spec.stateChain_succ, Spec.Decoration.stateChain,
          Role.Refine.stateChain, PFunctor.FreeM.Path.stateChainFamily,
          toMonadDecoration_append]
        using
          (Spec.Counterpart.withMonads.append
            (verifierStep accSpec i st b)
            (fun tr b' =>
              stateChainVerifier od
                ((accSpecAfter (spec i st) (roles i st) (od i st) accSpec tr).2)
                verifierStep n (i + 1) (advance i st tr) b'))

/-- Concrete-input specialization of state-chain composition for oracle
reductions. The canonical ambient-spine version is defined below. -/
private def stateChainCompConcrete {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : StatementIn → Type}
    {Stage : Nat → Type}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    {ιₛₒ : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) → Type}
    {OStmtOut :
      (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (proverInit :
      (s : StatementIn) →
      StatementWithOracles (fun _ => PUnit) OStmtIn s →
      WitnessIn s →
      OracleComp oSpec (ProverState 0 (initStage s)))
    (proverStep : (i : Nat) → (st : Stage i) → ProverState i st →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (spec i st) (roles i st)
        (fun tr => ProverState (i + 1) (advance i st tr))))
    (stmtResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      PFunctor.FreeM.Path.stateChainFamily VerifierState n 0 (initStage s) tr)
    (proverOStmtResult :
      (s : StatementIn) →
      StatementWithOracles (fun _ => PUnit) OStmtIn s →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      OracleStatement (OStmtOut s tr))
    (verifierInit : (s : StatementIn) → VerifierState 0 (initStage s))
    (verifierStep : (s : StatementIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      (i : Nat) → (st : Stage i) → VerifierState i st →
      Spec.Counterpart.withMonads (spec i st) (roles i st)
        (toMonadDecoration oSpec (OStmtIn s) (spec i st) (roles i st) (od i st) accSpec)
        (fun tr => VerifierState (i + 1) (advance i st tr)))
    (simulateResult : (s : StatementIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage s))) →
      QueryImpl [OStmtOut s tr]ₒ
        (OracleComp ([OStmtIn s]ₒ + toOracleSpec
          (Spec.stateChain Stage spec advance n 0 (initStage s))
          (Spec.Decoration.stateChain roles n 0 (initStage s))
          (Role.Refine.stateChain (fun i st => od i st) n 0 (initStage s)) tr))) :
    OracleReduction oSpec StatementIn
      (fun s => Spec.stateChain Stage spec advance n 0 (initStage s))
      (fun s => Spec.Decoration.stateChain roles n 0 (initStage s))
      (fun s => Role.Refine.stateChain (fun i st => od i st) n 0 (initStage s))
      (fun _ => PUnit)
      OStmtIn
      WitnessIn
      (fun s => PFunctor.FreeM.Path.stateChainFamily VerifierState n 0 (initStage s))
      OStmtOut
      (fun s => PFunctor.FreeM.Path.stateChainFamily ProverState n 0 (initStage s)) where
  prover s sWithOracles w := do
    let a ← proverInit s sWithOracles w
    let strat ← Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage s) a
    pure <| by
      simpa [Spec.stateChain, Spec.Decoration.stateChain,
        PFunctor.FreeM.Path.stateChainFamily] using
        (Spec.Strategy.mapOutputWithRoles
          (fun tr pOut => ⟨⟨stmtResult s tr, proverOStmtResult s sWithOracles tr⟩, pOut⟩)
          strat)
  verifier s {_} accSpec _ :=
    stateChainVerifier od accSpec (verifierStep s) n 0 (initStage s) (verifierInit s)
  simulate := simulateResult

/-- N-ary state chain composition of oracle continuations. The shared input
determines the full chained protocol, while the continuation-local statement and
witness are only used to initialize and interpret the carried prover/verifier
state. Each stage's verifier sees oracle access from `oSpec + [OStatementIn]ₒ` plus
the accumulated sender-message spec. -/
def OracleReduction.stateChainComp {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {Stage : Nat → Type}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s)}
    {ProverState VerifierState : (shared : SharedIn) → (i : Nat) → Stage i → Type}
    (n : Nat)
    (initStage : SharedIn → Stage 0)
    {ιₛₒ : (shared : SharedIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage shared))) → Type}
    {OStatementOut :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage shared))) →
      ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (proverInit :
      (shared : SharedIn) →
      StatementWithOracles StatementIn OStatementIn shared →
      WitnessIn shared →
      OracleComp oSpec (ProverState shared 0 (initStage shared)))
    (proverStep : (shared : SharedIn) → (i : Nat) → (st : Stage i) →
      ProverState shared i st →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (spec i st) (roles i st)
        (fun tr => ProverState shared (i + 1) (advance i st tr))))
    (stmtResult : (shared : SharedIn) → (stmt : StatementIn shared) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage shared))) →
      PFunctor.FreeM.Path.stateChainFamily (fun i st => VerifierState shared i st)
        n 0 (initStage shared) tr)
    (proverOStatementResult :
      (shared : SharedIn) →
      (s : StatementWithOracles StatementIn OStatementIn shared) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage shared))) →
      OracleStatement (OStatementOut shared tr))
    (verifierInit : (shared : SharedIn) → StatementIn shared →
      VerifierState shared 0 (initStage shared))
    (verifierStep : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
        (i : Nat) → (st : Stage i) → VerifierState shared i st →
      Spec.Counterpart.withMonads (spec i st) (roles i st)
        (toMonadDecoration oSpec
          (OStatementIn shared) (spec i st) (roles i st) (od i st) accSpec)
        (fun tr => VerifierState shared (i + 1) (advance i st tr)))
    (simulateResult : (shared : SharedIn) →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage shared))) →
      QueryImpl [OStatementOut shared tr]ₒ
        (OracleComp ([OStatementIn shared]ₒ + toOracleSpec
          (Spec.stateChain Stage spec advance n 0 (initStage shared))
          (Spec.Decoration.stateChain roles n 0 (initStage shared))
          (Role.Refine.stateChain (fun i st => od i st) n 0 (initStage shared)) tr))) :
    OracleReduction oSpec SharedIn
      (fun shared => Spec.stateChain Stage spec advance n 0 (initStage shared))
      (fun shared => Spec.Decoration.stateChain roles n 0 (initStage shared))
      (fun shared => Role.Refine.stateChain (fun i st => od i st) n 0 (initStage shared))
      StatementIn OStatementIn WitnessIn
      (fun shared tr =>
        PFunctor.FreeM.Path.stateChainFamily (fun i st => VerifierState shared i st)
          n 0 (initStage shared) tr)
      OStatementOut
      (fun shared tr =>
        PFunctor.FreeM.Path.stateChainFamily (fun i st => ProverState shared i st)
          n 0 (initStage shared) tr) where
  prover shared sWithOracles w := do
    let a ← proverInit shared sWithOracles w
    let strat ← Spec.Strategy.stateChainCompWithRoles
      (proverStep shared) n 0 (initStage shared) a
    pure <| by
      simpa [Spec.stateChain, Spec.Decoration.stateChain,
        PFunctor.FreeM.Path.stateChainFamily] using
        (Spec.Strategy.mapOutputWithRoles
          (fun tr pOut =>
            ⟨⟨stmtResult shared sWithOracles.stmt tr,
                proverOStatementResult shared sWithOracles tr⟩, pOut⟩)
          strat)
  verifier shared {_} accSpec stmt :=
    stateChainVerifier od accSpec (verifierStep shared) n 0 (initStage shared)
      (verifierInit shared stmt)
  simulate shared tr :=
    simulateResult shared tr

end OracleDecoration

end Interaction
