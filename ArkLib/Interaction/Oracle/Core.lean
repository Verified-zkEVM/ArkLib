/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.Oracle.Spec
import PolyFun.Interaction.TwoParty.Refine

open Interaction.TwoParty

/-!
# Oracle.Spec Prover, Verifier, and Reduction

This module contains the forward oracle API built on `Interaction.Oracle.Spec`.
-/

universe u v w

open OracleComp OracleSpec

namespace Interaction

/-- Oracle-statement data for an indexed oracle-statement family. -/
abbrev OracleStatement {ιₛ : Type v} (OStmt : ιₛ → Type w) :=
  ∀ i, OStmt i

namespace OracleStatement

/-- A concrete oracle statement realizes a deterministic query implementation
when every query receives exactly the answer specified by that statement. -/
def Realizes
    {ιₛ : Type v} {OStatement : ιₛ → Type w}
    [∀ i, OracleInterface (OStatement i)]
    (impl : QueryImpl [OStatement]ₒ Id)
    (oStatement : OracleStatement OStatement) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatement i)),
    impl ⟨i, q⟩ = OracleInterface.answer (oStatement i) q

@[simp]
theorem realizes_simOracle0
    {ιₛ : Type v} {OStatement : ιₛ → Type w}
    [∀ i, OracleInterface (OStatement i)]
    (oStatement : OracleStatement OStatement) :
    Realizes (OracleInterface.simOracle0 OStatement oStatement) oStatement := by
  intro i q
  rfl

end OracleStatement

/-- A local statement bundled with oracle-statement data for a fixed ambient
input `i`. Used for both oracle inputs and oracle outputs. -/
structure StatementWithOracles
    {Input : Type u}
    (LocalStmt : Input → Type v) {ιₛ : Input → Type v}
    (OStmt : (i : Input) → ιₛ i → Type w)
    (i : Input) where
  stmt : LocalStmt i
  oracleStmt : OracleStatement (OStmt i)
/-! ## Oracle.Spec-based prover, verifier, and reduction

These definitions use `Oracle.Spec` (the inductive type with `.public`/`.oracle`).
Output types and `simulate` are indexed by `Oracle.Spec.PublicTranscript`,
giving definitional independence from oracle message values. Everything is
indexed by a `SharedIn` ambient input that determines the protocol context,
roles, oracle decoration, and statement/witness families. -/

namespace Oracle

namespace Prover

/-- Oracle prover on `Oracle.Spec` with explicit setup and prover-side node
effects.

The setup monad produces the focal `StrategyOver` induced by
`focalMonadicSyntax`. The oracle spec supplies the control
tree and roles, while `ProverMd` supplies the node effect used by the prover at
each runtime node. The ordinary `Oracle.Prover` below specializes setup and all
prover nodes to `OracleComp oSpec`. -/
abbrev WithMonads (Setup : Type → Type)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (ProverMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec)
    (StatementIn WitnessIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) :=
  (shared : SharedIn) →
    StatementWithOracles StatementIn OStatementIn shared →
      WitnessIn shared →
        Setup (Interaction.Spec.StrategyOver
          focalMonadicSyntax
          PUnit.unit
          (Context shared).toInteractionSpec
          (RoleDecoration.withMonads
            ((Context shared).toSpecRoles (Roles shared))
            (ProverMd shared))
          (fun tr =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => StatementOut shared ((Context shared).projectPublic tr))
                (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
                shared)
              (WitnessOut shared ((Context shared).projectPublic tr))))

end Prover

/-- Oracle prover on `Oracle.Spec`: given ambient input `shared`, local
statement/oracle data and witness, performs monadic setup in `OracleComp oSpec`
and produces a role-dependent strategy on `(Context shared).toInteractionSpec`.
The honest prover output is the next local statement bundled with its output
oracle statements, plus the next witness. -/
abbrev Prover {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (StatementIn WitnessIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) :=
  Prover.WithMonads (OracleComp oSpec) SharedIn Context Roles
    (fun shared => (Context shared).toProverMonadDecoration oSpec)
    StatementIn WitnessIn OStatementIn StatementOut OStatementOut WitnessOut

namespace Verifier

/-- Oracle verifier on `Oracle.Spec` with an explicit verifier-side monad
decoration.

This is the lower-level ambient-effect surface: callers choose the monad
decoration used by the verifier counterpart. The ordinary `Oracle.Verifier`
below specializes this by using `Spec.toMonadDecoration`, whose receiver nodes
can query ambient oracles, input oracle statements, and accumulated prover
oracle messages.

The `simulate` field remains oracle-specific: it provides query-level access to
output oracle statements, indexed by `PublicTranscript` so it is definitionally
independent of oracle message values. -/
structure WithMonads {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (VerifierMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec)
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] where
  toFun : (shared : SharedIn) →
    StatementIn shared →
      Interaction.Spec.StrategyOver
        counterpartMonadicSyntax
        PUnit.unit
        (Context shared).toInteractionSpec
        (RoleDecoration.withMonads
          ((Context shared).toSpecRoles (Roles shared))
          (VerifierMd shared))
        (fun tr => StatementOut shared ((Context shared).projectPublic tr))
  simulate : (shared : SharedIn) →
    (pt : Spec.PublicTranscript (Context shared)) →
    QueryImpl [OStatementOut shared pt]ₒ
      (OracleComp
        ([OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt))

end Verifier

/-- Oracle verifier on `Oracle.Spec`: the interactive verifier (`toFun`) and
output-oracle simulation (`simulate`), both on the same `Oracle.Spec`.

The verifier uses the counterpart `StrategyOver` induced by
`counterpartMonadicSyntax` with `toMonadDecoration`, giving
`Id` monad at sender/oracle nodes and `OracleComp` at receiver nodes. The
accumulated oracle spec starts at `[]ₒ` and grows as `.oracle` nodes are
traversed, so the verifier's oracle access is fully determined by the protocol
structure.

The `simulate` field provides query-level access to output oracle statements,
indexed by `PublicTranscript` (so it is definitionally independent of oracle
message values). -/
abbrev Verifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] :=
  Verifier.WithMonads oSpec SharedIn Context Roles OracleDeco
    (fun shared => (Context shared).toMonadDecoration oSpec (OStatementIn shared)
      (Roles shared) (OracleDeco shared) []ₒ)
    StatementIn OStatementIn StatementOut OStatementOut

/-- Oracle reduction on `Oracle.Spec` with explicit prover and verifier ambient
effect layers.

This is the fully general reduction layer: the prover has a setup monad and a
nodewise monad decoration, while the verifier has its own nodewise monad
decoration. The oracle-specific part that remains is `simulate`, because output
oracle statements must still be queryable by the verifier/security layer. -/
structure Reduction.WithMonads {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (Setup : Type → Type)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (ProverMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec)
    (VerifierMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec)
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) where
  prover : Prover.WithMonads Setup SharedIn Context Roles ProverMd StatementIn WitnessIn
    OStatementIn StatementOut OStatementOut WitnessOut
  verifier : Verifier.WithMonads oSpec SharedIn Context Roles OracleDeco VerifierMd
    StatementIn OStatementIn StatementOut OStatementOut

/-- Oracle reduction on `Oracle.Spec`: bundles a prover and a verifier for the
same protocol. The prover produces strategies on `(Context shared).toInteractionSpec`
while the verifier interacts as a counterpart strategy with growing oracle access.

All output types are indexed by `PublicTranscript`, ensuring they do not
depend on oracle message values. -/
abbrev Reduction {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) :=
  Reduction.WithMonads oSpec (OracleComp oSpec) SharedIn Context Roles OracleDeco
    (fun shared => (Context shared).toProverMonadDecoration oSpec)
    (fun shared => (Context shared).toMonadDecoration oSpec (OStatementIn shared)
      (Roles shared) (OracleDeco shared) []ₒ)
    StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut

/-- Forget the prover and witness of an `Oracle.Reduction`, keeping the
verifier. -/
def Reduction.toVerifier
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (r : Reduction oSpec SharedIn Context Roles OracleDeco StatementIn OStatementIn
      WitnessIn StatementOut OStatementOut WitnessOut) :
    Verifier oSpec SharedIn Context Roles OracleDeco StatementIn OStatementIn
      StatementOut OStatementOut :=
  r.verifier

end Oracle

end Interaction

