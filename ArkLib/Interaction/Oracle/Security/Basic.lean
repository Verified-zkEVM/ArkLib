/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

/-!
# Basic Oracle Security Interfaces

Behavior-level oracle implementations, output realization, security relations,
and straightline extractors for `Interaction.Oracle`.
-/

noncomputable section

open OracleComp

namespace Interaction
namespace Oracle

/-! ## Oracle behavior types -/

abbrev InputImpl
    {SharedIn : Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (shared : SharedIn) :=
  QueryImpl [OStatementIn shared]ₒ Id

abbrev OutputImpl
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Context shared)) →
      ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (pt : Spec.PublicTranscript (Context shared)) :=
  QueryImpl [OStatementOut shared pt]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ +
        (Context shared).toOracleSpec (OracleDeco shared) pt))

/-- Query-level agreement between an output-oracle behavior and a concrete
output oracle family, relative to a deterministic input-oracle implementation.

Takes the full transcript `tr` (needed to answer oracle queries via
`Spec.answerQuery`) and computes the `PublicTranscript` index for the
output oracle types. -/
def OutputRealizes
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (inputImpl : InputImpl OStatementIn shared)
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (outputImpl :
      OutputImpl (Context := Context) (OracleDeco := OracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared
        ((Context shared).projectPublic tr))
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    Prop :=
  let pt := (Context shared).projectPublic tr
  ∀ i (q : OracleInterface.Query (OStatementOut shared pt i)),
    simulateQ
        (QueryImpl.add inputImpl
          (Spec.answerQuery (Context shared) (OracleDeco shared) tr))
        (outputImpl ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-! ## Reduction relations and extractors -/

namespace Reduction

abbrev InputRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _) :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  WitnessIn shared →
  Prop

abbrev OutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  StatementOut shared pt →
  OutputImpl (Context := Context) (OracleDeco := OracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared pt →
  WitnessOut shared pt →
  Prop

namespace Extractor

/-- A straightline extractor for an oracle reduction. The extractor is a
deterministic function of:

- the shared context `shared` and input statement `stmt`,
- the deterministic input oracle implementation `inputImpl`,
- the **full transcript** `tr` (including the concrete prover oracle message
  values, which are needed to answer queries under `outputImpl` via
  `Spec.answerQuery`),
- the verifier's output statement `stmtOut` (indexed by `projectPublic tr`),
- the verifier's output oracle simulator `outputImpl` (a `QueryImpl` that
  defines the output oracle semantics relative to `inputImpl` and the full
  transcript),
- the adversarial prover's witness output `witOut`.

It reconstructs an input witness. Note that the extractor does *not* receive
concrete output oracle data: the output oracle's semantics are fully captured
by `outputImpl`, which the verifier defines. Access to the full transcript is
what lets the extractor actually evaluate `outputImpl` at any query, since
`outputImpl`'s underlying query spec uses `Spec.answerQuery` on `tr` to respond
to oracle-message queries. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_stmt : StatementIn shared)
      (_inputImpl : InputImpl OStatementIn shared)
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
      (_stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
      OutputImpl (Context := Context) (OracleDeco := OracleDeco)
          OStatementIn OStatementOut shared ((Context shared).projectPublic tr) →
        WitnessOut shared ((Context shared).projectPublic tr) → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _} :
    CoeFun
      (Straightline
        (SharedIn := SharedIn) (Context := Context) (OracleDeco := OracleDeco)
        (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStatementOut := OStatementOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_stmt : StatementIn shared)
        (_inputImpl : InputImpl OStatementIn shared)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
        (_stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
        OutputImpl (Context := Context) (OracleDeco := OracleDeco)
            OStatementIn OStatementOut shared
            ((Context shared).projectPublic tr) →
          WitnessOut shared ((Context shared).projectPublic tr) →
            WitnessIn shared) where
  coe E := E.toFun

end Extractor

end Reduction

end Oracle
end Interaction
