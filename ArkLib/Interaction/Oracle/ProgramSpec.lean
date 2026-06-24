/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Spec
import ArkLib.Interaction.Oracle.VerifierAccess

open Interaction.TwoParty

/-!
# Programmatic oracle spec helpers

Additive helpers for the experimental verifier-program layer. The core
`Oracle.Spec` module stays focused on protocol shape; this file records the
extra routing operations needed by programmatic verifier execution and
composition.
-/

open OracleComp OracleSpec

namespace Interaction.Oracle
namespace Spec

/-- Extend an accumulated oracle spec along a public transcript.

Unlike `accumulatedSpec`, this version does not require the concrete prover
oracle messages. It records only the oracle interfaces that become available to
verifier-local computations after following the public/control path. -/
def accumulatedPublicSpec :
    (s : Spec) → (od : OracleDeco s) →
    PublicTranscript s →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Σ ιₐ', OracleSpec.{0, 0} ιₐ'
  | .done, _, _, _, accSpec => ⟨_, accSpec⟩
  | .«public» _ rest, odRest, ⟨x, pt⟩, _, accSpec =>
      accumulatedPublicSpec (rest x) (odRest x) pt accSpec
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, pt⟩, _, accSpec =>
      accumulatedPublicSpec (cont ⟨⟩) odRest pt
        (accSpec + @OracleInterface.spec _ oi)

/-- Query the original accumulator after it has been embedded into
`accumulatedPublicSpec`. -/
def queryAccumulatedPublicBase :
    (s : Spec) → (od : OracleDeco s) → (pt : PublicTranscript s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    QueryImpl accSpec (OracleComp (accumulatedPublicSpec s od pt accSpec).2)
  | .done, _, _, _, accSpec => fun q =>
      (show OracleComp accSpec (accSpec.Range q) from liftM (accSpec.query q))
  | .«public» _ rest, odRest, ⟨x, pt⟩, _, accSpec =>
      queryAccumulatedPublicBase (rest x) (odRest x) pt accSpec
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, pt⟩, _, accSpec =>
      let nextSpec := accSpec + @OracleInterface.spec _ oi
      let route := queryAccumulatedPublicBase (cont ⟨⟩) odRest pt nextSpec
      fun q => route (.inl q)

/-- Query a prover oracle message from the final accumulator determined by a
public transcript. -/
def queryAccumulatedPublicOracle :
    (s : Spec) → (od : OracleDeco s) → (pt : PublicTranscript s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    QueryImpl (toOracleSpec s od pt)
      (OracleComp (accumulatedPublicSpec s od pt accSpec).2)
  | .done, _, _, _, _ => fun q => q.elim
  | .«public» _ rest, odRest, ⟨x, pt⟩, _, accSpec =>
      queryAccumulatedPublicOracle (rest x) (odRest x) pt accSpec
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, pt⟩, _, accSpec =>
      let nextSpec := accSpec + @OracleInterface.spec _ oi
      let baseRoute := queryAccumulatedPublicBase (cont ⟨⟩) odRest pt nextSpec
      let restRoute := queryAccumulatedPublicOracle (cont ⟨⟩) odRest pt nextSpec
      fun
        | .inl q => baseRoute (.inr q)
        | .inr q => restRoute q

/-- Compute verifier-side node monads from an explicit read-access family.

Public sender nodes and prover-oracle nodes remain verifier-pure. Public
receiver nodes run in the access-family monad for the current accumulated
oracle-message spec. -/
def toVerifierAccessDecoration {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    (access : Verifier.AccessFamily oSpec OStmtIn) :
    (s : Spec) → (roles : RoleDeco s) → (od : OracleDeco s) →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    Interaction.Spec.MonadDecoration s.toInteractionSpec :=
  toMonadDecorationWith
    (fun _ => pureNodeMonad)
    (fun accSpec => access.nodeMonad accSpec)
    (fun _ => pureNodeMonad)

/-- Query the left-hand oracle context through an appended oracle context.

This is the executable counterpart of `QueryHandle.appendLeft`, defined by
structural recursion so callers can route prefix simulators into the combined
oracle context without casts. -/
def queryAppendLeft :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryImpl (toOracleSpec s₁ od₁ pt₁)
      (OracleComp
        (toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
          (PublicTranscript.append s₁ s₂ pt₁ pt₂)))
  | .done, _, _, _, _, _, q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      queryAppendLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» X cont, s₂, ⟨oi, odRest⟩, od₂, ⟨u, pt₁⟩, pt₂, q =>
      let restSpec :=
        toOracleSpec ((cont ⟨⟩).append (fun pt => s₂ ⟨⟨⟩, pt⟩))
          (OracleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
            odRest (fun pt => od₂ ⟨⟨⟩, pt⟩))
          (PublicTranscript.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) pt₁ pt₂)
      let targetSpec :=
        toOracleSpec ((Spec.«oracle» X cont).append s₂)
          (OracleDeco.append (Spec.«oracle» X cont) s₂ ⟨oi, odRest⟩ od₂)
          (PublicTranscript.append (Spec.«oracle» X cont) s₂ ⟨u, pt₁⟩ pt₂)
      match q with
      | .inl q => liftM (targetSpec.query (.inl q))
      | .inr q =>
          simulateQ
            (fun h => liftM (targetSpec.query (.inr h)))
            (queryAppendLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
              odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ q :
                OracleComp restSpec _)

/-- Query the right-hand oracle context through an appended oracle context.

This is the executable counterpart of `QueryHandle.appendRight`, defined by
structural recursion so callers can route suffix simulators into the combined
oracle context without casts. -/
def queryAppendRight :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryImpl (toOracleSpec (s₂ pt₁) (od₂ pt₁) pt₂)
      (OracleComp
        (toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
          (PublicTranscript.append s₁ s₂ pt₁ pt₂)))
  | .done, s₂, _, od₂, ⟨⟩, pt₂, q =>
      (show OracleComp (toOracleSpec (s₂ ⟨⟩) (od₂ ⟨⟩) pt₂)
          (toOracleSpec (s₂ ⟨⟩) (od₂ ⟨⟩) pt₂ |>.Range q) from
        liftM <| (toOracleSpec (s₂ ⟨⟩) (od₂ ⟨⟩) pt₂).query q)
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      queryAppendRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» X cont, s₂, ⟨oi, odRest⟩, od₂, ⟨u, pt₁⟩, pt₂, q =>
      let restSpec :=
        toOracleSpec ((cont ⟨⟩).append (fun pt => s₂ ⟨⟨⟩, pt⟩))
          (OracleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
            odRest (fun pt => od₂ ⟨⟨⟩, pt⟩))
          (PublicTranscript.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) pt₁ pt₂)
      let targetSpec :=
        toOracleSpec ((Spec.«oracle» X cont).append s₂)
          (OracleDeco.append (Spec.«oracle» X cont) s₂ ⟨oi, odRest⟩ od₂)
          (PublicTranscript.append (Spec.«oracle» X cont) s₂ ⟨u, pt₁⟩ pt₂)
      simulateQ
        (fun h => liftM (targetSpec.query (.inr h)))
        (queryAppendRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
          odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ q :
            OracleComp restSpec _)

end Spec
end Interaction.Oracle
