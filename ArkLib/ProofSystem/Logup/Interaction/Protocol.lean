/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Source
public import ArkLib.ProofSystem.Logup.Interaction.Config
public import ArkLib.ProofSystem.Sumcheck.Interaction.Computable
public import ArkLib.Interaction.Oracle.SourceRouting
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Executable scalar weighted LogUp

The native tree publishes alpha, receives the actual helper oracle, and publishes one joint
challenge containing the batching point and coefficients. It then runs the existing native
coefficient-message Sumcheck and authenticates its final claim against the same retained source.

Generic challenge programs give deterministic fixtures and the named uniform endpoint the same
verifier implementation. Ordinary prover strategies retain their private state and all receiver
and sender effects. The mathematical family is only a type/proof descriptor; executable source
programs supply every answer. Security and honest-prover proofs are separate consumer owners.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec
open PFunctor.FreeM.Displayed (Decoration)

namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E]

/-- Native Sumcheck starts from the zero-sum claim with an empty challenge prefix. -/
def zeroStatement (E : Type) [Zero E] (n : Nat) : Sumcheck.Spec.StatementRound E n 0 :=
  ⟨0, Fin.elim0⟩

/-- Publish alpha, retain one helper oracle, then publish one joint batching challenge. -/
def prefixProtocol (E : Type) [CommRing E] (n K : Nat) : Protocol :=
  .public .receiver E fun _ =>
    .oracleWith (Vector (CompPoly.CMlPolynomialEval E n) K) (helperInterface (E := E) n K)
      (.public .receiver ((Fin n → E) × (Fin K → E)) fun _ => .done)

/-- The weighted prefix followed by the existing coefficient-message native Sumcheck tree. -/
abbrev protocol (E : Type) [CommRing E] (n K ell : Nat) : Protocol :=
  ⟨PFunctor.FreeM.append (prefixProtocol E n K).tree
      (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree),
    Decoration.append (prefixProtocol E n K).roles
      (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles),
    Decoration.append (prefixProtocol E n K).oracles
      (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles)⟩

variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

/-- Proof/type descriptor of the existing bounded native Sumcheck polynomial family. -/
noncomputable abbrev family :=
  Sumcheck.Interaction.MultivariateRound.polynomialFamily E n (ell + 2)

/-- Draw public challenges and export Q through the actual retained helper source. -/
def prefixVerifier (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (A : PFunctor.{0, 0}) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) :
    Verifier.Fragment ambient (prefixProtocol E n (T ⌈/⌉ ell)).tree
      (prefixProtocol E n (T ⌈/⌉ ell)).roles (prefixProtocol E n (T ⌈/⌉ ell)).oracles A
      (fun p => OpenClaim
        (ofPFunctor (TypeTree.accessAfter (prefixProtocol E n (T ⌈/⌉ ell)).tree
          (prefixProtocol E n (T ⌈/⌉ ell)).oracles A p))
        (Sumcheck.Spec.StatementRound E n 0) (family (E := E) n ell)) := do
  let alpha ← OracleComp.liftComp alphaDraw (ambient + ofPFunctor A)
  return ⟨alpha, pure (do
    let joint ← OracleComp.liftComp jointDraw
      (ambient + ofPFunctor (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell))))
    return ⟨joint, ⟨zeroStatement E n,
      qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView⟩⟩)⟩

variable [DecidableEq E]

/-- The suffix is authored over Q alone, with the executable Boolean domain list. -/
def suffixVerifier (roundDraw : OracleComp ambient E)
    (_ : (prefixProtocol E n (T ⌈/⌉ ell)).tree.BranchPath)
    (stmt : Sumcheck.Spec.StatementRound E n 0) :=
  Sumcheck.Interaction.Computable.verifier E n (ell + 2) ambient roundDraw [0, 1] n 0
    (Nat.zero_add n)
    (family (E := E) n ell).spec.toPFunctor (VirtualOracle.id (family (E := E) n ell)) stmt

/-- Route the native final claim back through the prefix's actual source export. -/
def reductionVerifier (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) :
    Verifier.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A
      (TerminalClaim (protocol E n (T ⌈/⌉ ell) ell) A
        (fun _ => Sumcheck.Interaction.Computable.FinalStatement E n)
        (fun _ => family (E := E) n ell)) :=
  Verifier.appendExported ambient (prefixProtocol E n (T ⌈/⌉ ell)).tree
    (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree)
    (prefixProtocol E n (T ⌈/⌉ ell)).roles
    (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles)
    (prefixProtocol E n (T ⌈/⌉ ell)).oracles
    (fun _ => (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles) A
    (fun _ => Sumcheck.Spec.StatementRound E n 0)
    (fun _ => Sumcheck.Spec.OracleStatement E n (ell + 2)) (fun _ => family (E := E) n ell)
    (fun _ => Sumcheck.Interaction.Computable.FinalStatement E n)
    (fun _ => Sumcheck.Spec.OracleStatement E n (ell + 2)) (fun _ => family (E := E) n ell)
    (prefixVerifier f n T ell cfg ambient alphaDraw jointDraw A inputView)
    (suffixVerifier n T ell ambient roundDraw)

/-- Complete the weighted verifier with actual final source authentication. -/
def verifier (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) :
    Verifier.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A
      (fun _ => Bool) :=
  Verifier.Fragment.mapOutput ambient (fun path action =>
    Sumcheck.Interaction.Native.Core.checkFinalResult E n (ell + 2) ambient
      (TypeTree.accessAfter (protocol E n (T ⌈/⌉ ell) ell).tree
        (protocol E n (T ⌈/⌉ ell) ell).oracles A path) action)
    (reductionVerifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView)

/-- Execute the actual weighted verifier against any private-output prover strategy. -/
def execute (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) : OracleComp ambient Bool := do
  let result ← executeStrategies ambient (protocol E n (T ⌈/⌉ ell) ell).tree
    (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A
    impl prover (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView)
  return result.2.2

variable [SampleableType E]

/-- The named probabilistic endpoint uses the existing scalar and product uniform samplers. -/
def uniformExecute (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) : ProbComp Bool :=
  execute f n T ell cfg unifSpec ($ᵗ E) ($ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    ($ᵗ E) A inputView impl prover

end Logup.Interaction
