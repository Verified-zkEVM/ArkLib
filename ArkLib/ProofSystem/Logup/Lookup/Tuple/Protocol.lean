/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Config
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
public import ArkLib.ProofSystem.Logup.Interaction.Protocol

/-!
# Executable tuple lookup with pre-compression multiplicities

The prover retains one base-field multiplicity oracle before the verifier draws beta. The verifier
opens the original stored coefficient columns and combines their actual scalar answers at beta;
it then runs the existing complete weighted LogUp verifier over that view, using the identity
map on the challenge field. No semantic bus is reconstructed at a non-Boolean point.

The generic challenge programs and named uniform endpoint share one implementation. Original
source realization and checked provider coherence are premises of the separate security theorem,
not runtime membership tests. The weighted suffix retains its existing alpha/helper/joint/native
rounds and actual final source authentication.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly

namespace Logup.Lookup.Tuple
variable {B E : Type} [CommRing B] [CommRing E]

/-- Retain base multiplicities before beta and the unchanged complete weighted suffix. -/
def protocol (f : B →+* E) (n M P ell : Nat) : Protocol :=
  .oracleWith (Vector (CMlPolynomialEval B n) P) (Logup.Lookup.multiplicityInterface f n P)
    (.public .receiver E fun _ => Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell)

variable (f : B →+* E) (n M P W ell : Nat) (cfg : Logup.Lookup.Config B n M P ell)
variable {ι : Type} (ambient : OracleSpec ι) [DecidableEq E]

/-- Draw beta over the retained base source, then use its concrete coefficient-Horner view. -/
def verifier (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W)) :
    Verifier.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (protocol f n M P ell).oracles A (fun _ => Bool) :=
  pure (do
    let beta ← OracleComp.liftComp betaDraw
      (ambient + ofPFunctor (Access.extend A (Logup.Lookup.multiplicityInterface f n P)))
    return ⟨beta, Logup.Interaction.verifier (RingHom.id E) n (M + P) ell cfg.weighted ambient
      alphaDraw jointDraw roundDraw (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
      (weightedView f n M P W beta A coeffView)⟩)

/-- Execute the actual tuple verifier against an ordinary whole prover with private output. -/
def execute (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) : OracleComp ambient Bool := do
  let result ← executeStrategies ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
    (protocol f n M P ell).oracles A impl prover
    (verifier f n M P W ell cfg ambient betaDraw alphaDraw jointDraw roundDraw A coeffView)
  return result.2.2


variable [SampleableType E]
/-- Supply existing uniform draws to the same tuple verifier and weighted native suffix. -/
def uniformExecute (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) : ProbComp Bool :=
  execute f n M P W ell cfg unifSpec ($ᵗ E) ($ᵗ E)
    ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))) ($ᵗ E) A coeffView impl prover
end Logup.Lookup.Tuple
