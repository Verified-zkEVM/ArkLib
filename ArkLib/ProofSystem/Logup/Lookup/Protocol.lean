/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Config
public import ArkLib.ProofSystem.Logup.Lookup.Source
public import ArkLib.ProofSystem.Logup.Interaction.Protocol

/-!
# Executable scalar lookup with an initial multiplicity message

One actual base-field multiplicity oracle is retained before the reviewed weighted LogUp protocol
publishes alpha. The verifier uses the original value view and that actual retained slot to expose
query weights1 and negative table multiplicities. The entire weighted suffix, including its native
Sumcheck and terminal source authentication, is unchanged.

The exact sender-bind law retains all effects, abort behavior and arbitrary path-dependent private
output of the ordinary whole prover. It assumes no message kernel or execution equality. Security
is a separate consumer of this actual endpoint and the existing weighted theorem.
-/

@[expose] public section

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly

namespace Logup.Lookup

variable {B E : Type} [CommRing B] [CommRing E]

/-- Retain one vector of base-field multiplicities, then run the complete weighted tree. -/
def protocol (f : B →+* E) (n M P ell : ℕ) : Protocol :=
  .oracleWith (Vector (CMlPolynomialEval B n) P) (multiplicityInterface f n P)
    (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell)

variable (f : B →+* E) (n M P ell : ℕ) (cfg : Config B n M P ell)
variable {ι : Type} (ambient : OracleSpec ι)
variable [DecidableEq E]

/-- Continue with the actual weighted verifier over the retained multiplicity source. -/
def verifier (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P)) :
    Verifier.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (protocol f n M P ell).oracles A (fun _ => Bool) :=
  pure (Logup.Interaction.verifier f n (M + P) ell cfg.weighted ambient
    alphaDraw jointDraw roundDraw (Access.extend A (multiplicityInterface f n P))
    (weightedView f n M P A valuesView))

/-- Execute the complete scalar lookup verifier against any ordinary whole prover. -/
def execute (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) : OracleComp ambient Bool := do
  let result ← executeStrategies ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
    (protocol f n M P ell).oracles A impl prover
    (verifier f n M P ell cfg ambient alphaDraw jointDraw roundDraw A valuesView)
  return result.2.2

set_option backward.isDefEq.respectTransparency false in
/-- The actual first sender program supplies both the retained message and weighted continuation. -/
theorem execute_eq_sender_bind (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) :
    execute f n M P ell cfg ambient alphaDraw jointDraw roundDraw A valuesView impl prover = (do
      let sent ← prover
      Logup.Interaction.execute f n (M + P) ell cfg.weighted ambient
        alphaDraw jointDraw roundDraw (Access.extend A (multiplicityInterface f n P))
        (weightedView f n M P A valuesView)
        (Access.extendImpl A (multiplicityInterface f n P) impl sent.1)
        (OutP := fun path => OutP ⟨sent.1, path⟩) sent.2) := by
  unfold execute
  simp only [protocol, Protocol.oracleWith]
  rw [executeStrategies_oracle]
  simp only [verifier, simulateQ_pure, bind_assoc, pure_bind]
  rfl

variable [SampleableType E]
/-- Use the existing independent scalar and product uniform samplers in the weighted suffix. -/
def uniformExecute (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f n M P ell).tree
      (protocol f n M P ell).roles OutP) : ProbComp Bool :=
  execute f n M P ell cfg unifSpec
    ($ᵗ E) ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    ($ᵗ E) A valuesView impl prover


end Logup.Lookup
