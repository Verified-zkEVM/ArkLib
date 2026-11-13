/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Basic
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.ProofSystem.RingSwitching.Packing.Algebra
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic

/-!
# Polynomial evaluation and opening interfaces

`MLPEvalStatement` and `WitMLP` describe multilinear evaluation claims and witnesses.
`AbstractOStmtIn` equips a commitment oracle family with a relation for knowledge soundness
and an honest subrelation for completeness. `MLIOPCS` bundles an opening protocol, perfect
completeness and round-by-round knowledge soundness.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over
  Binary Towers*][DP24], §2.5.
-/

@[expose] public section

noncomputable section

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial TensorProduct
open scoped NNReal
open Sumcheck.Structured

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (L : Type) [CommRing L] (ℓ ℓ' : ℕ)

section ProtocolTypes
/-!
## Statement and witness types at the phase boundaries

What each phase of the reduction consumes and produces, plus the downstream-opening
interface.
-/

/-- A claim that a multilinear polynomial evaluates to `s` at `r`. -/
structure MLPEvalStatement where
  /-- The evaluation point `r = (r₀, …, r_{ℓ-1})` — shared input. -/
  t_eval_point : Fin ℓ → L
  /-- The claimed evaluation `s = t(r)`. -/
  original_claim : L

/-- A multilinear polynomial witnessing an evaluation claim. -/
structure WitMLP where
  t : MultilinearPoly L ℓ

section MLIOPCS

/-- A commitment oracle interface with soundness and honest compatibility relations. -/
structure AbstractOStmtIn where
  ιₛᵢ : Type
  OStmtIn : ιₛᵢ → Type
  Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)
  /-- Compatibility between the polynomial and the commitment oracle statements. -/
  initialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop
  /-- Honest compatibility, used by completeness. Each consumer supplies compatible oracle
  statements for its honest polynomials. -/
  strictInitialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop :=
    initialCompatibility
  /-- Honest compatibility also satisfies the relation used for knowledge soundness. -/
  strictInitialCompatibility_implies_initialCompatibility :
    ∀ oStmt t, strictInitialCompatibility ⟨t, oStmt⟩ → initialCompatibility ⟨t, oStmt⟩ := by
      intros
      assumption

/-- The same oracle interface, with honest compatibility as its input relation. -/
def AbstractOStmtIn.strictView (aOStmtIn : AbstractOStmtIn L ℓ') : AbstractOStmtIn L ℓ' where
  ιₛᵢ := aOStmtIn.ιₛᵢ
  OStmtIn := aOStmtIn.OStmtIn
  Oₛᵢ := aOStmtIn.Oₛᵢ
  initialCompatibility := aOStmtIn.strictInitialCompatibility

/-- Evaluation equality together with commitment compatibility. -/
def AbstractOStmtIn.toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
    Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    input.1.1.original_claim = input.2.t.val.eval input.1.1.t_eval_point
    ∧ aOStmtIn.initialCompatibility ⟨input.2.t, input.1.2⟩}

/-- Evaluation equality together with honest commitment compatibility. -/
def AbstractOStmtIn.toStrictRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :=
  aOStmtIn.strictView.toRelInput

/-- A multilinear opening protocol with completeness and round-by-round knowledge soundness. -/
structure MLIOPCS extends (AbstractOStmtIn L ℓ') where
  /-- Protocol specification -/
  numRounds : ℕ
  pSpec : ProtocolSpec numRounds
  Oₘ: ∀ j, OracleInterface (pSpec.Message j)
  O_challenges: ∀ (i : pSpec.ChallengeIdx), SampleableType (pSpec.Challenge i)
  /-- The evaluation protocol Π' as an oracle proof. -/
  oracleReduction : OracleProof (oSpec := []ₒ)
    (Statement := MLPEvalStatement L ℓ') (OStatement := OStmtIn)
    (Witness := WitMLP L ℓ')
    (pSpec := pSpec)
  -- Security properties
  perfectCompleteness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleProof.perfectCompleteness (oSpec := []ₒ)
      (Statement := MLPEvalStatement L ℓ') (OStatement := OStmtIn)
      (Witness := WitMLP L ℓ') (pSpec := pSpec) (init := init) (impl := impl)
      (relation := toAbstractOStmtIn.toStrictRelInput)
      (oracleProof := oracleReduction)
  -- RBR knowledge error function for the MLIOPCS
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  -- RBR knowledge soundness property
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleProof.rbrKnowledgeSoundness
      (verifier := oracleReduction.toOracleVerifier)
      (init := init)
      (impl := impl)
      (relIn := toAbstractOStmtIn.toRelInput)
      (rbrKnowledgeError := rbrKnowledgeError)

end MLIOPCS

section OStmt
variable (aOStmtIn : AbstractOStmtIn L ℓ')

instance instOstmtMLIOPCS : ∀ (i : aOStmtIn.ιₛᵢ), OracleInterface (aOStmtIn.OStmtIn i) :=
  fun i => aOStmtIn.Oₛᵢ i

end OStmt

end ProtocolTypes
end Preliminaries

end RingSwitching
