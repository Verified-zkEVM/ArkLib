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
# Packing protocol vocabulary

The protocol-level types the `Packing` phases speak about, one level below any particular
message flow. The framework-independent algebra — pack/unpack, the tensor carrier, the verifier
subroutines and `tensorProductProfile` — lives in `Algebra.lean`, which this file re-exports.

## Main components

* **Protocol types** — statement/witness types at the phase boundaries and the `MLIOPCS`
  interface for the downstream opening (any protocol that opens a large-ring multilinear
  evaluation claim, bundled with its completeness and round-by-round knowledge-soundness
  obligations), and its worst-case strengthening `MLIOPCS.RbrKnowledgeSoundWorstCase`, carried as
  a hypothesis. An `AbstractOStmtIn` carries two compatibility relations between the packed
  polynomial and the oracle statements: the relaxed `initialCompatibility` used for knowledge
  soundness, and the honest `strictInitialCompatibility` (by default the same) used for perfect
  completeness through `AbstractOStmtIn.strictView`.
* **Relations** — the sumcheck multiplier parameter `RingSwitching_SumcheckMultParam` and the
  relations/knowledge-state predicates the security analysis threads through the phases.

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

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section ProtocolTypes
/-!
## Statement and witness types at the phase boundaries

What each phase of the reduction consumes and produces, plus the downstream-opening
interface.
-/

/-- Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`. -/
structure MLPEvalStatement where
  /-- The evaluation point `r = (r₀, …, r_{ℓ-1})` — shared input. -/
  t_eval_point : Fin ℓ → L
  /-- The claimed evaluation `s = t(r)`. -/
  original_claim : L

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext (P : RingSwitchingProfile K L κ)
    extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : P.A -- ŝ
  r_batching : Fin κ → L -- r''

-- `SumcheckWitness` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured` (the data shape is
-- generic and degree-neutral; only the per-round prover/verifier in `SumcheckPhase.lean` consume
-- it). Binius ring-switching is the degree-2 case `H = m · t'`, so this Binius-local abbrev pins
-- `d := 2`. Other instantiations (e.g. Hachi at `d := 2b+1`) pin their own degree — no
-- instantiation is privileged by a default on the generic type. The packed polynomial `t'` and
-- round polynomial `H` (after fixing previous challenges) live in the same structure.
abbrev SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) :=
  Sumcheck.Structured.SumcheckWitness L ℓ i 2

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  stmt.original_claim = wit.t.val.eval stmt.t_eval_point

structure AbstractOStmtIn where
  ιₛᵢ : Type
  OStmtIn : ιₛᵢ → Type
  Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)
  -- The abstract initial compatibility relation, which along with
  -- MLPEvalRelation, forms the initial input relation for the MLIOPCS.
  initialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop
  /-- Honest inputs may require exact compatibility, rather than decoding proximity.

  Perfect completeness is stated at this relation, so it is only as strong as this relation is
  inhabited: a client choosing an empty relation (e.g. `fun _ => False`) makes every completeness
  statement at `toStrictRelInput` vacuous. Instances should show that every packed polynomial has
  a strictly compatible oracle statement. -/
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

def AbstractOStmtIn.toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
    Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    MLPEvalRelation L ℓ' aOStmtIn.ιₛᵢ aOStmtIn.OStmtIn input
    ∧ aOStmtIn.initialCompatibility ⟨input.2.t, input.1.2⟩}

/-- Evaluation and honest oracle compatibility, used for perfect completeness. Completeness at this
relation is vacuous when `strictInitialCompatibility` is empty; see its docstring. -/
def AbstractOStmtIn.toStrictRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :=
  aOStmtIn.strictView.toRelInput

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
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)
  },
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

section WorstCase

attribute [local instance] MLIOPCS.Oₘ MLIOPCS.O_challenges

variable {L ℓ'} in
/-- **Worst-case round-by-round knowledge soundness of a downstream opening protocol**: for every
shared-oracle initialisation, its verifier is round-by-round knowledge sound per fixed transcript
prefix (`OracleProof.rbrKnowledgeSoundnessWorstCase`), at the relation and error of the averaged
`MLIOPCS.rbrKnowledgeSoundness` field.

It is a hypothesis on an `MLIOPCS`, not a field of it. It implies the averaged field, by
`OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`, so an instance that
proves the worst-case form fills that field with this lemma. The implication runs in one
direction only (see the note on the worst-case-per-prefix variants in
`OracleReduction/Security/RoundByRound.lean`), so an opening protocol whose knowledge soundness
depends on averaging over the prover's randomness or the shared oracle's state is still an
`MLIOPCS`. Sequential composition is proved for the
worst-case notion, so a composite that ends with the opening protocol takes this hypothesis. -/
def MLIOPCS.RbrKnowledgeSoundWorstCase (M : MLIOPCS L ℓ') : Prop :=
  ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleProof.rbrKnowledgeSoundnessWorstCase init impl M.toRelInput
      M.oracleReduction.toOracleVerifier M.rbrKnowledgeError

end WorstCase

end ProtocolTypes
end Preliminaries

/- This section defines the specific relations for the ring-switching protocol, whereas
the basis of L over K has rank `2^κ` instead of `κ` as in the Preliminaries section.
-/
section Relations
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
    SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ P) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K P ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
  -- Ring-switching is the plain degree-2 case `H = P · t'`: combinator `Q := X`, degree 1.
  combinator := fun _ => Polynomial.X
  degCombinator := 1
  combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le
}

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
    (ctx := stmt.ctx) (t := wit.t')
    (i := i) (challenges := stmt.challenges)
  ).val

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
    Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

/-- Sumcheck relation with honest initial oracle compatibility. -/
def strictSumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :=
  sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn.strictView i

end Relations

end RingSwitching
