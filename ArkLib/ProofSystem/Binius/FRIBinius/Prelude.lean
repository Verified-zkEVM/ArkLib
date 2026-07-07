/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

/-!
# FRI-Binius IOPCS Prelude
This module contains the preliminary definitions for the FRI-Binius IOPCS.
-/

noncomputable section

namespace Binius.FRIBinius

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

omit [NeZero κ] in
lemma card_bool_hypercube_eq :
  Fintype.card (Fin κ → Fin 2) = 2 ^ κ := by
  simp only [Fintype.card_pi, Fintype.card_fin, prod_const, card_univ]

def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  Fintype.equivFinOfCardEq (card_bool_hypercube_eq κ)

instance booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

instance linearIndependentBooleanHypercubeBasis : Fact (LinearIndependent K ⇑β) := by
  constructor
  exact β.linearIndependent

def BinaryBasefoldAbstractOStmtIn : (RingSwitching.AbstractOStmtIn L ℓ') where
  ιₛᵢ := Fin (BinaryBasefold.toOutCodewordsCount ℓ' ϑ (i:=0))
  OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0
  Oₛᵢ := Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := 0)
  initialCompatibility := fun ⟨t, oStmt⟩ =>
    Binius.BinaryBasefold.firstOracleWitnessConsistencyProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t (f₀ := Binius.BinaryBasefold.getFirstOracle K β oStmt)

/-- The Binius codeword-consistency predicate in the generic `commitsTo` orientation
(oracle statement → committed multilinear → `Prop`, cf.
`RingSwitching.Generic.PackedCommitment.commitsTo`): the initial oracle commits to `t` iff
`firstOracleWitnessConsistencyProp t f₀` holds for the first oracle. Same semantics as
`BinaryBasefoldAbstractOStmtIn.initialCompatibility` (pinned by
`initialCompatibility_eq_biniusCommitsTo`), re-oriented for the S7 migration onto the generic
PCS interface.

The underlying predicate reads `t`'s cube table via `witnessNovelCoeffs` (LSB-first bit order;
see its docstring for the history: the original spelling read `t`'s *diagonal* evaluations
through a silent coercion, making the encoding non-injective — found at the S5 close-review and
fixed in this PR). The **functionality proof** (`commitsTo c t → commitsTo c t' → t = t'`) is
the recorded S7 obligation, provable by unique decoding: two codewords within half the code
distance of one word coincide; the novel-basis coefficient map is injective; a multilinear is
determined by its cube table. It bundles into a `PackedCommitment` at S7. -/
def biniusCommitsTo
    (oStmt : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j)
    (t : Sumcheck.Structured.MultilinearPoly L ℓ') : Prop :=
  Binius.BinaryBasefold.firstOracleWitnessConsistencyProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    t (f₀ := Binius.BinaryBasefold.getFirstOracle K β oStmt)

omit [NeZero κ] [CharP L 2] [SampleableType L] [DecidableEq K] [NeZero 𝓡] in
/-- The legacy free hook and the `commitsTo`-oriented predicate are definitionally the same —
the S5 re-expression is a re-orientation, not a semantic change. -/
lemma initialCompatibility_eq_biniusCommitsTo :
    (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).initialCompatibility
      = fun x => biniusCommitsTo κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate x.2 x.1 :=
  rfl

end Binius.FRIBinius
