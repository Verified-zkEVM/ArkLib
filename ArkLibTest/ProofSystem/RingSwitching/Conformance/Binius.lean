/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.FRIBinius.General
import ArkLibTest.ProofSystem.RingSwitching.Packing.Orientation

/-!
# Binius batching-phase conformance to the shared packing layer

The conformance theorem `batching_conforms` states the DP24 batching phase used by Binius
through the shared packing layer of `RingSwitching.Packing`, at the packing data
`PackingData.ofBasis P.basis` of a profile and DP24's prefix claim layout `prefixLayout P ℓ'`
(the shared `packedPrefixLayout`). Its left side is the verifier's column check together with the
round-zero sumcheck relation at the statement the verifier outputs on acceptance. Its right side
says that:

* the packed polynomial is compatible with the oracle statement;
* the round polynomial is the shared `multiplier` at the retained point and the batching weights,
  times the packed polynomial;
* the batched rows of the sent carrier and the packed polynomial are in the shared
  `sumcheckClaimRel` of that multiplier;
* the claim is the layout-weighted sum of the sent carrier's column family.

The statements it is built from are:

* `check_iff_layout_weight`: the column check is the layout-weighted read-back;
* `witnessStructuralInvariant_iff`: the round polynomial is the shared multiplier times the packed
  polynomial (through `compute_A_MLE_eq_multiplier`);
* `sumcheckConsistencyProp_iff_sumcheckClaimRel`: for a structured round polynomial, round-zero
  consistency is the shared `sumcheckClaimRel`, by summing the sum-check cube as the Boolean cube
  (`sum_cube_boolDomain`).

`oracleVerifier_eq_scalarRoundOracleVerifier` pins `acceptedStatement` to production: the
production verifier is, by `rfl`, the shared `scalarRoundOracleVerifier` with the column check
and `acceptedStatement` as its accept branch. A failed check aborts.

Two further statements cover the rest of the phase:

* `mem_batchingInputRelation_iff_layout`: the input relation says that the packed polynomial is
  the shared `packedMLE` of the source's prefix-layout components, and that the claim is the
  layout's weighted reconstruction from the component evaluations;
* `embedded_MLP_eval_packMLE_eq_iff_sliceRel` and
  `embedded_MLP_eval_packMLE_eq_iff_openingClaimRel`: a carrier is the honest message of the
  packed source exactly when its rows are the shared slices (`sliceRel`) of that `packedMLE`,
  equivalently when its columns are the component opening values (`openingClaimRel`). The second
  form goes through the shared `openingClaimRel_iff_sliceRel` and `transpose_decomposeColumns`.

The ring-switching layer enters Binius's verifier a second time, in the final sum-check step
(`SumcheckPhase.finalSumcheckVerifier`). `compute_final_eq_value_eq_multiplier` states its
equality value as the evaluation of the same shared `multiplier`, at the same retained point and
batching weights, and `finalCheck_iff_multiplier` states the final check through it. The
intermediate sum-check rounds belong to the generic structured sum-check, and the FRI folding and
query phases to Binary Basefold; both are out of scope here.

`biniusBatching_conforms` is `batching_conforms` at Binius's `biniusProfile` and oracle statement
`BinaryBasefoldAbstractOStmtIn`, where compatibility is the first-oracle codeword consistency.

Scope: the statements cover the accepting branch; the rejecting branch aborts. The output
relation fixes only the batched target, so acceptance does not make the carrier honest: the gap is
the batching collision event bounded by `compute_s0_collision_le` and
`prob_exists_consistent_ne_le`. The phase's security theorems are in `BatchingPhase`
(`batchingReduction_perfectCompleteness`, `batchingOracleVerifier_rbrKnowledgeSoundness`); no
security theorem is claimed here.

The concrete instances, at the `GF(4)/GF(2)` orientation fixture with a binding oracle statement,
show the honest round accepted through `batching_conforms`; the zero carrier passing the check but
failing the batched target at the zero challenge; no carrier at all accepted for a false claim at
the zero batching challenge; and the honest carrier's columns, not its rows, opening the
components. At the source `X₁` in the retained variable and the point `(0, Z 1)`, the honest check
accepts the true claim `Z 1` while the rows read back `0`, so a row/column swap is caught there
too. At `X₀` and the point `(Z 1, 0)`, weighting the columns by the retained coordinate instead of
the packed one reads back `0`, so a packed/retained swap is caught.

Two regression fixtures pin the behaviour at the limits. `zero_carrier_collides` realises the
batching collision: at the challenge `1` the zero carrier is accepted with the honest witness.
`failedCheck_aborts` pins the abort on rejection: for the claim `1`, which no witness satisfies
(`claimAt_one_not_mem_batchingInputRelation`), the check rejects the honest carrier and the
production verifier aborts, so no output can meet the round-zero relation. Before the repair the
verifier returned a dummy `failureState`, which lay in that relation with the zero polynomial
committed.

The fixture objects come from `ArkLibTest.RingSwitchingOrientation`; its single-letter names are
opened here only under the renamings `GF2`, `GF4`, `P₄`, `r₀` and `tX₀`.
-/

open Module MvPolynomial RingSwitching Sumcheck.Structured

noncomputable section

namespace ArkLibTest.RingSwitchingConformance.Binius

section SharedLayer

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L] {κ ℓ ℓ' : ℕ}
  (P : RingSwitchingProfile K L κ) (h_l : ℓ = ℓ' + κ)

/-- DP24's claim layout at a profile: the `κ` prefix variables are packed along the profile
basis and the `ℓ'` suffix variables are retained. -/
abbrev prefixLayout (ℓ' : ℕ) :
    Packing.ScalarHead.ClaimLayout (Packing.PackingData.ofBasis P.basis) ℓ' :=
  Packing.ScalarHead.packedPrefixLayout (Packing.PackingData.ofBasis P.basis) ℓ' κ (Equiv.refl _)

/-- The layout query of an evaluation point: its packed prefix and its retained suffix. -/
abbrev prefixQuery (r : Fin ℓ → L) : (prefixLayout P ℓ').Query :=
  (fun i => r ⟨i.val, by omega⟩, getEvaluationPointSuffix κ L ℓ ℓ' h_l r)

/-- The batching weights of a batching challenge: the equality weights of the Boolean cube. -/
abbrev batchingWeight (c : Fin κ → L) : (Fin κ → Fin 2) → L :=
  fun u => eqTilde (u : Fin κ → L) c

/-- The rows of a carrier are the shared slices of a packed polynomial exactly when its columns
are the opening values of the components: the row family is the shared transpose of the column
family. -/
theorem sliceRel_iff_openingClaimRel {m : ℕ} (z : P.A)
    (ps : (Fin κ → Fin 2) → K⦃≤ 1⦄[X Fin m]) (x : Fin m → L) :
    (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE ps) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel m x ↔
      ((P.decomposeColumns z, x), ps) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel m := by
  rw [← P.transpose_decomposeColumns, ← Packing.PackingData.openingClaimRel_iff_sliceRel]

/-- A carrier is the honest tensor evaluation of the packed source exactly when its rows are the
shared slices of the `packedMLE` of the source's prefix-layout components. -/
theorem embedded_MLP_eval_packMLE_eq_iff_sliceRel (t : MultilinearPoly K ℓ) (r : Fin ℓ → L)
    (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE
          ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l t))) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel ℓ'
          ((prefixLayout P ℓ').point (prefixQuery P h_l r)) := by
  rw [packMLE_eq_packedPrefixLayout]
  exact embedded_MLP_eval_eq_iff_sliceRel P h_l _ r z

/-- A carrier is the honest tensor evaluation of the packed source exactly when its columns are
the opening values of the source's prefix-layout components at the retained point. -/
theorem embedded_MLP_eval_packMLE_eq_iff_openingClaimRel (t : MultilinearPoly K ℓ)
    (r : Fin ℓ → L) (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      ((P.decomposeColumns z, (prefixLayout P ℓ').point (prefixQuery P h_l r)),
          (prefixLayout P ℓ').components (sourceDimensionEquiv h_l t)) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel ℓ' := by
  rw [embedded_MLP_eval_packMLE_eq_iff_sliceRel, sliceRel_iff_openingClaimRel]

/-- The column check says that the claim is the layout-weighted sum of the carrier's column
family. -/
theorem check_iff_layout_weight [DecidableEq L] (s : L) (r : Fin ℓ → L) (z : P.A) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l s r z = true ↔
      s = ∑ v, (prefixLayout P ℓ').weight (prefixQuery P h_l r) v * P.decomposeColumns z v := by
  unfold performCheckOriginalEvaluation
  rw [decide_eq_true_iff, eqWeightedCoordSum_eq_sum]
  rfl

/-- The input relation through the shared layout: the packed polynomial is the shared
`packedMLE` of the source's prefix-layout components, the claim is the layout's weighted
reconstruction from the component evaluations at the retained point, and the packed polynomial
is compatible with the oracle statement. -/
theorem mem_batchingInputRelation_iff_layout (aOStmtIn : AbstractOStmtIn L ℓ')
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') :
    ((stmt, oStmt), wit) ∈ BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn ↔
      wit.t' = (Packing.PackingData.ofBasis P.basis).packedMLE
          ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l wit.t)) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout P ℓ').weight (prefixQuery P h_l stmt.t_eval_point) v *
            aeval ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
              ((prefixLayout P ℓ').components (sourceDimensionEquiv h_l wit.t) v).val ∧
        aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩ := by
  change wit.t' = _ ∧ stmt.original_claim = _ ∧ _ ↔ _
  rw [packMLE_eq_packedPrefixLayout, aeval_eq_sum_splitFirst h_l]
  rfl

/-- The statement the batching verifier outputs when its check accepts the carrier `z` and the
batching challenge is `c`: the accept branch of `BatchingPhase.oracleVerifier`, as
`oracleVerifier_eq_scalarRoundOracleVerifier` states. -/
abbrev acceptedStatement (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 :=
  { ctx :=
      { t_eval_point := stmt.t_eval_point
        original_claim := stmt.original_claim
        s_hat := z
        r_batching := c }
    sumcheck_target := compute_s0 κ L K P z c
    challenges := Fin.elim0 }

/-- The production batching verifier is the shared check-then-update scalar-round verifier with
the column check and the accepted statement `acceptedStatement`. -/
theorem oracleVerifier_eq_scalarRoundOracleVerifier [DecidableEq L]
    (aOStmtIn : AbstractOStmtIn L ℓ') :
    BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn) =
      scalarRoundOracleVerifier (Msg := P.A) (C := Fin κ → L)
        (fun stmt z => performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
          stmt.t_eval_point z)
        (acceptedStatement P) :=
  rfl

/-- At the accepted statement, the round-zero structural invariant says that the round polynomial
is the shared multiplier at the retained point and the batching weights, times the packed
polynomial. -/
theorem witnessStructuralInvariant_iff (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L)
    (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    witnessStructuralInvariant κ L K P ℓ ℓ' h_l (acceptedStatement P stmt z c) wit ↔
      wit.H.val = ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
          (batchingWeight c)).val * wit.t'.val := by
  unfold witnessStructuralInvariant
  simp only [projectToMidSumcheckPolyWithParam]
  -- `erw`: the fixed-prefix length is `↑(0 : Fin (ℓ' + 1))`, only definitionally `0`
  erw [fixFirstVariablesOfMQP_zero]
  simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, compute_A_MLE_eq_multiplier,
    Polynomial.aeval_X]
  exact Iff.rfl

/-- For a structured round polynomial, round-zero sumcheck consistency of the accepted target says
that the batched rows of the carrier and the packed polynomial are in the shared
`sumcheckClaimRel` of the shared multiplier. -/
theorem sumcheckConsistencyProp_iff_sumcheckClaimRel [Nontrivial L] (stmt : BatchingStmtIn L ℓ)
    (z : P.A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0)
    (hH : witnessStructuralInvariant κ L K P ℓ ℓ' h_l (acceptedStatement P stmt z c) wit) :
    sumcheckConsistencyProp (boolDomain L _) (compute_s0 κ L K P z c) wit.H ↔
      (∑ u, batchingWeight c u * P.decomposeRows z u, wit.t') ∈
        (Packing.PackingData.ofBasis P.basis).sumcheckClaimRel ℓ'
          ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point)) (batchingWeight c) := by
  rw [witnessStructuralInvariant_iff] at hH
  unfold sumcheckConsistencyProp
  rw [hH, sum_cube_boolDomain, compute_s0_eq_sum]
  change _ = _ ↔ _ = _
  exact Iff.of_eq (congrArg₂ (· = ·) rfl (Finset.sum_congr rfl fun y _ => MvPolynomial.eval_mul))

/-- **Binius batching conformance.** The batching verifier's column check accepts a sent carrier
and its accepted output is in the round-zero sumcheck relation exactly when the packed polynomial
is compatible with the oracle statement, the round polynomial is the shared multiplier times the
packed polynomial, the batched rows of the carrier are the shared sumcheck claim of that
multiplier, and the claim is the layout-weighted sum of the carrier's column family. -/
theorem batching_conforms [Nontrivial L] [DecidableEq L] (aOStmtIn : AbstractOStmtIn L ℓ')
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (z : P.A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    (performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim stmt.t_eval_point z =
          true ∧
        ((acceptedStatement P stmt z c, oStmt), wit) ∈
          sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0) ↔
      aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩ ∧
        wit.H.val = ((Packing.PackingData.ofBasis P.basis).multiplier
          ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point))
            (batchingWeight c)).val * wit.t'.val ∧
        (∑ u, batchingWeight c u * P.decomposeRows z u, wit.t') ∈
          (Packing.PackingData.ofBasis P.basis).sumcheckClaimRel ℓ'
            ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.t_eval_point)) (batchingWeight c) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout P ℓ').weight (prefixQuery P h_l stmt.t_eval_point) v *
            P.decomposeColumns z v := by
  rw [check_iff_layout_weight]
  change _ ∧ (True ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l _ wit ∧
    sumcheckConsistencyProp _ _ wit.H ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩) ↔ _
  rw [← witnessStructuralInvariant_iff]
  constructor
  · rintro ⟨hs, -, hH, hcons, hcomp⟩
    exact ⟨hcomp, hH,
      (sumcheckConsistencyProp_iff_sumcheckClaimRel P h_l stmt z c wit hH).1 hcons, hs⟩
  · rintro ⟨hcomp, hH, hclaim, hs⟩
    exact ⟨hs, trivial, hH,
      (sumcheckConsistencyProp_iff_sumcheckClaimRel P h_l stmt z c wit hH).2 hclaim, hcomp⟩

/-- The final sum-check step's equality value is the shared multiplier, at the same retained
point and batching weights as the batching phase, evaluated at the sum-check challenges. -/
theorem compute_final_eq_value_eq_multiplier (r : Fin ℓ → L) (r' : Fin ℓ' → L)
    (c : Fin κ → L) :
    compute_final_eq_value κ L K P ℓ ℓ' h_l r r' c =
      eval r' ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l r)) (batchingWeight c)).val := by
  rw [compute_final_eq_value_eq_eval, compute_A_MLE_eq_multiplier]
  rfl

/-- The final sum-check check of `SumcheckPhase.finalSumcheckVerifier`, through the shared
multiplier: the target is the multiplier at the challenges times the prover's final constant. -/
theorem finalCheck_iff_multiplier
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (s' : L) :
    stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point
        stmt.challenges stmt.ctx.r_batching * s' ↔
      stmt.sumcheck_target = eval stmt.challenges ((Packing.PackingData.ofBasis P.basis).multiplier
        ((prefixLayout P ℓ').point (prefixQuery P h_l stmt.ctx.t_eval_point))
          (batchingWeight stmt.ctx.r_batching)).val * s' := by
  rw [compute_final_eq_value_eq_multiplier]

end SharedLayer

section Binius

open Binius.FRIBinius Binius.FRIBinius.FullFRIBinius

variable (κ : ℕ) [NeZero κ]
  (L : Type) [Field L] [Fintype L] [DecidableEq L]
  (K : Type) [Field K] [Fintype K]
  [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)] [Algebra K L]
  (β : Basis (Fin (2 ^ κ)) K L) {ℓ ℓ' 𝓡 ϑ : ℕ} [NeZero ℓ'] [NeZero ϑ]
  (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ) (h_l : ℓ = ℓ' + κ) [Fact (ϑ ∣ ℓ')]

/-- `batching_conforms` at Binius's tensor profile and committed first oracle: compatibility is
the consistency of the packed polynomial with the first committed codeword. -/
theorem biniusBatching_conforms (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j)
    (z : (biniusProfile κ L K β).A) (c : Fin κ → L) (wit : RingSwitching.SumcheckWitness L ℓ' 0) :
    (performCheckOriginalEvaluation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l stmt.original_claim
          stmt.t_eval_point z = true ∧
        ((acceptedStatement (biniusProfile κ L K β) stmt z c, oStmt), wit) ∈
          sumcheckRoundRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
            (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) 0) ↔
      Binius.BinaryBasefold.firstOracleWitnessConsistencyProp K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t'
          (Binius.BinaryBasefold.getFirstOracle K β oStmt) ∧
        wit.H.val = ((Packing.PackingData.ofBasis (biniusProfile κ L K β).basis).multiplier
          ((prefixLayout (biniusProfile κ L K β) ℓ').point
            (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point))
            (batchingWeight c)).val * wit.t'.val ∧
        (∑ u, batchingWeight c u * (biniusProfile κ L K β).decomposeRows z u, wit.t') ∈
          (Packing.PackingData.ofBasis (biniusProfile κ L K β).basis).sumcheckClaimRel ℓ'
            ((prefixLayout (biniusProfile κ L K β) ℓ').point
              (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point)) (batchingWeight c) ∧
        stmt.original_claim = ∑ v,
          (prefixLayout (biniusProfile κ L K β) ℓ').weight
            (prefixQuery (biniusProfile κ L K β) h_l stmt.t_eval_point) v *
            (biniusProfile κ L K β).decomposeColumns z v :=
  batching_conforms (biniusProfile κ L K β) h_l
    (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) stmt oStmt z c wit

end Binius

/-! The conformance theorems depend only on the standard axioms. -/

/--
info: 'ArkLibTest.RingSwitchingConformance.Binius.batching_conforms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLibTest.RingSwitchingConformance.Binius.batching_conforms

/--
info: 'ArkLibTest.RingSwitchingConformance.Binius.mem_batchingInputRelation_iff_layout' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLibTest.RingSwitchingConformance.Binius.mem_batchingInputRelation_iff_layout

/--
info: 'ArkLibTest.RingSwitchingConformance.Binius.embedded_MLP_eval_packMLE_eq_iff_openingClaimRel'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.RingSwitchingConformance.Binius.embedded_MLP_eval_packMLE_eq_iff_openingClaimRel

section Concrete

open ConcreteBinaryTower
open scoped TensorProduct
open ArkLibTest.RingSwitchingOrientation renaming K → GF2, L → GF4, p → P₄, r → r₀, t → tX₀
open ArkLibTest.RingSwitchingOrientation (beta tp shat beta_zero beta_one sum_one_bit shat_eq
  column_zero row_zero row_one bit_zero_ne_one)

attribute [local instance] ArkLibTest.RingSwitchingOrientation.algebraKL

local instance : SampleableType GF4 := SampleableType.ofFintype GF4

/-- A binding oracle statement over the orientation fixture: it holds the packed polynomial. -/
def exactOStmtIn : AbstractOStmtIn GF4 1 where
  ιₛᵢ := Unit
  OStmtIn := fun _ => MultilinearPoly GF4 1
  Oₛᵢ := fun _ => OracleInterface.instDefault
  initialCompatibility := fun x => x.1 = x.2 ()

/-- The oracle statement committing to the honest packed polynomial `tp`. -/
def oStmt₀ : ∀ j, exactOStmtIn.OStmtIn j := fun _ => tp

/-- An evaluation claim at the zero point. -/
def claimAt (s : GF4) : BatchingStmtIn GF4 2 := ⟨r₀, s⟩

/-- The honest round-zero witness at the accepted statement for `shat` and the zero challenge. -/
def wit₀ : RingSwitching.SumcheckWitness GF4 1 0 where
  t' := tp
  H := projectToMidSumcheckPolyWithParam (L := GF4) (ℓ := 1)
    (param := RingSwitching_SumcheckMultParam 1 GF4 GF2 P₄ 2 1 rfl)
    (ctx := (acceptedStatement P₄ (ℓ' := 1) (claimAt 0) shat 0).ctx) (t := tp) (i := 0)
    (challenges := Fin.elim0)

/-- With one packed variable, a layout-weighted sum is the linear interpolation at the point's
first coordinate. -/
theorem sum_weight (x : Fin 2 → GF4) (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl x) v * f v =
      (1 - x 0) * f (fun _ => 0) + x 0 * f (fun _ => 1) := by
  simp [sum_one_bit, prefixLayout, prefixQuery, Packing.ScalarHead.packedPrefixLayout, eqTilde]

/-- At a point with a Boolean first coordinate, layout-weighted sums select that bit. -/
theorem sum_weight_of_bit (x : Fin 2 → GF4) (b : Fin 2) (hx : x 0 = b)
    (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl x) v * f v = f (fun _ => b) := by
  rw [sum_weight, hx]
  fin_cases b <;> simp

/-- At the zero point, layout-weighted sums select the coordinate at the zero bit. -/
theorem sum_weight_zero (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * f v = f (fun _ => 0) :=
  sum_weight_of_bit r₀ 0 (by simp [r₀]) f

/-- With one batching variable, a batched sum is the linear interpolation at the challenge. -/
theorem sum_batchingWeight (c : Fin 1 → GF4) (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight c u * f u = (1 - c 0) * f (fun _ => 0) + c 0 * f (fun _ => 1) := by
  simp [sum_one_bit, batchingWeight, eqTilde]

/-- At a Boolean challenge, batched sums select that bit. -/
theorem sum_batchingWeight_of_bit (c : Fin 1 → GF4) (b : Fin 2) (hc : c 0 = b)
    (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight c u * f u = f (fun _ => b) := by
  rw [sum_batchingWeight, hc]
  fin_cases b <;> simp

/-- At the zero challenge, batched sums select the coordinate at the zero bit. -/
theorem sum_batchingWeight_zero (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight (0 : Fin 1 → GF4) u * f u = f (fun _ => 0) :=
  sum_batchingWeight_of_bit 0 0 (by simp) f

/-- The second basis vector `Z 1` is nonzero. -/
theorem Z_one_ne_zero : Z 1 ≠ (0 : GF4) := beta_one ▸ beta.ne_zero _

/-- At every challenge, the honest carrier's batched rows are the shared sumcheck claim of the
packed polynomial. -/
theorem honest_sumcheckClaimRel (c : Fin 1 → GF4) :
    (∑ u, batchingWeight c u * P₄.decomposeRows shat u, tp) ∈
      (Packing.PackingData.ofBasis P₄.basis).sumcheckClaimRel 1
        ((prefixLayout P₄ 1).point (prefixQuery P₄ rfl r₀)) (batchingWeight c) := by
  have h := (Packing.PackingData.ofBasis P₄.basis).sumcheckClaim_of_slices (C := GF4)
    (embedded_MLP_eval_sliceRel P₄ rfl tp r₀) (batchingWeight c)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

/-- The honest round is accepted, through `batching_conforms`: compatibility and the structural
invariant hold by construction, the honest batched rows are the shared sumcheck claim, and the
claim `0` is the layout-weighted sum of the columns `(0, 1)`. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 0).original_claim
      (claimAt 0).t_eval_point shat = true ∧
    ((acceptedStatement P₄ (claimAt 0) shat 0, oStmt₀), wit₀) ∈
      sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0 :=
  (batching_conforms P₄ rfl exactOStmtIn (claimAt 0) oStmt₀ shat 0 wit₀).2
    ⟨rfl, (witnessStructuralInvariant_iff P₄ rfl (claimAt 0) shat 0 wit₀).1 rfl,
      honest_sumcheckClaimRel 0, by
        change (0 : GF4) = ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * _
        rw [sum_weight_zero, column_zero]⟩

/-- The zero carrier passes the column check for the claim `0`. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 0 r₀ 0 = true :=
  (check_iff_layout_weight P₄ rfl 0 r₀ 0).2 (by rw [sum_weight_zero, P₄.decomposeColumns_zero]; rfl)

/-- The zero carrier fails the batched target for every output witness: binding fixes the packed
polynomial to `tp`, whose shared sumcheck claim is the honest batched value `Z 1`, not `0`. -/
example (wit : RingSwitching.SumcheckWitness GF4 1 0) :
    ¬ (performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 0).original_claim
        (claimAt 0).t_eval_point 0 = true ∧
      ((acceptedStatement P₄ (claimAt 0) 0 0, oStmt₀), wit) ∈
        sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0) := by
  intro h
  obtain ⟨hcomp, -, hclaim, -⟩ := (batching_conforms P₄ rfl exactOStmtIn _ _ _ _ wit).1 h
  rw [show wit.t' = tp from hcomp] at hclaim
  have h0 := (show _ = _ from hclaim).trans (show _ = _ from honest_sumcheckClaimRel 0).symm
  rw [sum_batchingWeight_zero, sum_batchingWeight_zero, P₄.decomposeRows_zero, shat_eq,
    row_zero] at h0
  exact Z_one_ne_zero h0.symm

/-- For the false claim `1`, no carrier and no output witness is accepted at the zero batching
challenge: the target forces row zero to be `Z 1`, the check forces column zero to be `1`, and the
shared transpose makes the zero coordinate of row zero that of column zero. -/
example (z : P₄.A) (wit : RingSwitching.SumcheckWitness GF4 1 0) :
    ¬ (performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 1).original_claim
        (claimAt 1).t_eval_point z = true ∧
      ((acceptedStatement P₄ (claimAt 1) z 0, oStmt₀), wit) ∈
        sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0) := by
  intro h
  obtain ⟨hcomp, -, hclaim, hs⟩ := (batching_conforms P₄ rfl exactOStmtIn _ _ _ _ wit).1 h
  rw [show wit.t' = tp from hcomp] at hclaim
  have hrow : P₄.decomposeRows z (fun _ => 0) = Z 1 := by
    have h0 := (show _ = _ from hclaim).trans (show _ = _ from honest_sumcheckClaimRel 0).symm
    rwa [sum_batchingWeight_zero, sum_batchingWeight_zero, shat_eq, row_zero] at h0
  have hcol : (1 : GF4) =
      ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * P₄.decomposeColumns z v := hs
  rw [sum_weight_zero] at hcol
  have key := (Packing.PackingData.ofBasis P₄.basis).repr_transpose (P₄.decomposeColumns z)
    (fun _ => 0) (fun _ => 0)
  rw [P₄.transpose_decomposeColumns, hrow, ← hcol, ← beta_one, ← beta_zero] at key
  change beta.repr (beta _) _ = beta.repr (beta _) _ at key
  rw [Basis.repr_self, Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne] at key
  · exact zero_ne_one key
  · exact fun h => absurd (congrFun h 0) (by decide)

/-- The honest carrier's columns open the components of the source `tX₀ = X₀` at the retained
point. -/
theorem columns_openingClaimRel :
    ((P₄.decomposeColumns shat, (prefixLayout P₄ 1).point (prefixQuery P₄ rfl r₀)),
        (prefixLayout P₄ 1).components (sourceDimensionEquiv rfl tX₀)) ∈
      (Packing.PackingData.ofBasis P₄.basis).openingClaimRel 1 :=
  (embedded_MLP_eval_packMLE_eq_iff_openingClaimRel P₄ rfl tX₀ r₀ shat).1 rfl

/-- Its rows `(Z 1, 0)` do not open them, so swapping rows and columns is caught. -/
example : ((P₄.decomposeRows shat, (prefixLayout P₄ 1).point (prefixQuery P₄ rfl r₀)),
      (prefixLayout P₄ 1).components (sourceDimensionEquiv rfl tX₀)) ∉
    (Packing.PackingData.ofBasis P₄.basis).openingClaimRel 1 := by
  intro h
  have h0 : P₄.decomposeRows shat (fun _ => 0) = P₄.decomposeColumns shat (fun _ => 0) :=
    (h _).trans (columns_openingClaimRel _).symm
  rw [column_zero, shat_eq, row_zero] at h0
  exact Z_one_ne_zero h0

/-- A source in the retained variable, `t₁ = X₁`. -/
def t₁ : MultilinearPoly GF2 2 :=
  ⟨X 1, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    simp only [degreeOf_X]
    split <;> omega⟩

/-- The honest carrier of `t₁` at a point with retained coordinate `Z 1`. -/
def shat₁ : P₄.A :=
  embedded_MLP_eval 1 GF4 GF2 P₄ 2 1 rfl (packMLE 1 GF4 GF2 2 1 rfl beta t₁) ![0, Z 1]

/-- Both columns of `shat₁` are `Z 1`: the honest check reads column `b` back as `t₁(b, Z 1)`
at the packed prefix `b`, and the carrier does not depend on the prefix. -/
theorem columns_shat₁ (v : Fin 1 → Fin 2) : P₄.decomposeColumns shat₁ v = Z 1 := by
  have hcol (b : Fin 2) : P₄.decomposeColumns shat₁ (fun _ => b) = Z 1 := by
    have h := (check_iff_layout_weight P₄ rfl _ _ _).1
      (performCheckOriginalEvaluation_honest P₄ rfl t₁ ![(b : GF4), Z 1])
    rw [sum_weight_of_bit _ b (by simp)] at h
    exact h.symm.trans (by simp [t₁])
  obtain ⟨b, rfl⟩ : ∃ b : Fin 2, v = fun _ => b := ⟨v 0, funext fun i => by fin_cases i; rfl⟩
  exact hcol b

/-- Row zero of `shat₁` is `0`: its coordinates are the zero coordinates of the columns `Z 1`,
through the shared transpose. -/
theorem row_zero_shat₁ : P₄.decomposeRows shat₁ (fun _ => 0) = 0 := by
  refine beta.repr.injective (Finsupp.ext fun v => ?_)
  have h := (Packing.PackingData.ofBasis P₄.basis).repr_transpose (P₄.decomposeColumns shat₁)
    (fun _ => 0) v
  rw [P₄.transpose_decomposeColumns, columns_shat₁, ← beta_one] at h
  change beta.repr _ v = beta.repr (beta _) _ at h
  rw [h, Basis.repr_self, map_zero, Finsupp.zero_apply]
  exact Finsupp.single_eq_of_ne fun h => absurd (congrFun h 0) (by decide)

/-- At the nonconstant source `t₁` and the point `(0, Z 1)`, the honest check accepts the true
claim `t₁(0, Z 1) = Z 1`, which is the column read-back. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (Z 1) ![0, Z 1] shat₁ = true := by
  have h := performCheckOriginalEvaluation_honest P₄ rfl t₁ ![0, Z 1]
  rwa [show aeval ![0, Z 1] t₁.val = Z 1 by simp [t₁]] at h

/-- Reading the claim back from the rows instead gives `0`, so a row/column swap rejects the
honest claim. -/
example : Z 1 ≠ ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl ![0, Z 1]) v *
    P₄.decomposeRows shat₁ v := by
  rw [sum_weight_of_bit _ 0 (by simp), row_zero_shat₁]
  exact Z_one_ne_zero

/-! ### A packed/retained swap

At `t = X₀` and the point `(Z 1, 0)`, the honest carrier is still `shat`, which depends only on the
retained coordinate `0`. The prefix-weighted columns read back the true claim `Z 1`; weighting the
columns by the retained coordinate instead reads back column zero, `0`. -/

/-- The honest carrier at `(Z 1, 0)` is `shat`. -/
theorem carrier_Z_one_zero : embedded_MLP_eval 1 GF4 GF2 P₄ 2 1 rfl tp ![Z 1, 0] = shat := by
  unfold shat embedded_MLP_eval
  dsimp only
  congr 2
  funext i
  fin_cases i
  simp [r₀]

/-- The honest check at `(Z 1, 0)` accepts the true claim `X₀(Z 1, 0) = Z 1`. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (Z 1) ![Z 1, 0] shat = true := by
  have h := performCheckOriginalEvaluation_honest P₄ rfl tX₀ ![Z 1, 0]
  rw [show aeval ![Z 1, 0] tX₀.val = Z 1 by simp [tX₀]] at h
  rw [← carrier_Z_one_zero]
  exact h

/-- Weighting the columns of `shat` by the retained coordinate of `(Z 1, 0)` instead of the packed
one gives `0`, so a packed/retained swap rejects the honest claim. -/
example : Z 1 ≠ ∑ v : Fin 1 → Fin 2,
    eqTilde (v : Fin 1 → GF4) (getEvaluationPointSuffix 1 GF4 2 1 rfl ![Z 1, 0]) *
      P₄.decomposeColumns shat v := by
  simp only [sum_one_bit, column_zero]
  simp [eqTilde, getEvaluationPointSuffix, Z_one_ne_zero]

/-! ### Regression fixtures for the disclosed limits -/

/-- The honest round-zero witness at the challenge `1`. -/
def wit₁ : RingSwitching.SumcheckWitness GF4 1 0 where
  t' := tp
  H := projectToMidSumcheckPolyWithParam (L := GF4) (ℓ := 1)
    (param := RingSwitching_SumcheckMultParam 1 GF4 GF2 P₄ 2 1 rfl)
    (ctx := (acceptedStatement P₄ (ℓ' := 1) (claimAt 0) shat 1).ctx) (t := tp) (i := 0)
    (challenges := Fin.elim0)

/-- The carrier is not pinned by acceptance: at the challenge `1` the zero carrier, which is not
`shat`, passes the check and its accepted output is in the round-zero relation with the honest
witness. Over `GF(4)` the honest batched target is `(1 - c) • Z 1`, so this collision happens at
exactly one of the `4` challenges, the rate `κ/|L|` of `compute_s0_collision_le`. -/
theorem zero_carrier_collides :
    (0 : P₄.A) ≠ shat ∧
    performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 0).original_claim
      (claimAt 0).t_eval_point 0 = true ∧
    ((acceptedStatement P₄ (claimAt 0) 0 1, oStmt₀), wit₁) ∈
      sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0 := by
  have hone : (1 : Fin 1 → GF4) 0 = ((1 : Fin 2) : GF4) := by simp
  refine ⟨fun h => ?_, (batching_conforms P₄ rfl exactOStmtIn (claimAt 0) oStmt₀ 0 1 wit₁).2
    ⟨rfl, (witnessStructuralInvariant_iff P₄ rfl (claimAt 0) 0 1 wit₁).1 rfl, ?_, ?_⟩⟩
  · have h0 := congrArg (fun z => P₄.decomposeRows z (fun _ => 0)) h
    simp only [P₄.decomposeRows_zero, shat_eq, row_zero, Pi.zero_apply] at h0
    exact Z_one_ne_zero h0.symm
  · have h := honest_sumcheckClaimRel 1
    rw [sum_batchingWeight_of_bit _ 1 hone, shat_eq, row_one] at h
    change _ = _
    rw [sum_batchingWeight_of_bit _ 1 hone, P₄.decomposeRows_zero]
    exact h
  · change (0 : GF4) = ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * _
    rw [sum_weight_zero, P₄.decomposeColumns_zero]
    rfl

/-- The oracle statement committing to the zero polynomial. -/
def oStmtZero : ∀ j, exactOStmtIn.OStmtIn j := fun _ => (0 : MultilinearPoly GF4 1)

/-- The abort on rejection, pinned: the check rejects the claim `1` at the honest carrier, and the
production verifier then aborts on every transcript sending that carrier. Before the repair it
returned a dummy statement that lay in the round-zero relation. -/
theorem failedCheck_aborts (tr : (pSpecBatching 1 GF4 GF2 P₄).FullTranscript)
    (htr : tr.messages ⟨0, rfl⟩ = shat) :
    performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 1).original_claim
      (claimAt 1).t_eval_point shat = false ∧
    (BatchingPhase.oracleVerifier 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn).toVerifier.verify
      (claimAt 1, oStmtZero) tr = failure := by
  have hcheck : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (claimAt 1).original_claim
      (claimAt 1).t_eval_point shat = false := by
    rw [Bool.eq_false_iff]
    intro h
    have hs := (check_iff_layout_weight P₄ rfl _ _ _).1 h
    change (1 : GF4) = ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * _ at hs
    rw [sum_weight_zero, column_zero] at hs
    exact one_ne_zero hs
  refine ⟨hcheck, ?_⟩
  rw [BatchingPhase.oracleVerifier, scalarRoundOracleVerifier_verify, htr, hcheck]
  rfl

/-- The claim of the `failedCheck_aborts` fixture is in the batching input relation for no
witness. -/
theorem claimAt_one_not_mem_batchingInputRelation (wit : BatchingWitIn GF4 GF2 2 1) :
    ((claimAt 1, oStmtZero), wit) ∉
      BatchingPhase.batchingInputRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn := by
  intro h
  obtain ⟨ht', hs, hcomp⟩ := (mem_batchingInputRelation_iff_layout P₄ rfl _ _ _ _).1 h
  have h0 : (Packing.PackingData.ofBasis P₄.basis).packedMLE
      ((prefixLayout P₄ 1).components (sourceDimensionEquiv rfl wit.t)) = 0 :=
    ht'.symm.trans hcomp
  have hc := congrArg (Packing.PackingData.ofBasis P₄.basis).unpack h0
  rw [Packing.PackingData.unpack_packedMLE] at hc
  change (1 : GF4) = _ at hs
  rw [hc] at hs
  have hu : ∀ v, ((Packing.PackingData.ofBasis P₄.basis).unpack
      (0 : MultilinearPoly GF4 1) v).val = 0 := fun v => by
    ext d
    rw [Packing.PackingData.unpack_coeff]
    simp
  simp [hu] at hs

end Concrete

end ArkLibTest.RingSwitchingConformance.Binius

end
