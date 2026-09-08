/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ExactCommitment
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Security
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete scalar-head acceptance and layout regressions

The ordinary fixture distinguishes a packed prefix from a packed suffix using a nonconstant
source. The quirky fixture uses two skipped nodes, an extra Boolean coordinate and an off-grid
univariate query. Tests exercise the actual source relation, verifier and full reduction rejection.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.ScalarHead

open MvPolynomial Module OracleSpec OracleComp ProtocolSpec ProbabilityTheory
open RingSwitching.Packing.ScalarHead

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev ordinaryData : PackingData (ZMod 5) where
  P := (Fin 1 → Fin 2) → ZMod 5
  E := ZMod 5
  ιP := Fin 1 → Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

abbrev dp := dp24Layout ordinaryData 1 1 (Equiv.refl _)
abbrev flock := flockLayout ordinaryData 1 1 (Equiv.refl _)
abbrev pc := ExactPackedCommitment.polynomialOracle ordinaryData.P 1

def source : (ZMod 5)⦃≤ 1⦄[X Fin 2] :=
  ⟨MLE (fun v => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5)), MLE_mem_restrictDegree _⟩

/-- Fixing the first coordinate to one leaves value one at retained zero. -/
theorem prefix_component :
    eval (fun _ => (0 : ZMod 5)) (dp.components source (fun _ => 1)).val = 1 := by
  change eval (fun _ => (0 : ZMod 5)) (splitFirst 1 1 source (fun _ => 1)).val = 1
  have hs := splitFirst_eval 1 1 source (fun _ => 1) (fun _ => 0)
  have hp := congrArg (fun r => eval r source.val)
    (cast_append_bool (R := ZMod 5) 1 1 (fun _ => 1) (fun _ => 0))
  have ht := MLE_eval_zeroOne (R := ZMod 5)
    (Fin.append (fun _ : Fin 1 => (1 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2)))
    (fun v : Fin 2 → Fin 2 => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5))
  have he := hs.trans (hp.symm.trans ht)
  change eval (fun _ => (0 : ZMod 5)) (splitFirst 1 1 source (fun _ => 1)).val =
    1 + 2 * 0 at he
  simpa only [mul_zero, add_zero] using he

/-- Fixing the last coordinate to one leaves value two at retained zero. -/
theorem suffix_component :
    eval (fun _ => (0 : ZMod 5)) (flock.components source (fun _ => 1)).val = 2 := by
  change eval (fun _ => (0 : ZMod 5)) (splitLast 1 1 source (fun _ => 1)).val = 2
  have hs := splitLast_eval 1 1 source (fun _ => 1) (fun _ => 0)
  have hp := congrArg (fun r => eval r source.val)
    (cast_append_bool (R := ZMod 5) 1 1 (fun _ => 0) (fun _ => 1))
  have ht := MLE_eval_zeroOne (R := ZMod 5)
    (Fin.append (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)))
    (fun v : Fin 2 → Fin 2 => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5))
  have he := hs.trans (hp.symm.trans ht)
  change eval (fun _ => (0 : ZMod 5)) (splitLast 1 1 source (fun _ => 1)).val =
    0 + 2 * 1 at he
  simpa only [mul_one, zero_add] using he

/-- The two source-coordinate orders produce different actual component polynomials. -/
theorem prefix_suffix_distinct : dp.components source ≠ flock.components source := by
  intro h
  have he := congrArg (fun ps => eval (fun _ => (0 : ZMod 5)) (ps (fun _ => 1)).val) h
  rw [prefix_component, suffix_component] at he
  exact (by decide : (1 : ZMod 5) ≠ 2) he

def query : dp.Query := (fun _ => 1, fun _ => 2)
def stmt : Input ordinaryData 1 dp := (query, dp.eval query source)
def ost := pc.commit (ordinaryData.packedMLE (dp.components source))
def α := partials ordinaryData 1 dp query (dp.components source)

/-- A concrete original scalar claim has the nonconstant source as an actual witness. -/
theorem source_related : ((stmt, ost), source) ∈ relIn ordinaryData 1 dp pc :=
  relIn_honest ordinaryData 1 dp pc query source

/-- The honest family is accepted by the materialized scalar-head verifier. -/
theorem ordinary_accept :
    (verifier ordinaryData 1 dp pc).toVerifier.verify (stmt, ost) (transcript ordinaryData α) =
      pure (nextStatement ordinaryData 1 dp stmt α, ost) := by
  rw [verifier_verify]
  exact if_pos (honest_check ordinaryData 1 dp pc source_related)

def falseStmt : Input ordinaryData 1 dp := (query, stmt.2 + 1)

/-- Altering the scalar by one fails even with the same otherwise correct family and commitment. -/
theorem false_check : ¬ check ordinaryData 1 dp falseStmt α := by
  intro h
  have ht := honest_check ordinaryData 1 dp pc source_related
  change stmt.2 + 1 = ∑ i, dp.weight stmt.1 i * α i at h
  change stmt.2 = ∑ i, dp.weight stmt.1 i * α i at ht
  rw [← ht] at h
  exact (by decide : (1 : ZMod 5) ≠ 0) (add_left_cancel (h.trans (add_zero _).symm))

/-- The complete production reduction aborts, rather than forwarding a false scalar claim. -/
theorem false_reduction :
    ((reduction ordinaryData 1 dp pc).toReduction.run (falseStmt, ost) source).run = pure none := by
  exact (reduction_run ordinaryData 1 dp pc falseStmt ost source).trans
    (congrArg pure (if_neg false_check))

/-- The production DP24 head supplies the zero-error worst-case contract at every initial state. -/
theorem ordinary_worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn ordinaryData 1 dp pc) (relOut ordinaryData 1 pc)
      (verifier ordinaryData 1 dp pc).toVerifier
      (WitMid ordinaryData 1 dp) (extractor ordinaryData 1 dp pc)
      (knowledgeStateFunction ordinaryData 1 dp pc init impl) (fun _ => 0) :=
  rbrKnowledgeSoundnessWorstCaseWith ordinaryData 1 dp pc init impl

/-- The production head is perfectly complete uniformly over initial oracle states. -/
theorem ordinary_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction ordinaryData 1 dp pc).perfectCompleteness init impl
      (relIn ordinaryData 1 dp pc) (relOut ordinaryData 1 pc) :=
  perfectCompleteness ordinaryData 1 dp pc init impl

abbrev quirkyData : PackingData (ZMod 5) where
  P := ((Fin 1 → Fin 2) × Fin 2) → ZMod 5
  E := ZMod 5
  ιP := (Fin 1 → Fin 2) × Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

local instance : Fact (IsField quirkyData.E) := ⟨Field.toIsField (ZMod 5)⟩

/-- The two skipped Boolean indices enumerate field nodes zero and two, not Boolean nodes. -/
def skipNodes : (Fin 1 → Fin 2) ↪ quirkyData.E where
  toFun σ := 2 * (σ 0 : ZMod 5)
  inj' σ τ h := by
    funext i
    fin_cases i
    have he := mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (σ 0).isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (τ 0).isLt (by decide))] at hv
    exact Fin.ext hv

abbrev quirky := flockQuirkyLayout quirkyData 1 1 skipNodes (Equiv.refl _)
abbrev quirkyPC := ExactPackedCommitment.polynomialOracle quirkyData.P 1

def quirkySource : QuirkyTable (B := ZMod 5) 1 1 :=
  fun yb σ => (yb.1 0 : ZMod 5) + 2 * (σ 0 : ZMod 5) + 3 * (yb.2 : ZMod 5)

def quirkyQuery : quirky.Query := (fun _ => 2, 3, 4)
def quirkyStmt : Input quirkyData 1 quirky := (quirkyQuery, quirky.eval quirkyQuery quirkySource)
def quirkyOracle := quirkyPC.commit (quirkyData.packedMLE (quirky.components quirkySource))
def quirkyPartials := partials quirkyData 1 quirky quirkyQuery (quirky.components quirkySource)

/-- The actual quirky scalar relation is inhabited at an off-grid univariate query. -/
theorem quirky_related :
    ((quirkyStmt, quirkyOracle), quirkySource) ∈ relIn quirkyData 1 quirky quirkyPC :=
  relIn_honest quirkyData 1 quirky quirkyPC quirkyQuery quirkySource

/-- The unusual skipped/extra order selects the actual table value at its retained Boolean point. -/
theorem quirky_component_order :
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 1), 0)).val = 2 ∧
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 0), 1)).val = 3 := by
  constructor <;>
    change eval (fun _ => (0 : ZMod 5)) (MLE _) = _ <;>
    rw [show (fun _ : Fin 1 => (0 : ZMod 5)) =
      ((fun _ : Fin 1 => (0 : Fin 2)) : Fin 1 → ZMod 5) from rfl, MLE_eval_zeroOne] <;>
    norm_num [quirkySource]

/-- The non-Boolean skip node selects its own section with weight one. -/
theorem quirky_weight_node :
    quirkyWeight quirkyData 1 skipNodes 0 (skipNodes (fun _ => 1)) ((fun _ => 1), 0) = 1 := by
  let : Field quirkyData.E := (show IsField quirkyData.E from Fact.out).toField
  unfold quirkyWeight
  rw [Lagrange.eval_basis_self skipNodes.injective.injOn (Finset.mem_univ _)]
  norm_num [eqTilde, eqPolynomial, singleEqPolynomial]

/-- The production verifier accepts the Lagrange-weighted claim at the off-grid point. -/
theorem quirky_accept :
    (verifier quirkyData 1 quirky quirkyPC).toVerifier.verify (quirkyStmt, quirkyOracle)
      (transcript quirkyData quirkyPartials) =
      pure (nextStatement quirkyData 1 quirky quirkyStmt quirkyPartials, quirkyOracle) := by
  rw [verifier_verify]
  exact if_pos (honest_check quirkyData 1 quirky quirkyPC quirky_related)

/-- The quirky layout supplies the actual production worst-case knowledge theorem. -/
theorem quirky_worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn quirkyData 1 quirky quirkyPC) (relOut quirkyData 1 quirkyPC)
      (verifier quirkyData 1 quirky quirkyPC).toVerifier
      (WitMid quirkyData 1 quirky) (extractor quirkyData 1 quirky quirkyPC)
      (knowledgeStateFunction quirkyData 1 quirky quirkyPC init impl) (fun _ => 0) :=
  rbrKnowledgeSoundnessWorstCaseWith quirkyData 1 quirky quirkyPC init impl

/-- State-aware completeness also applies to the original Lagrange-interpolated quirky claim. -/
theorem quirky_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction quirkyData 1 quirky quirkyPC).perfectCompleteness init impl
      (relIn quirkyData 1 quirky quirkyPC) (relOut quirkyData 1 quirkyPC) :=
  perfectCompleteness quirkyData 1 quirky quirkyPC init impl

end RingSwitching.Packing.Tests.ScalarHead

end
