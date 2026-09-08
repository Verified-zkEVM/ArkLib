/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Phase

/-! # Prover factorization and full-reduction scalar rejection -/

noncomputable section

namespace RingSwitching.Packing.ScalarFamily

open MvPolynomial OracleSpec OracleComp ProtocolSpec

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ScalarHead.ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

omit [Algebra B C] [IsScalarTower B data.P C] in
/--
The composed prover sends the partial-evaluation family, then runs the full-family prover with
the same oracle and a transported challenge query.
-/
theorem prover_run (stmt : ScalarHead.Input data m layout) (ost : ∀ j, pc.OStmt j)
    (p : layout.Source) :
    (reduction data m layout bat pc).prover.run (stmt, ost) p = (do
      let α := ScalarHead.partials data m layout stmt.1 (layout.components p)
      let rest ← liftAppendRight (ScalarHead.pSpec data)
        ((FullFamily.prover data m bat pc).run
          (ScalarHead.nextStatement data m layout stmt α, ost) (layout.components p))
      pure (ScalarHead.transcript data α ++ₜ rest.1, rest.2)) := by
  change ((ScalarHead.prover data m layout pc).append (FullFamily.prover data m bat pc)).run
    (stmt, ost) p = _
  rw [Prover.append_run, ScalarHead.prover_run]
  simp only [liftAppendLeft, liftM_pure, pure_bind]

omit [Algebra B C] [IsScalarTower B data.P C] in
/--
A false scalar check rejects the composed reduction, including after the suffix prover's
challenge query.
-/
theorem reduction_reject_scalar (stmt : ScalarHead.Input data m layout) (ost : ∀ j, pc.OStmt j)
    (p : layout.Source)
    (hc : ¬ ScalarHead.check data m layout stmt
      (ScalarHead.partials data m layout stmt.1 (layout.components p))) :
    ((reduction data m layout bat pc).toReduction.run (stmt, ost) p).run = (do
      let α := ScalarHead.partials data m layout stmt.1 (layout.components p)
      let _ ← liftAppendRight (ScalarHead.pSpec data)
        ((FullFamily.prover data m bat pc).run
          (ScalarHead.nextStatement data m layout stmt α, ost) (layout.components p))
      pure none) := by
  classical
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm data m layout bat pc)]
  change ((reduction data m layout bat pc).prover.run (stmt, ost) p >>= _) = _
  rw [prover_run, bind_assoc]
  apply bind_congr
  intro rest
  have hg : (guardedForm data m layout bat pc).check (stmt, ost)
      (ScalarHead.transcript data
        (ScalarHead.partials data m layout stmt.1 (layout.components p)) ++ₜ rest.1) = false := by
    change ((ScalarHead.guardedForm data m layout pc).check (stmt, ost) _ && _) = false
    rw [FullTranscript.append_fst]
    change (decide (ScalarHead.check data m layout stmt
      (ScalarHead.partials data m layout stmt.1 (layout.components p))) && _) = false
    rw [decide_eq_false_iff_not.mpr hc, Bool.false_and]
  simp only [pure_bind, hg, Bool.false_eq_true, if_false]

end RingSwitching.Packing.ScalarFamily

end
