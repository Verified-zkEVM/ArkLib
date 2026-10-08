/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.General

/-!
# A direct opening protocol for ring switching's downstream claim

A concrete `MLIOPCS` over any commutative ring `L`, used to show that the hypotheses of the full
ring-switching composite can hold together. The oracle statement is the multilinear polynomial
itself (`oStmtIn`), and the opening has no rounds: the verifier reads the polynomial from its
oracle and accepts exactly when the claimed evaluation is its value at the claimed point.

* `verifier_rbrKnowledgeSoundnessWorstCase`: the verifier is worst-case round-by-round knowledge
  sound at `oStmtIn.toRelInput`, at every error. The extractor reads the witness off the oracle
  statement.
* `oracleProof_perfectCompleteness`: the honest prover, which sends nothing, is accepted on every
  input with an honest oracle statement.
* `mliopcs`: the opening as an `MLIOPCS`. Its averaged knowledge-soundness field is filled from the
  worst-case proof by
  `OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`, and
  `mliopcs_rbrKnowledgeSoundWorstCase` is its worst-case hypothesis.
-/

open OracleSpec OracleComp ProtocolSpec RingSwitching
open scoped NNReal
open Sumcheck.Structured

namespace ArkLibTest.RingSwitchingConformance.DirectOpening

variable {L : Type} [CommRing L] [DecidableEq L] {ℓ' : ℕ}

/-- The binding oracle statement: one oracle, which holds the multilinear polynomial itself. -/
def oStmtIn : AbstractOStmtIn L ℓ' where
  ιₛᵢ := Unit
  OStmtIn := fun _ => MultilinearPoly L ℓ'
  Oₛᵢ := fun _ => OracleInterface.instDefault
  initialCompatibility := fun x => x.1 = x.2 ()

/-- The zero-round opening verifier: it reads the polynomial from its oracle and accepts exactly
when the claimed evaluation is the polynomial's value at the claimed point. -/
def verifier : OracleProofVerifier []ₒ (MLPEvalStatement L ℓ')
    (oStmtIn (L := L) (ℓ' := ℓ')).OStmtIn (!p[] : ProtocolSpec 0) :=
  OracleProofVerifier.ofVerify (fun stmt _ => do
    let t : MultilinearPoly L ℓ' ←
      query (spec := [(oStmtIn (L := L) (ℓ' := ℓ')).OStmtIn]ₒ) ⟨(), ()⟩
    return decide (stmt.original_claim = MvPolynomial.eval stmt.t_eval_point t.val))

/-- The opening verifier's guard and verdict as data, over the empty ambient oracle. The verifier
never rejects, so the fallback verdict is never used. -/
noncomputable def guardedForm : (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
    (verifier (L := L) (ℓ' := ℓ'))).GuardedForm :=
  Verifier.GuardedForm.ofEmpty _ (fun _ => (false, isEmptyElim))

/-- The opening's verdict is the evaluation check on the polynomial held by the oracle. -/
theorem guardedForm_out_fst
    (s : MLPEvalStatement L ℓ' × ∀ j, (oStmtIn (L := L) (ℓ' := ℓ')).OStmtIn j)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    ((guardedForm (L := L) (ℓ' := ℓ')).out s tr).1 =
      decide (s.1.original_claim = MvPolynomial.eval s.1.t_eval_point (s.2 ()).val) := rfl

/-- The opening verifier is worst-case round-by-round knowledge sound at every error: it has no
challenges, and on acceptance the polynomial held by the oracle is a witness for the claim. -/
theorem verifier_rbrKnowledgeSoundnessWorstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (err : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0) :
    OracleProof.rbrKnowledgeSoundnessWorstCase init impl
      (oStmtIn (L := L) (ℓ' := ℓ')).toRelInput verifier err := by
  refine ⟨fun _ => WitMLP L ℓ',
    { eqIn := rfl
      extractMid := fun i => Fin.elim0 i
      extractOut := fun s _ _ => ⟨s.2 ()⟩ },
    { toFun := fun _ s _ w => (s, w) ∈ (oStmtIn (L := L) (ℓ' := ℓ')).toRelInput
      toFun_empty := fun _ _ => Iff.rfl
      toFun_next := fun m => Fin.elim0 m
      toFun_full := fun s tr _ h => ?_ },
    fun _ i => Fin.elim0 i.1⟩
  obtain ⟨-, hp⟩ := (guardedForm (L := L) (ℓ' := ℓ')).check_and_of_prEvent_pos h
  have hacc : ((guardedForm (L := L) (ℓ' := ℓ')).out s tr).1 = true := by
    revert hp
    generalize (guardedForm (L := L) (ℓ' := ℓ')).out s tr = o
    intro hp
    simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    exact congrArg Prod.fst hp.1
  have hclaim : decide (s.1.original_claim = MvPolynomial.eval s.1.t_eval_point (s.2 ()).val) =
      true := (guardedForm_out_fst s tr).symm.trans hacc
  have hrel := of_decide_eq_true hclaim
  exact ⟨hrel, rfl⟩

/-- The honest opening prover: it sends nothing and outputs acceptance. -/
def prover : OracleProver []ₒ (MLPEvalStatement L ℓ') (oStmtIn (L := L) (ℓ' := ℓ')).OStmtIn
    (WitMLP L ℓ') Bool (fun _ : Empty => Unit) Unit (!p[] : ProtocolSpec 0) where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun _ => pure ((true, isEmptyElim), ())

/-- The zero-round opening as an oracle proof. -/
def oracleProof : OracleProof []ₒ (MLPEvalStatement L ℓ') (oStmtIn (L := L) (ℓ' := ℓ')).OStmtIn
    (WitMLP L ℓ') (!p[] : ProtocolSpec 0) :=
  OracleReduction.mk (Oₛₒ := fun i : Empty => nomatch i) prover verifier

/-- The opening is perfectly complete on inputs with an honest oracle statement: the oracle holds
the witness polynomial, so the claimed evaluation passes the check. -/
theorem oracleProof_perfectCompleteness {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)} :
    OracleProof.perfectCompleteness init impl (oStmtIn (L := L) (ℓ' := ℓ')).toStrictRelInput
      oracleProof := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro s w ⟨hclaim, hcomp⟩ x hx
  have hrun : ((OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (oracleProof (L := L) (ℓ' := ℓ'))).run s w).run =
      (pure (some ((default, ((true, isEmptyElim), ())),
        (guardedForm (L := L) (ℓ' := ℓ')).out s default)) : OracleComp _ _) := rfl
  erw [hrun, support_pure, Set.mem_singleton_iff] at hx
  subst hx
  have hacc : ((guardedForm (L := L) (ℓ' := ℓ')).out s default).1 = true := by
    refine (guardedForm_out_fst s default).trans ?_
    change _ = MvPolynomial.eval _ (w.t : MvPolynomial (Fin ℓ') L) at hclaim
    change w.t = s.2 () at hcomp
    rw [hcomp] at hclaim
    exact decide_eq_true hclaim
  have hout : (guardedForm (L := L) (ℓ' := ℓ')).out s default = (true, isEmptyElim) :=
    Prod.ext hacc (Subsingleton.elim _ _)
  refine ⟨_, rfl, ?_, hout.symm⟩
  change ((guardedForm (L := L) (ℓ' := ℓ')).out s default, ()) ∈ acceptRejectOracleRel
  rw [hout]
  rfl

/-- The direct opening as an `MLIOPCS`, at error `0`. Its averaged round-by-round knowledge
soundness field is filled from the worst-case proof. -/
noncomputable def mliopcs : MLIOPCS L ℓ' where
  toAbstractOStmtIn := oStmtIn
  numRounds := 0
  pSpec := !p[]
  Oₘ := inferInstance
  O_challenges := inferInstance
  oracleReduction := oracleProof
  perfectCompleteness := oracleProof_perfectCompleteness
  rbrKnowledgeError := fun _ => 0
  rbrKnowledgeSoundness :=
    OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
      (verifier_rbrKnowledgeSoundnessWorstCase _ _ _)

/-- The direct opening satisfies the worst-case hypothesis of the full ring-switching composite. -/
theorem mliopcs_rbrKnowledgeSoundWorstCase :
    (mliopcs (L := L) (ℓ' := ℓ')).RbrKnowledgeSoundWorstCase :=
  verifier_rbrKnowledgeSoundnessWorstCase _ _ _

end ArkLibTest.RingSwitchingConformance.DirectOpening
