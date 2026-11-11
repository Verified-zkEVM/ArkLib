/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# The trace head's soundness depends on its check

A verifier with the same output map but no trace check is not coordinate-wise special sound for
the trace head's relations with the head's own extractor `traceHeadExtractor`. This pins that
`traceHeadVerifier_coordinateWiseSpecialSoundWith` is not vacuous: with that extractor, its content
is the check. It does not refute the existential form (some extractor), since another weak opening
of the same commitment could satisfy the scalar relation.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter
open OracleComp OracleSpec ProtocolSpec CoordinateWise

namespace HachiTraceHeadRubberStampTest

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
private theorem hk : 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide

open HachiTraceHeadTest

/-- The trace head's verifier with the check deleted. -/
def rubber {ι : Type} {oSpec : OracleSpec ι} : Verifier oSpec
    (Statement 5 1 0 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1)
    (PolyEvalStatement Φ 1 (Nat.clog 2 5) 1 (Nat.clog 2 5) 1 0 1) (pSpecTraceHead (q := 5) 1) where
  verify := fun s tr => pure (output 1 0 s (tr 0))

/-- Deleting the trace check makes coordinate-wise special soundness with `traceHeadExtractor`
false, so the head's certificate at that extractor depends on the check: a false claim with the
honest committer's opening is accepted, and the extractor's witness, the leaf's weak opening, does
not satisfy the scalar relation. -/
theorem rubber_not_cwss {ι : Type} (oSpec : OracleSpec ι)
    (impl : QueryImpl oSpec (StateT Unit ProbComp)) :
    ¬ Verifier.coordinateWiseSpecialSoundWith (pure ()) impl CWSSStructure.ofIsEmpty
      (TraceHead.relScalarEval 1 0 hk h2 pp 2 6 1 1) (relPolyEval Φ pp 2 6 1 1)
      (rubber (oSpec := oSpec)) (traceHeadExtractor 1 0) := by
  intro h
  let tree : ChallengeTree (pSpecTraceHead (q := 5) 1)
      (CWSSStructure.ofIsEmpty (pSpec := pSpecTraceHead (q := 5) 1)).toShape.arity 0 :=
    .msgNode 0 rfl (honestMessage 1 0 2 s w) .leaf
  have hout : (output 1 0 bad (honestMessage 1 0 2 s w), w) ∈ relPolyEval Φ pp 2 6 1 1 :=
    output_mem_relPolyEval_of_mem_relScalarEval 1 0 hk h2 pp 2 6 1 1 s w source_valid.1
  have hacc : tree.IsAccepting (pure ()) impl (rubber (oSpec := oSpec)) bad
      (relPolyEval Φ pp 2 6 1 1).language := by
    intro tr htr
    have htr' : tr 0 = honestMessage 1 0 2 s w := by
      rcases List.mem_singleton.1 htr with rfl
      rfl
    refine OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support (pure ()) impl _ _ ?_
    intro o ho
    exact ⟨_, ho, (Set.mem_language_iff _ _).2 ⟨w, by rw [htr']; exact hout⟩⟩
  have htr0 : ∀ p : tree.LeafPath, p.fullTranscript 0 = honestMessage 1 0 2 s w := by
    intro p
    rcases List.mem_singleton.1 p.mem_fullTranscripts with h
    rw [h]; rfl
  have hvalid : ChallengeTree.LeafWitnesses.IsValid (pure ()) impl (rubber (oSpec := oSpec))
      (relPolyEval Φ pp 2 6 1 1) bad (fun _ => some w : tree.LeafWitnesses _) := by
    intro p
    obtain ⟨out, hout'⟩ := Verifier.outputs_nonempty_of_isAccepting hacc p
    refine ⟨w, rfl, out, hout', ?_⟩
    have heq := Verifier.outputs_guarded_subsingleton (pure ()) impl (rubber (oSpec := oSpec))
      (fun _ _ => true) (fun s tr => output 1 0 s (tr 0)) (fun _ _ => by simp [rubber])
      bad p.fullTranscript hout'
    rw [heq]; exact (htr0 p) ▸ hout
  obtain ⟨w', hw', hrel⟩ := h bad tree trivial hacc _ hvalid
  have hw'' : w = w' := Option.some.inj hw'
  subst hw''
  have hz : s.value = 0 := source_valid.1.2.symm.trans hrel.2
  rw [claim_two] at hz
  exact HachiTraceHeadAlgebraTest.value_ne_zero (congrArg Subtype.val hz)

end

end HachiTraceHeadRubberStampTest
