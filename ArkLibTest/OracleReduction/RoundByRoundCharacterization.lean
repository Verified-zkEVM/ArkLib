/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.Security.Implications

/-!
# Round-by-round soundness and knowledge soundness without input witnesses

A zero-round verifier that rejects every transcript, with an input statement and an output
witness but no input witnesses, separates the two notions for every output relation.
Round-by-round soundness holds, while no round-by-round extractor exists, because extraction must
also map the rejected transcript. Knowledge soundness therefore fails for every pair of relations
and every error.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace RoundByRoundCharacterization

/-- A zero-round verifier that rejects every statement. -/
def rejectAll : Verifier emptySpec.{0, 0} Unit Unit !p[] := ⟨fun _ _ => failure⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl emptySpec.{0, 0} (StateT σ ProbComp))

/-- No round-by-round extractor has an empty input-witness type here. -/
example (WitMid : Fin 1 → Type) :
    IsEmpty (Extractor.RoundByRound emptySpec.{0, 0} Unit Empty Unit !p[] WitMid) :=
  Extractor.RoundByRound.isEmpty_of_isEmpty_witIn () default ()

/-- The rejecting verifier outputs no statement. -/
theorem rejectAll_prEvent_eq_zero (langOut : Set Unit) (stmt : Unit) (tr : !p[].FullTranscript) :
    Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (rejectAll.run stmt tr)).run' (← init))}[stmtOut ∈ langOut] = 0 := by
  rw [OracleComp.OptionT.prEvent_mk_eq_zero_iff]
  intro x hx
  change some x ∈ support (do
    let s ← init
    (simulateQ impl (pure none : OracleComp emptySpec.{0, 0} (Option Unit))).run' s) at hx
  simp at hx

/-- For every output relation, round-by-round soundness holds and round-by-round knowledge
soundness fails. -/
example (relOut : Set (Unit × Unit)) :
    rejectAll.rbrSoundness init impl (∅ : Set (Unit × Empty)).language
        relOut.language 0 ∧
      ¬ rejectAll.rbrKnowledgeSoundness init impl (∅ : Set (Unit × Empty)) relOut 0 :=
  ⟨Verifier.rbrSoundness_of_forall_prEvent_eq_zero init impl
      (rejectAll_prEvent_eq_zero init impl _) 0,
    Verifier.not_rbrKnowledgeSoundness_of_isEmpty init impl () default ()⟩

/-- The equivalence fails for some relations and error. -/
example : ¬ ∀ (relIn : Set (Unit × Empty)) (relOut : Set (Unit × Unit))
      (ε : !p[].ChallengeIdx → ℝ≥0),
    rejectAll.rbrSoundness init impl relIn.language relOut.language ε ↔
      rejectAll.rbrKnowledgeSoundness init impl relIn relOut ε := fun h =>
  ((Verifier.forall_rbrSoundness_iff_rbrKnowledgeSoundness_iff
      init impl).1 h).elim (fun ⟨w⟩ => w.elim) fun hempty => hempty.false ((), default, ())

/-- With an empty output-witness type the two notions coincide again, without input witnesses. -/
example (relIn : Set (Unit × Empty)) (relOut : Set (Unit × Empty))
    (ε : !p[].ChallengeIdx → ℝ≥0) :
    rejectAll.rbrSoundness init impl relIn.language relOut.language ε ↔
      rejectAll.rbrKnowledgeSoundness init impl relIn relOut ε :=
  Verifier.rbrSoundness_iff_rbrKnowledgeSoundness_of_nonempty_or_isEmpty init impl
    (Or.inr inferInstance)

end RoundByRoundCharacterization
