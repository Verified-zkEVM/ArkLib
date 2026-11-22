/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Implications

/-! Public simplification and executable extraction for `Unit` witnesses. -/

open OracleComp OracleSpec ProtocolSpec

namespace RoundByRoundUnit

abbrev oneRound : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => Unit⟩

def zeroExtractor : Extractor.RoundByRound []ₒ Unit Unit Unit !p[] (fun _ => Unit) :=
  Extractor.RoundByRound.unit

def oneExtractor : Extractor.RoundByRound []ₒ Unit Unit Unit oneRound (fun _ => Unit) :=
  Extractor.RoundByRound.unit

/-- info: (PUnit.unit, PUnit.unit, PUnit.unit) -/
#guard_msgs in
#eval (zeroExtractor.extractIn () (), zeroExtractor.extractOut () default (),
  oneExtractor.extractMid 0 () (fun _ => ()) ())

section

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {L : Set StmtIn} {L' : Set StmtOut} {V : Verifier oSpec StmtIn StmtOut pSpec}
  (S : V.StateFunction init impl L L')
  (m : Fin (n + 1)) (x : StmtIn) (tr : Transcript m pSpec)

-- Both simplification rules are available through an ordinary public import.
example : (S.toKnowledgeStateFunction init impl).toFun m x tr () = S.toFun m x tr := by
  simp

example : ((S.toKnowledgeStateFunction init impl).toStateFunction init impl).toFun m x tr =
    S.toFun m x tr := by
  simp

end

end RoundByRoundUnit
