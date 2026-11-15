/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Execution

/-!
# Recording a prover's transcript in its private state

This instrumentation preserves the prover's oracle calls and messages. It allows execution
comparisons that retain private state to observe the complete interactive transcript.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Record every message locally without changing the protocol or its oracle effects. -/
def withTranscript (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec where
  PrvState i := pSpec.Transcript i × P.PrvState i
  input sw := (default, P.input sw)
  sendMessage i st := do
    let z ← P.sendMessage i st.2
    pure (z.1, st.1.concat z.1, z.2)
  receiveChallenge i st := do
    let f ← P.receiveChallenge i st.2
    pure fun c => (st.1.concat c, f c)
  output st := P.output st.2

set_option backward.isDefEq.respectTransparency false in
/-- The recorded transcript agrees with the executor's transcript at every prefix. -/
theorem withTranscript_runToRound (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) (stmt : StmtIn) (wit : WitIn) :
    P.withTranscript.runToRound i stmt wit =
      (fun z => (z.1, z)) <$> P.runToRound i stmt wit := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [runToRound_succ, runToRound_succ, processRound_bind, ih,
      processRound_bind P]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro z
    by_cases hd : pSpec.dir i = .P_to_V
    · rw [processRound_of_dir_eq_P_to_V _ hd, processRound_of_dir_eq_P_to_V _ hd]
      simp [withTranscript]
    · have hd : pSpec.dir i = .V_to_P := by cases h : pSpec.dir i <;> simp_all
      rw [processRound_of_dir_eq_V_to_P _ hd, processRound_of_dir_eq_V_to_P _ hd]
      simp [withTranscript]

end Prover
