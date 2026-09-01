/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù
-/

import ArkLib.OracleReduction.ProtocolSpec.Basic
import ArkLib.ToVCVio.OracleComp.QueryTracking.QueryLog

/-!
# Characterization of the (logged) SR/FS transcript derivation

The FS/SR transcript derivation `deriveTranscriptSR` queries the challenge oracle once per
challenge round, in round order.  This file characterizes it — and its `loggingOracle`-wrapped
run — via an explicit form `chalTupleUpTo` that returns the challenge tuple, from which the
transcript (`Transcript.ofMessagesChallenges`) and the canonical query log (`canonChalLog`) are
pure read-outs.

This is the formal content of **"the verifier's trace determines the transcript"**, which the
Fiat-Shamir extractor constructions (e.g. CO25 Construction 3.19, the DSFS Construction 6.3)
rely on: `challengesOfLog` reconstructs the challenges from any log containing the canonical
derivation log, and `challengesOfLog_canonChalLog` shows the reconstruction is exact.

All statements are generic in the `Statement` keying the challenge oracle (for salted
Fiat-Shamir, instantiate `Statement := StmtIn × Salt`).
-/

open OracleComp OracleSpec

universe u

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {Statement : Type}

/-- A typed challenge-oracle log entry. Keeping the dependent pair behind this constructor avoids
unfolding the newer `ProtocolSpec.take` representation during log rewrites. -/
private def canonChalEntry (stmt : Statement) (m : pSpec.Messages) (i : Fin n)
    (h : pSpec.dir i = .V_to_P) (c : pSpec.Challenge ⟨i, h⟩) :
    (t : (srChallengeOracle Statement pSpec).Domain) ×
      (srChallengeOracle Statement pSpec).Range t :=
  ⟨⟨⟨i, h⟩, (stmt, m.take i.castSucc)⟩, c⟩

/-- Query the FS challenge oracle at every challenge round before `j` (in round order),
returning the tuple of sampled challenges.  Explicit form of the transcript derivation
`deriveTranscriptSR`: see `Messages.deriveTranscriptSR_eq_chalTupleUpTo`. -/
def chalTupleUpTo (stmt : Statement) (m : pSpec.Messages) (j : Fin (n + 1)) :
    OracleComp (oSpec + srChallengeOracle Statement pSpec) (pSpec.ChallengesUpTo j) :=
  Fin.induction
    (pure (fun ⟨i, _⟩ => i.elim0))
    (fun i ih => do
      let cs ← ih
      match hDir : pSpec.dir i with
      | .V_to_P => do
        let c ← getChallengeSR (oSpec := oSpec) ⟨i, hDir⟩ (stmt, m.take i.castSucc)
        return cs.concat hDir c
      | .P_to_V => return cs.extend hDir)
    j

/-- The canonical challenge-oracle query log of the transcript derivation up to round `j`: one
entry per challenge round `i < j`, keyed by the statement and message prefix and answered by
that round's challenge. -/
def canonChalLog (stmt : Statement) (m : pSpec.Messages) (j : Fin (n + 1))
    (cs : pSpec.ChallengesUpTo j) : QueryLog (srChallengeOracle Statement pSpec) :=
  Fin.induction (motive := fun j => pSpec.ChallengesUpTo j →
      QueryLog (srChallengeOracle Statement pSpec))
    (fun _ => [])
    (fun i ih cs =>
      match hDir : pSpec.dir i with
      | .V_to_P =>
        ih (show pSpec.ChallengesUpTo i.castSucc from
          ChallengesUpTo.take (k := i.succ) (Fin.last i.1).castSucc cs) ++
          [canonChalEntry stmt m i hDir (ChallengesUpTo.last cs hDir)]
      | .P_to_V => ih (show pSpec.ChallengesUpTo i.castSucc from
          ChallengesUpTo.take (k := i.succ) (Fin.last i.1).castSucc cs))
    j cs

/-- The canonical derivation log after appending a challenge round. -/
lemma canonChalLog_concat (stmt : Statement) (m : pSpec.Messages)
    {i : Fin n} (cs : pSpec.ChallengesUpTo i.castSucc) (h : pSpec.dir i = .V_to_P)
    (c : pSpec.Challenge ⟨i, h⟩) :
    canonChalLog stmt m i.succ (ChallengesUpTo.concat cs h c)
      = canonChalLog stmt m i.castSucc cs
        ++ [canonChalEntry stmt m i h c] := by
  simp only [canonChalLog, Fin.induction_succ]
  split
  · rename_i hDir
    rw [ChallengesUpTo.take_concat]
    have hproof : hDir = h := Subsingleton.elim _ _
    cases hproof
    rw [ChallengesUpTo.last_concat]
  · rename_i hDir
    exact absurd (h.symm.trans hDir) (by simp)

/-- The canonical derivation log is unchanged by appending a message round. -/
lemma canonChalLog_extend (stmt : Statement) (m : pSpec.Messages)
    {i : Fin n} (cs : pSpec.ChallengesUpTo i.castSucc) (h : pSpec.dir i = .P_to_V) :
    canonChalLog stmt m i.succ (ChallengesUpTo.extend cs h)
      = canonChalLog stmt m i.castSucc cs := by
  simp only [canonChalLog, Fin.induction_succ]
  split
  · rename_i hDir
    exact absurd (h.symm.trans hDir) (by simp)
  · rename_i hDir
    rw [ChallengesUpTo.take_extend]

/-- Logging a right-summand (challenge-oracle) query in the sum ambient records the
`Sum.inr` entry. -/
private lemma withQueryLog_getChallengeSR_inr
    (i : pSpec.ChallengeIdx) (input : Statement × pSpec.MessagesUpTo i.1.castSucc) :
    (getChallengeSR (oSpec := oSpec) i input).withQueryLog
      = getChallengeSR (oSpec := oSpec) i input >>= fun u =>
          pure (u, [⟨Sum.inr ⟨i, input⟩, u⟩]) := by
  unfold getChallengeSR
  exact OracleComp.withQueryLog_query
    (spec := oSpec + srChallengeOracle Statement pSpec)
    (Sum.inr (⟨i, input⟩ : (srChallengeOracle Statement pSpec).Domain))

/-- **Logged transcript-derivation characterization** (the formal content of "the verifier's
trace determines the transcript"): the `loggingOracle`-wrapped transcript derivation equals the
explicit challenge-tuple computation followed by pure read-outs of the transcript
(`Transcript.ofMessagesChallenges`) and the canonical challenge-only query log
(`canonChalLog`). -/
lemma logged_deriveTranscriptSRAux_eq (stmt : Statement) (m : pSpec.Messages)
    (j : Fin (n + 1)) :
    (simulateQ loggingOracle
      (MessagesUpTo.deriveTranscriptSRAux (oSpec := oSpec) (StmtIn := Statement)
        stmt ⟨n, Nat.lt_succ_self n⟩ (Messages.asUpTo m) j)).run
    = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) stmt m j >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (m.take j) cs,
          QueryLog.inr (canonChalLog stmt m j cs)) := by
  induction j using Fin.induction with
  | zero =>
    delta MessagesUpTo.deriveTranscriptSRAux chalTupleUpTo canonChalLog
    simp only [Fin.induction_zero]
    simp only [simulateQ_pure, WriterT.run_pure, pure_bind, QueryLog.inr, List.map_nil]
    exact congrArg (fun t => (pure (t, []) : OracleComp _ _))
      (Subsingleton.elim (α := pSpec.Transcript 0) _ _)
  | succ i ih =>
    unfold MessagesUpTo.deriveTranscriptSRAux chalTupleUpTo at ih ⊢
    simp only [Fin.induction_succ, Fin.castLE_refl]
    refine Eq.trans (OracleComp.withQueryLog_bind _ _) ?_
    refine Eq.trans (congrArg (fun z : OracleComp (oSpec + srChallengeOracle Statement pSpec)
      (pSpec.Transcript i.castSucc × QueryLog (oSpec + srChallengeOracle Statement pSpec)) =>
        z >>= _) ih) ?_
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun cs => ?_
    split <;> split
    · -- challenge round: one query, one appended log entry
      rename_i hDir hDir'
      have hproof : hDir = hDir' := Subsingleton.elim _ _
      cases hproof
      rw [Messages.take_asUpTo]
      rw [OracleComp.withQueryLog_bind, withQueryLog_getChallengeSR_inr]
      simp only [bind_assoc, pure_bind, OracleComp.withQueryLog_pure, map_pure, Prod.map,
        map_bind]
      refine bind_congr fun c => ?_
      rw [Transcript.ofMessagesChallenges_concat_challenge, canonChalLog_concat]
      simp only [QueryLog.inr, List.map_append, List.map_cons, List.map_nil, id]
      rfl
    · rename_i hDir hDir'
      exact absurd (hDir.symm.trans hDir') (by simp)
    · rename_i hDir hDir'
      exact absurd (hDir.symm.trans hDir') (by simp)
    · -- message round: no query, log unchanged
      rename_i hDir hDir'
      have hproof : hDir = hDir' := Subsingleton.elim _ _
      cases hproof
      rw [Messages.asUpTo_apply]
      rw [OracleComp.withQueryLog_pure]
      simp only [map_pure, Prod.map, pure_bind, List.append_nil, id]
      rw [Transcript.ofMessagesChallenges_concat_message, canonChalLog_extend]

/-- Value-marginal of the characterization: the (unlogged) transcript derivation is the
challenge-tuple computation followed by the transcript read-out. -/
lemma Messages.deriveTranscriptSR_eq_chalTupleUpTo (stmt : Statement)
    (m : pSpec.Messages) :
    (Messages.deriveTranscriptSR (oSpec := oSpec) stmt m : OracleComp _ _)
      = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) stmt m ⟨n, Nat.lt_succ_self n⟩
          >>= fun cs =>
          pure (Transcript.ofMessagesChallenges (m.take ⟨n, Nat.lt_succ_self n⟩) cs) := by
  have h := congrArg (fun z => Prod.fst <$> z)
    (logged_deriveTranscriptSRAux_eq (oSpec := oSpec) stmt m ⟨n, Nat.lt_succ_self n⟩)
  simp only [loggingOracle.fst_map_run_simulateQ] at h
  exact h.trans (Eq.trans (map_bind _ _ _) (bind_congr fun cs => map_pure _ _))

section Reconstruction

variable [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]

/-- **Reconstruction identity**: looking up the round-`r` key in the canonical derivation log
(up to round `j`) returns the round-`r` challenge when `r < j`, and nothing otherwise. -/
lemma lookup?_canonChalLog (stmt : Statement)
    (m : pSpec.Messages) (j : Fin (n + 1)) (cs : pSpec.ChallengesUpTo j)
    (r : pSpec.ChallengeIdx) :
    (canonChalLog stmt m j cs).lookup? ⟨r, (stmt, m.take r.1.castSucc)⟩
      = if h : r.1.1 < j.1 then some (ChallengesUpTo.getAt cs r h) else none := by
  induction j using Fin.induction with
  | zero =>
    rw [show canonChalLog stmt m 0 cs = [] from rfl]
    rw [dif_neg (by simp)]
    rfl
  | succ i ih =>
    simp only [canonChalLog, Fin.induction_succ]
    split
    · -- challenge round `i`: the log gains the round-`i` entry at the end
      rename_i hDir
      rw [show (Fin.induction (motive := fun j => pSpec.ChallengesUpTo j →
            QueryLog (srChallengeOracle Statement pSpec)) _ _ i.castSucc)
          = canonChalLog stmt m i.castSucc from rfl]
      rw [QueryLog.lookup?_append, ih]
      simp only [Fin.val_castSucc, Fin.val_succ]
      by_cases hlt : r.1.1 < i.1
      · rw [dif_pos hlt, dif_pos (by omega)]
        rfl
      · rw [dif_neg hlt]
        by_cases heq : r.1.1 = i.1
        · -- the appended entry answers exactly the round-`i` key
          rcases r with ⟨r1, hr⟩
          obtain rfl : r1 = i := Fin.ext heq
          rw [dif_pos (by omega)]
          rw [QueryLog.lookup?_cons]
          have hkey :
              (canonChalEntry stmt m r1 hDir (ChallengesUpTo.last cs hDir)).fst =
                ⟨⟨r1, hr⟩, (stmt, m.take r1.castSucc)⟩ := by rfl
          rw [dif_pos hkey]
          unfold canonChalEntry ChallengesUpTo.last ChallengesUpTo.getAt
          rfl
        · rw [dif_neg (by omega)]
          rw [QueryLog.lookup?_cons]
          rw [dif_neg (fun hkey => heq (by
            have := congrArg (fun d : (srChallengeOracle Statement pSpec).Domain =>
              d.1.1.1) hkey
            simpa only [canonChalEntry] using this.symm))]
          rfl
    · -- message round `i`: the log is unchanged, and `r ≠ i` since `r` is a challenge round
      rename_i hDir
      rw [show (Fin.induction (motive := fun j => pSpec.ChallengesUpTo j →
            QueryLog (srChallengeOracle Statement pSpec)) _ _ i.castSucc)
          = canonChalLog stmt m i.castSucc from rfl]
      rw [ih]
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hne : r.1.1 ≠ i.1 := by
        intro hval
        obtain ⟨r1, hr⟩ := r
        obtain rfl : r1 = i := Fin.ext hval
        exact absurd (hr.symm.trans hDir) (by simp)
      by_cases hlt : r.1.1 < i.1
      · rw [dif_pos hlt, dif_pos (by omega)]
        rfl
      · rw [dif_neg hlt, dif_neg (by omega)]

variable [∀ i, Inhabited (pSpec.Challenge i)]

/-- Reconstruct the challenges of an FS/SR transcript from a challenge-oracle query log:
the round-`i` challenge is the logged answer at the round-`i` key (the statement together
with the message prefix), defaulting when the key was never queried.

This is the Fiat-Shamir extractor's transcript reconstruction, reading the challenges off the
verifier's trace.  It is *computable* (a single left-to-right scan of the log per round) — the
extractor built from it is the paper's explicitly efficient algorithm, not a classical choice
of witness. -/
def Messages.challengesOfLog (stmt : Statement) (m : pSpec.Messages)
    (log : QueryLog (srChallengeOracle Statement pSpec)) :
    pSpec.Challenges :=
  fun i => (log.lookup? ⟨i, (stmt, m.take i.1.castSucc)⟩).getD (default : pSpec.Challenge i)

/-- **Exactness of the reconstruction**: reading the challenges off the canonical derivation
log recovers exactly the derived challenge tuple. -/
lemma Messages.challengesOfLog_canonChalLog (stmt : Statement) (m : pSpec.Messages)
    (cs : pSpec.ChallengesUpTo ⟨n, Nat.lt_succ_self n⟩) :
    Messages.challengesOfLog stmt m (canonChalLog stmt m ⟨n, Nat.lt_succ_self n⟩ cs)
      = (show pSpec.Challenges from fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩) := by
  funext r
  change ((canonChalLog stmt m _ cs).lookup? _).getD _ = _
  rw [lookup?_canonChalLog]
  rw [dif_pos (by exact r.1.2)]
  unfold ChallengesUpTo.getAt
  rfl

end Reconstruction

end ProtocolSpec
