/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Backward extraction from round-by-round extractors

The intermediate extractor functions reconstruct an input witness by traversing a transcript
backward. This construction is deterministic, ignores query logs, and never rejects. It makes no
efficiency claim about the supplied intermediate functions and needs no inhabited witness types.

The shared transcript predicate `Transcript.HasBadRound` also supports ordinary soundness:
both ordinary and knowledge states must cross a bad challenge when the input is invalid but
the terminal state is valid. These pathwise lemmas are separate from probability accumulation.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
  (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)

/-- Reconstruct the input witness from a witness at any transcript prefix. -/
def extractPrefix (stmtIn : StmtIn) :
    (m : Fin (n + 1)) → Transcript m pSpec → WitMid m → WitIn :=
  Fin.induction
    (fun _ witMid => cast extractor.eqIn witMid)
    (fun m previous transcript witMid =>
      previous (Fin.init transcript) (extractor.extractMid m stmtIn transcript witMid))

/-- At the empty prefix, only the input witness type equality is needed. -/
@[simp] theorem extractPrefix_zero (stmtIn : StmtIn)
    (transcript : Transcript 0 pSpec) (witMid : WitMid 0) :
    extractor.extractPrefix stmtIn 0 transcript witMid = cast extractor.eqIn witMid := rfl

/-- Each backward step applies the supplied intermediate extractor exactly once. -/
@[simp] theorem extractPrefix_succ (stmtIn : StmtIn) (m : Fin n)
    (transcript : Transcript m.succ pSpec) (witMid : WitMid m.succ) :
    extractor.extractPrefix stmtIn m.succ transcript witMid =
      extractor.extractPrefix stmtIn m.castSucc (Fin.init transcript)
        (extractor.extractMid m stmtIn transcript witMid) := by
  simp [extractPrefix]

/-- The canonical straightline extractor reconstructs the input from the output witness.
Both query logs are deliberately unused; no extra oracle query or failure is introduced. -/
def toStraightline : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmtIn witOut transcript _ _ =>
    pure (extractor.extractPrefix stmtIn (.last n) transcript
      (extractor.extractOut stmtIn transcript witOut))

/-- The straightline extractor returns precisely the backward reconstruction. -/
@[simp] theorem toStraightline_run (stmtIn : StmtIn) (witOut : WitOut)
    (transcript : FullTranscript pSpec) (proveLog verifyLog : QueryLog oSpec) :
    (extractor.toStraightline stmtIn witOut transcript proveLog verifyLog).run =
      pure (some (extractor.extractPrefix stmtIn (.last n) transcript
        (extractor.extractOut stmtIn transcript witOut))) := rfl

end Extractor.RoundByRound

namespace ProtocolSpec.Transcript

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Removing an appended message recovers the previous dependent transcript. -/
@[simp] theorem init_concat {m : Fin n} (transcript : Transcript m.castSucc pSpec)
    (message : pSpec.Type m) : Fin.init (transcript.concat message) = transcript := by
  funext j
  exact concat_castSucc _ _ j

/-- Some prefix of this transcript satisfies the corresponding round's bad event.
This recursive form records only transcript data, never a future-dependent witness. -/
def HasBadRound (bad : (m : Fin n) → Transcript m.succ pSpec → Prop) :
    (m : Fin (n + 1)) → Transcript m pSpec → Prop :=
  Fin.induction (fun _ => False)
    (fun m previous transcript => previous (Fin.init transcript) ∨ bad m transcript)

/-- No bad transition has occurred in the empty transcript. -/
@[simp] theorem hasBadRound_zero (bad : (m : Fin n) → Transcript m.succ pSpec → Prop)
    (transcript : Transcript 0 pSpec) : ¬ HasBadRound bad 0 transcript := id

/-- A bad transition either occurred earlier or occurs in the last round. -/
@[simp] theorem hasBadRound_succ (bad : (m : Fin n) → Transcript m.succ pSpec → Prop)
    (m : Fin n) (transcript : Transcript m.succ pSpec) :
    HasBadRound bad m.succ transcript ↔
      HasBadRound bad m.castSucc (Fin.init transcript) ∨ bad m transcript := by
  simp [HasBadRound]

end ProtocolSpec.Transcript

namespace Verifier.KnowledgeStateFunction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
  (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)

/-- A challenge makes some intermediate witness valid although its predecessor is invalid.
The witness is existentially hidden, so the predicate depends only on the transcript prefix. -/
def badChallenge (stmtIn : StmtIn) (m : Fin n) (transcript : Transcript m.succ pSpec) : Prop :=
  pSpec.dir m = .V_to_P ∧ ∃ witMid,
    ¬ kSF m.castSucc stmtIn (Fin.init transcript)
      (extractor.extractMid m stmtIn transcript witMid) ∧
    kSF m.succ stmtIn transcript witMid

/-- A valid later witness that reconstructs an invalid input must cross a bad challenge.
No probability assumption is used: this is a pathwise fact for arbitrary transcript orderings. -/
theorem hasBadRound_of_extractPrefix_invalid (stmtIn : StmtIn)
    (m : Fin (n + 1)) (transcript : Transcript m pSpec) (witMid : WitMid m)
    (hvalid : kSF m stmtIn transcript witMid)
    (hinvalid : (stmtIn, extractor.extractPrefix stmtIn m transcript witMid) ∉ relIn) :
    Transcript.HasBadRound (kSF.badChallenge stmtIn) m transcript := by
  induction m using Fin.induction with
  | zero =>
    have htr : transcript = default := Subsingleton.elim _ _
    subst transcript
    exact (hinvalid ((kSF.toFun_empty stmtIn witMid).mpr hvalid)).elim
  | succ m ih =>
    rw [Transcript.hasBadRound_succ]
    by_cases hprev : kSF m.castSucc stmtIn (Fin.init transcript)
        (extractor.extractMid m stmtIn transcript witMid)
    · exact Or.inl (ih _ _ hprev hinvalid)
    · right
      refine ⟨?_, witMid, hprev, hvalid⟩
      cases hdir : pSpec.dir m with
      | V_to_P => rfl
      | P_to_V =>
        apply False.elim
        apply hprev
        have hnext := kSF.toFun_next m hdir stmtIn (Fin.init transcript)
          (transcript (Fin.last m.val)) witMid
        simpa only [Transcript.concat, Fin.snoc_init_self] using
          hnext (by simpa only [Transcript.concat, Fin.snoc_init_self] using hvalid)

end Verifier.KnowledgeStateFunction

namespace Verifier.StateFunction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {langIn : Set StmtIn} {langOut : Set StmtOut}
  (sF : verifier.StateFunction init impl langIn langOut)

/-- An ordinary state can change from false to true only at a challenge round. -/
def badChallenge (stmtIn : StmtIn) (m : Fin n) (transcript : Transcript m.succ pSpec) : Prop :=
  pSpec.dir m = .V_to_P ∧
    ¬ sF m.castSucc stmtIn (Fin.init transcript) ∧ sF m.succ stmtIn transcript

/-- A true later state on an invalid input must have crossed a bad challenge. -/
theorem hasBadRound_of_not_mem (stmtIn : StmtIn) (hinvalid : stmtIn ∉ langIn)
    (m : Fin (n + 1)) (transcript : Transcript m pSpec)
    (hvalid : sF m stmtIn transcript) :
    Transcript.HasBadRound (sF.badChallenge stmtIn) m transcript := by
  induction m using Fin.induction with
  | zero =>
    have htr : transcript = default := Subsingleton.elim _ _
    subst transcript
    exact (hinvalid ((sF.toFun_empty stmtIn).mpr hvalid)).elim
  | succ m ih =>
    rw [Transcript.hasBadRound_succ]
    by_cases hprev : sF m.castSucc stmtIn (Fin.init transcript)
    · exact Or.inl (ih _ hprev)
    · right
      refine ⟨?_, hprev, hvalid⟩
      cases hdir : pSpec.dir m with
      | V_to_P => rfl
      | P_to_V =>
        apply False.elim
        apply sF.toFun_next m hdir stmtIn (Fin.init transcript) hprev
          (transcript (Fin.last m.val))
        simpa only [Transcript.concat, Fin.snoc_init_self] using hvalid

end Verifier.StateFunction
