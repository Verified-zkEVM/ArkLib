/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Construction
public import ArkLib.OracleReduction.Execution
public import ArkLib.OracleReduction.ProtocolSpec.PrefixLemmas

/-!
# Scheduled DSFS execution

The proof-only reference runner executes every private-state transition and omits absorptions
after the last verifier step. For proofs, an auxiliary observation reconstructs the unused final
sponge state, allowing the existing verifier reconstruction invariant to be reused. This
observation is not executed by the prover or its output phase. Equalities hold after interpreting
fixed public sponge functions, not as raw oracle traces.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

/-! ## Observing the transcript in prover state -/

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
    dsimp only [withTranscript]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro z
    by_cases hd : pSpec.dir i = .P_to_V
    · rw [processRound_of_dir_eq_P_to_V _ hd, processRound_of_dir_eq_P_to_V _ hd]
      simp
    · have hd : pSpec.dir i = .V_to_P := by cases h : pSpec.dir i <;> simp_all
      rw [processRound_of_dir_eq_V_to_P _ hd, processRound_of_dir_eq_V_to_P _ hd]
      simp

end Prover

open scoped DuplexSpongeFS

section ReferenceExecution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut U : Type} [SpongeUnit U] [SpongeSize U] [Codec pSpec U]

/-- Execute one protocol step. Every verifier message is derived and delivered to the
prover. A prover message is absorbed exactly when a later verifier step exists. These rules
preserve the original private-state transitions for arbitrary protocol schedules. -/
def Prover.referenceRoundDSFS (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (previousRound : OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc × CanonicalDuplexSponge U × P.PrvState j.castSucc)) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.succ × CanonicalDuplexSponge U × P.PrvState j.succ) := do
  let ⟨messages, sponge, prvState⟩ ← previousRound
  match hd : pSpec.dir j with
  | .P_to_V => do
    let ⟨msg, nextPrvState⟩ ← P.sendMessage ⟨j, hd⟩ prvState
    if HasLaterVerifierMessage pSpec j then
      let encodedMessage := ((Codec.instSerializeMessage ⟨j, hd⟩).serialize msg).toList
      let sponge ← sponge.absorb encodedMessage
      return (messages.concat hd msg, sponge, nextPrvState)
    else return (messages.concat hd msg, sponge, nextPrvState)
  | .V_to_P => do
    let receiveChallenge ← P.receiveChallenge ⟨j, hd⟩ prvState
    let (verifierMessage, sponge) ← sponge.squeeze (verifierMessageSize ⟨j, hd⟩)
    return (messages.extend hd, sponge,
      receiveChallenge ((Codec.instDeserializeChallenge ⟨j, hd⟩).deserialize verifierMessage))

/-- Run the salted DSFS prover through a protocol prefix using schedule-directed guards. -/
def Prover.referenceRunDSFSSalted {δ : Nat} (salt : Vector U δ) (i : Fin (n + 1)) (stmt : StmtIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (initialPrvState : P.PrvState 0) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo i × CanonicalDuplexSponge U × P.PrvState i) :=
  Fin.induction
    (zero := do
      let initialSponge : CanonicalDuplexSponge U ← liftM (DuplexSponge.start stmt)
      let sponge ← initialSponge.absorb salt.toList
      return (default, sponge, initialPrvState))
    (succ := Prover.referenceRoundDSFS P) i

end ReferenceExecution

namespace DuplexSpongeFS.ScheduledExecution

variable {n : ℕ} {p : ProtocolSpec n} {ι : Type} {o : OracleSpec ι}
  {SI WI SO WO U : Type} [SpongeUnit U] [SpongeSize U] [Codec p U]

/-- Proof-only reconstruction of omitted trailing absorptions from the transcript.
The canonical prover never executes this observation. -/
def restoreSponge (i : Fin (n + 1)) :
    p.MessagesUpTo i → CanonicalDuplexSponge U →
      OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) (CanonicalDuplexSponge U) :=
  Fin.induction
    (zero := fun _ sponge => pure sponge)
    (succ := fun j previous messages sponge => do
      let sponge ← previous (fun k => messages ⟨k.1.castSucc, k.2⟩) sponge
      if hd : p.dir j = .P_to_V then
        if HasLaterVerifierMessage p j then pure sponge
        else
          let msg : p.Message ⟨j, hd⟩ := messages ⟨Fin.last j.val, hd⟩
          sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize msg).toList
      else pure sponge) i

/-- Observe a reference prefix with its unused final sponge state reconstructed for proofs.
The messages and private state are those produced by the reference runner. -/
def reconstructedRun (P : Prover o SI WI SO WO p) {δ : Nat}
    (salt : Vector U δ) (i : Fin (n + 1)) (stmt : SI) (initialPrvState : P.PrvState 0) :
    OracleComp (o + duplexSpongeOracle SI U)
      (p.MessagesUpTo i × CanonicalDuplexSponge U × P.PrvState i) := do
  let runResult ← P.referenceRunDSFSSalted salt i stmt initialPrvState
  let sponge ← restoreSponge i runResult.1 runResult.2.1
  return (runResult.1, sponge, runResult.2.2)

/-- The initial prefix already agrees with its proof-only sponge reconstruction. -/
lemma reconstructedRun_zero (P : Prover o SI WI SO WO p) {δ : Nat}
    (salt : Vector U δ) (stmt : SI) (initialPrvState : P.PrvState 0) :
    reconstructedRun P salt 0 stmt initialPrvState = (do
      let sponge0 ← liftM (DuplexSponge.start stmt)
      let sponge ← liftComp (sponge0.absorb salt.toList)
        (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
      return (default, sponge, initialPrvState)) := by
  simp only [reconstructedRun, Prover.referenceRunDSFSSalted, Fin.induction_zero,
    restoreSponge, monadLift_pure, bind_assoc, pure_bind]
  rfl


private lemma restoreSponge_succ (j : Fin n) (messages : p.MessagesUpTo j.succ)
    (sponge : CanonicalDuplexSponge U) :
    restoreSponge j.succ messages sponge = (do
      let sponge ← restoreSponge j.castSucc
        (fun k => messages ⟨k.1.castSucc, k.2⟩) sponge
      if hd : p.dir j = .P_to_V then
        if HasLaterVerifierMessage p j then pure sponge else
          sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize
            (messages ⟨Fin.last j.val, hd⟩)).toList
      else pure sponge) := rfl

omit [SpongeSize U] in
private lemma prefix_concat (j : Fin n) (hd : p.dir j = .P_to_V)
    (messages : p.MessagesUpTo j.castSucc) (msg : p.Message ⟨j, hd⟩) :
    (fun k : p.MessageIdxUpTo j.castSucc => (messages.concat hd msg) ⟨k.1.castSucc, k.2⟩) =
      messages := by
  funext k
  exact MessagesUpTo.concat_apply_castSucc messages hd msg k.1 k.2

private lemma restoreSponge_concat (j : Fin n) (hd : p.dir j = .P_to_V)
    (messages : p.MessagesUpTo j.castSucc) (msg : p.Message ⟨j, hd⟩)
    (sponge : CanonicalDuplexSponge U) :
    restoreSponge j.succ (messages.concat hd msg) sponge = (do
      let sponge ← restoreSponge j.castSucc messages sponge
      if HasLaterVerifierMessage p j then pure sponge else
        sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize msg).toList) := by
  have hl : (messages.concat hd msg) ⟨Fin.last j.val, hd⟩ = msg :=
    MessagesUpTo.concat_apply_last messages hd msg hd
  rw [restoreSponge_succ, prefix_concat]
  simp only [dite_eq_left hd, hl]

omit [SpongeSize U] in
private lemma prefix_extend (j : Fin n) (hd : p.dir j = .V_to_P)
    (messages : p.MessagesUpTo j.castSucc) :
    (fun k : p.MessageIdxUpTo j.castSucc => (messages.extend hd) ⟨k.1.castSucc, k.2⟩) =
      messages := by
  funext k
  exact MessagesUpTo.extend_apply_castSucc messages hd k.1 k.2

private lemma restoreSponge_extend (j : Fin n) (hd : p.dir j = .V_to_P)
    (messages : p.MessagesUpTo j.castSucc) (sponge : CanonicalDuplexSponge U) :
    restoreSponge j.succ (messages.extend hd) sponge =
      restoreSponge j.castSucc messages sponge := by
  rw [restoreSponge_succ, prefix_extend]
  simp [hd]

private lemma restoreSponge_eq_pure (i : Fin (n + 1)) (messages : p.MessagesUpTo i)
    (sponge : CanonicalDuplexSponge U)
    (h : ∀ j : Fin n, j.val < i.val → p.dir j = .P_to_V → HasLaterVerifierMessage p j) :
    restoreSponge i messages sponge = pure sponge := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    rw [restoreSponge_succ]
    erw [ih _ (fun k hk hd => h k
      (by simp only [Fin.val_castSucc] at hk; simp only [Fin.val_succ]; omega) hd)]
    simp only [pure_bind]
    split
    · rename_i hd
      simp [h j (by simp) hd]
    · rfl

private lemma restoreSponge_before_absorb (j : Fin n) (hn : HasLaterVerifierMessage p j)
    (messages : p.MessagesUpTo j.castSucc) (sponge : CanonicalDuplexSponge U) :
    restoreSponge j.castSucc messages sponge = pure sponge := by
  apply restoreSponge_eq_pure
  intro k hk _
  obtain ⟨v, hjv, hv⟩ := hn
  exact ⟨v, (show k < j from hk).trans hjv, hv⟩

private lemma restoreSponge_before_verifierMessage (j : Fin n) (hd : p.dir j = .V_to_P)
    (messages : p.MessagesUpTo j.castSucc)
    (sponge : CanonicalDuplexSponge U) :
    restoreSponge j.castSucc messages sponge = pure sponge := by
  apply restoreSponge_eq_pure
  intro k hk _
  exact ⟨j, hk, hd⟩

variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Target" => m

/-- Combine an ambient handler with fixed answers to public sponge queries. -/
def interp (a : QueryImpl o Target)
    (f : QueryImpl (duplexSpongeOracle SI U) Id) :
    QueryImpl (o + duplexSpongeOracle SI U) Target :=
  a + (fun q => pure (f q) : QueryImpl (duplexSpongeOracle SI U) Target)

/-- Ambient computations retain their handler under the combined interpreter. -/
lemma interp_liftComp_left (a : QueryImpl o Target)
    (f : QueryImpl (duplexSpongeOracle SI U) Id)
    {α : Type} (oa : OracleComp o α) :
    simulateQ (interp a f) (liftComp oa (o + duplexSpongeOracle SI U)) =
      simulateQ a oa :=
  QueryImpl.simulateQ_add_liftComp_left _ _ _

/-- Initialization is deterministic once the public hash function is fixed. -/
lemma interp_start (a : QueryImpl o ProbComp)
    (f : QueryImpl (duplexSpongeOracle SI U) Id) (stmt : SI) :
    simulateQ (interp a f)
      (liftM (DuplexSponge.start stmt) :
        OracleComp (o + duplexSpongeOracle SI U) (CanonicalDuplexSponge U)) =
      pure (evalWithAnswerFn (fun q => f (.inl q)) (DuplexSponge.start stmt)) := by
  simp only [DuplexSponge.start, monadLift_bind, monadLift_pure, simulateQ_bind,
    simulateQ_pure, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

/-- Fixed public permutation queries evaluate deterministically under `interp`. -/
lemma interp_forward (a : QueryImpl o Target)
    (f : QueryImpl (duplexSpongeOracle SI U) Id)
    {α : Type} (oa : OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) α) :
    simulateQ (interp a f)
      (liftM oa : OracleComp (o + duplexSpongeOracle SI U) α) =
    pure (evalWithAnswerFn (fun q => f (.inr (.inl q))) oa) := by
  change simulateQ (interp a f)
    (liftComp oa (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)) = _
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, evalWithAnswerFn_bind]
    simp only [liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [simulateQ_liftM_query]
    change (((id <$> pure (f (.inr (.inl t)))) : Target _) >>= _) = _
    simp only [id_map]
    simp only [pure_bind, ih]
    rfl
private lemma reconstruct_processRound (a : QueryImpl o Target)
    (f : QueryImpl (duplexSpongeOracle SI U) Id)
    (P : Prover o SI WI SO WO p) (j : Fin n)
    (previousRound : OracleComp (o + duplexSpongeOracle SI U)
      (p.MessagesUpTo j.castSucc × CanonicalDuplexSponge U × P.PrvState j.castSucc)) :
    simulateQ (interp a f) (do
      let ⟨messages, sponge, prvState⟩ ← (do
        let runResult ← previousRound
        let sponge ← liftComp (restoreSponge j.castSucc runResult.1 runResult.2.1)
          (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
        return (runResult.1, sponge, runResult.2.2))
      match hDir : p.dir j with
      | .V_to_P => do
        let idx : p.ChallengeIdx := ⟨j, hDir⟩
        let inst : Deserialize (p.Challenge idx) (Vector U (verifierMessageSize idx)) :=
          Codec.instDeserializeChallenge idx
        let receiveChallenge ← P.receiveChallenge idx prvState
        let (verifierMessage, newSponge) ←
          OracleComp.liftComp (DuplexSponge.squeeze sponge (verifierMessageSize idx))
            (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
        -- Deserialize the verifier message
        let decodedVerifierMessage : p.Challenge idx := inst.deserialize verifierMessage
        return ⟨messages.extend hDir, newSponge, receiveChallenge decodedVerifierMessage⟩
      | .P_to_V => do
        let idx : p.MessageIdx := ⟨j, hDir⟩
        let inst : Serialize (p.Message idx) (Vector U (proverMessageSize idx)) :=
          Codec.instSerializeMessage idx
        let ⟨msg, nextPrvState⟩ ← P.sendMessage idx prvState
        let serializedMessage : Vector U (proverMessageSize idx) := inst.serialize msg
        let newSponge ← OracleComp.liftComp (DuplexSponge.absorb sponge serializedMessage.toList)
          (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
        return ⟨messages.concat hDir msg, newSponge, nextPrvState⟩) =
    simulateQ (interp a f) (do
      let runResult ← Prover.referenceRoundDSFS P j previousRound
      let sponge ← liftComp (restoreSponge j.succ runResult.1 runResult.2.1)
        (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
      return (runResult.1, sponge, runResult.2.2)) := by
  simp only [Prover.referenceRoundDSFS, liftComp_eq_liftM,
    simulateQ_bind, bind_assoc, pure_bind, interp_forward]
  apply bind_congr
  rintro ⟨messages, sponge, prvState⟩
  split <;> rename_i hl <;> split <;> rename_i hr
  · cases hl.symm.trans hr
  · simp [restoreSponge_extend, restoreSponge_before_verifierMessage j hl,
      interp_forward, simulateQ_bind, simulateQ_pure]
  · simp only [simulateQ_bind, bind_assoc, simulateQ_pure]
    apply bind_congr
    rintro ⟨msg, nextPrvState⟩
    split
    · rename_i hn
      simp [restoreSponge_concat, hn, restoreSponge_before_absorb j hn,
        interp_forward]
    · rename_i hn
      simp [restoreSponge_concat, hn, interp_forward, simulateQ_pure]
  · cases hl.symm.trans hr

/-- Semantic successor rule for the reconstructed canonical prefix. It depends on the constructor
only through its local step proof, isolating downstream induction proofs from scheduling details. -/
lemma reconstructedRun_succ (a : QueryImpl o Target)
    (f : QueryImpl (duplexSpongeOracle SI U) Id)
    (P : Prover o SI WI SO WO p) {δ : Nat} (salt : Vector U δ)
    (i : Fin n) (stmt : SI) (initialPrvState : P.PrvState 0) :
    simulateQ (interp a f) (reconstructedRun P salt i.succ stmt initialPrvState) =
    simulateQ (interp a f) (do
      let ⟨messages, sponge, prvState⟩ ← reconstructedRun P salt i.castSucc stmt initialPrvState
      match hDir : p.dir i with
      | .V_to_P => do
        let idx : p.ChallengeIdx := ⟨i, hDir⟩
        let inst : Deserialize (p.Challenge idx) (Vector U (verifierMessageSize idx)) :=
          Codec.instDeserializeChallenge idx
        let receiveChallenge ← P.receiveChallenge idx prvState
        let (verifierMessage, newSponge) ←
          OracleComp.liftComp (DuplexSponge.squeeze sponge (verifierMessageSize idx))
            (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
        -- Deserialize the verifier message
        let decodedVerifierMessage : p.Challenge idx := inst.deserialize verifierMessage
        return ⟨messages.extend hDir, newSponge, receiveChallenge decodedVerifierMessage⟩
      | .P_to_V => do
        let idx : p.MessageIdx := ⟨i, hDir⟩
        let inst : Serialize (p.Message idx) (Vector U (proverMessageSize idx)) :=
          Codec.instSerializeMessage idx
        let ⟨msg, nextPrvState⟩ ← P.sendMessage idx prvState
        let serializedMessage : Vector U (proverMessageSize idx) := inst.serialize msg
        let newSponge ← OracleComp.liftComp (DuplexSponge.absorb sponge serializedMessage.toList)
          (o + duplexSpongeOracle SI U) (h := dsfsForwardPermutationLift)
        return ⟨messages.concat hDir msg, newSponge, nextPrvState⟩) := by
  have h := (reconstruct_processRound a f P i
    (P.referenceRunDSFSSalted salt i.castSucc stmt initialPrvState)).symm
  simp only [reconstructedRun, Prover.referenceRunDSFSSalted, Fin.induction_succ] at h ⊢
  convert h using 1
  simp only [simulateQ_bind]
  apply bind_congr
  intro runResult
  split <;> rename_i hd <;> split <;> rename_i he
  · rfl
  · cases hd.symm.trans he
  · cases hd.symm.trans he
  · rfl

end DuplexSpongeFS.ScheduledExecution

/-! ## Forward verifier routing -/

section VerifierRouting

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize U]
  [Codec pSpec U]

/-- Pinned narrow→wide lift for whole `𝒱^{h,p}` computations: embeds
`oSpec + duplexSpongeForwardOracle` into `oSpec + duplexSpongeOracle`, sending
- ambient queries to the ambient slot (`.inl i ↦ .inl i`),
- hash queries to the hash slot (`.inr (.inl 𝕩) ↦ .inr (.inl 𝕩)`),
- permutation queries to the forward slot `p` (`.inr (.inr s) ↦ .inr (.inr (.inl s))`).

The generic narrow-to-wide lift routes permutation queries to the forward slot, so
verifier computations use inferred lifting. This pinned lift remains available for explicit
routing statements; `liftComp_dsfsForwardToFullLift` rewrites it away. -/
@[reducible]
def dsfsForwardToFullLift : MonadLiftT
    (OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query :=
    match query with
    | ⟨Sum.inl i, cont⟩ => ⟨Sum.inl i, cont⟩
    | ⟨Sum.inr (Sum.inl stmt), cont⟩ => ⟨Sum.inr (Sum.inl stmt), cont⟩
    | ⟨Sum.inr (Sum.inr stateIn), cont⟩ => ⟨Sum.inr (Sum.inr (Sum.inl stateIn)), cont⟩

omit [VCVCompatible StmtIn] in
/-- The pinned narrow→wide lift agrees with the generic `liftComp`: both send every
permutation query to the forward slot `p`. -/
theorem liftComp_dsfsForwardToFullLift {α : Type}
    (oa : OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) α) :
    liftComp oa (oSpec + duplexSpongeOracle StmtIn U) (h := dsfsForwardToFullLift) =
      liftComp oa (oSpec + duplexSpongeOracle StmtIn U) :=
  liftComp_inst_irrel (fun t => by rcases t with t | t | t <;> rfl) oa

/-- **[CO25, Construction 4.4]** Run the narrow-spec salted forward verifier `𝒱^{h,p}`
(`V.duplexSpongeFiatShamirForward δ`) on
`(stmtIn, nargString : DSFSTypedNARGString pSpec U δ)`, then `liftComp` the resulting computation
up to the wide spec `oSpec + duplexSpongeOracle StmtIn U`.

Shared by:
- `dsfsGame` / `hybridGame` (KeyLemma.lean — `Hyb_0` through `Hyb_3` skeleton);
- `abortableTraceDist` (BadEvents.lean — §5.6).

Encodes [CO25, Figure 4, line 3] at the type level: the narrow input spec
`oSpec + duplexSpongeForwardOracle StmtIn U` exposes only `(h, p)`, while the wide output spec
`oSpec + duplexSpongeOracle StmtIn U` exposes `(h, p, p⁻¹)`. Because the body is just
`liftComp`-ed from the narrow surface, no `p⁻¹` query ever appears in the resulting query log. -/
def runForwardVerifierWide (δ : Nat) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) (Option StmtOut) :=
  let verifyCompNarrow :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((V.duplexSpongeFiatShamirForward δ).run stmtIn
      (fun i => match i with | ⟨0, _⟩ => nargString)).run
  liftComp verifyCompNarrow (oSpec + duplexSpongeOracle StmtIn U)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The canonical salted verifier executes the forward-only Section 5 verifier,
after widening its oracle interface. -/
theorem Verifier.duplexSpongeFiatShamir_verify (δ : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmt : StmtIn)
    (tr : FullTranscript ⟨!v[.P_to_V], !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩) :
    (V.duplexSpongeFiatShamir δ).verify stmt tr =
      OptionT.mk (runForwardVerifierWide δ V stmt (tr 0)) := by
  simp only [Verifier.duplexSpongeFiatShamir, Verifier.liftOracles, runForwardVerifierWide,
    Verifier.run]
  congr 3

end VerifierRouting
