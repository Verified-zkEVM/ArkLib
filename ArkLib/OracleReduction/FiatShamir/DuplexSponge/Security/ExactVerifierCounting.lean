/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule

/-!
# Exact forward-query count for the live DSFS transcript derivation

This module is the operational counterpart of the stateful paper count
\`N_𝒱\`.  Unlike the historical \`QueryCounting\` induction, it charges each
absorb/squeeze operation by the difference of its two stateful cursor query
indices.  Consequently an operation that resumes inside a rate block is not
charged a fictitious fresh block.
-/

namespace DuplexSpongeFS

open OracleComp OracleSpec ProtocolSpec

section ExactDeriveTranscript

variable {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn : Type} [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]

variable [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) +
  duplexSpongeForwardOracle StmtIn U)]

/-- The exact forward-query count of a transcript prefix, measured from an
arbitrary live sponge/cursor pair that agrees at the start. -/
lemma deriveTranscriptDSFSAux_fwd_bound_exact
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages)
    (initial : Backtrack.ScheduleCursor)
    (hinitial : Backtrack.ScheduleCursor.SpongeCursorAgrees sponge initial)
    (k : Fin (n + 1)) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSAux (oSpec := []ₒ) (StmtIn := StmtIn)
        (U := U) sponge messages k)
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      ((deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial k).queryIndex -
        initial.queryIndex) := by
  induction k using Fin.induction with
  | zero =>
      simp [ProtocolSpec.Messages.deriveTranscriptDSFSAux, deriveTranscriptCursor]
  | succ i ih =>
      rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux] at ih
      rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux, Fin.induction_succ]
      split
      · rename_i hdir
        rw [deriveTranscriptCursor_succ_v (initial := initial) (i := i) _ hdir]
        refine (isQueryBoundP_bind
          (n := (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex -
            initial.queryIndex)
          (m := (Backtrack.ScheduleCursor.squeeze SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            (challengeSize ⟨i, hdir⟩)).queryIndex -
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex)
          ih (fun x hx => ?_)).mono ?_
        obtain ⟨curSponge, prevTranscript⟩ := x
        have hprev : Backtrack.ScheduleCursor.SpongeCursorAgrees curSponge
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc) :=
          deriveTranscriptDSFSAux_support_cursor_agrees_live
          (pSpec := pSpec) sponge messages initial hinitial i.castSucc
            ⟨curSponge, prevTranscript⟩ hx
        dsimp only
        refine (isQueryBoundP_bind
          (n := (Backtrack.ScheduleCursor.squeeze SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            (challengeSize ⟨i, hdir⟩)).queryIndex -
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex)
          (m := 0)
          ((isQueryBoundP_liftM_of_lawful _
            (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
            (fun t => ?_)
            (Backtrack.ScheduleCursor.squeeze_isQueryBoundP_cursor curSponge
              (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
              (challengeSize ⟨i, hdir⟩) hprev)).mono ?_)
          (fun y _ => ?_)).mono ?_
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
            OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          exact fun _ => by simp
        · exact le_rfl
        · rcases y with ⟨challenge, nextSponge⟩
          simp
        · have hstep := Backtrack.ScheduleCursor.queryIndex_le_squeeze SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            (challengeSize ⟨i, hdir⟩)
          have hinitial_le := deriveTranscriptCursor_queryIndex_le
            (pSpec := pSpec) SpongeSize.R initial i.castSucc
          omega
        · have hstep := Backtrack.ScheduleCursor.queryIndex_le_squeeze SpongeSize.R
              (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
              (challengeSize ⟨i, hdir⟩)
          have hinitial_le := deriveTranscriptCursor_queryIndex_le
            (pSpec := pSpec) SpongeSize.R initial i.castSucc
          omega
      · rename_i hdir
        rw [deriveTranscriptCursor_succ_p (initial := initial) (i := i) _ hdir]
        refine (isQueryBoundP_bind
          (n := (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex -
            initial.queryIndex)
          (m := (Backtrack.ScheduleCursor.absorb SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            (messageSize ⟨i, hdir⟩)).queryIndex -
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex)
          ih (fun x hx => ?_)).mono ?_
        obtain ⟨curSponge, prevTranscript⟩ := x
        have hprev : Backtrack.ScheduleCursor.SpongeCursorAgrees curSponge
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc) :=
          deriveTranscriptDSFSAux_support_cursor_agrees_live
          (pSpec := pSpec) sponge messages initial hinitial i.castSucc
            ⟨curSponge, prevTranscript⟩ hx
        dsimp only
        refine (isQueryBoundP_bind
          (n := (Backtrack.ScheduleCursor.absorb SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            (messageSize ⟨i, hdir⟩)).queryIndex -
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc).queryIndex)
          (m := 0)
          ((isQueryBoundP_liftM_of_lawful _
            (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
            (fun t => ?_)
            (Backtrack.ScheduleCursor.absorb_isQueryBoundP_cursor curSponge
              (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
              ((Codec.instSerializeMessage (pSpec := pSpec) (U := U) ⟨i, hdir⟩).serialize
                (messages ⟨i, hdir⟩)).toList hprev)).mono ?_)
          (fun y _ => ?_)).mono ?_
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
            OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          exact fun _ => by simp
        · simp
        · simp
        · have hstep := Backtrack.ScheduleCursor.queryIndex_le_absorb SpongeSize.R
            (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
            ((Codec.instSerializeMessage (pSpec := pSpec) (U := U) ⟨i, hdir⟩).serialize
              (messages ⟨i, hdir⟩)).toList.length
          have hinitial_le := deriveTranscriptCursor_queryIndex_le
            (pSpec := pSpec) SpongeSize.R initial i.castSucc
          omega
        · have hstep := Backtrack.ScheduleCursor.queryIndex_le_absorb SpongeSize.R
              (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc)
              (messageSize ⟨i, hdir⟩)
          have hinitial_le := deriveTranscriptCursor_queryIndex_le
            (pSpec := pSpec) SpongeSize.R initial i.castSucc
          omega

omit [VCVCompatible StmtIn]
  [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)] in
/-- `DS.Start` performs only the duplex-hash query.  In particular it does
not contribute to the forward-permutation budget. -/
private lemma start_fwd_bound_zero (stmtIn : StmtIn) :
    IsQueryBoundP
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U)
          (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
            state := SpongeState.update (0 : CanonicalSpongeState U)
              (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
            absorbPos := 0,
            squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true) 0 := by
  refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)).mono (by omega)
  rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  rw [show ((liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
      OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U) _).input)
    = Sum.inr (Sum.inl stmtIn) from rfl]
  simp [isNarrowFwdPermPoint]

omit [VCVCompatible StmtIn]
  [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)] in
/-- Every `DS.Start` support point realizes the initial stateful cursor. -/
private lemma start_support_cursor_agrees (stmtIn : StmtIn)
    (sponge : CanonicalDuplexSponge U)
    (hsponge : sponge ∈ support
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U)
          (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
            state := SpongeState.update (0 : CanonicalSpongeState U)
              (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
            absorbPos := 0,
            squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))) :
    Backtrack.ScheduleCursor.SpongeCursorAgrees sponge ⟨0, 0, SpongeSize.R⟩ := by
  rw [mem_support_bind_iff] at hsponge
  obtain ⟨c, _, hsponge⟩ := hsponge
  rw [mem_support_pure_iff] at hsponge
  subst sponge
  simp [Backtrack.ScheduleCursor.SpongeCursorAgrees]

/-- The live salted derivation performs exactly the stateful schedule's
forward-permutation count `N_𝒱`.  This is the operational bridge used by the
revised Lemma 5.8 analysis; it deliberately has no rounded-block premise. -/
lemma deriveTranscriptDSFSSalted_fwd_bound_exact {δ : ℕ}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := []ₒ) (U := U)
        stmtIn salt messages)
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ)) := by
  rw [ProtocolSpec.Messages.deriveTranscriptDSFSSalted]
  refine (isQueryBoundP_bind (n := 0)
    (m := verifierPermCallCount (pSpec := pSpec) (δ := δ))
    (start_fwd_bound_zero stmtIn) (fun sponge0 hs0 => ?_)).mono (by omega)
  have hstart : Backtrack.ScheduleCursor.SpongeCursorAgrees sponge0 ⟨0, 0, SpongeSize.R⟩ :=
    start_support_cursor_agrees stmtIn sponge0 hs0
  let saltCursor := Backtrack.ScheduleCursor.absorb SpongeSize.R
    (⟨0, 0, SpongeSize.R⟩ : Backtrack.ScheduleCursor) δ
  refine (isQueryBoundP_bind
    (n := saltCursor.queryIndex)
    (m :=
      (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R saltCursor (Fin.last n)).queryIndex -
        saltCursor.queryIndex)
    ?_ (fun sponge hsponge => ?_)).mono ?_
  · refine ((isQueryBoundP_liftM_of_lawful _
      (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
      (fun t => ?_)
      (Backtrack.ScheduleCursor.absorb_isQueryBoundP_cursor sponge0
        ⟨0, 0, SpongeSize.R⟩ salt.toList hstart)).mono ?_)
    · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
          OracleQuery (([]ₒ : OracleSpec PEmpty) + duplexSpongeForwardOracle StmtIn U) _)) _ _
      rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => by simp
    · simp [saltCursor]
  · have hsalt : Backtrack.ScheduleCursor.SpongeCursorAgrees sponge saltCursor := by
      simpa [saltCursor] using
        (Backtrack.ScheduleCursor.lifted_absorb_support_cursor_agrees_live
          sponge0 ⟨0, 0, SpongeSize.R⟩ salt.toList sponge hstart hsponge)
    exact deriveTranscriptDSFSAux_fwd_bound_exact sponge messages saltCursor hsalt (Fin.last n)
  · have hle := deriveTranscriptCursor_queryIndex_le (pSpec := pSpec) SpongeSize.R
      saltCursor (Fin.last n)
    have hfinal :
        (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R saltCursor (Fin.last n)).queryIndex =
          verifierPermCallCount (pSpec := pSpec) (δ := δ) := by
      simpa [saltCursor] using
        (deriveTranscriptCursor_last_queryIndex_eq_verifierPermCallCount (pSpec := pSpec) δ)
    rw [Nat.add_sub_of_le hle, hfinal]

/-- The actual narrow DSFS verifier inherits the exact transcript count: its
post-transcript verification is over the empty external oracle and therefore
does not add a forward permutation query. -/
lemma dsfsForwardVerify_fwd_bound_exact {StmtOut : Type} {δ : ℕ}
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := []ₒ) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ)) := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, Option.getM, Option.elimM]
  refine (isQueryBoundP_bind
    (n := verifierPermCallCount (pSpec := pSpec) (δ := δ)) (m := 0) ?_
    (fun o _ => ?_)).mono (by omega)
  · exact (isQueryBoundP_bind
      (n := verifierPermCallCount (pSpec := pSpec) (δ := δ)) (m := 0)
      (deriveTranscriptDSFSSalted_fwd_bound_exact stmtIn proof.1 proof.2)
      (fun _ _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      obtain ⟨v, hv⟩ := emptySpec_eq_pure ((V.verify stmtIn x.2).run)
      rw [hv]
      rcases v with _ | a <;> simp

end ExactDeriveTranscript

end DuplexSpongeFS
