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

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize] [CodecCore pSpec U]

/-- The exact forward-query count of a transcript prefix, measured from an
arbitrary live sponge/cursor pair that agrees at the start. -/
lemma deriveTranscriptDSFSAux_fwd_bound_exact
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages)
    (initial : Backtrack.ScheduleCursor)
    (hinitial : Backtrack.ScheduleCursor.SpongeCursorAgrees sponge initial)
    (k : Fin (n + 1)) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSAux (oSpec := oSpec) (StmtIn := StmtIn)
        (U := U) sponge messages k)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
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
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
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
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
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

/-- `DS.Start` performs only the duplex-hash query.  In particular it does
not contribute to the forward-permutation budget. -/
private lemma start_fwd_bound_zero (stmtIn : StmtIn) :
    IsQueryBoundP
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
          (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
            state := SpongeState.update (0 : CanonicalSpongeState U)
              (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
            absorbPos := 0,
            squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0 := by
  refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)).mono (by omega)
  rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  rw [show ((liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
      OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
    = Sum.inr (Sum.inl stmtIn) from rfl]
  simp [isNarrowFwdPermPoint]

/-- Every `DS.Start` support point realizes the initial stateful cursor. -/
private lemma start_support_cursor_agrees (stmtIn : StmtIn)
    (sponge : CanonicalDuplexSponge U)
    (hsponge : sponge ∈ support
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
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
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U)
        stmtIn salt messages)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
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
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
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

/-- Lifting an ambient `OptionT` computation into the narrow DSFS verifier
spec preserves its zero forward-permutation-query budget.  The explicit
three-hop shape is Lean's canonical subspec route for
`oSpec + duplexSpongeForwardOracle`; semantically, every query remains in the
ambient summand. -/
private lemma ambientOptionT_fwd_bound_zero {α : Type} (oa : OptionT (OracleComp oSpec) α) :
    IsQueryBoundP
      ((liftM oa : OptionT
        (OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)) α).run)
      (fun t => isNarrowFwdPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0 := by
  let mid0 : OracleSpec _ := oSpec + forwardPermutationOracle (CanonicalSpongeState U)
  let mid1 : OracleSpec _ := oSpec + (([]ₒ : OracleSpec PEmpty) +
    forwardPermutationOracle (CanonicalSpongeState U))
  let mid2 : OracleSpec _ := oSpec + duplexSpongeForwardOracle StmtIn U
  change IsQueryBoundP
    ((liftM (liftM (liftM oa : OptionT (OracleComp mid0) α) :
      OptionT (OracleComp mid1) α) : OptionT (OracleComp mid2) α).run)
    (fun t => isNarrowFwdPermPoint
      (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0
  have h0 : IsQueryBoundP
      ((liftM oa : OptionT (OracleComp mid0) α).run)
      (fun t : mid0.Domain => Sum.isRight t = true) 0 := by
    rw [OracleComp.liftM_OptionT_eq]
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (p := fun _ : oSpec.Domain => False)
      (q := fun t : mid0.Domain => Sum.isRight t = true)
      (fun t => by
        change False ↔ Sum.isRight (Sum.inl t) = true
        simp)
      (isQueryBoundP_zero_of_forall_not oa.run (by simp))
  have h1 : IsQueryBoundP
      ((liftM (liftM oa : OptionT (OracleComp mid0) α) :
        OptionT (OracleComp mid1) α).run)
      (fun t : mid1.Domain =>
        (match t with | .inr (.inr _) => true | _ => false) = true) 0 := by
    rw [OracleComp.liftM_OptionT_eq]
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (p := fun t : mid0.Domain => Sum.isRight t = true)
      (q := fun t : mid1.Domain =>
        (match t with | .inr (.inr _) => true | _ => false) = true)
      (fun t => by cases t <;> simp)
      h0
  have h2 : IsQueryBoundP
      ((liftM (liftM (liftM oa : OptionT (OracleComp mid0) α) :
        OptionT (OracleComp mid1) α) : OptionT (OracleComp mid2) α).run)
      (fun t => isNarrowFwdPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0 := by
    rw [OracleComp.liftM_OptionT_eq]
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (p := fun t : mid1.Domain =>
        (match t with | .inr (.inr _) => true | _ => false) = true)
      (q := fun t => isNarrowFwdPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      (fun t => by rcases t with t | (t | t) <;> simp [isNarrowFwdPermPoint])
      h1
  exact h2

/-- The raw ambient computation case of `ambientOptionT_fwd_bound_zero`.
The verifier body lifts `V.verify … |>.run` into `OptionT`, hence this is the
form used in the post-transcript branch. -/
private lemma ambientOracleComp_fwd_bound_zero {α : Type} (oa : OracleComp oSpec α) :
    IsQueryBoundP
      ((liftM oa : OptionT
        (OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)) α).run)
      (fun t => isNarrowFwdPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0 := by
  let mid0 : OracleSpec _ := oSpec + forwardPermutationOracle (CanonicalSpongeState U)
  let mid1 : OracleSpec _ := oSpec + (([]ₒ : OracleSpec PEmpty) +
    forwardPermutationOracle (CanonicalSpongeState U))
  let mid2 : OracleSpec _ := oSpec + duplexSpongeForwardOracle StmtIn U
  change IsQueryBoundP
    ((liftM (liftM (liftM (OptionT.lift oa : OptionT (OracleComp oSpec) α) :
      OptionT (OracleComp mid0) α) : OptionT (OracleComp mid1) α) :
      OptionT (OracleComp mid2) α).run)
    (fun t => isNarrowFwdPermPoint
      (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0
  exact ambientOptionT_fwd_bound_zero (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
    (OptionT.lift oa)

/-- Ambient verifier work cannot produce the distinguished DSFS hash query either.
The intermediate empty-summand case is impossible; spelling it out here makes the
sub-spec transport independent of any accidental choice of lift instance. -/
private lemma ambientOracleComp_hash_bound_zero {α : Type} (oa : OracleComp oSpec α) :
    IsQueryBoundP
      ((liftM oa : OptionT
        (OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)) α).run)
      (fun t => isNarrowHashPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0 := by
  let mid0 : OracleSpec _ := oSpec + forwardPermutationOracle (CanonicalSpongeState U)
  let mid1 : OracleSpec _ := oSpec + (([]ₒ : OracleSpec PEmpty) +
    forwardPermutationOracle (CanonicalSpongeState U))
  let mid2 : OracleSpec _ := oSpec + duplexSpongeForwardOracle StmtIn U
  change IsQueryBoundP
    ((liftM (liftM (liftM (OptionT.lift oa : OptionT (OracleComp oSpec) α) :
      OptionT (OracleComp mid0) α) : OptionT (OracleComp mid1) α) :
      OptionT (OracleComp mid2) α).run)
    (fun t => isNarrowHashPoint
      (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0
  have h0 : IsQueryBoundP
      ((liftM (OptionT.lift oa : OptionT (OracleComp oSpec) α) :
        OptionT (OracleComp mid0) α).run)
      (fun _ : mid0.Domain => False) 0 := by
    rw [OracleComp.liftM_OptionT_eq]
    exact isQueryBoundP_zero_of_forall_not _ (by simp)
  have h1 : IsQueryBoundP
      ((liftM (liftM (OptionT.lift oa : OptionT (OracleComp oSpec) α) :
        OptionT (OracleComp mid0) α) : OptionT (OracleComp mid1) α).run)
      (fun _ : mid1.Domain => False) 0 := by
    rw [OracleComp.liftM_OptionT_eq]
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (p := fun _ : mid0.Domain => False)
      (q := fun _ : mid1.Domain => False)
      (fun _ => by simp)
      h0
  rw [OracleComp.liftM_OptionT_eq]
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : mid1.Domain => False)
    (q := fun t => isNarrowHashPoint
      (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
    (fun t => by
      rcases t with t | (t | t)
      · simp [isNarrowHashPoint]
      · nomatch t
      · simp [isNarrowHashPoint])
    h1

/-- The actual narrow DSFS verifier inherits the exact transcript count.
Its post-transcript verification may use the ambient oracle, but this is
lifted into the left summand and therefore adds no forward permutation query. -/
lemma dsfsForwardVerify_fwd_bound_exact {StmtOut : Type} {δ : ℕ}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := oSpec) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ)) := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, Option.getM, Option.elimM]
  refine (isQueryBoundP_bind
    (n := verifierPermCallCount (pSpec := pSpec) (δ := δ)) (m := 0) ?_
    (fun o _ => ?_)).mono (by omega)
  · exact (isQueryBoundP_bind
      (n := verifierPermCallCount (pSpec := pSpec) (δ := δ)) (m := 0)
      (deriveTranscriptDSFSSalted_fwd_bound_exact
        (oSpec := oSpec) stmtIn proof.1 proof.2)
      (fun _ _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      exact (isQueryBoundP_bind (n := 0) (m := 0)
        (ambientOracleComp_fwd_bound_zero (oSpec := oSpec) (StmtIn := StmtIn)
          (U := U) (V.verify stmtIn x.2).run)
        (fun z _ => by
          rcases z with _ | z
          · simp
          · cases z <;> simp)).mono (by omega)

/-- The actual narrow DSFS verifier makes exactly the one `DS.Start` hash query.
As in `dsfsForwardVerify_fwd_bound_exact`, ambient verifier calls are transported
through the left summand and cost zero in this DSFS-specific class. -/
lemma dsfsForwardVerify_hash_bound_exact {StmtOut : Type} {δ : ℕ}
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := oSpec) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowHashPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      1 := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, Option.getM, Option.elimM]
  refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ (fun o _ => ?_)).mono (by omega)
  · exact (isQueryBoundP_bind (n := 1) (m := 0)
      (deriveTranscriptDSFSSalted_hash_bound (oSpec := oSpec) stmtIn proof.1 proof.2)
      (fun _ _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      exact (isQueryBoundP_bind (n := 0) (m := 0)
        (ambientOracleComp_hash_bound_zero (oSpec := oSpec) (StmtIn := StmtIn)
          (U := U) (V.verify stmtIn x.2).run)
        (fun z _ => by
          rcases z with _ | z
          · simp
          · cases z <;> simp)).mono (by omega)

/-- The wide forward verifier has exactly the DSFS-query budget needed by the
ambient-safe H₀→H₁ runner: one `DS.Start` hash call and the stateful `N_𝒱`
forward calls.  Queries of the arbitrary ambient verifier remain in the left
summand and hence do not consume this budget. -/
lemma runForwardVerifierWide_right_bound_exact {StmtOut : Type} {δ : ℕ}
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP (runForwardVerifierWide δ V stmtIn proof)
      (fun point => point.isRight = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) := by
  rw [runForwardVerifierWide]
  have hClasses := IsQueryBoundP.or_add
      (dsfsForwardVerify_hash_bound_exact V stmtIn proof)
      (dsfsForwardVerify_fwd_bound_exact V stmtIn proof)
      (by
        rintro (_ | (_ | _)) ⟨hHash, hFwd⟩ <;>
          simp_all [isNarrowHashPoint, isNarrowFwdPermPoint])
  have hNarrow : IsQueryBoundP
      (((Verifier.toDSFS (oSpec := oSpec) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun point => point.isRight = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) := by
    rw [isQueryBoundP_congr_pred (p' := fun point => point.isRight = true)] at hClasses
    · simpa [Nat.add_comm] using hClasses
    · rintro (_ | (_ | _)) <;>
        simp [isNarrowHashPoint, isNarrowFwdPermPoint]
  refine isQueryBoundP_liftM_of_lawful _
    (p := fun (point : (oSpec + duplexSpongeForwardOracle StmtIn U).Domain) =>
      Sum.isRight point = true)
    (q := fun (point : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain) =>
      Sum.isRight point = true)
    (fun point => ?_) hNarrow
  show IsQueryBoundP
    (liftM (liftM (OracleSpec.query point) : OracleQuery
      (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
    (fun point => Sum.isRight point = true)
    (if Sum.isRight point = true then 1 else 0)
  rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  rcases point with point | (point | point)
  · simp [OracleSpec.query]
  · simp [OracleSpec.query]
  · simp [OracleSpec.query]

end ExactDeriveTranscript

end DuplexSpongeFS
