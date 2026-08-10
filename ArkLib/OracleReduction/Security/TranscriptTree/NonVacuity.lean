/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.TranscriptTree.Basic

/-!
  # Non-vacuity gates for tree special soundness

  A soundness notion is worth only as much as its premises are satisfiable and its conclusion
  refutable. This file is the **permanent regression gate** for
  `Verifier.treeSpecialSoundWith`: each theorem below pins one typing decision of the notion by
  exhibiting concrete data on which a differently-typed variant is strictly worse. Re-run them
  (i.e. keep this file compiling) before weakening the notion.

  * `not_vacuous` — with `relIn = ∅` the notion is **refutable for every extractor**: non-vacuity
    in its strongest form.
  * `exists_valid_witnessing` — at a randomized two-output verifier a **valid witnessing exists**,
    so the validity premise is satisfiable exactly where the ∀-variant collapses.
  * `unclaimed_vacuous` / `classical_refutable` — the **∀-variant kill**: requiring one witness per
    leaf to serve *every* reachable output makes the premise unsatisfiable at that same verifier, so
    that notion is provable at the constant-`none` extractor with `relIn = ∅` — on data where the
    classical (total-extractor) statement is refutable. The adopted `IsValid` differs by exactly one
    quantifier.
  * `reachable_sound` / `free_refuted` — **reachability has teeth in both directions**: on the same
    sound data, with the same forwarding engine, the adopted notion is provable while the
    reachability-free variant is refuted (junk witnesses at unreachable statements are what the
    condition excludes).
  * `isValid_none_false` — the constant-`none` witnessing is invalid as soon as the tree has a leaf,
    so no chain can be "closed" by feeding it nothing.
  * `isAccepting_of_no_transcripts` / `fullTranscripts_eq_nil_of_arity_zero` — the **arity-0 edge**:
    a zero-arity challenge node has no transcripts, so acceptance is vacuous there. Inherited
    unchanged from the classical notion, and excluded by every concrete shape (CWSS structures give
    `arity ≥ 1`).

  The rejected variants (`LeafWitnesses.IsValidUnclaimed`, `treeSpecialSoundWithUnclaimed`,
  `LeafWitnesses.IsValidFree`, `treeSpecialSoundWithFree`) and the classical statement shape
  (`oldStatement`) are declared **`private`** here: they exist only so the kills can be *stated*,
  and are no part of the public notion.

  The companion positive fact — that the premise is never an obstruction — is in the notion's own
  file: `ChallengeTree.canonWitnesses_isValid` (valid on *every* accepting tree) with
  `Verifier.treeSpecialSoundWith.old_of_new`.
-/

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree

namespace ProtocolSpec.ChallengeTree.NonVacuity

/-! ## The rejected alternatives -/

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-- The ∀-variant's validity condition. -/
private def LeafWitnesses.IsValidUnclaimed (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (o : tree.LeafWitnesses WitOut) : Prop :=
  ∀ (p : ChallengeTree.LeafPath tree) (out : StmtOut),
    out ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript →
      ∃ w, o p = some w ∧ (out, w) ∈ relOut

/-- The ∀-variant's soundness notion. -/
private def treeSpecialSoundWithUnclaimed (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
      ∀ o : tree.LeafWitnesses WitOut,
        LeafWitnesses.IsValidUnclaimed init impl V relOut stmtIn o →
          ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- Two reachable outputs with no common witness make the ∀-variant's premise unsatisfiable. -/
private theorem isValidUnclaimed_false_of_two_outputs (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} (p : ChallengeTree.LeafPath tree) {out₁ out₂ : StmtOut}
    (h₁ : out₁ ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript)
    (h₂ : out₂ ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript)
    (hsep : ∀ w : WitOut, (out₁, w) ∈ relOut → (out₂, w) ∉ relOut)
    (o : tree.LeafWitnesses WitOut) :
    ¬ LeafWitnesses.IsValidUnclaimed init impl V relOut stmtIn o := by
  intro hvalid
  obtain ⟨w₁, hw₁, hm₁⟩ := hvalid p out₁ h₁
  obtain ⟨w₂, hw₂, hm₂⟩ := hvalid p out₂ h₂
  rw [hw₁] at hw₂
  cases Option.some.inj hw₂
  exact hsep w₁ hm₁ hm₂

/-- The reachability-free validity: any `relOut`-witness at ANY statement, reachable or not. -/
private def LeafWitnesses.IsValidFree (relOut : Set (StmtOut × WitOut))
    {tree : ChallengeTree pSpec arity 0} (o : tree.LeafWitnesses WitOut) : Prop :=
  ∀ p : ChallengeTree.LeafPath tree, ∃ w, o p = some w ∧ ∃ out, (out, w) ∈ relOut

/-- The reachability-free soundness notion. -/
private def treeSpecialSoundWithFree (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
      ∀ o : tree.LeafWitnesses WitOut, LeafWitnesses.IsValidFree relOut o →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- The classical statement shape (total extractor, no witnessing input). -/
private def oldStatement (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (S : ChallengeTreeShape pSpec) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBasedClassical StmtIn WitIn pSpec S.arity) : Prop :=
  ∀ stmtIn tree, ChallengeTree.IsStructured S tree →
    tree.IsAccepting init impl V stmtIn relOut.language → (stmtIn, Ext stmtIn tree) ∈ relIn

/-! ## The fixtures -/

/-- One-bit oracle, answered uniformly at random. -/
private def cimpl : QueryImpl coinSpec (StateT Unit ProbComp) :=
  fun _ => fun s => do let b ← ($ᵗ Bool); pure (b, s)

/-- Coin-flipping verifier: the output statement is a fresh uniform bit. -/
private def coinVerifier : Verifier coinSpec Unit Bool (!p[] : ProtocolSpec 0) where
  verify := fun _ _ => OptionT.mk (do
    let b ← (liftM (query (spec := coinSpec) (m := OracleComp coinSpec) ()) :
      OracleComp coinSpec Bool)
    pure (some b))

/-- An output relation forcing DIFFERENT witnesses at the two possible outputs. -/
private def relOutBad : Set (Bool × ℕ) := {(true, 0), (false, 1)}

private theorem relOutBad_language : relOutBad.language = Set.univ := by
  ext b
  simp only [Set.mem_univ, iff_true, Set.mem_language_iff]
  cases b
  · exact ⟨1, by simp [relOutBad]⟩
  · exact ⟨0, by simp [relOutBad]⟩

/-- The coin verifier's run, unfolded. -/
private theorem coinRun (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (do (simulateQ cimpl (coinVerifier.run () tr)).run' (← (pure () : ProbComp Unit)) :
      ProbComp (Option Bool)) = (do let b ← ($ᵗ Bool); pure (some b)) := by
  simp only [coinVerifier, Verifier.run, OptionT.mk, StateT.run',
    simulateQ_bind, simulateQ_pure]
  change (fun x => x.1) <$>
      ((fun (p : Bool × Unit) => (some p.1, p.2)) <$>
        (do let b ← ($ᵗ Bool); pure (b, ()))) = some <$> ($ᵗ Bool)
  simp [Functor.map_map, bind_pure_comp]

private theorem true_mem_outputs (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    true ∈ Verifier.Outputs (pure ()) cimpl coinVerifier () tr := by
  simp only [Verifier.Outputs, Set.mem_setOf_eq, coinRun]
  simp

private theorem false_mem_outputs (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    false ∈ Verifier.Outputs (pure ()) cimpl coinVerifier () tr := by
  simp only [Verifier.Outputs, Set.mem_setOf_eq, coinRun]
  simp

/-- The two reachable outputs admit no COMMON witness. -/
private theorem relOutBad_sep : ∀ w : ℕ, (true, w) ∈ relOutBad → (false, w) ∉ relOutBad := by
  intro w hw
  simp only [relOutBad, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hw ⊢
  rcases hw with ⟨_, rfl⟩ | ⟨h, _⟩
  · simp
  · exact absurd h (by simp)

/-- The coin verifier is accepting on every tree (its output language is everything). -/
private theorem coinAccepting {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    tree.IsAccepting (pure ()) cimpl coinVerifier () relOutBad.language := by
  intro tr _
  rw [relOutBad_language]
  rw [coinRun tr, probEvent_eq_one_iff]
  refine ⟨?_, fun x _ => Set.mem_univ x⟩
  rw [OptionT.probFailure_eq, OptionT.run_mk]
  simp

instance : IsEmpty ((!p[] : ProtocolSpec 0).ChallengeIdx) :=
  ⟨fun i => Fin.elim0 i.1⟩

/-- A pure verifier over the same protocol, constant verdict `true`. -/
private def pureVerifier : Verifier coinSpec Unit Bool (!p[] : ProtocolSpec 0) where
  verify := fun _ _ => OptionT.mk (pure (some true))

/-- The pure verifier's run, unfolded. -/
private theorem pureRun (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (do (simulateQ cimpl (pureVerifier.run () tr)).run' (← (pure () : ProbComp Unit)) :
      ProbComp (Option Bool)) = (pure (some true)) := by
  simp only [pureVerifier, Verifier.run, OptionT.mk, StateT.run', simulateQ_pure]
  change (fun x => x.1) <$> (pure (some true, ()) : ProbComp (Option Bool × Unit)) =
    pure (some true)
  simp

private theorem pureVerifier_accepting {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) (lang : Set Bool) (hmem : true ∈ lang) :
    tree.IsAccepting (pure ()) cimpl pureVerifier () lang := by
  intro tr _
  rw [pureRun tr, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  intro x hx
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
  subst hx
  exact hmem

/-- The forwarding extractor: read the (unique) leaf's witness and return it. A real engine in
miniature — witness-only, computable. -/
private def fwdExt (arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ) :
    Extractor.TreeBased Unit ℕ ℕ (!p[] : ProtocolSpec 0) arity :=
  fun _ tree o => o tree.onlyPath

/-- Two statements, two witnesses — but only `true` is reachable at `pureVerifier`. -/
private def relOutMix : Set (Bool × ℕ) := {(true, 0), (false, 7)}

/-- The input relation the forwarding extractor targets: exactly the witness at the REACHABLE
statement. -/
private def relInPt : Set (Unit × ℕ) := {((), 0)}

/-! ## The gates -/

/-- **G1 (satisfiability).** -/
theorem exists_valid_witnessing {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    ProtocolSpec.ChallengeTree.LeafWitnesses.IsValid (pure ()) cimpl coinVerifier relOutBad ()
      (tree := tree) (fun _ => some 0) :=
  fun p => ⟨0, rfl, true, true_mem_outputs p.fullTranscript, by simp [relOutBad]⟩

/-- **G2 (non-vacuity).** -/
theorem not_vacuous (S : ChallengeTreeShape (!p[] : ProtocolSpec 0))
    (Ext : Extractor.TreeBased Unit ℕ ℕ !p[] S.arity) :
    ¬ Verifier.treeSpecialSoundWith (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier
      Ext := by
  intro h
  obtain ⟨w, -, hw⟩ := h () ChallengeTree.leaf trivial (coinAccepting _) _
    (ChallengeTree.canonWitnesses_isValid (coinAccepting _))
  exact hw

/-- **G4.** -/
theorem isValid_none_false {StmtOut WitOut : Type} {init : ProbComp Unit}
    {impl : QueryImpl coinSpec (StateT Unit ProbComp)} {n : ℕ} {pSpec : ProtocolSpec n}
    {arity : pSpec.ChallengeIdx → ℕ} {tree : ChallengeTree pSpec arity 0}
    (V : Verifier coinSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) (hpath : Nonempty (ChallengeTree.LeafPath tree)) :
    ¬ ProtocolSpec.ChallengeTree.LeafWitnesses.IsValid init impl V relOut stmtIn (tree := tree)
      (fun _ => none) := by
  intro h
  obtain ⟨p⟩ := hpath
  obtain ⟨w, hw, -⟩ := h p
  exact absurd hw (by simp)

/-- **G0.** -/
theorem unclaimed_vacuous (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    treeSpecialSoundWithUnclaimed (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier
      (fun _ _ _ => none) := by
  intro stmtIn tree _ _ o hvalid
  exact absurd hvalid
    (isValidUnclaimed_false_of_two_outputs (pure ()) cimpl coinVerifier relOutBad ()
      tree.onlyPath (true_mem_outputs _) (false_mem_outputs _) relOutBad_sep o)

/-- The classical notion is refutable on that same data, for every extractor. -/
theorem classical_refutable (S : ChallengeTreeShape (!p[] : ProtocolSpec 0))
    (Ext : Extractor.TreeBasedClassical Unit ℕ (!p[] : ProtocolSpec 0) S.arity) :
    ¬ oldStatement (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier Ext := by
  intro h
  exact (h () ChallengeTree.leaf trivial (coinAccepting _) : (_, _) ∈ (∅ : Set (Unit × ℕ)))

/-- **G3, positive half.** -/
theorem reachable_sound (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    Verifier.treeSpecialSoundWith (pure ()) cimpl S relInPt relOutMix pureVerifier
      (fwdExt S.arity) := by
  intro stmtIn tree hstr hacc o hvalid
  obtain ⟨w, hw, out, hout, hrel⟩ := hvalid tree.onlyPath
  have hout' : out = true :=
    Verifier.outputs_pure_subsingleton (pure ()) cimpl pureVerifier (fun _ _ => true)
      (fun _ _ => rfl) () tree.onlyPath.fullTranscript hout
  subst hout'
  have hw0 : w = 0 := by
    simp only [relOutMix, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hrel
    rcases hrel with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by simp)
  subst hw0
  exact ⟨0, by simpa [fwdExt] using hw, by simp [relInPt]⟩

/-- **G3, negative half.** -/
theorem free_refuted (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    ¬ treeSpecialSoundWithFree (pure ()) cimpl S relInPt relOutMix pureVerifier
      (fwdExt S.arity) := by
  intro h
  obtain ⟨w, hw, hrel⟩ := h () ChallengeTree.leaf trivial
    (pureVerifier_accepting _ _ ((Set.mem_language_iff _ _).2 ⟨0, by simp [relOutMix]⟩))
    (fun _ => some 7) (fun _ => ⟨7, rfl, false, by simp [relOutMix]⟩)
  have hw7 : w = 7 := by
    have : some (7 : ℕ) = some w := by simpa [fwdExt, ChallengeTree.onlyPath] using hw
    exact (Option.some.inj this).symm
  subst hw7
  simp [relInPt] at hrel

/-! ## E20 — the arity-0 degeneracy -/

theorem isAccepting_of_no_transcripts {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    {arity : pSpec.ChallengeIdx → ℕ}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (lang : Set StmtOut) {tree : ChallengeTree pSpec arity 0}
    (h : tree.fullTranscripts = []) : tree.IsAccepting init impl V stmtIn lang := by
  intro tr htr; rw [h] at htr; exact absurd htr (by simp)

theorem fullTranscripts_eq_nil_of_arity_zero {m : ℕ} {pSpec : ProtocolSpec (m + 1)}
    {arity : pSpec.ChallengeIdx → ℕ} (h : pSpec.dir 0 = .V_to_P)
    (harity : arity ⟨0, h⟩ = 0)
    (chals : Fin (arity ⟨0, h⟩) → pSpec.Challenge ⟨0, h⟩)
    (children : Fin (arity ⟨0, h⟩) → ChallengeTree pSpec arity (Fin.succ 0))
    (pre : Transcript (Fin.castSucc 0) pSpec) :
    (ChallengeTree.chalNode (arity := arity) 0 h chals children).transcripts pre = [] := by
  simp only [ChallengeTree.transcripts]
  rw [List.eq_nil_iff_forall_not_mem]
  intro tr htr
  rw [List.mem_flatMap] at htr
  obtain ⟨j, -, -⟩ := htr
  have hj := j.isLt
  omega

end ProtocolSpec.ChallengeTree.NonVacuity
