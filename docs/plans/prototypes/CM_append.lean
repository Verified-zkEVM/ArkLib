/-
PROTOTYPE: sequential composition of witness-only extractors — all four theorems.

`TreeBased.append verify₁ E₁ E₂` threads the leaf witnessings through the seam: the composed
extract runs the left extractor on the prefix tree, feeding it, per prefix leaf, the right
extractor's output on the suffix tree below that leaf — at the intermediate statement computed
by `verify₁`, the LEFT VERIFIER's verdict function, passed as data (in packages: read off the
`PureForm`/`GuardedForm` field). The extractors attribute no statements, so composition needs
no path splitting: the only path machinery on the runtime path is `AppendSplit.gluePath`
(landed in the library by M3 step 3b — see Part A's note).

Proved here:
  - `append_treeSpecialSoundWith` (pure left factor). The load-bearing moves: prefix acceptance
    is established by running the RIGHT certificate at the canonical witnessing first (`key0`),
    which licenses the LEFT certificate; the two witnessing-validity transfers ride
    `fullTranscript_gluePath` + `append_run_outputs` (validity is `Outputs`-relative, so left
    purity rewrites the output set directly), and the prefix witnessing's reachability comes
    from `pure_verdict_mem_outputs` at the prefix tree's own acceptance.
  - `append_treeSpecialSoundWithEscape` (pure left) — at the repo's UNCHANGED
    `ChallengeTree.EscapeEvent.append`.
  - `append_treeSpecialSoundWith_guardedLeft` — the guarded-left twin (`hcheck` first, learned
    from one `somePath` suffix leaf, then the pure skeleton at the guarded lemmas).
  - `append_treeSpecialSoundWithEscape_guardedLeft` — escape × guarded-left: the statement
    `Guarded.lean:141` hides behind a `sorry` today, proved here in full generality.
  - Runtime demos: 2-fold and 3-fold chains `#eval` through the composed extractor and
    kernel-`rfl` — `verify₁`, `gluePath`, and (3-fold) the composed seam function
    (`PureForm.append`'s data, transcript split at runtime) all on the executable path.
-/
import ArkLib.OracleReduction.Security.TranscriptTree
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree

/-! ## Part A — leaf-path glue for `appendSplit`

**Landed in the library** by milestone M3 step 3b: `LeafPath.embedRight`, `SplitData.gluePath`,
the transcript specs, `LeafPath.transport` and `AppendSplit.gluePath` +
`fullTranscript_gluePath` now live in
`ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean`, imported above, so the copy
that used to sit here was deleted to avoid `has already been declared`. The transcription was
verbatim; Parts B–F below still exercise the glue, so E10's evidence is unchanged. -/

/-! ## Part B — the witness-only core (as in `CM_gates.lean`) -/

namespace CM

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-- The statements the verifier can output on `(stmtIn, tr)` under the fixed sampling. -/
def Outputs (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript) :
    Set StmtOut :=
  {out | some out ∈ support (do (simulateQ impl (V.run stmtIn tr)).run' (← init))}

/-- One candidate output witness per root-to-leaf transcript. -/
def LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=
  ChallengeTree.LeafPath tree → Option WitOut

/-- Validity: each answer certifies, in `relOut`, some reachable output statement. -/
def LeafWitnesses.IsValid (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (o : LeafWitnesses tree WitOut) : Prop :=
  ∀ p, ∃ w, o p = some w ∧
    ∃ out ∈ Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut

/-- The witness-only tree extractor. -/
def TreeBased (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → (tree : ChallengeTree pSpec arity 0) → LeafWitnesses tree WitOut → Option WitIn

/-- The revised notion. -/
def treeSpecialSoundWith (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
      ∀ o : LeafWitnesses tree WitOut, LeafWitnesses.IsValid init impl V relOut stmtIn o →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- The escape twin. -/
def treeSpecialSoundWithEscape (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (S : ChallengeTreeShape pSpec) (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
      esc stmtIn tree ∨
      ∀ o : LeafWitnesses tree WitOut, LeafWitnesses.IsValid init impl V relOut stmtIn o →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

theorem mem_outputs_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript)
    (out : StmtOut) :
    out ∈ Outputs init impl V stmtIn tr ↔
      out ∈ support (OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)) := by
  rw [OptionT.mem_support_iff, OptionT.run_mk]; rfl

/-- Under `IsAccepting`, every reachable output at a leaf is in the language. -/
theorem mem_language_of_mem_outputs {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relOut : Set (StmtOut × WitOut)} {stmtIn : StmtIn}
    {tree : ChallengeTree pSpec arity 0}
    (hacc : tree.IsAccepting init impl V stmtIn relOut.language)
    (p : ChallengeTree.LeafPath tree) {out : StmtOut}
    (hout : out ∈ Outputs init impl V stmtIn p.fullTranscript) :
    out ∈ relOut.language := by
  have h := hacc p.fullTranscript p.mem_fullTranscripts
  rw [probEvent_eq_one_iff] at h
  exact h.2 out ((mem_outputs_iff init impl V stmtIn p.fullTranscript out).1 hout)

theorem not_isAccepting_of_no_outputs (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (p : ChallengeTree.LeafPath tree) (lang : Set StmtOut)
    (hrej : Outputs init impl V stmtIn p.fullTranscript = ∅) :
    ¬ tree.IsAccepting init impl V stmtIn lang := by
  intro hacc
  have h := hacc p.fullTranscript p.mem_fullTranscripts
  rw [probEvent_eq_one_iff] at h
  have hsupp : support (OptionT.mk do
      (simulateQ impl (V.run stmtIn p.fullTranscript)).run' (← init)) = ∅ := by
    ext x
    rw [← mem_outputs_iff, hrej]
  rw [probFailure_eq_one hsupp] at h
  exact one_ne_zero h.1

/-- Under `IsAccepting` the reachable-output set at every leaf is NONEMPTY. -/
theorem outputs_nonempty_of_isAccepting {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0}
    {lang : Set StmtOut} (hacc : tree.IsAccepting init impl V stmtIn lang)
    (p : ChallengeTree.LeafPath tree) :
    (Outputs init impl V stmtIn p.fullTranscript).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  exact not_isAccepting_of_no_outputs init impl V stmtIn p lang hempty hacc

/-- An accepting tree with a leaf forces the sampling's support to be nonempty. -/
theorem support_init_nonempty_of_accepting {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0} {lang : Set StmtOut}
    (hacc : tree.IsAccepting init impl V stmtIn lang)
    (p : ChallengeTree.LeafPath tree) :
    (support init).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  refine not_isAccepting_of_no_outputs init impl V stmtIn p lang ?_ hacc
  ext out
  simp only [Outputs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨s, hs, -⟩ := hmem
  rw [hempty] at hs
  simp at hs

/-- A pure verifier's output set is a subset of the singleton of its verdict. -/
theorem outputs_pure_subsingleton {Stmt₁ Stmt₂ : Type} {m : ℕ} {pSpec₁ : ProtocolSpec m}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) {out : Stmt₂}
    (hout : out ∈ Outputs init impl V₁ stmt tr) : out = verify₁ stmt tr := by
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV₁] at hout
  have : (do (simulateQ impl
      (pure (verify₁ stmt tr) : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
      ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some (verify₁ stmt tr))) := by
    congr 1
  rw [this] at hout
  simp only [support_bind_const, support_pure, Set.mem_setOf_eq] at hout
  exact Option.some.inj hout.1

/-- A pure verifier's verdict IS reachable, given a productive sampling. -/
theorem pure_verdict_mem_outputs (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {V : Verifier oSpec StmtIn StmtOut pSpec}
    (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (hV : ∀ stmt tr, V.verify stmt tr = pure (verify stmt tr))
    (hinit : (support init).Nonempty) (stmtIn : StmtIn) (tr : pSpec.FullTranscript) :
    verify stmtIn tr ∈ Outputs init impl V stmtIn tr := by
  obtain ⟨s, hs⟩ := hinit
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV]
  have heq : (do (simulateQ impl
      (pure (verify stmtIn tr) : OptionT (OracleComp oSpec) StmtOut)).run' (← init) :
      ProbComp (Option StmtOut)) = (init >>= fun _ => pure (some (verify stmtIn tr))) := by
    congr 1
  rw [heq]
  exact (mem_support_bind_iff init _ _).2 ⟨s, hs, (mem_support_pure_iff _ _).2 rfl⟩

open scoped Classical in
/-- The canonical witnessing. -/
noncomputable def canonWitnesses (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} : LeafWitnesses tree WitOut :=
  fun p =>
    if h : ∃ w, ∃ out ∈ Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut
    then some h.choose else none

/-- `canonWitnesses` is valid on every accepting tree. -/
theorem canonWitnesses_isValid {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relOut : Set (StmtOut × WitOut)} {stmtIn : StmtIn}
    {tree : ChallengeTree pSpec arity 0}
    (hacc : tree.IsAccepting init impl V stmtIn relOut.language) :
    LeafWitnesses.IsValid init impl V relOut stmtIn
      (canonWitnesses init impl V relOut stmtIn (tree := tree)) := by
  intro p
  obtain ⟨out, hout⟩ := outputs_nonempty_of_isAccepting hacc p
  obtain ⟨w, hw⟩ := (Set.mem_language_iff relOut _).1 (mem_language_of_mem_outputs hacc p hout)
  have hex : ∃ w, ∃ out ∈ Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut :=
    ⟨w, out, hout, hw⟩
  exact ⟨hex.choose, by simp [canonWitnesses, dif_pos hex], hex.choose_spec⟩

end CM

/-! ## Part C — the appended verifier's outputs through a pure left factor -/

namespace CM

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The appended verifier's output set at a glued transcript is the right verifier's at the left
verdict. -/
theorem append_run_outputs
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
    Outputs init impl (V₁.append V₂) stmt (tr₁ ++ₜ tr₂)
      = Outputs init impl V₂ (verify₁ stmt tr₁) tr₂ := by
  unfold Outputs
  rw [Verifier.append_run_pure_left V₁ V₂ verify₁ hV₁ stmt tr₁ tr₂]

end CM

/-! ## Part D — `TreeBased.append` and the composition theorems -/

namespace CM

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Sequential composition of witness-only extractors.** The intermediate statement is
computed by `verify₁` — the left verifier's verdict function, passed as DATA (packages read it
off their `PureForm`/`GuardedForm` field). The extract runs the left extractor on the prefix
tree, feeding it the right extractor's output below each prefix leaf. The only path machinery
on the runtime path is `AppendSplit.gluePath`. -/
def TreeBased.append (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ arity₁)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ arity₂) :
    TreeBased Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) :=
  fun stmt tree o =>
    E₁ stmt tree.appendSplit.fst fun p₁ =>
      E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **THE COMPOSITION THEOREM (pure left factor).** Prefix acceptance via the right
certificate at the canonical witnessing (`key0`); validity transfers ride
`fullTranscript_gluePath` + `append_run_outputs`. -/
theorem append_treeSpecialSoundWith
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWith init impl S₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWith init impl S₂ rel₂ rel₃ V₂ E₂) :
    treeSpecialSoundWith init impl (S₁.append S₂) rel₁ rel₃ (V₁.append V₂)
      (TreeBased.append verify₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  -- Step 0: every suffix tree is accepting for V₂ at the left verdict.
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (verify₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    simpa [Verifier.append_run_pure_left V₁ V₂ verify₁ hV₁
      stmt p₁.fullTranscript tr₂] using hfull
  -- Step 1: the downstream certificate at each prefix leaf, at the left verdict.
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  -- Step 2: a rel₂-witness exists at every left verdict (via the canonical witnessing).
  have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ∃ w₂, (verify₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
    intro p₁
    obtain ⟨w₂, -, hw₂⟩ := h₂' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
    exact ⟨w₂, hw₂⟩
  -- Step 3: the prefix tree is accepting for V₁.
  have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
    intro tr₁ htr₁
    obtain ⟨p₁, rfl⟩ :=
      ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
    obtain ⟨w₂, hw₂⟩ := key0 p₁
    exact Verifier.pure_accepting_of_mem init impl V₁ stmt p₁.fullTranscript rel₂.language
      (verify₁ stmt p₁.fullTranscript) (hV₁ stmt p₁.fullTranscript)
      ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
  -- Step 4: extraction on every valid witnessing.
  intro o hvalid
  -- each suffix witnessing is valid for V₂ at the left verdict: validity is `Outputs`-relative,
  -- so `fullTranscript_gluePath` + `append_run_outputs` transfer it — no claim identification.
  have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
      LeafWitnesses.IsValid init impl V₂ rel₃ (verify₁ stmt p₁.fullTranscript)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
    intro p₁ p₂
    obtain ⟨w, hw, out, hout, hrel⟩ :=
      hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
    refine ⟨w, hw, out, ?_, hrel⟩
    -- note-6 move: author the transfer at the `appendArity` forms (where both rewrites are
    -- syntactic), close against the notion-typed instance by `exact` (full transparency).
    have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
        (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
        out ∈ Outputs init impl (V₁.append V₂) stmt
          (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
        out ∈ Outputs init impl V₂ (verify₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
      intro T q₁ q₂ h
      rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
      rwa [append_run_outputs init impl V₁ V₂ verify₁ hV₁] at h
    exact key tree p₁ p₂ hout
  -- the prefix witnessing — E₂'s outputs below each prefix leaf — is valid for V₁: the verdict
  -- is reachable (`pure_verdict_mem_outputs`) and E₂'s certificate makes its output a
  -- rel₂-witness for it.
  have hpreValid : LeafWitnesses.IsValid init impl V₁ rel₂ stmt
      (fun p₁ => E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
    intro p₁
    obtain ⟨w₂, hw₂, hrel₂⟩ := h₂' p₁ _ (hsuffValid p₁)
    exact ⟨w₂, hw₂, verify₁ stmt p₁.fullTranscript,
      pure_verdict_mem_outputs init impl verify₁ hV₁
        (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript, hrel₂⟩
  -- close with the left certificate.
  exact h₁ stmt tree.appendSplit.fst
    (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc _ hpreValid

/-- **The escape composition (pure left factor)**, at the repo's UNCHANGED
`ChallengeTree.EscapeEvent.append`. The disjunction routing: a right-factor escape anywhere
fires the composed event's right disjunct; else every suffix certificate extracts, `key0`
licenses the left certificate, whose escape fires the left disjunct or whose extraction closes
the plain skeleton. -/
theorem append_treeSpecialSoundWithEscape
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWithEscape init impl S₂ esc₂ rel₂ rel₃ V₂ E₂) :
    treeSpecialSoundWithEscape init impl (S₁.append S₂)
      (ChallengeTree.EscapeEvent.append esc₁ esc₂ verify₁) rel₁ rel₃ (V₁.append V₂)
      (TreeBased.append verify₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (verify₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    simpa [Verifier.append_run_pure_left V₁ V₂ verify₁ hV₁
      stmt p₁.fullTranscript tr₂] using hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  by_cases hesc₂ : ∃ p₁ : LeafPath tree.appendSplit.fst,
      esc₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
  · exact Or.inl (Or.inr hesc₂)
  · push Not at hesc₂
    have h₂'' := fun p₁ : LeafPath tree.appendSplit.fst => (h₂' p₁).resolve_left (hesc₂ p₁)
    have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
        ∃ w₂, (verify₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
      intro p₁
      obtain ⟨w₂, -, hw₂⟩ := h₂'' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
      exact ⟨w₂, hw₂⟩
    have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨p₁, rfl⟩ :=
        ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
      obtain ⟨w₂, hw₂⟩ := key0 p₁
      exact Verifier.pure_accepting_of_mem init impl V₁ stmt p₁.fullTranscript rel₂.language
        (verify₁ stmt p₁.fullTranscript) (hV₁ stmt p₁.fullTranscript)
        ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
    rcases h₁ stmt tree.appendSplit.fst
      (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc with
      hesc₁ | hext₁
    · exact Or.inl (Or.inl hesc₁)
    · refine Or.inr fun o hvalid => ?_
      have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
          LeafWitnesses.IsValid init impl V₂ rel₃ (verify₁ stmt p₁.fullTranscript)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
        intro p₁ p₂
        obtain ⟨w, hw, out, hout, hrel⟩ :=
          hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
        refine ⟨w, hw, out, ?_, hrel⟩
        have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
            (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
            out ∈ Outputs init impl (V₁.append V₂) stmt
              (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
            out ∈ Outputs init impl V₂ (verify₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
          intro T q₁ q₂ h
          rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
          rwa [append_run_outputs init impl V₁ V₂ verify₁ hV₁] at h
        exact key tree p₁ p₂ hout
      have hpreValid : LeafWitnesses.IsValid init impl V₁ rel₂ stmt
          (fun p₁ => E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
        intro p₁
        obtain ⟨w₂, hw₂, hrel₂⟩ := h₂'' p₁ _ (hsuffValid p₁)
        exact ⟨w₂, hw₂, verify₁ stmt p₁.fullTranscript,
          pure_verdict_mem_outputs init impl verify₁ hV₁
            (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript, hrel₂⟩
      exact hext₁ _ hpreValid

end CM

/-! ## Part E — the guarded seam -/

namespace ProtocolSpec.ChallengeTree

variable {n : ℕ} {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}

/-- A computable leaf path of any tree with positive branching (a guarded left factor learns
`check₁ = true` only from *some* suffix leaf). -/
def somePath (harity : ∀ i, 0 < arity i) :
    {m : Fin (n + 1)} → (t : ChallengeTree pSpec arity m) → LeafPath t
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (somePath harity child)
  | _, .chalNode k h _ children =>
      .chal ⟨0, harity ⟨k, h⟩⟩ (somePath harity (children ⟨0, harity ⟨k, h⟩⟩))

end ProtocolSpec.ChallengeTree

namespace CM

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- Acceptance with probability one forces the sampling to have nonempty support
(transcript-level form; Part B's `support_init_nonempty_of_accepting` is the tree-level one). -/
theorem support_init_nonempty_of_prob_one {StmtIn StmtOut : Type} {k : ℕ}
    {pSpec : ProtocolSpec k} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmt : StmtIn} {tr : pSpec.FullTranscript} {lang : Set StmtOut}
    (h : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) :
    (support init).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  rw [probEvent_eq_one_iff] at h
  obtain ⟨hFail, -⟩ := h
  rw [OptionT.probFailure_eq, OptionT.run_mk] at hFail
  have hsupp : support (do (simulateQ impl (V.run stmt tr)).run' (← init) :
      ProbComp (Option StmtOut)) = ∅ := by
    simp [support_bind, hempty]
  rw [probFailure_eq_one hsupp] at hFail
  simp at hFail

/-- Acceptance is impossible for a `failure` verdict. -/
theorem not_accepting_of_failure {StmtIn StmtOut : Type} {k : ℕ} {pSpec : ProtocolSpec k}
    {V : Verifier oSpec StmtIn StmtOut pSpec} {stmt : StmtIn} {tr : pSpec.FullTranscript}
    (hV : V.verify stmt tr = failure) {lang : Set StmtOut}
    (h : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) : False := by
  have hne : (support init).Nonempty := support_init_nonempty_of_prob_one init impl h
  rw [probEvent_eq_one_iff] at h
  obtain ⟨hFail, -⟩ := h
  rw [OptionT.probFailure_eq, OptionT.run_mk] at hFail
  simp only [Verifier.run, hV] at hFail
  have hc : (do (simulateQ impl (failure : OptionT (OracleComp oSpec) StmtOut)).run' (← init) :
      ProbComp (Option StmtOut)) = (init >>= fun _ => pure none) := by congr 1
  rw [hc] at hFail
  have h0 : Pr[= (none : Option StmtOut) | (init >>= fun _ => pure none : ProbComp _)] = 0 :=
    (add_eq_zero.mp hFail).2
  rw [probOutput_eq_zero_iff] at h0
  exact h0 (by simp [hne])

/-- Guarded analogue of `append_run_pure_left`. -/
theorem append_run_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
    (V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) =
      if check₁ stmt tr₁ then V₂.run (out₁ stmt tr₁) tr₂ else failure := by
  rw [Verifier.append_run]
  simp only [Verifier.run, FullTranscript.append_fst, FullTranscript.append_snd, hV₁ stmt tr₁]
  by_cases hc : check₁ stmt tr₁ <;> simp [hc]

/-- On a guarded left factor, `Outputs` at a passing guard is the right factor's at the
verdict. -/
theorem append_run_outputs_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript)
    (hc : check₁ stmt tr₁ = true) :
    Outputs init impl (V₁.append V₂) stmt (tr₁ ++ₜ tr₂)
      = Outputs init impl V₂ (out₁ stmt tr₁) tr₂ := by
  unfold Outputs
  rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt tr₁ tr₂, if_pos hc]

/-- A guarded verifier's output set pins BOTH the guard and the verdict. -/
theorem outputs_guarded_subsingleton
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) {out : Stmt₂}
    (hout : out ∈ Outputs init impl V₁ stmt tr) : out = out₁ stmt tr := by
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV₁ stmt tr] at hout
  by_cases hc : check₁ stmt tr
  · rw [if_pos hc] at hout
    have : (do (simulateQ impl
        (pure (out₁ stmt tr) : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
        ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some (out₁ stmt tr))) := by
      congr 1
    rw [this] at hout
    simp only [support_bind_const, support_pure, Set.mem_setOf_eq] at hout
    exact Option.some.inj hout.1
  · rw [if_neg (by simpa using hc)] at hout
    have : (do (simulateQ impl (failure : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
        ProbComp (Option Stmt₂)) = (init >>= fun _ => pure none) := by
      congr 1
    rw [this] at hout
    simp only [support_bind_const, support_pure, Set.mem_setOf_eq] at hout
    exact absurd hout.1 (by simp)

/-- Guarded analogue of `pure_accepting_of_mem`. -/
theorem guarded_accepting_of_mem [∀ i, SampleableType (pSpec₁.Challenge i)]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (hc : check₁ stmt tr = true)
    (lang : Set Stmt₂) (hmem : out₁ stmt tr ∈ lang) :
    Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V₁.run stmt tr)).run' (← init)] = 1 :=
  Verifier.pure_accepting_of_mem init impl V₁ stmt tr lang (out₁ stmt tr)
    (by rw [hV₁ stmt tr, if_pos hc]) hmem

/-- A guarded verifier's verdict IS reachable where its check passes, given a productive
sampling — the guarded analogue of `pure_verdict_mem_outputs`. -/
theorem guarded_verdict_mem_outputs
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (hinit : (support init).Nonempty)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (hc : check₁ stmt tr = true) :
    out₁ stmt tr ∈ Outputs init impl V₁ stmt tr := by
  obtain ⟨s, hs⟩ := hinit
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV₁ stmt tr]
  rw [if_pos hc]
  have heq : (do (simulateQ impl
      (pure (out₁ stmt tr) : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
      ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some (out₁ stmt tr))) := by
    congr 1
  rw [heq]
  exact (mem_support_bind_iff init _ _).2 ⟨s, hs, (mem_support_pure_iff _ _).2 rfl⟩

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **The guarded-left composition.** `hcheck` — every prefix guard passes on an accepting
composed tree, learned from one `somePath` suffix leaf — comes first; the rest is the pure-left
skeleton at the guarded lemmas. -/
theorem append_treeSpecialSoundWith_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < S₂.arity i)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWith init impl S₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWith init impl S₂ rel₂ rel₃ V₂ E₂) :
    treeSpecialSoundWith init impl (S₁.append S₂) rel₁ rel₃ (V₁.append V₂)
      (TreeBased.append out₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  have hcheck : ∀ p₁ : LeafPath tree.appendSplit.fst,
      check₁ stmt p₁.fullTranscript = true := by
    intro p₁
    by_contra hc
    have hpath₂ := ChallengeTree.somePath harity₂ (tree.appendSplit.sndAt p₁)
    have hmem : p₁.fullTranscript ++ₜ hpath₂.fullTranscript ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁
        hpath₂.mem_fullTranscripts
    exact not_accepting_of_failure init impl
      (V := V₁.append V₂) (stmt := stmt)
      (tr := p₁.fullTranscript ++ₜ hpath₂.fullTranscript)
      (by
        have h := append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt p₁.fullTranscript
          hpath₂.fullTranscript
        rw [if_neg hc] at h
        exact h)
      (hAccept _ hmem)
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (out₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    rw [show (V₁.append V₂).run stmt (p₁.fullTranscript ++ₜ tr₂)
        = V₂.run (out₁ stmt p₁.fullTranscript) tr₂ from by
      rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁, if_pos (hcheck p₁)]] at hfull
    exact hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ∃ w₂, (out₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
    intro p₁
    obtain ⟨w₂, -, hw₂⟩ := h₂' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
    exact ⟨w₂, hw₂⟩
  have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
    intro tr₁ htr₁
    obtain ⟨p₁, rfl⟩ :=
      ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
    obtain ⟨w₂, hw₂⟩ := key0 p₁
    exact guarded_accepting_of_mem init impl V₁ check₁ out₁ hV₁ stmt p₁.fullTranscript
      (hcheck p₁) rel₂.language ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
  intro o hvalid
  have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
      LeafWitnesses.IsValid init impl V₂ rel₃ (out₁ stmt p₁.fullTranscript)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
    intro p₁ p₂
    obtain ⟨w, hw, out, hout, hrel⟩ :=
      hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
    refine ⟨w, hw, out, ?_, hrel⟩
    have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
        (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
        check₁ stmt q₁.fullTranscript = true →
        out ∈ Outputs init impl (V₁.append V₂) stmt
          (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
        out ∈ Outputs init impl V₂ (out₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
      intro T q₁ q₂ hcq h
      rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
      rwa [append_run_outputs_guardedLeft init impl V₁ V₂ check₁ out₁ hV₁ stmt _ _ hcq] at h
    exact key tree p₁ p₂ (hcheck p₁) hout
  have hpreValid : LeafWitnesses.IsValid init impl V₁ rel₂ stmt
      (fun p₁ => E₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
    intro p₁
    obtain ⟨w₂, hw₂, hrel₂⟩ := h₂' p₁ _ (hsuffValid p₁)
    exact ⟨w₂, hw₂, out₁ stmt p₁.fullTranscript,
      guarded_verdict_mem_outputs init impl V₁ check₁ out₁ hV₁
        (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript (hcheck p₁),
      hrel₂⟩
  exact h₁ stmt tree.appendSplit.fst
    (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc _ hpreValid

/-- **The escape × guarded-left composition** — the statement `Guarded.lean:141` hides behind a
`sorry` today, at the repo's UNCHANGED `ChallengeTree.EscapeEvent.append`. On an accepting
composed tree `hcheck` forces every prefix guard to pass, after which the escape routing is the
pure-left escape proof at the guarded lemmas. -/
theorem append_treeSpecialSoundWithEscape_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < S₂.arity i)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWithEscape init impl S₂ esc₂ rel₂ rel₃ V₂ E₂) :
    treeSpecialSoundWithEscape init impl (S₁.append S₂)
      (ChallengeTree.EscapeEvent.append esc₁ esc₂ out₁) rel₁ rel₃ (V₁.append V₂)
      (TreeBased.append out₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  have hcheck : ∀ p₁ : LeafPath tree.appendSplit.fst,
      check₁ stmt p₁.fullTranscript = true := by
    intro p₁
    by_contra hc
    have hpath₂ := ChallengeTree.somePath harity₂ (tree.appendSplit.sndAt p₁)
    have hmem : p₁.fullTranscript ++ₜ hpath₂.fullTranscript ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁
        hpath₂.mem_fullTranscripts
    exact not_accepting_of_failure init impl
      (V := V₁.append V₂) (stmt := stmt)
      (tr := p₁.fullTranscript ++ₜ hpath₂.fullTranscript)
      (by
        have h := append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt p₁.fullTranscript
          hpath₂.fullTranscript
        rw [if_neg hc] at h
        exact h)
      (hAccept _ hmem)
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (out₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    rw [show (V₁.append V₂).run stmt (p₁.fullTranscript ++ₜ tr₂)
        = V₂.run (out₁ stmt p₁.fullTranscript) tr₂ from by
      rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁, if_pos (hcheck p₁)]] at hfull
    exact hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  by_cases hesc₂ : ∃ p₁ : LeafPath tree.appendSplit.fst,
      esc₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
  · exact Or.inl (Or.inr hesc₂)
  · push Not at hesc₂
    have h₂'' := fun p₁ : LeafPath tree.appendSplit.fst => (h₂' p₁).resolve_left (hesc₂ p₁)
    have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
        ∃ w₂, (out₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
      intro p₁
      obtain ⟨w₂, -, hw₂⟩ := h₂'' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
      exact ⟨w₂, hw₂⟩
    have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨p₁, rfl⟩ :=
        ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
      obtain ⟨w₂, hw₂⟩ := key0 p₁
      exact guarded_accepting_of_mem init impl V₁ check₁ out₁ hV₁ stmt p₁.fullTranscript
        (hcheck p₁) rel₂.language ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
    rcases h₁ stmt tree.appendSplit.fst
      (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc with
      hesc₁ | hext₁
    · exact Or.inl (Or.inl hesc₁)
    · refine Or.inr fun o hvalid => ?_
      have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
          LeafWitnesses.IsValid init impl V₂ rel₃ (out₁ stmt p₁.fullTranscript)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
        intro p₁ p₂
        obtain ⟨w, hw, out, hout, hrel⟩ :=
          hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
        refine ⟨w, hw, out, ?_, hrel⟩
        have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
            (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
            check₁ stmt q₁.fullTranscript = true →
            out ∈ Outputs init impl (V₁.append V₂) stmt
              (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
            out ∈ Outputs init impl V₂ (out₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
          intro T q₁ q₂ hcq h
          rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
          rwa [append_run_outputs_guardedLeft init impl V₁ V₂ check₁ out₁ hV₁ stmt _ _ hcq]
            at h
        exact key tree p₁ p₂ (hcheck p₁) hout
      have hpreValid : LeafWitnesses.IsValid init impl V₁ rel₂ stmt
          (fun p₁ => E₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
        intro p₁
        obtain ⟨w₂, hw₂, hrel₂⟩ := h₂'' p₁ _ (hsuffValid p₁)
        exact ⟨w₂, hw₂, out₁ stmt p₁.fullTranscript,
          guarded_verdict_mem_outputs init impl V₁ check₁ out₁ hV₁
            (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript
            (hcheck p₁), hrel₂⟩
      exact hext₁ _ hpreValid

end CM

/-! ## Part F — runtime demo: 2-fold and 3-fold chains through the composed extractor -/

namespace CMDemo

open ProtocolSpec ProtocolSpec.ChallengeTree CM

instance : IsEmpty ((!p[] : ProtocolSpec 0).ChallengeIdx) :=
  ⟨fun i => Fin.elim0 i.1⟩

instance : IsEmpty (((!p[] : ProtocolSpec 0) ++ₚ (!p[] : ProtocolSpec 0)).ChallengeIdx) :=
  ⟨fun i => Fin.elim0 i.1⟩

/-- The unique leaf path of a challenge-free tree. -/
def onlyPath {n : ℕ} {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}
    [IsEmpty pSpec.ChallengeIdx] :
    {m : Fin (n + 1)} → (t : ChallengeTree pSpec arity m) → ChallengeTree.LeafPath t
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (onlyPath child)
  | _, .chalNode m h _ _ => isEmptyElim (⟨m, h⟩ : pSpec.ChallengeIdx)

/-- Left engine: forward the leaf witness, plus one if the seam statement is `true`-flavored. -/
def leftExt (arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ) :
    TreeBased Unit ℕ ℕ (!p[] : ProtocolSpec 0) arity :=
  fun _ tree o => (o (onlyPath tree)).map (· + 1)

/-- Right engine: double the leaf witness; the statement input is the seam value `verify₁`
computes at runtime. -/
def rightExt (arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ) :
    TreeBased Bool ℕ ℕ (!p[] : ProtocolSpec 0) arity :=
  fun b tree o => (o (onlyPath tree)).map (fun w => if b then 2 * w else w)

/-- The composed extractor: `verify₁ := fun _ _ => true` is the seam data a package would read
off its `PureForm`. -/
def chain : TreeBased Unit ℕ ℕ ((!p[] : ProtocolSpec 0) ++ₚ (!p[] : ProtocolSpec 0))
    (appendArity (fun _ => 1) (fun _ => 1)) :=
  TreeBased.append (fun _ _ => true) (leftExt _) (rightExt _)

-- The composed extract runs: top witnessing `some 5` → right engine doubles at the seam
-- statement `true` → left engine adds one: `some 11`.
#eval chain () ChallengeTree.leaf (fun _ => some 5)

/-- Kernel-checked: the composed runtime result is definitional, not an accident of `#eval`. -/
theorem chain_eval : chain () ChallengeTree.leaf (fun _ => some 5) = some 11 := rfl

/-- Declining leaves decline the chain: no junk is invented. -/
theorem chain_none : chain () ChallengeTree.leaf (fun _ => none) = none := rfl

/-! ### The 3-fold chain: the composed seam function runs at runtime

In a ≥3-fold chain the left factor is itself composed, so its seam function is the composed
verdict `PureForm.append` supplies — a transcript-level read (`tr.fst`/`tr.snd` plus the two
verdicts). This is the ONLY extra machinery a deep chain runs; nothing traverses paths besides
`gluePath`. -/

/-- The 2-fold chain's own verdict function, composed exactly as `PureForm.append` composes it:
first factor's verdict (`fun _ _ => true`) on the prefix half, second factor's (`not`) on the
suffix half. -/
def composedVerify :
    Unit → ((!p[] : ProtocolSpec 0) ++ₚ (!p[] : ProtocolSpec 0)).FullTranscript → Bool :=
  fun _ tr =>
    (fun (b : Bool) (_ : (!p[] : ProtocolSpec 0).FullTranscript) => !b)
      ((fun (_ : Unit) (_ : (!p[] : ProtocolSpec 0).FullTranscript) => true) () tr.fst) tr.snd

/-- Third engine: statement-sensitive on the seam value the composed verdict computes. -/
def thirdExt (arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ) :
    TreeBased Bool ℕ ℕ (!p[] : ProtocolSpec 0) arity :=
  fun b tree o => (o (onlyPath tree)).map (fun w => if b then 2 * w else w + 100)

/-- The 3-fold chain: `(left ▷ right) ▷ third`, seamed by `composedVerify`. -/
def chain₃ := TreeBased.append composedVerify chain (thirdExt (fun _ => 1))

-- composedVerify () (empty transcript) = !true = false → thirdExt adds 100: some 105;
-- then the inner chain doubles (seam `true`) and adds one: 105*2 + 1 = 211.
#eval chain₃ () ChallengeTree.leaf (fun _ => some 5)

/-- Kernel-checked: the composed seam function (transcript split + two verdicts) is on the
definitional runtime path. -/
theorem chain₃_eval : chain₃ () ChallengeTree.leaf (fun _ => some 5) = some 211 := rfl

end CMDemo

section Audit
#print axioms CM.append_treeSpecialSoundWith
#print axioms CM.append_treeSpecialSoundWithEscape
#print axioms CM.append_treeSpecialSoundWith_guardedLeft
#print axioms CM.append_treeSpecialSoundWithEscape_guardedLeft
#print axioms CM.canonWitnesses_isValid
#print axioms CM.append_run_outputs
#print axioms CM.append_run_outputs_guardedLeft
#print axioms CM.outputs_guarded_subsingleton
#print axioms CM.guarded_verdict_mem_outputs
#print axioms ProtocolSpec.ChallengeTree.AppendSplit.fullTranscript_gluePath
#print axioms CMDemo.chain_eval
#print axioms CMDemo.chain_none
#print axioms CMDemo.chain₃_eval
end Audit

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for nm in [``CMDemo.chain, ``CMDemo.chain₃, ``CMDemo.leftExt, ``CMDemo.rightExt,
      ``CMDemo.thirdExt, ``CMDemo.composedVerify, ``CMDemo.onlyPath,
      ``ProtocolSpec.ChallengeTree.SplitData.gluePath,
      ``ProtocolSpec.ChallengeTree.AppendSplit.gluePath,
      ``ProtocolSpec.ChallengeTree.somePath] do
    match Lean.IR.findEnvDecl env nm with
    | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
    | none   => Lean.logWarning m!"NO IR (noncomputable): {nm}"
