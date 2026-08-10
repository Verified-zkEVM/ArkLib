/-
PROTOTYPE: the witness-only extractor notion, its adversarial gates, purity as data, and the
transports.

The extractor is a bare function — it consumes the tree AND one candidate output witness per
leaf (`LeafWitnesses`), and produces an input witness. It attributes NO statements: a
witnessing is valid when each answer certifies, in `relOut`, some statement the verifier can
actually output on that leaf's transcript (`Outputs`-membership INSIDE `IsValid`). Statement
attribution lives where it semantically belongs — with the verifier; on the data side it is
carried by `PureForm` (purity with its verdict function as data), which is what composition
reads.

The gates are why the notion has exactly this shape; each is refutation-resistant evidence that
a differently-typed variant is worse. Do not weaken the notion without re-running them.
  G0  the ∀-variant kill: one witness per leaf required to serve EVERY reachable output makes
      the notion VACUOUS on a two-output randomized verifier — provable at the constant-`none`
      extractor with `relIn = ∅` where the classical notion is refutable. The adopted `IsValid`
      is the ∃-form: each witness serves SOME reachable output;
  G1  a valid witnessing exists at the ∃-form on that same two-output `coinVerifier` — the
      premise is satisfiable exactly where the ∀-form collapses;
  G2  the notion is refutable at `relIn = ∅` for EVERY extractor — genuine non-vacuity;
  G3  reachability inside `IsValid` has teeth: at a REACHABILITY-FREE validity (any
      `relOut`-witness at any statement, reachable or not) the forwarding extractor on sound
      data is REFUTED, while the adopted notion is PROVABLE at it on the same data. Dropping
      reachability breaks real engines — reachability is the notion's honesty discipline,
      carried in the premise;
  G4  `IsValid` fails at the constant-`none` witnessing whenever the tree has a leaf, so no
      chain can be "closed" by feeding it nothing;
  G5  `canonWitnesses` is valid on every accepting tree — the premise is never an obstruction;
  E8  the two-way bridge with the total classical form: `old_of_new` needs `[Inhabited WitIn]`
      and no purity; `new_of_old` = the shim's `ofClassical` certificate — and `ofClassical` is
      a COMPUTABILITY-PRESERVING wrapper (instance-free, no `init/impl/V` argument);
  E26 the transports (shape congruence, event monotonicity) at the single `HEq`;
  E34 `PureForm`/`GuardedForm` (purity as data): the verdict function is package data, and
      `PureForm.append` composes it computably (transcript-level, no path machinery);
  E35 the pure-case collapse: at a pure verifier with nonempty-support `init`, `IsValid` is
      EXACTLY per-verdict witnessing (`isValid_iff_pure`) — engine certificates consume `→`,
      composition proofs produce with `←`;
  E20 the arity-0 degeneracy, a pre-existing sharp edge this notion inherits unchanged;
  E25 codegen calibration: `Prop`-valued and `Set`-valued fields never block `#eval`.
-/
import ArkLib.OracleReduction.Security.TranscriptTree
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree

namespace CM

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-! ## The definitions -/

/-- The statements the verifier can output on `(stmtIn, tr)` under the fixed sampling. -/
def Outputs (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript) :
    Set StmtOut :=
  {out | some out ∈ support (do (simulateQ impl (V.run stmtIn tr)).run' (← init))}

/-- One candidate output witness per root-to-leaf transcript — the "output witnesses" input of a
reduction-of-knowledge extractor. In a chain it is produced by the downstream extractor; at the
top of a security statement, classically from `IsAccepting` (`canonWitnesses`). -/
def LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=
  ChallengeTree.LeafPath tree → Option WitOut

/-- A witnessing is **valid** when it answers at every leaf and each answer certifies, in
`relOut`, some statement the verifier can actually output on that leaf's transcript. The
reachability condition (`Outputs`-membership) is the notion's honesty discipline: trust at a statement the verifier cannot output is not a
witnessing of the tree at all (gate G3). The ∃ over outputs — NOT ∀ — is what keeps the premise
satisfiable at randomized verifiers (gates G0/G1). -/
def LeafWitnesses.IsValid (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (o : LeafWitnesses tree WitOut) : Prop :=
  ∀ p, ∃ w, o p = some w ∧
    ∃ out ∈ Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut

/-- The witness-only tree extractor: assemble an input witness from the tree and witnesses for
its leaves' output claims (or decline). A bare function — the extractor extracts; it does not
attribute statements. `StmtOut` does not appear: output statements enter only through the
soundness notion's validity premise. -/
def TreeBased (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → (tree : ChallengeTree pSpec arity 0) → LeafWitnesses tree WitOut → Option WitIn

/-- The library's `Verifier.treeSpecialSoundWith`: on every structured accepting tree,
extraction succeeds on every valid witnessing. One clause — honesty is the validity premise's
reachability condition, not a separate conjunct. -/
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

/-- The escape twin: same premises, with the escape event as an alternative to extraction (an
escaping factor owes no witness). -/
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

/-- At the never-firing event the escape notion is the plain notion. -/
theorem treeSpecialSoundWithEscape_false_iff (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity) :
    treeSpecialSoundWithEscape init impl S (fun _ _ => False) relIn relOut V Ext ↔
      treeSpecialSoundWith init impl S relIn relOut V Ext := by
  constructor <;> intro h stmtIn tree hstr hacc
  · exact (h stmtIn tree hstr hacc).resolve_left id
  · exact Or.inr (h stmtIn tree hstr hacc)

/-- Lossless escape lift. -/
theorem treeSpecialSoundWith.withEscape {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {S : ChallengeTreeShape pSpec}
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut V Ext) :
    treeSpecialSoundWithEscape init impl S esc relIn relOut V Ext :=
  fun stmtIn tree hstr hacc => Or.inr (h stmtIn tree hstr hacc)

/-! ## Transports: shape congruence and event monotonicity

At the bare-function extractor these are TODAY's repo proofs, verbatim (mirrors of
`TranscriptTree/Basic.lean`'s `treeSpecialSoundWith_congr` / `treeSpecialSoundWithEscape.mono` /
`treeSpecialSoundWithEscape_congr` at the widened type): `subst` at the shape equality
homogenizes the extractor types before the single `HEq` is consumed — the added witnessing
binder is invisible to the proof — and `mono` never inspects the extractor. -/

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Shape-congruence transport, extractor carried across heterogeneously. -/
theorem treeSpecialSoundWith_congr {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity}
    {Ext' : TreeBased StmtIn WitIn WitOut pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWith init impl S relIn relOut V Ext) :
    treeSpecialSoundWith init impl S' relIn relOut V Ext' := by
  subst hS
  obtain rfl := eq_of_heq hExt
  exact h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Event monotonicity at a fixed shape: `.imp (hmono _ _) id` on the outer disjunction, never
touching the extractor. -/
theorem treeSpecialSoundWithEscape.mono {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {S : ChallengeTreeShape pSpec}
    {esc esc' : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    (hmono : ∀ s t, esc s t → esc' s t)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut V Ext) :
    treeSpecialSoundWithEscape init impl S esc' relIn relOut V Ext :=
  fun stmtIn tree hstr hacc => (h stmtIn tree hstr hacc).imp (hmono _ _) id

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Shape congruence carrying both the escape event and the extractor heterogeneously. -/
theorem treeSpecialSoundWithEscape_congr {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {esc' : ChallengeTree.EscapeEvent StmtIn pSpec S'.arity} (hEsc : HEq esc esc')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity}
    {Ext' : TreeBased StmtIn WitIn WitOut pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut V Ext) :
    treeSpecialSoundWithEscape init impl S' esc' relIn relOut V Ext' := by
  subst hS
  obtain rfl := eq_of_heq hEsc
  obtain rfl := eq_of_heq hExt
  exact h

/-! ## Purity as data: `PureForm` and `GuardedForm`

Statement attribution belongs to the verifier. On the proof side it is already there (`Verifier.IsPure`, `IsGuardedWith`); what
composition additionally needs is the verdict function as DATA — extracting it from the
`IsPure` existential costs `Classical.choice`. `PureForm` is that data: the bundled form of
`IsPure`, playing the role `Equiv` plays for `Bijective`. -/

/-- A purity witness carrying its verdict function as data. -/
structure PureForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The verdict: the statement the verifier outputs on `(stmtIn, tr)`. -/
  verify : StmtIn → pSpec.FullTranscript → StmtOut
  /-- The verifier computes exactly that verdict. -/
  verify_eq : ∀ stmtIn tr, V.verify stmtIn tr = pure (verify stmtIn tr)

/-- Forget the data: a `PureForm` yields the `IsPure` class. -/
theorem PureForm.isPure {V : Verifier oSpec StmtIn StmtOut pSpec} (P : PureForm V) :
    V.IsPure :=
  ⟨P.verify, P.verify_eq⟩

/-- The classical converse — the migration shim's cost, quarantined: recovering the data from
the class is a choice. Canonical packages carry `PureForm`; only `ofClassical` lifts pay this. -/
noncomputable def pureFormOfIsPure (V : Verifier oSpec StmtIn StmtOut pSpec) [h : V.IsPure] :
    PureForm V :=
  ⟨h.is_pure.choose, h.is_pure.choose_spec⟩

/-- A guardedness witness carrying check and output map as data (the bundled
`Verifier.IsGuardedWith`). -/
structure GuardedForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The runtime guard. -/
  check : StmtIn → pSpec.FullTranscript → Bool
  /-- The verdict where the guard passes. -/
  out : StmtIn → pSpec.FullTranscript → StmtOut
  /-- The verifier is guarded with exactly these. -/
  verify_eq : V.IsGuardedWith check out

/-- Forget the data: a `GuardedForm` yields the `IsGuarded` class. -/
theorem GuardedForm.isGuarded {V : Verifier oSpec StmtIn StmtOut pSpec} (G : GuardedForm V) :
    V.IsGuarded :=
  ⟨G.check, G.out, G.verify_eq⟩

/-- Every pure form is a guarded form with the trivially-true check (the data form of
`IsGuarded.of_isPure`). -/
def PureForm.toGuardedForm {V : Verifier oSpec StmtIn StmtOut pSpec} (P : PureForm V) :
    GuardedForm V where
  check := fun _ _ => true
  out := P.verify
  verify_eq := fun stmt tr => by rw [P.verify_eq stmt tr]; simp

section PureFormAppend

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- Purity data composes computably: the composed verdict runs the two verdicts through the
transcript seam. Transcript-level (`tr.fst`/`tr.snd`) — no path machinery. This is what a
composed package's extractor reads for its seam statements. -/
def PureForm.append {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂} (P₁ : PureForm V₁) (P₂ : PureForm V₂) :
    PureForm (V₁.append V₂) where
  verify := fun stmt tr => P₂.verify (P₁.verify stmt tr.fst) tr.snd
  verify_eq := fun stmt tr => by
    have h₁ := P₁.verify_eq
    have h₂ := P₂.verify_eq
    simp only [Verifier.append, h₁, h₂, pure_bind, bind_pure]

end PureFormAppend

/-! ## Supporting probability lemmas -/

theorem mem_outputs_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript)
    (out : StmtOut) :
    out ∈ Outputs init impl V stmtIn tr ↔
      out ∈ support (OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)) := by
  rw [OptionT.mem_support_iff, OptionT.run_mk]; rfl

/-- Under `IsAccepting`, every statement the verifier can output at a leaf is in the language. -/
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

/-- An accepting tree with a leaf forces the sampling's support to be nonempty (the composition
proofs' entry ticket to `pure_verdict_mem_outputs`). -/
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

/-- A pure verifier's verdict IS reachable, as soon as the sampling can produce a seed. -/
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

/-- **The pure-case collapse.** At a pure verifier with a productive sampling,
validity is EXACTLY per-verdict witnessing: the statements are pinned by the verdict function,
not carried by the witnessing. Engine certificates consume the `→` direction (their `hpure` pins the statements);
composition proofs produce validity with the `←` direction. -/
theorem isValid_iff_pure (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (hV : ∀ stmt tr, V.verify stmt tr = pure (verify stmt tr))
    (hinit : (support init).Nonempty) (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} (o : LeafWitnesses tree WitOut) :
    LeafWitnesses.IsValid init impl V relOut stmtIn o ↔
      ∀ p, ∃ w, o p = some w ∧ (verify stmtIn p.fullTranscript, w) ∈ relOut := by
  constructor
  · intro h p
    obtain ⟨w, hw, out, hout, hrel⟩ := h p
    exact ⟨w, hw,
      outputs_pure_subsingleton init impl V verify hV stmtIn p.fullTranscript hout ▸ hrel⟩
  · intro h p
    obtain ⟨w, hw, hrel⟩ := h p
    exact ⟨w, hw, verify stmtIn p.fullTranscript,
      pure_verdict_mem_outputs init impl verify hV hinit stmtIn p.fullTranscript, hrel⟩

/-! ## The canonical witnessing (the classical closer) -/

open scoped Classical in
/-- The witnessing `IsAccepting` already guarantees: per leaf, a chosen `relOut`-witness at a
chosen reachable statement where one exists, `none` elsewhere. Classical; lives only in proofs
and in the top-level closer, erased at codegen. -/
noncomputable def canonWitnesses (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} : LeafWitnesses tree WitOut :=
  fun p =>
    if h : ∃ w, ∃ out ∈ Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut
    then some h.choose else none

/-- **G5.** `canonWitnesses` is valid on every accepting tree: the premise of the new notion is
never an obstruction. -/
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

/-! ## E8' — the two-way bridge with the total classical form -/

/-- The classical extractor shape: a *total* function of `(stmtIn, tree)`, with no witnessing input
and no way to decline. This was `Extractor.TreeBasedClassical` in the library while the migration
shim was up; M9 deleted the shim, so the prototype carries its own copy to keep E8' statable. -/
def TreeBasedClassical (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → ChallengeTree pSpec arity 0 → WitIn

/-- The classical statement shape (total extractor, no witnessing input) — what the library
asserted before the witness-only notion, and what the migration shim lifted. -/
def oldStatement (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (S : ChallengeTreeShape pSpec) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBasedClassical StmtIn WitIn pSpec S.arity) : Prop :=
  ∀ stmtIn tree, ChallengeTree.IsStructured S tree →
    tree.IsAccepting init impl V stmtIn relOut.language → (stmtIn, Ext stmtIn tree) ∈ relIn

/-- **E8', new ⟹ old.** Close the extractor with `canonWitnesses`. Needs no purity
hypothesis. -/
theorem old_of_new [Inhabited WitIn] (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    {Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut V Ext) :
    oldStatement init impl S relIn relOut V
      (fun stmtIn tree =>
        (Ext stmtIn tree (canonWitnesses init impl V relOut stmtIn)).getD default) := by
  intro stmtIn tree hstr hacc
  obtain ⟨w, hw, hrel⟩ :=
    h stmtIn tree hstr hacc _ (canonWitnesses_isValid hacc)
  simpa [hw] using hrel

/-- The shim's classical lift — a computability-preserving wrapper: ignore the witnessing.
Instance-free (no `[Nonempty StmtOut]`), no `init/impl/V` argument, and IR whenever the wrapped extractor has IR. -/
def ofClassical (E : TreeBasedClassical StmtIn WitIn pSpec arity) :
    TreeBased StmtIn WitIn WitOut pSpec arity :=
  fun stmtIn tree _ => some (E stmtIn tree)

/-- **E8', old ⟹ new** — the shim's `ofClassical` certificate: extraction by ignoring the
witnessing. -/
theorem new_of_old (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (S : ChallengeTreeShape pSpec) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    {E : TreeBasedClassical StmtIn WitIn pSpec S.arity}
    (h : oldStatement init impl S relIn relOut V E) :
    treeSpecialSoundWith init impl S relIn relOut V (ofClassical (WitOut := WitOut) E) :=
  fun stmtIn tree hstr hacc _ _ => ⟨E stmtIn tree, rfl, h stmtIn tree hstr hacc⟩

/-! ## The rejected alternatives, for the G0 and G3 kills below

Two rejected ways to type validity, both killed on fixtures:
- **∀ over reachable outputs** (`IsValidUnclaimed`): one witness per leaf serving EVERY
  reachable statement — vacuous at randomized verifiers (G0).
- **No reachability at all** (`IsValidFree`): any `relOut`-witness at ANY statement — admits
  junk the extractor cannot use; refuted at a sound forwarding engine (G3). -/

/-- The ∀-variant's validity condition. -/
def IsValidUnclaimed (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (o : LeafWitnesses tree WitOut) : Prop :=
  ∀ (p : ChallengeTree.LeafPath tree) (out : StmtOut),
    out ∈ Outputs init impl V stmtIn p.fullTranscript → ∃ w, o p = some w ∧ (out, w) ∈ relOut

/-- The ∀-variant's soundness notion. -/
def treeSpecialSoundWithUnclaimed (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
  ∀ o : LeafWitnesses tree WitOut, IsValidUnclaimed init impl V relOut stmtIn o →
    ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- Two reachable outputs with no common witness make the ∀-variant's premise unsatisfiable. -/
theorem isValidUnclaimed_false_of_two_outputs
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (p : ChallengeTree.LeafPath tree) {out₁ out₂ : StmtOut}
    (h₁ : out₁ ∈ Outputs init impl V stmtIn p.fullTranscript)
    (h₂ : out₂ ∈ Outputs init impl V stmtIn p.fullTranscript)
    (hsep : ∀ w : WitOut, (out₁, w) ∈ relOut → (out₂, w) ∉ relOut)
    (o : LeafWitnesses tree WitOut) :
    ¬ IsValidUnclaimed init impl V relOut stmtIn o := by
  intro hvalid
  obtain ⟨w₁, hw₁, hm₁⟩ := hvalid p out₁ h₁
  obtain ⟨w₂, hw₂, hm₂⟩ := hvalid p out₂ h₂
  rw [hw₁] at hw₂
  cases Option.some.inj hw₂
  exact hsep w₁ hm₁ hm₂

/-- The reachability-free validity: any `relOut`-witness at ANY statement, reachable or not. -/
def IsValidFree (relOut : Set (StmtOut × WitOut)) {tree : ChallengeTree pSpec arity 0}
    (o : LeafWitnesses tree WitOut) : Prop :=
  ∀ p : ChallengeTree.LeafPath tree, ∃ w, o p = some w ∧ ∃ out, (out, w) ∈ relOut

/-- The reachability-free soundness notion. -/
def treeSpecialSoundWithFree (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn, ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl V stmtIn relOut.language →
  ∀ o : LeafWitnesses tree WitOut, IsValidFree relOut o →
    ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

end CM

/-! ## The concrete fixtures

A zero-round protocol; a verifier making one uniform `Bool` query (two reachable outputs) with
an output relation forcing different witnesses at them — the data on which the ∀-variant
collapses and the adopted ∃-form does not. And a pure constant verifier with a two-statement
relation — the data on which the reachability-free variant breaks a sound forwarding engine. -/

namespace CM

/-- One-bit oracle, answered uniformly at random. -/
def cimpl : QueryImpl coinSpec (StateT Unit ProbComp) :=
  fun _ => fun s => do let b ← ($ᵗ Bool); pure (b, s)

/-- Coin-flipping verifier: output statement is a fresh uniform bit. -/
def coinVerifier : Verifier coinSpec Unit Bool (!p[] : ProtocolSpec 0) where
  verify := fun _ _ => OptionT.mk (do
    let b ← (liftM (query (spec := coinSpec) (m := OracleComp coinSpec) ()) :
      OracleComp coinSpec Bool)
    pure (some b))

/-- `relOut` forces DIFFERENT witnesses at the two possible outputs. -/
def relOutBad : Set (Bool × ℕ) := {(true, 0), (false, 1)}

theorem relOutBad_language : relOutBad.language = Set.univ := by
  ext b
  simp only [Set.mem_univ, iff_true, Set.mem_language_iff]
  cases b
  · exact ⟨1, by simp [relOutBad]⟩
  · exact ⟨0, by simp [relOutBad]⟩

/-- The coin verifier's run, unfolded. -/
theorem coinRun (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (do (simulateQ cimpl (coinVerifier.run () tr)).run' (← (pure () : ProbComp Unit)) :
      ProbComp (Option Bool)) = (do let b ← ($ᵗ Bool); pure (some b)) := by
  simp only [coinVerifier, Verifier.run, OptionT.mk, StateT.run',
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  show (fun x => x.1) <$>
      ((fun (p : Bool × Unit) => (some p.1, p.2)) <$>
        (do let b ← ($ᵗ Bool); pure (b, ()))) = some <$> ($ᵗ Bool)
  simp [map_bind, Functor.map_map, bind_pure_comp]

theorem true_mem_outputs (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    true ∈ Outputs (pure ()) cimpl coinVerifier () tr := by
  simp only [Outputs, Set.mem_setOf_eq, coinRun]
  simp

theorem false_mem_outputs (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    false ∈ Outputs (pure ()) cimpl coinVerifier () tr := by
  simp only [Outputs, Set.mem_setOf_eq, coinRun]
  simp

/-- The two reachable outputs admit no COMMON witness. -/
theorem relOutBad_sep : ∀ w : ℕ, (true, w) ∈ relOutBad → (false, w) ∉ relOutBad := by
  intro w hw
  simp only [relOutBad, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hw ⊢
  rcases hw with ⟨_, rfl⟩ | ⟨h, _⟩
  · simp
  · exact absurd h (by simp)

/-- The coin verifier is `IsAccepting` on every tree (its output language is everything). -/
theorem coinAccepting {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
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

/-- Every no-challenge tree has a leaf path (from its unique transcript). -/
theorem nonempty_leafPath {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    Nonempty (ChallengeTree.LeafPath tree) :=
  ⟨ProtocolSpec.ChallengeTree.onlyPath tree⟩

/-- A pure verifier over the same protocol, constant verdict `true`. -/
def pureVerifier : Verifier coinSpec Unit Bool (!p[] : ProtocolSpec 0) where
  verify := fun _ _ => OptionT.mk (pure (some true))

theorem pureVerifier_accepting {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    tree.IsAccepting (pure ()) cimpl pureVerifier () relOutBad.language := by
  intro tr _
  exact Verifier.pure_accepting_of_mem (pure ()) cimpl pureVerifier () tr relOutBad.language
    true rfl (by rw [relOutBad_language]; trivial)

/-! ## The gates -/

/-- **G1 (satisfiability).** At the two-output coin verifier — the very data on which the
∀-variant collapses (`unclaimed_vacuous`) — a valid witnessing exists at the adopted ∃-form:
the constant `some 0`, certifying the reachable output `true`. -/
theorem exists_valid_witnessing {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    LeafWitnesses.IsValid (pure ()) cimpl coinVerifier relOutBad () (tree := tree)
      (fun _ => some 0) :=
  fun p => ⟨0, rfl, true, true_mem_outputs p.fullTranscript, by simp [relOutBad]⟩

/-- **G2 (non-vacuity).** With `relIn = ∅`, the notion is REFUTABLE at the coin verifier — for
EVERY extractor. Contrast `unclaimed_vacuous`, which is *provable* at the constant-`none`
extractor on identical data. -/
theorem not_vacuous (S : ChallengeTreeShape (!p[] : ProtocolSpec 0))
    (Ext : TreeBased Unit ℕ ℕ !p[] S.arity) :
    ¬ treeSpecialSoundWith (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier
      Ext := by
  intro h
  obtain ⟨w, -, hw⟩ := h () ChallengeTree.leaf trivial (coinAccepting _) _
    (canonWitnesses_isValid (coinAccepting _))
  exact hw

/-- **G4.** The constant-`none` witnessing is invalid whenever the tree has a leaf: a chain
cannot be "closed" by feeding it nothing. -/
theorem isValid_none_false {StmtOut WitOut : Type}
    {init : ProbComp Unit} {impl : QueryImpl coinSpec (StateT Unit ProbComp)}
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    {arity : pSpec.ChallengeIdx → ℕ} {tree : ChallengeTree pSpec arity 0}
    (V : Verifier coinSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) (hpath : Nonempty (ChallengeTree.LeafPath tree)) :
    ¬ LeafWitnesses.IsValid init impl V relOut stmtIn (tree := tree) (fun _ => none) := by
  intro h
  obtain ⟨p⟩ := hpath
  obtain ⟨w, hw, -⟩ := h p
  exact absurd hw (by simp)

/-! ## G0 — the ∀-variant kill: unclaimed-∀ witnessings are VACUOUS

The regression gate against re-weakening: require one witness per leaf to serve EVERY reachable statement and the premise is unsatisfiable at any
randomized verifier with two separated outputs — the notion becomes provable at the
constant-`none` extractor with `relIn = ∅`, on data where the classical notion is refutable.
The adopted `IsValid` differs exactly by the ∃/∀ swap over reachable outputs. -/

/-- **G0.** The ∀-variant is VACUOUS: proved at the constant-`none` extractor with
`relIn = ∅`, at a verifier that accepts every tree. -/
theorem unclaimed_vacuous (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    treeSpecialSoundWithUnclaimed (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier
      (fun _ _ _ => none) := by
  intro stmtIn tree _ _ o hvalid
  obtain ⟨path⟩ := nonempty_leafPath tree
  exact absurd hvalid
    (isValidUnclaimed_false_of_two_outputs (pure ()) cimpl coinVerifier relOutBad () path
      (true_mem_outputs _) (false_mem_outputs _) relOutBad_sep o)

/-- ... while the CLASSICAL notion is refutable at that same data, for every extractor — so the
∀-variant is strictly weaker than what it would replace. -/
theorem classical_refutable (S : ChallengeTreeShape (!p[] : ProtocolSpec 0))
    (Ext : TreeBasedClassical Unit ℕ (!p[] : ProtocolSpec 0) S.arity) :
    ¬ oldStatement (pure ()) cimpl S (∅ : Set (Unit × ℕ)) relOutBad coinVerifier Ext := by
  intro h
  exact (h () ChallengeTree.leaf trivial (coinAccepting _) : (_, _) ∈ (∅ : Set (Unit × ℕ)))

/-! ## G3 — reachability inside `IsValid` is load-bearing

The pair `reachable_sound` / `free_refuted`: the SAME forwarding extractor on the SAME sound
data satisfies the adopted notion and is refuted by the reachability-free variant — junk
witnesses at unreachable statements are exactly what the relocated honesty condition excludes. -/

/-- The unique leaf path of a challenge-free tree (the plan's M0 `onlyPath`, inlined). -/
def onlyPath {n : ℕ} {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}
    [IsEmpty pSpec.ChallengeIdx] :
    {m : Fin (n + 1)} → (t : ChallengeTree pSpec arity m) → ChallengeTree.LeafPath t
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (onlyPath child)
  | _, .chalNode m h _ _ => isEmptyElim (⟨m, h⟩ : pSpec.ChallengeIdx)

/-- The forwarding extractor: read the (unique) leaf's witness and return it. A real engine in
miniature — witness-only, computable. -/
def fwdExt (arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ) :
    TreeBased Unit ℕ ℕ (!p[] : ProtocolSpec 0) arity :=
  fun _ tree o => o (onlyPath tree)

/-- Two statements, two witnesses — but only `true` is reachable at `pureVerifier`. -/
def relOutMix : Set (Bool × ℕ) := {(true, 0), (false, 7)}

/-- The input relation the forwarding extractor targets: exactly the witness at the REACHABLE
statement. -/
def relInPt : Set (Unit × ℕ) := {((), 0)}

theorem pureVerifier_accepting_mix {arity : (!p[] : ProtocolSpec 0).ChallengeIdx → ℕ}
    (tree : ChallengeTree (!p[] : ProtocolSpec 0) arity 0) :
    tree.IsAccepting (pure ()) cimpl pureVerifier () relOutMix.language := by
  intro tr _
  exact Verifier.pure_accepting_of_mem (pure ()) cimpl pureVerifier () tr relOutMix.language
    true rfl ((Set.mem_language_iff _ _).2 ⟨0, by simp [relOutMix]⟩)

/-- **G3, positive half.** The adopted notion HOLDS at the forwarding extractor: validity pins
the witness to the reachable statement `true`, whose only `relOutMix`-witness is `0`. -/
theorem reachable_sound (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    treeSpecialSoundWith (pure ()) cimpl S relInPt relOutMix pureVerifier
      (fwdExt S.arity) := by
  intro stmtIn tree hstr hacc o hvalid
  obtain ⟨w, hw, out, hout, hrel⟩ := hvalid (onlyPath tree)
  have hout' : out = true :=
    outputs_pure_subsingleton (pure ()) cimpl pureVerifier (fun _ _ => true)
      (fun _ _ => rfl) () (onlyPath tree).fullTranscript hout
  subst hout'
  have hw0 : w = 0 := by
    simp only [relOutMix, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hrel
    rcases hrel with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by simp)
  subst hw0
  exact ⟨0, by simpa [fwdExt] using hw, by simp [relInPt]⟩

/-- **G3, negative half.** The reachability-free variant is REFUTED at that same extractor on
that same data: the junk witnessing `some 7` — certifying only the UNREACHABLE statement
`false` — is free-valid, the forwarding extractor dutifully returns `7`, and `((), 7) ∉ relInPt`.
Dropping reachability breaks sound engines. -/
theorem free_refuted (S : ChallengeTreeShape (!p[] : ProtocolSpec 0)) :
    ¬ treeSpecialSoundWithFree (pure ()) cimpl S relInPt relOutMix pureVerifier
      (fwdExt S.arity) := by
  intro h
  obtain ⟨w, hw, hrel⟩ := h () ChallengeTree.leaf trivial (pureVerifier_accepting_mix _)
    (fun _ => some 7) (fun _ => ⟨7, rfl, false, by simp [relOutMix]⟩)
  have hw7 : w = 7 := by
    have : some (7 : ℕ) = some w := by simpa [fwdExt, onlyPath] using hw
    exact (Option.some.inj this).symm
  subst hw7
  simp [relInPt] at hrel

/-! ## E20 — the arity-0 degeneracy -/

theorem isAccepting_of_no_transcripts {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}
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

/-! ## P — purity-as-data runtime fixtures -/

/-- A second pure verifier, on the `Bool` seam. -/
def notVerifier : Verifier coinSpec Bool Bool (!p[] : ProtocolSpec 0) where
  verify := fun b _ => OptionT.mk (pure (some (!b)))

def pureVerifierPF : PureForm pureVerifier := ⟨fun _ _ => true, fun _ _ => rfl⟩

def notVerifierPF : PureForm notVerifier := ⟨fun b _ => !b, fun _ _ => rfl⟩

/-- Composed purity data — computable, IR-gated below. -/
def appendedPF : PureForm (pureVerifier.append notVerifier) :=
  pureVerifierPF.append notVerifierPF

/-- The classical wrapper applied to a computable classical extractor — IR-gated below (a
plain wrapper — nothing classical anywhere). -/
def ofClassicalDemo : TreeBased Unit ℕ ℕ (!p[] : ProtocolSpec 0) (fun _ => 1) :=
  ofClassical (fun (_ : Unit) (_ : ChallengeTree (!p[] : ProtocolSpec 0) (fun _ => 1) 0) =>
    (5 : ℕ))

/-- The forwarding engine at a fixed arity — IR-gated below. -/
def fwdExtDemo : TreeBased Unit ℕ ℕ (!p[] : ProtocolSpec 0) (fun _ => 1) :=
  fwdExt (fun _ => 1)

#eval fwdExtDemo () ChallengeTree.leaf (fun _ => some 42)  -- some 42
#eval ofClassicalDemo () ChallengeTree.leaf (fun _ => none) -- some 5

end CM

/-! ## E25 — codegen calibration

A package-shaped structure whose relation field is `Set`-valued and even *noncomputably defined*
still `#eval`s its data field: `Prop`-level and `Set`-valued fields are erased and never block
codegen — a package failing an IR gate is always the fault of a data field. -/

namespace CMCalibration

structure Pkg where
  rel : Set (ℕ × ℕ)
  ext : ℕ → Option ℕ

noncomputable def weird : ℕ → ℝ := fun n => Classical.choice ⟨(n : ℝ)⟩

def p : Pkg where
  rel := {q | weird q.1 = weird q.2}
  ext := fun n => some (n + 1)

#eval p.ext 3

end CMCalibration

section Audit
#print axioms CM.canonWitnesses_isValid
#print axioms CM.old_of_new
#print axioms CM.new_of_old
#print axioms CM.unclaimed_vacuous
#print axioms CM.classical_refutable
#print axioms CM.exists_valid_witnessing
#print axioms CM.not_vacuous
#print axioms CM.reachable_sound
#print axioms CM.free_refuted
#print axioms CM.isValid_none_false
#print axioms CM.isValid_iff_pure
#print axioms CM.pure_verdict_mem_outputs
#print axioms CM.support_init_nonempty_of_accepting
#print axioms CM.treeSpecialSoundWithEscape_false_iff
#print axioms CM.treeSpecialSoundWith.withEscape
#print axioms CM.treeSpecialSoundWith_congr
#print axioms CM.treeSpecialSoundWithEscape.mono
#print axioms CM.treeSpecialSoundWithEscape_congr
#print axioms CM.PureForm.append
#print axioms CM.PureForm.toGuardedForm
#print axioms CM.isAccepting_of_no_transcripts
#print axioms CM.fullTranscripts_eq_nil_of_arity_zero
end Audit

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for nm in [``CM.ofClassicalDemo, ``CM.fwdExtDemo, ``CM.appendedPF, ``CM.onlyPath,
      ``CMCalibration.p] do
    match Lean.IR.findEnvDecl env nm with
    | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
    | none   => Lean.logWarning m!"NO IR (noncomputable): {nm}"
