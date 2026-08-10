/-
PROTOTYPE: the computable witness-only leaf engines and their soundness CERTIFICATES.

The engines replace the noncomputable classical-inversion extractors (`ReduceClaim`,
`SingleRound`, `ScalarRound`): each is a bare function collecting per-leaf witnesses off the
witnessing input — no `Classical.choose`, no `[Nonempty WitOut]`, no statement attribution.
attribution lives on the verifier; the certificates consume the notion's validity premise
through `isValid_iff_pure` at TODAY's `hpure` hypotheses (the verdict pins the statements).

Proved here:
  - `CMEngines.rcTreeExtractor` + `rc_coordinateWiseSpecialSoundWith` — the `ReduceClaim`
    engine (pull the single leaf witness back along `mapWitInv`) with a FULL CWSS certificate.
  - `CMSR.treeExtractor` + `coordinateWiseSpecialSoundWith_of_mkWitness` and the escape twin —
    the `SingleRound` engine (`collect` the per-branch witnesses into `mkWitness`), mirroring
    the repo statements (SingleRound.lean:404/:455) with today's `hpure`/`hmk` at the repo's
    UNCHANGED `escEvent relOut escLocal`; the escape disjunction is decided by a classical case
    split on the event, refuted in the no-escape branch by the collected responses.
  - `CMSC.treeExtractorScalar` + both certificates — the `(ℓ = 1, k)` transplant at the repo's
    UNCHANGED `escEventScalar`, `hmk` at `Function.Injective fam` via `injective_of_nodeOk`.
  - Runtime demo: the real engine `#eval`s on a concrete star tree, kernel-`rfl`-checked; a
    missing leaf witness yields `none`, not junk.

The lemma layer: `collect_eq_some` (a validated witnessing feeds `collect`),
`fullTranscript_branchPathOf` (the branch path's transcript IS the branch transcript — `rfl` on
the star tree), and the per-engine `collect_branch_data` (validity at the verdicts yields the
per-branch response family, choice-free). No inverse path readers or star-path classification
are needed: validity is consumed at `branchPathOf`-paths only.

Part A inlines the witness-only core from `CM_gates.lean` (independently green there).
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound
import ArkLib.ProofSystem.Component.ReduceClaim

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree

/-! ## Part A — the witness-only core (as in `CM_gates.lean`) -/

namespace CM

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

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

/-- The witness-only notion. -/
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

/-- CWSS instance. -/
def coordinateWiseSpecialSoundWith (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity) : Prop :=
  treeSpecialSoundWith init impl (CWSSStructure.toShape D) relIn relOut V Ext

/-- Escape CWSS instance. -/
def coordinateWiseSpecialSoundWithEscape (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (D : CWSSStructure pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity) : Prop :=
  treeSpecialSoundWithEscape init impl (CWSSStructure.toShape D) esc relIn relOut V Ext

theorem mem_outputs_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript)
    (out : StmtOut) :
    out ∈ Outputs init impl V stmtIn tr ↔
      out ∈ support (OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)) := by
  rw [OptionT.mem_support_iff, OptionT.run_mk]; rfl

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

/-- The pure-case collapse: at a pure verifier with a productive sampling, validity is
per-verdict witnessing. -/
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

end CM

-- `ProtocolSpec.ChallengeTree.onlyPath` (inlined here when this prototype was written) now lives
-- in the library, in `Security/TranscriptTree/Basic.lean`; the IR gate at the end still checks it.

instance : IsEmpty ((!p[] : ProtocolSpec 0).ChallengeIdx) :=
  ⟨fun i => Fin.elim0 i.1⟩

/-! ## Part B — the `ReduceClaim` engine and its certificate -/

namespace CMEngines

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The `ReduceClaim` engine, witness-only** — computable, classical-free: pull the single
leaf witness back along `mapWitInv`. No statement map: the engine extracts, the verifier
attributes. -/
def rcTreeExtractor (mapWitInv : StmtIn → WitOut → WitIn)
    (D : CWSSStructure (!p[] : ProtocolSpec 0)) :
    CM.TreeBased StmtIn WitIn WitOut !p[] (CWSSStructure.toShape D).arity :=
  fun stmtIn tree o => (o (ChallengeTree.onlyPath tree)).map (mapWitInv stmtIn)

/-- **CWSS of `ReduceClaim`, witness-only** — REAL extraction: the returned witness is
`mapWitInv stmtIn` of the leaf witness the downstream certificate supplied. The validity
premise collapses through the verifier's purity (`isValid_iff_pure` at `mapStmt`). -/
theorem rc_coordinateWiseSpecialSoundWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (mapStmt : StmtIn → StmtOut) (mapWitInv : StmtIn → WitOut → WitIn)
    (D : CWSSStructure (!p[] : ProtocolSpec 0))
    (hRel : ∀ stmtIn witOut,
      (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    CM.coordinateWiseSpecialSoundWith init impl D relIn relOut
      (ReduceClaim.verifier oSpec mapStmt) (rcTreeExtractor mapWitInv D) := by
  intro stmtIn tree _ hAcc o hvalid
  have hne : (support init).Nonempty :=
    CM.support_init_nonempty_of_accepting hAcc (ChallengeTree.onlyPath tree)
  have hvalid' := (CM.isValid_iff_pure init impl (fun s _ => mapStmt s)
    (fun _ _ => rfl) hne relOut stmtIn o).mp hvalid
  obtain ⟨w, hw, hrel⟩ := hvalid' (ChallengeTree.onlyPath tree)
  have hrel' : (mapStmt stmtIn, w) ∈ relOut := hrel
  refine ⟨mapWitInv stmtIn w, ?_, hRel stmtIn w hrel'⟩
  show (o (ChallengeTree.onlyPath tree)).map (mapWitInv stmtIn) = some (mapWitInv stmtIn w)
  rw [hw]; rfl

end CMEngines

/-! ## Part C — the `SingleRound` engine -/

namespace CMSR

open ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise CoordinateWise.SingleRound

variable {CarrierCom C : Type} {r : ℕ}
  {arity : (pSpec CarrierCom C r).ChallengeIdx → ℕ}

/-- Index-generic: at the last round every tree is a leaf. -/
def lastPathAux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    a = Fin.last 2 → LeafPath t
  | _, .leaf, _ => .leaf
  | _, .msgNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)
  | _, .chalNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)

/-- Index-generic round-1 branch path. -/
def chalPathAux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    a = (1 : Fin 3) → Fin (arity ⟨1, rfl⟩) → LeafPath t
  | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
  | _, .msgNode k h _ _, ha, _ => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode k h _ children, ha, j => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact .chal j (lastPathAux (children j) rfl)

/-- The root-to-leaf path of branch `j` of an arbitrary full single-round tree. -/
def branchPathOf (tree : ChallengeTree (pSpec CarrierCom C r) arity 0)
    (j : Fin (arity ⟨1, rfl⟩)) : LeafPath tree := aux tree rfl j
where
  aux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) → a = (0 : Fin 3) →
      Fin (arity ⟨1, rfl⟩) → LeafPath t
    | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
    | _, .msgNode k _ _ child, ha, j => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact .msg (chalPathAux child rfl j)
    | _, .chalNode k h _ _, ha, _ => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact absurd h Direction.noConfusion

/-- `Option`-valued sequencing of the per-branch witnesses (no search, no choice, no
`Fintype`). -/
def collect {K : ℕ} {W : Type} (f : Fin K → Option W) : Option (Fin K → W) :=
  if h : ∀ j, (f j).isSome then some (fun j => (f j).get (h j)) else none

/-- **The `SingleRound` engine, witness-only** — replaces the `noncomputable`
`CoordinateWise.SingleRound.treeExtractor`: collect the per-branch leaf witnesses off the
witnessing and assemble via `mkWitness`. A bare function; the engine attributes no
statements. -/
def treeExtractor {StmtIn WitOut WitIn : Type}
    (mkWitness : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → WitIn) :
    CM.TreeBased StmtIn WitIn WitOut (pSpec CarrierCom C r)
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).arity :=
  fun stmtIn tree o =>
    (collect (fun j => o (branchPathOf tree (Fin.cast foldStructure_arity.symm j)))).map
      (mkWitness stmtIn (readPre tree)
        (fun j => readChallenges tree (Fin.cast foldStructure_arity.symm j)))

/-! ### The lemma layer -/

/-- A validated leaf witnessing feeds `collect`. -/
theorem collect_eq_some {K : ℕ} {W : Type} {f : Fin K → Option W} {w : Fin K → W}
    (h : ∀ j, f j = some (w j)) : collect f = some w := by
  have hs : ∀ j, (f j).isSome := fun j => by rw [h j]; rfl
  unfold collect
  rw [dif_pos hs]
  exact congrArg some (funext fun j =>
    Option.some.inj ((Option.some_get (hs j)).trans (h j)))

/-- The branch path's transcript IS the branch transcript — definitional on the star tree
(the readers and the path builder compute on `tree2`'s concrete constructors). -/
theorem fullTranscript_branchPathOf (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchPathOf (tree2 v challenges) j).fullTranscript = branchTr v challenges j := rfl

section Certificates

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut WitIn : Type} {σ : Type}

/-- Extraction core: a witnessing that is valid at the pure verdicts yields the per-branch
response family — each branch's witness is present (`collect`'s guard) and satisfies `relOut`
at that branch's extended statement. Choice-free: the family is read off `o` by `Option.get`.
Validity is consumed at `branchPathOf`-paths only; no path classification needed. -/
theorem collect_branch_data
    {relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut)}
    (harity : 2 ^ r + 1 = arity ⟨1, rfl⟩)
    (stmtIn : StmtIn) (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (o : CM.LeafWitnesses (tree2 v challenges) WitOut)
    (hvalid : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
        ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
          ∈ relOut) :
    ∃ resp : Fin (2 ^ r + 1) → WitOut,
      (∀ j, o (branchPathOf (tree2 v challenges) (Fin.cast harity j)) = some (resp j)) ∧
      (∀ j, ((stmtIn, v, challenges (Fin.cast harity j)), resp j) ∈ relOut) := by
  have hsome : ∀ j : Fin (2 ^ r + 1),
      (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).isSome := by
    intro j
    obtain ⟨w, hw, -⟩ := hvalid (branchPathOf (tree2 v challenges) (Fin.cast harity j))
    rw [hw]; rfl
  refine ⟨fun j => (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j),
    fun j => (Option.some_get (hsome j)).symm, fun j => ?_⟩
  obtain ⟨w, hw, hrel⟩ := hvalid (branchPathOf (tree2 v challenges) (Fin.cast harity j))
  rw [fullTranscript_branchPathOf, branch_pre, branch_challenge] at hrel
  have hget : (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j) = w :=
    Option.some.inj ((Option.some_get (hsome j)).trans hw)
  change ((stmtIn, v, challenges (Fin.cast harity j)),
      (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j)) ∈ relOut
  rw [hget]
  exact hrel

/-- **Generic single-round CWSS assembly, witness-only, named engine.** Any pure
statement-extending verifier of the two-round `pSpec` is CWSS for `foldStructure` at the
computable engine `CMSR.treeExtractor mkWitness`, given today's witness assembler `hmk`.
Mirrors `CoordinateWise.SingleRound.coordinateWiseSpecialSoundWith_of_mkWitness` with
`[Nonempty WitOut]` dropped. -/
theorem coordinateWiseSpecialSoundWith_of_mkWitness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn (StmtIn × CarrierCom × (Fin (2 ^ r) → C)) (pSpec CarrierCom C r))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut))
    (mkWitness : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → WitIn)
    (hmk : ∀ stmtIn v (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → C))
        (resp : Fin (2 ^ r + 1) → WitOut),
      (∀ j, ((stmtIn, v, fam j), resp j) ∈ relOut) →
      (∃ e, StarAt fam e) →
      (stmtIn, mkWitness stmtIn v fam resp) ∈ relIn) :
    CM.coordinateWiseSpecialSoundWith init impl
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)) relIn relOut V
      (treeExtractor mkWitness) := by
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (foldStructure_arity (CarrierCom := CarrierCom) (C := C) (r := r)).symm
  intro o hvalid
  have hne : (support init).Nonempty :=
    CM.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity 0))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (CM.isValid_iff_pure init impl
      (fun s tr => (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
      hpure hne relOut stmtIn o).mp hvalid
  obtain ⟨resp, hro, hbranch⟩ := collect_branch_data harity stmtIn v challenges o hvalid'
  have hfam := (nodeOk_iff_family challenges).1 hStruct.1
  have hstar : ∃ e, StarAt
      (fun j : Fin (2 ^ r + 1) => challenges (Fin.cast harity j)) e :=
    exists_starAt (le_refl 2) (by omega) _ hfam
  have hcol : collect (fun j : Fin (2 ^ r + 1) =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j))) = some resp :=
    collect_eq_some hro
  refine ⟨mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp, ?_,
    hmk stmtIn v (fun j => challenges (Fin.cast harity j)) resp hbranch hstar⟩
  change (collect (fun j : Fin (2 ^ r + 1) =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j)))).map
      (mkWitness stmtIn (readPre (tree2 v challenges))
        (fun j => readChallenges (tree2 v challenges) (Fin.cast harity j)))
    = some (mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp)
  rw [hcol]
  rfl

/-- **Generic single-round escape-threaded CWSS assembly, witness-only, named engine.** At the
repo's UNCHANGED `escEvent relOut escLocal`: the disjunction is decided before seeing `o` by a
classical case split on the event; in the no-escape branch `hmk`'s escape conclusion is
refuted — the collected response family is exactly an event witness. Mirrors
`CoordinateWise.SingleRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness` with
`[Nonempty WitOut]` dropped. -/
theorem coordinateWiseSpecialSoundWithEscape_of_mkWitness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn (StmtIn × CarrierCom × (Fin (2 ^ r) → C)) (pSpec CarrierCom C r))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut))
    (mkWitness : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → WitIn)
    (escLocal : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → Prop)
    (hmk : ∀ stmtIn v (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → C))
        (resp : Fin (2 ^ r + 1) → WitOut),
      (∀ j, ((stmtIn, v, fam j), resp j) ∈ relOut) →
      (∃ e, StarAt fam e) →
      escLocal stmtIn v fam resp ∨ (stmtIn, mkWitness stmtIn v fam resp) ∈ relIn) :
    CM.coordinateWiseSpecialSoundWithEscape init impl
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r))
      (escEvent relOut escLocal) relIn relOut V
      (treeExtractor mkWitness) := by
  classical
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (foldStructure_arity (CarrierCom := CarrierCom) (C := C) (r := r)).symm
  by_cases hesc : escEvent relOut escLocal stmtIn (tree2 v challenges)
  · exact Or.inl hesc
  refine Or.inr fun o hvalid => ?_
  have hne : (support init).Nonempty :=
    CM.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity 0))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (CM.isValid_iff_pure init impl
      (fun s tr => (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
      hpure hne relOut stmtIn o).mp hvalid
  obtain ⟨resp, hro, hbranch⟩ := collect_branch_data harity stmtIn v challenges o hvalid'
  have hfam := (nodeOk_iff_family challenges).1 hStruct.1
  have hstar : ∃ e, StarAt
      (fun j : Fin (2 ^ r + 1) => challenges (Fin.cast harity j)) e :=
    exists_starAt (le_refl 2) (by omega) _ hfam
  have hcol : collect (fun j : Fin (2 ^ r + 1) =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j))) = some resp :=
    collect_eq_some hro
  rcases hmk stmtIn v (fun j => challenges (Fin.cast harity j)) resp hbranch hstar with
    hbad | hgood
  · -- the collected responses witness the tree-level event: contradiction with `hesc`
    exact absurd
      (show escEvent relOut escLocal stmtIn (tree2 v challenges) from ⟨resp, hbranch, hbad⟩)
      hesc
  · refine ⟨mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp, ?_, hgood⟩
    change (collect (fun j : Fin (2 ^ r + 1) =>
        o (branchPathOf (tree2 v challenges) (Fin.cast harity j)))).map
        (mkWitness stmtIn (readPre (tree2 v challenges))
          (fun j => readChallenges (tree2 v challenges) (Fin.cast harity j)))
      = some (mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp)
    rw [hcol]
    rfl

end Certificates

end CMSR

/-! ## Part D — the `ScalarRound` engine and its certificates

The `(ℓ = 1, k)` transplant: the same path builders at `pSpecScalar`, the computable scalar
engine (replacing the `noncomputable` `treeExtractorScalar`), and both certificates — `hmk`
receives `Function.Injective fam` (via `injective_of_nodeOk`), the escape variant carries the
repo's unchanged `escEventScalar`. `[Nonempty WitOut]` dropped throughout. -/

namespace CMSC

open ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise CoordinateWise.ScalarRound

variable {Msg C : Type} {arity : (pSpecScalar Msg C).ChallengeIdx → ℕ}

/-- Index-generic: at the last round every tree is a leaf. -/
def lastPathAux : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) →
    a = Fin.last 2 → LeafPath t
  | _, .leaf, _ => .leaf
  | _, .msgNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)
  | _, .chalNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)

/-- Index-generic round-1 branch path. -/
def chalPathAux : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) →
    a = (1 : Fin 3) → Fin (arity ⟨1, rfl⟩) → LeafPath t
  | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
  | _, .msgNode k h _ _, ha, _ => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode k h _ children, ha, j => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact .chal j (lastPathAux (children j) rfl)

/-- The root-to-leaf path of branch `j` of an arbitrary full scalar-round tree. -/
def branchPathOf (tree : ChallengeTree (pSpecScalar Msg C) arity 0)
    (j : Fin (arity ⟨1, rfl⟩)) : LeafPath tree := aux tree rfl j
where
  aux : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) → a = (0 : Fin 3) →
      Fin (arity ⟨1, rfl⟩) → LeafPath t
    | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
    | _, .msgNode k _ _ child, ha, j => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact .msg (chalPathAux child rfl j)
    | _, .chalNode k h _ _, ha, _ => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact absurd h Direction.noConfusion

/-- **The `ScalarRound` engine, witness-only** — replaces the `noncomputable`
`CoordinateWise.ScalarRound.treeExtractorScalar`: collect the `k` per-branch leaf witnesses
(reusing the generic `CMSR.collect`) and assemble via `mkWitness` at the family
`readFam hk tree`. -/
def treeExtractorScalar {StmtIn WitIn WitOut : Type} {k : ℕ} (hk : 2 ≤ k)
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn) :
    CM.TreeBased StmtIn WitIn WitOut (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity :=
  fun stmtIn tree o =>
    (CMSR.collect (fun j : Fin k => o (branchPathOf tree
        (Fin.cast (scalarStructure_arity (Msg := Msg) (C := C) hk).symm j)))).map
      (mkWitness stmtIn (readPre tree) (readFam hk tree))

/-- The branch path's transcript IS the branch transcript — definitional on the star tree. -/
theorem fullTranscript_branchPathOf (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchPathOf (tree2 v challenges) j).fullTranscript = branchTr v challenges j := rfl

section Certificates

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {σ : Type}

/-- Extraction core, scalar round: validity at the pure verdicts yields the `k` per-branch
responses, present and `relOut`-valid at the branch statements. Choice-free. -/
theorem collect_branch_data {k : ℕ}
    {relOut : Set ((StmtIn × Msg × C) × WitOut)}
    (harity : k = arity ⟨1, rfl⟩)
    (stmtIn : StmtIn) (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (o : CM.LeafWitnesses (tree2 v challenges) WitOut)
    (hvalid : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
        ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
          ∈ relOut) :
    ∃ resp : Fin k → WitOut,
      (∀ j, o (branchPathOf (tree2 v challenges) (Fin.cast harity j)) = some (resp j)) ∧
      (∀ j, ((stmtIn, v, challenges (Fin.cast harity j)), resp j) ∈ relOut) := by
  have hsome : ∀ j : Fin k,
      (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).isSome := by
    intro j
    obtain ⟨w, hw, -⟩ := hvalid (branchPathOf (tree2 v challenges) (Fin.cast harity j))
    rw [hw]; rfl
  refine ⟨fun j => (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j),
    fun j => (Option.some_get (hsome j)).symm, fun j => ?_⟩
  obtain ⟨w, hw, hrel⟩ := hvalid (branchPathOf (tree2 v challenges) (Fin.cast harity j))
  rw [fullTranscript_branchPathOf, branch_pre, branch_challenge] at hrel
  have hget : (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j) = w :=
    Option.some.inj ((Option.some_get (hsome j)).trans hw)
  change ((stmtIn, v, challenges (Fin.cast harity j)),
      (o (branchPathOf (tree2 v challenges) (Fin.cast harity j))).get (hsome j)) ∈ relOut
  rw [hget]
  exact hrel

/-- **Generic scalar-round CWSS assembly, witness-only, named engine.** Mirrors
`CoordinateWise.ScalarRound.coordinateWiseSpecialSoundWith_of_mkWitness_scalar` with
`[Nonempty WitOut]` dropped. -/
theorem coordinateWiseSpecialSoundWith_of_mkWitness_scalar
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {k : ℕ} (hk : 2 ≤ k)
    (V : Verifier oSpec StmtIn (StmtIn × Msg × C) (pSpecScalar Msg C))
    (hpure : ∀ s tr,
      V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn)
    (hmk : ∀ s v (fam : Fin k → C) (resp : Fin k → WitOut),
      (∀ j, ((s, v, fam j), resp j) ∈ relOut) → Function.Injective fam →
      (s, mkWitness s v fam resp) ∈ relIn) :
    CM.coordinateWiseSpecialSoundWith init impl (scalarStructure k hk) relIn relOut V
      (treeExtractorScalar hk mkWitness) := by
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (scalarStructure_arity (Msg := Msg) (C := C) (k := k) hk).symm
  intro o hvalid
  have hne : (support init).Nonempty :=
    CM.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity ⟨0, by omega⟩))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (CM.isValid_iff_pure init impl
      (fun s tr => (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
      hpure hne relOut stmtIn o).mp hvalid
  obtain ⟨resp, hro, hbranch⟩ := collect_branch_data harity stmtIn v challenges o hvalid'
  have hinj := injective_of_nodeOk (Msg := Msg) (C := C) (hk := hk) hStruct.1
  have hcol : CMSR.collect (fun j : Fin k =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j))) = some resp :=
    CMSR.collect_eq_some hro
  refine ⟨mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp, ?_,
    hmk stmtIn v (fun j => challenges (Fin.cast harity j)) resp hbranch hinj⟩
  change (CMSR.collect (fun j : Fin k =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j)))).map
      (mkWitness stmtIn (readPre (tree2 v challenges)) (readFam hk (tree2 v challenges)))
    = some (mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp)
  rw [hcol]
  rfl

/-- **Generic scalar-round escape-threaded CWSS assembly, witness-only, named engine.** At the
repo's UNCHANGED `escEventScalar hk relOut escLocal`; classical case split on the event, the
collected responses refuting `hmk`'s escape conclusion in the no-escape branch. Mirrors
`CoordinateWise.ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar` with
`[Nonempty WitOut]` dropped. -/
theorem coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {k : ℕ} (hk : 2 ≤ k)
    (V : Verifier oSpec StmtIn (StmtIn × Msg × C) (pSpecScalar Msg C))
    (hpure : ∀ s tr,
      V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn)
    (escLocal : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → Prop)
    (hmk : ∀ s v (fam : Fin k → C) (resp : Fin k → WitOut),
      (∀ j, ((s, v, fam j), resp j) ∈ relOut) → Function.Injective fam →
      escLocal s v fam resp ∨ (s, mkWitness s v fam resp) ∈ relIn) :
    CM.coordinateWiseSpecialSoundWithEscape init impl (scalarStructure k hk)
      (escEventScalar hk relOut escLocal) relIn relOut V
      (treeExtractorScalar hk mkWitness) := by
  classical
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (scalarStructure_arity (Msg := Msg) (C := C) (k := k) hk).symm
  by_cases hesc : escEventScalar hk relOut escLocal stmtIn (tree2 v challenges)
  · exact Or.inl hesc
  refine Or.inr fun o hvalid => ?_
  have hne : (support init).Nonempty :=
    CM.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity ⟨0, by omega⟩))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (CM.isValid_iff_pure init impl
      (fun s tr => (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
      hpure hne relOut stmtIn o).mp hvalid
  obtain ⟨resp, hro, hbranch⟩ := collect_branch_data harity stmtIn v challenges o hvalid'
  have hinj := injective_of_nodeOk (Msg := Msg) (C := C) (hk := hk) hStruct.1
  have hcol : CMSR.collect (fun j : Fin k =>
      o (branchPathOf (tree2 v challenges) (Fin.cast harity j))) = some resp :=
    CMSR.collect_eq_some hro
  rcases hmk stmtIn v (fun j => challenges (Fin.cast harity j)) resp hbranch hinj with
    hbad | hgood
  · exact absurd
      (show escEventScalar hk relOut escLocal stmtIn (tree2 v challenges) from
        ⟨resp, hbranch, hbad⟩)
      hesc
  · refine ⟨mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp, ?_, hgood⟩
    change (CMSR.collect (fun j : Fin k =>
        o (branchPathOf (tree2 v challenges) (Fin.cast harity j)))).map
        (mkWitness stmtIn (readPre (tree2 v challenges)) (readFam hk (tree2 v challenges)))
      = some (mkWitness stmtIn v (fun j => challenges (Fin.cast harity j)) resp)
    rw [hcol]
    rfl

end Certificates

end CMSC

/-! ## Part E — runtime demo (kernel-checked): the real engine runs -/

namespace CMEngineDemo

open ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise.SingleRound

/-- `r = 0` star tree: `2 ^ 0 + 1 = 2` branches, challenge vectors `Fin 1 → ℕ`;
branch `j` carries the constant vector `j`. -/
def T : ChallengeTree (pSpec ℕ ℕ 0)
    (foldStructure (CarrierCom := ℕ) (C := ℕ) (r := 0)).arity 0 :=
  tree2 5 (fun j _ => (j : ℕ))

def mk : ℕ → ℕ → (Fin (2 ^ 0 + 1) → (Fin (2 ^ 0) → ℕ)) → (Fin (2 ^ 0 + 1) → ℕ) → ℕ :=
  fun s v fam resp => s + v + fam 1 0 + resp 0 + resp 1

-- extraction collects both leaf witnesses: 1 + 5 + 1 + 7 + 7
#eval CMSR.treeExtractor mk 1 T (fun _ => some 7)  -- expect some 21
-- absent witness at some leaf: extraction reports failure, no junk
#eval CMSR.treeExtractor mk 1 T (fun _ => none)  -- expect none

-- kernel-checked, not just #eval-checked:
example : CMSR.treeExtractor mk 1 T (fun _ => some 7) = some 21 := rfl
example : CMSR.treeExtractor mk 1 T (fun _ => none) = none := rfl

end CMEngineDemo

/-! ### Axiom audit -/

#print axioms CMEngines.rc_coordinateWiseSpecialSoundWith
#print axioms CMEngines.rcTreeExtractor
#print axioms CMSR.coordinateWiseSpecialSoundWith_of_mkWitness
#print axioms CMSR.coordinateWiseSpecialSoundWithEscape_of_mkWitness
#print axioms CMSC.coordinateWiseSpecialSoundWith_of_mkWitness_scalar
#print axioms CMSC.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar
#print axioms CMSR.fullTranscript_branchPathOf
#print axioms CMSR.treeExtractor
#print axioms CMSC.treeExtractorScalar

/-! ### IR gate: the engines and all their data readers compile to executable code -/

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for nm in [``CMEngines.rcTreeExtractor, ``ProtocolSpec.ChallengeTree.onlyPath,
             ``CMSR.treeExtractor, ``CMSR.branchPathOf, ``CMSR.collect,
             ``CMSC.treeExtractorScalar, ``CMSC.branchPathOf] do
    match Lean.IR.findEnvDecl env nm with
    | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
    | none   => Lean.logError m!"NO IR (noncomputable): {nm}"
