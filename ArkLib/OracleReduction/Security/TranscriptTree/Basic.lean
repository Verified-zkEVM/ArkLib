/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Trees of transcripts — core definitions

  This file defines `ChallengeTree`, the *tree of transcripts* of a public-coin protocol, together
  with the generic structural data attached to it. The tree branches only at challenge rounds: a
  message round has a single child (the prover's message), a challenge round has one child per
  branch (each labelled by the verifier's challenge), and every root-to-leaf path reads off a full
  transcript. Two paths that share their challenges up to a round share the same prefix, so the tree
  is exactly the family of transcripts a forking extractor produces and that special-soundness
  notions extract a witness from.

  Composing trees along sequential protocol composition is handled in `TranscriptTree.Composition`.

  ## Representation

  `ChallengeTree pSpec arity m` is the tree over the remaining rounds `m, …, n-1`, indexed by the
  current round `m : Fin (n + 1)`; a full tree is the `m = 0` case. Its three constructors are
  `leaf` (all rounds processed), `msgNode` (a message round, one child), and `chalNode` (a challenge
  round, `arity i` children). A challenge node stores the sibling labels and the child subtrees as
  two separate functions rather than one into a product, since a product would nest the recursive
  occurrence under `Prod`, which the kernel rejects. `LeafPath.transcript` reads a `FullTranscript`
  off a path, `transcripts` lists all leaf transcripts, and the membership lemmas identify
  "transcript on some path" with "transcript in the list".

  ## Decoupling structure from the soundness relation

  `ChallengeTree` does not fix what the sibling challenges at a node must satisfy. That condition is
  supplied as a `ChallengeTreeShape` — a branching `arity` and a `nodeOk` predicate on each round's
  siblings — and `ChallengeTree.IsStructured S` asserts every challenge node satisfies `S.nodeOk`. A
  concrete notion is then a choice of shape: pairwise-distinct siblings for plain special soundness,
  a coordinate-structured condition for CWSS (`CWSSStructure.toShape`). This keeps the composition
  results in `TranscriptTree.Composition` shape-generic, hence proved once for all notions.

  ## Main definitions

  - `ChallengeTree` — the inductive tree, branching only at challenge rounds.
  - `ChallengeTreeShape` / `ChallengeTree.IsStructured` — the shape (arity + `nodeOk`) and the
    predicate that every challenge node satisfies it.
  - `LeafPath`, `LeafPath.transcript` / `fullTranscript`, `transcripts` / `fullTranscripts` — the
    root-to-leaf paths, the transcript each selects, the list of all leaf transcripts, and their
    membership correspondence (`mem_fullTranscripts`, `exists_of_mem_fullTranscripts`).
  - `ChallengeTree.IsAccepting` — the verifier accepts every root-to-leaf transcript into the output
    language with probability one.
  - `Extractor.TreeBased` — the deterministic tree-consuming extractor shared by all tree-based
    notions.
  - `Verifier.treeSpecialSound` — the shape-generic tree-soundness predicate: a tree-based extractor
    that, on every `S`-structured accepting tree, recovers a witness. Plain special soundness
    (`Security.SpecialSoundness`) and coordinate-wise special soundness
    (`Security.CoordinateWiseSpecialSoundness`) are both instances, for different shapes.
  - `ChallengeTree.EscapeEvent` / `Verifier.treeSpecialSoundWithEscape` — the escape-threaded
    variant, for reductions whose extraction may instead break a cryptographic assumption: the
    conclusion is `esc stmtIn tree ∨ extraction succeeds`, with the extractor still a plain
    `Extractor.TreeBased`. The plain notion is the never-firing event
    (`treeSpecialSoundWithEscape_false_iff`), and every plain certificate lifts losslessly
    (`Verifier.treeSpecialSoundWith.withEscape`).

  ## Caveat

  The branching arity is fixed by the round index, not the path, so path-dependent branching is not
  supported. This matches the source notions and could be relaxed later.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

variable {n : ℕ}

/-- A **tree of transcripts** for a protocol `pSpec`, branching only at challenge rounds.

The tree is indexed by the current round `m : Fin (n + 1)` (the rounds `m, m+1, …, n-1` are still to
come). Each challenge round `i` branches into `arity i` children. A `ChallengeTree pSpec arity 0`
(rooted at round `0`) describes a full tree of transcripts; reading the messages and challenges
along each root-to-leaf path recovers the corresponding `FullTranscript pSpec` (see
`ChallengeTree.transcripts`).

The challenge labels and subtrees of a challenge node are kept as two separate functions (rather
than a single function into a product) so that the recursive occurrence is not nested under `Prod`,
which the kernel forbids.

Note: The challenge arity is determined by the round index, not the path. So path-dependent
branching (e.g. "branch into 2 if the first challenge is `0`, branch into 3 if it's `1`") is not
currently supported. This may be generalized in the future, but keeps the current design simple
enough to follow the CWSS paper proofs.
-/
inductive ChallengeTree (pSpec : ProtocolSpec n) (arity : pSpec.ChallengeIdx → ℕ) :
    Fin (n + 1) → Type where
  /-- A leaf, reached once all `n` rounds have been processed. -/
  | leaf : ChallengeTree pSpec arity (Fin.last n)
  /-- A message round: the prover sends a single message `msg`, and the tree continues with a
    single child. -/
  | msgNode (m : Fin n) (h : pSpec.dir m = .P_to_V) (msg : pSpec.Message ⟨m, h⟩)
      (child : ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc
  /-- A challenge round: the verifier branches into `arity ⟨m, h⟩` children, with `challenges j` the
    challenge value sent on branch `j` and `children j` the corresponding subtree. -/
  | chalNode (m : Fin n) (h : pSpec.dir m = .V_to_P)
      (challenges : Fin (arity ⟨m, h⟩) → pSpec.Challenge ⟨m, h⟩)
      (children : Fin (arity ⟨m, h⟩) → ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc

/-- A protocol-generic structural predicate for challenge-tree nodes.

The `arity` field fixes the number of children at every challenge round, while `nodeOk` records
the combinatorial predicate that the sibling challenges at that round must satisfy. Plain special
soundness and coordinate-wise special soundness are both instances of this shape abstraction. -/
@[ext]
structure ChallengeTreeShape (pSpec : ProtocolSpec n) where
  /-- Branching factor at every verifier-to-prover round. -/
  arity : pSpec.ChallengeIdx → ℕ
  /-- Predicate on the sibling challenge labels at a verifier-to-prover round. -/
  nodeOk : (i : pSpec.ChallengeIdx) → (Fin (arity i) → pSpec.Challenge i) → Prop

namespace ChallengeTree

variable {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}

section Shape

variable (S : ChallengeTreeShape pSpec)

/-- A tree is structured by a `ChallengeTreeShape` if every challenge node satisfies the shape's
node predicate and all subtrees are recursively structured. -/
def IsStructured :
    {m : Fin (n + 1)} → ChallengeTree pSpec S.arity m → Prop
  | _, .leaf => True
  | _, .msgNode _ _ _ child => child.IsStructured
  | _, .chalNode _ h challenges children =>
      S.nodeOk ⟨_, h⟩ challenges ∧ ∀ j, (children j).IsStructured

end Shape

section LeafPath

/-- A root-to-leaf path through a challenge tree. At challenge nodes, the path records the selected
child index; at message nodes there is only one child to follow. -/
inductive LeafPath : {m : Fin (n + 1)} → ChallengeTree pSpec arity m → Type where
  | leaf : LeafPath .leaf
  | msg {m : Fin n} {h : pSpec.dir m = .P_to_V} {msg : pSpec.Message ⟨m, h⟩}
      {child : ChallengeTree pSpec arity m.succ}
      (path : LeafPath child) : LeafPath (.msgNode m h msg child)
  | chal {m : Fin n} {h : pSpec.dir m = .V_to_P}
      {challenges : Fin (arity ⟨m, h⟩) → pSpec.Challenge ⟨m, h⟩}
      {children : Fin (arity ⟨m, h⟩) → ChallengeTree pSpec arity m.succ}
      (j : Fin (arity ⟨m, h⟩)) (path : LeafPath (children j)) :
      LeafPath (.chalNode m h challenges children)

namespace LeafPath

/-- **Every tree with positive branching has a leaf path**: descend through message nodes, and at
each challenge node take the first child.

This is what makes a subtree's transcript set inhabited, which matters as soon as verifiers are
allowed to *reject*: to rule out a rejecting prefix one must exhibit an actual transcript of the
subtree below it and contradict acceptance there. For pure verifiers the fact is never needed,
which is why it appears only now. Positivity is free for every coordinate-wise structure, whose
arity is `ℓᵢ·(kᵢ−1)+1` (`CWSSStructure.arity_pos`). -/
def some (harity : ∀ i, 0 < arity i) :
    {m : Fin (n + 1)} → (T : ChallengeTree pSpec arity m) → LeafPath T
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (some harity child)
  | _, .chalNode m h _ children =>
      .chal ⟨0, harity ⟨m, h⟩⟩ (some harity (children ⟨0, harity ⟨m, h⟩⟩))

/-- Read the full transcript selected by a leaf path, extending an already-accumulated prefix. -/
def transcript :
    {m : Fin (n + 1)} → {T : ChallengeTree pSpec arity m} →
      LeafPath T → Transcript m pSpec → FullTranscript pSpec
  | _, _, .leaf, pre => pre
  | _, _, @LeafPath.msg _ _ _ _ _ message _ path, pre => path.transcript (pre.concat message)
  | _, _, @LeafPath.chal _ _ _ _ _ chals _ j path, pre =>
      path.transcript (pre.concat (chals j))

/-- Read the full transcript selected by a leaf path in a tree rooted at round `0`. -/
def fullTranscript {T : ChallengeTree pSpec arity 0} (path : LeafPath T) :
    FullTranscript pSpec :=
  path.transcript default

end LeafPath

end LeafPath

/-- Collect all root-to-leaf transcripts of a tree, given the partial transcript `pre` accumulated
  on the path from the root to the current node.

  At a message (resp. challenge) node we extend the prefix by the stored message (resp. by each
  child's challenge label) and recurse. At a leaf the accumulated prefix is a `FullTranscript`. -/
def transcripts :
    {m : Fin (n + 1)} → ChallengeTree pSpec arity m → Transcript m pSpec →
      List (FullTranscript pSpec)
  | _, .leaf, pre => [pre]
  | _, .msgNode _ _ msg child, pre => child.transcripts (pre.concat msg)
  | _, .chalNode m h challenges children, pre =>
      (List.finRange (arity ⟨m, h⟩)).flatMap fun j =>
        (children j).transcripts (pre.concat (challenges j))

/-- The transcripts of a full tree (rooted at round `0`), starting from the empty prefix. -/
def fullTranscripts (tree : ChallengeTree pSpec arity 0) : List (FullTranscript pSpec) :=
  tree.transcripts default

namespace LeafPath

/-- The transcript selected by a path appears in the list of transcripts collected from the tree. -/
theorem mem_transcripts :
    {m : Fin (n + 1)} → {T : ChallengeTree pSpec arity m} →
      (path : LeafPath T) → (pre : Transcript m pSpec) →
        path.transcript pre ∈ T.transcripts pre
  | _, _, .leaf, pre => by simp [transcript, transcripts]
  | _, _, @LeafPath.msg _ _ _ _ _ message _ path, pre => by
      simp only [transcript, transcripts]
      exact mem_transcripts path (pre.concat message)
  | _, _, @LeafPath.chal _ _ _ _ _ chals _ j path, pre => by
      simp only [transcript, transcripts, List.mem_flatMap, List.mem_finRange]
      exact ⟨j, trivial, mem_transcripts path (pre.concat (chals j))⟩

/-- The transcript selected by a full-tree path appears in `fullTranscripts`. -/
theorem mem_fullTranscripts {T : ChallengeTree pSpec arity 0} (path : LeafPath T) :
    path.fullTranscript ∈ T.fullTranscripts := by
  simpa [fullTranscript, ChallengeTree.fullTranscripts] using mem_transcripts path default

/-- Every transcript listed by a tree is selected by some leaf path. -/
theorem exists_of_mem_transcripts :
    {m : Fin (n + 1)} → {T : ChallengeTree pSpec arity m} →
      {pre : Transcript m pSpec} → {tr : FullTranscript pSpec} →
        tr ∈ T.transcripts pre → ∃ path : LeafPath T, path.transcript pre = tr
  | _, .leaf, pre, tr, h => by
      simp only [transcripts, List.mem_singleton] at h
      exact ⟨.leaf, h.symm⟩
  | _, .msgNode _ _ _ child, pre, tr, h => by
      simp only [transcripts] at h
      obtain ⟨path, hpath⟩ := exists_of_mem_transcripts h
      exact ⟨.msg path, hpath⟩
  | _, .chalNode _ _ chals children, pre, tr, h => by
      simp only [transcripts, List.mem_flatMap, List.mem_finRange] at h
      obtain ⟨j, _, hj⟩ := h
      obtain ⟨path, hpath⟩ := exists_of_mem_transcripts hj
      exact ⟨.chal j path, hpath⟩

/-- Every transcript listed by a full tree is selected by some leaf path. -/
theorem exists_of_mem_fullTranscripts {T : ChallengeTree pSpec arity 0}
    {tr : FullTranscript pSpec} (hmem : tr ∈ T.fullTranscripts) :
      ∃ path : LeafPath T, path.fullTranscript = tr := by
  simpa [fullTranscript, ChallengeTree.fullTranscripts] using
    (exists_of_mem_transcripts (T := T) (pre := default) (tr := tr) hmem)

end LeafPath

section IsAccepting

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {arity : pSpec.ChallengeIdx → ℕ}

/-- A tree of transcripts is **accepting** with respect to an input statement `stmtIn` and an output
  language `langOut` if the verifier accepts every root-to-leaf transcript, i.e. for each such
  transcript the verifier outputs a statement in `langOut` with probability `1`.

  This is the tree-level analogue of the verifier's "accept" condition, phrased exactly as in the
  round-by-round state-function machinery (cf. `Verifier.StateFunction.toFun_full`). -/
def IsAccepting (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (langOut : Set StmtOut)
    (tree : ChallengeTree pSpec arity 0) : Prop :=
  ∀ tr ∈ tree.fullTranscripts,
    Pr[(· ∈ langOut) |
      OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] = 1

end IsAccepting

section EscapeEvent

/-- An **escape event**: a statement-indexed predicate on full challenge trees, the
  hypothesis-side home of cryptographic escapes (e.g. "the openings derived from this tree collide
  under the fixed commitment key — a Module-SIS solution"). A tree-special-soundness certificate
  concludes `esc stmt tree ∨ extraction succeeds`, so an escape is an event on the *observable
  data*, never an output the extractor can fabricate.

  An escape event is a **trusted specification**, on the same footing as a package's
  `relIn`/`relOut`: nothing in the framework checks it. Two conditions every instance must satisfy,
  reviewed by reading its definition:

  - **hardness-tied and unconditional**: every `(stmt, tree)` satisfying the event must yield a
    break of the ambient assumption, checked against protocol parameters fixed outside the
    statement — at *every* pair, including statements no honest execution produces (composed
    events evaluate factor events at adversarially controllable intermediate statements);
  - **tree-determined**: the event may only constrain values computed from `(stmt, tree)`. It must
    not mention the verifier, the sampling `(init, impl)`, the *input* relation `relIn`, an
    extractor, or acceptance, since those smuggle in tautologies (e.g.
    `fun s t => (s, Ext s t) ∉ relIn` makes any certificate at `Ext` vacuous). Constraining the
    tree's per-branch responses by the *output* relation is fine and desirable — see below.

  Beyond honesty, aim for a **tight** event: one that fires only where extraction genuinely fails.
  Tightness is not enforced; a wider event just yields a weaker certificate, and a statement-only
  event like "some collision of this commitment exists" is honest yet worthless because it fires
  almost everywhere. Pinning the tree's per-branch responses to `relOut` (as
  `CoordinateWise.SingleRound.escEvent` does) is the standard way to get tightness.

  The trivial event `fun _ _ => False` is the escape-free degeneration (lossless: see
  `Verifier.treeSpecialSoundWith.withEscape`). -/
def EscapeEvent (Stmt : Type) (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  Stmt → ChallengeTree pSpec arity 0 → Prop

end EscapeEvent

end ChallengeTree

end ProtocolSpec

namespace Extractor

open ProtocolSpec

/-- A **tree-based extractor**: a deterministic algorithm that, given the input statement and a tree
  of transcripts (rooted at round `0`), outputs an input witness.

  This is the type of extractor used by tree-based knowledge-extraction notions — plain `k`-special
  soundness and coordinate-wise special soundness alike. The tree already contains all transcripts,
  so the extractor is a plain function; it is the rewinding/forking extractor of the
  knowledge-soundness reduction that actually *produces* the tree. Both notions share it, so it
  lives here on the shared `ChallengeTree` rather than in either notion's file. -/
def TreeBased (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → ProtocolSpec.ChallengeTree pSpec arity 0 → WitIn

end Extractor

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A named tree-based extractor `Ext` **witnesses tree special soundness** of a verifier with
  respect to a generic challenge-tree shape `S`, an input relation `relIn` and an output relation
  `relOut`: for every input statement `stmtIn` and every tree of transcripts that is

  - `S`-structured (its sibling challenges satisfy the shape's `nodeOk` predicate), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `relOut.language`),

  the extracted witness `Ext stmtIn tree` satisfies `(stmtIn, Ext stmtIn tree) ∈ relIn`.

  This named form is the **content-bearing** statement of special soundness: it pins the
  extraction *algorithm*, so it asserts something about the actual output of `Ext` on every
  accepting tree. Its existential closure is `Verifier.treeSpecialSound` — prefer the named form
  in advertised protocol statements, since a chain of named certificates exposes a runnable
  end-to-end extractor (`chain.extractor`), which is what a later knowledge-error accounting has
  to run. Reductions whose extraction may instead break a cryptographic assumption use
  `Verifier.treeSpecialSoundWithEscape` below. -/
def treeSpecialSoundWith (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl verifier stmtIn relOut.language →
      (stmtIn, Ext stmtIn tree) ∈ relIn

/-- A verifier is **tree special sound** with respect to a generic challenge-tree shape `S`, an
  input relation `relIn` and an output relation `relOut` if *some* tree-based extractor witnesses
  it (`Verifier.treeSpecialSoundWith`).

  This is the shape-generic core of tree-based knowledge extraction: every concrete special-
  soundness-style notion is an instance obtained by supplying a shape. Plain `k`-special soundness
  (`Verifier.specialSound`, `Security.SpecialSoundness`) supplies the pairwise-distinct shape;
  coordinate-wise special soundness (`Verifier.coordinateWiseSpecialSound`,
  `Security.CoordinateWiseSpecialSoundness`) supplies the CWSS shape `D.toShape`. Phrasing the
  notion over an arbitrary `ChallengeTreeShape` is what lets the composition theory be proved once
  generically (see `Verifier.append_treeSpecialSoundWith`) and reused by each concrete notion.

  The extractor is existential here, which loses the *algorithm*: advertised protocol statements
  should use the named form `treeSpecialSoundWith` at an explicit extractor and keep this form for
  plumbing, e.g. the right factor of an append (`Verifier.append_treeSpecialSoundWith`). -/
def treeSpecialSound (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ E : Extractor.TreeBased StmtIn WitIn pSpec S.arity,
    treeSpecialSoundWith init impl S relIn relOut verifier E

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The existential notion is definitionally the existential closure of the named one. -/
theorem treeSpecialSound_iff_exists (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.treeSpecialSound init impl S relIn relOut ↔
      ∃ Ext, treeSpecialSoundWith init impl S relIn relOut verifier Ext := Iff.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor. -/
theorem treeSpecialSoundWith.toTreeSpecialSound {S : ChallengeTreeShape pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    verifier.treeSpecialSound init impl S relIn relOut := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Shape-congruence transport for named tree special soundness.** The named notion transports
  along an equality of shapes, with the extractor carried across heterogeneously. The extractor's
  type mentions `S.arity`, so a plain `rw` at the shape is motive-incorrect; this lemma does the
  transport once and for all (in practice `hExt := HEq.rfl`, since the relevant shape equalities
  — e.g. `CWSSStructure.toShape_append` — have definitionally equal arities). -/
theorem treeSpecialSoundWith_congr {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    {Ext' : Extractor.TreeBased StmtIn WitIn pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    treeSpecialSoundWith init impl S' relIn relOut verifier Ext' := by
  subst hS
  obtain rfl := eq_of_heq hExt
  exact h

/-! ## Escape-threaded tree special soundness

For reductions whose extraction may instead break a cryptographic assumption: the conclusion becomes
a disjunction against an escape event (`ChallengeTree.EscapeEvent`). Relations and extractors stay
unchanged, and since the event never mentions the extractor, no choice of extractor can trivialize
the statement — a certificate is exactly as strong as its event is honest. -/

/-- **Escape-threaded tree special soundness, named form.** `Verifier.treeSpecialSoundWith` with
  an escape-event disjunct: on every structured accepting tree, either the tree exhibits the escape
  event `esc` (a trusted spec — see `ChallengeTree.EscapeEvent`) or the named extractor produces a
  `relIn`-witness. -/
def treeSpecialSoundWithEscape (S : ChallengeTreeShape pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl verifier stmtIn relOut.language →
      esc stmtIn tree ∨ (stmtIn, Ext stmtIn tree) ∈ relIn

/-- Existential closure of `treeSpecialSoundWithEscape`, for use as the *right* factor of an
  append. The named form is preferred in advertised statements, since a composed chain then exposes
  a runnable end-to-end extractor. -/
def treeSpecialSoundEscape (S : ChallengeTreeShape pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity,
    treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor. -/
theorem treeSpecialSoundWithEscape.toEscape {S : ChallengeTreeShape pSpec}
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundEscape init impl S esc relIn relOut verifier := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- At the never-firing event the escape notion is the plain notion: the escape layer is a
  conservative extension. -/
theorem treeSpecialSoundWithEscape_false_iff (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity) :
    treeSpecialSoundWithEscape init impl S (fun _ _ => False) relIn relOut verifier Ext ↔
      treeSpecialSoundWith init impl S relIn relOut verifier Ext := by
  constructor <;> intro h stmtIn tree hstr hacc
  · exact (h stmtIn tree hstr hacc).resolve_left id
  · exact Or.inr (h stmtIn tree hstr hacc)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Lossless escape lift**: a plain certificate holds at *any* escape event, via the right
  disjunct — so an escape-free protocol enters an escape-threaded chain for free. -/
theorem treeSpecialSoundWith.withEscape {S : ChallengeTreeShape pSpec}
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext :=
  fun stmtIn tree hstr hacc => Or.inr (h stmtIn tree hstr hacc)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Escape events are monotone: a certificate at `esc` holds at any weaker (larger) event. -/
theorem treeSpecialSoundWithEscape.mono {S : ChallengeTreeShape pSpec}
    {esc esc' : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    (hmono : ∀ s t, esc s t → esc' s t)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S esc' relIn relOut verifier Ext :=
  fun stmtIn tree hstr hacc => (h stmtIn tree hstr hacc).imp (hmono _ _) id

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Shape-congruence transport for escape-threaded named tree special soundness.** Both the
  extractor and the escape event have types mentioning `S.arity`, so a plain `rw` at the shape is
  motive-incorrect; this lemma carries them across heterogeneously (in practice both `HEq`s are
  `HEq.rfl`, the relevant shape equalities having definitionally equal arities). -/
theorem treeSpecialSoundWithEscape_congr {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {esc' : ChallengeTree.EscapeEvent StmtIn pSpec S'.arity} (hEsc : HEq esc esc')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn pSpec S.arity}
    {Ext' : Extractor.TreeBased StmtIn WitIn pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S' esc' relIn relOut verifier Ext' := by
  subst hS
  obtain rfl := eq_of_heq hEsc
  obtain rfl := eq_of_heq hExt
  exact h

end Verifier
