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
  - `ChallengeTree.onlyPath` — the unique root-to-leaf path of a challenge-free tree, read off the
    tree by structural recursion — and `ChallengeTree.somePath`, its positive-arity analogue: *some*
    leaf path of any tree that branches at all.
  - `ChallengeTree.IsAccepting` — the verifier accepts every root-to-leaf transcript into the output
    language with probability one.
  - `Verifier.Outputs` — the statements the verifier *can* output on a transcript under the fixed
    sampling, with the acceptance bridges (`mem_language_of_mem_outputs`,
    `outputs_nonempty_of_isAccepting`) and the pure-verifier pin-down (`outputs_pure_subsingleton`,
    `pure_verdict_mem_outputs`). `support_init_nonempty_of_prob_one` and
    `not_accepting_of_failure` read the same acceptance fact off a single transcript.
  - `ChallengeTree.LeafWitnesses` / `LeafWitnesses.IsValid` — one candidate *output* witness per
    leaf, and what makes such a witnessing honest: every answer certifies, in `relOut`, some
    statement the verifier can output at that leaf. At a pure verifier this collapses to per-verdict
    witnessing (`LeafWitnesses.isValid_iff_pure`).
  - `Extractor.TreeBased` — the tree-consuming extractor shared by all tree-based notions: it
    consumes the tree *and* a leaf witnessing, and returns `Option WitIn`.
  - `Verifier.treeSpecialSoundWith` / `Verifier.treeSpecialSound` — the shape-generic
    tree-soundness predicate (named and existential): on every `S`-structured accepting tree, the
    extractor succeeds on every valid witnessing. Plain special soundness
    (`Security.SpecialSoundness`) and coordinate-wise special soundness
    (`Security.CoordinateWiseSpecialSoundness`) are both instances, for different shapes.
  - `ChallengeTree.EscapeEvent` / `Verifier.treeSpecialSoundWithEscape` — the escape-threaded
    variant, for reductions whose extraction may instead break a cryptographic assumption: the
    conclusion is `esc stmtIn tree ∨ extraction succeeds`. The plain notion is the never-firing
    event (`treeSpecialSoundWithEscape_false_iff`), and every plain certificate lifts losslessly
    (`Verifier.treeSpecialSoundWith.withEscape`).
  - `ChallengeTree.canonWitnesses` / `canonWitnesses_isValid` and
    `Verifier.treeSpecialSoundWith.mem_relIn_of_isAccepting` — the closer: acceptance alone supplies
    a valid witnessing, so the validity premise is never an obstruction and a certificate can still
    be read unconditionally.

  ## Caveat

  The branching arity is fixed by the round index, not the path, so path-dependent branching is not
  supported. This matches the source notions and could be relaxed later.
-/

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

/-- The **unique root-to-leaf path** of a challenge-free tree (`IsEmpty pSpec.ChallengeIdx`).

With no challenge rounds a tree cannot contain a `chalNode`, so it is a single chain of message
nodes ending in a leaf: there is no branch to choose, and the path is read off the tree by plain
structural recursion. In particular it is **computable**, which is what the zero-challenge
special-soundness bridges in `Security.CoordinateWiseSpecialSoundness.NoChallenge` build their
extractors on. The transcript it selects, `tree.onlyPath.fullTranscript`, is the tree's unique full
transcript and lies in `tree.fullTranscripts` by `LeafPath.mem_fullTranscripts`. -/
def onlyPath [IsEmpty pSpec.ChallengeIdx] :
    {m : Fin (n + 1)} → (tree : ChallengeTree pSpec arity m) → LeafPath tree
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (onlyPath child)
  | _, .chalNode m h _ _ => isEmptyElim (⟨m, h⟩ : pSpec.ChallengeIdx)

/-- **Some** root-to-leaf path of a tree whose branching is everywhere positive: take the first
branch at each challenge node.

Where `onlyPath` needs the tree to be challenge-free, this needs only `0 < arity i` — enough to
know a challenge node *has* a child. It is the probe of the guarded composition theorems: a guarded
left factor learns that its check passes on a prefix transcript only by exhibiting *some* suffix
leaf beneath it, and a witness of "the suffix tree is inhabited" is exactly this path. Like
`onlyPath` it is plain structural recursion, hence computable. -/
def somePath (harity : ∀ i, 0 < arity i) :
    {m : Fin (n + 1)} → (tree : ChallengeTree pSpec arity m) → LeafPath tree
  | _, .leaf => .leaf
  | _, .msgNode _ _ _ child => .msg (somePath harity child)
  | _, .chalNode k h _ children =>
      .chal ⟨0, harity ⟨k, h⟩⟩ (somePath harity (children ⟨0, harity ⟨k, h⟩⟩))

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
  | _, _, .leaf, pre => by
      change pre ∈ [pre]
      exact List.mem_cons_self
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
      have htr : tr = pre := List.eq_of_mem_singleton h
      exact ⟨.leaf, htr.symm⟩
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

/-! ## The verifier's reachable output statements

A leaf witnessing (below) certifies its witnesses *at statements the verifier can actually output*
on that leaf's transcript. `Verifier.Outputs` is that set, read off the fixed sampling
`(init, impl)`; the lemmas here relate it to `IsAccepting` (on an accepting tree the set is nonempty
and contained in the output language) and pin it down at a pure verifier (there it is the singleton
of the verdict, as soon as the sampling can produce a seed). -/

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-- The set of statements the verifier **can output** on `(stmtIn, tr)` under the fixed sampling
  `(init, impl)`: the `some`-values in the support of its run.

  This is the reachability condition of `ChallengeTree.LeafWitnesses.IsValid`: a witnessing may only
  certify witnesses at statements in this set, which is what makes it a witnessing *of this tree
  under this verifier* rather than an arbitrary function into `Option WitOut`. -/
def Outputs (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (tr : pSpec.FullTranscript) : Set StmtOut :=
  {out | some out ∈ support (do (simulateQ impl (V.run stmtIn tr)).run' (← init))}

/-- `Outputs` membership, spelled through the `OptionT` the acceptance condition uses. -/
theorem mem_outputs_iff (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (tr : pSpec.FullTranscript) (out : StmtOut) :
    out ∈ Outputs init impl V stmtIn tr ↔
      out ∈ support (OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)) := by
  rw [OptionT.mem_support_iff, OptionT.run_mk]; rfl

/-- On an accepting tree, every statement the verifier can output at a leaf lies in the output
  language. -/
theorem mem_language_of_mem_outputs {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relOut : Set (StmtOut × WitOut)} {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0}
    (hacc : tree.IsAccepting init impl V stmtIn relOut.language)
    (p : ChallengeTree.LeafPath tree) {out : StmtOut}
    (hout : out ∈ Outputs init impl V stmtIn p.fullTranscript) :
    out ∈ relOut.language := by
  have h := hacc p.fullTranscript p.mem_fullTranscripts
  rw [probEvent_eq_one_iff] at h
  exact h.2 out ((mem_outputs_iff init impl V stmtIn p.fullTranscript out).1 hout)

/-- A leaf at which the verifier can output *nothing* refutes acceptance: acceptance with
  probability one rules out certain failure. -/
theorem not_isAccepting_of_no_outputs (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} (p : ChallengeTree.LeafPath tree) (lang : Set StmtOut)
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

/-- On an accepting tree the reachable-output set at every leaf is **nonempty**. -/
theorem outputs_nonempty_of_isAccepting {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0} {lang : Set StmtOut}
    (hacc : tree.IsAccepting init impl V stmtIn lang) (p : ChallengeTree.LeafPath tree) :
    (Outputs init impl V stmtIn p.fullTranscript).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  exact not_isAccepting_of_no_outputs init impl V stmtIn p lang hempty hacc

/-- An accepting tree with a leaf forces the sampling's support to be nonempty — the entry ticket to
  `pure_verdict_mem_outputs`, hence to `LeafWitnesses.isValid_iff_pure`, in every certificate. -/
theorem support_init_nonempty_of_accepting {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0} {lang : Set StmtOut}
    (hacc : tree.IsAccepting init impl V stmtIn lang) (p : ChallengeTree.LeafPath tree) :
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

/-- A pure verifier can only output its verdict: `Outputs` is a subset of that singleton. -/
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

/-- A pure verifier's verdict **is** reachable, as soon as the sampling can produce a seed. -/
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

/-- Acceptance of a *single* transcript with probability one already forces the sampling's support
  to be nonempty: a sampling that produces no seed makes the whole computation fail.

  The transcript-level form of `support_init_nonempty_of_accepting`, used where the acceptance fact
  in hand is about one leaf rather than a tree. -/
theorem support_init_nonempty_of_prob_one {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
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

/-- A verifier that **rejects outright** on a transcript cannot accept it with probability one: on
  the `failure` branch the run fails certainly.

  This is what makes a guarded verifier's check *learnable* from acceptance — see
  `Verifier.append_run_guardedLeft`, whose rejecting branch this lemma refutes. -/
theorem not_accepting_of_failure {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {stmt : StmtIn} {tr : pSpec.FullTranscript} (hV : V.verify stmt tr = failure)
    {lang : Set StmtOut}
    (h : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) : False := by
  have hne : (support init).Nonempty := support_init_nonempty_of_prob_one h
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

end Verifier

/-! ## Leaf witnessings

The second input of a reduction-of-knowledge extractor: one candidate *output* witness per
root-to-leaf transcript. In a chain these are produced by the downstream reduction's extractor; at
the top of a security statement they come classically from acceptance
(`ChallengeTree.canonWitnesses`). -/

namespace ProtocolSpec.ChallengeTree

open Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {arity : pSpec.ChallengeIdx → ℕ}

/-- A **leaf witnessing**: one candidate output witness per root-to-leaf transcript of `tree`, or
  `none` where the witnessing declines.

  This is the "output witnesses" input of a reduction-of-knowledge extractor
  (`Extractor.TreeBased`). In a composed chain it is produced by the *downstream* extractor, which
  is exactly how a chain closes on a terminal link whose witness the tree itself contains. -/
def LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=
  ChallengeTree.LeafPath tree → Option WitOut

namespace LeafWitnesses

/-- A leaf witnessing is **valid** when it answers at every leaf and each answer certifies, in
  `relOut`, *some* statement the verifier can actually output on that leaf's transcript
  (`Verifier.Outputs`).

  The reachability condition is the notion's honesty discipline, carried in the premise: trusting a
  witness at a statement the verifier cannot output is unrepresentable, so a witnessing citing only
  unreachable statements is not a witnessing of the tree at all. The quantifier over reachable
  outputs is `∃`, not `∀`: demanding one witness serve *every* reachable statement is unsatisfiable
  at a randomized verifier with two separated outputs, which would make the notion vacuous.

  At a pure verifier validity collapses to per-verdict witnessing (`isValid_iff_pure`), which is why
  engine certificates need no hypothesis beyond the purity they already carry. -/
def IsValid (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) {tree : ChallengeTree pSpec arity 0}
    (o : LeafWitnesses tree WitOut) : Prop :=
  ∀ p, ∃ w, o p = some w ∧
    ∃ out ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut

/-- **The pure-case collapse.** At a pure verifier with a productive sampling, validity is *exactly*
  per-verdict witnessing: the statements are pinned by the verdict function rather than carried by
  the witnessing.

  Engine certificates consume the forward direction (their purity hypothesis pins the statements);
  composition proofs produce validity with the backward one. -/
theorem isValid_iff_pure (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (hV : ∀ stmt tr, V.verify stmt tr = pure (verify stmt tr))
    (hinit : (support init).Nonempty) (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} (o : LeafWitnesses tree WitOut) :
    o.IsValid init impl V relOut stmtIn ↔
      ∀ p, ∃ w, o p = some w ∧ (verify stmtIn p.fullTranscript, w) ∈ relOut := by
  constructor
  · intro h p
    obtain ⟨w, hw, out, hout, hrel⟩ := h p
    exact ⟨w, hw,
      Verifier.outputs_pure_subsingleton init impl V verify hV stmtIn p.fullTranscript hout ▸ hrel⟩
  · intro h p
    obtain ⟨w, hw, hrel⟩ := h p
    exact ⟨w, hw, verify stmtIn p.fullTranscript,
      Verifier.pure_verdict_mem_outputs init impl verify hV hinit stmtIn p.fullTranscript, hrel⟩

end LeafWitnesses

section CanonWitnesses

open scoped Classical in
/-- The **canonical witnessing**, i.e. exactly what acceptance already guarantees: at each leaf, a
  chosen `relOut`-witness at a chosen reachable statement where one exists, and `none` elsewhere.

  Classical by construction, and that is its whole point: it lives in proofs and in the top-level
  closer that reads a certificate unconditionally
  (`Verifier.treeSpecialSoundWith.mem_relIn_of_isAccepting`), and is erased at codegen. Extraction
  *algorithms* never call it — they consume the witnessing their caller supplies. -/
noncomputable def canonWitnesses (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn)
    {tree : ChallengeTree pSpec arity 0} : LeafWitnesses tree WitOut :=
  fun p =>
    if h : ∃ w, ∃ out ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut
    then some h.choose else none

/-- The canonical witnessing is **valid on every accepting tree**: the validity premise of the
  soundness notion is never an obstruction, which is what lets a certificate be read
  unconditionally (`Verifier.treeSpecialSoundWith.mem_relIn_of_isAccepting`). -/
theorem canonWitnesses_isValid {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relOut : Set (StmtOut × WitOut)} {stmtIn : StmtIn} {tree : ChallengeTree pSpec arity 0}
    (hacc : tree.IsAccepting init impl V stmtIn relOut.language) :
    (canonWitnesses init impl V relOut stmtIn (tree := tree)).IsValid
      init impl V relOut stmtIn := by
  intro p
  obtain ⟨out, hout⟩ := Verifier.outputs_nonempty_of_isAccepting hacc p
  obtain ⟨w, hw⟩ := (Set.mem_language_iff relOut _).1
    (Verifier.mem_language_of_mem_outputs hacc p hout)
  have hex : ∃ w, ∃ out ∈ Verifier.Outputs init impl V stmtIn p.fullTranscript, (out, w) ∈ relOut :=
    ⟨w, out, hout, hw⟩
  exact ⟨hex.choose, by simp [canonWitnesses, dif_pos hex], hex.choose_spec⟩

end CanonWitnesses

end ProtocolSpec.ChallengeTree

namespace Extractor

open ProtocolSpec

/-- A **tree-based extractor**: assemble an input witness from the input statement, a tree of
  transcripts (rooted at round `0`), and one candidate output witness per leaf
  (`ChallengeTree.LeafWitnesses`) — or decline, returning `none`.

  The leaf witnessing is the second input of a reduction-of-knowledge extractor, and it is not
  eliminable: a `ChallengeTree` carries messages and challenges only, never an output witness, so
  for a cryptographic input relation no *total* function of `(stmtIn, tree)` alone can land in it.
  In a composed chain the witnessing is supplied by the downstream extractor, and the chain closes
  on a terminal link whose witness the tree does contain.

  `StmtOut` is deliberately **absent**: the extractor extracts a witness, full stop. Attributing
  output statements to leaves is the verifier's business, and output statements enter only through
  the soundness notion's validity premise (`ChallengeTree.LeafWitnesses.IsValid`). Both tree-based
  notions — plain `k`-special soundness and coordinate-wise special soundness — share this type, so
  it lives here on the shared `ChallengeTree`. -/
def TreeBased (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → (tree : ProtocolSpec.ChallengeTree pSpec arity 0) →
    tree.LeafWitnesses WitOut → Option WitIn

end Extractor

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-! ## Tree special soundness at the witness-only extractor

The notion the library states, at `Extractor.TreeBased`: on every structured accepting tree,
extraction succeeds *on every valid leaf witnessing*. One clause — the honesty discipline is the
validity premise's reachability condition (`ChallengeTree.LeafWitnesses.IsValid`), not a separate
conjunct, and there is no claim map for a certificate to be honest about, because the extractor
attributes no statements.

The premise is never an obstruction: the canonical witnessing is valid on every accepting tree
(`ChallengeTree.canonWitnesses_isValid`), so a certificate can still be read unconditionally
(`treeSpecialSoundWith.mem_relIn_of_isAccepting`). -/

/-- A named tree-based extractor `Ext` **witnesses tree special soundness** of a verifier with
  respect to a generic challenge-tree shape `S`, an input relation `relIn` and an output relation
  `relOut`: for every input statement `stmtIn` and every tree of transcripts that is

  - `S`-structured (its sibling challenges satisfy the shape's `nodeOk` predicate), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `relOut.language`),

  and for every **valid** leaf witnessing `o` of that tree
  (`ChallengeTree.LeafWitnesses.IsValid` — each of its witnesses certifies, in `relOut`, some
  statement the verifier can output at that leaf), the extractor succeeds: `Ext stmtIn tree o` is
  `some w` with `(stmtIn, w) ∈ relIn`.

  This named form is the **content-bearing** statement of special soundness: it pins the extraction
  *algorithm*, so it asserts something about the actual output of `Ext`. Its existential closure is
  `Verifier.treeSpecialSound` — prefer the named form in advertised protocol statements, since a
  chain of named certificates exposes a runnable end-to-end extractor (`chain.extractor`), which is
  what a later knowledge-error accounting has to run. Reductions whose extraction may instead break
  a cryptographic assumption use `Verifier.treeSpecialSoundWithEscape` below. -/
def treeSpecialSoundWith (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl verifier stmtIn relOut.language →
      ∀ o : tree.LeafWitnesses WitOut, o.IsValid init impl verifier relOut stmtIn →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- **Escape-threaded tree special soundness, named form.** `Verifier.treeSpecialSoundWith` with an
  escape-event disjunct: on every structured accepting tree, either the tree exhibits the escape
  event `esc` (a trusted spec — see `ChallengeTree.EscapeEvent`) or extraction succeeds on every
  valid leaf witnessing. An escaping factor owes no witness, and the disjunction is decided before
  any witnessing is seen.

  **The quantifier order is deliberate: do not commute it.** The disjunction sits *outside* the
  witnessing quantifier — `esc ∨ ∀ o valid, …`, not `∀ o valid, esc ∨ …`. The two are not
  interchangeable: this form is strictly stronger, and it is what makes the escape decision
  independent of the supplied witnessing, so an escape cannot be conjured by feeding the reduction
  an awkward set of output witnesses. The composition proofs depend on it —
  `append_treeSpecialSoundWithEscape_guardedLeft` resolves both factors' escape disjuncts *before*
  it introduces a witnessing (`refine Or.inr fun o hvalid => ?_`), which is only possible at this
  order — and so does the unconditioned closer
  `treeSpecialSoundWithEscape.escape_or_mem_relIn_of_isAccepting`, which passes the escape disjunct
  through untouched. A later "simplification" pushing the `∨` inside the `∀` would silently weaken
  every certificate in the chain. -/
def treeSpecialSoundWithEscape (S : ChallengeTreeShape pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec S.arity 0,
    tree.IsStructured S →
    tree.IsAccepting init impl verifier stmtIn relOut.language →
      esc stmtIn tree ∨
      ∀ o : tree.LeafWitnesses WitOut, o.IsValid init impl verifier relOut stmtIn →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn

/-- A verifier is **tree special sound** with respect to a shape `S`, an input relation `relIn` and
  an output relation `relOut` if *some* tree-based extractor witnesses it
  (`Verifier.treeSpecialSoundWith`).

  This is the shape-generic core of tree-based knowledge extraction: every concrete
  special-soundness-style notion is an instance obtained by supplying a shape — plain `k`-special
  soundness (`Verifier.specialSound`) the pairwise-distinct shape, coordinate-wise special soundness
  (`Verifier.coordinateWiseSpecialSound`) the CWSS shape `D.toShape`.

  The extractor is existential here, which loses the *algorithm*: advertised protocol statements
  should use the named form at an explicit extractor and keep this form for plumbing. -/
def treeSpecialSound (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ E : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity,
    treeSpecialSoundWith init impl S relIn relOut verifier E

/-- Existential closure of `Verifier.treeSpecialSoundWithEscape`.

  **No consumer, by design.** Before the named escape appends, this form was the right-factor
  hypothesis of every escape composition theorem; now each of those takes a named `E₂`, so nothing
  in the library consumes it — that is the point of the redesign, not an oversight. It is kept only
  as the notion "*some* extractor works up to the escape event", for stating a lower bound on what a
  reduction achieves when the algorithm is genuinely not the subject. Do not reintroduce it as a
  composition hypothesis: forgetting the extractor there is exactly what hid every downstream link's
  extraction inside an `Exists.choose` and made the composed chain unrunnable. -/
def treeSpecialSoundEscape (S : ChallengeTreeShape pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity,
    treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The existential notion is definitionally the existential closure of the named one. -/
theorem treeSpecialSound_iff_exists (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.treeSpecialSound (WitOut := WitOut) init impl S relIn relOut ↔
      ∃ Ext, treeSpecialSoundWith init impl S relIn relOut verifier Ext := Iff.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor. -/
theorem treeSpecialSoundWith.toTreeSpecialSound {S : ChallengeTreeShape pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    verifier.treeSpecialSound init impl S relIn relOut := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor (escape-threaded). -/
theorem treeSpecialSoundWithEscape.toEscape {S : ChallengeTreeShape pSpec}
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundEscape init impl S esc relIn relOut verifier := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- At the never-firing event the escape notion is the plain notion: the escape layer is a
  conservative extension. -/
theorem treeSpecialSoundWithEscape_false_iff (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) :
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
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext :=
  fun stmtIn tree hstr hacc => Or.inr (h stmtIn tree hstr hacc)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Escape events are monotone: a certificate at `esc` holds at any weaker (larger) event. The
  extractor is never inspected. -/
theorem treeSpecialSoundWithEscape.mono {S : ChallengeTreeShape pSpec}
    {esc esc' : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    (hmono : ∀ s t, esc s t → esc' s t)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S esc' relIn relOut verifier Ext :=
  fun stmtIn tree hstr hacc => (h stmtIn tree hstr hacc).imp (hmono _ _) id

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Shape-congruence transport for named tree special soundness.** The named notion transports
  along an equality of shapes, with the extractor carried across heterogeneously. The extractor's
  type mentions `S.arity`, so a plain `rw` at the shape is motive-incorrect; `subst` at the shape
  equality homogenizes the extractor types before the single `HEq` is consumed (in practice
  `hExt := HEq.rfl`, since the relevant shape equalities — e.g. `CWSSStructure.toShape_append` —
  have definitionally equal arities). -/
theorem treeSpecialSoundWith_congr {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    {Ext' : Extractor.TreeBased StmtIn WitIn WitOut pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) :
    treeSpecialSoundWith init impl S' relIn relOut verifier Ext' := by
  subst hS
  obtain rfl := eq_of_heq hExt
  exact h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Shape-congruence transport, escape-threaded.** Both the extractor and the escape event have
  types mentioning `S.arity`; this lemma carries them across heterogeneously (in practice both
  `HEq`s are `HEq.rfl`). -/
theorem treeSpecialSoundWithEscape_congr {S S' : ChallengeTreeShape pSpec} (hS : S = S')
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {esc' : ChallengeTree.EscapeEvent StmtIn pSpec S'.arity} (hEsc : HEq esc esc')
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    {Ext' : Extractor.TreeBased StmtIn WitIn WitOut pSpec S'.arity} (hExt : HEq Ext Ext')
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) :
    treeSpecialSoundWithEscape init impl S' esc' relIn relOut verifier Ext' := by
  subst hS
  obtain rfl := eq_of_heq hEsc
  obtain rfl := eq_of_heq hExt
  exact h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The unconditioned reading of a certificate.** Closing a named certificate's extractor with the
  canonical witnessing (`ChallengeTree.canonWitnesses`) drops the validity premise entirely: on
  every structured accepting tree the recovered witness is in `relIn`.

  Needs `[Inhabited WitIn]` (to read the `Option` off) and *nothing else* — no purity hypothesis:
  validity of the canonical witnessing follows from acceptance alone. -/
theorem treeSpecialSoundWith.mem_relIn_of_isAccepting [Inhabited WitIn]
    {S : ChallengeTreeShape pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWith init impl S relIn relOut verifier Ext) (stmtIn : StmtIn)
    (tree : ChallengeTree pSpec S.arity 0) (hstr : tree.IsStructured S)
    (hacc : tree.IsAccepting init impl verifier stmtIn relOut.language) :
    (stmtIn, (Ext stmtIn tree
      (ChallengeTree.canonWitnesses init impl verifier relOut stmtIn)).getD default) ∈ relIn := by
  obtain ⟨w, hw, hrel⟩ :=
    h stmtIn tree hstr hacc _ (ChallengeTree.canonWitnesses_isValid hacc)
  simpa [hw] using hrel

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The unconditioned reading of an escape-threaded certificate**, i.e.
  `treeSpecialSoundWith.mem_relIn_of_isAccepting` for the notion the Hachi chain actually uses:
  every certificate in that chain is escape-threaded, so this — not the plain closer — is the
  statement that says nothing was lost in moving to the `∀ o valid` form.

  The escape disjunct passes through untouched, which is the point of the quantifier order (see
  `Verifier.treeSpecialSoundWithEscape`): the escape decision does not depend on the witnessing, so
  it survives closing with the canonical one.

  Note what closing does: `ChallengeTree.canonWitnesses` is
  `if h : ∃ w, … then some h.choose else none`, so this theorem plugs the choice function back in
  and recovers the *non-algorithmic* reading a pre-witnessing statement had. That is precisely why
  it is the right migration receipt — it is the old statement, derived — and not a reason to prefer
  it: for a reduction the `∀ o valid` form is the stronger and more useful statement, since it is
  what composes into a runnable end-to-end extractor. -/
theorem treeSpecialSoundWithEscape.escape_or_mem_relIn_of_isAccepting [Inhabited WitIn]
    {S : ChallengeTreeShape pSpec}
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec S.arity}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity}
    (h : treeSpecialSoundWithEscape init impl S esc relIn relOut verifier Ext) (stmtIn : StmtIn)
    (tree : ChallengeTree pSpec S.arity 0) (hstr : tree.IsStructured S)
    (hacc : tree.IsAccepting init impl verifier stmtIn relOut.language) :
    esc stmtIn tree ∨
      (stmtIn, (Ext stmtIn tree
        (ChallengeTree.canonWitnesses init impl verifier relOut stmtIn)).getD default) ∈ relIn := by
  rcases h stmtIn tree hstr hacc with hesc | hgood
  · exact Or.inl hesc
  · obtain ⟨w, hw, hrel⟩ := hgood _ (ChallengeTree.canonWitnesses_isValid hacc)
    exact Or.inr (by simpa [hw] using hrel)

end Verifier
