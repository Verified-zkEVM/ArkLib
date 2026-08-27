/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree.Basic

/-!
  # Trees of transcripts — sequential composition

  This file relates trees of transcripts across sequential composition. If the first reduction
  speaks protocol `pSpec₁` and the second `pSpec₂`, the composed reduction speaks the appended
  protocol `pSpec₁ ++ₚ pSpec₂`. The central operation `appendSplit` cuts a tree over the appended
  protocol into a *first-stage* tree over `pSpec₁` and, below each first-stage leaf, a
  *second-stage* tree over `pSpec₂` — mirroring how the two reductions run in sequence. Everything
  is proved for an *arbitrary* `ChallengeTreeShape`, so each notion's composition theorem reduces to
  checking that its shape composes like the generic one, instead of repeating the work here.

  ## Main definitions

  - `ChallengeTree.appendArity` / `ChallengeTreeShape.append` — the canonical appended arity and
    shape for `pSpec₁ ++ₚ pSpec₂`, built by routing each appended challenge index back to its left
    or right component via `ChallengeIdx.sumEquiv`.
  - `ChallengeTree.AppendSplit` / `ChallengeTree.appendSplit` — the split of a tree over
    `pSpec₁ ++ₚ pSpec₂` into a first-stage tree (`fst`) and a path-indexed family of suffix trees
    (`sndAt`).
  - `ChallengeTree.AppendSplit.gluePath` — the split undone *on paths*: a first-stage leaf path
    together with a leaf path of the suffix tree below it names one leaf path of the original tree.
    This is the only path machinery composition needs, and it runs at runtime, inside every composed
    extractor.
  - `ChallengeTree.EscapeEvent.append` — composition of two escape events
    (`ChallengeTree.EscapeEvent`) along the same split: the left event on the prefix tree, or the
    right event on some suffix tree at the left verifier's verdict on that prefix leaf.
  - `Extractor.TreeBased.append` — the composed extraction algorithm itself: the left extractor on
    the prefix tree, fed per prefix leaf with the right extractor's output on the suffix tree below
    it, at the intermediate statement the left verifier's verdict function names.

  ## Main theorems

  - `appendSplit_fst_isStructured` — the first-stage tree of a structured appended tree is itself
    structured (for `S₁`).
  - `appendSplit_sndAt_isStructured` — so is every second-stage tree hanging below a first-stage
    leaf (for `S₂`).
  - `appendSplit_fullTranscripts_append_of_mem` — recombination: gluing a first-stage leaf
    transcript onto any leaf transcript of the second-stage tree it selects gives back a leaf
    transcript of the original appended tree. This is the bridge from "extract on each stage" to
    "extract on the whole protocol".
  - `AppendSplit.fullTranscript_gluePath` — the same recombination at the level of paths: a glued
    path reads exactly the concatenation of the two transcripts. This is what lets a composed
    extractor hand each factor the leaf data belonging to that factor's own leaves.

  ## Implementation

  The mathematical split is simple: read the appended tree until the `pSpec₁` part ends, then view
  each remaining subtree as a `pSpec₂` tree. The work is in the indices: `ChallengeTree` is indexed
  by its current round, and a round of the appended protocol is propositionally — but usually not
  definitionally — the corresponding round of `pSpec₁` or `pSpec₂`.

  The design is organised around one observation. `Fin.castSucc`, `Fin.succ` and `Fin.last` are not
  constructors, so index unification never fires on them and `cases` on a tree or `LeafPath` at such
  an index stalls on an unresolvable dependent equation. `Fin.mk` *is* the sole constructor of
  `Fin`, and proofs are definitionally irrelevant. So the builders take the round as a **raw `ℕ`
  plus its bound**, never as a `Fin`: then `Fin.castSucc ⟨rv, _⟩ ≡ ⟨rv, _⟩`, `Fin.succ ⟨rv, _⟩ ≡
  ⟨rv + 1, _⟩` and `Fin.last k ≡ ⟨k, _⟩` all hold by `rfl`. Every constructor lands on its target
  index with no transport, boundary detection is a plain `dite` on `rv < m` rather than a
  dependent-motive `Fin.lastCases`, and each builder is an ordinary structurally recursive
  definition — hence *computable*, which the extraction algorithms downstream depend on
  (`CoordinateWise.CWSSPackage.append` and friends run `appendSplit` on the prefix tree).

  Two consequences worth knowing when editing this file. Only `SplitData` remains as a certificate
  type, recording the left-hand prefix with the suffix tree stored at each boundary leaf; the
  right-hand side needs no certificate, since `embedRight`/`unembedRight` convert directly between a
  `pSpec₂` tree and an appended tree already past the boundary, with `embedRight_unembedRight` as
  the round trip. And when proving anything by recursion here, hoist the induction hypothesis with a
  `have` *before* any `obtain rfl`/`subst` on a tree index: `subst` reverts and reintroduces the
  child, severing it from the termination argument, and the recursion then fails to elaborate.

  The reducible helpers `rightRound` and `leftRound` make the appended round indices line up by
  computation, leaving only the expected casts for directions, message/challenge types, and arities;
  those casts are supplied by the named transport lemmas at the top of the `AppendSplit` section.

  ## Limitation

  Composition is binary and sequential (a single append `pSpec₁ ++ₚ pSpec₂`); `n`-ary composition
  is obtained by iterating.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

namespace ChallengeTree

section AppendShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Canonical arity for a challenge tree over an appended protocol. -/
def appendArity (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → ℕ :=
  Sum.elim arity₁ arity₂ ∘ ChallengeIdx.sumEquiv.symm

end AppendShape

end ChallengeTree

namespace ChallengeTreeShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Append two protocol-generic tree shapes along sequential protocol append. -/
def append (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂) :
    ChallengeTreeShape (pSpec₁ ++ₚ pSpec₂) where
  arity := ChallengeTree.appendArity S₁.arity S₂.arity
  nodeOk := fun i challenges =>
    match h : ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ =>
        S₁.nodeOk i₁ fun j =>
          cast (by
            have hi : i = ChallengeIdx.inl i₁ := by
              have hi' : i = ChallengeIdx.sumEquiv (Sum.inl i₁) :=
                (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
              simpa [ChallengeIdx.sumEquiv_apply] using hi'
            subst i
            simp [ProtocolSpec.append, ChallengeIdx.inl])
            (challenges (Fin.cast (by simp [ChallengeTree.appendArity, h]) j))
    | Sum.inr i₂ =>
        S₂.nodeOk i₂ fun j =>
          cast (by
            have hi : i = ChallengeIdx.inr i₂ := by
              have hi' : i = ChallengeIdx.sumEquiv (Sum.inr i₂) :=
                (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
              simpa [ChallengeIdx.sumEquiv_apply] using hi'
            subst i
            simp [ProtocolSpec.append, ChallengeIdx.inr])
            (challenges (Fin.cast (by simp [ChallengeTree.appendArity, h]) j))

end ChallengeTreeShape

namespace ChallengeTree

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section AppendSplit

variable {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- Embed a right-protocol round `r : Fin (n+1)` into the appended protocol's rounds.
Reducible so that `(Fin.natAdd m i).castSucc` and `(Fin.natAdd m i).succ` reduce on the nose to
the indices `ChallengeTree` constructors produce. -/
@[reducible] def rightRound (r : Fin (n + 1)) : Fin (m + n + 1) := Fin.natAdd m r

/-- Embed a left-protocol round `r : Fin (m+1)` into the appended protocol's rounds. Written as an
explicit `Fin.mk` (defeq to `Fin.castLE`) so that `(leftRound r).val` reduces to `r.val` by
projection — important for `simp`/`Fin.snoc` lemmas in the membership proof. -/
@[reducible] def leftRound (r : Fin (m + 1)) : Fin (m + n + 1) :=
  ⟨r.val, Nat.lt_of_lt_of_le r.isLt (by omega)⟩

/-! ### Transport across the protocol append

The appended protocol agrees with its factors on directions and message/challenge types once the
round index is routed through `Fin.castAdd`/`Fin.natAdd`. These named lemmas supply the casts that
the constructors below need; keeping them named (rather than inlining `simpa`) is what makes the
builders readable. -/

/-- A right-hand round of the appended protocol has `pSpec₂`'s direction. -/
theorem appendDir_right (i : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = pSpec₂.dir i := by
  simp [Fin.vappend_eq_append, Fin.append_right]

/-- A right-hand round of the appended protocol has `pSpec₂`'s type. -/
theorem appendType_right (i : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m i) = pSpec₂.«Type» i := by
  simp [Fin.vappend_eq_append, Fin.append_right]

/-- A left-hand round of the appended protocol has `pSpec₁`'s direction. -/
theorem appendDir_left (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = pSpec₁.dir i := by
  simp [Fin.vappend_eq_append, Fin.append_left]

/-- A left-hand round of the appended protocol has `pSpec₁`'s type. -/
theorem appendType_left (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n i) = pSpec₁.«Type» i := by
  simp [Fin.vappend_eq_append, Fin.append_left]

/-- The appended arity at a right-hand challenge round is `arity₂`'s. -/
theorem appendArity_right {i : Fin n} {h : pSpec₂.dir i = .V_to_P}
    (hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P) :
    appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ := by
  rw [show (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
      = ChallengeIdx.inr ⟨i, h⟩ from by ext; rfl]
  simpa [appendArity] using congrArg (Sum.elim arity₁ arity₂)
    (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)

/-- The appended arity at a left-hand challenge round is `arity₁`'s. -/
theorem appendArity_left {i : Fin m} {h : pSpec₁.dir i = .V_to_P}
    (hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P) :
    appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := by
  rw [show (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
      = ChallengeIdx.inl ⟨i, h⟩ from by ext; rfl]
  simpa [appendArity] using congrArg (Sum.elim arity₁ arity₂)
    (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)

/-! ### The right-hand side of the split

Past the boundary an appended tree *is* a `pSpec₂` tree, up to index transport. `embedRight` and
`unembedRight` witness that in both directions and `embedRight_unembedRight` is the round trip, so
the right-hand side needs no certificate type at all. -/

/-- Embed a `pSpec₂`-tree as the tail of a tree over the appended protocol. -/
def embedRight : {r : Fin (n + 1)} → ChallengeTree pSpec₂ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)
  | _, .leaf => .leaf
  | _, .msgNode i h msg child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .P_to_V :=
        (appendDir_right i).trans h
      .msgNode (Fin.natAdd m i) hApp (cast (appendType_right i).symm msg) (embedRight child)
  | _, .chalNode i h chals children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P :=
        (appendDir_right i).trans h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ :=
        appendArity_right hApp
      .chalNode (Fin.natAdd m i) hApp
        (fun j => cast (appendType_right i).symm (chals (Fin.cast hAr j)))
        (fun j => embedRight (children (Fin.cast hAr j)))

/-- Index bookkeeping: the successor of a right-hand round, as a raw-`ℕ` round equation. -/
theorem rightSucc {i : Fin (m + n)} {rv : ℕ} (hv : (i : ℕ) = m + rv) (hlt : rv + 1 < n + 1) :
    i.succ = rightRound ⟨rv + 1, hlt⟩ :=
  Fin.ext (by simp only [Fin.val_succ, rightRound, Fin.val_natAdd]; omega)

/-- Read a `pSpec₂`-tree off an appended tree that has already entered the right protocol.

The round is passed as a raw `ℕ` (`rv`) plus its bound, so the index equations of the
`ChallengeTree` constructors hold definitionally and no `Fin.lastCases` motive, `▸` or `convert` is
needed — see this file's `## Implementation`. -/
def unembedRight : {a : Fin (m + n + 1)} →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a →
    (rv : ℕ) → (hlt : rv < n + 1) → a = rightRound ⟨rv, hlt⟩ →
    ChallengeTree pSpec₂ arity₂ ⟨rv, hlt⟩
  | _, .leaf, rv, hlt, h => by
      obtain rfl : rv = n := by
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, rightRound, Fin.val_natAdd] at hv; omega
      exact .leaf
  | _, .msgNode i hd msg child, rv, hlt, h =>
      have hv : (i : ℕ) = m + rv := by
        have hv := congrArg Fin.val h; simpa [rightRound] using hv
      have hrn : rv < n := by have := i.isLt; omega
      have hi : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (by simpa using hv)
      have hdir : pSpec₂.dir ⟨rv, hrn⟩ = .P_to_V := by
        rw [← appendDir_right (pSpec₁ := pSpec₁), ← hi]; exact hd
      .msgNode ⟨rv, hrn⟩ hdir (cast (by subst hi; exact appendType_right _) msg)
        (unembedRight child (rv + 1) (by omega) (rightSucc hv (by omega)))
  | _, .chalNode i hd chals children, rv, hlt, h =>
      have hv : (i : ℕ) = m + rv := by
        have hv := congrArg Fin.val h; simpa [rightRound] using hv
      have hrn : rv < n := by have := i.isLt; omega
      have hi : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (by simpa using hv)
      have hdir : pSpec₂.dir ⟨rv, hrn⟩ = .V_to_P := by
        rw [← appendDir_right (pSpec₁ := pSpec₁), ← hi]; exact hd
      have hAr : appendArity arity₁ arity₂ ⟨i, hd⟩ = arity₂ ⟨⟨rv, hrn⟩, hdir⟩ := by
        subst hi; exact appendArity_right _
      .chalNode ⟨rv, hrn⟩ hdir
        (fun j => cast (by subst hi; exact appendType_right _) (chals (Fin.cast hAr.symm j)))
        (fun j => unembedRight (children (Fin.cast hAr.symm j)) (rv + 1) (by omega)
          (rightSucc hv (by omega)))

/-- `unembedRight` at a `Fin`-valued round: the form consumers use. -/
def unembedRight' {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    ChallengeTree pSpec₂ arity₂ r := unembedRight T r.val r.isLt rfl

/-- `embedRight` recovers the appended tree that `unembedRight` read.

Note the shape of the inductive branches: the induction hypothesis is hoisted by a `have` *before*
the `obtain rfl` on `i`, because `subst` would sever `child` from the termination argument. -/
theorem embedRight_unembedRight : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (rv : ℕ) → (hlt : rv < n + 1) → (h : a = rightRound ⟨rv, hlt⟩) →
    HEq (embedRight (arity₁ := arity₁) (unembedRight t rv hlt h)) t
  | _, .leaf, rv, hlt, h => by
      obtain rfl : rv = n := by
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, rightRound, Fin.val_natAdd] at hv; omega
      rfl
  | _, .msgNode i hd msg child, rv, hlt, h => by
      have hv : (i : ℕ) = m + rv := by
        have hv := congrArg Fin.val h; simpa [rightRound] using hv
      have hrn : rv < n := by have := i.isLt; omega
      have ih := embedRight_unembedRight child (rv + 1) (by omega) (rightSucc hv (by omega))
      obtain rfl : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (by simpa using hv)
      simp only [unembedRight, embedRight]
      apply heq_of_eq
      congr 1
      · simp [cast_cast]
      · exact eq_of_heq ih
  | _, .chalNode i hd chals children, rv, hlt, h => by
      have hv : (i : ℕ) = m + rv := by
        have hv := congrArg Fin.val h; simpa [rightRound] using hv
      have hrn : rv < n := by have := i.isLt; omega
      have ih := fun j =>
        embedRight_unembedRight (children j) (rv + 1) (by omega) (rightSucc hv (by omega))
      obtain rfl : i = Fin.natAdd m (⟨rv, hrn⟩ : Fin n) := Fin.ext (by simpa using hv)
      simp only [unembedRight, embedRight]
      apply heq_of_eq
      congr 1
      · funext j; simp [cast_cast]
      · funext j; exact eq_of_heq (ih _)

/-- The round trip at a `Fin`-valued round. -/
theorem embedRight_unembedRight' {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    embedRight (arity₁ := arity₁) (unembedRight' T) = T :=
  eq_of_heq (embedRight_unembedRight T r.val r.isLt rfl)

/-- A split certificate for the first `m` rounds. At the boundary it stores the suffix tree itself;
before that it mirrors the appended tree's left-protocol structure. -/
inductive SplitData
    (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    Fin (m + 1) → Type where
  | boundary (t₂ : ChallengeTree pSpec₂ arity₂ (0 : Fin (n + 1))) :
      SplitData arity₁ arity₂ (Fin.last m)
  | msg (i : Fin m) (h : pSpec₁.dir i = .P_to_V) (msg : pSpec₁.Message ⟨i, h⟩)
      (child : SplitData arity₁ arity₂ i.succ) : SplitData arity₁ arity₂ i.castSucc
  | chal (i : Fin m) (h : pSpec₁.dir i = .V_to_P)
      (challenges : Fin (arity₁ ⟨i, h⟩) → pSpec₁.Challenge ⟨i, h⟩)
      (children : Fin (arity₁ ⟨i, h⟩) → SplitData arity₁ arity₂ i.succ) :
      SplitData arity₁ arity₂ i.castSucc

/-- The first-stage tree projected from a `SplitData` certificate. -/
def SplitData.fst {r : Fin (m + 1)} : SplitData arity₁ arity₂ r →
    ChallengeTree pSpec₁ arity₁ r
  | .boundary _ => .leaf
  | .msg _ h m₁ child => .msgNode _ h m₁ child.fst
  | .chal _ h challenges children => .chalNode _ h challenges fun j => (children j).fst

/-- The appended source tree represented by a `SplitData` certificate. Every constructor index
lands on the nose (`leftRound` reducible); the boundary reuses `embedRight` since
`leftRound (Fin.last m)` is defeq `rightRound 0`. -/
def SplitData.src : {r : Fin (m + 1)} → SplitData arity₁ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)
  | _, .boundary t₂ => embedRight t₂
  | _, .msg i h m₁ child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .P_to_V := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      .msgNode (Fin.castAdd n i) hApp
        (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append, Fin.append_left]) m₁)
        child.src
  | _, .chal i h challenges children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      have hIdx : (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inl ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)
      .chalNode (Fin.castAdd n i) hApp
        (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append, Fin.append_left])
          (challenges (Fin.cast hAr j)))
        (fun j => (children (Fin.cast hAr j)).src)

/-- Peel the child path from a `LeafPath` at a message node, bundled with the reconstruction
`p = .msg p'`.

Inverting a `LeafPath` at a fixed `castSucc`-indexed tree fails (the round equation `↑k = m'` is
unsolvable for `cases`), so the round and tree stay general and the cases are routed by the
hypotheses `ρ = k.castSucc` and `HEq T (.msgNode …)`. This is a plain `match` — note there is no
recursion here at all, and hence no termination obligation. -/
def peelMsgAux : {ρ : Fin (m + 1)} → {T : ChallengeTree pSpec₁ arity₁ ρ} → (p : LeafPath T) →
    (k : Fin m) → (h : pSpec₁.dir k = .P_to_V) → (msg : pSpec₁.Message ⟨k, h⟩) →
    (child : ChallengeTree pSpec₁ arity₁ k.succ) →
    ρ = k.castSucc → HEq T (ChallengeTree.msgNode k h msg child) →
    { p' : LeafPath child // HEq p (@LeafPath.msg _ _ _ k h msg child p') }
  | _, _, .leaf, k, _, _, _, hρ, _ => by
      exfalso
      have hv := congrArg Fin.val hρ
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      have := k.isLt; omega
  | _, _, @LeafPath.msg _ _ _ k' _ _ _ path, k, h, msg, child, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      injection eq_of_heq hT with _ hmsg hchild
      subst hmsg; subst hchild
      exact ⟨path, HEq.rfl⟩
  | _, _, @LeafPath.chal _ _ _ k' _ _ _ _ _, k, h, msg, child, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hT) (by simp)

/-- The child path obtained by peeling a `LeafPath` at a message node (the bundled certificate
`peelMsgAux` dropped to its underlying path). -/
def peelMsg {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    LeafPath child := (peelMsgAux p k h msg child rfl HEq.rfl).1

/-- A `LeafPath` at a message node is `.msg` of its peel. -/
theorem peelMsg_spec {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    p = @LeafPath.msg _ _ _ k h msg child (peelMsg p) :=
  eq_of_heq (peelMsgAux p k h msg child rfl HEq.rfl).2

/-- Peel the branch index and child path from a `LeafPath` at a challenge node, bundled with the
reconstruction `p = .chal j p'`. Non-recursive, like `peelMsgAux`. -/
def chalPeelAux : {ρ : Fin (m + 1)} → {T : ChallengeTree pSpec₁ arity₁ ρ} → (p : LeafPath T) →
    (k : Fin m) → (h : pSpec₁.dir k = .V_to_P) →
    (challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩) →
    (children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ) →
    ρ = k.castSucc → HEq T (ChallengeTree.chalNode k h challenges children) →
    { jp : (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) //
      HEq p (@LeafPath.chal _ _ _ k h challenges children jp.1 jp.2) }
  | _, _, .leaf, k, _, _, _, hρ, _ => by
      exfalso
      have hv := congrArg Fin.val hρ
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      have := k.isLt; omega
  | _, _, @LeafPath.msg _ _ _ k' _ _ _ _, k, h, challenges, children, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hT) (by simp)
  | _, _, @LeafPath.chal _ _ _ k' _ _ _ j path, k, h, challenges, children, hρ, hT => by
      obtain rfl : k' = k := Fin.castSucc_injective _ hρ
      injection eq_of_heq hT with _ hchal hchildren
      subst hchal; subst hchildren
      exact ⟨⟨j, path⟩, HEq.rfl⟩

/-- The branch index and child path obtained by peeling a `LeafPath` at a challenge node (the
bundled certificate `chalPeelAux` dropped to its underlying index/path pair). -/
def chalPeel {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) :=
  (chalPeelAux p k h challenges children rfl HEq.rfl).1

/-- A `LeafPath` at a challenge node is `.chal` of its peeled index and child path. -/
theorem chalPeel_spec {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    p = @LeafPath.chal _ _ _ k h challenges children (chalPeel p).1 (chalPeel p).2 :=
  eq_of_heq (chalPeelAux p k h challenges children rfl HEq.rfl).2

/-- A `LeafPath` at a leaf tree is `.leaf`. Direct `cases`/`match` fails the dependent-elimination
round equation (`m = ↑m'`), so route via `LeafPath.rec`, discharging the message/challenge branches
by the impossible round equation `Fin.last m = m'.castSucc`. -/
theorem leafPeel_spec
    (p : LeafPath (.leaf : ChallengeTree pSpec₁ arity₁ (Fin.last m))) :
    p = LeafPath.leaf :=
  eq_of_heq <|
    LeafPath.rec
      (motive := fun {ρ} {_τ} q => Fin.last m = ρ →
        HEq q (LeafPath.leaf : LeafPath (.leaf : ChallengeTree pSpec₁ arity₁ (Fin.last m))))
      (fun _ => HEq.rfl)
      (by intro m' h msg child path _ih hρ
          exfalso; have := congrArg Fin.val hρ
          simp only [Fin.val_last, Fin.val_castSucc] at this; have := m'.isLt; omega)
      (by intro m' h challenges children j path _ih hρ
          exfalso; have := congrArg Fin.val hρ
          simp only [Fin.val_last, Fin.val_castSucc] at this; have := m'.isLt; omega)
      p rfl

/-- The transcript read off a message-node path factors through the peeled child path. -/
theorem transcript_msg {k : Fin m} {h : pSpec₁.dir k = .P_to_V}
    {msg : pSpec₁.Message ⟨k, h⟩} {child : ChallengeTree pSpec₁ arity₁ k.succ}
    (path : LeafPath (.msgNode k h msg child)) (pre : Transcript k.castSucc pSpec₁) :
    path.transcript pre = (peelMsg path).transcript (pre.concat msg) := by
  conv_lhs => rw [peelMsg_spec path]
  rfl

/-- The transcript read off a challenge-node path factors through the peeled branch and child. -/
theorem transcript_chal {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (path : LeafPath (.chalNode k h challenges children)) (pre : Transcript k.castSucc pSpec₁) :
    path.transcript pre =
      (chalPeel path).2.transcript (pre.concat (challenges (chalPeel path).1)) := by
  conv_lhs => rw [chalPeel_spec path]
  rfl

/-- The second-stage suffix tree selected below a given first-stage leaf path. Following the path
down the certificate, the boundary hands back the suffix tree it stores; message and challenge nodes
recurse into the peeled child certificate. -/
def SplitData.sndAt {r : Fin (m + 1)} :
    (S : SplitData arity₁ arity₂ r) → LeafPath S.fst → ChallengeTree pSpec₂ arity₂ 0
  | .boundary t₂, _ => t₂
  | .msg _ _ _ child, path => child.sndAt (peelMsg path)
  | .chal _ _ _ children, path => (children (chalPeel path).1).sndAt (chalPeel path).2

/-- Index bookkeeping: the successor of a left-hand round, as a raw-`ℕ` round equation. -/
theorem leftSucc {i : Fin (m + n)} {rv : ℕ} (hv : (i : ℕ) = rv) (hlt : rv + 1 < m + 1) :
    i.succ = leftRound ⟨rv + 1, hlt⟩ :=
  Fin.ext (by simp only [Fin.val_succ]; omega)

/-- At the boundary round (`a` is round `m` of the appended protocol) the tree has already entered
the right protocol, so `unembedRight` reads it off directly. Kept as a named definition so that the
three boundary branches of `splitOf` share one proof obligation, and so elaboration can infer
`pSpec₁`/`arity₁` from the argument's type. -/
def boundaryOf {a : Fin (m + n + 1)}
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a)
    (hb : (a : ℕ) = m) : SplitData arity₁ arity₂ (Fin.last m) :=
  .boundary (unembedRight t 0 (by omega) (Fin.ext (by simp [rightRound]; omega)))

/-- Build the split certificate for an appended tree at left round `rv`.

Boundary detection is a plain `dite` on `rv < m` — no `Fin.lastCases` motive — and every
constructor lands on its index without transport, because the round travels as a raw `ℕ`. -/
def splitOf : {a : Fin (m + n + 1)} →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a →
    (rv : ℕ) → (hlt : rv < m + 1) → a = leftRound ⟨rv, hlt⟩ → SplitData arity₁ arity₂ ⟨rv, hlt⟩
  | _, .leaf, rv, hlt, h => by
      have hv : m + n = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      obtain rfl : rv = m := by omega
      exact boundaryOf .leaf (by simp only [Fin.val_last]; omega)
  | _, .msgNode i hd msg child, rv, hlt, h =>
      have hv : (i : ℕ) = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      if hrm : rv < m then
        have hi : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (by simpa using hv)
        have hdir : pSpec₁.dir ⟨rv, hrm⟩ = .P_to_V := by
          rw [← appendDir_left (pSpec₂ := pSpec₂), ← hi]; exact hd
        .msg ⟨rv, hrm⟩ hdir (cast (by subst hi; exact appendType_left _) msg)
          (splitOf child (rv + 1) (by omega) (leftSucc hv (by omega)))
      else by
        obtain rfl : rv = m := by omega
        exact boundaryOf (.msgNode i hd msg child) (by simp only [Fin.val_castSucc]; omega)
  | _, .chalNode i hd chals children, rv, hlt, h =>
      have hv : (i : ℕ) = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      if hrm : rv < m then
        have hi : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (by simpa using hv)
        have hdir : pSpec₁.dir ⟨rv, hrm⟩ = .V_to_P := by
          rw [← appendDir_left (pSpec₂ := pSpec₂), ← hi]; exact hd
        have hAr : appendArity arity₁ arity₂ ⟨i, hd⟩ = arity₁ ⟨⟨rv, hrm⟩, hdir⟩ := by
          subst hi; exact appendArity_left _
        .chal ⟨rv, hrm⟩ hdir
          (fun j => cast (by subst hi; exact appendType_left _) (chals (Fin.cast hAr.symm j)))
          (fun j => splitOf (children (Fin.cast hAr.symm j)) (rv + 1) (by omega)
            (leftSucc hv (by omega)))
      else by
        obtain rfl : rv = m := by omega
        exact boundaryOf (.chalNode i hd chals children)
          (by simp only [Fin.val_castSucc]; omega)

/-- Build a `SplitData` certificate from an appended tree. -/
def splitDataOfTree {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    SplitData arity₁ arity₂ r := splitOf T r.val r.isLt rfl

/-- `splitOf` is faithful: reassembling its certificate returns the tree it was built from. All
three boundary branches reduce to the single `embedRight`/`unembedRight` round trip — the payoff of
splitting the two builders apart. As in `embedRight_unembedRight`, the induction hypothesis is
hoisted before `obtain rfl` so that the recursion still elaborates. -/
theorem src_splitOf : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (rv : ℕ) → (hlt : rv < m + 1) → (h : a = leftRound ⟨rv, hlt⟩) →
    HEq (splitOf t rv hlt h).src t
  | _, .leaf, rv, hlt, h => by
      have hv : m + n = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      obtain rfl : rv = m := by omega
      simp only [splitOf, boundaryOf, SplitData.src]
      exact embedRight_unembedRight _ 0 _ _
  | _, .msgNode i hd msg child, rv, hlt, h => by
      have hv : (i : ℕ) = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      by_cases hrm : rv < m
      · have ih := src_splitOf child (rv + 1) (by omega) (leftSucc hv (by omega))
        obtain rfl : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (by simpa using hv)
        simp only [splitOf, dif_pos hrm, SplitData.src]
        apply heq_of_eq
        congr 1
        · simp [cast_cast]
        · exact eq_of_heq ih
      · obtain rfl : rv = m := by omega
        simp only [splitOf, dif_neg hrm, boundaryOf, SplitData.src]
        exact embedRight_unembedRight _ 0 _ _
  | _, .chalNode i hd chals children, rv, hlt, h => by
      have hv : (i : ℕ) = rv := by
        have hv := congrArg Fin.val h; simpa [leftRound] using hv
      by_cases hrm : rv < m
      · have ih := fun j => src_splitOf (children j) (rv + 1) (by omega) (leftSucc hv (by omega))
        obtain rfl : i = Fin.castAdd n (⟨rv, hrm⟩ : Fin m) := Fin.ext (by simpa using hv)
        simp only [splitOf, dif_pos hrm, SplitData.src]
        apply heq_of_eq
        congr 1
        · funext j; simp [cast_cast]
        · funext j; exact eq_of_heq (ih _)
      · obtain rfl : rv = m := by omega
        simp only [splitOf, dif_neg hrm, boundaryOf, SplitData.src]
        exact embedRight_unembedRight _ 0 _ _

/-- The `SplitData` certificate built from an appended tree faithfully represents it. -/
theorem splitDataOfTree_src {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    (splitDataOfTree (arity₁ := arity₁) (arity₂ := arity₂) T).src = T :=
  eq_of_heq (src_splitOf T r.val r.isLt rfl)

/-- The source law for a split rooted at the beginning of an appended protocol. -/
theorem splitDataOfTree_src_zero
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) :
    (splitDataOfTree (r := 0) T).src = T :=
  @splitDataOfTree_src m n pSpec₁ pSpec₂ arity₁ arity₂ (0 : Fin (m + 1)) T

section Structure

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

/-- If a `pSpec₂`-tree embeds into a structured appended tree then it is itself structured.
The message case is a direct `exact`, since `embedRight`'s constructor indices are definitionally
the ones `IsStructured` expects. -/
theorem embedRight_isStructured :
    {r : Fin (n + 1)} → (t : ChallengeTree pSpec₂ S₂.arity r) →
    (embedRight (arity₁ := S₁.arity) t).IsStructured (S₁.append S₂) → t.IsStructured S₂
  | _, .leaf, _ => trivial
  | _, .msgNode i h m₂ child, hR => by
      simp only [embedRight, ChallengeTree.IsStructured] at hR
      exact embedRight_isStructured child hR
  | _, .chalNode i h chals children, hR => by
      simp only [embedRight, ChallengeTree.IsStructured] at hR
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P :=
        (appendDir_right i).trans h
      refine ⟨?_, fun j => embedRight_isStructured (children j) (hR.2 (Fin.cast
        (appendArity_right (arity₁ := S₁.arity) (h := h) hApp).symm j))⟩
      -- `hsymm` is quantified over the dir proof so `simp` rewrites the `match` scrutinee
      -- regardless of which (proof-irrelevant) proof term `embedRight` inlined.
      have hsymm : ∀ (P : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P),
          ChallengeIdx.sumEquiv.symm (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
            = Sum.inr ⟨i, h⟩ := fun P => by
        rw [show (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) = ChallengeIdx.inr ⟨i, h⟩
          from by ext; rfl, ChallengeIdx.sumEquiv_symm_inr]
      have hR1 := hR.1
      simp only [ChallengeTreeShape.append] at hR1
      split at hR1
      · rename_i i₁ heqs; exact absurd (heqs.symm.trans (hsymm _)) (by simp)
      · rename_i i₂ heqs
        obtain rfl : i₂ = ⟨i, h⟩ := Sum.inr.inj (heqs.symm.trans (hsymm _))
        convert hR1 using 2
        simp [cast_cast]

/-- If the appended source tree of a `SplitData` is structured then so is its first-stage tree. -/
theorem SplitData.fst_isStructured :
    {r : Fin (m + 1)} → (S : SplitData S₁.arity S₂.arity r) →
    S.src.IsStructured (S₁.append S₂) → S.fst.IsStructured S₁
  | _, .boundary _, _ => trivial
  | _, .msg i h m₁ child, hS => by
      have hround : (Fin.castAdd n i).succ = leftRound i.succ := by
        apply Fin.ext
        rfl
      simp only [SplitData.src, ChallengeTree.IsStructured] at hS
      apply SplitData.fst_isStructured child
      exact hS
  | _, .chal i h chals children, hS => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      have hIdx : (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inl ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity S₁.arity S₂.arity ⟨Fin.castAdd n i, hApp⟩ = S₁.arity ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim S₁.arity S₂.arity)
            (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)
      have hS' := hS
      simp only [SplitData.src, ChallengeTree.IsStructured] at hS'
      refine ⟨?_, fun j => SplitData.fst_isStructured (children j) (hS'.2 (Fin.cast hAr.symm j))⟩
      have hsymm : ∀ (P : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P),
          ChallengeIdx.sumEquiv.symm (⟨Fin.castAdd n i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
            = Sum.inl ⟨i, h⟩ := fun P => by
        rw [show (⟨Fin.castAdd n i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) = ChallengeIdx.inl ⟨i, h⟩
          from by ext; rfl, ChallengeIdx.sumEquiv_symm_inl]
      have hS1 := hS'.1
      simp only [ChallengeTreeShape.append] at hS1
      split at hS1
      · rename_i i₁ heqs
        obtain rfl : i₁ = ⟨i, h⟩ := Sum.inl.inj (heqs.symm.trans (hsymm _))
        convert hS1 using 2
        simp [cast_cast]
      · rename_i i₂ heqs; exact absurd (heqs.symm.trans (hsymm _)) (by simp)

/-- The suffix tree selected by any first-stage path of a structured `SplitData` is structured. -/
theorem SplitData.sndAt_isStructured :
    {r : Fin (m + 1)} → (S : SplitData S₁.arity S₂.arity r) →
    S.src.IsStructured (S₁.append S₂) → (path : LeafPath S.fst) →
    (S.sndAt path).IsStructured S₂
  | _, .boundary t₂, hS, _ => embedRight_isStructured t₂ hS
  | _, .msg i h m₁ child, hS, path => by
      have hround : (Fin.castAdd n i).succ = leftRound i.succ := by
        apply Fin.ext
        rfl
      simp only [SplitData.src, ChallengeTree.IsStructured] at hS
      have hS' : child.src.IsStructured (S₁.append S₂) := by
        exact hS
      exact SplitData.sndAt_isStructured child hS' (peelMsg path)
  | _, .chal i h chals children, hS, path => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      have hIdx : (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inl ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity S₁.arity S₂.arity ⟨Fin.castAdd n i, hApp⟩ = S₁.arity ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim S₁.arity S₂.arity)
            (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)
      have hS' := hS
      simp only [SplitData.src, ChallengeTree.IsStructured] at hS'
      exact SplitData.sndAt_isStructured (children (chalPeel path).1)
        (hS'.2 (Fin.cast hAr.symm (chalPeel path).1)) (chalPeel path).2

end Structure

/-- A split of a challenge tree over an appended protocol into a first-stage tree and a suffix tree
below every first-stage leaf. -/
structure AppendSplit
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) where
  /-- The projected first-stage tree. -/
  fst : ChallengeTree pSpec₁ arity₁ 0
  /-- The second-stage suffix tree below a first-stage leaf. -/
  sndAt : LeafPath fst → ChallengeTree pSpec₂ arity₂ 0

/-- Split a tree over an appended protocol into a first-stage tree and path-indexed suffix trees. -/
def appendSplit
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) :
      AppendSplit T where
  fst := (splitDataOfTree (r := 0) T).fst
  sndAt := (splitDataOfTree (r := 0) T).sndAt

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

/-- The first-stage projection of a structured appended tree is structured. -/
theorem appendSplit_fst_isStructured
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
    (hT : T.IsStructured (S₁.append S₂)) :
      T.appendSplit.fst.IsStructured S₁ :=
  SplitData.fst_isStructured (splitDataOfTree (r := 0) T)
    ((splitDataOfTree_src_zero T).symm ▸ hT)

/-- Every suffix tree selected by a first-stage leaf of a structured appended tree is structured. -/
theorem appendSplit_sndAt_isStructured
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
    (hT : T.IsStructured (S₁.append S₂))
    (path : LeafPath T.appendSplit.fst) :
      (T.appendSplit.sndAt path).IsStructured S₂ :=
  SplitData.sndAt_isStructured (splitDataOfTree (r := 0) T)
    ((splitDataOfTree_src_zero T).symm ▸ hT) path

section Membership

/-- A low-index entry of the appended protocol's `take` lives in `pSpec₁`. -/
theorem appendTakeType_left {k : ℕ} (hk : k ≤ m + n) (i : Fin k) (hlt : i.val < m) :
    ((pSpec₁ ++ₚ pSpec₂).take k hk).«Type» i = pSpec₁.«Type» ⟨i.val, hlt⟩ := by
  simp only [ProtocolSpec.take, Fin.take_apply, Fin.vappend_eq_append]
  rw [show (Fin.castLE hk i : Fin (m + n)) = Fin.castAdd n ⟨i.val, hlt⟩ from Fin.ext rfl,
    Fin.append_left]

/-- A high-index entry of the appended protocol's `take` lives in `pSpec₂`. -/
theorem appendTakeType_right {k : ℕ} (hk : k ≤ m + n) (i : Fin k) (hge : ¬ i.val < m)
    (hb : i.val - m < n) :
    ((pSpec₁ ++ₚ pSpec₂).take k hk).«Type» i = pSpec₂.«Type» ⟨i.val - m, hb⟩ := by
  simp only [ProtocolSpec.take, Fin.take_apply, Fin.vappend_eq_append]
  rw [show (Fin.castLE hk i : Fin (m + n)) = Fin.natAdd m ⟨i.val - m, hb⟩ from
    Fin.ext (by simp; omega), Fin.append_right]

/-- Embed a left-protocol partial transcript into the appended protocol; the first `r.val ≤ m`
entries land in `pSpec₁`. -/
def leftPrefix {r : Fin (m + 1)} (pre : Transcript r pSpec₁) :
    Transcript (leftRound r) (pSpec₁ ++ₚ pSpec₂) := fun i =>
  have hlt : i.val < m := by have h1 : i.val < r.val := i.isLt; have := r.isLt; omega
  cast (by
    change (pSpec₁.take r.val r.is_le).«Type» i
       = ((pSpec₁ ++ₚ pSpec₂).take (leftRound r).val (leftRound r).is_le).«Type» i
    rw [appendTakeType_left (leftRound r).is_le i hlt]
    simp only [ProtocolSpec.take, Fin.take_apply]; congr 1) (pre i)

/-- Embed a full left transcript followed by a right-protocol partial transcript into the appended
protocol; the first `m` entries are `tr₁`, the next `r.val` are `pre₂`. -/
def rightPrefix (tr₁ : FullTranscript pSpec₁) {r : Fin (n + 1)}
    (pre₂ : Transcript r pSpec₂) : Transcript (rightRound r) (pSpec₁ ++ₚ pSpec₂) := fun i =>
  if hlt : i.val < m then
    cast (by
      change pSpec₁.«Type» ⟨i.val, hlt⟩
         = ((pSpec₁ ++ₚ pSpec₂).take (rightRound r).val (rightRound r).is_le).«Type» i
      rw [appendTakeType_left (rightRound r).is_le i hlt]) (tr₁ ⟨i.val, hlt⟩)
  else
    have hb' : i.val - m < r.val := by have h1 : i.val < m + r.val := i.isLt; omega
    cast (by
      change (pSpec₂.take r.val r.is_le).«Type» ⟨i.val - m, hb'⟩
         = ((pSpec₁ ++ₚ pSpec₂).take (rightRound r).val (rightRound r).is_le).«Type» i
      rw [appendTakeType_right (rightRound r).is_le i hlt
        (by have h1 : i.val < m + r.val := i.isLt; have := r.isLt; omega)]
      simp only [ProtocolSpec.take, Fin.take_apply]; congr 1) (pre₂ ⟨i.val - m, hb'⟩)

/-- At the right boundary (`pre₂` is a full right transcript) the embedding is literally
`tr₁ ++ₜ`. -/
theorem rightPrefix_leaf_eq_append (tr₁ : FullTranscript pSpec₁)
    (pre₂ : Transcript (Fin.last n) pSpec₂) :
    rightPrefix tr₁ pre₂ = tr₁ ++ₜ pre₂ := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [FullTranscript.append, rightPrefix]
    rw [Fin.happend_left, dif_pos (by simp)]; rfl
  · simp only [FullTranscript.append, rightPrefix]
    rw [Fin.happend_right, dif_neg (by simp)]
    refine cast_eq_iff_heq.mpr (HEq.trans ?_ (cast_heq _ _).symm)
    congr 1
    exact Fin.ext (by simp only [Fin.val_natAdd]; omega)

/-- At the left boundary the left embedding coincides with the right embedding of the empty right
transcript. -/
theorem leftPrefix_last_eq_rightPrefix_default (pre₁ : Transcript (Fin.last m) pSpec₁) :
    leftPrefix pre₁ = rightPrefix pre₁ (default : Transcript (0 : Fin (n + 1)) pSpec₂) := by
  funext j
  simp only [leftPrefix, rightPrefix]
  rw [dif_pos (by simp)]; rfl

/-- `leftPrefix` commutes with extending the prefix by one round. -/
theorem leftPrefix_concat {i : Fin m} (pre : Transcript i.castSucc pSpec₁)
    (x : pSpec₁.«Type» i) :
    leftPrefix (pre.concat x) =
      (leftPrefix pre).concat (cast (by simp only [Fin.vappend_eq_append,
        Fin.append_left]) x : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n i)) := by
  funext idx
  refine Fin.lastCases ?_ (fun j => ?_) idx
  · simp only [leftPrefix, Transcript.concat_last, Fin.val_succ]
    exact (Transcript.concat_last _ _).symm
  · simp only [leftPrefix, Transcript.concat_castSucc, Fin.val_castSucc, Fin.val_succ]
    rfl

/-- Two casts into a common type are equal as soon as their arguments are `HEq`. Lets cast-equality
goals be discharged by reasoning about the (cast-free) underlying values. -/
theorem cast_eq_cast_of_heq {α α' β : Sort _} (h1 : α = β) (h2 : α' = β) {a : α} {a' : α'}
    (h : HEq a a') : cast h1 a = cast h2 a' :=
  eq_of_heq ((cast_heq h1 a).trans (h.trans (cast_heq h2 a').symm))

/-- `rightPrefix` commutes with extending the right prefix by one round. The
`rightPrefix`/`Fin.snoc` `dite`s are split by `split_ifs`; contradictory combinations close by
`omega` (with `idx`'s bound), matching ones by `cast_eq_cast_of_heq` (stripping casts to a base
`HEq`, then
`rfl`/index `omega`). -/
theorem rightPrefix_concat (tr₁ : FullTranscript pSpec₁) {i : Fin n}
    (pre₂ : Transcript i.castSucc pSpec₂) (x : pSpec₂.«Type» i) :
    rightPrefix tr₁ (pre₂.concat x) =
      (rightPrefix tr₁ pre₂).concat (cast (by simp only [Fin.vappend_eq_append,
        Fin.append_right]) x : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m i)) := by
  funext idx
  have hidx : idx.val < m + i.val + 1 := by
    have := idx.isLt; simp only [rightRound, Fin.val_natAdd, Fin.val_succ] at this; omega
  have hi : i.val < n := i.isLt
  simp only [rightPrefix, Transcript.concat, Fin.snoc, Fin.val_castLT, Fin.val_castSucc,
    Fin.val_succ, Fin.val_natAdd]
  split_ifs <;>
    first
      | (exfalso; omega)
      | rfl
      | (apply cast_eq_cast_of_heq
         try simp only [cast_heq_iff_heq]
         first
           | rfl
           | exact HEq.rfl
           | (exact (heq_cast_iff_heq _ _ _).mpr (cast_heq _ x)))

/-- A right-suffix transcript, prefixed by a full left transcript, is a transcript of the embedded
appended tree. Induction is on the `pSpec₂`-tree itself — the right-hand side of the split carries
no certificate, so no `LeafPath` peeling is involved. -/
theorem embedRight_mem_transcripts_append :
    {r : Fin (n + 1)} → (t : ChallengeTree pSpec₂ arity₂ r) → (tr₁ : FullTranscript pSpec₁) →
    (pre₂ : Transcript r pSpec₂) → {tr₂ : FullTranscript pSpec₂} →
    tr₂ ∈ t.transcripts pre₂ →
    tr₁ ++ₜ tr₂ ∈ (embedRight (arity₁ := arity₁) t).transcripts (rightPrefix tr₁ pre₂)
  | _, .leaf, tr₁, pre₂, tr₂, htr₂ => by
      -- `rw [htr₂]` needs `FullTranscript` and `rightRound (Fin.last n)` to reduce to the
      -- same index; v4.33 keeps them apart at implicit transparency, so the rewrite is ill-typed.
      set_option backward.isDefEq.respectTransparency false in
        simp only [embedRight, transcripts, List.mem_singleton] at htr₂ ⊢
        rw [htr₂]
        exact (rightPrefix_leaf_eq_append _ _).symm
  | _, .msgNode i h m₂ child, tr₁, pre₂, tr₂, htr₂ => by
      simp only [transcripts] at htr₂
      simp only [embedRight, transcripts]
      rw [← rightPrefix_concat]
      exact embedRight_mem_transcripts_append child tr₁ (pre₂.concat m₂) htr₂
  | _, .chalNode i h chals children, tr₁, pre₂, tr₂, htr₂ => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P :=
        (appendDir_right i).trans h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ :=
        appendArity_right hApp
      simp only [transcripts, List.mem_flatMap, List.mem_finRange] at htr₂
      obtain ⟨j, _, hj⟩ := htr₂
      simp only [embedRight, transcripts, List.mem_flatMap, List.mem_finRange]
      refine ⟨Fin.cast hAr.symm j, trivial, ?_⟩
      rw [← rightPrefix_concat]
      exact embedRight_mem_transcripts_append (children j) tr₁ (pre₂.concat (chals j)) hj

/-- A first-stage path transcript, suffixed by a leaf of the right tree it selects, is a transcript
of the appended source tree. Induction on the certificate, threading the first-stage path via the
`transcript`/peel lemmas; boundary delegates to `embedRight_mem_transcripts_append`. -/
theorem SplitData.mem_transcripts_append :
    {r : Fin (m + 1)} → (S : SplitData arity₁ arity₂ r) → (pre₁ : Transcript r pSpec₁) →
    (path₁ : LeafPath S.fst) → {tr₂ : FullTranscript pSpec₂} →
    tr₂ ∈ (S.sndAt path₁).fullTranscripts →
    (path₁.transcript pre₁) ++ₜ tr₂ ∈ S.src.transcripts (leftPrefix pre₁)
  | _, .boundary t₂, pre₁, path₁, tr₂, htr₂ => by
      rw [leafPeel_spec path₁, leftPrefix_last_eq_rightPrefix_default]
      exact embedRight_mem_transcripts_append t₂ pre₁ default htr₂
  | _, .msg i h m₁ child, pre₁, path₁, tr₂, htr₂ => by
      rw [show path₁.transcript pre₁ = (peelMsg path₁).transcript (pre₁.concat m₁)
          from transcript_msg path₁ pre₁]
      simp only [SplitData.src, transcripts]
      rw [← leftPrefix_concat]
      exact SplitData.mem_transcripts_append child (pre₁.concat m₁) (peelMsg path₁) htr₂
  | _, .chal i h chals children, pre₁, path₁, tr₂, htr₂ => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := by
        rw [show (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inl ⟨i, h⟩ from by ext; rfl]
        simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)
      rw [show path₁.transcript pre₁
          = (chalPeel path₁).2.transcript (pre₁.concat (chals (chalPeel path₁).1))
          from transcript_chal path₁ pre₁]
      simp only [SplitData.src, transcripts, List.mem_flatMap, List.mem_finRange]
      refine ⟨Fin.cast hAr.symm (chalPeel path₁).1, trivial, ?_⟩
      rw [← leftPrefix_concat]
      exact SplitData.mem_transcripts_append (children (chalPeel path₁).1)
        (pre₁.concat (chals (chalPeel path₁).1)) (chalPeel path₁).2 htr₂

/-- Recombining a first-stage path with a suffix leaf gives a leaf transcript of the appended
tree. -/
theorem appendSplit_fullTranscripts_append_of_mem
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0)
    (path : LeafPath T.appendSplit.fst)
    {tr₂ : FullTranscript pSpec₂}
    (htr₂ : tr₂ ∈ (T.appendSplit.sndAt path).fullTranscripts) :
      path.fullTranscript ++ₜ tr₂ ∈ T.fullTranscripts := by
  have key := SplitData.mem_transcripts_append (splitDataOfTree (r := 0) T) default path htr₂
  rw [splitDataOfTree_src_zero] at key
  have hpre : leftPrefix (default : Transcript (0 : Fin (m + 1)) pSpec₁)
      = (default : Transcript (0 : Fin (m + n + 1)) (pSpec₁ ++ₚ pSpec₂)) := by
    funext idx; exact idx.elim0
  rw [hpre] at key
  exact key

end Membership

section LeafPathGlue

/-! ### Leaf-path glue: recombining a prefix path with a suffix path

`appendSplit` cuts a tree; sequential composition needs the inverse **on paths**. Given a
first-stage leaf path `p₁` and a leaf path `p₂` of the suffix tree hanging below it,
`AppendSplit.gluePath` returns the leaf path of the original appended tree that the two jointly
select, and `AppendSplit.fullTranscript_gluePath` identifies the transcript it reads as the
concatenation `p₁.fullTranscript ++ₜ p₂.fullTranscript`.

This is the *only* path machinery sequential composition needs, and it is needed in one direction
only: a composed extractor consults the whole tree's leaf data at glued paths, and nothing ever
**un-glues** a path. The glue therefore sits on the runtime path of every composed extraction, so —
like the builders above — it is an ordinary structural recursion rather than a transport-heavy
inverse. -/

/-- Embed a leaf path of a `pSpec₂`-tree into the `embedRight`-embedded appended tree: past the
boundary an appended tree *is* a `pSpec₂` tree, and this is that fact for paths. The branch index at
a challenge node is transported along `appendArity_right`, exactly as `embedRight` transports the
children it indexes. -/
def LeafPath.embedRight : {r : Fin (n + 1)} → {t : ChallengeTree pSpec₂ arity₂ r} →
    LeafPath t → LeafPath (ChallengeTree.embedRight (arity₁ := arity₁) t)
  | _, _, .leaf => .leaf
  | _, _, .msg p => .msg p.embedRight
  | _, .chalNode i h _ _, .chal j p =>
      .chal (Fin.cast (appendArity_right (arity₁ := arity₁) (h := h)
        ((appendDir_right i).trans h)).symm j) p.embedRight

/-- Glue a first-stage leaf path with a suffix leaf path into a leaf path of the source tree. The
recursion follows the certificate: at the boundary the suffix path is embedded
(`LeafPath.embedRight`), and message/challenge nodes rebuild the node around the glue of the peeled
child path. -/
def SplitData.gluePath : {r : Fin (m + 1)} → (S : SplitData arity₁ arity₂ r) →
    (p₁ : LeafPath S.fst) → LeafPath (S.sndAt p₁) → LeafPath S.src
  | _, .boundary _, _, p₂ => p₂.embedRight
  | _, .msg _ _ _ child, p₁, p₂ => .msg (child.gluePath (peelMsg p₁) p₂)
  | _, .chal i h _ children, p₁, p₂ =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n i, hApp⟩ = arity₁ ⟨i, h⟩ := by
        rw [show (⟨Fin.castAdd n i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
            = ChallengeIdx.inl ⟨i, h⟩ from by ext; rfl]
        simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨i, h⟩)
      .chal (Fin.cast hAr.symm (chalPeel p₁).1)
        ((children (chalPeel p₁).1).gluePath (chalPeel p₁).2 p₂)

/-- Transcript spec of the embedding: an embedded suffix path, read from a prefix consisting of a
full left transcript, produces that transcript followed by what the suffix path reads. -/
theorem LeafPath.transcript_embedRight :
    {r : Fin (n + 1)} → {t : ChallengeTree pSpec₂ arity₂ r} → (p₂ : LeafPath t) →
    (tr₁ : FullTranscript pSpec₁) → (pre₂ : Transcript r pSpec₂) →
    (p₂.embedRight (arity₁ := arity₁)).transcript (rightPrefix tr₁ pre₂)
      = tr₁ ++ₜ p₂.transcript pre₂
  | _, _, .leaf, tr₁, pre₂ => by
      simp only [LeafPath.embedRight, LeafPath.transcript]
      exact rightPrefix_leaf_eq_append _ _
  | _, _, @LeafPath.msg _ _ _ _ _ message _ path, tr₁, pre₂ => by
      simp only [LeafPath.embedRight, LeafPath.transcript]
      rw [← rightPrefix_concat]
      exact LeafPath.transcript_embedRight path tr₁ (pre₂.concat message)
  | _, _, @LeafPath.chal _ _ _ i h chals children j path, tr₁, pre₂ => by
      have ih := LeafPath.transcript_embedRight path tr₁ (pre₂.concat (chals j))
      rw [rightPrefix_concat] at ih
      simp only [LeafPath.embedRight, LeafPath.transcript]
      exact ih

/-- Transcript spec of the glue: the glued path reads the prefix path's transcript followed by the
suffix path's. The certificate-level statement behind `AppendSplit.fullTranscript_gluePath`. -/
theorem SplitData.transcript_gluePath :
    {r : Fin (m + 1)} → (S : SplitData arity₁ arity₂ r) → (pre₁ : Transcript r pSpec₁) →
    (p₁ : LeafPath S.fst) → (p₂ : LeafPath (S.sndAt p₁)) →
    (S.gluePath p₁ p₂).transcript (leftPrefix pre₁)
      = (p₁.transcript pre₁) ++ₜ p₂.fullTranscript
  | _, .boundary t₂, pre₁, p₁, p₂ => by
      rw [leafPeel_spec p₁, leftPrefix_last_eq_rightPrefix_default]
      exact LeafPath.transcript_embedRight p₂ pre₁ default
  | _, .msg i h m₁ child, pre₁, p₁, p₂ => by
      have ih := SplitData.transcript_gluePath child (pre₁.concat m₁) (peelMsg p₁) p₂
      rw [show p₁.transcript pre₁ = (peelMsg p₁).transcript (pre₁.concat m₁)
        from transcript_msg p₁ pre₁]
      simp only [SplitData.gluePath, LeafPath.transcript]
      rw [← leftPrefix_concat]
      exact ih
  | _, .chal i h chals children, pre₁, p₁, p₂ => by
      have ih := SplitData.transcript_gluePath (children (chalPeel p₁).1)
        (pre₁.concat (chals (chalPeel p₁).1)) (chalPeel p₁).2 p₂
      rw [show p₁.transcript pre₁
          = (chalPeel p₁).2.transcript (pre₁.concat (chals (chalPeel p₁).1))
        from transcript_chal p₁ pre₁]
      simp only [SplitData.gluePath, LeafPath.transcript]
      rw [← leftPrefix_concat]
      exact ih

/-- Transport a leaf path along an equality of trees. Needed once, to move the glue built over a
certificate's `src` onto the tree the certificate was read from (`splitDataOfTree_src`). -/
def LeafPath.transport {r : Fin (m + 1)} {T T' : ChallengeTree pSpec₁ arity₁ r}
    (h : T = T') (p : LeafPath T) : LeafPath T' := h ▸ p

/-- Transporting a path along an equality of trees does not change the transcript it reads. -/
theorem LeafPath.fullTranscript_transport {T T' : ChallengeTree pSpec₁ arity₁ 0}
    (h : T = T') (p : LeafPath T) :
    (p.transport h).fullTranscript = p.fullTranscript := by subst h; rfl

/-- Path-level recombination for `appendSplit`: the leaf path of `T` selected by a first-stage leaf
path together with a leaf path of the suffix tree below it. -/
def AppendSplit.gluePath
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0)
    (p₁ : LeafPath T.appendSplit.fst) (p₂ : LeafPath (T.appendSplit.sndAt p₁)) : LeafPath T :=
  ((splitDataOfTree (r := 0) T).gluePath p₁ p₂).transport
    (splitDataOfTree_src (r := 0) (arity₁ := arity₁) (arity₂ := arity₂) T)

/-- The glued path reads exactly the concatenation of the two transcripts. This is the path-level
counterpart of `appendSplit_fullTranscripts_append_of_mem`, and the lemma that carries leaf data
across the seam of a composed reduction. -/
theorem AppendSplit.fullTranscript_gluePath
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0)
    (p₁ : LeafPath T.appendSplit.fst) (p₂ : LeafPath (T.appendSplit.sndAt p₁)) :
    (AppendSplit.gluePath T p₁ p₂).fullTranscript
      = p₁.fullTranscript ++ₜ p₂.fullTranscript := by
  -- Unfolding `gluePath` exposes `T.splitDataOfTree`, whose round index is `0` here but
  -- `leftRound 0` in `splitDataOfTree`'s own signature. v4.33 keeps the two apart at implicit
  -- transparency, so the goal is not type-correct there and `rw` cannot match the transport.
  set_option backward.isDefEq.respectTransparency false in
    rw [AppendSplit.gluePath, LeafPath.fullTranscript_transport]
  have key := SplitData.transcript_gluePath (splitDataOfTree (r := 0) T) default p₁ p₂
  have hpre : leftPrefix (default : Transcript (0 : Fin (m + 1)) pSpec₁)
      = (default : Transcript (0 : Fin (m + n + 1)) (pSpec₁ ++ₚ pSpec₂)) := by
    funext idx; exact idx.elim0
  rw [hpre] at key
  exact key

end LeafPathGlue

section EscapeEventAppend

variable {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- Binary composition of escape events along a protocol append: the composed event fires iff the
left event fires on the prefix tree, or the right event fires on the suffix tree hanging off some
prefix leaf, at the intermediate statement `verify₁` computes on that leaf's transcript. Each
factor's event stays self-contained, so factors may track breaks of entirely different assumptions.

Where `verify₁` is unconstrained the composed event evaluates `esc₂` at intermediate statements no
honest execution produces — harmless, since an honest event is a break at *every* `(stmt, tree)`
pair (`ChallengeTree.EscapeEvent`). -/
def EscapeEvent.append {Stmt₁ Stmt₂ : Type}
    (esc₁ : EscapeEvent Stmt₁ pSpec₁ arity₁) (esc₂ : EscapeEvent Stmt₂ pSpec₂ arity₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
    EscapeEvent Stmt₁ (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) :=
  fun stmt tree =>
    esc₁ stmt tree.appendSplit.fst ∨
    ∃ path : LeafPath tree.appendSplit.fst,
      esc₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)

/-- Unfolding lemma for the composed escape event (definitional; for readability at composition
sites and `simp`-driven characterizations of composed chains' events). -/
theorem EscapeEvent.append_apply {Stmt₁ Stmt₂ : Type}
    (esc₁ : EscapeEvent Stmt₁ pSpec₁ arity₁) (esc₂ : EscapeEvent Stmt₂ pSpec₂ arity₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) (stmt : Stmt₁)
    (tree : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) 0) :
    esc₁.append esc₂ verify₁ stmt tree ↔
      (esc₁ stmt tree.appendSplit.fst ∨
        ∃ path : LeafPath tree.appendSplit.fst,
          esc₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)) := Iff.rfl

end EscapeEventAppend

end AppendSplit

end ChallengeTree

end ProtocolSpec

/-! ## Sequential composition of tree-based extractors -/

namespace Extractor

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- **Sequential composition of witness-only tree extractors.** Split the appended tree
(`ChallengeTree.appendSplit`) and run the left extractor on the prefix tree, feeding it — per prefix
leaf — the right extractor's output on the suffix tree hanging below that leaf. The intermediate
statement the right extractor runs at is computed by `verify₁`, the **left verifier's verdict
function**, passed as data; a package reads it off its `Verifier.PureForm` / `Verifier.GuardedForm`
field, which is exactly why those fields carry the verdict as data rather than as an existential.

The right extractor's own witnessing input is the top-level witnessing read at the glued path
(`ChallengeTree.AppendSplit.gluePath`), and that glue is the *only* path machinery a composed
extraction runs: extractors attribute no output statements, so nothing ever un-glues a path.
Declining propagates — if the top witnessing declines at some glued leaf the right extractor may
decline, hence so may the left. -/
def TreeBased.append (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ arity₁)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ arity₂) :
    TreeBased Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) (ChallengeTree.appendArity arity₁ arity₂) :=
  fun stmt tree o =>
    E₁ stmt tree.appendSplit.fst fun p₁ =>
      E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)

end Extractor
