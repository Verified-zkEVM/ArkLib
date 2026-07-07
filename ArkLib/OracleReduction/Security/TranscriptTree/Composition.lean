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

  ## Main theorems

  - `appendSplit_fst_isStructured` — the first-stage tree of a structured appended tree is itself
    structured (for `S₁`).
  - `appendSplit_sndAt_isStructured` — so is every second-stage tree hanging below a first-stage
    leaf (for `S₂`).
  - `appendSplit_fullTranscripts_append_of_mem` — recombination: gluing a first-stage leaf
    transcript onto any leaf transcript of the second-stage tree it selects gives back a leaf
    transcript of the original appended tree. This is the bridge from "extract on each stage" to
    "extract on the whole protocol".

  ## Implementation

  The mathematical split is simple: read the appended tree until the `pSpec₁` part ends, then view
  each remaining subtree as a `pSpec₂` tree. The Lean implementation is longer because
  `ChallengeTree` is indexed by its current round `Fin (n + 1)`. A round of the appended protocol is
  propositionally, but usually not definitionally, the same as the corresponding round of
  `pSpec₁` or `pSpec₂`, so directly doing `cases` on a tree or `LeafPath` can leave Lean with an
  unresolvable dependent index equation.

  To make the split visible to Lean, the file uses small certificate types. `RightProj` certifies
  that an appended subtree is already in the right-hand protocol, and `SplitData` certifies the
  left-hand prefix together with a `RightProj` at every boundary leaf. Each certificate has a `src`
  function reconstructing the original appended tree, so the auxiliary builders always return both
  the certificate and the proof that this reconstruction is faithful.

  Most of the technical code is then just dependent bookkeeping. The builders and `LeafPath`
  peelers (`peelMsg`, `chalPeel`) recurse with the round and tree still general, only specializing
  after matching the actual constructor; this is the usual convoy pattern. Bundling the
  reconstruction equation into the same recursion ensures that the proof obligations mention
  concrete constructors rather than an opaque recursive call. The reducible helpers `rightRound`
  and `leftRound` make the appended round indices line up by computation, leaving only the expected
  casts for directions, message/challenge types, and arities.

  ## Limitation

  Composition is binary and sequential (a single append `pSpec₁ ++ₚ pSpec₂`); `n`-ary composition
  is obtained by iterating.
-/

noncomputable section

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

/-- An appended subtree that is already in the right protocol, as an internal certificate indexed
by the right-protocol round. -/
inductive RightProj
    (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    Fin (n + 1) → Type where
  | leaf : RightProj arity₁ arity₂ (Fin.last n)
  | msg (i : Fin n) (h : pSpec₂.dir i = .P_to_V) (msg : pSpec₂.Message ⟨i, h⟩)
      (child : RightProj arity₁ arity₂ i.succ) : RightProj arity₁ arity₂ i.castSucc
  | chal (i : Fin n) (h : pSpec₂.dir i = .V_to_P)
      (challenges : Fin (arity₂ ⟨i, h⟩) → pSpec₂.Challenge ⟨i, h⟩)
      (children : Fin (arity₂ ⟨i, h⟩) → RightProj arity₁ arity₂ i.succ) :
      RightProj arity₁ arity₂ i.castSucc

/-- The right-protocol tree represented by a `RightProj` certificate. -/
def RightProj.tree : {r : Fin (n + 1)} → RightProj arity₁ arity₂ r →
    ChallengeTree pSpec₂ arity₂ r
  | _, .leaf => .leaf
  | _, .msg _ h m₂ child => .msgNode _ h m₂ child.tree
  | _, .chal _ h challenges children => .chalNode _ h challenges fun j => (children j).tree

/-- The appended source tree represented by a `RightProj` certificate. Thanks to `rightRound`
being reducible, every constructor index lands on the nose; only the `dir`/`Type`/arity transports
require casts. -/
def RightProj.src : {r : Fin (n + 1)} → RightProj arity₁ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)
  | _, .leaf => .leaf
  | _, .msg i h m₂ child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .P_to_V := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      .msgNode (Fin.natAdd m i) hApp
        (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append,
          Fin.append_right]) m₂) child.src
  | _, .chal i h challenges children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      have hIdx : (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inr ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)
      .chalNode (Fin.natAdd m i) hApp
        (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append,
          Fin.append_right]) (challenges (Fin.cast hAr j)))
        (fun j => (children (Fin.cast hAr j)).src)

/-- Build a `RightProj` certificate from an appended tree, **bundled with the proof** that its
`src` recovers the original tree. Bundling is essential: the round-trip equation is discharged in
the same convoy recursion that builds the certificate, so every obligation is about a literal
constructor (the recursor-defined function never needs to be reduced under a variable index). -/
def rightProjOfTreeAux : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (r : Fin (n + 1)) → (heq : a = rightRound r) →
    { R : RightProj arity₁ arity₂ r // HEq R.src t } := fun {a} t =>
  ChallengeTree.rec
    (motive := fun a t => (r : Fin (n + 1)) → (heq : a = rightRound r) →
      { R : RightProj arity₁ arity₂ r // HEq R.src t })
    (fun r heq => by
      have hr : r = Fin.last n := by
        apply Fin.ext
        have hv := congrArg Fin.val heq
        unfold rightRound at hv
        simp only [Fin.val_last, Fin.val_natAdd] at hv ⊢
        omega
      subst hr
      exact ⟨.leaf, HEq.rfl⟩)
    (fun m' h' m₂ child ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = rightRound r) →
          { R : RightProj arity₁ arity₂ r // HEq R.src (ChallengeTree.msgNode m' h' m₂ child) })
        (fun heq => by
          exfalso
          have hv := congrArg Fin.val heq
          unfold rightRound at hv
          simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv
          have := m'.isLt; omega)
        (fun r₀ heq => by
          have hm' : m' = Fin.natAdd m r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold rightRound at hv
            simp only [Fin.val_castSucc, Fin.val_natAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₂.dir r₀ = .P_to_V := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h'
          refine ⟨.msg r₀ hdir
            (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append,
              Fin.append_right]) m₂)
            (ih r₀.succ rfl).1, ?_⟩
          have hchild : ((ih r₀.succ rfl).1).src = child := eq_of_heq (ih r₀.succ rfl).2
          apply heq_of_eq
          simp only [RightProj.src]
          rw [hchild]
          congr 1
          simp [cast_cast])
        heq)
    (fun m' h' chals children ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = rightRound r) →
          { R : RightProj arity₁ arity₂ r //
            HEq R.src (ChallengeTree.chalNode m' h' chals children) })
        (fun heq => by
          exfalso
          have hv := congrArg Fin.val heq
          unfold rightRound at hv
          simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv
          have := m'.isLt; omega)
        (fun r₀ heq => by
          have hm' : m' = Fin.natAdd m r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold rightRound at hv
            simp only [Fin.val_castSucc, Fin.val_natAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₂.dir r₀ = .V_to_P := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h'
          have hIdx : (⟨Fin.natAdd m r₀, h'⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
              = ChallengeIdx.inr ⟨r₀, hdir⟩ := by ext; rfl
          have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m r₀, h'⟩ = arity₂ ⟨r₀, hdir⟩ := by
            rw [hIdx]; simpa [appendArity] using
              congrArg (Sum.elim arity₁ arity₂)
                (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨r₀, hdir⟩)
          refine ⟨.chal r₀ hdir
            (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append,
              Fin.append_right]) (chals (Fin.cast hAr.symm j)))
            (fun j => (ih (Fin.cast hAr.symm j) r₀.succ rfl).1), ?_⟩
          apply heq_of_eq
          simp only [RightProj.src]
          congr 1
          · funext j
            simp [cast_cast]
          · funext j
            exact eq_of_heq (ih _ r₀.succ rfl).2)
        heq)
    t

/-- Build a `RightProj` certificate from an appended tree already in the right protocol. -/
def rightProjOfTree {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    RightProj arity₁ arity₂ r := (rightProjOfTreeAux T r rfl).1

/-- The `RightProj` certificate built from an appended tree faithfully represents it. -/
theorem rightProjOfTree_src {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    (rightProjOfTree (arity₁ := arity₁) (arity₂ := arity₂) T).src = T :=
  eq_of_heq (rightProjOfTreeAux T r rfl).2

/-- A split certificate for the first `m` rounds. At the boundary it stores a `RightProj` at right
round `0`; before that it mirrors the appended tree's left-protocol structure. -/
inductive SplitData
    (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    Fin (m + 1) → Type where
  | boundary (rp : RightProj arity₁ arity₂ (0 : Fin (n + 1))) :
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

/-- The appended source tree represented by a `SplitData` certificate. As with `RightProj.src`,
every constructor index lands on the nose (`leftRound` reducible); the boundary reuses
`RightProj.src` since `leftRound (Fin.last m)` is defeq `rightRound 0`. -/
def SplitData.src : {r : Fin (m + 1)} → SplitData arity₁ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)
  | _, .boundary rp => rp.src
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

/-- Peel the child path from a `LeafPath` at a message node. Inverting a `LeafPath` at a fixed
`castSucc`-indexed tree fails (the round equation `↑k = m'` is unsolvable for `cases`); instead we
recurse via `LeafPath.rec` with the round/tree free and route the cases by the hypotheses
`k.castSucc = ρ` and `HEq τ (.msgNode …)` — the same convoy trick as the `…OfTree` builders. -/
def peelMsgAux {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    { p' : LeafPath child // HEq p (@LeafPath.msg _ _ _ k h msg child p') } :=
  LeafPath.rec
    (motive := fun {ρ} {τ} q => ∀ (k : Fin m) (h : pSpec₁.dir k = .P_to_V)
      (msg : pSpec₁.Message ⟨k, h⟩) (child : ChallengeTree pSpec₁ arity₁ k.succ),
      k.castSucc = ρ → HEq τ (ChallengeTree.msgNode k h msg child) →
      { p' : LeafPath child // HEq q (@LeafPath.msg _ _ _ k h msg child p') })
    (fun k h msg child hρ _ => by
      exfalso; have := congrArg Fin.val hρ
      simp only [Fin.val_castSucc, Fin.val_last] at this; have := k.isLt; omega)
    (fun path _ k h msg child hρ hτ => by
      obtain rfl : k = _ := Fin.castSucc_injective _ hρ
      injection eq_of_heq hτ with _ hmsg hchild
      subst hmsg; subst hchild
      exact ⟨path, HEq.rfl⟩)
    (fun j path _ k h msg child hρ hτ => by
      obtain rfl : k = _ := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hτ) (by simp))
    p k h msg child rfl HEq.rfl

/-- The child path obtained by peeling a `LeafPath` at a message node (the bundled certificate
`peelMsgAux` dropped to its underlying path). -/
def peelMsg {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    LeafPath child := (peelMsgAux p).1

/-- A `LeafPath` at a message node is `.msg` of its peel. -/
theorem peelMsg_spec {k : Fin m} {h : pSpec₁.dir k = .P_to_V} {msg : pSpec₁.Message ⟨k, h⟩}
    {child : ChallengeTree pSpec₁ arity₁ k.succ} (p : LeafPath (.msgNode k h msg child)) :
    p = @LeafPath.msg _ _ _ k h msg child (peelMsg p) := eq_of_heq (peelMsgAux p).2

/-- Peel the branch index and child path from a `LeafPath` at a challenge node, bundled with the
reconstruction `p = .chal j p'`. -/
def chalPeelAux {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    { jp : (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) //
      HEq p (@LeafPath.chal _ _ _ k h challenges children jp.1 jp.2) } :=
  LeafPath.rec
    (motive := fun {ρ} {τ} q => ∀ (k : Fin m) (h : pSpec₁.dir k = .V_to_P)
      (challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩)
      (children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ),
      k.castSucc = ρ → HEq τ (ChallengeTree.chalNode k h challenges children) →
      { jp : (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) //
        HEq q (@LeafPath.chal _ _ _ k h challenges children jp.1 jp.2) })
    (fun k h challenges children hρ _ => by
      exfalso; have := congrArg Fin.val hρ
      simp only [Fin.val_castSucc, Fin.val_last] at this; have := k.isLt; omega)
    (fun path _ k h challenges children hρ hτ => by
      obtain rfl : k = _ := Fin.castSucc_injective _ hρ
      exact absurd (eq_of_heq hτ) (by simp))
    (fun j path _ k h challenges children hρ hτ => by
      obtain rfl : k = _ := Fin.castSucc_injective _ hρ
      injection eq_of_heq hτ with _ hchal hchildren
      subst hchal; subst hchildren
      exact ⟨⟨j, path⟩, HEq.rfl⟩)
    p k h challenges children rfl HEq.rfl

/-- The branch index and child path obtained by peeling a `LeafPath` at a challenge node (the
bundled certificate `chalPeelAux` dropped to its underlying index/path pair). -/
def chalPeel {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    (j : Fin (arity₁ ⟨k, h⟩)) × LeafPath (children j) := (chalPeelAux p).1

/-- A `LeafPath` at a challenge node is `.chal` of its peeled index and child path. -/
theorem chalPeel_spec {k : Fin m} {h : pSpec₁.dir k = .V_to_P}
    {challenges : Fin (arity₁ ⟨k, h⟩) → pSpec₁.Challenge ⟨k, h⟩}
    {children : Fin (arity₁ ⟨k, h⟩) → ChallengeTree pSpec₁ arity₁ k.succ}
    (p : LeafPath (.chalNode k h challenges children)) :
    p = @LeafPath.chal _ _ _ k h challenges children (chalPeel p).1 (chalPeel p).2 :=
      eq_of_heq (chalPeelAux p).2

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
down the certificate, the boundary's stored `RightProj` yields the right-protocol tree; message and
challenge nodes recurse into the peeled child certificate. -/
def SplitData.sndAt {r : Fin (m + 1)} :
    (S : SplitData arity₁ arity₂ r) → LeafPath S.fst → ChallengeTree pSpec₂ arity₂ 0
  | .boundary rp, _ => rp.tree
  | .msg _ _ _ child, path => child.sndAt (peelMsg path)
  | .chal _ _ _ children, path => (children (chalPeel path).1).sndAt (chalPeel path).2

/-- Build a `SplitData` certificate from an appended tree, bundled with the round-trip proof. The
boundary case delegates to `rightProjOfTreeAux`; `leftRound (Fin.last m)` is defeq `rightRound 0`
so the same `heq` is reused. -/
def splitDataOfTreeAux : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (r : Fin (m + 1)) → (heq : a = leftRound r) →
    { S : SplitData arity₁ arity₂ r // HEq S.src t } := fun {a} t =>
  ChallengeTree.rec
    (motive := fun a t => (r : Fin (m + 1)) → (heq : a = leftRound r) →
      { S : SplitData arity₁ arity₂ r // HEq S.src t })
    (fun r heq =>
      r.lastCases
        (motive := fun r => (heq : Fin.last (m + n) = leftRound r) →
          { S : SplitData arity₁ arity₂ r // HEq S.src ChallengeTree.leaf })
        (fun heq => ⟨.boundary (rightProjOfTreeAux .leaf 0 heq).1,
          (rightProjOfTreeAux .leaf 0 heq).2⟩)
        (fun r₀ heq => by
          exfalso
          have hv := congrArg Fin.val heq
          unfold leftRound at hv
          simp only [Fin.val_last, Fin.val_castSucc] at hv
          have := r₀.isLt; omega)
        heq)
    (fun m' h' m₁ child ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = leftRound r) →
          { S : SplitData arity₁ arity₂ r // HEq S.src (ChallengeTree.msgNode m' h' m₁ child) })
        (fun heq => ⟨.boundary (rightProjOfTreeAux (.msgNode m' h' m₁ child) 0 heq).1,
          (rightProjOfTreeAux (.msgNode m' h' m₁ child) 0 heq).2⟩)
        (fun r₀ heq => by
          have hm' : m' = Fin.castAdd n r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold leftRound at hv
            simp only [Fin.val_castSucc, Fin.val_castAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₁.dir r₀ = .P_to_V := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h'
          refine ⟨.msg r₀ hdir
            (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append, Fin.append_left]) m₁)
            (ih r₀.succ rfl).1, ?_⟩
          have hchild : ((ih r₀.succ rfl).1).src = child := eq_of_heq (ih r₀.succ rfl).2
          apply heq_of_eq
          simp only [SplitData.src]
          rw [hchild]
          congr 1
          simp [cast_cast])
        heq)
    (fun m' h' chals children ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = leftRound r) →
          { S : SplitData arity₁ arity₂ r //
            HEq S.src (ChallengeTree.chalNode m' h' chals children) })
        (fun heq => ⟨.boundary (rightProjOfTreeAux (.chalNode m' h' chals children) 0 heq).1,
          (rightProjOfTreeAux (.chalNode m' h' chals children) 0 heq).2⟩)
        (fun r₀ heq => by
          have hm' : m' = Fin.castAdd n r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold leftRound at hv
            simp only [Fin.val_castSucc, Fin.val_castAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₁.dir r₀ = .V_to_P := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using h'
          have hIdx : (⟨Fin.castAdd n r₀, h'⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
              = ChallengeIdx.inl ⟨r₀, hdir⟩ := by ext; rfl
          have hAr : appendArity arity₁ arity₂ ⟨Fin.castAdd n r₀, h'⟩ = arity₁ ⟨r₀, hdir⟩ := by
            rw [hIdx]; simpa [appendArity] using
              congrArg (Sum.elim arity₁ arity₂)
                (ChallengeIdx.sumEquiv_symm_inl (pSpec₂ := pSpec₂) ⟨r₀, hdir⟩)
          refine ⟨.chal r₀ hdir
            (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append,
              Fin.append_left]) (chals (Fin.cast hAr.symm j)))
            (fun j => (ih (Fin.cast hAr.symm j) r₀.succ rfl).1), ?_⟩
          apply heq_of_eq
          simp only [SplitData.src]
          congr 1
          · funext j
            simp [cast_cast]
          · funext j
            exact eq_of_heq (ih _ r₀.succ rfl).2)
        heq)
    t

/-- Build a `SplitData` certificate from an appended tree. -/
def splitDataOfTree {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    SplitData arity₁ arity₂ r := (splitDataOfTreeAux T r rfl).1

/-- The `SplitData` certificate built from an appended tree faithfully represents it. -/
theorem splitDataOfTree_src {r : Fin (m + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (leftRound r)) :
    (splitDataOfTree (arity₁ := arity₁) (arity₂ := arity₂) T).src = T :=
  eq_of_heq (splitDataOfTreeAux T r rfl).2

section Structure

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

/-- If the appended source tree of a `RightProj` is structured then so is its right-protocol
tree. -/
theorem RightProj.tree_isStructured :
    {r : Fin (n + 1)} → (R : RightProj S₁.arity S₂.arity r) →
    R.src.IsStructured (S₁.append S₂) → R.tree.IsStructured S₂
  | _, .leaf, _ => trivial
  | _, .msg i h m₂ child, hR =>
      RightProj.tree_isStructured child
        (by simpa [RightProj.src, ChallengeTree.IsStructured] using hR)
  | _, .chal i h chals children, hR => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      have hIdx : (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inr ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity S₁.arity S₂.arity ⟨Fin.natAdd m i, hApp⟩ = S₂.arity ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim S₁.arity S₂.arity)
            (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)
      have hR' := hR
      simp only [RightProj.src, ChallengeTree.IsStructured] at hR'
      refine ⟨?_, fun j => RightProj.tree_isStructured (children j) (hR'.2 (Fin.cast hAr.symm j))⟩
      -- `hsymm` is quantified over the dir proof so `simp` rewrites the `match` scrutinee
      -- regardless
      -- of which (proof-irrelevant) proof term `RightProj.src` inlined.
      have hsymm : ∀ (P : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P),
          ChallengeIdx.sumEquiv.symm (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
            = Sum.inr ⟨i, h⟩ := fun P => by
        rw [show (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) = ChallengeIdx.inr ⟨i, h⟩
          from by ext; rfl, ChallengeIdx.sumEquiv_symm_inr]
      have hR1 := hR'.1
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
  | _, .msg i h m₁ child, hS =>
      SplitData.fst_isStructured child
        (by simpa [SplitData.src, ChallengeTree.IsStructured] using hS)
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
  | _, .boundary rp, hS, _ =>
      rp.tree_isStructured (by simpa [SplitData.src] using hS)
  | _, .msg i h m₁ child, hS, path => by
      have hS' : child.src.IsStructured (S₁.append S₂) := by
        simpa [SplitData.src, ChallengeTree.IsStructured] using hS
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
    (by rw [splitDataOfTree_src]; exact hT)

/-- Every suffix tree selected by a first-stage leaf of a structured appended tree is structured. -/
theorem appendSplit_sndAt_isStructured
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
    (hT : T.IsStructured (S₁.append S₂))
    (path : LeafPath T.appendSplit.fst) :
      (T.appendSplit.sndAt path).IsStructured S₂ :=
  SplitData.sndAt_isStructured (splitDataOfTree (r := 0) T)
    (by rw [splitDataOfTree_src]; exact hT) path

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
  refine Fin.lastCases ?_ (fun j => ?_) idx <;>
    simp only [leftPrefix, Transcript.concat, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_castSucc,
      Fin.val_castAdd, Fin.val_succ] <;>
    exact cast_eq_iff_heq.mpr (cast_heq _ _).symm

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
           | (exact (heq_cast_iff_heq _ _ _).mpr HEq.rfl))

/-- A right-suffix transcript, prefixed by a full left transcript, is a transcript of the appended
source tree (membership form: induction on the certificate, no `LeafPath` peeling). -/
theorem RightProj.mem_transcripts_append :
    {r : Fin (n + 1)} → (R : RightProj arity₁ arity₂ r) → (tr₁ : FullTranscript pSpec₁) →
    (pre₂ : Transcript r pSpec₂) → {tr₂ : FullTranscript pSpec₂} →
    tr₂ ∈ R.tree.transcripts pre₂ → tr₁ ++ₜ tr₂ ∈ R.src.transcripts (rightPrefix tr₁ pre₂)
  | _, .leaf, tr₁, pre₂, tr₂, htr₂ => by
      simp only [RightProj.tree, RightProj.src, transcripts, List.mem_singleton] at htr₂ ⊢
      rw [htr₂]; exact (rightPrefix_leaf_eq_append _ _).symm
  | _, .msg i h m₂ child, tr₁, pre₂, tr₂, htr₂ => by
      simp only [RightProj.tree, transcripts] at htr₂
      simp only [RightProj.src, transcripts]
      rw [← rightPrefix_concat]
      exact RightProj.mem_transcripts_append child tr₁ (pre₂.concat m₂) htr₂
  | _, .chal i h chals children, tr₁, pre₂, tr₂, htr₂ => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ := by
        rw [show (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inr ⟨i, h⟩ from by ext; rfl]
        simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)
      simp only [RightProj.tree, transcripts, List.mem_flatMap, List.mem_finRange] at htr₂
      obtain ⟨j, _, hj⟩ := htr₂
      simp only [RightProj.src, transcripts, List.mem_flatMap, List.mem_finRange]
      refine ⟨Fin.cast hAr.symm j, trivial, ?_⟩
      rw [← rightPrefix_concat]
      exact RightProj.mem_transcripts_append (children j) tr₁ (pre₂.concat (chals j)) hj

/-- A first-stage path transcript, suffixed by a leaf of the right tree it selects, is a transcript
of the appended source tree. Induction on the certificate, threading the first-stage path via the
`transcript`/peel lemmas; boundary delegates to `RightProj.mem_transcripts_append`. -/
theorem SplitData.mem_transcripts_append :
    {r : Fin (m + 1)} → (S : SplitData arity₁ arity₂ r) → (pre₁ : Transcript r pSpec₁) →
    (path₁ : LeafPath S.fst) → {tr₂ : FullTranscript pSpec₂} →
    tr₂ ∈ (S.sndAt path₁).fullTranscripts →
    (path₁.transcript pre₁) ++ₜ tr₂ ∈ S.src.transcripts (leftPrefix pre₁)
  | _, .boundary rp, pre₁, path₁, tr₂, htr₂ => by
      rw [leafPeel_spec path₁, leftPrefix_last_eq_rightPrefix_default]
      exact RightProj.mem_transcripts_append rp pre₁ default htr₂
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
  rw [splitDataOfTree_src] at key
  have hpre : leftPrefix (default : Transcript (0 : Fin (m + 1)) pSpec₁)
      = (default : Transcript (0 : Fin (m + n + 1)) (pSpec₁ ++ₚ pSpec₂)) := by
    funext idx; exact idx.elim0
  rw [hpre] at key
  exact key

end Membership

end AppendSplit

end ChallengeTree

end ProtocolSpec
