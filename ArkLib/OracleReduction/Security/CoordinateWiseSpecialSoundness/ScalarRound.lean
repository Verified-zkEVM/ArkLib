/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
  # Scalar single-challenge-round CWSS assembly (generic building block)

  The `(ℓ = 1, k)` twin of `CoordinateWise.SingleRound` (which stays pinned to the vector-challenge
  `(ℓ, k) = (2^r, 2)` fold shape of `QuadEval`).

  Several two-round reductions are of the shape "one prover message, then one **scalar**
  challenge", with plain `k`-special soundness (`ℓ = 1`) at various `k`:

  * the DP24/Binius ring-switching batching round (`RingSwitching.pSpecBatching` is this wire
    format at `Msg := P.A`, `C := Fin κ → L`);
  * Hachi's HMZ25 quotient-evaluation ring switch ([NOZ26] Figure 4 / Lemma 9):
    message `t = Com(w̃)`, challenge `α ← F`, `k = 2d`;
  * each paired sumcheck round (Hachi Figure 6 / Lemma 11): message = round-polynomial pair,
    challenge `aᵢ ← F`, `k = max-degree + 1`.

  ## Contents

  The shared wire format `pSpecScalar`; the CWSS structure `scalarStructure k`
  (= `CWSSStructure.ofSpecialSound`, arity `1·(k−1)+1 = k`, with the bridge
  `scalarStructure_arity`); the per-round instances; the **tree readers and shape recovery**
  (`readPre`, `readChallenges`, `tree2`, `tree_shape` — the `(ℓ = 1, k)` transplant of
  `SingleRound.lean`'s, index-generic in the same way); the per-branch transcript machinery
  (`branchPath`, `branchTr`, `branch_pre`, `branch_challenge`, `branch_mem`) and the
  pure-acceptance bridge `branch_relOut_language`; the named extractor `treeExtractorScalar`; and
  the escape event `escEventScalar` induced by a local per-family event.

  Both generic assemblies are **proven**:
  `coordinateWiseSpecialSoundWith_of_mkWitness_scalar` and its escape-threaded twin
  `coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar`. Any pure statement-extending verifier
  of this shape is CWSS for `scalarStructure k` given only a witness assembler `mkWitness` that
  turns `k` per-branch `relOut`-witnesses at *pairwise-distinct* challenges into a `relIn`-witness
  (escape variant: or into a local escape event). At `ℓ = 1` the star machinery of `SingleRound`
  collapses to injectivity of the challenge family (`injective_of_nodeOk`, via
  `isSpecialSoundFamily_one_iff_injective` composed with the `Equiv.funUnique` decomposition of
  `scalarStructure`), so `hmk` receives plain `Function.Injective fam` instead of `StarAt`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise

namespace CoordinateWise.ScalarRound

/-- The two-round scalar-challenge protocol: the prover sends a message `Msg` (round 0,
`P_to_V`), the verifier replies with a single scalar challenge `C` (round 1, `V_to_P`). -/
@[reducible] def pSpecScalar (Msg C : Type) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Msg, C]⟩

variable {Msg C : Type} {arity : (pSpecScalar Msg C).ChallengeIdx → ℕ}

/-- The scalar-round CWSS structure at soundness parameter `k`: a single challenge coordinate
(`ℓ = 1`) over the alphabet `C`, i.e. plain `k`-special soundness — the shape of Hachi
Lemmas 9 and 11. Arity `1·(k−1)+1 = k`. -/
@[reducible] def scalarStructure (k : ℕ) (hk : 2 ≤ k) :
    CWSSStructure (pSpecScalar Msg C) :=
  CWSSStructure.ofSpecialSound (fun _ => k) (fun _ => hk)

/-- The scalar-round arity is `k` (propositionally — `1 * (k - 1) + 1` is not `rfl`-equal to `k`;
this is the bridge the extractor's and the escape event's `Fin.cast`s use). The `(ℓ = 1, k)`
analogue of `SingleRound.foldStructure_arity`. -/
theorem scalarStructure_arity {k : ℕ} (hk : 2 ≤ k) :
    (scalarStructure (Msg := Msg) (C := C) k hk).arity ⟨1, rfl⟩ = k :=
  show 1 * (k - 1) + 1 = k from by omega

section Instances

variable [SampleableType C] [OracleInterface Msg]

/-- Hand-written 2-round instances (not auto-derived for `ProtocolSpec 2`). -/
instance : ∀ i, SampleableType ((pSpecScalar Msg C).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType C)

/-- `OracleInterface` for each message index: round 0 carries the prover message `Msg`;
round 1 is a challenge, so it has no message. -/
instance : ∀ i, OracleInterface ((pSpecScalar Msg C).Message i)
  | ⟨0, _⟩ => (inferInstance : OracleInterface Msg)
  | ⟨1, h⟩ => nomatch h

end Instances

/-! ## Round readers

The `(ℓ = 1, k)` transplant of `SingleRound.lean`'s readers. Naive `match tree` on a
`ChallengeTree … 0` fails ("dependent elimination failed"), so each reader is index-generic: it
matches at an arbitrary round index `a` and carries the proof `a = 0` (resp. `a = 1`), discharged
per constructor via `congrArg Fin.val` + `Direction.noConfusion`. -/

/-- Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a`
together with a proof `a = 0`. -/
def topMsgAux : {a : Fin 3} → ChallengeTree (pSpecScalar Msg C) arity a → a = (0 : Fin 3) →
    (pSpecScalar Msg C).Message ⟨0, rfl⟩
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m _ msg _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact msg
  | _, .chalNode m h _ _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion

/-- Read the round-0 message (the pre-challenge prover message) off a full tree. -/
def readPre (tree : ChallengeTree (pSpecScalar Msg C) arity 0) :
    (pSpecScalar Msg C).Message ⟨0, rfl⟩ :=
  topMsgAux tree rfl

/-- Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any
index `a` together with a proof `a = 1`. -/
def chalsAux : {a : Fin 3} → ChallengeTree (pSpecScalar Msg C) arity a → a = (1 : Fin 3) →
    (Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode m h chals _, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact chals

/-- Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0
helper strips the top `msgNode` and hands its child (which sits at round 1) to `chalsAux`. -/
def readChallenges (tree : ChallengeTree (pSpecScalar Msg C) arity 0) :
    Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩ :=
  aux tree rfl
where
  /-- Round-0 helper for `readChallenges`: strip the top `msgNode`, delegate to `chalsAux`. -/
  aux : {a : Fin 3} → ChallengeTree (pSpecScalar Msg C) arity a → a = (0 : Fin 3) →
      (Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    | _, .leaf, ha => by simp [Fin.ext_iff] at ha
    | _, .msgNode m _ _ child, ha => by
        obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact chalsAux child rfl
    | _, .chalNode m h _ _, ha => by
        obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact absurd h Direction.noConfusion

/-! ## The star tree and shape recovery -/

/-- The star tree: one message node carrying `v`, one challenge node carrying the sibling
family, leaves below. Every tree of this `pSpec` has this shape (`tree_shape`). -/
def tree2 (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩) :
    ChallengeTree (pSpecScalar Msg C) arity 0 :=
  .msgNode 0 rfl v (.chalNode 1 rfl challenges (fun _ => .leaf))

/-- The round-0 reader computes on the star tree. -/
@[simp] theorem readPre_tree2 (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩) :
    readPre (tree2 v challenges) = v := rfl

/-- The round-1 reader computes on the star tree. -/
@[simp] theorem readChallenges_tree2 (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩) :
    readChallenges (tree2 v challenges) = challenges := rfl

/-- Shape recovery, level 2: every subtree at the last round is a leaf. -/
theorem eq_leaf : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) →
    (ha : a = Fin.last 2) →
      HEq t (ChallengeTree.leaf : ChallengeTree (pSpecScalar Msg C) arity (Fin.last 2))
  | _, .leaf, _ => HEq.rfl
  | _, .msgNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simpa using m.isLt.ne)
  | _, .chalNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simpa using m.isLt.ne)

/-- Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves. -/
theorem chal_shape : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) →
    (ha : a = 1) →
    ∃ challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩,
      HEq t (ChallengeTree.chalNode (pSpec := pSpecScalar Msg C) (arity := arity)
        1 rfl challenges (fun _ => .leaf))
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode m h chals children, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      refine ⟨chals, ?_⟩
      have hch : children = fun _ => .leaf := by
        funext j
        exact eq_of_heq (eq_leaf (children j) rfl)
      rw [hch]

/-- Shape recovery, level 0: every tree at round 0 is a `tree2`. -/
theorem tree_shape_aux : {a : Fin 3} → (t : ChallengeTree (pSpecScalar Msg C) arity a) →
    (ha : a = 0) →
    ∃ v challenges, HEq t (tree2 (arity := arity) v challenges)
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m h msg child, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      obtain ⟨challenges, hchild⟩ := chal_shape child rfl
      refine ⟨msg, challenges, ?_⟩
      rw [eq_of_heq hchild]
      exact HEq.rfl
  | _, .chalNode m h _ _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion

/-- **Shape recovery.** Every full tree of the two-round scalar `pSpecScalar` is a star tree —
one message node, one challenge node of `arity ⟨1, rfl⟩` siblings, leaves below. -/
theorem tree_shape (tree : ChallengeTree (pSpecScalar Msg C) arity 0) :
    ∃ v challenges, tree = tree2 (arity := arity) v challenges := by
  obtain ⟨v, challenges, h⟩ := tree_shape_aux tree rfl
  exact ⟨v, challenges, eq_of_heq h⟩

/-! ## Per-branch transcripts -/

/-- The root-to-leaf path through `tree2` selecting branch `j` of the challenge node. -/
def branchPath (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) : LeafPath (tree2 v challenges) :=
  .msg (.chal j .leaf)

/-- The full transcript of branch `j` of the star tree: message `v`, challenge
`challenges j`. -/
def branchTr (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) : (pSpecScalar Msg C).FullTranscript :=
  (branchPath v challenges j).fullTranscript

/-- Branch `j`'s transcript carries challenge `challenges j` at round 1. -/
theorem branch_challenge (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchTr v challenges j).challenges ⟨1, rfl⟩ = challenges j := by
  simp only [branchTr, branchPath, LeafPath.fullTranscript, LeafPath.transcript,
    FullTranscript.challenges, Transcript.concat]
  simp [Fin.snoc]

/-- Branch `j`'s transcript carries the shared message `v` at round 0. -/
theorem branch_pre (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchTr v challenges j).messages ⟨0, rfl⟩ = v := by
  simp only [branchTr, branchPath, LeafPath.fullTranscript, LeafPath.transcript,
    FullTranscript.messages, Transcript.concat]
  simp [Fin.snoc]

/-- Branch `j`'s transcript is one of the star tree's leaf transcripts. -/
theorem branch_mem (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    branchTr v challenges j ∈ (tree2 v challenges).fullTranscripts :=
  LeafPath.mem_fullTranscripts _

/-! ## The scalar structure's node predicate -/

/-- At `ℓ = 1` the coordinate-wise node predicate collapses to **injectivity** of the sibling
challenges (`isSpecialSoundFamily_one_iff_injective`): the `SS(C, 1, k)` condition is exactly
`k` pairwise-distinct challenge values — the shape of Hachi Lemmas 9 and 11. -/
theorem injective_of_nodeOk {k : ℕ} {hk : 2 ≤ k}
    {challenges : Fin ((scalarStructure (Msg := Msg) (C := C) k hk).arity ⟨1, rfl⟩) →
      (pSpecScalar Msg C).Challenge ⟨1, rfl⟩}
    (hOk : (scalarStructure (Msg := Msg) (C := C) k hk).nodeOk ⟨1, rfl⟩ challenges) :
    Function.Injective fun j : Fin k =>
      challenges (Fin.cast (scalarStructure_arity (Msg := Msg) (C := C) hk).symm j) := by
  have hfam : Function.Injective fun j : Fin (1 * (k - 1) + 1) =>
      (Equiv.funUnique (Fin 1) ((pSpecScalar Msg C).Challenge ⟨1, rfl⟩)).symm
        (challenges (Fin.cast
          (congrFun (scalarStructure (Msg := Msg) (C := C) k hk).arity_eq ⟨1, rfl⟩).symm j)) :=
    (isSpecialSoundFamily_one_iff_injective _).mp hOk
  have h₃ : k = 1 * (k - 1) + 1 := by omega
  intro a b hab
  have hstep : Fin.cast h₃ a = Fin.cast h₃ b := by
    apply hfam
    change (Equiv.funUnique (Fin 1) _).symm (challenges _)
        = (Equiv.funUnique (Fin 1) _).symm (challenges _)
    exact congrArg _ (by
      have ha : (Fin.cast
          (congrFun (scalarStructure (Msg := Msg) (C := C) k hk).arity_eq ⟨1, rfl⟩).symm
            (Fin.cast h₃ a))
          = Fin.cast (scalarStructure_arity (Msg := Msg) (C := C) hk).symm a := rfl
      have hb : (Fin.cast
          (congrFun (scalarStructure (Msg := Msg) (C := C) k hk).arity_eq ⟨1, rfl⟩).symm
            (Fin.cast h₃ b))
          = Fin.cast (scalarStructure_arity (Msg := Msg) (C := C) hk).symm b := rfl
      rw [ha, hb]
      exact hab)
  exact Fin.cast_injective h₃ hstep

/-! ## Pure-acceptance bridge -/

section Bridge

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type} {σ : Type}

/-- Acceptance of the star tree specializes, per branch `j`, to membership of the branch's
verifier output `(stmtIn, v, challenges j)` in `relOut.language` — for any pure verifier that
outputs the statement extended by the transcript's message and challenge. -/
theorem branch_relOut_language (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn (StmtIn × Msg × C) (pSpecScalar Msg C))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (stmtIn : StmtIn) (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (hAcc : (tree2 v challenges).IsAccepting init impl V stmtIn relOut.language)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (stmtIn, v, challenges j) ∈ relOut.language :=
  Verifier.mem_of_pure_accepting init impl V stmtIn (branchTr v challenges j) relOut.language
    (stmtIn, v, challenges j) (by rw [hpure]; rw [branch_pre, branch_challenge]; rfl)
    (hAcc _ (branch_mem v challenges j))

end Bridge

/-! ## The extractor and the escape event -/

section Extractor

variable {StmtIn WitIn WitOut : Type} [Nonempty WitOut]

/-- Read the `k` sibling scalar challenges off a full tree at the `scalarStructure k` arity,
re-indexed by `Fin k` through the arity bridge `scalarStructure_arity`. Shared by the extractor
and the escape event so that both are pinned to the *same* reading of the tree. -/
def readFam {k : ℕ} (hk : 2 ≤ k)
    (tree : ChallengeTree (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity 0) :
    Fin k → C :=
  fun j => readChallenges tree (Fin.cast (scalarStructure_arity (Msg := Msg) (C := C) hk).symm j)

open Classical in
/-- **The scalar-round tree extractor**, the `(ℓ = 1, k)` analogue of `SingleRound.treeExtractor`:
read the message and the `k` sibling scalar challenges off the tree, choose a per-branch
`relOut`-witness classically (`Classical.ofNonempty` where none exists; on structured accepting
trees every guard fires), and assemble via `mkWitness`. Hypothesis-free — all correctness lives in
the assembly below. -/
noncomputable def treeExtractorScalar {k : ℕ} (hk : 2 ≤ k)
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn) :
    Extractor.TreeBased StmtIn WitIn (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity :=
  fun stmtIn tree =>
    let v := readPre tree
    let fam : Fin k → C := readFam hk tree
    let resp : Fin k → WitOut := fun j =>
      if h : ∃ w, ((stmtIn, v, fam j), w) ∈ relOut then h.choose else Classical.ofNonempty
    mkWitness stmtIn v fam resp

/-- The scalar-round tree-level escape event induced by a **local** (per-family) event `escLocal`
and a per-branch validity predicate `valid`: the tree's own message and challenge family admit
per-branch responses that are `valid` and on which `escLocal` fires.

The `(ℓ = 1, k)` analogue of `SingleRound.escEvent`, generalized in `valid` so that rounds whose
verifier is *not* statement-extending (each sumcheck round replaces the targets rather than
appending to the statement) can still pin their responses to their own output relation — which is
what keeps the event **tight**. -/
def escEventScalarOfValid {k : ℕ} (hk : 2 ≤ k)
    (valid : StmtIn → Msg → (Fin k → C) → Fin k → WitOut → Prop)
    (escLocal : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → Prop) :
    ChallengeTree.EscapeEvent StmtIn (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity :=
  fun stmtIn tree =>
    ∃ resp : Fin k → WitOut,
      (∀ j, valid stmtIn (readPre tree) (readFam hk tree) j (resp j)) ∧
      escLocal stmtIn (readPre tree) (readFam hk tree) resp

/-- `escEventScalarOfValid` at the branch validity of a **statement-extending** round: the branch's
output statement is the input statement extended by the message and that branch's challenge, so
per-branch validity is membership in `relOut` there. Used by the HMZ25 lift. -/
def escEventScalar {k : ℕ} (hk : 2 ≤ k)
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (escLocal : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → Prop) :
    ChallengeTree.EscapeEvent StmtIn (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity :=
  escEventScalarOfValid hk (fun s v fam j w => ((s, v, fam j), w) ∈ relOut) escLocal

end Extractor

section Assembly

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} [Nonempty WitOut]
  {σ : Type}

/-- **Generic scalar-round CWSS assembly, named form.** Any pure statement-extending verifier of
the two-round scalar `pSpecScalar` is coordinate-wise special sound for `scalarStructure k` **at
the named extractor** `treeExtractorScalar`, provided a witness assembler `mkWitness` that turns
`k` per-branch `relOut`-witnesses at pairwise-distinct challenges into a `relIn`-witness.

This is the engine behind Hachi Lemma 9 (`k = 2d`, interpolation) and Lemma 11
(`k = deg + 1`, per sumcheck round): all tree/extractor plumbing is discharged here once, and the
protocol-specific work lives entirely in `hmk`. The `ℓ = 1` node predicate unfolds to injectivity
of the challenge family (`injective_of_nodeOk`), and `tree_shape` puts an arbitrary structured
accepting tree into star form so that `branch_relOut_language` can certify each branch. -/
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
    Verifier.coordinateWiseSpecialSoundWith init impl (scalarStructure k hk) relIn relOut V
      (treeExtractorScalar hk relOut mkWitness) := by
  classical
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (scalarStructure_arity (Msg := Msg) (C := C) (k := k) hk).symm
  have hmem : ∀ j : Fin k,
      ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈ relOut := by
    intro j
    have h := branch_relOut_language init impl V hpure relOut stmtIn v challenges hAcc
      (Fin.cast harity j)
    exact (Set.mem_language_iff relOut _).1 h
  have hinj := injective_of_nodeOk (Msg := Msg) (C := C) (hk := hk) hStruct.1
  have hbranch : ∀ j : Fin k,
      ((stmtIn, v, challenges (Fin.cast harity j)),
        if h : ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈ relOut
          then h.choose else Classical.ofNonempty) ∈ relOut := by
    intro j
    rw [dif_pos (hmem j)]
    exact (hmem j).choose_spec
  exact hmk stmtIn v _ _ hbranch hinj

/-- **Generic scalar-round escape-threaded CWSS assembly, named form.** The escape twin of
`coordinateWiseSpecialSoundWith_of_mkWitness_scalar`: `hmk` may conclude a local escape event
`escLocal` instead of a `relIn`-witness, and the certificate carries the induced tree-level event
`escEventScalar relOut escLocal`. This is the engine behind Hachi Lemma 9 (`k = 2d`, interpolation,
weak-binding escape) and Lemma 11 (`k = deg + 1`, per sumcheck round).

Same proof as the plain assembly up to the last step, where the disjunction is threaded: the
extractor's own chosen per-branch responses — certified `relOut`-valid by `hbranch` — witness
`escEventScalar`'s existential. -/
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
    Verifier.coordinateWiseSpecialSoundWithEscape init impl (scalarStructure k hk)
      (escEventScalar hk relOut escLocal) relIn relOut V
      (treeExtractorScalar hk relOut mkWitness) := by
  classical
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (scalarStructure_arity (Msg := Msg) (C := C) (k := k) hk).symm
  have hmem : ∀ j : Fin k,
      ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈ relOut := by
    intro j
    have h := branch_relOut_language init impl V hpure relOut stmtIn v challenges hAcc
      (Fin.cast harity j)
    exact (Set.mem_language_iff relOut _).1 h
  have hinj := injective_of_nodeOk (Msg := Msg) (C := C) (hk := hk) hStruct.1
  have hbranch : ∀ j : Fin k,
      ((stmtIn, v, challenges (Fin.cast harity j)),
        if h : ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈ relOut
          then h.choose else Classical.ofNonempty) ∈ relOut := by
    intro j
    rw [dif_pos (hmem j)]
    exact (hmem j).choose_spec
  rcases hmk stmtIn v _ _ hbranch hinj with hbad | hgood
  · exact Or.inl ⟨_, hbranch, hbad⟩
  · exact Or.inr hgood

end Assembly

/-! ## The guarded, target-replacing scalar round

The assembly above serves a verifier that is **pure** and **statement-extending**: it never
rejects, and its output is the input statement paired with the round's message and challenge. A
Hachi sumcheck round ([NOZ26] Figure 6) is neither. It *rejects* when `gᵢ(0) + gᵢ(1)` misses the
running target, and it *replaces* that target rather than appending to the statement — the two
properties are linked, since it is precisely the dropping of the old target that forces the check
out of the output relation and into a runtime guard (`Guarded.lean`).

So the engine is re-run here at an arbitrary output type `StmtOut`, with the verifier presented as
a check/output pair `(check, out)` of the input statement, the message and the challenge. The
escape event and extractor are the `…OfValid` forms, which pin per-branch responses to the
verifier's *own* output statement — that is what keeps the event tight when the output is not the
input plus data. -/

section GuardedAssembly

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type} [Nonempty WitOut]
  {σ : Type}

open Classical in
/-- The guarded scalar-round tree extractor: as `treeExtractorScalar`, but per-branch witnesses are
chosen at the verifier's own output statement `out stmtIn v (fam j)` rather than at the extended
statement. -/
noncomputable def treeExtractorScalarOfValid {k : ℕ} (hk : 2 ≤ k)
    (out : StmtIn → Msg → C → StmtOut) (relOut : Set (StmtOut × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn) :
    Extractor.TreeBased StmtIn WitIn (pSpecScalar Msg C)
      (CWSSStructure.toShape (scalarStructure (Msg := Msg) (C := C) k hk)).arity :=
  fun stmtIn tree =>
    let v := readPre tree
    let fam : Fin k → C := readFam hk tree
    let resp : Fin k → WitOut := fun j =>
      if h : ∃ w, (out stmtIn v (fam j), w) ∈ relOut then h.choose else Classical.ofNonempty
    mkWitness stmtIn v fam resp

variable (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Per-branch reading of an accepting star tree, guarded form.** Each branch of an accepting
star both *passes the guard* and lands its output statement in `relOut.language`. The first
conjunct is the new one: a branch whose check failed would make the verifier `failure` on that
branch's transcript, which no accepting tree admits
(`Verifier.not_accepting_of_verify_failure`). -/
theorem branch_guarded_relOut_language
    (V : Verifier oSpec StmtIn StmtOut (pSpecScalar Msg C))
    (check : StmtIn → Msg → C → Bool) (out : StmtIn → Msg → C → StmtOut)
    (hV : V.IsGuardedWith
      (fun s tr => check s (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩))
      (fun s tr => out s (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩)))
    (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn) (v : Msg)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpecScalar Msg C).Challenge ⟨1, rfl⟩)
    (hAcc : (tree2 v challenges).IsAccepting init impl V stmtIn relOut.language)
    (j : Fin (arity ⟨1, rfl⟩)) :
    check stmtIn v (challenges j) = true ∧
      out stmtIn v (challenges j) ∈ relOut.language := by
  have hacc := hAcc _ (branch_mem v challenges j)
  have hverify := hV stmtIn (branchTr v challenges j)
  simp only [branch_pre, branch_challenge] at hverify
  have hc : check stmtIn v (challenges j) = true := by
    by_contra hc
    exact Verifier.not_accepting_of_verify_failure init impl V stmtIn
      (branchTr v challenges j) relOut.language (by rw [hverify, if_neg hc]) hacc
  exact ⟨hc, Verifier.mem_of_pure_accepting init impl V stmtIn (branchTr v challenges j)
    relOut.language _ (by rw [hverify, if_pos hc]) hacc⟩

/-- **Generic guarded scalar-round escape-threaded CWSS assembly, named form.** The guarded,
target-replacing twin of `coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar`: the verifier
is given by a check/output pair rather than assumed pure and statement-extending, and `hmk`
receives the extra premise that **every branch passed the guard** — the formal content of the
paper's "valid transcripts" premise, and exactly what a sumcheck round needs in order to read
`gᵢ(0) + gᵢ(1) = targetᵢ₋₁` off an accepting tree ([NOZ26] Lemma 11).

All tree plumbing is discharged here once; the protocol-specific work lives entirely in `hmk`. -/
theorem coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded
    {k : ℕ} (hk : 2 ≤ k)
    (V : Verifier oSpec StmtIn StmtOut (pSpecScalar Msg C))
    (check : StmtIn → Msg → C → Bool) (out : StmtIn → Msg → C → StmtOut)
    (hV : V.IsGuardedWith
      (fun s tr => check s (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩))
      (fun s tr => out s (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩)))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn)
    (escLocal : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → Prop)
    (hmk : ∀ s v (fam : Fin k → C) (resp : Fin k → WitOut),
      (∀ j, check s v (fam j) = true) →
      (∀ j, (out s v (fam j), resp j) ∈ relOut) → Function.Injective fam →
      escLocal s v fam resp ∨ (s, mkWitness s v fam resp) ∈ relIn) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl (scalarStructure k hk)
      (escEventScalarOfValid hk (fun s v fam j w => (out s v (fam j), w) ∈ relOut) escLocal)
      relIn relOut V (treeExtractorScalarOfValid hk out relOut mkWitness) := by
  classical
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (scalarStructure_arity (Msg := Msg) (C := C) (k := k) hk).symm
  have hbranch := fun j : Fin k =>
    branch_guarded_relOut_language init impl V check out hV relOut stmtIn v challenges hAcc
      (Fin.cast harity j)
  have hmem : ∀ j : Fin k,
      ∃ w, (out stmtIn v (challenges (Fin.cast harity j)), w) ∈ relOut :=
    fun j => (Set.mem_language_iff relOut _).1 (hbranch j).2
  have hinj := injective_of_nodeOk (Msg := Msg) (C := C) (hk := hk) hStruct.1
  have hresp : ∀ j : Fin k,
      ((out stmtIn v (challenges (Fin.cast harity j))),
        if h : ∃ w, (out stmtIn v (challenges (Fin.cast harity j)), w) ∈ relOut
          then h.choose else Classical.ofNonempty) ∈ relOut := by
    intro j
    rw [dif_pos (hmem j)]
    exact (hmem j).choose_spec
  rcases hmk stmtIn v _ _ (fun j => (hbranch j).1) hresp hinj with hbad | hgood
  · exact Or.inl ⟨_, hresp, hbad⟩
  · exact Or.inr hgood

end GuardedAssembly

end CoordinateWise.ScalarRound
