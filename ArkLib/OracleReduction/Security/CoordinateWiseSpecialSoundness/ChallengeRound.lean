/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SeqCompose

/-!
  # Single challenge-only-round tree navigation (generic CWSS building block)

  Generic machinery for coordinate-wise special soundness (CWSS) of any **one-round,
  challenge-only** protocol — the verifier sends a single challenge vector `Fin ℓ → C`; the
  prover sends nothing on the wire (its response is the reduction's *output witness*) — at an
  **arbitrary per-coordinate soundness parameter `k`**. It is the challenge-only, parametric-`k`
  sibling of `SingleRound.lean` (which is pinned to a message round plus `k = 2`, the folding
  shape of Hachi Lemma 8).

  The target instance is the **repaired Hachi zero-check** (Hachi [NOZ26] Lemma 10, Figure 5;
  `Commitments/Functional/Hachi/ZeroCheck/`): `ℓ = 2` scalar Kronecker seeds at
  `k = D = max(2^{m₀}, 2^{m_α})`. There, extraction consumes all `k` distinct challenge values
  of a coordinate (univariate root-counting on the Kronecker pullback), not just the one sibling
  a folding extractor subtracts. Accordingly, the star lemma exported here is
  `IsSpecialSoundFamily.exists_coord_finset`: a special-sound family attains, per coordinate, a
  `Finset` of at least `k` distinct values — the interpolation root supply.

  Main pieces (mirroring `SingleRound.lean`):

  - the one-round `pSpec` and its CWSS structure `chalStructure`
    (`ℓ` coordinates, parameter `k`, arity `ℓ·(k-1)+1`);
  - **shape recovery** (`tree_shape`): every challenge tree of this `pSpec` is a `tree1` — one
    node of sibling challenge vectors, leaves below;
  - per-branch transcripts and the pure-acceptance bridge (`branch_relOut_language`);
  - the tree extractor `treeExtractor` and the **generic assembly**
    `coordinateWiseSpecialSound_of_mkWitness`: any pure statement-extending verifier of this
    `pSpec` is CWSS for `chalStructure`, given only a protocol-specific witness assembler
    `mkWitness` turning per-branch `relOut`-witnesses at special-sound challenge families into a
    `relIn`-witness.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree

namespace CoordinateWise

/-- **Per-coordinate root supply of a special-sound family**: a family in `SS(S, ℓ, k)` attains,
in every coordinate `i`, at least `k` pairwise-distinct values — the center's value together with
the `k-1` siblings' values at `i` (all distinct: siblings agree with the center off `i`, so
injectivity of the family separates them at `i`). This is the extraction input of the repaired
Hachi Lemma 10: with Kronecker-curve challenges, the values of coordinate `i` are `k` distinct
roots of a univariate pullback of degree `< k`. -/
theorem IsSpecialSoundFamily.exists_coord_finset {S : Type*} {ℓ k : ℕ}
    {c : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → S)}
    (hfam : IsSpecialSoundFamily ℓ k c) (i : Fin ℓ) :
    ∃ s : Finset S, k ≤ s.card ∧ ∀ τ ∈ s, ∃ j, c j i = τ := by
  letI : DecidableEq S := Classical.decEq S
  obtain ⟨hinj, e, h⟩ := hfam
  obtain ⟨J, heJ, hcard, hJ⟩ := h i
  refine ⟨insert (c e i) (J.image fun j => c j i), ?_, fun τ hτ => ?_⟩
  · -- Distinctness: two siblings agreeing at `i` agree everywhere (they share the center off
    -- `i`), so injectivity of the family collapses them.
    have himg : (J.image fun j => c j i).card = J.card := by
      refine Finset.card_image_of_injOn fun j hj j' hj' hij => hinj (funext fun t => ?_)
      by_cases ht : t = i
      · subst ht; exact hij
      · rw [← (hJ j hj).2 t ht]; exact (hJ j' hj').2 t ht
    have hnot : c e i ∉ J.image fun j => c j i := by
      simp only [Finset.mem_image, not_exists, not_and]
      exact fun j hj heq => (hJ j hj).1 heq.symm
    rw [Finset.card_insert_of_notMem hnot, himg, hcard]
    omega
  · rcases Finset.mem_insert.mp hτ with h1 | h1
    · exact ⟨e, h1.symm⟩
    · obtain ⟨j, _, hje⟩ := Finset.mem_image.mp h1
      exact ⟨j, hje⟩

namespace ChallengeRound

/-- The one-round, challenge-only protocol (instantiated by the repaired Hachi zero-check,
Lemma 10 / Figure 5): the verifier sends a challenge vector `Fin ℓ → C` (round 0, `V_to_P`).
The prover's answer is the reduction's output witness, never sent on the wire. -/
@[reducible] def pSpec (C : Type) (ℓ : ℕ) : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin ℓ → C]⟩

variable {C : Type} {ℓ : ℕ} {arity : (pSpec C ℓ).ChallengeIdx → ℕ}

/-! ## Round reader, the star tree, and shape recovery

Naive `match tree` on a `ChallengeTree … 0` fails ("dependent elimination failed"), so — as in
`SingleRound.lean` — the reader is index-generic: it matches at an arbitrary round index `a` and
carries the proof `a = 0`. -/

/-- Index-generic round-0 reader: peel the sibling-challenge family off a `chalNode` at any
index `a` together with a proof `a = 0`. -/
def chalsAux : {a : Fin 2} → ChallengeTree (pSpec C ℓ) arity a → a = (0 : Fin 2) →
    (Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
  | _, .leaf, ha => by simp at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 0 := Subsingleton.elim m 0
      exact absurd h Direction.noConfusion
  | _, .chalNode m _ chals _, ha => by
      obtain rfl : m = 0 := Subsingleton.elim m 0
      exact chals

/-- Read the sibling-challenge family off a full tree. -/
def readChallenges (tree : ChallengeTree (pSpec C ℓ) arity 0) :
    Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩ :=
  chalsAux tree rfl

/-- The star tree: one challenge node carrying the sibling family, leaves below. Every tree of
this `pSpec` has this shape (`tree_shape`). -/
def tree1 (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩) :
    ChallengeTree (pSpec C ℓ) arity 0 :=
  .chalNode 0 rfl challenges (fun _ => .leaf)

/-- The reader computes on the star tree. -/
@[simp] theorem readChallenges_tree1
    (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩) :
    readChallenges (tree1 challenges) = challenges := rfl

/-- Shape recovery, level 1: every subtree at the last round is a leaf. -/
theorem eq_leaf : {a : Fin 2} → (t : ChallengeTree (pSpec C ℓ) arity a) →
    (ha : a = Fin.last 1) →
      HEq t (ChallengeTree.leaf : ChallengeTree (pSpec C ℓ) arity (Fin.last 1))
  | _, .leaf, _ => HEq.rfl
  | _, .msgNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simp)
  | _, .chalNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simp)

/-- Shape recovery, level 0: every tree at round 0 is a `tree1`. -/
theorem tree_shape_aux : {a : Fin 2} → (t : ChallengeTree (pSpec C ℓ) arity a) →
    (ha : a = 0) → ∃ challenges, HEq t (tree1 (arity := arity) challenges)
  | _, .leaf, ha => by simp at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 0 := Subsingleton.elim m 0
      exact absurd h Direction.noConfusion
  | _, .chalNode m _ chals children, ha => by
      obtain rfl : m = 0 := Subsingleton.elim m 0
      refine ⟨chals, ?_⟩
      have hch : children = fun _ => .leaf := by
        funext j
        exact eq_of_heq (eq_leaf (children j) rfl)
      rw [hch]
      exact HEq.rfl

/-- **Shape recovery.** Every full tree of the one-round `pSpec` is a star tree. -/
theorem tree_shape (tree : ChallengeTree (pSpec C ℓ) arity 0) :
    ∃ challenges, tree = tree1 (arity := arity) challenges := by
  obtain ⟨challenges, h⟩ := tree_shape_aux tree rfl
  exact ⟨challenges, eq_of_heq h⟩

/-! ## Per-branch transcripts -/

/-- The root-to-leaf path through `tree1` selecting branch `j` of the challenge node. -/
def branchPath (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
    (j : Fin (arity ⟨0, rfl⟩)) : LeafPath (tree1 challenges) :=
  .chal j .leaf

/-- The full transcript of branch `j` of the star tree: the single challenge `challenges j`. -/
def branchTr (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
    (j : Fin (arity ⟨0, rfl⟩)) : (pSpec C ℓ).FullTranscript :=
  (branchPath challenges j).fullTranscript

/-- Branch `j`'s transcript carries challenge `challenges j` at round 0. -/
theorem branch_challenge (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
    (j : Fin (arity ⟨0, rfl⟩)) :
    (branchTr challenges j).challenges ⟨0, rfl⟩ = challenges j := by
  simp only [branchTr, branchPath, LeafPath.fullTranscript, LeafPath.transcript,
    FullTranscript.challenges, Transcript.concat]
  simp [Fin.snoc]

/-- Branch `j`'s transcript is one of the star tree's leaf transcripts. -/
theorem branch_mem (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
    (j : Fin (arity ⟨0, rfl⟩)) :
    branchTr challenges j ∈ (tree1 challenges).fullTranscripts :=
  LeafPath.mem_fullTranscripts _

/-! ## The CWSS structure -/

variable (C ℓ) in
/-- The challenge-only CWSS structure at coordinate count `ℓ` and soundness parameter `k`: the
single challenge round decomposes by the identity into `ℓ` coordinates over `C`, with branching
arity `ℓ·(k-1)+1`. The repaired Hachi zero-check instantiates `ℓ = 2` (the two Kronecker seeds)
and `k = D = max(2^{m₀}, 2^{m_α})` — Lemma 10's corrected parameter, **not** the paper's
`max(2d, 2b-1)`. -/
def chalStructure (k : ℕ) (hℓ : 0 < ℓ) (hk : 2 ≤ k) : CWSSStructure (pSpec C ℓ) where
  coordIndex := fun _ => ⟨ℓ, hℓ⟩
  alphabet := fun _ => C
  decompose := fun i => Equiv.cast (by rcases i with ⟨j, hj⟩; fin_cases j; rfl)
  soundnessParam := fun _ => ⟨k, hk⟩
  arity := fun _ => ℓ * (k - 1) + 1
  arity_eq := rfl

/-- The node predicate of `chalStructure` is exactly the `SS(C, ℓ, k)` condition on the sibling
family. -/
theorem nodeOk_iff_family {k : ℕ} {hℓ : 0 < ℓ} {hk : 2 ≤ k}
    (challenges : Fin ((chalStructure C ℓ k hℓ hk).arity ⟨0, rfl⟩) →
      (pSpec C ℓ).Challenge ⟨0, rfl⟩) :
    (chalStructure C ℓ k hℓ hk).nodeOk ⟨0, rfl⟩ challenges ↔
      IsSpecialSoundFamily ℓ k challenges := by
  unfold CWSSStructure.nodeOk
  simp only [chalStructure, CWSSStructure.ell, CWSSStructure.k]
  rfl

/-! ## Pure-acceptance bridge and extractor -/

section Bridge

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type} {σ : Type}

/-- Acceptance of the star tree specializes, per branch `j`, to membership of the branch's
verifier output `mapStmt stmtIn (challenges j)` in `relOut.language` — for any pure verifier that
outputs `mapStmt` applied to the input statement and the transcript's challenge. The reshaping
`mapStmt` is the identity pair `(·, ·)` for a statement-extending verifier, but may repack the
challenge into a richer output-statement structure (the Hachi zero-check packs the two Kronecker
seeds into named fields). -/
theorem branch_relOut_language {StmtOut : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut (pSpec C ℓ))
    (mapStmt : StmtIn → (Fin ℓ → C) → StmtOut)
    (hpure : ∀ s tr, V.verify s tr = pure (mapStmt s (tr.challenges ⟨0, rfl⟩)))
    (relOut : Set (StmtOut × WitOut))
    (stmtIn : StmtIn)
    (challenges : Fin (arity ⟨0, rfl⟩) → (pSpec C ℓ).Challenge ⟨0, rfl⟩)
    (hAcc : (tree1 challenges).IsAccepting init impl V stmtIn relOut.language)
    (j : Fin (arity ⟨0, rfl⟩)) :
    (mapStmt stmtIn (challenges j)) ∈ relOut.language :=
  Verifier.mem_of_pure_accepting init impl V stmtIn (branchTr challenges j) relOut.language
    (mapStmt stmtIn (challenges j)) (by rw [hpure, branch_challenge])
    (hAcc _ (branch_mem challenges j))

end Bridge

open Classical in
/-- The tree extractor, generic over separate witness types: `relOut` relates the extended
statement to a per-branch response `WitOut`; `mkWitness` assembles the extracted input witness
`WitIn` from the `ℓ·(k-1)+1` sibling challenge vectors and one classically chosen `WitOut` per
branch (`Classical.ofNonempty` where none exists — on structured accepting trees
`branch_relOut_language` fires every guard). Hypothesis-free: all correctness is proven
downstream. -/
noncomputable def treeExtractor {k : ℕ} {StmtIn StmtOut WitOut WitIn : Type} [Nonempty WitOut]
    (hℓ : 0 < ℓ) (hk : 2 ≤ k)
    (mapStmt : StmtIn → (Fin ℓ → C) → StmtOut)
    (relOut : Set (StmtOut × WitOut))
    (mkWitness : StmtIn → (Fin (ℓ * (k - 1) + 1) → (Fin ℓ → C)) →
      (Fin (ℓ * (k - 1) + 1) → WitOut) → WitIn) :
    Extractor.TreeBased StmtIn WitIn (pSpec C ℓ) (chalStructure C ℓ k hℓ hk).arity :=
  fun stmtIn tree =>
    let fam : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → C) := readChallenges tree
    let resp : Fin (ℓ * (k - 1) + 1) → WitOut := fun j =>
      if h : ∃ w, ((mapStmt stmtIn (fam j)), w) ∈ relOut then h.choose else Classical.ofNonempty
    mkWitness stmtIn fam resp

section Assembly

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut WitIn : Type} [Nonempty WitOut]
  {σ : Type}

/-- **Generic challenge-only-round CWSS assembly.** Any pure statement-extending verifier of the
one-round `pSpec` is coordinate-wise special sound for `chalStructure`, provided a witness
assembler `mkWitness` that turns per-branch `relOut`-witnesses at special-sound challenge
families into a `relIn`-witness. This discharges all tree/extractor plumbing once; the
protocol-specific work (the repaired Hachi Lemma 10's binding-or-roots case split) lives
entirely in `hmk`. Unlike `SingleRound`, `hmk` receives the full `IsSpecialSoundFamily`
certificate — extraction at parameter `k` needs all `k` values per coordinate
(`IsSpecialSoundFamily.exists_coord_finset`), not just a star center and one sibling. -/
theorem coordinateWiseSpecialSound_of_mkWitness {k : ℕ} {StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hℓ : 0 < ℓ) (hk : 2 ≤ k)
    (V : Verifier oSpec StmtIn StmtOut (pSpec C ℓ))
    (mapStmt : StmtIn → (Fin ℓ → C) → StmtOut)
    (hpure : ∀ s tr, V.verify s tr = pure (mapStmt s (tr.challenges ⟨0, rfl⟩)))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (mkWitness : StmtIn → (Fin (ℓ * (k - 1) + 1) → (Fin ℓ → C)) →
      (Fin (ℓ * (k - 1) + 1) → WitOut) → WitIn)
    (hmk : ∀ stmtIn (fam : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → C))
      (resp : Fin (ℓ * (k - 1) + 1) → WitOut),
      (∀ j, (mapStmt stmtIn (fam j), resp j) ∈ relOut) →
      IsSpecialSoundFamily ℓ k fam →
      (stmtIn, mkWitness stmtIn fam resp) ∈ relIn) :
    V.coordinateWiseSpecialSound init impl (chalStructure C ℓ k hℓ hk) relIn relOut := by
  classical
  refine ⟨treeExtractor hℓ hk mapStmt relOut mkWitness, ?_⟩
  intro stmtIn tree hStruct hAcc
  obtain ⟨challenges, rfl⟩ := tree_shape tree
  -- each branch's guard fires: per-branch membership in `relOut.language`
  have hmem : ∀ j : Fin (ℓ * (k - 1) + 1),
      ∃ w, (mapStmt stmtIn (challenges j), w) ∈ relOut := fun j =>
    (Set.mem_language_iff relOut _).1
      (branch_relOut_language init impl V mapStmt hpure relOut stmtIn challenges hAcc j)
  -- the sibling family is special sound
  have hfam : IsSpecialSoundFamily ℓ k challenges := (nodeOk_iff_family challenges).1 hStruct.1
  -- each chosen response satisfies the relation (the extractor's guards fire)
  have hbranch : ∀ j : Fin (ℓ * (k - 1) + 1),
      (mapStmt stmtIn (challenges j),
        if h : ∃ w, (mapStmt stmtIn (challenges j), w) ∈ relOut
          then h.choose else Classical.ofNonempty) ∈ relOut := by
    intro j
    rw [dif_pos (hmem j)]
    exact (hmem j).choose_spec
  -- the extractor computes definitionally on the recovered star tree
  exact hmk stmtIn _ _ hbranch hfam

end Assembly

/-! ## The 1-round protocol instances (NOT auto-derived for `ProtocolSpec 1`) -/

section Instances

variable {C : Type} {ℓ : ℕ} [SampleableType C]

/-- Hand-written 1-round instance (not auto-derived for `ProtocolSpec 1`), generic in `C`. -/
instance : ∀ i, SampleableType ((pSpec C ℓ).Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType (Fin ℓ → C))

end Instances

end ChallengeRound

end CoordinateWise
