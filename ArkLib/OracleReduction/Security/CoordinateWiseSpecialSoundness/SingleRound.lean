/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition

/-!
  # Single-challenge-round tree navigation (generic CWSS building block)

  Generic machinery for coordinate-wise special soundness (CWSS) of any two-round protocol —
  one prover message, then one challenge vector `Fin (2 ^ r) → C` — such as Hachi's
  polynomial-evaluation reduction (`QuadEval`, Hachi [NOZ26] Lemma 8; originally Greyhound's
  [NS24, §3.1] folding protocol).

  Main pieces:

  - the two-round `pSpec` and its CWSS structure `foldStructure`
    (`ℓ = 2 ^ r`, `k = 2`, arity `2 ^ r + 1`);
  - **shape recovery** (`tree_shape`): every challenge tree of this `pSpec` is a star `tree2` —
    one message `v`, one node of `arity` sibling challenge vectors, leaves below;
  - the **star-center machinery** (`StarAt`, `central`, `sib`, `exists_starAt`, `sib_coordEq`):
    a special-sound sibling family has a center and, per coordinate `i`, a sibling differing
    from the center exactly at `i`. Over a decidable alphabet both are found by bounded search
    (`Fin.find`), so they are computable and downstream extraction algorithms stay executable;
  - the **per-branch paths** (`branchPathOf`) and the `Option`-traverse `collect`, which together
    read the leaf witnessing at exactly the `2 ^ r + 1` branch leaves;
  - the tree extractor `treeExtractor` and the **generic assembly**
    `coordinateWiseSpecialSoundWith_of_mkWitness`: any pure statement-extending verifier of
    this `pSpec` is CWSS for `foldStructure`, given only a protocol-specific witness assembler
    `mkWitness` turning per-branch `relOut`-witnesses at star-shaped challenge families into a
    `relIn`-witness — all tree navigation, shape recovery, and guard-firing is discharged here once;
  - the **escape-threaded** twin `escEvent` /
    `coordinateWiseSpecialSoundWithEscape_of_mkWitness`, for reductions whose extraction
    may instead exhibit a cryptographic break: `hmk` concludes `escLocal … ∨ (stmtIn, mkWitness …) ∈
    relIn` and the certificate carries the induced tree-level event `escEvent relOut escLocal`
    (contract for `escLocal`: `ChallengeTree.EscapeEvent`).

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise

namespace CoordinateWise.SingleRound

/-- The two-round single-challenge-round protocol (instantiated by Hachi's `QuadEval` reduction):
the prover sends a carrier commitment `CarrierCom` (round 0, `P_to_V`), the verifier replies with
a challenge vector `Fin (2 ^ r) → C` (round 1, `V_to_P`). -/
@[reducible] def pSpec (CarrierCom C : Type) (r : ℕ) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[CarrierCom, Fin (2 ^ r) → C]⟩

variable {CarrierCom C : Type} {r : ℕ}
  {arity : (pSpec CarrierCom C r).ChallengeIdx → ℕ}

/-! ## Round readers

Naive `match tree` on a `ChallengeTree … 0` fails ("dependent elimination failed"), so each
reader is index-generic: it matches at an arbitrary round index `a` and carries the proof
`a = 0` (resp. `a = 1`), discharged per constructor via `congrArg Fin.val` +
`Direction.noConfusion`. -/

/-- Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a`
together with a proof `a = 0`. -/
def topMsgAux : {a : Fin 3} → ChallengeTree (pSpec CarrierCom C r) arity a → a = (0 : Fin 3) →
    (pSpec CarrierCom C r).Message ⟨0, rfl⟩
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m _ msg _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact msg
  | _, .chalNode m h _ _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion

/-- Read the round-0 message (the pre-challenge carrier commitment) off a full tree. -/
def readPre (tree : ChallengeTree (pSpec CarrierCom C r) arity 0) :
    (pSpec CarrierCom C r).Message ⟨0, rfl⟩ :=
  topMsgAux tree rfl

/-- Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any
index `a` together with a proof `a = 1`. The family is returned plainly typed — the child count
of the round-1 `chalNode` is definitionally `arity ⟨1, rfl⟩`. -/
def chalsAux : {a : Fin 3} → ChallengeTree (pSpec CarrierCom C r) arity a → a = (1 : Fin 3) →
    (Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
  | _, .leaf, ha => by simp [Fin.ext_iff] at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode m h chals _, ha => by
      obtain rfl : m = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact chals

/-- Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0
helper strips the top `msgNode` and hands its child (which sits at round 1) to `chalsAux`. -/
def readChallenges (tree : ChallengeTree (pSpec CarrierCom C r) arity 0) :
    Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩ :=
  aux tree rfl
where
  /-- Round-0 helper for `readChallenges`: strip the top `msgNode`, delegate to `chalsAux`. -/
  aux : {a : Fin 3} → ChallengeTree (pSpec CarrierCom C r) arity a → a = (0 : Fin 3) →
      (Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
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
def tree2 (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩) :
    ChallengeTree (pSpec CarrierCom C r) arity 0 :=
  .msgNode 0 rfl v (.chalNode 1 rfl challenges (fun _ => .leaf))

/-- The round-0 reader computes on the star tree. -/
@[simp] theorem readPre_tree2 (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩) :
    readPre (tree2 v challenges) = v := rfl

/-- The round-1 reader computes on the star tree. -/
@[simp] theorem readChallenges_tree2 (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩) :
    readChallenges (tree2 v challenges) = challenges := rfl

/-- Shape recovery, level 2: every subtree at the last round is a leaf. -/
theorem eq_leaf : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    (ha : a = Fin.last 2) →
      HEq t (ChallengeTree.leaf : ChallengeTree (pSpec CarrierCom C r) arity (Fin.last 2))
  | _, .leaf, _ => HEq.rfl
  | _, .msgNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simpa using m.isLt.ne)
  | _, .chalNode m _ _ _, ha => by
      exact absurd (congrArg Fin.val ha) (by simpa using m.isLt.ne)

/-- Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves. -/
theorem chal_shape : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    (ha : a = 1) →
    ∃ challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩,
      HEq t (ChallengeTree.chalNode (pSpec := pSpec CarrierCom C r) (arity := arity)
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
theorem tree_shape_aux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
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

/-- **Shape recovery.** Every full tree of the two-round `pSpec` is a star tree. This is the
rewrite that turns an arbitrary structured accepting tree into the synthetic `tree2` that the
branch lemmas (`branch_pre`/`branch_challenge`/`branch_mem`/`branch_relOut_language`) are
pinned to. -/
theorem tree_shape (tree : ChallengeTree (pSpec CarrierCom C r) arity 0) :
    ∃ v challenges, tree = tree2 (arity := arity) v challenges := by
  obtain ⟨v, challenges, h⟩ := tree_shape_aux tree rfl
  exact ⟨v, challenges, eq_of_heq h⟩

/-! ## Per-branch transcripts -/

/-- The root-to-leaf path through `tree2` selecting branch `j` of the challenge node. Defined
separately from `branchTr` so the path's tree index is pinned to `tree2 v challenges` (a bare
`LeafPath.msg (.chal j .leaf)` leaves the tree — hence `v`, `challenges` — undetermined). -/
def branchPath (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) : LeafPath (tree2 v challenges) :=
  .msg (.chal j .leaf)

/-- The full transcript of branch `j` of the star tree: message `v`, challenge
`challenges j`. -/
def branchTr (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) : (pSpec CarrierCom C r).FullTranscript :=
  (branchPath v challenges j).fullTranscript

/-- Branch `j`'s transcript carries challenge `challenges j` at round 1. -/
theorem branch_challenge (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchTr v challenges j).challenges ⟨1, rfl⟩ = challenges j := by
  simp only [branchTr, branchPath, LeafPath.fullTranscript, LeafPath.transcript,
    FullTranscript.challenges, Transcript.concat]
  simp [Fin.snoc]
  exact eq_of_heq (cast_heq _ _)

/-- Branch `j`'s transcript carries the shared message `v` at round 0. -/
theorem branch_pre (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchTr v challenges j).messages ⟨0, rfl⟩ = v := by
  simp only [branchTr, branchPath, LeafPath.fullTranscript, LeafPath.transcript,
    FullTranscript.messages, Transcript.concat]
  simp [Fin.snoc]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Branch `j`'s transcript is one of the star tree's leaf transcripts. -/
theorem branch_mem (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    branchTr v challenges j ∈ (tree2 v challenges).fullTranscripts :=
  LeafPath.mem_fullTranscripts _

/-! ## Per-branch paths

`branchPath` above is pinned to the synthetic `tree2`; extraction has to index the *given* tree's
leaf witnessing, so it needs the same path at an arbitrary tree. `branchPathOf` builds it by the
same index-generic peeling the round readers use, and `fullTranscript_branchPathOf` says the two
agree on a star tree — by `rfl`, since both sides compute on `tree2`'s constructors. Those are the
only two facts extraction needs about paths: the witnessing is read at `branchPathOf`-paths only,
so no inverse reader and no path classification is ever required. -/

/-- Index-generic: at the last round every tree is a leaf, so its only path is the empty one. -/
def lastPathAux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    a = Fin.last 2 → LeafPath t
  | _, .leaf, _ => .leaf
  | _, .msgNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)
  | _, .chalNode k _ _ _, ha => absurd (congrArg Fin.val ha) (by simpa using k.isLt.ne)

/-- Index-generic round-1 branch path: descend into sibling `j` of the challenge node. -/
def chalPathAux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) →
    a = (1 : Fin 3) → Fin (arity ⟨1, rfl⟩) → LeafPath t
  | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
  | _, .msgNode k h _ _, ha, _ => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact absurd h Direction.noConfusion
  | _, .chalNode k h _ children, ha, j => by
      obtain rfl : k = 1 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
      exact .chal j (lastPathAux (children j) rfl)

/-- The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the
index at which the extractor reads its leaf witnessing. -/
def branchPathOf (tree : ChallengeTree (pSpec CarrierCom C r) arity 0)
    (j : Fin (arity ⟨1, rfl⟩)) : LeafPath tree := aux tree rfl j
where
  /-- Round-0 helper for `branchPathOf`: strip the top `msgNode`, delegate to `chalPathAux`. -/
  aux : {a : Fin 3} → (t : ChallengeTree (pSpec CarrierCom C r) arity a) → a = (0 : Fin 3) →
      Fin (arity ⟨1, rfl⟩) → LeafPath t
    | _, .leaf, ha, _ => by simp [Fin.ext_iff] at ha
    | _, .msgNode k _ _ child, ha, j => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact .msg (chalPathAux child rfl j)
    | _, .chalNode k h _ _, ha, _ => by
        obtain rfl : k = 0 := Fin.ext (by have := congrArg Fin.val ha; simpa using this)
        exact absurd h Direction.noConfusion

/-- The branch path's transcript **is** the branch transcript — definitional on the star tree, since
the path builder and the readers both compute on `tree2`'s concrete constructors. -/
theorem fullTranscript_branchPathOf (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (branchPathOf (tree2 v challenges) j).fullTranscript = branchTr v challenges j := rfl

/-! ## The CWSS structure -/

/-- The single-round CWSS structure (Hachi's `QuadEval` reduction, Hachi Lemma 8): the single
challenge round carries `ℓ = 2 ^ r` coordinates over
the alphabet `C`, decomposed by the identity (`Challenge ⟨1, rfl⟩ = (Fin (2 ^ r) → C)` already),
with soundness parameter `k = 2`; hence arity `2 ^ r·(2−1)+1 = 2 ^ r + 1` and
`nodeOk = IsSpecialSoundFamily (2 ^ r) 2` — the branching of Hachi Lemma 8 / Def. 3. -/
def foldStructure : CWSSStructure (pSpec CarrierCom C r) where
  coordIndex := fun _ => ⟨2 ^ r, Nat.two_pow_pos r⟩
  alphabet := fun _ => C
  decompose := fun i => Equiv.cast (by rcases i with ⟨j, hj⟩; fin_cases j
                                       · exact (Direction.noConfusion hj : _)
                                       · rfl)
  soundnessParam := fun _ => ⟨2, le_refl 2⟩
  arity := fun _ => 2 ^ r * (2 - 1) + 1
  arity_eq := rfl

/-- The single-round arity is `2 ^ r + 1` (propositionally — `2 ^ r * (2 - 1) + 1` is not
`rfl`-equal to `2 ^ r + 1`; this is the bridge the extractor's `Fin.cast` uses). -/
theorem foldStructure_arity :
    (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).arity ⟨1, rfl⟩ = 2 ^ r + 1 := by
  simp [foldStructure]

/-- The single-round node predicate is exactly the `SS(C, 2 ^ r, 2)` condition on the sibling
family (Hachi Lemma 8 / Def. 3). -/
theorem nodeOk_iff_family
    (challenges : Fin ((foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).arity
        ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩) :
    (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).nodeOk ⟨1, rfl⟩ challenges ↔
      IsSpecialSoundFamily (2 ^ r) 2
        (fun j => (challenges (Fin.cast (by simp [foldStructure]) j))) := by
  unfold CWSSStructure.nodeOk
  simp only [foldStructure, CWSSStructure.ell, CWSSStructure.k]
  rfl

/-! ## Star-center machinery -/

/-- `e` is a star center of the sibling family: every coordinate has a sibling differing from
`challenges e` exactly there. -/
def StarAt {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C)) (e : Fin K) : Prop :=
  ∀ i, ∃ j, CoordEq i (challenges e) (challenges j)

/-- Being a star center is decidable over a decidable alphabet: two bounded quantifiers over
`CoordEq`, itself decidable (`instDecidableCoordEq`). -/
instance instDecidableStarAt [DecidableEq C] {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C))
    (e : Fin K) : Decidable (StarAt challenges e) := by unfold StarAt; infer_instance

/-- The star center of the family: the least index that is one, found by search (junk `default`
if none exists). No `IsSpecialSoundFamily` hypothesis at the definition — `exists_starAt`
supplies existence. Computable: `Fin.find` is a bounded search over the decidable `StarAt`,
which is what keeps the extractors built on it executable. -/
def central [DecidableEq C] {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C)) [Inhabited (Fin K)] :
    Fin K :=
  if h : ∃ e, StarAt challenges e then Fin.find _ h else default

/-- The coordinate-`i` sibling of the star center, found by the same bounded search. -/
def sib [DecidableEq C] {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C)) [Inhabited (Fin K)]
    (i : Fin ℓ) : Fin K :=
  if h : ∃ j, CoordEq i (challenges (central challenges)) (challenges j) then Fin.find _ h
  else default

/-- A special-sound family has a star center (promotes the family's central index; needs
`2 ≤ k` so each coordinate's sibling set is nonempty). -/
theorem exists_starAt {ℓ k K : ℕ} (hk : 2 ≤ k) (hK : K = ℓ * (k - 1) + 1)
    (challenges : Fin K → (Fin ℓ → C))
    (hfam : IsSpecialSoundFamily ℓ k (fun j => challenges (Fin.cast hK.symm j))) :
    ∃ e, StarAt challenges e := by
  obtain ⟨_, e, he⟩ := hfam; refine ⟨Fin.cast hK.symm e, fun i => ?_⟩
  obtain ⟨J, _, hJcard, hJ⟩ := he i
  obtain ⟨j, hj⟩ : J.Nonempty := by rw [← Finset.card_pos, hJcard]; omega
  exact ⟨Fin.cast hK.symm j, hJ j hj⟩

/-- The found sibling differs from the found center exactly at coordinate `i`. -/
theorem sib_coordEq [DecidableEq C] {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C))
    [Inhabited (Fin K)] (hstar : ∃ e, StarAt challenges e) (i : Fin ℓ) :
    CoordEq i (challenges (central challenges)) (challenges (sib challenges i)) := by
  have hc : StarAt challenges (central challenges) := by
    unfold central; rw [dif_pos hstar]; exact Fin.find_spec hstar
  unfold sib; rw [dif_pos (hc i)]; exact Fin.find_spec (hc i)

/-- `CoordEq` is symmetric (orientation bridge: `sib_coordEq` is oriented center-first, the
extraction's difference challenge `c̄ᵢ := c_{sib,i} − c_{central,i}` is oriented sibling-first). -/
theorem coordEq_symm {S : Type*} {ℓ : ℕ} {i : Fin ℓ} {x y : Fin ℓ → S}
    (h : CoordEq i x y) : CoordEq i y x :=
  ⟨h.1.symm, fun j hj => (h.2 j hj).symm⟩

/-- Sibling-first pointwise disagreement at coordinate `i`: with a ring-valued alphabet,
`sub_ne_zero_of_ne` turns this into `challenges (sib …) i - challenges (central …) i ≠ 0` —
the nonzeroness of the extracted difference challenge `c̄ᵢ`. -/
theorem sib_coordEq_ne [DecidableEq C] {ℓ K : ℕ} (challenges : Fin K → (Fin ℓ → C))
    [Inhabited (Fin K)] (hstar : ∃ e, StarAt challenges e) (i : Fin ℓ) :
    challenges (sib challenges i) i ≠ challenges (central challenges) i :=
  (coordEq_symm (sib_coordEq challenges hstar i)).1

/-! ## Pure-acceptance bridge and extractor -/

section Bridge

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type} {σ : Type}

/-- Acceptance of the star tree specializes, per branch `j`, to membership of the branch's
verifier output `(stmtIn, v, challenges j)` in `relOut.language` — for any pure verifier that
outputs the statement extended by the transcript's message and challenge. -/
theorem branch_relOut_language (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn (StmtIn × CarrierCom × (Fin (2 ^ r) → C)) (pSpec CarrierCom C r))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut))
    (stmtIn : StmtIn) (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (hAcc : (tree2 v challenges).IsAccepting init impl V stmtIn relOut.language)
    (j : Fin (arity ⟨1, rfl⟩)) :
    (stmtIn, v, challenges j) ∈ relOut.language :=
  Verifier.mem_of_pure_accepting init impl V stmtIn (branchTr v challenges j) relOut.language
    (stmtIn, v, challenges j) (by rw [hpure]; rw [branch_pre, branch_challenge])
    (hAcc _ (branch_mem v challenges j))

end Bridge

/-- `Option`-valued sequencing of a finite family: `some` of the pointwise values when every one of
them is present, `none` otherwise. No search, no choice, no `Fintype` — the guard is a bounded
decidable `∀` over `Fin K`. This is how the extractor consumes a leaf witnessing. -/
def collect {K : ℕ} {W : Type} (f : Fin K → Option W) : Option (Fin K → W) :=
  if h : ∀ j, (f j).isSome then some (fun j => (f j).get (h j)) else none

/-- A witnessing that answers at every branch feeds `collect`. -/
theorem collect_eq_some {K : ℕ} {W : Type} {f : Fin K → Option W} {w : Fin K → W}
    (h : ∀ j, f j = some (w j)) : collect f = some w := by
  have hs : ∀ j, (f j).isSome := fun j => by rw [h j]; rfl
  unfold collect
  rw [dif_pos hs]
  exact congrArg some (funext fun j =>
    Option.some.inj ((Option.some_get (hs j)).trans (h j)))

/-- **The single-round tree extractor**, generic over separate witness types: read the shared
message and the `2 ^ r + 1` sibling challenge vectors off the tree, `collect` the per-branch
responses off the leaf witnessing at the branch paths, and assemble via `mkWitness`. Declines
(`none`) exactly when the witnessing declines at some branch.

A bare function — no relation argument, no `[Nonempty WitOut]`, no choice: the responses are
*given*, not inverted out of `relOut`. The engine attributes no output statements either; that is
the verifier's business, and it enters the certificates below only through the notion's validity
premise. Hypothesis-free: all correctness is proven downstream. -/
def treeExtractor {StmtIn WitOut WitIn : Type}
    (mkWitness : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → WitIn) :
    Extractor.TreeBased StmtIn WitIn WitOut (pSpec CarrierCom C r)
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).arity :=
  fun stmtIn tree o =>
    (collect (fun j => o (branchPathOf tree (Fin.cast foldStructure_arity.symm j)))).map
      (mkWitness stmtIn (readPre tree)
        (fun j => readChallenges tree (Fin.cast foldStructure_arity.symm j)))

/-! ## The single-round escape event -/

/-- The tree-level escape event induced by a **local** (per-star) event `escLocal`: the tree's own
message and challenge family admit per-branch `relOut`-responses on which `escLocal` fires. The
responses are existentially quantified but pinned to the tree's actual data through the round
readers (`readPre` / `readChallenges`), so the event is `(stmtIn, tree)`-determined and tight, as
`ChallengeTree.EscapeEvent`'s contract asks. Its honesty is exactly the honesty of `escLocal` —
the protocol's obligation. -/
def escEvent {StmtIn WitOut : Type}
    (relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut))
    (escLocal : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → Prop) :
    ChallengeTree.EscapeEvent StmtIn (pSpec CarrierCom C r)
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)).arity :=
  fun stmtIn tree =>
    ∃ resp : Fin (2 ^ r + 1) → WitOut,
      (∀ j, ((stmtIn, readPre tree,
          readChallenges tree (Fin.cast foldStructure_arity.symm j)), resp j) ∈ relOut) ∧
      escLocal stmtIn (readPre tree)
        (fun j => readChallenges tree (Fin.cast foldStructure_arity.symm j)) resp

section Assembly

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut WitIn : Type} {σ : Type}

/-- **Extraction core.** A leaf witnessing that is valid *at the verifier's verdicts* yields the
per-branch response family: each branch's witness is present (so `collect`'s guard fires) and
satisfies `relOut` at that branch's extended statement.

Choice-free — the family is read off `o` by `Option.get`. Validity is consumed at
`branchPathOf`-paths only, so no classification of the tree's other paths is ever needed. -/
theorem collect_branch_data
    {relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut)}
    (harity : 2 ^ r + 1 = arity ⟨1, rfl⟩)
    (stmtIn : StmtIn) (v : CarrierCom)
    (challenges : Fin (arity ⟨1, rfl⟩) → (pSpec CarrierCom C r).Challenge ⟨1, rfl⟩)
    (o : ChallengeTree.LeafWitnesses (tree2 v challenges) WitOut)
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

/-- **Generic single-round CWSS assembly, named form.** Any pure statement-extending verifier of
the two-round `pSpec` is coordinate-wise special sound for `foldStructure` **at the named engine**
`treeExtractor mkWitness`, provided a witness assembler `mkWitness` that turns per-branch
`relOut`-witnesses at star-shaped challenge families into a `relIn`-witness. This discharges all
tree/extractor plumbing once; the protocol-specific work (Hachi Lemma 8's case split and
subtract-divide) lives entirely in `hmk`, whose hypotheses are unchanged.

Naming the extractor keeps the extraction *algorithm* inside the statement, which the existential
closure loses (see `Verifier.treeSpecialSoundWith`). The notion's validity premise costs `hmk`
nothing: the verifier is pure, so validity collapses to per-verdict witnessing
(`LeafWitnesses.isValid_iff_pure` at `hpure`) and hands over exactly the per-branch responses,
with no inversion out of `relOut`. -/
theorem coordinateWiseSpecialSoundWith_of_mkWitness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn (StmtIn × CarrierCom × (Fin (2 ^ r) → C)) (pSpec CarrierCom C r))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × CarrierCom × (Fin (2 ^ r) → C)) × WitOut))
    (mkWitness : StmtIn → CarrierCom → (Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) →
      (Fin (2 ^ r + 1) → WitOut) → WitIn)
    (hmk : ∀ stmtIn v (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) (resp : Fin (2 ^ r + 1) → WitOut),
      (∀ j, ((stmtIn, v, fam j), resp j) ∈ relOut) →
      (∃ e, StarAt fam e) →
      (stmtIn, mkWitness stmtIn v fam resp) ∈ relIn) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      (foldStructure (CarrierCom := CarrierCom) (C := C) (r := r)) relIn relOut V
      (treeExtractor mkWitness) := by
  intro stmtIn tree hStruct hAcc
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (foldStructure_arity (CarrierCom := CarrierCom) (C := C) (r := r)).symm
  intro o hvalid
  have hne : (support init).Nonempty :=
    Verifier.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity 0))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (ChallengeTree.LeafWitnesses.isValid_iff_pure init impl
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

/-- **Generic single-round escape-threaded CWSS assembly, named form.**
`coordinateWiseSpecialSoundWith_of_mkWitness` where the protocol-specific obligation `hmk` may
conclude a **local escape event** `escLocal` instead of a `relIn`-witness; the certificate then
carries the induced tree-level event `escEvent relOut escLocal`, unchanged. This is the assembly
for reductions whose extraction can fail into a cryptographic break (e.g. Hachi Lemma 8's
Module-SIS cases).

The disjunction is decided **before any witnessing is seen**, by a classical case split on the
event itself; in the no-escape branch `hmk`'s escape conclusion is refuted, because the collected
response family is itself a witness of `escEvent`'s existential. -/
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
    (hmk : ∀ stmtIn v (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → C)) (resp : Fin (2 ^ r + 1) → WitOut),
      (∀ j, ((stmtIn, v, fam j), resp j) ∈ relOut) →
      (∃ e, StarAt fam e) →
      escLocal stmtIn v fam resp ∨ (stmtIn, mkWitness stmtIn v fam resp) ∈ relIn) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
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
    Verifier.support_init_nonempty_of_accepting hAcc
      (branchPathOf (tree2 v challenges) (Fin.cast harity 0))
  have hvalid' : ∀ p : LeafPath (tree2 v challenges), ∃ w, o p = some w ∧
      ((stmtIn, p.fullTranscript.messages ⟨0, rfl⟩, p.fullTranscript.challenges ⟨1, rfl⟩), w)
        ∈ relOut :=
    (ChallengeTree.LeafWitnesses.isValid_iff_pure init impl
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

end Assembly

/-! ## The 2-round protocol instances (NOT auto-derived for `ProtocolSpec 2`) -/

section Instances

variable {CarrierCom C : Type} {r : ℕ} [SampleableType C] [OracleInterface CarrierCom]

/-- Hand-written 2-round instances (not auto-derived for `ProtocolSpec 2`), generic in `C`. -/
instance : ∀ i, SampleableType ((pSpec CarrierCom C r).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType (Fin (2 ^ r) → C))

instance : ∀ i, OracleInterface ((pSpec CarrierCom C r).Message i)
  | ⟨0, _⟩ => (inferInstance : OracleInterface CarrierCom)
  | ⟨1, h⟩ => nomatch h

end Instances

end CoordinateWise.SingleRound
