/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree

/-!
  # Coordinate-Wise Special Soundness (CWSS) — the notion

  This file defines **coordinate-wise special soundness** for (oracle) reductions, following
  [FMN24] (*Lattice-Based Polynomial Commitments*, who introduce the notion) and [NOZ26] (*Hachi*,
  Definition 3, the multi-round form we target).

  Coordinate-wise special soundness generalizes `k`-special soundness. In `k`-special soundness one
  extracts a witness from a tree of accepting transcripts in which, at each challenge round, there
  are `k` children with pairwise distinct challenges. In coordinate-wise special soundness the
  challenge of round `i` is a *vector* `Sᵢ^{ℓᵢ}`, and the children challenges form a structured set
  `SS(Sᵢ, ℓᵢ, kᵢ)`: a "central" challenge vector together with, for every coordinate, `kᵢ-1` sibling
  vectors that differ from the central one *only in that coordinate*. The arity at round `i` is
  therefore `ℓᵢ·(kᵢ-1)+1`.

  ## What is defined here

  1. The combinatorics of `SS(S, ℓ, k)`: `CoordEq` (the relation `≡ᵢ`) and `IsSpecialSoundFamily`.
  2. A `CWSSStructure`, packaging intrinsically valid per-round coordinate decompositions
     `Challenge i ≃ Sᵢ^{ℓᵢ}` and soundness parameters `kᵢ`.
  3. `CWSSStructure.toShape`: the generic challenge-tree shape whose node predicate is the CWSS
     `SS(Sᵢ, ℓᵢ, kᵢ)` condition.
  4. `Verifier.coordinateWiseSpecialSoundWith` / `Verifier.coordinateWiseSpecialSound`: a tree-based
     extractor turns any structured accepting tree, together with a valid witnessing of its leaves
     (`ChallengeTree.LeafWitnesses.IsValid`), into a valid input witness — the IOR form of [NOZ26]
     Def. 3, named and existentially closed.
  5. `Verifier.coordinateWiseSpecialSoundWithEscape`: the escape-threaded variant, for reductions
     whose extraction may instead break a cryptographic assumption. The escape is an event on
     `(stmtIn, tree)` (`ChallengeTree.EscapeEvent`) entering as a disjunct of the conclusion, so
     relations and extractors stay plain and plain certificates lift losslessly
     (`coordinateWiseSpecialSoundWith.withEscape`).

  Every notion here is its generic counterpart in `Security.TranscriptTree` at the shape
  `D.toShape`, so the generic theory — the shape transports, the classical closer, the composition
  theorems — applies at the CWSS shape with no separate proof.

  Plain `(k)`-special soundness is the `ℓᵢ = 1` case (`Verifier.specialSound` in
  `Security.SpecialSoundness`).

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace CoordinateWise

/-! ## The combinatorial structure `SS(S, ℓ, k)`

These definitions are pure combinatorics on vectors in `S^ℓ ≃ (Fin ℓ → S)`, independent of any
protocol. They capture exactly the set `SS(S, ℓ, k)` from [FMN24] / [NOZ26].
-/

variable {S : Type*}

/-- The relation `x ≡ᵢ y`: the coordinate-vectors `x` and `y` agree in every coordinate except the
  `i`-th, where they differ. For `ℓ = 1` this is just `x 0 ≠ y 0`. -/
def CoordEq {ℓ : ℕ} (i : Fin ℓ) (x y : Fin ℓ → S) : Prop :=
  x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

/-- `≡ᵢ` is decidable over a decidable alphabet: finitely many coordinates, each compared by
`DecidableEq`. This is what lets the star-center search (`CoordinateWise.SingleRound.central` /
`sib`) run rather than choose classically, hence what keeps tree extractors executable. -/
instance instDecidableCoordEq [DecidableEq S] {ℓ : ℕ} (i : Fin ℓ) (x y : Fin ℓ → S) :
    Decidable (CoordEq i x y) := by unfold CoordEq; infer_instance

/-- A family of `ℓ·(k-1)+1` coordinate-vectors `c` is **coordinate-wise special sound**, i.e. lies
  in `SS(S, ℓ, k)`, if

  - the `ℓ·(k-1)+1` vectors are pairwise distinct (`Function.Injective c`), and
  - there is a *central* index `e` such that for every coordinate `i ∈ Fin ℓ` there are `k-1` other
    indices whose vectors agree with `c e` off coordinate `i` (and differ on it).

  This is the precise rendering of the set `SS(S, ℓ, k)` from [FMN24] Def. 2.9 / [NOZ26] §2.3.
  In the paper `SS(S, ℓ, k)` is a *set* `{x₁, …, x_K}` of `K := ℓ·(k-1)+1` **distinct** vectors; the
  `Function.Injective c` clause is what encodes that distinctness. It is load-bearing: since the
  `k-1` siblings of a coordinate `i` agree with `c e` off coordinate `i`, distinctness of the
  vectors forces them to be pairwise distinct *in coordinate `i`*, giving the `k` distinct values
  per coordinate that extraction relies on. (Without it, the siblings could collapse to a single
  value, leaving only `2` distinct values in a coordinate.) The branching arity `ℓ·(k-1)+1` is
  built into the index type. -/
def IsSpecialSoundFamily (ℓ k : ℕ) (c : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → S)) : Prop :=
  Function.Injective c ∧
  ∃ e : Fin (ℓ * (k - 1) + 1),
    ∀ i : Fin ℓ, ∃ J : Finset (Fin (ℓ * (k - 1) + 1)),
      e ∉ J ∧ J.card = k - 1 ∧ ∀ j ∈ J, CoordEq i (c e) (c j)

/-- For `ℓ = 1`, coordinate-wise special soundness is ordinary `k`-special soundness: the challenge
  values are distinct, and there is a central vector together with `k - 1` siblings differing in the
  single coordinate — i.e. `k` pairwise-distinct challenge values. -/
theorem isSpecialSoundFamily_one {k : ℕ} (c : Fin (1 * (k - 1) + 1) → (Fin 1 → S)) :
    IsSpecialSoundFamily 1 k c ↔
      Function.Injective c ∧
      ∃ e, ∃ J : Finset (Fin (1 * (k - 1) + 1)),
        e ∉ J ∧ J.card = k - 1 ∧ ∀ j ∈ J, c e 0 ≠ c j 0 := by
  unfold IsSpecialSoundFamily CoordEq
  constructor
  · rintro ⟨hinj, e, h⟩
    obtain ⟨J, hJ⟩ := h 0
    exact ⟨hinj, e, J, hJ.1, hJ.2.1, fun j hj => (hJ.2.2 j hj).1⟩
  · rintro ⟨hinj, e, J, heJ, hcard, hdiff⟩
    refine ⟨hinj, e, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    refine ⟨J, heJ, hcard, fun j hj => ⟨hdiff j hj, fun j' hj' => ?_⟩⟩
    exact absurd (Subsingleton.elim _ _) hj'

/-- For a single coordinate (`ℓ = 1`), membership in the special-sound family `SS(S, 1, k)` is
  exactly injectivity of the `k` challenge vectors: a central vector together with `k-1` siblings
  differing in the unique coordinate is just `k` pairwise-distinct values. This is the cleaner
  `ℓ = 1` characterization underlying the bridge to plain `k`-special soundness. -/
theorem isSpecialSoundFamily_one_iff_injective {k : ℕ}
    (c : Fin (1 * (k - 1) + 1) → (Fin 1 → S)) :
    IsSpecialSoundFamily 1 k c ↔ Function.Injective c := by
  rw [isSpecialSoundFamily_one]
  refine ⟨fun h => h.1, fun hinj => ⟨hinj, 0, Finset.univ.erase 0,
    Finset.notMem_erase _ _, ?_, ?_⟩⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]; omega
  · intro j hj h0
    exact (Finset.ne_of_mem_erase hj)
      (hinj (funext fun x => by obtain rfl : x = 0 := Subsingleton.elim x 0; exact h0)).symm

end CoordinateWise

-- No `noncomputable section` here: everything below is `Prop`-valued or computable data, and
-- `CoordEq`'s `Decidable` instance above is the search step of the star-center machinery, so it
-- must stay computable. A section here would silently swallow a codegen failure.

/-! ## Coordinate-wise structure on a protocol -/

variable {n : ℕ}

/-- A **coordinate-wise special-soundness structure** for a protocol `pSpec`. For each challenge
  round `i` it provides:
  - the positive number `coordIndex i = ℓᵢ` of coordinates,
  - the per-coordinate alphabet `alphabet i = Sᵢ`,
  - an identification `decompose i : Challenge i ≃ Sᵢ^{ℓᵢ}` of the challenge as a coordinate-vector,
  - the non-trivial soundness parameter `soundnessParam i = kᵢ`,
  - the induced branching arity `ℓᵢ·(kᵢ-1)+1`.

  The branching arity it induces at round `i` is `arity i = ℓᵢ·(kᵢ-1)+1`. -/
structure CWSSStructure (pSpec : ProtocolSpec n) where
  /-- Number of coordinates `ℓᵢ` of the `i`-th challenge. -/
  coordIndex : pSpec.ChallengeIdx → { ell : ℕ // 0 < ell }
  /-- Per-coordinate alphabet `Sᵢ` of the `i`-th challenge. -/
  alphabet : pSpec.ChallengeIdx → Type
  /-- Identification of the `i`-th challenge as a coordinate-vector `Sᵢ^{ℓᵢ}`. -/
  decompose : (i : pSpec.ChallengeIdx) →
    pSpec.Challenge i ≃ (Fin ((coordIndex i).val) → alphabet i)
  /-- The soundness parameter `kᵢ` for the `i`-th challenge. -/
  soundnessParam : pSpec.ChallengeIdx → { k : ℕ // 2 ≤ k }
  /-- Branching arity at the `i`-th challenge. -/
  arity : pSpec.ChallengeIdx → ℕ
  /-- The branching arity is exactly `ℓᵢ·(kᵢ-1)+1`. -/
  arity_eq :
    arity = fun i => (coordIndex i).val * ((soundnessParam i).val - 1) + 1

namespace CWSSStructure

variable {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)

/-- **Every coordinate-wise structure branches at least once**: the arity `ℓᵢ·(kᵢ−1)+1` is
positive whatever `ℓᵢ` and `kᵢ` are. Consumed by `ChallengeTree.LeafPath.some` to produce a
transcript of an arbitrary structured subtree, which is what rules out a rejecting prefix in the
guarded composition. -/
theorem arity_pos (i : pSpec.ChallengeIdx) : 0 < D.arity i := by
  have h := congrFun D.arity_eq i
  omega

/-- The coordinate count `ℓᵢ` as a natural number. -/
abbrev ell (i : pSpec.ChallengeIdx) : ℕ := (D.coordIndex i).val

/-- The soundness parameter `kᵢ` as a natural number. -/
abbrev k (i : pSpec.ChallengeIdx) : ℕ := (D.soundnessParam i).val

/-- The coordinate-wise node predicate at a challenge round. -/
def nodeOk (i : pSpec.ChallengeIdx)
    (challenges : Fin (D.arity i) → pSpec.Challenge i) : Prop :=
  let hArity : D.arity i = D.ell i * (D.k i - 1) + 1 := congrFun D.arity_eq i
  CoordinateWise.IsSpecialSoundFamily (D.ell i) (D.k i)
    (fun j => D.decompose i (challenges (Fin.cast hArity.symm j)))

/-- The generic challenge-tree shape induced by a CWSS structure. -/
def toShape : ChallengeTreeShape pSpec where
  arity := D.arity
  nodeOk := D.nodeOk

/-- Every CWSS shape branches: the arity `ℓᵢ·(kᵢ-1)+1` is positive at every challenge round.

  The generic tree-soundness notion is unconditioned in the arity, but the guarded-left composition
  theorems need a suffix leaf to probe; this is what discharges their positivity hypothesis at every
  CWSS call site. -/
theorem toShape_arity_pos : ∀ i, 0 < D.toShape.arity i := fun i => by
  change 0 < D.arity i
  rw [congrFun D.arity_eq i]; omega

/-- The canonical coordinate-wise structure underlying plain `k`-special soundness: every challenge
  has a single coordinate (`ℓᵢ = 1`) over the alphabet `Challenge i`, with soundness parameters `k`.
  Used to relate `k`-special soundness to CWSS as the `ℓᵢ = 1` case.

  Marked `@[reducible]` so that instances on `pSpec.Challenge i` (e.g. `Fintype`, `SampleableType`)
  are found for `(ofSpecialSound k).alphabet i`. -/
@[reducible]
def ofSpecialSound (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i : pSpec.ChallengeIdx, 2 ≤ k i) : CWSSStructure pSpec where
  coordIndex := fun _ => ⟨1, Nat.zero_lt_one⟩
  alphabet := fun i => pSpec.Challenge i
  decompose := fun i => (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm
  soundnessParam := fun i => ⟨k i, hk i⟩
  arity := fun i => 1 * (k i - 1) + 1
  arity_eq := rfl

end CWSSStructure

/-! ## The coordinate-wise special-soundness predicate

`Verifier.treeSpecialSoundWith` and its escape twin at the CWSS shape `D.toShape`. Every declaration
below is that instance, so the generic theory applies at the CWSS shape and nothing here carries a
proof of its own. -/

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A named tree-based extractor `Ext` **witnesses coordinate-wise special soundness** of a
  verifier: `Verifier.treeSpecialSoundWith` at the CWSS shape `D.toShape`. On every `D`-structured
  accepting tree and every valid leaf witnessing of it, `Ext` succeeds with a `relIn`-witness.

  This named form is the content-bearing statement (see `Verifier.treeSpecialSoundWith`); its
  existential closure is `Verifier.coordinateWiseSpecialSound`. Advertised protocol theorems should
  state this form at the protocol's actual extractor; the `CoordinateWise` packages carry the
  extractor as a field and their `isCWSS` certificate is this form at it. -/
def coordinateWiseSpecialSoundWith (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity) : Prop :=
  treeSpecialSoundWith init impl (CWSSStructure.toShape D) relIn relOut verifier Ext

/-- A verifier is **coordinate-wise special sound** with respect to a coordinate-wise structure `D`,
  an input relation `relIn` and an output relation `relOut` if it is tree-special-sound for the
  generic shape induced by `D`.

  This is the multi-round coordinate-wise special soundness of [NOZ26] Def. 3 / [FMN24] Def. 2.10,
  phrased over ArkLib's IOR machinery. The papers' accept/reject condition is represented by the
  language of the output relation. Specializing `D` to `CWSSStructure.ofSpecialSound k` corresponds
  to the standard notion of `k`-special soundness.

  The extractor is existential (inherited from `Verifier.treeSpecialSound`), which loses the
  extraction *algorithm*; prefer `coordinateWiseSpecialSoundWith` at a named extractor for
  advertised protocol statements and keep this form for plumbing. Reductions whose extraction may
  instead break a cryptographic assumption use `coordinateWiseSpecialSoundWithEscape` / `…Escape`
  below. -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  verifier.treeSpecialSound init impl (CWSSStructure.toShape D) relIn relOut

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The existential notion is definitionally the existential closure of the named one. -/
theorem coordinateWiseSpecialSound_iff_exists (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.coordinateWiseSpecialSound init impl D relIn relOut ↔
      ∃ Ext, coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext := Iff.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor. -/
theorem coordinateWiseSpecialSoundWith.toCWSS {D : CWSSStructure pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext) :
    verifier.coordinateWiseSpecialSound init impl D relIn relOut := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The unconditioned reading of a CWSS certificate**: `treeSpecialSoundWith`'s closer at the CWSS
  shape. Closing the named extractor with the canonical witnessing
  (`ChallengeTree.canonWitnesses`) drops the validity premise, at the cost of `[Inhabited WitIn]`
  and nothing else. -/
theorem coordinateWiseSpecialSoundWith.mem_relIn_of_isAccepting [Inhabited WitIn]
    {D : CWSSStructure pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext) (stmtIn : StmtIn)
    (tree : ChallengeTree pSpec (CWSSStructure.toShape D).arity 0)
    (hstr : tree.IsStructured (CWSSStructure.toShape D))
    (hacc : tree.IsAccepting init impl verifier stmtIn relOut.language) :
    (stmtIn, (Ext stmtIn tree
      (ChallengeTree.canonWitnesses init impl verifier relOut stmtIn)).getD default) ∈ relIn :=
  treeSpecialSoundWith.mem_relIn_of_isAccepting init impl h stmtIn tree hstr hacc

/-! ### Escape-threaded CWSS

The CWSS-shaped instances of `Verifier.treeSpecialSoundWithEscape`: the conclusion is
`esc stmtIn tree ∨ extraction succeeds on every valid witnessing`, where `esc` is a trusted escape
event on `(stmtIn, tree)` (contract: `ChallengeTree.EscapeEvent`). -/

/-- **Escape-threaded CWSS, named form**: `Verifier.treeSpecialSoundWithEscape` at the CWSS shape
  `D.toShape`, i.e. on every structured accepting tree either the tree exhibits the escape event
  `esc` (a trusted spec — `ChallengeTree.EscapeEvent`) or `Ext` produces a `relIn`-witness from
  every valid leaf witnessing. -/
def coordinateWiseSpecialSoundWithEscape (D : CWSSStructure pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity) : Prop :=
  treeSpecialSoundWithEscape init impl (CWSSStructure.toShape D) esc relIn relOut verifier Ext

/-- Existential closure of `coordinateWiseSpecialSoundWithEscape`. The named form is preferred in
  advertised statements, since a composed chain then exposes a runnable end-to-end extractor.

  **This form has no consumer, by design** — see `Verifier.treeSpecialSoundEscape`. It is not
  "kept for plumbing": every escape append now names its right factor's extractor, and reverting
  one to this form would break the runnable composed chain. -/
def coordinateWiseSpecialSoundEscape (D : CWSSStructure pSpec)
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  treeSpecialSoundEscape init impl (CWSSStructure.toShape D) esc relIn relOut verifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor (escape-threaded). -/
theorem coordinateWiseSpecialSoundWithEscape.toEscape {D : CWSSStructure pSpec}
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier Ext) :
    coordinateWiseSpecialSoundEscape init impl D esc relIn relOut verifier := ⟨Ext, h⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The unconditioned reading of an escape-threaded CWSS certificate**, the closer for the notion
  every Hachi link actually carries: on a structured accepting tree, either the escape event fires
  or the recovered witness is in `relIn`, with no witnessing premise in the statement.

  The escape disjunct is untouched by the closing, which is exactly what the quantifier order of
  `Verifier.treeSpecialSoundWithEscape` buys. See
  `Verifier.treeSpecialSoundWithEscape.escape_or_mem_relIn_of_isAccepting` for what this reading
  does and does not say: it recovers the *non-algorithmic* statement, as a migration receipt, and
  the `∀ o valid` form remains the stronger one. -/
theorem coordinateWiseSpecialSoundWithEscape.escape_or_mem_relIn_of_isAccepting [Inhabited WitIn]
    {D : CWSSStructure pSpec}
    {esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier Ext)
    (stmtIn : StmtIn) (tree : ChallengeTree pSpec (CWSSStructure.toShape D).arity 0)
    (hstr : tree.IsStructured (CWSSStructure.toShape D))
    (hacc : tree.IsAccepting init impl verifier stmtIn relOut.language) :
    esc stmtIn tree ∨
      (stmtIn, (Ext stmtIn tree
        (ChallengeTree.canonWitnesses init impl verifier relOut stmtIn)).getD default) ∈ relIn :=
  treeSpecialSoundWithEscape.escape_or_mem_relIn_of_isAccepting init impl h stmtIn tree hstr hacc

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Lossless escape lift at the CWSS shape** (the entry point for the packages' kind lifts): a
  plain CWSS certificate holds at any escape event, via the right disjunct. -/
theorem coordinateWiseSpecialSoundWith.withEscape {D : CWSSStructure pSpec}
    (esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext) :
    coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier Ext :=
  treeSpecialSoundWith.withEscape init impl esc h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- At the never-firing event escape-threaded CWSS is plain CWSS. -/
theorem coordinateWiseSpecialSoundWithEscape_false_iff (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity) :
    coordinateWiseSpecialSoundWithEscape init impl D (fun _ _ => False) relIn relOut verifier Ext ↔
      coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext :=
  treeSpecialSoundWithEscape_false_iff init impl _ relIn relOut verifier Ext

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Escape events are monotone at the CWSS shape. -/
theorem coordinateWiseSpecialSoundWithEscape.mono {D : CWSSStructure pSpec}
    {esc esc' : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape D).arity}
    (hmono : ∀ s t, esc s t → esc' s t)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier Ext) :
    coordinateWiseSpecialSoundWithEscape init impl D esc' relIn relOut verifier Ext :=
  treeSpecialSoundWithEscape.mono init impl hmono h

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-! ## The oracle-level predicate

As at the non-oracle level, each notion is the underlying verifier's on the combined (oracle +
non-oracle) statements; the challenge structure `D` is unchanged, since an oracle verifier's
challenges are the same. -/

/-- A named tree-based extractor witnesses coordinate-wise special soundness of an oracle reduction:
  `Verifier.coordinateWiseSpecialSoundWith` of the underlying non-oracle verifier on the combined
  (oracle + non-oracle) statements. The named form is the content-bearing statement (see
  `Verifier.treeSpecialSoundWith`). -/
def coordinateWiseSpecialSoundWith (D : CWSSStructure pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (Ext : Extractor.TreeBased (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec
      (CWSSStructure.toShape D).arity) : Prop :=
  Verifier.coordinateWiseSpecialSoundWith init impl D relIn relOut verifier.toVerifier Ext

/-- Coordinate-wise special soundness of an oracle reduction, defined (as for round-by-round
  notions) via the underlying non-oracle verifier on the combined (oracle + non-oracle) statements.

  As at the non-oracle level, the extractor is existential, so prefer
  `coordinateWiseSpecialSoundWith` at a named extractor for advertised statements. -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  verifier.toVerifier.coordinateWiseSpecialSound init impl D relIn relOut

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor (oracle level). -/
theorem coordinateWiseSpecialSoundWith.toCWSS {D : CWSSStructure pSpec}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {Ext : Extractor.TreeBased (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec
      (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWith init impl D relIn relOut verifier Ext) :
    verifier.coordinateWiseSpecialSound init impl D relIn relOut := ⟨Ext, h⟩

/-- Escape-threaded CWSS of an oracle reduction, **named form**: the non-oracle escape notion of the
  underlying verifier on the combined (oracle + non-oracle) statements. The escape event is indexed
  by the combined input statement, so it may read the oracle statements. -/
def coordinateWiseSpecialSoundWithEscape (D : CWSSStructure pSpec)
    (esc : ChallengeTree.EscapeEvent (StmtIn × ∀ i, OStmtIn i) pSpec
      (CWSSStructure.toShape D).arity)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (Ext : Extractor.TreeBased (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec
      (CWSSStructure.toShape D).arity) : Prop :=
  Verifier.coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier.toVerifier Ext

/-- Existential closure of the oracle-level escape-threaded CWSS. Like its non-oracle counterpart
  `Verifier.coordinateWiseSpecialSoundEscape`, this has **no consumer by design**; prefer the named
  form in advertised statements. -/
def coordinateWiseSpecialSoundEscape (D : CWSSStructure pSpec)
    (esc : ChallengeTree.EscapeEvent (StmtIn × ∀ i, OStmtIn i) pSpec
      (CWSSStructure.toShape D).arity)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  Verifier.coordinateWiseSpecialSoundEscape init impl D esc relIn relOut verifier.toVerifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Forget the name of the extractor (oracle level, escape-threaded). -/
theorem coordinateWiseSpecialSoundWithEscape.toEscape {D : CWSSStructure pSpec}
    {esc : ChallengeTree.EscapeEvent (StmtIn × ∀ i, OStmtIn i) pSpec
      (CWSSStructure.toShape D).arity}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {Ext : Extractor.TreeBased (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec
      (CWSSStructure.toShape D).arity}
    (h : coordinateWiseSpecialSoundWithEscape init impl D esc relIn relOut verifier Ext) :
    coordinateWiseSpecialSoundEscape init impl D esc relIn relOut verifier := ⟨Ext, h⟩

end OracleVerifier
