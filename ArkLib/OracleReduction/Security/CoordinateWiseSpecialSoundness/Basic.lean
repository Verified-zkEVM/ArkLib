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
  2. A `CWSSStructure`, packaging the per-round coordinate decomposition `Challenge i ≃ Sᵢ^{ℓᵢ}` and
     soundness parameters `kᵢ`.
  3. `ChallengeTree.IsStructured`: the predicate that a tree's sibling challenges form `SS`-sets.
  4. `Verifier.coordinateWiseSpecialSound`: existence of a (deterministic) tree-based extractor that
     turns any structured, accepting tree into a valid input witness — exactly [NOZ26] Def. 3.
  5. `CWSSStructure.knowledgeError`: the knowledge error `∑ᵢ ℓᵢ·(kᵢ-1) / |Sᵢ|` of [FMN24]
     Lemma 2.31. ([NOZ26] Lemma 4 misprints the denominator as `|Sᵢ|^{ℓᵢ}`; see the docstring.)

  Plain `(k)`-special soundness is the `ℓᵢ = 1` case (`Verifier.specialSound` in
  `Security.SpecialSoundness`); the coordinate oracle realizing the rewinding extraction lives in
  `CoordinateOracle.lean`, and the CWSS ⇒ rewinding-knowledge-soundness implication in
  `Security.Implications.CoordinateWiseSpecialSoundnessRewinding`.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

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

end CoordinateWise

/-! ## Coordinate-wise structure on a protocol -/

variable {n : ℕ}

/-- A **coordinate-wise special-soundness structure** for a protocol `pSpec`. For each challenge
  round `i` it provides:
  - the number `coordIndex i = ℓᵢ` of coordinates,
  - the per-coordinate alphabet `alphabet i = Sᵢ`,
  - an identification `decompose i : Challenge i ≃ Sᵢ^{ℓᵢ}` of the challenge as a coordinate-vector,
  - the soundness parameter `soundnessParam i = kᵢ`.

  The branching arity it induces at round `i` is `arity i = ℓᵢ·(kᵢ-1)+1`. -/
structure CWSSStructure (pSpec : ProtocolSpec n) where
  /-- Number of coordinates `ℓᵢ` of the `i`-th challenge. -/
  coordIndex : pSpec.ChallengeIdx → ℕ
  /-- Per-coordinate alphabet `Sᵢ` of the `i`-th challenge. -/
  alphabet : pSpec.ChallengeIdx → Type
  /-- Identification of the `i`-th challenge as a coordinate-vector `Sᵢ^{ℓᵢ}`. -/
  decompose : (i : pSpec.ChallengeIdx) → pSpec.Challenge i ≃ (Fin (coordIndex i) → alphabet i)
  /-- The soundness parameter `kᵢ` for the `i`-th challenge. -/
  soundnessParam : pSpec.ChallengeIdx → ℕ

namespace CWSSStructure

variable {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)

/-- The branching arity `arity i = ℓᵢ·(kᵢ-1)+1` of the transcript tree at challenge round `i`. -/
@[reducible]
def arity : pSpec.ChallengeIdx → ℕ :=
  fun i => D.coordIndex i * (D.soundnessParam i - 1) + 1

/-- The canonical coordinate-wise structure underlying plain `k`-special soundness: every challenge
  has a single coordinate (`ℓᵢ = 1`) over the alphabet `Challenge i`, with soundness parameters `k`.
  Used to relate `k`-special soundness to CWSS as the `ℓᵢ = 1` case.

  Marked `@[reducible]` so that instances on `pSpec.Challenge i` (e.g. `Fintype`, `SampleableType`)
  are found for `(ofSpecialSound k).alphabet i`. -/
@[reducible]
def ofSpecialSound (k : pSpec.ChallengeIdx → ℕ) : CWSSStructure pSpec where
  coordIndex := fun _ => 1
  alphabet := fun i => pSpec.Challenge i
  decompose := fun i => (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm
  soundnessParam := k

/-- The CWSS knowledge error `∑ᵢ ℓᵢ·(kᵢ-1) / |Sᵢ|`, summed over challenge rounds: the
  per-round generalization of [FMN24] Lemma 2.31 (stated there, for a common alphabet `S` and
  parameter `k`, as `(ℓ₁ + ⋯ + ℓ_μ)·(k-1)/|S|`).

  **[NOZ26] misprint.** Hachi's Lemma 4 states this error as `∑ᵢ ℓᵢ·kᵢ / |Sᵢ|^{ℓᵢ}` while citing
  [FMN24, Section 7], whose Lemma 2.31 has denominator `|S|`, not `|S|^ℓ`. This is a typo in the
  Hachi paper (soon to be corrected).

  Achieving this linear error requires an *expected-time* rewinding extractor ([FMN24] Fig. 11,
  a retry-until-accept loop); strictly bounded extractors (every `OracleComp` makes finitely many
  queries) can only achieve forking-lemma-style bounds. This constant is therefore the reference
  target; the bound actually proved by the implication in
  `Security.Implications.CoordinateWiseSpecialSoundnessRewinding` is the forking-style one. -/
def knowledgeError (D : CWSSStructure pSpec) [∀ i, Fintype (D.alphabet i)] : ℝ≥0 :=
  ∑ i : pSpec.ChallengeIdx,
    (D.coordIndex i * (D.soundnessParam i - 1) : ℝ≥0) /
      (Fintype.card (D.alphabet i) : ℝ≥0)

end CWSSStructure

namespace ProtocolSpec.ChallengeTree

open CoordinateWise

variable {pSpec : ProtocolSpec n}

/-- A tree of transcripts with arity `D.arity` is **`D`-structured** if, at every challenge node,
  the sibling challenges — read as coordinate-vectors via `D.decompose` — form a coordinate-wise
  special-sound family `SS(Sᵢ, ℓᵢ, kᵢ)`.

  This is the structural condition that makes a tree usable by a coordinate-wise special-soundness
  extractor. With `D = CWSSStructure.ofSpecialSound k` it specializes to "the `k` sibling challenges
  at each node are pairwise distinct", i.e. the condition for plain `k`-special soundness. -/
def IsStructured (D : CWSSStructure pSpec) :
    {m : Fin (n + 1)} → ChallengeTree pSpec D.arity m → Prop
  | _, .leaf => True
  | _, .msgNode _ _ _ child => child.IsStructured D
  | _, .chalNode m h challenges children =>
      IsSpecialSoundFamily (D.coordIndex ⟨m, h⟩) (D.soundnessParam ⟨m, h⟩)
        (fun j => D.decompose ⟨m, h⟩ (challenges j))
      ∧ ∀ j, (children j).IsStructured D

end ProtocolSpec.ChallengeTree

/-! ## The coordinate-wise special-soundness predicate -/

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A verifier is **coordinate-wise special sound** with respect to a coordinate-wise structure `D`,
  an input relation `relIn` and an output language `langOut` if there is a tree-based extractor `E`
  such that: for every input statement `stmtIn` and every tree of transcripts that is

  - `D`-structured (its sibling challenges form `SS(Sᵢ, ℓᵢ, kᵢ)`-sets), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `langOut`),

  the extracted witness `E stmtIn tree` satisfies `(stmtIn, E stmtIn tree) ∈ relIn`.

  This is the multi-round coordinate-wise special soundness of [NOZ26] Def. 3 / [FMN24] Def. 2.10,
  phrased over ArkLib's IOR machinery. Specializing `D` to `CWSSStructure.ofSpecialSound k`
  corresponds to the standard notion of `k`-special soundness (`Verifier.specialSound`). -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ E : Extractor.TreeBased StmtIn WitIn pSpec D.arity,
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec D.arity 0,
    tree.IsStructured D →
    tree.IsAccepting init impl verifier stmtIn langOut →
      (stmtIn, E stmtIn tree) ∈ relIn

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Coordinate-wise special soundness of an oracle reduction, defined (as for round-by-round
  notions) via the underlying non-oracle verifier on the combined (oracle + non-oracle) statements.
  The challenge structure `D` is unchanged, since the verifier's challenges are the same. -/
def coordinateWiseSpecialSound (D : CWSSStructure pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  verifier.toVerifier.coordinateWiseSpecialSound init impl D relIn langOut

end OracleVerifier
