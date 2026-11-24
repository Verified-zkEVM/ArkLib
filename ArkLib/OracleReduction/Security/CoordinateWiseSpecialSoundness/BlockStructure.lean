/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn, Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Layout
public import Mathlib.Order.Sigma

/-!
  # Coordinate-wise special soundness with a layout per round

  `CWSSStructure` gives every round one alphabet and one threshold for all coordinates of its
  challenge, and extracts with one star. `BlockCWSSStructure` gives every round a `Layout`: a
  sequence of blocks, each a star with an alphabet and a threshold per coordinate. A flat round is
  one block, a nested round is one coordinate per block, and plain `k`-special soundness is one
  block with one coordinate.

  The structure carries the temporary name `BlockCWSSStructure` while it coexists with
  `CWSSStructure`. When the consumers have moved over, it takes the name `CWSSStructure`, and
  today's structure becomes `HomogeneousCWSSStructure`.

  ## Main definitions

  - `BlockCWSSStructure`: a layout for every challenge round and an identification of the round's
    challenge with the layout's points.
  - `BlockCWSSStructure.toShape`: the generic tree shape whose node predicate is the tree condition
    of the layout.
  - `BlockCWSSStructure.treeSize` and `BlockCWSSStructure.knowledgeError`: the number of leaves of
    a complete tree and the sum of the errors of all blocks. The error is the failure probability
    of the coordinate-fibre search of one block, summed over blocks. It becomes a bound on a
    knowledge error through the block finder, not through this file.
  - `BlockCWSSStructure.BlockIdx`: the blocks of all rounds in protocol order, the index set of a
    multi-round finder (`treeSize_eq_prod_blocks`, `knowledgeError_eq_sum_blocks`).
  - `BlockCWSSStructure.ofSpecialSound`, `BlockCWSSStructure.ofIsEmpty`: plain `k`-special
    soundness and the structure of a protocol without challenges.
  - `CWSSStructure.toBlock`: today's structure as a structure with a flat layout per round. Its
    shape is today's shape (`CWSSStructure.toBlock_toShape`), so tree soundness at the two agree
    (`Verifier.treeSpecialSound_toBlock_iff`).

  ## Computability

  Everything here is a proposition or computable data. The errors take values in `ℚ≥0`.

  ## References

  * [Dao, Q., Bodaghi, O., Khajehpour, A., Vitto, G., Badakhshan, M., Georghiades, M., Liu, F.,
      Zhang, J., and Thaler, J., *Akita: A High-Performance Lattice-Based Polynomial Commitment
      Scheme*][DBKVBGLZT26]
  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
-/

@[expose] public section

open ProtocolSpec CoordinateWise
open scoped NNRat

variable {n : ℕ}

/-- A **coordinate-wise special-soundness structure with layouts** for a protocol `pSpec`: a layout
for every challenge round, and an identification of the round's challenge with the points of its
layout. -/
structure BlockCWSSStructure (pSpec : ProtocolSpec n) where
  /-- The layout of the `i`-th challenge. -/
  layout : pSpec.ChallengeIdx → Layout
  /-- Identification of the `i`-th challenge with the points of its layout. -/
  decompose : (i : pSpec.ChallengeIdx) → pSpec.Challenge i ≃ (layout i).Point
  /-- Branching arity at the `i`-th challenge. A closed form keeps the branch types of extractors
  definitional at call sites. -/
  arity : pSpec.ChallengeIdx → ℕ := fun i => (layout i).arity
  /-- The branching arity is the number of leaves of the layout. -/
  arity_eq : ∀ i, arity i = (layout i).arity := by intro; rfl

namespace BlockCWSSStructure

variable {pSpec : ProtocolSpec n} (D : BlockCWSSStructure pSpec)

/-- Every round branches at least once. -/
theorem arity_pos (i : pSpec.ChallengeIdx) : 0 < D.arity i :=
  (D.arity_eq i) ▸ (D.layout i).arity_pos

/-- The node predicate at a challenge round: the children form a tree of the round's layout. -/
def nodeOk (i : pSpec.ChallengeIdx) (challenges : Fin (D.arity i) → pSpec.Challenge i) : Prop :=
  (D.layout i).IsTree (fun j => D.decompose i (challenges (Fin.cast (D.arity_eq i).symm j)))

/-- The generic challenge-tree shape induced by the structure. -/
def toShape : ChallengeTreeShape pSpec where
  arity := D.arity
  nodeOk := D.nodeOk

theorem toShape_arity_pos : ∀ i, 0 < D.toShape.arity i := D.arity_pos

/-- The number of leaves of a complete tree: the product of the arities. -/
def treeSize : ℕ := ∏ i, D.arity i

/-- The sum of the errors of all blocks of all rounds. -/
def knowledgeError [∀ i b u, Fintype (((D.layout i).block b).Alphabet u)] : ℚ≥0 :=
  ∑ i, (D.layout i).error

/-- Every block of every round is admissible. -/
def Admissible [∀ i b u, Fintype (((D.layout i).block b).Alphabet u)] : Prop :=
  ∀ i, (D.layout i).Admissible

/-! ### All blocks of all rounds -/

/-- The blocks of every round, in protocol order and then block order. -/
abbrev BlockIdx : Type := Lex (Σ i : pSpec.ChallengeIdx, Fin (D.layout i).depth)

/-- The blocks are linearly ordered. -/
example : LinearOrder D.BlockIdx := inferInstance

/-- The block at an index. -/
abbrev blockOf (β : D.BlockIdx) : Block := (D.layout (ofLex β).1).block (ofLex β).2

instance : Fintype D.BlockIdx :=
  inferInstanceAs (Fintype (Σ i : pSpec.ChallengeIdx, Fin (D.layout i).depth))

theorem treeSize_eq_prod_blocks : D.treeSize = ∏ β : D.BlockIdx, (D.blockOf β).arity := by
  change ∏ i, D.arity i =
    ∏ x : (Σ i : pSpec.ChallengeIdx, Fin (D.layout i).depth), ((D.layout x.1).block x.2).arity
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => D.arity_eq i

theorem knowledgeError_eq_sum_blocks [∀ i b u, Fintype (((D.layout i).block b).Alphabet u)] :
    D.knowledgeError = ∑ β : D.BlockIdx, (D.blockOf β).error := by
  change ∑ i, (D.layout i).error =
    ∑ x : (Σ i : pSpec.ChallengeIdx, Fin (D.layout i).depth), ((D.layout x.1).block x.2).error
  rw [Fintype.sum_sigma]
  rfl

/-! ### Constructors -/

/-- Plain `k`-special soundness: one coordinate per round, over the challenge itself.

Marked `@[reducible]` so that instances on `pSpec.Challenge i` (for example `Fintype`) are found for
the alphabet of its layout. -/
@[reducible]
def ofSpecialSound (k : pSpec.ChallengeIdx → ℕ) : BlockCWSSStructure pSpec where
  layout i := Layout.single (pSpec.Challenge i) (k i)
  decompose i := Layout.singleEquiv _ _

/-- The structure of a protocol without challenge rounds. -/
def ofIsEmpty [IsEmpty pSpec.ChallengeIdx] : BlockCWSSStructure pSpec where
  layout i := isEmptyElim i
  decompose i := isEmptyElim i
  arity i := isEmptyElim i
  arity_eq i := isEmptyElim i

end BlockCWSSStructure

/-! ## Today's structure as a structure with layouts -/

namespace CWSSStructure

variable {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)

/-- A homogeneous structure is a structure with a flat layout of one block per round, with constant
alphabets and thresholds.

Marked `@[reducible]` so that instances on `D.alphabet i` (for example `Fintype`) are found for the
alphabets of `D.toBlock`. -/
@[reducible]
def toBlock : BlockCWSSStructure pSpec where
  layout i := Layout.homogeneous (D.ell i) (D.alphabet i) (D.k i)
  decompose i := (D.decompose i).trans (Layout.homogeneousEquiv _ _ _)
  arity := D.arity
  arity_eq i := by rw [congrFun D.arity_eq i, Layout.arity_homogeneous]

/-- The node predicates of `D` and of `D.toBlock` agree. -/
theorem toBlock_nodeOk_iff (i : pSpec.ChallengeIdx)
    (challenges : Fin (D.arity i) → pSpec.Challenge i) :
    D.toBlock.nodeOk i challenges ↔ D.nodeOk i challenges := by
  have hA : D.arity i = D.ell i * (D.k i - 1) + 1 := congrFun D.arity_eq i
  have hB : Block.arity ⟨D.ell i, fun _ => D.alphabet i, fun _ => D.k i⟩ =
      D.ell i * (D.k i - 1) + 1 := by
    simp [Block.arity]
  unfold BlockCWSSStructure.nodeOk nodeOk
  rw [Layout.isTree_flat_iff]
  exact CoordinateWise.isBlockSpecialSoundFamily_comp_equiv_iff (k := fun _ => D.k i)
    (c := fun j => D.decompose i (challenges (Fin.cast hA.symm j))) (finCongr hB)

/-- The shape of `D.toBlock` is the shape of `D`. -/
theorem toBlock_toShape : D.toBlock.toShape = D.toShape :=
  ChallengeTreeShape.ext rfl
    (heq_of_eq (funext fun i => funext fun c => propext (D.toBlock_nodeOk_iff i c)))

/-- The number of leaves of a complete tree of a homogeneous structure. -/
theorem toBlock_treeSize : D.toBlock.treeSize = ∏ i, (D.ell i * (D.k i - 1) + 1) :=
  Finset.prod_congr rfl fun i _ => congrFun D.arity_eq i

/-- The error of a homogeneous structure is `∑ i, ℓ i * (k i - 1) / |S i|`. -/
theorem toBlock_knowledgeError [∀ i, Fintype (D.alphabet i)] :
    D.toBlock.knowledgeError =
      ∑ i, ((D.ell i * (D.k i - 1) : ℕ) : ℚ≥0) / Fintype.card (D.alphabet i) := by
  unfold BlockCWSSStructure.knowledgeError
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toBlock, Layout.error, Block.error, Finset.univ_unique, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.card_singleton, Nat.cast_one,
    one_mul, Nat.cast_mul]
  exact (mul_div_assoc _ _ _).symm

end CWSSStructure

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Tree special soundness at the shape of `D.toBlock` is coordinate-wise special soundness at
`D`. -/
theorem treeSpecialSound_toBlock_iff [∀ i, SampleableType (pSpec.Challenge i)]
    (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.treeSpecialSound init impl D.toBlock.toShape relIn relOut ↔
      verifier.coordinateWiseSpecialSound init impl D relIn relOut := by
  rw [CWSSStructure.toBlock_toShape]
  rfl

end Verifier
