/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import Mathlib.Data.NNRat.Defs

/-!
  # Coordinate-wise special soundness with one alphabet and one arity per coordinate

  `CWSSStructure` gives every coordinate of a round's challenge the same alphabet and the same
  soundness parameter. This file drops both restrictions: coordinate `u` of round `i` ranges over
  its own alphabet `alphabet i u`, and extraction needs `soundnessParam i u` distinct values there
  while all other coordinates stay fixed. Such a round branches into
  `1 + ∑ u, (soundnessParam i u - 1)` children.

  ## Main definitions

  - `CoordinateWise.HeteroCoordEq`, `CoordinateWise.IsHeteroSpecialSoundFamily`: the star
    condition on a family of coordinate vectors over per-coordinate alphabets. A family is a star
    when it has a centre with `k u - 1` siblings that differ from the centre in coordinate `u`
    alone, for every coordinate `u`. `CoordinateWise.IsHeteroSpecialSoundFamily.card_ge` shows
    that such a family has at least `1 + ∑ u, (k u - 1)` members.
  - `HeteroCWSSStructure`: the per-round data (coordinates, alphabets, decomposition of the
    challenge, parameters) with its induced generic tree shape `HeteroCWSSStructure.toShape`.
  - `CWSSStructure.toHetero`: the homogeneous structure as a heterogeneous one. Its shape is the
    homogeneous shape (`CWSSStructure.toHetero_toShape`), so tree soundness at the two agree
    (`Verifier.treeSpecialSound_toHetero_iff`).
  - `HeteroCWSSStructure.treeSize` and `HeteroCWSSStructure.errorBound`: the number of leaves of a
    complete tree, `∏ i, (1 + ∑ u, (k i u - 1))`, and the sum `∑ i, ∑ u, (k i u - 1) / |X i u|`
    of the coordinate failure probabilities. Both reduce to the homogeneous formulas
    (`CWSSStructure.toHetero_treeSize`, `CWSSStructure.toHetero_errorBound`). This file does not
    bound a knowledge error by `errorBound`; that statement needs a rewinding engine.

  ## Computability

  Everything here is a proposition or computable data. `errorBound` takes values in `ℚ≥0` so that
  it can be evaluated.

  ## References

  * [Dao, Q., Bodaghi, O., Khajehpour, A., Vitto, G., Badakhshan, M., Georghiades, M., Liu, F.,
      Zhang, J., and Thaler, J., *Akita: A High-Performance Lattice-Based Polynomial Commitment
      Scheme*][DBKVBGLZT26]
  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
-/

@[expose] public section

open ProtocolSpec
open scoped NNRat

namespace CoordinateWise

section Family

variable {ℓ : ℕ} {S : Fin ℓ → Type*}

/-- Two coordinate vectors over per-coordinate alphabets agree everywhere except at coordinate
`i`, where they differ. -/
def HeteroCoordEq (i : Fin ℓ) (x y : (u : Fin ℓ) → S u) : Prop :=
  x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j

instance [∀ u, DecidableEq (S u)] (i : Fin ℓ) (x y : (u : Fin ℓ) → S u) :
    Decidable (HeteroCoordEq i x y) := by
  unfold HeteroCoordEq
  infer_instance

/-- With one alphabet for all coordinates, `HeteroCoordEq` is `CoordEq`. -/
theorem heteroCoordEq_iff_coordEq {T : Type*} (i : Fin ℓ) (x y : Fin ℓ → T) :
    HeteroCoordEq (S := fun _ => T) i x y ↔ CoordEq i x y :=
  Iff.rfl

/-- A family of coordinate vectors is a **star** with parameters `k` when its vectors are pairwise
distinct and it has a centre with `k u - 1` siblings for every coordinate `u`. The siblings agree
with the centre off `u` and differ from it at `u`.

The size `N` of the family is not fixed here; a complete star has `1 + ∑ u, (k u - 1)` members
(see `IsHeteroSpecialSoundFamily.card_ge`). A parameter `k u` of `0` or `1` asks for no sibling
at coordinate `u`. -/
def IsHeteroSpecialSoundFamily {N : ℕ} (k : Fin ℓ → ℕ) (c : Fin N → ((u : Fin ℓ) → S u)) : Prop :=
  Function.Injective c ∧
  ∃ e : Fin N, ∀ i : Fin ℓ, ∃ J : Finset (Fin N),
    e ∉ J ∧ J.card = k i - 1 ∧ ∀ j ∈ J, HeteroCoordEq i (c e) (c j)

instance [∀ u, DecidableEq (S u)] {N : ℕ} (k : Fin ℓ → ℕ) (c : Fin N → ((u : Fin ℓ) → S u)) :
    Decidable (IsHeteroSpecialSoundFamily k c) := by
  unfold IsHeteroSpecialSoundFamily
  infer_instance

/-- With one alphabet and one parameter for all coordinates, the star condition is the one of
`IsSpecialSoundFamily`. -/
theorem isSpecialSoundFamily_iff_isHeteroSpecialSoundFamily {T : Type*} {k : ℕ}
    (c : Fin (ℓ * (k - 1) + 1) → (Fin ℓ → T)) :
    IsSpecialSoundFamily ℓ k c ↔ IsHeteroSpecialSoundFamily (S := fun _ => T) (fun _ => k) c :=
  Iff.rfl

variable {N M : ℕ} {k : Fin ℓ → ℕ} {c : Fin N → ((u : Fin ℓ) → S u)}

/-- Reindexing a star along an equivalence of index types gives a star. -/
theorem IsHeteroSpecialSoundFamily.comp_equiv (h : IsHeteroSpecialSoundFamily k c)
    (e : Fin M ≃ Fin N) : IsHeteroSpecialSoundFamily k (c ∘ e) := by
  obtain ⟨hinj, c₀, hc⟩ := h
  refine ⟨hinj.comp e.injective, e.symm c₀, fun i => ?_⟩
  obtain ⟨J, hJ₀, hJcard, hJ⟩ := hc i
  refine ⟨J.map e.symm.toEmbedding, ?_, ?_, ?_⟩
  · simpa [Finset.mem_map_equiv] using hJ₀
  · simpa using hJcard
  · intro j hj
    rw [Finset.mem_map_equiv] at hj
    simpa using hJ (e j) (by simpa using hj)

/-- Being a star does not depend on how the index type is presented. -/
theorem isHeteroSpecialSoundFamily_comp_equiv_iff (e : Fin M ≃ Fin N) :
    IsHeteroSpecialSoundFamily k (c ∘ e) ↔ IsHeteroSpecialSoundFamily k c := by
  refine ⟨fun h => ?_, fun h => h.comp_equiv e⟩
  simpa [Function.comp_def] using h.comp_equiv e.symm

/-- A star with parameters `k` has at least `1 + ∑ u, (k u - 1)` members: the siblings of
different coordinates are different, and none is the centre. -/
theorem IsHeteroSpecialSoundFamily.card_ge (h : IsHeteroSpecialSoundFamily k c) :
    ∑ u, (k u - 1) + 1 ≤ N := by
  classical
  obtain ⟨_, e, hstar⟩ := h
  choose J hJe hJcard hJ using hstar
  have hdisj : (Set.univ : Set (Fin ℓ)).PairwiseDisjoint J := by
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro j hj hj'
    exact (hJ i' j hj').1 ((hJ i j hj).2 i' (Ne.symm hii'))
  have hcard : (insert e (Finset.univ.biUnion J)).card = ∑ u, (k u - 1) + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_biUnion (fun i _ i' _ hii' => hdisj trivial
      trivial hii')]
    · simp [hJcard]
    · simpa using fun i => hJe i
  calc ∑ u, (k u - 1) + 1 = (insert e (Finset.univ.biUnion J)).card := hcard.symm
    _ ≤ Fintype.card (Fin N) := Finset.card_le_univ _
    _ = N := Fintype.card_fin N

end Family

end CoordinateWise

/-! ## The structure on a protocol -/

variable {n : ℕ}

/-- A **heterogeneous coordinate-wise special-soundness structure** for a protocol `pSpec`. For
every challenge round `i` it gives the number `coordIndex i` of coordinates, an alphabet
`alphabet i u` and a parameter `soundnessParam i u` for each coordinate `u`, an identification of
the challenge with the coordinate vectors, and the resulting branching arity
`1 + ∑ u, (soundnessParam i u - 1)`. -/
structure HeteroCWSSStructure (pSpec : ProtocolSpec n) where
  /-- Number of coordinates of the `i`-th challenge. -/
  coordIndex : pSpec.ChallengeIdx → ℕ
  /-- Alphabet of coordinate `u` of the `i`-th challenge. -/
  alphabet : (i : pSpec.ChallengeIdx) → Fin (coordIndex i) → Type
  /-- Identification of the `i`-th challenge with its coordinate vectors. -/
  decompose : (i : pSpec.ChallengeIdx) →
    pSpec.Challenge i ≃ ((u : Fin (coordIndex i)) → alphabet i u)
  /-- Number of distinct values needed at coordinate `u` of the `i`-th challenge. -/
  soundnessParam : (i : pSpec.ChallengeIdx) → Fin (coordIndex i) → ℕ
  /-- Branching arity at the `i`-th challenge. -/
  arity : pSpec.ChallengeIdx → ℕ
  /-- The branching arity is `1 + ∑ u, (soundnessParam i u - 1)`. -/
  arity_eq : arity = fun i => ∑ u, (soundnessParam i u - 1) + 1

namespace HeteroCWSSStructure

variable {pSpec : ProtocolSpec n} (D : HeteroCWSSStructure pSpec)

/-- Every round of a heterogeneous structure branches at least once. -/
theorem arity_pos (i : pSpec.ChallengeIdx) : 0 < D.arity i := by
  rw [congrFun D.arity_eq i]
  exact Nat.succ_pos _

/-- The node predicate at a challenge round: the sibling challenges form a star. -/
def nodeOk (i : pSpec.ChallengeIdx) (challenges : Fin (D.arity i) → pSpec.Challenge i) : Prop :=
  CoordinateWise.IsHeteroSpecialSoundFamily (D.soundnessParam i)
    (fun j => D.decompose i (challenges j))

/-- The generic challenge-tree shape induced by a heterogeneous structure. -/
def toShape : ChallengeTreeShape pSpec where
  arity := D.arity
  nodeOk := D.nodeOk

/-- The number of leaves of a complete tree of the shape: the product of the arities. -/
def treeSize : ℕ :=
  ∏ i, D.arity i

/-- The sum over rounds and coordinates of the failure probability `(k - 1) / |X|` of collecting
`k` distinct values from an alphabet `X`. -/
def errorBound [∀ i u, Fintype (D.alphabet i u)] : ℚ≥0 :=
  ∑ i, ∑ u, ((D.soundnessParam i u - 1 : ℕ) : ℚ≥0) / Fintype.card (D.alphabet i u)

end HeteroCWSSStructure

/-! ## The homogeneous structure as a heterogeneous one -/

namespace CWSSStructure

variable {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)

/-- A homogeneous structure is a heterogeneous one with constant alphabets and parameters.

Marked `@[reducible]` so that instances on `D.alphabet i` (e.g. `Fintype`) are found for
`D.toHetero.alphabet i u`. -/
@[reducible]
def toHetero : HeteroCWSSStructure pSpec where
  coordIndex := fun i => D.ell i
  alphabet := fun i _ => D.alphabet i
  decompose := D.decompose
  soundnessParam := fun i _ => D.k i
  arity := D.arity
  arity_eq := by
    funext i
    simp [congrFun D.arity_eq i]

/-- The node predicates of `D` and of `D.toHetero` agree. -/
theorem toHetero_nodeOk_iff (i : pSpec.ChallengeIdx)
    (challenges : Fin (D.arity i) → pSpec.Challenge i) :
    D.toHetero.nodeOk i challenges ↔ D.nodeOk i challenges := by
  have hArity : D.arity i = D.ell i * (D.k i - 1) + 1 := congrFun D.arity_eq i
  unfold HeteroCWSSStructure.nodeOk nodeOk CoordinateWise.IsSpecialSoundFamily
  exact (CoordinateWise.isHeteroSpecialSoundFamily_comp_equiv_iff (finCongr hArity.symm)).symm

/-- The shape of `D.toHetero` is the shape of `D`. -/
theorem toHetero_toShape : D.toHetero.toShape = D.toShape :=
  ChallengeTreeShape.ext rfl
    (heq_of_eq (funext fun i => funext fun c => propext (D.toHetero_nodeOk_iff i c)))

/-- The number of leaves of a complete tree of a homogeneous structure. -/
theorem toHetero_treeSize : D.toHetero.treeSize = ∏ i, (D.ell i * (D.k i - 1) + 1) := by
  unfold HeteroCWSSStructure.treeSize
  exact Finset.prod_congr rfl fun i _ => congrFun D.arity_eq i

/-- The error bound of a homogeneous structure is `∑ i, ℓ i * (k i - 1) / |S i|`. -/
theorem toHetero_errorBound [∀ i, Fintype (D.alphabet i)] :
    D.toHetero.errorBound =
      ∑ i, ((D.ell i * (D.k i - 1) : ℕ) : ℚ≥0) / Fintype.card (D.alphabet i) := by
  unfold HeteroCWSSStructure.errorBound
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toHetero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact (mul_div_assoc _ _ _).symm

end CWSSStructure

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Tree special soundness at the shape of `D.toHetero` is coordinate-wise special soundness at
`D`. -/
theorem treeSpecialSound_toHetero_iff (D : CWSSStructure pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.treeSpecialSound init impl D.toHetero.toShape relIn relOut ↔
      verifier.coordinateWiseSpecialSound init impl D relIn relOut := by
  rw [CWSSStructure.toHetero_toShape]
  rfl

end Verifier
