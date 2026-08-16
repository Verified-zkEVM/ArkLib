/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# The geometric agreement hypergraph behind [CZ25]'s subspace-design bound

Machinery, not statements. To bound the list size of a subspace-designable code one counts
*agreements*: for a received word `y` and a finite set `T` of codewords, `agreementWeight y T` sums
`|{c ∈ T : cᵢ = yᵢ}| − 1` over the coordinates `i`. The subspace-design premise caps the same
quantity from above, because the codewords agreeing with `y` at `i` span a subspace of
`ker (proj i)`, and a design budgets `∑ᵢ dim (A ⊓ ker (proj i))`.

Turning that into a contradiction needs the geometric side of [CZ25]'s Lemma B.4: the *affine* rank
of a finite set (`geometricAffineRank`), a flag-level function on a basis (`basisFlagLevel`) with
the affine-independence lemmas it supports, a rank partition of a heavy set
(`GeometricRankPartition`, `exists_geometricRankPartition`), and the extraction of a *minimal*
linear-heavy subset (`exists_minimal_linear_heavy_subset`) whose minimality forces a lower bound on
`∑ᵢ` edge ranks. `agreementWeight_lt_of_subspaceDesign` assembles these into the strict inequality
the list-size bound contradicts.

Nothing here mentions `Lambda`: the development is about agreement counts and affine rank, and is
independent of list decoding.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and references.

## References

The keys cited here — [CZ25] — are resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which every file in this directory shares.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

section AgreementHypergraph

/-- The `i`-th **agreement edge**: the codewords in `T` that agree with the received word `y` at
coordinate `i`. One edge per coordinate presents `T` as a hypergraph. -/
def agreementEdges {ι : Type*} {A : Type*} [DecidableEq A]
    (T : Finset (ι → A)) (y : ι → A) (i : ι) : Finset (ι → A) :=
  T.filter (fun c => c i = y i)

theorem agreementEdges_inter_subset
    {ι : Type*} [Fintype ι] {A : Type*} [DecidableEq A]
    (T H : Finset (ι → A)) (y : ι → A) (i : ι)
    (hHT : H ⊆ T) :
    agreementEdges T y i ∩ H = agreementEdges H y i := by
  ext c
  simp only [agreementEdges, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcT, hci⟩, hcH⟩
    exact ⟨hcH, hci⟩
  · rintro ⟨hcH, hci⟩
    exact ⟨⟨hHT hcH, hci⟩, hcH⟩

open scoped BigOperators in
/-- The **agreement weight** of a codeword set `T` against a received word `y`:
`∑ᵢ (|agreementEdges T y i| − 1)`, the number of agreements beyond the first at each coordinate.
Natural subtraction, so a coordinate where at most one codeword agrees contributes `0`. -/
def agreementWeight {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (y : ι → A) (T : Finset (ι → A)) : ℕ :=
  ∑ i : ι, ((T.filter (fun c => c i = y i)).card - 1)

open scoped BigOperators in
/-- **The double-counting lower bound.** If every codeword in `S` is within relative distance `δ` of
`y`, then `S` forces agreement weight at least `|S| · n · (1 − δ) − n`: sum the per-codeword
agreement counts, exchange the order of summation, and pay one unit per coordinate for the `− 1` in
`agreementWeight`. -/
theorem agreementWeight_ge_of_hammingDist_le
    {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (δ : ℝ) (y : ι → A) (S : Finset (ι → A))
    (hdist : ∀ c ∈ S,
      (hammingDist c y : ℝ) ≤ δ * Fintype.card ι) :
    (S.card : ℝ) * Fintype.card ι * (1 - δ) - Fintype.card ι ≤
      (agreementWeight y S : ℝ) := by
  classical
  have hpoint : ∀ c ∈ S,
      (Fintype.card ι : ℝ) * (1 - δ) ≤ (Code.agree c y : ℝ) := by
    intro c hc
    have hcast : (Code.agree c y : ℝ) + hammingDist c y = Fintype.card ι := by
      exact_mod_cast (Code.agree_add_hammingDist (u := c) (v := y))
    nlinarith [hdist c hc]
  have hlower :
      (S.card : ℝ) * Fintype.card ι * (1 - δ) ≤
        ∑ c ∈ S, (Code.agree c y : ℝ) := by
    have hsum := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hsum
  have hdouble :
      (∑ c ∈ S, (Code.agree c y : ℝ)) =
        ∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ) := by
    unfold Code.agree
    simp_rw [Finset.natCast_card_filter]
    rw [Finset.sum_comm]
  have hfiber : ∀ i : ι,
      ((S.filter (fun c => c i = y i)).card : ℝ) ≤
        (((S.filter (fun c => c i = y i)).card - 1 : ℕ) : ℝ) + 1 := by
    intro i
    exact_mod_cast (show
      (S.filter (fun c => c i = y i)).card ≤
        (S.filter (fun c => c i = y i)).card - 1 + 1 by omega)
  have hupper :
      (∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ)) ≤
        (agreementWeight y S : ℝ) + Fintype.card ι := by
    calc
      (∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ)) ≤
          ∑ i : ι,
            ((((S.filter (fun c => c i = y i)).card - 1 : ℕ) : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => hfiber i
      _ = (agreementWeight y S : ℝ) + Fintype.card ι := by
        rw [Finset.sum_add_distrib]
        unfold agreementWeight
        rw [Nat.cast_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hdouble] at hlower
  linarith

/-- The **flag level** of `x` against a basis `b`: the least `k` such that `x` lies in the span of
the first `k` basis vectors, using `Module.Basis.flag`. It is `0` exactly when `x = 0`, and `j.succ`
at the basis vector `b j`, so a strictly monotone family of levels is linearly independent. -/
noncomputable def basisFlagLevel {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] {r : ℕ}
    (b : Module.Basis (Fin r) F V) (x : V) : Fin (r + 1) := by
  classical
  exact Finset.min'
    (Finset.univ.filter (fun k => x ∈ b.flag k))
    (by
      refine ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [b.flag_last]
      exact Submodule.mem_top)

theorem basisFlagLevel_le_of_mem
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) (k : Fin (r + 1))
    (hx : x ∈ b.flag k) : basisFlagLevel b x ≤ k := by
  classical
  unfold basisFlagLevel
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

theorem basisFlagLevel_mem_flag
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) :
    x ∈ b.flag (basisFlagLevel b x) := by
  classical
  unfold basisFlagLevel
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun k => x ∈ b.flag k))
    (by
      refine ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [b.flag_last]
      exact Submodule.mem_top)
  exact (Finset.mem_filter.mp hmem).2

theorem basisFlagLevel_basis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (j : Fin r) :
    basisFlagLevel b (b j) = j.succ := by
  apply le_antisymm
  · apply basisFlagLevel_le_of_mem
    exact b.self_mem_flag j.castSucc_lt_succ
  · have hmem := basisFlagLevel_mem_flag b (b j)
    have hlt : j.castSucc < basisFlagLevel b (b j) :=
      (b.self_mem_flag_iff).mp hmem
    have hne : j.succ ≠ 0 := Fin.succ_ne_zero j
    have hcast : ((j.succ).pred hne).castSucc < basisFlagLevel b (b j) := by
      simpa only [Fin.pred_succ] using hlt
    exact (Fin.castSucc_pred_lt_iff hne).mp hcast

theorem basisFlagLevel_eq_zero_iff
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) :
    basisFlagLevel b x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hmem := basisFlagLevel_mem_flag b x
    rw [h, b.flag_zero] at hmem
    exact hmem
  · intro hx
    subst x
    apply le_antisymm
    · exact basisFlagLevel_le_of_mem b 0 0 (by simp only [b.flag_zero, Submodule.mem_bot])
    · exact Fin.zero_le _

theorem basisFlagLevel_mem_iff_le
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) (k : Fin (r + 1)) :
    x ∈ b.flag k ↔ basisFlagLevel b x ≤ k := by
  constructor
  · exact basisFlagLevel_le_of_mem b x k
  · intro hle
    exact b.flag_mono hle (basisFlagLevel_mem_flag b x)

theorem exists_minimal_subset_property
    {V : Type*} [DecidableEq V] (P : Finset V → Prop)
    (S : Finset V) (hPS : P S) :
    ∃ T : Finset V, T ⊆ S ∧ P T ∧
      ∀ U : Finset V, U ⊂ T → ¬ P U := by
  classical
  let candidates : Finset (Finset V) := S.powerset.filter P
  have hnonempty : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hPS⟩
  obtain ⟨T, hTmin⟩ := candidates.exists_minimal hnonempty
  obtain ⟨hTmem, hminimal⟩ := minimal_iff.mp hTmin
  have hTS : T ⊆ S := (Finset.mem_powerset.mp
    (Finset.mem_filter.mp hTmem).1)
  have hPT : P T := (Finset.mem_filter.mp hTmem).2
  refine ⟨T, hTS, hPT, ?_⟩
  intro U hUT hPU
  have hUS : U ⊆ S := hUT.1.trans hTS
  have hUmem : U ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hUS, hPU⟩
  have heq : T = U := hminimal hUmem hUT.1
  apply hUT.2
  rw [heq]

/-- **Extraction of a minimal heavy subset.** From any `T` of size `≥ 2` whose weight is at least
`geometricEdgeWeight T · κ`, extract `U ⊆ T` still of size `≥ 2` and still heavy, but with *no*
proper subset of size `≥ 2` heavy. Minimality is what supplies the lower bound the design premise
then contradicts. -/
theorem exists_minimal_linear_heavy_subset
    {V : Type*} [DecidableEq V] (weight : Finset V → ℝ)
    (κ : ℝ) (S : Finset V) (hScard : 2 ≤ S.card)
    (hSheavy : (((S.card - 1 : ℕ) : ℝ)) * κ ≤ weight S) :
    ∃ T : Finset V, T ⊆ S ∧ 2 ≤ T.card ∧
      (((T.card - 1 : ℕ) : ℝ)) * κ ≤ weight T ∧
      ∀ U : Finset V, U ⊂ T → 2 ≤ U.card →
        weight U < (((U.card - 1 : ℕ) : ℝ)) * κ := by
  let P : Finset V → Prop := fun T =>
    2 ≤ T.card ∧ (((T.card - 1 : ℕ) : ℝ)) * κ ≤ weight T
  have hPS : P S := ⟨hScard, hSheavy⟩
  obtain ⟨T, hTS, hPT, hminimal⟩ :=
    exists_minimal_subset_property P S hPS
  refine ⟨T, hTS, hPT.1, hPT.2, ?_⟩
  intro U hUT hUcard
  have hnot := hminimal U hUT
  have hnle : ¬((((U.card - 1 : ℕ) : ℝ)) * κ ≤ weight U) := by
    intro hle
    exact hnot ⟨hUcard, hle⟩
  exact lt_of_not_ge hnle

/-- The **affine rank** of a finite set: the dimension of its `vectorSpan`, equivalently one less
than the size of a maximal affinely independent subset. -/
noncomputable def geometricAffineRank {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] (S : Finset V) : ℕ :=
  Module.finrank F (vectorSpan F (S : Set V))

/-- A **rank partition** of `S`: a partition into `geometricAffineRank S + 1` nonempty blocks such
that every subset `e ⊆ S` meets at most `geometricAffineRank e + 1` of them. The last field is what
converts a count of blocks met into a bound on affine rank. Constructed by
`selectedGeometricFlagRankPartition`; existence is `exists_geometricRankPartition`. -/
structure GeometricRankPartition {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    (S : Finset V) where
  blocks : Fin (geometricAffineRank (F := F) S + 1) → Finset V
  nonempty : ∀ a, (blocks a).Nonempty
  subset : ∀ a, blocks a ⊆ S
  disjoint : ∀ a b, a ≠ b → Disjoint (blocks a) (blocks b)
  cover : S = Finset.univ.biUnion blocks
  rank_bound : ∀ e : Finset V, e ⊆ S →
    (Finset.univ.filter (fun a => (e ∩ blocks a).Nonempty)).card ≤
      geometricAffineRank (F := F) e + 1

/-- A basis of `vectorSpan S` realised *inside* `S`: a base point `base ∈ S` together with witnesses
`witness i ∈ S` whose differences `witness i − base` are the basis vectors. Existence is
`exists_selectedGeometricFlagBasis`. -/
structure SelectedGeometricFlagBasis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) where
  base : V
  base_mem : base ∈ S
  basis : Module.Basis (Fin (geometricAffineRank (F := F) S)) F
    (vectorSpan F (S : Set V))
  witness : Fin (geometricAffineRank (F := F) S) → V
  witness_mem : ∀ i, witness i ∈ S
  basis_eq_vsub : ∀ i, ((basis i : vectorSpan F (S : Set V)) : V) =
    witness i - base

theorem exists_selectedGeometricFlagBasis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : S.Nonempty) :
    Nonempty (SelectedGeometricFlagBasis (F := F) S) := by
  classical
  obtain ⟨a, ha⟩ := hS
  let A : Submodule F V := vectorSpan F (S : Set V)
  let D : Finset V := (S.erase a).image (fun x => x - a)
  have hAD : A = Submodule.span F (D : Set V) := by
    dsimp [A, D]
    exact vectorSpan_eq_span_vsub_finset_right_ne F ha
  letI : FiniteDimensional F (Submodule.span F (D : Set V)) :=
    FiniteDimensional.span_of_finite F D.finite_toSet
  have hex := Submodule.exists_fun_fin_finrank_span_eq F (D : Set V)
  rw [← hAD] at hex
  obtain ⟨v, hvD, hspanv, hlinv⟩ := hex
  have hexw : ∀ i, ∃ x : V, x ∈ S ∧ v i = x - a := by
    intro i
    have hmem : v i ∈ D := hvD i
    dsimp [D] at hmem
    obtain ⟨x, hxer, hx⟩ := Finset.mem_image.mp hmem
    exact ⟨x, Finset.mem_of_mem_erase hxer, hx.symm⟩
  choose w hwS hvw using hexw
  have hvA : ∀ i, v i ∈ A := by
    intro i
    rw [← hspanv]
    exact Submodule.subset_span (Set.mem_range_self i)
  let lift : Fin (Module.finrank F A) → A := fun i => ⟨v i, hvA i⟩
  have hlinlift : LinearIndependent F lift := by
    apply LinearIndependent.of_comp A.subtype
    have hfun : A.subtype ∘ lift = v := by
      funext i
      rfl
    rw [hfun]
    exact hlinv
  have hspanlift : Submodule.span F (Set.range lift) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff A hvA).2 hspanv
  let b : Module.Basis (Fin (Module.finrank F A)) F A :=
    Module.Basis.mk hlinlift (by rw [hspanlift])
  have hb : ∀ i, ((b i : A) : V) = w i - a := by
    intro i
    dsimp [b]
    rw [Module.Basis.mk_apply]
    exact hvw i
  dsimp [A, geometricAffineRank] at b w hwS hb
  exact ⟨{
    base := a
    base_mem := ha
    basis := b
    witness := w
    witness_mem := hwS
    basis_eq_vsub := hb }⟩

theorem geometricAffineRank_pos_of_two_le_card
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : 2 ≤ S.card) :
    1 ≤ geometricAffineRank (F := F) S := by
  classical
  letI : FiniteDimensional F (vectorSpan F (S : Set V)) :=
    finiteDimensional_vectorSpan_of_finite F S.finite_toSet
  unfold geometricAffineRank
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hv := vsub_mem_vectorSpan F
    (show x ∈ (S : Set V) from hx) (show y ∈ (S : Set V) from hy)
  rw [hbot] at hv
  have hsub : x - y = 0 := hv
  exact hxy (sub_eq_zero.mp hsub)

/-- The **weight** of an edge: one less than its cardinality, truncated at `0`. It decomposes over a
rank partition up to a crossing term (`geometricEdgeWeight_partition_decomposition`). -/
def geometricEdgeWeight {V : Type*} (S : Finset V) : ℕ :=
  S.card - 1

theorem geometricAffineRank_le_edgeWeight
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) :
    geometricAffineRank (F := F) S ≤ geometricEdgeWeight S := by
  classical
  by_cases hS : S = ∅
  · subst S
    unfold geometricAffineRank geometricEdgeWeight
    rw [Finset.card_empty, Nat.zero_sub]
    have hempty : ((∅ : Finset V) : Set V) = ∅ := by
      ext x
      exact iff_of_false (Finset.notMem_empty x) (Set.notMem_empty x)
    rw [hempty, vectorSpan_empty, finrank_bot]
  · have hcard_pos : 0 < S.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hS)
    have hcard : S.card = (S.card - 1) + 1 := by omega
    have hle := finrank_vectorSpan_image_finset_le (k := F)
      (fun x : V => x) S hcard
    rw [Finset.image_id'] at hle
    exact hle

/-- The **crossing number** of `e` against a rank partition: one less than the number of blocks `e`
meets. Bounded above by `geometricAffineRank e` — that is exactly the partition's `rank_bound`
field, repackaged as `geometricPartitionCrossing_le_affineRank`. -/
noncomputable def geometricPartitionCrossing {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (e : Finset V) : ℕ :=
  (Finset.univ.filter (fun a => (e ∩ P.blocks a).Nonempty)).card - 1

open scoped BigOperators in
theorem geometricEdgeWeight_partition_decomposition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (e : Finset V) (he : e ⊆ S) :
    geometricEdgeWeight e =
      (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) +
        geometricPartitionCrossing P e := by
  classical
  let q : ℕ :=
    (Finset.univ.filter (fun a => (e ∩ P.blocks a).Nonempty)).card
  have hpair : ((Finset.univ : Finset
      (Fin (geometricAffineRank (F := F) S + 1))) : Set _).PairwiseDisjoint
      (fun a => e ∩ P.blocks a) := by
    intro a _ b _ hab
    exact (P.disjoint a b hab).mono Finset.inter_subset_right
      Finset.inter_subset_right
  have hcover : Finset.univ.biUnion (fun a => e ∩ P.blocks a) = e := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, _, hxi⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxi).1
    · intro hx
      have hxS : x ∈ S := he hx
      rw [P.cover] at hxS
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxS
      exact Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_inter.mpr ⟨hx, hxa⟩⟩
  have hsum_card :
      (∑ a, (e ∩ P.blocks a).card) = e.card := by
    have hc := Finset.card_biUnion hpair
    rw [hcover] at hc
    simpa only using hc.symm
  have hpoint : ∀ a : Fin (geometricAffineRank (F := F) S + 1),
      geometricEdgeWeight (e ∩ P.blocks a) +
        (if (e ∩ P.blocks a).Nonempty then 1 else 0) =
          (e ∩ P.blocks a).card := by
    intro a
    unfold geometricEdgeWeight
    by_cases hne : (e ∩ P.blocks a).Nonempty
    · rw [if_pos hne]
      have hpos := Finset.card_pos.mpr hne
      omega
    · rw [if_neg hne]
      have hz : (e ∩ P.blocks a).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      omega
  have hindicator :
      (∑ a : Fin (geometricAffineRank (F := F) S + 1),
        if (e ∩ P.blocks a).Nonempty then 1 else 0) = q := by
    unfold q
    rw [Finset.card_filter]
  have hsum : (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) + q = e.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      (∑ a, (geometricEdgeWeight (e ∩ P.blocks a) +
          if (e ∩ P.blocks a).Nonempty then 1 else 0)) =
          ∑ a, (e ∩ P.blocks a).card :=
        Finset.sum_congr rfl fun a _ => hpoint a
      _ = e.card := hsum_card
  unfold geometricPartitionCrossing
  change geometricEdgeWeight e =
    (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) + (q - 1)
  unfold geometricEdgeWeight at hsum ⊢
  by_cases hene : e.Nonempty
  · obtain ⟨x, hx⟩ := hene
    have hxS : x ∈ S := he hx
    rw [P.cover] at hxS
    obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hxS
    have hqpos : 0 < q := by
      rw [Finset.card_pos]
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ?_⟩⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hxa⟩⟩
    have hepos : 0 < e.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · have he0 : e.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hene)
    have hsum0 :
        (∑ a, ((e ∩ P.blocks a).card - 1)) + q = 0 := by
      simpa only [he0] using hsum
    omega

theorem geometricPartitionCrossing_le_affineRank
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (e : Finset V) (he : e ⊆ S) :
    geometricPartitionCrossing P e ≤ geometricAffineRank (F := F) e := by
  unfold geometricPartitionCrossing
  have h := P.rank_bound e he
  omega

theorem geometricRankPartition_blocks_ssubset
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (hS : 2 ≤ S.card) :
    ∀ a, P.blocks a ⊂ S := by
  have hrank := geometricAffineRank_pos_of_two_le_card (F := F) S hS
  have hidx : 1 < Fintype.card
      (Fin (geometricAffineRank (F := F) S + 1)) := by
    rw [Fintype.card_fin]
    omega
  intro a
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hidx a
  obtain ⟨x, hxb⟩ := P.nonempty b
  refine ⟨P.subset a, ?_⟩
  intro hSa
  have hxS : x ∈ S := P.subset b hxb
  have hxa : x ∈ P.blocks a := hSa hxS
  exact (Finset.disjoint_left.mp (P.disjoint a b hba.symm)) hxa hxb

open scoped BigOperators in
theorem geometricRankPartition_sum_blockWeight
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) :
    (∑ a, geometricEdgeWeight (P.blocks a)) =
      geometricEdgeWeight S - geometricAffineRank (F := F) S := by
  classical
  have hdecomp := geometricEdgeWeight_partition_decomposition P S
    (Finset.Subset.rfl)
  have hinter : ∀ a : Fin (geometricAffineRank (F := F) S + 1),
      S ∩ P.blocks a = P.blocks a := by
    intro a
    exact Finset.inter_eq_right.mpr (P.subset a)
  simp_rw [hinter] at hdecomp
  have hfilter :
      Finset.univ.filter (fun a => (S ∩ P.blocks a).Nonempty) =
        (Finset.univ : Finset (Fin (geometricAffineRank (F := F) S + 1))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hinter a]
    exact iff_true_intro (P.nonempty a)
  have hcross : geometricPartitionCrossing P S =
      geometricAffineRank (F := F) S := by
    unfold geometricPartitionCrossing
    rw [hfilter, Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcross] at hdecomp
  have hle := geometricAffineRank_le_edgeWeight (F := F) S
  omega

open scoped BigOperators in
/-- The total edge weight of a hypergraph `E` restricted to `S`: `∑ᵢ geometricEdgeWeight (E i ∩ S)`.
For the agreement edges this *is* the agreement weight
(`agreementWeight_eq_geometricTotalWeight`). -/
def geometricTotalWeight {ι : Type*} {V : Type*} [Fintype ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset V) : ℕ :=
  ∑ i : ι, geometricEdgeWeight (E i ∩ S)

open scoped BigOperators in
theorem agreementWeight_eq_geometricTotalWeight
    {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (y : ι → A) (T : Finset (ι → A)) :
    agreementWeight y T = geometricTotalWeight (agreementEdges T y) T := by
  unfold agreementWeight geometricTotalWeight geometricEdgeWeight agreementEdges
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]

open scoped BigOperators in
theorem geometricTotalWeight_eq_zero_of_card_le_one
    {ι : Type*} {V : Type*} [Fintype ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset V) (hS : S.card ≤ 1) :
    geometricTotalWeight E S = 0 := by
  unfold geometricTotalWeight
  apply Finset.sum_eq_zero
  intro i _
  unfold geometricEdgeWeight
  have hcard : (E i ∩ S).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hS
  omega

open scoped BigOperators in
theorem geometricTotalWeight_partition_decomposition
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) :
    geometricTotalWeight E S =
      (∑ a, geometricTotalWeight E (P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
  classical
  have hinter : ∀ (i : ι) (a : Fin (geometricAffineRank (F := F) S + 1)),
      (E i ∩ S) ∩ P.blocks a = E i ∩ P.blocks a := by
    intro i a
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hxe, _⟩, hxb⟩
      exact ⟨hxe, hxb⟩
    · rintro ⟨hxe, hxb⟩
      exact ⟨⟨hxe, P.subset a hxb⟩, hxb⟩
  unfold geometricTotalWeight
  calc
    (∑ i : ι, geometricEdgeWeight (E i ∩ S)) =
        ∑ i : ι, ((∑ a, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
          geometricPartitionCrossing P (E i ∩ S)) := by
      exact Finset.sum_congr rfl fun i _ =>
        geometricEdgeWeight_partition_decomposition P (E i ∩ S)
          Finset.inter_subset_right
    _ = (∑ i : ι, ∑ a, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ i : ι, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      rw [Finset.sum_comm]
    _ = (∑ a, ∑ i : ι, geometricEdgeWeight (E i ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      have hdouble :
          (∑ a, ∑ i : ι, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) =
            ∑ a, ∑ i : ι, geometricEdgeWeight (E i ∩ P.blocks a) := by
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun i _ => congrArg geometricEdgeWeight (hinter i a)
      rw [hdouble]

theorem linearIndependent_of_strictMono_basisFlagLevels
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r n : ℕ} (b : Module.Basis (Fin r) F V)
    (v : Fin n → V) (level : Fin n → Fin (r + 1))
    (hlevel : StrictMono level) (hpos : ∀ i, level i ≠ 0)
    (hv : ∀ i, basisFlagLevel b (v i) = level i) :
    LinearIndependent F v := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      rw [linearIndependent_finSucc']
      constructor
      · apply ih (v := Fin.init v) (level := fun i => level i.castSucc)
        · intro i j hij
          exact hlevel (Fin.castSucc_lt_castSucc_iff.mpr hij)
        · intro i
          exact hpos i.castSucc
        · intro i
          change basisFlagLevel b (v i.castSucc) = level i.castSucc
          exact hv i.castSucc
      · intro hspan
        let k : Fin (r + 1) := level (Fin.last n)
        have hk : k ≠ 0 := hpos (Fin.last n)
        let predK : Fin (r + 1) := (k.pred hk).castSucc
        have hspan_le : Submodule.span F (Set.range (Fin.init v)) ≤ b.flag predK := by
          rw [Submodule.span_le]
          intro x hx
          rcases hx with ⟨i, rfl⟩
          change v i.castSucc ∈ b.flag predK
          rw [basisFlagLevel_mem_iff_le, hv]
          have hlt : level i.castSucc < k :=
            hlevel (Fin.castSucc_lt_last i)
          change (level i.castSucc).val ≤ (k.pred hk).val
          rw [Fin.val_pred]
          omega
        have hlast : v (Fin.last n) ∉ b.flag predK := by
          rw [basisFlagLevel_mem_iff_le, hv]
          intro hle
          have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk
          change k.val ≤ (k.pred hk).val at hle
          rw [Fin.val_pred] at hle
          omega
        exact hlast (hspan_le hspan)

theorem affineIndependent_of_basisFlagLevels
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V)
    (p : Fin (r + 1) → V)
    (hp : ∀ i, basisFlagLevel b (p i) = i) :
    AffineIndependent F p := by
  have hp0 : p 0 = 0 :=
    (basisFlagLevel_eq_zero_iff b (p 0)).mp (hp 0)
  have hlin : LinearIndependent F (fun i : Fin r => p i.succ) := by
    apply linearIndependent_of_strictMono_basisFlagLevels b
      (fun i : Fin r => p i.succ) (fun i : Fin r => i.succ)
    · exact Fin.strictMono_succ
    · intro i
      exact Fin.succ_ne_zero i
    · intro i
      exact hp i.succ
  rw [affineIndependent_iff_linearIndependent_vsub F p 0]
  let e := finSuccAboveEquiv (0 : Fin (r + 1))
  let q : {x : Fin (r + 1) // x ≠ 0} → V :=
    fun i => p i.1 -ᵥ p 0
  have hcomp : q ∘ e = fun i : Fin r => p i.succ := by
    funext i
    change p ((e i).1) - p 0 = p i.succ
    rw [hp0, sub_zero]
    change p ((0 : Fin (r + 1)).succAbove i) = p i.succ
    rw [Fin.succAbove_zero_apply]
  exact (linearIndependent_equiv' (R := F) e hcomp).mp hlin

open scoped BigOperators in
theorem minimal_linear_heavy_crossing_lower
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) (κ : ℝ)
    (hblocks : ∀ a, P.blocks a ⊂ S)
    (hheavy : (geometricEdgeWeight S : ℝ) * κ ≤
      (geometricTotalWeight E S : ℝ))
    (hminimal : ∀ U : Finset V, U ⊂ S → 2 ≤ U.card →
      (geometricTotalWeight E U : ℝ) <
        (geometricEdgeWeight U : ℝ) * κ) :
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
      ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) := by
  classical
  have hblock : ∀ a, (geometricTotalWeight E (P.blocks a) : ℝ) ≤
      (geometricEdgeWeight (P.blocks a) : ℝ) * κ := by
    intro a
    by_cases hcard : (P.blocks a).card ≤ 1
    · have hzero := geometricTotalWeight_eq_zero_of_card_le_one
        E (P.blocks a) hcard
      have hwzero : geometricEdgeWeight (P.blocks a) = 0 := by
        unfold geometricEdgeWeight
        omega
      rw [hzero, hwzero]
      norm_num
    · have htwo : 2 ≤ (P.blocks a).card := by omega
      exact (hminimal (P.blocks a) (hblocks a) htwo).le
  have hsum_blocks :
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
        ∑ a, (geometricEdgeWeight (P.blocks a) : ℝ) * κ :=
    Finset.sum_le_sum fun a _ => hblock a
  have hsum_weight_nat := geometricRankPartition_sum_blockWeight P
  have hrank_le := geometricAffineRank_le_edgeWeight (F := F) S
  have hsum_weight :
      (∑ a, (geometricEdgeWeight (P.blocks a) : ℝ)) =
        (geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ) := by
    rw [← Nat.cast_sum, hsum_weight_nat, Nat.cast_sub hrank_le]
  have hsum_blocks' :
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
        ((geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ)) * κ := by
    calc
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
          ∑ a, (geometricEdgeWeight (P.blocks a) : ℝ) * κ := hsum_blocks
      _ = (∑ a, (geometricEdgeWeight (P.blocks a) : ℝ)) * κ := by
        rw [Finset.sum_mul]
      _ = ((geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ)) * κ := by
        rw [hsum_weight]
  have hdecomp_nat := geometricTotalWeight_partition_decomposition P E
  have hdecomp : (geometricTotalWeight E S : ℝ) =
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) +
        ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) := by
    exact_mod_cast hdecomp_nat
  linarith

open scoped BigOperators in
theorem minimal_linear_heavy_affineRank_lower_of_partition
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) (κ : ℝ) (hS : 2 ≤ S.card)
    (hheavy : (geometricEdgeWeight S : ℝ) * κ ≤
      (geometricTotalWeight E S : ℝ))
    (hminimal : ∀ U : Finset V, U ⊂ S → 2 ≤ U.card →
      (geometricTotalWeight E U : ℝ) <
        (geometricEdgeWeight U : ℝ) * κ) :
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
      ∑ i : ι, (geometricAffineRank (F := F) (E i ∩ S) : ℝ) := by
  calc
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
        ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) :=
      minimal_linear_heavy_crossing_lower P E κ
        (geometricRankPartition_blocks_ssubset P hS) hheavy hminimal
    _ ≤ ∑ i : ι, (geometricAffineRank (F := F) (E i ∩ S) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast geometricPartitionCrossing_le_affineRank P (E i ∩ S)
        Finset.inter_subset_right

/-- The block index of `x` in the partition induced by a selected flag basis: the flag level of
`x − B.base`, and `0` for points outside `S`. -/
noncomputable def selectedGeometricFlagPart
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) (x : V) :
    Fin (geometricAffineRank (F := F) S + 1) :=
  if hx : x ∈ S then
    basisFlagLevel B.basis
      ⟨x - B.base, vsub_mem_vectorSpan F hx B.base_mem⟩
  else 0

theorem affineIndependent_of_selectedGeometricFlagPart_transversal
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (p : Fin (geometricAffineRank (F := F) S + 1) → V)
    (hpS : ∀ i, p i ∈ S)
    (hpPart : ∀ i, selectedGeometricFlagPart B (p i) = i) :
    AffineIndependent F p := by
  let A : Submodule F V := vectorSpan F (S : Set V)
  let q : Fin (geometricAffineRank (F := F) S + 1) → A :=
    fun i => ⟨p i - B.base, vsub_mem_vectorSpan F (hpS i) B.base_mem⟩
  have hqLevel : ∀ i, basisFlagLevel B.basis (q i) = i := by
    intro i
    have h := hpPart i
    unfold selectedGeometricFlagPart at h
    rw [dif_pos (hpS i)] at h
    exact h
  have hqAI : AffineIndependent F q :=
    affineIndependent_of_basisFlagLevels B.basis q hqLevel
  have hdiff : AffineIndependent F (fun i => p i - B.base) := by
    have hmap := hqAI.map' A.subtype.toAffineMap A.subtype_injective
    have hfun : (fun i => p i - B.base) = A.subtype.toAffineMap ∘ q := by
      funext i
      rfl
    rw [hfun]
    exact hmap
  have htrans := hdiff.vadd F (v := B.base)
  convert htrans using 1
  funext i
  rw [Pi.vadd_apply, vadd_eq_add]
  exact (add_sub_cancel B.base (p i)).symm

theorem selectedGeometricFlagPart_base
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    selectedGeometricFlagPart B B.base = 0 := by
  unfold selectedGeometricFlagPart
  rw [dif_pos B.base_mem]
  rw [basisFlagLevel_eq_zero_iff]
  apply Subtype.ext
  simp only [sub_self, Submodule.coe_zero]

theorem selectedGeometricFlagPart_witness
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (i : Fin (geometricAffineRank (F := F) S)) :
    selectedGeometricFlagPart B (B.witness i) = i.succ := by
  unfold selectedGeometricFlagPart
  rw [dif_pos (B.witness_mem i)]
  have heq :
      (⟨B.witness i - B.base,
        vsub_mem_vectorSpan F (B.witness_mem i) B.base_mem⟩ :
          vectorSpan F (S : Set V)) = B.basis i := by
    apply Subtype.ext
    exact (B.basis_eq_vsub i).symm
  rw [heq]
  exact basisFlagLevel_basis B.basis i

/-- A representative in `S` for each block index: the base point at `0`, and the `i`-th witness at
`i.succ`. It lands in its own block (`selectedGeometricFlagPart_rep`), which is what makes every
block nonempty. -/
noncomputable def selectedGeometricFlagRep
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    Fin (geometricAffineRank (F := F) S + 1) → V :=
  Fin.cases B.base B.witness

theorem selectedGeometricFlagPart_rep
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    ∀ i, selectedGeometricFlagPart B (selectedGeometricFlagRep B i) = i := by
  intro i
  refine Fin.cases (selectedGeometricFlagPart_base B) (fun j => ?_) i
  exact selectedGeometricFlagPart_witness B j

theorem selectedGeometricFlagRep_mem
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    ∀ i, selectedGeometricFlagRep B i ∈ S := by
  intro i
  refine Fin.cases B.base_mem (fun j => ?_) i
  exact B.witness_mem j

theorem selectedGeometricFlagPart_image_card_le
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (E : Finset V) (hES : E ⊆ S) :
    (E.image (selectedGeometricFlagPart B)).card ≤
      geometricAffineRank (F := F) E + 1 := by
  classical
  let part := selectedGeometricFlagPart B
  let J : Finset (Fin (geometricAffineRank (F := F) S + 1)) := E.image part
  have hex : ∀ j : (J : Set _), ∃ x : V, x ∈ E ∧ part x = j.1 := by
    intro j
    have hj : j.1 ∈ E.image part := j.2
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hj
    exact ⟨x, hx, heq⟩
  choose pick hpickE hpickPart using hex
  let p : Fin (geometricAffineRank (F := F) S + 1) → V := fun j =>
    if hj : j ∈ J then pick ⟨j, hj⟩ else selectedGeometricFlagRep B j
  have hpS : ∀ j, p j ∈ S := by
    intro j
    by_cases hj : j ∈ J
    · rw [show p j = pick ⟨j, hj⟩ by simp only [p, dif_pos hj]]
      exact hES (hpickE ⟨j, hj⟩)
    · rw [show p j = selectedGeometricFlagRep B j by simp only [p, dif_neg hj]]
      exact selectedGeometricFlagRep_mem B j
  have hpPart : ∀ j, selectedGeometricFlagPart B (p j) = j := by
    intro j
    by_cases hj : j ∈ J
    · rw [show p j = pick ⟨j, hj⟩ by simp only [p, dif_pos hj]]
      exact hpickPart ⟨j, hj⟩
    · rw [show p j = selectedGeometricFlagRep B j by simp only [p, dif_neg hj]]
      exact selectedGeometricFlagPart_rep B j
  have hpAI : AffineIndependent F p :=
    affineIndependent_of_selectedGeometricFlagPart_transversal B p hpS hpPart
  have hpickAI : AffineIndependent F pick := by
    have hsub := hpAI.subtype (J : Set _)
    convert hsub using 1
    funext j
    have hj : j.1 ∈ J := j.2
    have hval : p j.1 = pick j := by
      dsimp [p]
      rw [if_pos hj]
    exact hval.symm
  have hcard := hpickAI.card_le_finrank_succ
  have hrange : Set.range pick ⊆ (E : Set V) := by
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact hpickE j
  have hspan : vectorSpan F (Set.range pick) ≤ vectorSpan F (E : Set V) :=
    vectorSpan_mono F hrange
  letI : FiniteDimensional F (vectorSpan F (E : Set V)) :=
    finiteDimensional_vectorSpan_of_finite F E.finite_toSet
  have hfin := Submodule.finrank_mono hspan
  calc
    (E.image (selectedGeometricFlagPart B)).card = J.card := by
      rfl
    _ = Fintype.card J := (Fintype.card_coe J).symm
    _ ≤ Module.finrank F (vectorSpan F (Set.range pick)) + 1 := hcard
    _ ≤ Module.finrank F (vectorSpan F (E : Set V)) + 1 :=
      Nat.add_le_add_right hfin 1
    _ = geometricAffineRank (F := F) E + 1 := rfl

/-- The rank partition of `S` induced by a selected flag basis: block `a` collects the points of
flag level `a`. This is the witness behind `exists_geometricRankPartition`, and its `rank_bound`
comes from the affine independence of a transversal of the levels a subset meets. -/
noncomputable def selectedGeometricFlagRankPartition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    GeometricRankPartition (F := F) S where
  blocks a := S.filter (fun x => selectedGeometricFlagPart B x = a)
  nonempty a := by
    refine ⟨selectedGeometricFlagRep B a, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨selectedGeometricFlagRep_mem B a, selectedGeometricFlagPart_rep B a⟩
  subset a := Finset.filter_subset _ _
  disjoint a b hab := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have ha := (Finset.mem_filter.mp hxa).2
    have hb := (Finset.mem_filter.mp hxb).2
    exact hab (ha.symm.trans hb)
  cover := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_biUnion.mpr
        ⟨selectedGeometricFlagPart B x, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · intro hx
      obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hxa).1
  rank_bound e he := by
    have hfilter :
        Finset.univ.filter
            (fun a => (e ∩ S.filter
              (fun x => selectedGeometricFlagPart B x = a)).Nonempty) =
          e.image (selectedGeometricFlagPart B) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨x, hx⟩
        have hxe := (Finset.mem_inter.mp hx).1
        have hpart := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
        exact ⟨x, hxe, hpart⟩
      · rintro ⟨x, hxe, hpart⟩
        refine ⟨x, Finset.mem_inter.mpr ⟨hxe, ?_⟩⟩
        exact Finset.mem_filter.mpr ⟨he hxe, hpart⟩
    rw [hfilter]
    exact selectedGeometricFlagPart_image_card_le B e he

/-- **Every nonempty finite set admits a rank partition.** Obtained from a flag basis realised
inside the set. -/
theorem exists_geometricRankPartition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : S.Nonempty) :
    Nonempty (GeometricRankPartition (F := F) S) := by
  obtain ⟨B⟩ := exists_selectedGeometricFlagBasis (F := F) S hS
  exact ⟨selectedGeometricFlagRankPartition B⟩

open scoped BigOperators in
/-- The subspace-design premise, in the form the counting argument consumes: for any subspace `A` of
the code, `∑ᵢ dim (A ⊓ ker (proj i)) ≤ n · dim A · τ (dim A)`. -/
theorem subspaceDesign_kernelSum_le_profile
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] {s : ℕ} {τ : ℕ → ℝ}
    (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (A : Submodule F (ι → Fin s → F)) (hAC : A ≤ C) :
    (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
      (Fintype.card ι : ℝ) * (Module.finrank F A : ℝ) *
        τ (Module.finrank F A) := by
  have h := hdesign (Module.finrank F A) A hAC le_rfl
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at h
  calc
    (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
        (Module.finrank F A : ℝ) * τ (Module.finrank F A) *
          Fintype.card ι := h
    _ = (Fintype.card ι : ℝ) * (Module.finrank F A : ℝ) *
        τ (Module.finrank F A) := by ring

open scoped Pointwise in
theorem vectorSpan_agreementEdges_le_inf_ker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] [DecidableEq F]
    (s : ℕ) (T : Finset (ι → Fin s → F)) (f : ι → Fin s → F) (i : ι) :
    vectorSpan F (agreementEdges T f i : Set (ι → Fin s → F)) ≤
      vectorSpan F (T : Set (ι → Fin s → F)) ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
  classical
  apply le_inf
  · apply vectorSpan_mono
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  · rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    rcases Set.mem_vsub.mp hz with ⟨c₁, hc₁, c₂, hc₂, heq⟩
    unfold agreementEdges at hc₁ hc₂
    have h₁ : c₁ i = f i := (Finset.mem_filter.mp hc₁).2
    have h₂ : c₂ i = f i := (Finset.mem_filter.mp hc₂).2
    rw [← heq]
    change c₁ i - c₂ i = 0
    rw [h₁, h₂, sub_self]

theorem vectorSpan_finset_le_submodule_of_subset
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (C : Submodule F V)
    (hSC : ∀ x ∈ S, x ∈ C) :
    vectorSpan F (S : Set V) ≤ C := by
  classical
  by_cases hS : S = ∅
  · subst S
    rw [Finset.coe_empty, vectorSpan_empty]
    exact bot_le
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [vectorSpan_eq_span_vsub_finset_right_ne (k := F) hp, Submodule.span_le]
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    change x - p ∈ C
    exact C.sub_mem (hSC x (Finset.mem_of_mem_erase hx)) (hSC p hp)

open scoped BigOperators in
/-- **The subspace-design agreement bound.** If `τ` stays below `t` on `1 ≤ r ≤ d` and `T` is a set
of at most `d + 1` codewords of a `τ`-design, then the agreement weight of `T` against any word is
*strictly* less than `n · (|T| − 1) · t`.

Two bounds on the same quantity meet: a minimal heavy subset `U` forces the sum of the edge affine
ranks to be at least `geometricAffineRank U · n · t`, while `vectorSpan_agreementEdges_le_inf_ker`
sends those ranks into `∑ᵢ dim (A ⊓ ker (proj i))` for `A = vectorSpan U`, which the design premise
caps at `n · dim A · τ (dim A)`. -/
theorem agreementWeight_lt_of_subspaceDesign
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [DecidableEq F]
    {s : ℕ} {τ : ℕ → ℝ} {C : Submodule F (ι → Fin s → F)}
    (hdesign : IsSubspaceDesign s τ C)
    (d : ℕ) (t : ℝ)
    (hτ : ∀ r : ℕ, 1 ≤ r → r ≤ d → τ r < t)
    (y : ι → Fin s → F) (T : Finset (ι → Fin s → F))
    (hcard2 : 2 ≤ T.card) (hcardd : T.card ≤ d + 1)
    (hTC : ∀ c ∈ T, c ∈ C) :
    (agreementWeight y T : ℝ) <
      (Fintype.card ι : ℝ) * (T.card - 1) * t := by
  classical
  by_contra hnot
  let E : ι → Finset (ι → Fin s → F) := agreementEdges T y
  let κ : ℝ := (Fintype.card ι : ℝ) * t
  have hge : (Fintype.card ι : ℝ) * (T.card - 1) * t ≤
      (agreementWeight y T : ℝ) := le_of_not_gt hnot
  have hcastT : ((T.card - 1 : ℕ) : ℝ) = (T.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ T.card)]
    norm_num
  have hheavyT : (geometricEdgeWeight T : ℝ) * κ ≤
      (geometricTotalWeight E T : ℝ) := by
    calc
      (geometricEdgeWeight T : ℝ) * κ =
          (Fintype.card ι : ℝ) * ((T.card : ℝ) - 1) * t := by
        unfold geometricEdgeWeight κ
        rw [hcastT]
        ring
      _ ≤ (agreementWeight y T : ℝ) := hge
      _ = (geometricTotalWeight E T : ℝ) := by
        exact_mod_cast agreementWeight_eq_geometricTotalWeight y T
  obtain ⟨U, hUT, hU2, hUheavy, hUmin⟩ :=
    exists_minimal_linear_heavy_subset
      (fun X => (geometricTotalWeight E X : ℝ)) κ T hcard2 hheavyT
  have hUne : U.Nonempty :=
    Finset.card_pos.mp (show 0 < U.card by omega)
  obtain ⟨P⟩ := exists_geometricRankPartition (F := F) U hUne
  have hlower := minimal_linear_heavy_affineRank_lower_of_partition
    P E κ hU2 hUheavy hUmin
  have hinter : ∀ i : ι, E i ∩ U = agreementEdges U y i := by
    intro i
    exact agreementEdges_inter_subset T U y i hUT
  simp_rw [hinter] at hlower
  let A : Submodule F (ι → Fin s → F) :=
    vectorSpan F (↑U : Set (ι → Fin s → F))
  have hAC : A ≤ C := by
    apply vectorSpan_finset_le_submodule_of_subset
    intro c hc
    exact hTC c (hUT hc)
  letI : FiniteDimensional F A :=
    finiteDimensional_vectorSpan_of_finite F U.finite_toSet
  have hsum :
      (∑ i : ι, (geometricAffineRank (F := F) (agreementEdges U y i) : ℝ)) ≤
        ∑ i : ι, (Module.finrank F
          ↥(A ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hspan := vectorSpan_agreementEdges_le_inf_ker s U y i
    change (Module.finrank F (vectorSpan F
      (agreementEdges U y i : Set (ι → Fin s → F))) : ℝ) ≤ _
    exact_mod_cast Submodule.finrank_mono hspan
  have hupper := subspaceDesign_kernelSum_le_profile C hdesign A hAC
  change (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
        τ (geometricAffineRank (F := F) U) at hupper
  have hrpos : 1 ≤ geometricAffineRank (F := F) U :=
    geometricAffineRank_pos_of_two_le_card U hU2
  have hrle_weight := geometricAffineRank_le_edgeWeight (F := F) U
  have hcardU : U.card ≤ T.card := Finset.card_le_card hUT
  have hrle : geometricAffineRank (F := F) U ≤ d := by
    unfold geometricEdgeWeight at hrle_weight
    omega
  have hτr := hτ (geometricAffineRank (F := F) U) hrpos hrle
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hrreal : (0 : ℝ) < geometricAffineRank (F := F) U := by
    exact_mod_cast hrpos
  have hnr : (0 : ℝ) < (Fintype.card ι : ℝ) *
      (geometricAffineRank (F := F) U : ℝ) := mul_pos hn hrreal
  have hstrict :
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
          τ (geometricAffineRank (F := F) U) <
        (geometricAffineRank (F := F) U : ℝ) * κ := by
    calc
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
          τ (geometricAffineRank (F := F) U) <
          ((Fintype.card ι : ℝ) *
            (geometricAffineRank (F := F) U : ℝ)) * t :=
        mul_lt_mul_of_pos_left hτr hnr
      _ = (geometricAffineRank (F := F) U : ℝ) * κ := by
        unfold κ
        ring
  have hchain : (geometricAffineRank (F := F) U : ℝ) * κ ≤
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
        τ (geometricAffineRank (F := F) U) :=
    hlower.trans (hsum.trans hupper)
  exact (not_lt_of_ge hchain) hstrict

/-- `agreementWeight_lt_of_subspaceDesign` at the rate-derived profile
`τ(r) = (s·R − 1/n) / (s − r + 1)`: a set of `d + 1` codewords has agreement weight strictly less
than `n · d · (s·R / (s − d + 1))`. -/
theorem agreementWeight_lt_of_subspaceDesign_rate
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [DecidableEq F]
    {s : ℕ} {R : ℝ} {C : Submodule F (ι → Fin s → F)}
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (hdesign : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (d : ℕ) (hdpos : 1 ≤ d) (hds : d ≤ s)
    (y : ι → Fin s → F) (T : Finset (ι → Fin s → F))
    (hcard : T.card = d + 1) (hTC : ∀ c ∈ T, c ∈ C) :
    (agreementWeight y T : ℝ) <
      (Fintype.card ι : ℝ) * d *
        (s * R / ((s : ℝ) - d + 1)) := by
  have hR0 : (0 : ℝ) ≤ R := by
    rw [← hR]
    positivity
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hτ : ∀ r : ℕ, 1 ≤ r → r ≤ d →
      (if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) <
        s * R / ((s : ℝ) - d + 1) := by
    intro r hrpos hrle
    have hrs : r ≤ s := hrle.trans hds
    rw [if_pos (Finset.mem_Icc.mpr ⟨hrpos, hrs⟩)]
    have hdenr : (0 : ℝ) < (s : ℝ) - r + 1 := by
      exact_mod_cast (show 0 < s - r + 1 by omega)
    have hdend : (0 : ℝ) < (s : ℝ) - d + 1 := by
      exact_mod_cast (show 0 < s - d + 1 by omega)
    have hinv : (0 : ℝ) < 1 / Fintype.card ι := one_div_pos.mpr hn
    have hnum : (s : ℝ) * R - 1 / Fintype.card ι < (s : ℝ) * R := by
      linarith
    have hfirst :
        ((s : ℝ) * R - 1 / Fintype.card ι) / ((s : ℝ) - r + 1) <
          (s : ℝ) * R / ((s : ℝ) - r + 1) :=
      div_lt_div_of_pos_right hnum hdenr
    have hdenle : (s : ℝ) - d + 1 ≤ (s : ℝ) - r + 1 := by
      exact_mod_cast (show s - d + 1 ≤ s - r + 1 by omega)
    have hnum0 : (0 : ℝ) ≤ (s : ℝ) * R :=
      mul_nonneg (Nat.cast_nonneg s) hR0
    have hsecond :
        (s : ℝ) * R / ((s : ℝ) - r + 1) ≤
          (s : ℝ) * R / ((s : ℝ) - d + 1) :=
      div_le_div_of_nonneg_left hnum0 hdend hdenle
    exact hfirst.trans_le hsecond
  have hcard2 : 2 ≤ T.card := by omega
  have hcardd : T.card ≤ d + 1 := by omega
  have hgen := agreementWeight_lt_of_subspaceDesign hdesign d
    (s * R / ((s : ℝ) - d + 1)) hτ y T hcard2 hcardd hTC
  rw [hcard] at hgen
  have hcastd : ((d + 1 : ℕ) : ℝ) - 1 = (d : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hcastd] at hgen
  exact hgen

end AgreementHypergraph

end CodingTheory
