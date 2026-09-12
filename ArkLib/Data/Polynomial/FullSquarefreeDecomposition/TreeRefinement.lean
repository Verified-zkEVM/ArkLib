/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.BatchRemainder
public import ArkLib.Data.Polynomial.GCDSplit

/-!
# Product and remainder trees for multiplicity strata

The weighted product uses the existing adjacent-pair balanced product forest.
Routing uses one batch reduction of a left-child product modulo the assigned
pieces, followed by gcd/exact-quotient splitting and recursive child routing.
Recursive factorization inputs are supplied; this is not the full decomposition
producer. Unit pieces are removed before each recursive batch, so only genuine
intersections continue to the children.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition

open BatchRemainder

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Multiply powered strata through the existing balanced product forest. -/
def weightedProduct (M : MulContext F) (strata : List (ℕ × CPolynomial F)) : CPolynomial F :=
  ((build M (strata.map fun z => z.2 ^ z.1)).map BatchRemainder.Tree.product).prod

/-- Well-formed cached trees compute the product of their actual leaves. -/
theorem tree_product_eq_prod (t : BatchRemainder.Tree F) (ht : t.WellFormed) :
    t.product = t.leaves.prod := by
  induction t with
  | leaf h => simp [BatchRemainder.Tree.product, BatchRemainder.Tree.leaves]
  | node h left right ihl ihr =>
    obtain ⟨heq, hl, hr⟩ := ht
    simpa [BatchRemainder.Tree.product, BatchRemainder.Tree.leaves,
      List.prod_append, ← ihl hl, ← ihr hr] using heq

/-- The balanced weighted producer is the prescribed stratum power product. -/
theorem weightedProduct_eq (M : MulContext F) (strata : List (ℕ × CPolynomial F))
    (hs : ∀ z ∈ strata, z.2.monic) :
    weightedProduct M strata = (strata.map fun z => z.2 ^ z.1).prod := by
  let powers := strata.map fun z => z.2 ^ z.1
  have hm : ∀ h ∈ powers, h.monic := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hh
    rw [monic_toPoly_iff, toPoly_pow]
    exact ((monic_toPoly_iff _).mp (hs z hz)).pow _
  have hw : ∀ t ∈ build M powers, t.WellFormed := by
    apply buildForest_wellFormed
    intro t ht
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ht
    exact hm h hh
  change ((build M powers).map BatchRemainder.Tree.product).prod = powers.prod
  calc
    _ = ((build M powers).map (fun t => t.leaves.prod)).prod := by
      congr 1
      exact List.map_congr_left fun t ht => tree_product_eq_prod t (hw t ht)
    _ = ((build M powers).flatMap BatchRemainder.Tree.leaves).prod := by
      induction build M powers with
      | nil => rfl
      | cons t rest ih => simp [ih]
    _ = powers.prod := by
      rw [build, buildForest_leaves, List.flatMap_map]
      simp [BatchRemainder.Tree.leaves]

/-- Batch the left-child polynomial modulo all current pieces before splitting.
The output pairs are the gcd child and exact complementary child. -/
def batchSplit (M : MulContext F) (D : ModContext F) (left : CPolynomial F)
    (pieces : List (CPolynomial F)) : List (CPolynomial F × CPolynomial F) :=
  List.zipWith gcdSplit pieces (remainders M D left pieces)

/-- Batched remainder reduction does not change any gcd or exact quotient. -/
theorem batchSplit_eq (M : MulContext F) (D : ModContext F) (left : CPolynomial F)
    (pieces : List (CPolynomial F)) (hm : ∀ a ∈ pieces, a.monic) :
    batchSplit M D left pieces = pieces.map (fun a => gcdSplit a left) := by
  rw [batchSplit, remainders_eq M D left pieces hm]
  induction pieces with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [ih (fun b hb => hm b (by simp [hb]))]
    congr 1
    simp [gcdSplit, gcdFactor_modByMonic a left (hm a (by simp)),
      gcdComplement_modByMonic a left (hm a (by simp))]

/-- Remove neutral pieces before batching or descending further. -/
def prune (pieces : List (CPolynomial F)) : List (CPolynomial F) :=
  pieces.filter fun a => a != 1

/-- Removing neutral factors preserves the product exactly. -/
theorem prune_prod (pieces : List (CPolynomial F)) : (prune pieces).prod = pieces.prod := by
  induction pieces with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : a = 1
    · simp_all [prune]
    · simp_all [prune, bne_iff_ne]

/-- Route assigned pieces down the supplied recursive-factor tree. Leaves retain
both their recursive modulus and the piece routed there. -/
def route (M : MulContext F) (D : ModContext F) :
    BatchRemainder.Tree F → List (CPolynomial F) → List (CPolynomial F × CPolynomial F)
  | .leaf h, pieces => (prune pieces).map fun a => (h, a)
  | .node _ left right, pieces =>
    let split := batchSplit M D left.product (prune pieces)
    route M D left (split.map Prod.fst) ++ route M D right (split.map Prod.snd)

private theorem split_prod (left : CPolynomial F) (pieces : List (CPolynomial F))
    (hm : ∀ a ∈ pieces, a.monic) :
    (pieces.map (fun a => gcdFactor a left)).prod *
      (pieces.map (fun a => gcdComplement a left)).prod = pieces.prod := by
  induction pieces with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [show gcdFactor a left * (List.map (fun a => gcdFactor a left) rest).prod *
          (gcdComplement a left * (List.map (fun a => gcdComplement a left) rest).prod) =
        (gcdFactor a left * gcdComplement a left) *
          ((List.map (fun a => gcdFactor a left) rest).prod *
            (List.map (fun a => gcdComplement a left) rest).prod) by ring]
    rw [gcdFactor_mul_gcdComplement
      ((toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp (hm a (by simp))).ne_zero),
      ih (fun b hb => hm b (by simp [hb]))]

/-- The actual tree routing preserves the exact product of all supplied pieces.
This holds without coprimality, even before leaf-divisibility is established. -/
theorem route_exact (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (CPolynomial F)) (hm : ∀ a ∈ pieces, a.monic) :
    ((route M D t pieces).map Prod.snd).prod = pieces.prod := by
  induction t generalizing pieces with
  | leaf h => simp [route, List.map_map, prune_prod]
  | node h left right ihl ihr =>
    have hp : ∀ a ∈ prune pieces, a.monic := fun a ha => hm a (List.mem_filter.mp ha).1
    rw [route, List.map_append, List.prod_append, batchSplit_eq M D _ _ hp]
    have hl : ∀ a ∈ ((prune pieces).map fun a => (gcdSplit a left.product).1), a.monic := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact gcdFactor_monic
        ((toPoly_eq_zero_iff b).not.mp ((monic_toPoly_iff b).mp (hp b hb)).ne_zero)
    have hr : ∀ a ∈ ((prune pieces).map fun a => (gcdSplit a left.product).2), a.monic := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact gcdComplement_monic (hp b hb)
    simp only [List.map_map, Function.comp_def]
    rw [ihl _ hl, ihr _ hr]
    simpa only [gcdSplit_fst, gcdSplit_snd] using
      (split_prod _ _ hp).trans (prune_prod pieces)

/-- Every emitted destination is an actual leaf of the supplied tree. -/
theorem route_leaf_mem (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (CPolynomial F)) :
    ∀ z ∈ route M D t pieces, z.1 ∈ t.leaves := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    simp [BatchRemainder.Tree.leaves]
  | node h left right ihl ihr =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ (ihl _ z hz)
    · exact List.mem_append_right _ (ihr _ z hz)

/-- Pruning prevents neutral pieces from being emitted at unrelated leaves. -/
theorem route_nonunit (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (CPolynomial F)) : ∀ z ∈ route M D t pieces, z.2 ≠ 1 := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    simpa only [bne_iff_ne] using (List.mem_filter.mp ha).2
  | node h left right ihl ihr =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ihl _ z hz
    · exact ihr _ z hz

/-- For squarefree assigned divisors, each routed piece divides the leaf to
which the actual batched tree algorithm sends it. Internal child products need
not be supplied as a list of pairwise gcd queries. -/
theorem route_leaf_dvd (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (ht : t.WellFormed) (pieces : List (CPolynomial F))
    (hm : ∀ a ∈ pieces, a.monic)
    (hs : ∀ a ∈ pieces, Squarefree a.toPoly)
    (hd : ∀ a ∈ pieces, a.toPoly ∣ t.product.toPoly) :
    ∀ z ∈ route M D t pieces, z.2.toPoly ∣ z.1.toPoly := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hd a (List.mem_filter.mp ha).1
  | node h left right ihl ihr =>
    obtain ⟨heq, hleft, hright⟩ := ht
    have hp : ∀ a ∈ prune pieces, a.monic := fun a ha => hm a (List.mem_filter.mp ha).1
    have hsp : ∀ a ∈ prune pieces, Squarefree a.toPoly :=
      fun a ha => hs a (List.mem_filter.mp ha).1
    have hdp : ∀ a ∈ prune pieces,
        a.toPoly ∣ (BatchRemainder.Tree.node h left right).product.toPoly :=
      fun a ha => hd a (List.mem_filter.mp ha).1
    rw [route, batchSplit_eq M D _ _ hp]
    simp only [List.map_map, Function.comp_def]
    have hn (a : CPolynomial F) (ha : a ∈ prune pieces) : a ≠ 0 :=
      (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp (hp a ha)).ne_zero
    have hdl (a : CPolynomial F) (ha : a ∈ prune pieces) :
        (gcdComplement a left.product).toPoly ∣ right.product.toPoly := by
      apply (gcdComplement_isCoprime_right (hn a ha) (hsp a ha)).dvd_of_dvd_mul_left
      have hac : (gcdComplement a left.product).toPoly ∣ a.toPoly := by
        have he := congrArg CPolynomial.toPoly
          (gcdFactor_mul_gcdComplement (h := a) (e := left.product) (hn a ha))
        rw [toPoly_mul] at he
        exact ⟨(gcdFactor a left.product).toPoly, by rw [← he]; ring⟩
      have hdiv := hac.trans (hdp a ha)
      simpa only [BatchRemainder.Tree.product, heq, toPoly_mul] using hdiv
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · apply ihl hleft _ ?_ ?_ ?_ z hz
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdFactor_monic (hn b hb)
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdFactor_squarefree (hsp b hb)
      · intro a ha
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
        exact gcdFactor_dvd_right _ _
    · apply ihr hright _ ?_ ?_ ?_ z hz
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdComplement_monic (hp b hb)
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdComplement_squarefree (hn b hb) (hsp b hb)
      · intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hdl b hb

/-- Keep each residue label attached while eliminating neutral pieces. -/
def pruneTagged (pieces : List (ℕ × CPolynomial F)) : List (ℕ × CPolynomial F) :=
  pieces.filter fun z => z.2 != 1

/-- Erasing labels commutes with neutral-factor pruning. -/
theorem pruneTagged_erase (pieces : List (ℕ × CPolynomial F)) :
    (pruneTagged pieces).map Prod.snd = prune (pieces.map Prod.snd) := by
  induction pieces with
  | nil => rfl
  | cons z rest ih =>
    by_cases hz : z.2 = 1 <;> simp_all [pruneTagged, prune, bne_iff_ne]

/-- Split all tagged pieces in one remainder batch, preserving the residue label. -/
def batchSplitTagged (M : MulContext F) (D : ModContext F) (left : CPolynomial F)
    (pieces : List (ℕ × CPolynomial F)) : List (ℕ × CPolynomial F × CPolynomial F) :=
  List.zipWith (fun z rem => (z.1, gcdFactor z.2 rem, gcdComplement z.2 rem))
    pieces (remainders M D left (pieces.map Prod.snd))

/-- Tagged batched splitting retains exactly the input label on each exact split. -/
theorem batchSplitTagged_eq (M : MulContext F) (D : ModContext F) (left : CPolynomial F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    batchSplitTagged M D left pieces =
      pieces.map (fun z => (z.1, gcdFactor z.2 left, gcdComplement z.2 left)) := by
  have hp : ∀ a ∈ pieces.map Prod.snd, a.monic := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact hm z hz
  rw [batchSplitTagged, remainders_eq M D left _ hp]
  simp only [List.map_map, Function.comp_def]
  induction pieces with
  | nil => rfl
  | cons z rest ih =>
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [ih (fun a ha => hm a (by simp [ha])) (fun a ha => hp a (by simp [ha]))]
    simp only [gcdFactor_modByMonic z.2 left (hm z (by simp)),
      gcdComplement_modByMonic z.2 left (hm z (by simp))]

/-- Batched routing preserving origin residue and destination recursive modulus.
The output triple is `(residue, recursive modulus, intersection piece)`. -/
def routeTagged (M : MulContext F) (D : ModContext F) : BatchRemainder.Tree F →
    List (ℕ × CPolynomial F) → List (ℕ × CPolynomial F × CPolynomial F)
  | .leaf h, pieces => (pruneTagged pieces).map fun z => (z.1, h, z.2)
  | .node _ left right, pieces =>
    let split := batchSplitTagged M D left.product (pruneTagged pieces)
    routeTagged M D left (split.map fun z => (z.1, z.2.1)) ++
      routeTagged M D right (split.map fun z => (z.1, z.2.2))

/-- Erasing only the origin metadata gives the proved untagged batched route. -/
theorem routeTagged_erase (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    (routeTagged M D t pieces).map Prod.snd = route M D t (pieces.map Prod.snd) := by
  induction t generalizing pieces with
  | leaf h =>
    simp only [routeTagged, route, ← pruneTagged_erase, List.map_map, Function.comp_def]
  | node h left right ihl ihr =>
    have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
      fun z hz => hm z (List.mem_filter.mp hz).1
    have hu : ∀ a ∈ prune (pieces.map Prod.snd), a.monic := by
      rw [← pruneTagged_erase]
      intro a ha
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      exact hp z hz
    rw [routeTagged, List.map_append, batchSplitTagged_eq M D _ _ hp]
    simp only [List.map_map, Function.comp_def]
    have hl : ∀ z ∈ (pruneTagged pieces).map
        (fun z => (z.1, gcdFactor z.2 left.product)), z.2.monic := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact gcdFactor_monic
        ((toPoly_eq_zero_iff a.2).not.mp ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)
    have hr : ∀ z ∈ (pruneTagged pieces).map
        (fun z => (z.1, gcdComplement z.2 left.product)), z.2.monic := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact gcdComplement_monic (hp a ha)
    rw [ihl _ hl, ihr _ hr, route, batchSplit_eq M D _ _ hu, ← pruneTagged_erase]
    simp [List.map_map, Function.comp_def, gcdSplit]

/-- The metadata-preserving producer reconstructs all input residue pieces. -/
theorem routeTagged_exact (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    ((routeTagged M D t pieces).map (fun z => z.2.2)).prod = (pieces.map Prod.snd).prod := by
  have hp : ∀ a ∈ pieces.map Prod.snd, a.monic := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact hm z hz
  have he := congrArg (fun l : List (CPolynomial F × CPolynomial F) =>
    (l.map Prod.snd).prod) (routeTagged_erase M D t pieces hm)
  simpa only [List.map_map, Function.comp_def] using he.trans (route_exact M D t _ hp)

/-- The tagged producer routes squarefree divisors only to containing leaves. -/
theorem routeTagged_leaf_dvd (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (ht : t.WellFormed) (pieces : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ pieces, z.2.monic) (hs : ∀ z ∈ pieces, Squarefree z.2.toPoly)
    (hd : ∀ z ∈ pieces, z.2.toPoly ∣ t.product.toPoly) :
    ∀ z ∈ routeTagged M D t pieces, z.2.2.toPoly ∣ z.2.1.toPoly := by
  intro z hz
  have hz' : z.2 ∈ route M D t (pieces.map Prod.snd) := by
    rw [← routeTagged_erase M D t pieces hm]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  apply route_leaf_dvd M D t ht (pieces.map Prod.snd) ?_ ?_ ?_ z.2 hz'
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hm b hb
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hs b hb
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hd b hb

/-- First split original residue strata against the root recursive product in
one batch. Route only intersections; return residue-only complements separately.
Recursive-only leftovers and final multiplicity grouping are subsequent stages. -/
def refineRoot (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) :
    List (ℕ × CPolynomial F × CPolynomial F) × List (ℕ × CPolynomial F) :=
  let split := batchSplitTagged M D t.product (pruneTagged pieces)
  (routeTagged M D t (split.map fun z => (z.1, z.2.1)),
    pruneTagged (split.map fun z => (z.1, z.2.2)))

/-- The initial batch split and routing reconstruct the supplied original
residue strata, including their portions outside the recursive factor product. -/
theorem refineRoot_exact (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    ((refineRoot M D t pieces).1.map (fun z => z.2.2)).prod *
      ((refineRoot M D t pieces).2.map Prod.snd).prod = (pieces.map Prod.snd).prod := by
  have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
    fun z hz => hm z (List.mem_filter.mp hz).1
  have hl : ∀ z ∈ (pruneTagged pieces).map
      (fun z => (z.1, gcdFactor z.2 t.product)), z.2.monic := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_monic
      ((toPoly_eq_zero_iff a.2).not.mp ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)
  have hu : ∀ a ∈ (pruneTagged pieces).map Prod.snd, a.monic := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact hp z hz
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
  rw [routeTagged_exact M D t _ hl, pruneTagged_erase, prune_prod]
  simp only [List.map_map, Function.comp_def]
  have he := split_prod t.product ((pruneTagged pieces).map Prod.snd) hu
  simp only [List.map_map, Function.comp_def] at he
  rw [he, pruneTagged_erase, prune_prod]

/-- Original squarefree residue strata need no caller-supplied intersection
certificate: the initial root gcd supplies it for the routed output. -/
theorem refineRoot_leaf_dvd (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (ht : t.WellFormed) (pieces : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ pieces, z.2.monic) (hs : ∀ z ∈ pieces, Squarefree z.2.toPoly) :
    ∀ z ∈ (refineRoot M D t pieces).1, z.2.2.toPoly ∣ z.2.1.toPoly := by
  have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
    fun z hz => hm z (List.mem_filter.mp hz).1
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
  apply routeTagged_leaf_dvd M D t ht
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_monic
      ((toPoly_eq_zero_iff a.2).not.mp ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_squarefree (hs a (List.mem_filter.mp ha).1)
  · intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_dvd_right _ _

end CompPoly.CPolynomial.FullSquarefreeDecomposition
