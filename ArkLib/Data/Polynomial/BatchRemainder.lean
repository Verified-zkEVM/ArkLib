/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Univariate.Context

/-!
# Product-tree remainders for arbitrary monic factors

Agreement recovery tests one residual polynomial against many live parameter factors. These
factors can have degree greater than one and need not have roots in the coefficient field.
A scalar multipoint-evaluation tree therefore does not supply the operation needed here.

`BatchRemainder.remainders` builds a product tree for the supplied monic moduli, then reduces the
residual down the tree. Each child modulus divides its parent product, so reducing at a parent
preserves the eventual remainder at every descendant leaf. `remainders_eq` proves that the
result is precisely the list of individual remainders, in the original order and with duplicates
preserved. No coprimality or squarefreeness assumption is needed for this identity.

Multiplication and remainder algorithms are explicit `MulContext` and `ModContext` inputs.
This file proves functional correctness and degree accounting; it does not yet assign an
arithmetic-operation bound to an entire decoder run.
-/

@[expose] public section

namespace CompPoly.CPolynomial
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Reducing modulo a multiple first does not change the final remainder modulo a monic divisor. -/
theorem modByMonic_of_dvd (p a b : CPolynomial F) (ha : a.monic) (hb : b.monic)
    (hab : a.toPoly ∣ b.toPoly) :
    (p.modByMonic b).modByMonic a = p.modByMonic a := by
  apply toPoly_injective
  simp only [modByMonic_toPoly_eq_modByMonic _ _ ha,
    modByMonic_toPoly_eq_modByMonic _ _ hb]
  apply Polynomial.modByMonic_eq_of_dvd_sub ((monic_toPoly_iff a).mp ha)
  -- The first division changes p by a multiple of b, hence also by a multiple of a.
  have hd : b.toPoly ∣ p.toPoly %ₘ b.toPoly - p.toPoly := by
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    ring_nf
    exact dvd_neg.mpr (dvd_mul_right _ _)
  exact hab.trans hd

namespace BatchRemainder

/-- Cached products over an ordered list of polynomial moduli. -/
inductive Tree (F : Type*) [Zero F] where
  | leaf (modulus : CPolynomial F)
  | node (product : CPolynomial F) (left right : Tree F)

/-- The cached product at the root; reading it does not recompute multiplication. -/
def Tree.product : Tree F → CPolynomial F
  | .leaf h => h
  | .node h _ _ => h

/-- Leaf moduli in the order of the input list. -/
def Tree.leaves : Tree F → List (CPolynomial F)
  | .leaf h => [h]
  | .node _ left right => left.leaves ++ right.leaves

/-- Every leaf is monic, and each internal cache is exactly its two child products multiplied. -/
def Tree.WellFormed : Tree F → Prop
  | .leaf h => h.monic
  | .node h left right =>
      h = left.product * right.product ∧ left.WellFormed ∧ right.WellFormed

/-- Pair adjacent trees, computing their shared product only once. -/
def Tree.combine (M : MulContext F) (left right : Tree F) : Tree F :=
  .node (M.mul left.product right.product) left right

/-- Descend with progressively smaller remainders and retain the leaf order. -/
def Tree.remainders (D : ModContext F) (p : CPolynomial F) : Tree F → List (CPolynomial F)
  | .leaf h => [D.modByMonic p h]
  | .node h left right =>
      let rem := D.modByMonic p h
      left.remainders D rem ++ right.remainders D rem

/-- Products remain monic, so every reduction during descent uses a valid monic divisor. -/
theorem Tree.product_monic (t : Tree F) (ht : t.WellFormed) : t.product.monic := by
  induction t with
  | leaf h => exact ht
  | node h left right ihl ihr =>
      rcases ht with ⟨rfl, hl, hr⟩
      simp only [product, monic_toPoly_iff, toPoly_mul]
      exact ((monic_toPoly_iff _).mp (ihl hl)).mul ((monic_toPoly_iff _).mp (ihr hr))

/-- A leaf modulus divides every cached product above it. -/
theorem Tree.leaf_dvd (t : Tree F) (ht : t.WellFormed) (h : CPolynomial F)
    (hh : h ∈ t.leaves) : h.toPoly ∣ t.product.toPoly := by
  induction t with
  | leaf a =>
      have : h = a := by simpa [leaves] using hh
      subst h
      exact dvd_rfl
  | node a left right ihl ihr =>
      rcases ht with ⟨rfl, hl, hr⟩
      simp only [leaves, List.mem_append] at hh
      simp only [product, toPoly_mul]
      rcases hh with hh | hh
      · exact dvd_mul_of_dvd_left (ihl hl hh) _
      · exact dvd_mul_of_dvd_right (ihr hr hh) _

/-- The tree invariant records monicity at each individual modulus. -/
theorem Tree.leaf_monic (t : Tree F) (ht : t.WellFormed) (h : CPolynomial F)
    (hh : h ∈ t.leaves) : h.monic := by
  induction t with
  | leaf a => simpa [leaves] using (show h = a from by simpa [leaves] using hh) ▸ ht
  | node a left right ihl ihr =>
      rcases ht with ⟨_, hl, hr⟩
      rcases List.mem_append.mp hh with hh | hh
      · exact ihl hl hh
      · exact ihr hr hh

/-- Intermediate reductions preserve every final leaf remainder. -/
theorem Tree.remainders_eq (D : ModContext F) (t : Tree F)
    (ht : t.WellFormed) (p : CPolynomial F) :
    t.remainders D p = t.leaves.map (p.modByMonic ·) := by
  induction t generalizing p with
  | leaf h => simp [remainders, leaves, D.modByMonic_eq_modByMonic]
  | node h left right ihl ihr =>
      have hmonic := (Tree.node h left right).product_monic ht
      have hdiv := (Tree.node h left right).leaf_dvd ht
      rcases ht with ⟨_, hl, hr⟩
      simp only [remainders, leaves, List.map_append, ihl hl, ihr hr,
        D.modByMonic_eq_modByMonic]
      congr 1
      · apply List.map_congr_left
        intro a ha
        exact modByMonic_of_dvd p a h (left.leaf_monic hl a ha)
          hmonic (hdiv a (List.mem_append_left _ ha))
      · apply List.map_congr_left
        intro a ha
        exact modByMonic_of_dvd p a h (right.leaf_monic hr a ha)
          hmonic (hdiv a (List.mem_append_right _ ha))

/-- One tree level pairs adjacent nodes; an unpaired final node is carried forward. -/
def combinePairs (M : MulContext F) : List (Tree F) → List (Tree F)
  | [] => []
  | [t] => [t]
  | a :: b :: rest => a.combine M b :: combinePairs M rest

/-- Iterate pairwise combination with a finite fuel bound. Singleton forests remain unchanged. -/
def buildForest (M : MulContext F) : ℕ → List (Tree F) → List (Tree F)
  | 0, trees => trees
  | fuel + 1, trees => buildForest M fuel (combinePairs M trees)

/-- Build the product forest from the actual moduli, including the empty-list case. -/
def build (M : MulContext F) (moduli : List (CPolynomial F)) : List (Tree F) :=
  buildForest M moduli.length (moduli.map Tree.leaf)

/-- Batch a residual against arbitrary monic factors using the chosen polynomial backends. -/
def remainders (M : MulContext F) (D : ModContext F)
    (p : CPolynomial F) (moduli : List (CPolynomial F)) :
    List (CPolynomial F) :=
  (build M moduli).flatMap (fun t => t.remainders D p)

/-- Pairing changes the topology but preserves the complete ordered leaf list. -/
theorem combinePairs_leaves (M : MulContext F) (trees : List (Tree F)) :
    (combinePairs M trees).flatMap Tree.leaves = trees.flatMap Tree.leaves := by
  match trees with
  | [] => rfl
  | [t] => rfl
  | a :: b :: rest =>
      simp only [combinePairs, List.flatMap_cons, Tree.combine, Tree.leaves,
        combinePairs_leaves M rest, List.append_assoc]

/-- Correct multiplication backends preserve the cached-product invariant. -/
theorem combinePairs_wellFormed (M : MulContext F) (trees : List (Tree F))
    (ht : ∀ t ∈ trees, t.WellFormed) : ∀ t ∈ combinePairs M trees, t.WellFormed := by
  match trees with
  | [] => simp [combinePairs]
  | [a] => simpa [combinePairs] using ht
  | a :: b :: rest =>
      intro t htmem
      simp only [combinePairs, List.mem_cons] at htmem
      rcases htmem with rfl | hrest
      · exact ⟨M.mul_eq_mul _ _, ht a (by simp), ht b (by simp)⟩
      · exact combinePairs_wellFormed M rest (fun x hx => ht x (by simp [hx])) t hrest

/-- Every construction round retains all input factors in order. -/
theorem buildForest_leaves (M : MulContext F) (fuel : ℕ) (trees : List (Tree F)) :
    (buildForest M fuel trees).flatMap Tree.leaves = trees.flatMap Tree.leaves := by
  induction fuel generalizing trees with
  | zero => rfl
  | succ fuel ih => rw [buildForest, ih, combinePairs_leaves]

/-- Pairwise construction preserves monicity and all cached products. -/
theorem buildForest_wellFormed (M : MulContext F) (fuel : ℕ) (trees : List (Tree F))
    (ht : ∀ t ∈ trees, t.WellFormed) : ∀ t ∈ buildForest M fuel trees, t.WellFormed := by
  induction fuel generalizing trees with
  | zero => exact ht
  | succ fuel ih => exact ih _ (combinePairs_wellFormed M trees ht)

/-- The executable batch result equals separate reduction modulo each input factor. -/
theorem remainders_eq (M : MulContext F) (D : ModContext F)
    (p : CPolynomial F) (moduli : List (CPolynomial F))
    (hm : ∀ h ∈ moduli, h.monic) :
    remainders M D p moduli = moduli.map (p.modByMonic ·) := by
  -- Construction starts with the supplied monic factors; pairing preserves that invariant.
  have hw : ∀ t ∈ build M moduli, t.WellFormed := by
    apply buildForest_wellFormed
    intro t ht
    rcases List.mem_map.mp ht with ⟨h, hh, rfl⟩
    exact hm h hh
  -- Reassociate the batch by leaves without changing their order or multiplicity.
  have hl : (build M moduli).flatMap Tree.leaves = moduli := by
    rw [build, buildForest_leaves, List.flatMap_map]
    simp [Tree.leaves]
  rw [remainders]
  conv_rhs => rw [← hl, List.map_flatMap]
  apply List.flatMap_congr
  intro t ht
  exact Tree.remainders_eq D t (hw t ht) p

/-- The root degree is the sum of the leaf degrees, including repeated or constant factors. -/
theorem Tree.product_natDegree (t : Tree F) (ht : t.WellFormed) :
    t.product.natDegree = (t.leaves.map CPolynomial.natDegree).sum := by
  induction t with
  | leaf h => simp [product, leaves]
  | node h left right ihl ihr =>
      rcases ht with ⟨rfl, hl, hr⟩
      simp only [product, leaves, List.map_append, List.sum_append]
      rw [← ihl hl, ← ihr hr]
      simp only [natDegree_toPoly, toPoly_mul]
      exact Polynomial.natDegree_mul
        ((monic_toPoly_iff _).mp (left.product_monic hl)).ne_zero
        ((monic_toPoly_iff _).mp (right.product_monic hr)).ne_zero

/-- There is exactly one output per supplied modulus; zipping metadata cannot drop a block. -/
theorem remainders_length (M : MulContext F) (D : ModContext F)
    (p : CPolynomial F) (moduli : List (CPolynomial F))
    (hm : ∀ h ∈ moduli, h.monic) :
    (remainders M D p moduli).length = moduli.length := by
  rw [remainders_eq M D p moduli hm, List.length_map]

end BatchRemainder
end CompPoly.CPolynomial
