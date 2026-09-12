/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PreprocessFiber
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PartitionAccounting

/-!
# Accounting for executable fiber preprocessing

The raw two-pass D5 preprocessor already carries a weighted base-by-fiber degree bound.  This file
transfers that bound through canonical base reduction and the final positive-dimension
`filterMap`, proves list-level geometric disjointness of the retained blocks, and packages those
facts with the existing exact point-set theorem for the separant-nonzero locus.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- A `filterMap` cannot increase a natural-valued sum when each successful output is bounded by
its source entry. -/
private theorem sum_map_filterMap_le {α β : Type*}
    (entries : List α) (f : α → Option β) (sourceWeight : α → ℕ) (outputWeight : β → ℕ)
    (hweight : ∀ entry ∈ entries, ∀ out, f entry = some out →
      outputWeight out ≤ sourceWeight entry) :
    ((entries.filterMap f).map outputWeight).sum ≤ (entries.map sourceWeight).sum := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      cases hvalue : f head with
      | none =>
          have htail : ∀ entry ∈ tail, ∀ out, f entry = some out →
              outputWeight out ≤ sourceWeight entry := by
            intro entry hentry out hout
            exact hweight entry (by simp [hentry]) out hout
          have hrest := ih htail
          simpa [List.filterMap, hvalue] using
            le_trans hrest (Nat.le_add_left _ _)
      | some value =>
          have hhead := hweight head (by simp) value hvalue
          have htail : ∀ entry ∈ tail, ∀ out, f entry = some out →
              outputWeight out ≤ sourceWeight entry := by
            intro entry hentry out hout
            exact hweight entry (by simp [hentry]) out hout
          have hrest := ih htail
          simpa [List.filterMap, hvalue] using Nat.add_le_add hhead hrest

/-- Packaging a raw preprocessing branch preserves its weighted base-by-fiber degree whenever the
branch survives the positive-dimension filter. -/
theorem packagePreprocessed_dimension_le
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r)
    (branch : PreprocessedBranch (F := F))
    (hbranch : branch ∈ preprocessTower r.modulus (preprocessState r hr).modulus_ne_zero
      hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)
      (FiberPolynomial.ofCPolynomial separant))
    (out : TowerRepresentation (F := F))
    (hpackage : packagePreprocessed r branch = some out) :
    out.dimension ≤ branch.separantTerminal.modulus.natDegree *
      branch.good.toCPolynomial.natDegree := by
  simp only [preprocessTower, List.mem_flatMap, List.mem_map] at hbranch
  obtain ⟨attached, _, terminal, hterminal, hbranchEq⟩ := hbranch
  subst branch
  let radical := preprocessState r hr
  let state := separantState radical attached.1 attached.2
    (FiberPolynomial.ofCPolynomial separant)
  obtain ⟨hdimension, hout⟩ :=
    (packagePreprocessed_eq_some_iff r
      (makePreprocessedBranch attached.1 terminal state) out).mp hpackage
  subst out
  simp only [makePreprocessedBranch, FiberPolynomial.toCPolynomial_ofCPolynomial] at hdimension ⊢
  have hi := factorTower_terminal_invariants state terminal hterminal
  have hpos : 0 < terminal.modulus.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hdimension
    simp [TowerRepresentation.dimension, restrictTower, state,
      radical, hzero]
  have hgoodMonic := preprocessed_good_monic r separant hr attached.1 attached.2
    terminal hterminal hpos
  have hdegree := natDegree_reduceBase terminal.modulus hi.2.1 hpos
    (terminalGoodPolynomial state terminal) hgoodMonic
  change terminal.modulus.natDegree *
      (TowerRepresentation.reduceBase terminal.modulus
        (terminalGoodPolynomial state terminal)).natDegree ≤
    terminal.modulus.natDegree * (terminalGoodPolynomial state terminal).natDegree
  rw [hdegree]

/-- The actual filtered `preprocessFiber` output has total quotient dimension at most the input
quotient dimension. -/
theorem preprocessFiber_dimension_sum_le
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) :
    ((preprocessFiber r separant hr).map TowerRepresentation.dimension).sum ≤ r.dimension := by
  let raw := preprocessTower r.modulus (preprocessState r hr).modulus_ne_zero
    hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)
    (FiberPolynomial.ofCPolynomial separant)
  have hfiltered :
      ((raw.filterMap (packagePreprocessed r)).map TowerRepresentation.dimension).sum ≤
        (raw.map fun branch => branch.separantTerminal.modulus.natDegree *
          branch.good.toCPolynomial.natDegree).sum := by
    apply sum_map_filterMap_le
    intro branch hbranch out hpackage
    exact packagePreprocessed_dimension_le r separant hr branch hbranch out hpackage
  have hraw := preprocessTower_output_weighted_sum_le r.modulus
    (preprocessState r hr).modulus_ne_zero hr.1 hr.2.1
    (FiberPolynomial.ofCPolynomial r.fiber) (FiberPolynomial.ofCPolynomial separant)
    (by simpa using hr.2.2)
  calc
    ((preprocessFiber r separant hr).map TowerRepresentation.dimension).sum
        = ((raw.filterMap (packagePreprocessed r)).map TowerRepresentation.dimension).sum := by
            rfl
    _ ≤ (raw.map fun branch => branch.separantTerminal.modulus.natDegree *
          branch.good.toCPolynomial.natDegree).sum := hfiltered
    _ ≤ r.modulus.natDegree * r.fiber.natDegree := by
      simpa [raw] using hraw
    _ = r.dimension := rfl

/-- The unfiltered two-pass preprocessing branches are pairwise disjoint already at the base
coordinate, because their terminal base moduli multiply to the squarefree input modulus. -/
theorem preprocessTower_pairwise_baseGeometricallyDisjoint
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) :
    (preprocessTower r.modulus (preprocessState r hr).modulus_ne_zero
      hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)
      (FiberPolynomial.ofCPolynomial separant)).Pairwise fun a b =>
        BaseGeometricallyDisjoint a.separantTerminal.modulus b.separantTerminal.modulus := by
  apply pairwise_baseGeometricallyDisjoint_of_product_squarefree
  rw [preprocessTower_modulus_product r.modulus (preprocessState r hr).modulus_ne_zero
    hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)
    (FiberPolynomial.ofCPolynomial separant)]
  exact hr.2.1

/-- The actual retained preprocessing list is pairwise geometrically disjoint. -/
theorem preprocessFiber_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) :
    (preprocessFiber r separant hr).Pairwise GeometricallyDisjoint := by
  let raw := preprocessTower r.modulus (preprocessState r hr).modulus_ne_zero
    hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)
    (FiberPolynomial.ofCPolynomial separant)
  change (raw.filterMap (packagePreprocessed r)).Pairwise GeometricallyDisjoint
  apply pairwise_filterMap_of_pairwise raw (packagePreprocessed r)
  · exact preprocessTower_pairwise_baseGeometricallyDisjoint r separant hr
  · intro left right outLeft outRight hbase hleft hright
    obtain ⟨_, houtLeft⟩ := (packagePreprocessed_eq_some_iff r left outLeft).mp hleft
    obtain ⟨_, houtRight⟩ := (packagePreprocessed_eq_some_iff r right outRight).mp hright
    subst outLeft
    subst outRight
    intro K _ phi u v hpLeft hpRight
    apply hbase K phi u
    · exact hpLeft.1
    · exact hpRight.1

/-- The preprocessing output is a disjoint, dimension-nonincreasing partition of exactly the
input geometric points where the supplied separant is nonzero. -/
theorem preprocessFiber_partition_accounting
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) (hdegree : r.fiber.natDegree < p)
    {L : Type} [Field L] (ι : F →+* L) (u v : L) :
    (preprocessFiber r separant hr).Pairwise GeometricallyDisjoint ∧
      ((preprocessFiber r separant hr).map TowerRepresentation.dimension).sum ≤ r.dimension ∧
      ((∃ out ∈ preprocessFiber r separant hr, out.Point ι u v) ↔
        r.Point ι u v ∧ TowerRepresentation.evalNested separant ι u v ≠ 0) := by
  exact ⟨preprocessFiber_pairwise_geometricallyDisjoint r separant hr,
    preprocessFiber_dimension_sum_le r separant hr,
    preprocessFiber_correct p r separant hr hdegree ι u v⟩

end ReedSolomon.ListDecoding.TowerAlgebra
