/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Normalization

/-!
# Partition accounting for executable zero/unit splitting

This file proves list-level accounting for `splitZeroUnit`.  The base factors returned by D5 are
pairwise geometrically disjoint because their product is the squarefree parent modulus.  The two
children of one terminal branch are disjoint by the zero/unit semantics already proved for the
splitter.  Finally, the actual filtered child list preserves the complete base-by-fiber dimension
budget, including the cases where a constant base or fiber is removed by `makeTagged?`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Two base moduli are geometrically disjoint when they have no common root after any field
extension. -/
def BaseGeometricallyDisjoint (a b : CPolynomial F) : Prop :=
  ∀ (K : Type) [Field K] (phi : F →+* K) (u : K),
    a.toPoly.eval₂ phi u = 0 → b.toPoly.eval₂ phi u = 0 → False

/-- Two tower blocks are geometrically disjoint when they have no common geometric point after
any field extension. -/
def GeometricallyDisjoint (a b : TowerRepresentation (F := F)) : Prop :=
  ∀ (K : Type) [Field K] (phi : F →+* K) (u v : K),
    a.Point phi u v → b.Point phi u v → False

/-- If one factor occurring in a product has a geometric root, the whole product has that root. -/
private theorem eval₂_product_eq_zero_of_mem {α : Type*}
    (entries : List α) (modulus : α → CPolynomial F)
    (entry : α) (hentry : entry ∈ entries)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hroot : (modulus entry).toPoly.eval₂ phi u = 0) :
    (((entries.map modulus).prod).toPoly).eval₂ phi u = 0 := by
  induction entries with
  | nil => simp at hentry
  | cons head tail ih =>
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [CPolynomial.toPoly_mul, hroot]
      · have htail := ih hentry
        simp [CPolynomial.toPoly_mul, htail]

/-- A list of factors whose product is squarefree is pairwise geometrically disjoint.  This is
list-level: repeated positions are therefore accounted for rather than hidden by membership. -/
theorem pairwise_baseGeometricallyDisjoint_of_product_squarefree {α : Type*}
    (entries : List α) (modulus : α → CPolynomial F)
    (hfree : Squarefree (((entries.map modulus).prod).toPoly)) :
    entries.Pairwise fun a b => BaseGeometricallyDisjoint (modulus a) (modulus b) := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      have hmulFree : Squarefree
          ((modulus head).toPoly * (((tail.map modulus).prod).toPoly)) := by
        simpa only [List.map_cons, List.prod_cons, CPolynomial.toPoly_mul] using hfree
      have hcoprime : IsRelPrime (modulus head).toPoly (((tail.map modulus).prod).toPoly) :=
        IsRelPrime.of_squarefree_mul hmulFree
      have htailFree : Squarefree (((tail.map modulus).prod).toPoly) := by
        apply hmulFree.squarefree_of_dvd
        refine ⟨(modulus head).toPoly, ?_⟩
        simp [mul_comm]
      constructor
      · intro other hother K _ phi u hhead hotherRoot
        have htailRoot := eval₂_product_eq_zero_of_mem tail modulus other hother phi u hotherRoot
        rcases hcoprime.isCoprime with ⟨left, right, hbezout⟩
        have heval := congrArg (fun p : F[X] => p.eval₂ phi u) hbezout
        simp [hhead, htailRoot] at heval
      · exact ih htailFree

/-- Pairwise relations are preserved by `filterMap` when every successful image preserves the
relation. -/
theorem pairwise_filterMap_of_pairwise {α β : Type*} {S : α → α → Prop} {R : β → β → Prop}
    (entries : List α) (f : α → Option β)
    (hentries : entries.Pairwise S)
    (hmap : ∀ {a b x y}, S a b → f a = some x → f b = some y → R x y) :
    (entries.filterMap f).Pairwise R := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      cases hentries with
      | cons hhead htail =>
          cases hvalue : f head with
          | none =>
              simpa [List.filterMap, hvalue] using ih htail
          | some value =>
              have htailMapped : (tail.filterMap f).Pairwise R := ih htail
              have hcross : ∀ other ∈ tail.filterMap f, R value other := by
                intro other hother
                simp only [List.mem_filterMap] at hother
                obtain ⟨source, hsource, hsourceMap⟩ := hother
                exact hmap (hhead source hsource) hvalue hsourceMap
              have hcons : (value :: tail.filterMap f).Pairwise R := by
                constructor
                · exact hcross
                · exact htailMapped
              simpa [List.filterMap, hvalue] using hcons

/-- Appending two pairwise families remains pairwise when every left entry is related to every
right entry. -/
private theorem pairwise_append_of_pairwise {α : Type*} {R : α → α → Prop}
    (left right : List α) (hleft : left.Pairwise R) (hright : right.Pairwise R)
    (hcross : ∀ a ∈ left, ∀ b ∈ right, R a b) :
    (left ++ right).Pairwise R := by
  induction left with
  | nil => simpa
  | cons head tail ih =>
      cases hleft with
      | cons hhead htail =>
          constructor
          · intro other hother
            have hor : other ∈ tail ∨ other ∈ right := List.mem_append.mp hother
            rcases hor with hother | hother
            · exact hhead other hother
            · exact hcross head (by simp) other hother
          · apply ih htail
            intro a ha b hb
            exact hcross a (by simp [ha]) b hb

/-- Pairwise relations distribute over a flattened family when the outer relation separates every
pair of child lists. -/
theorem pairwise_flatMap_of_pairwise {α β : Type*} {S : α → α → Prop} {R : β → β → Prop}
    (entries : List α) (children : α → List β)
    (hentries : entries.Pairwise S)
    (hchildren : ∀ entry ∈ entries, (children entry).Pairwise R)
    (hcross : ∀ {a b}, S a b → ∀ x ∈ children a, ∀ y ∈ children b, R x y) :
    (entries.flatMap children).Pairwise R := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      cases hentries with
      | cons hhead htail =>
          rw [List.flatMap_cons]
          apply pairwise_append_of_pairwise
          · exact hchildren head (by simp)
          · apply ih htail
            · intro entry hentry
              exact hchildren entry (by simp [hentry])
          · intro x hx y hy
            simp only [List.mem_flatMap] at hy
            obtain ⟨other, hother, hy⟩ := hy
            exact hcross (hhead other hother) x hx y hy

/-- D5 terminal base factors are pairwise geometrically disjoint as list entries. -/
theorem factorTower_pairwise_baseGeometricallyDisjoint (state : TowerState (F := F)) :
    (factorTower state).Pairwise fun a b =>
      BaseGeometricallyDisjoint a.modulus b.modulus := by
  apply pairwise_baseGeometricallyDisjoint_of_product_squarefree
  rw [factorTower_modulus_product state]
  exact state.modulus_squarefree

/-- Every child emitted for a fixed terminal branch keeps that terminal's base modulus. -/
theorem modulus_eq_of_mem_terminalChildren
    (source : TowerRepresentation (F := F)) (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (out : TaggedTower (F := F))
    (hout : out ∈ terminalChildren source state terminal) :
    out.tower.modulus = terminal.modulus := by
  simp only [terminalChildren, List.mem_filterMap] at hout
  obtain ⟨candidate, hcandidate, hcandidateEq⟩ := hout
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcandidate
  rcases hcandidate with rfl | rfl
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hcandidateEq
    rfl
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hcandidateEq
    rfl

/-- The residual vanishes on every zero-tagged returned component. -/
theorem residual_eq_zero_of_zero_child
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (out : TaggedTower (F := F))
    (hout : out ∈ splitZeroUnit r residual hr) (htag : out.tag = .zero)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : out.tower.Point phi u v) :
    TowerRepresentation.evalNested residual phi u v = 0 :=
  (splitZeroUnit_point_sound r residual hr out hout phi u v hpoint).2.mp htag

/-- The residual is nonzero on every unit-tagged returned component. -/
theorem residual_ne_zero_of_unit_child
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (out : TaggedTower (F := F))
    (hout : out ∈ splitZeroUnit r residual hr) (htag : out.tag = .unit)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : out.tower.Point phi u v) :
    TowerRepresentation.evalNested residual phi u v ≠ 0 := by
  intro hzero
  have hzeroTag :=
    (splitZeroUnit_point_sound r residual hr out hout phi u v hpoint).2.mpr hzero
  rw [htag] at hzeroTag
  cases hzeroTag

/-- The at-most-two children of one terminal branch are geometrically disjoint. -/
theorem terminalChildren_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower (splitState r residual hr)) :
    (terminalChildren r (splitState r residual hr) terminal).Pairwise fun a b =>
      GeometricallyDisjoint a.tower b.tower := by
  let state := splitState r residual hr
  cases hzero : makeTagged? r .zero terminal.modulus terminal.gcdPolynomial.toCPolynomial with
  | none =>
      cases hunit : makeTagged? r .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) <;>
        simp [terminalChildren, state, hzero, hunit]
  | some zeroChild =>
      cases hunit : makeTagged? r .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) with
      | none =>
          simp [terminalChildren, state, hzero, hunit]
      | some unitChild =>
          have hzeroShape := makeTagged?_eq_some_iff.mp hzero
          have hunitShape := makeTagged?_eq_some_iff.mp hunit
          have hzeroTag : zeroChild.tag = .zero := by simp [hzeroShape.2]
          have hunitTag : unitChild.tag = .unit := by simp [hunitShape.2]
          have hzeroMemTerminal : zeroChild ∈ terminalChildren r state terminal := by
            simp [terminalChildren, hzero, hunit]
          have hunitMemTerminal : unitChild ∈ terminalChildren r state terminal := by
            simp [terminalChildren, hzero, hunit]
          have hzeroMem : zeroChild ∈ splitZeroUnit r residual hr := by
            change zeroChild ∈ (factorTower state).flatMap (terminalChildren r state)
            exact List.mem_flatMap.mpr ⟨terminal, hterminal, hzeroMemTerminal⟩
          have hunitMem : unitChild ∈ splitZeroUnit r residual hr := by
            change unitChild ∈ (factorTower state).flatMap (terminalChildren r state)
            exact List.mem_flatMap.mpr ⟨terminal, hterminal, hunitMemTerminal⟩
          have hdisjoint : GeometricallyDisjoint zeroChild.tower unitChild.tower := by
            intro K _ phi u v hzeroPoint hunitPoint
            have hz := residual_eq_zero_of_zero_child r residual hr zeroChild hzeroMem
              hzeroTag phi u v hzeroPoint
            have hu := residual_ne_zero_of_unit_child r residual hr unitChild hunitMem
              hunitTag phi u v hunitPoint
            exact hu hz
          simpa [terminalChildren, state, hzero, hunit] using hdisjoint

/-- Children coming from distinct D5 terminal base factors are geometrically disjoint. -/
theorem terminalChildren_cross_geometricallyDisjoint
    (source : TowerRepresentation (F := F)) (state : TowerState (F := F))
    {left right : TerminalGCDBranch (F := F)}
    (hbase : BaseGeometricallyDisjoint left.modulus right.modulus)
    {a b : TaggedTower (F := F)}
    (ha : a ∈ terminalChildren source state left)
    (hb : b ∈ terminalChildren source state right) :
    GeometricallyDisjoint a.tower b.tower := by
  intro K _ phi u v hpa hpb
  apply hbase K phi u
  · simpa [modulus_eq_of_mem_terminalChildren source state left a ha] using hpa.1
  · simpa [modulus_eq_of_mem_terminalChildren source state right b hb] using hpb.1

/-- The actual returned `splitZeroUnit` list is pairwise geometrically disjoint. -/
theorem splitZeroUnit_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) :
    (splitZeroUnit r residual hr).Pairwise fun a b =>
      GeometricallyDisjoint a.tower b.tower := by
  let state := splitState r residual hr
  change ((factorTower state).flatMap (terminalChildren r state)).Pairwise _
  apply pairwise_flatMap_of_pairwise
  · exact factorTower_pairwise_baseGeometricallyDisjoint state
  · intro terminal hterminal
    exact terminalChildren_pairwise_geometricallyDisjoint r residual hr terminal hterminal
  · intro left right hbase a ha b hb
    exact terminalChildren_cross_geometricallyDisjoint r state hbase ha hb

/-- For one terminal D5 branch, the actual filtered zero/unit children carry exactly that branch's
base degree times the incoming fiber degree.  Constant base or fiber children contribute zero and
are therefore harmless when `makeTagged?` removes them. -/
theorem terminalChildren_dimension_sum
    (source : TowerRepresentation (F := F)) (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    ((terminalChildren source state terminal).map fun out => out.tower.dimension).sum =
      terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
  have hi := factorTower_terminal_invariants state terminal hterminal
  by_cases hbase : terminal.modulus.natDegree = 0
  · have hzeroDim : (restrictTower source terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).dimension = 0 := by
      simp [TowerRepresentation.dimension, restrictTower, hbase]
    have hunitDim : (restrictTower source terminal.modulus
        (terminalQuotientPolynomial state terminal)).dimension = 0 := by
      simp [TowerRepresentation.dimension, restrictTower, hbase]
    simp [terminalChildren, makeTagged?, hzeroDim, hunitDim, hbase]
  · have hpos : 0 < terminal.modulus.natDegree := Nat.pos_of_ne_zero hbase
    have hgMonic := factorTower_terminal_gcd_monic state hdividend terminal hterminal
    have hquotientNe := terminalQuotientPolynomial_ne_zero state hdividend terminal hterminal hpos
    have hqMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividend terminal hterminal hpos hquotientNe
    have hzeroDegree : (restrictTower source terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).dimension =
        terminal.modulus.natDegree * terminal.gcdPolynomial.toCPolynomial.natDegree := by
      rw [TowerRepresentation.dimension]
      change terminal.modulus.natDegree *
          (TowerRepresentation.reduceBase terminal.modulus
            terminal.gcdPolynomial.toCPolynomial).natDegree = _
      rw [natDegree_reduceBase terminal.modulus hi.2.1 hpos
        terminal.gcdPolynomial.toCPolynomial hgMonic]
    have hunitDegree : (restrictTower source terminal.modulus
        (terminalQuotientPolynomial state terminal)).dimension =
        terminal.modulus.natDegree * (terminalQuotientPolynomial state terminal).natDegree := by
      rw [TowerRepresentation.dimension]
      change terminal.modulus.natDegree *
          (TowerRepresentation.reduceBase terminal.modulus
            (terminalQuotientPolynomial state terminal)).natDegree = _
      rw [natDegree_reduceBase terminal.modulus hi.2.1 hpos
        (terminalQuotientPolynomial state terminal) hqMonic]
    have hfiber := terminal_fiber_degree_sum state hdividend terminal hterminal hpos
    by_cases hz : (restrictTower source terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).dimension = 0 <;>
      by_cases hu : (restrictTower source terminal.modulus
        (terminalQuotientPolynomial state terminal)).dimension = 0
    · have hzeroOption : makeTagged? source .zero terminal.modulus
          terminal.gcdPolynomial.toCPolynomial = none := by
        simp [makeTagged?, hz]
      have hunitOption : makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) = none := by
        simp [makeTagged?, hu]
      have hzprod : terminal.modulus.natDegree *
          terminal.gcdPolynomial.toCPolynomial.natDegree = 0 := by
        rw [← hzeroDegree]
        exact hz
      have huprod : terminal.modulus.natDegree *
          (terminalQuotientPolynomial state terminal).natDegree = 0 := by
        rw [← hunitDegree]
        exact hu
      change (([makeTagged? source .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial,
        makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal)].filterMap id).map
            fun out => out.tower.dimension).sum = _
      rw [hzeroOption, hunitOption]
      simp only [id_eq, List.filterMap_cons, List.filterMap_nil, List.map_nil, List.sum_nil]
      symm
      calc
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree =
            terminal.modulus.natDegree *
              (terminal.gcdPolynomial.toCPolynomial.natDegree +
                (terminalQuotientPolynomial state terminal).natDegree) := by rw [hfiber]
        _ = _ := by simp [Nat.mul_add, hzprod, huprod]
    · have hzeroOption : makeTagged? source .zero terminal.modulus
          terminal.gcdPolynomial.toCPolynomial = none := by
        simp [makeTagged?, hz]
      have hunitOption : makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) =
            some ⟨.unit, restrictTower source terminal.modulus
              (terminalQuotientPolynomial state terminal)⟩ := by
        simp [makeTagged?, hu]
      have hzprod : terminal.modulus.natDegree *
          terminal.gcdPolynomial.toCPolynomial.natDegree = 0 := by
        rw [← hzeroDegree]
        exact hz
      change (([makeTagged? source .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial,
        makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal)].filterMap id).map
            fun out => out.tower.dimension).sum = _
      rw [hzeroOption, hunitOption]
      simp only [id_eq, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hunitDegree, ← hfiber, Nat.mul_add, hzprod, zero_add]
    · have hzeroOption : makeTagged? source .zero terminal.modulus
          terminal.gcdPolynomial.toCPolynomial =
            some ⟨.zero, restrictTower source terminal.modulus
              terminal.gcdPolynomial.toCPolynomial⟩ := by
        simp [makeTagged?, hz]
      have hunitOption : makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) = none := by
        simp [makeTagged?, hu]
      have huprod : terminal.modulus.natDegree *
          (terminalQuotientPolynomial state terminal).natDegree = 0 := by
        rw [← hunitDegree]
        exact hu
      change (([makeTagged? source .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial,
        makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal)].filterMap id).map
            fun out => out.tower.dimension).sum = _
      rw [hzeroOption, hunitOption]
      simp only [id_eq, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hzeroDegree, ← hfiber, Nat.mul_add, huprod, add_zero]
    · have hzeroOption : makeTagged? source .zero terminal.modulus
          terminal.gcdPolynomial.toCPolynomial =
            some ⟨.zero, restrictTower source terminal.modulus
              terminal.gcdPolynomial.toCPolynomial⟩ := by
        simp [makeTagged?, hz]
      have hunitOption : makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) =
            some ⟨.unit, restrictTower source terminal.modulus
              (terminalQuotientPolynomial state terminal)⟩ := by
        simp [makeTagged?, hu]
      change (([makeTagged? source .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial,
        makeTagged? source .unit terminal.modulus
          (terminalQuotientPolynomial state terminal)].filterMap id).map
            fun out => out.tower.dimension).sum = _
      rw [hzeroOption, hunitOption]
      simp only [id_eq, List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [hzeroDegree, hunitDegree, ← hfiber, Nat.mul_add]

/-- The actual returned child list preserves the parent quotient dimension exactly. -/
theorem splitZeroUnit_dimension_sum
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) :
    ((splitZeroUnit r residual hr).map fun out => out.tower.dimension).sum = r.dimension := by
  let state := splitState r residual hr
  have hdividend : state.dividend.toCPolynomial.monic := by
    simpa [state, splitState] using hr.2.2.2.1
  change (((factorTower state).flatMap (terminalChildren r state)).map
    (fun out => out.tower.dimension)).sum = r.dimension
  rw [sum_map_flatMap]
  calc
    _ = ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro terminal hterminal
      exact terminalChildren_dimension_sum r state hdividend terminal hterminal
    _ = ((factorTower state).map fun terminal => terminal.modulus.natDegree).sum *
        state.dividend.toCPolynomial.natDegree := by
      induction factorTower state with
      | nil => simp
      | cons terminal terminals ih => simp [ih, Nat.add_mul]
    _ = state.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
      rw [factorTower_natDegree_sum]
    _ = r.dimension := by
      simp [state, splitState, TowerRepresentation.dimension]

/-- `splitZeroUnit` is therefore an exact list-level geometric partition with exact dimension
accounting and the expected zero/unit residual semantics. -/
theorem splitZeroUnit_partition_accounting
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) :
    ((splitZeroUnit r residual hr).Pairwise fun a b =>
        GeometricallyDisjoint a.tower b.tower) ∧
      ((splitZeroUnit r residual hr).map fun out => out.tower.dimension).sum = r.dimension ∧
      ∀ (K : Type) [Field K] (phi : F →+* K) (u v : K), r.Point phi u v →
        ∃ out ∈ splitZeroUnit r residual hr,
          out.tower.Point phi u v ∧
            (out.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  refine ⟨splitZeroUnit_pairwise_geometricallyDisjoint r residual hr,
    splitZeroUnit_dimension_sum r residual hr, ?_⟩
  intro K _ phi u v hpoint
  exact splitZeroUnit_point_complete r residual hr phi u v hpoint

end ReedSolomon.ListDecoding.TowerAlgebra
