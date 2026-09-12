/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Normalization

/-!
# Preprocessing ramified finite fibers

`PreprocessFiber` reuses the existing D5 radical and separant passes. It discards constant fibers
and packages the retained components in the common tower representation. Message coefficients
are empty at this stage: denominator inversion and coefficient materialization follow separately.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Base invariants required before fiber radicalization. Repeated fiber roots are permitted. -/
def Preprocessable (r : TowerRepresentation (F := F)) : Prop :=
  r.modulus.monic ∧ Squarefree r.modulus.toPoly ∧ r.fiber.monic

/-- The initial D5 radical state for a possibly ramified fiber. -/
def preprocessState (r : TowerRepresentation (F := F)) (hr : Preprocessable r) :
    TowerState (F := F) :=
  radicalState r.modulus
    ((CPolynomial.toPoly_eq_zero_iff _).not.mp ((CPolynomial.monic_toPoly_iff _).mp hr.1).ne_zero)
    hr.1 hr.2.1 (FiberPolynomial.ofCPolynomial r.fiber)

/-- Package one existing D5 preprocessing branch, removing precisely zero-dimensional pieces. -/
def packagePreprocessed (r : TowerRepresentation (F := F)) (branch : PreprocessedBranch (F := F)) :
    Option (TowerRepresentation (F := F)) :=
  (makeTagged? {r with coefficients := []} .unit branch.separantTerminal.modulus
    branch.good.toCPolynomial).map TaggedTower.tower

/-- Execute the paper's `PreprocessFiber`: derivative-gcd radicalization, removal of the
separant-zero locus, and deletion of constant fibers. Neither base factorization nor geometric
root extraction is executed. -/
def preprocessFiber (r : TowerRepresentation (F := F))
    (separant : CPolynomial (CPolynomial F)) (hr : Preprocessable r) :
    List (TowerRepresentation (F := F)) :=
  (preprocessTower r.modulus (preprocessState r hr).modulus_ne_zero hr.1 hr.2.1
    (FiberPolynomial.ofCPolynomial r.fiber) (FiberPolynomial.ofCPolynomial separant)).filterMap
      (packagePreprocessed r)

/-- Membership in the packaged output exposes the two actual D5 terminal branches and the
positive-dimension packaging check. -/
theorem mem_preprocessFiber_iff (r : TowerRepresentation (F := F))
    (separant : CPolynomial (CPolynomial F)) (hr : Preprocessable r)
    (out : TowerRepresentation (F := F)) :
    out ∈ preprocessFiber r separant hr ↔
      ∃ (rt : TerminalGCDBranch (F := F))
        (hrt : rt ∈ factorTower (preprocessState r hr)),
        ∃ st ∈ factorTower (separantState (preprocessState r hr) rt hrt
          (FiberPolynomial.ofCPolynomial separant)),
          packagePreprocessed r (makePreprocessedBranch rt st
            (separantState (preprocessState r hr) rt hrt
              (FiberPolynomial.ofCPolynomial separant))) = some out := by
  simp only [preprocessFiber, List.mem_filterMap, preprocessTower, List.mem_flatMap,
    List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨branch, ⟨attached, st, hst, rfl⟩, hp⟩
    exact ⟨attached.val, attached.property, st, hst, hp⟩
  · rintro ⟨rt, hrt, st, hst, hp⟩
    exact ⟨_, ⟨⟨rt, hrt⟩, st, hst, rfl⟩, hp⟩

/-- The package contains the canonically restricted good fiber exactly when its dimension is
positive. This is the only deletion performed after the D5 passes. -/
theorem packagePreprocessed_eq_some_iff (r : TowerRepresentation (F := F))
    (branch : PreprocessedBranch (F := F)) (out : TowerRepresentation (F := F)) :
    packagePreprocessed r branch = some out ↔
      (restrictTower {r with coefficients := []} branch.separantTerminal.modulus
        branch.good.toCPolynomial).dimension ≠ 0 ∧
      out = restrictTower {r with coefficients := []} branch.separantTerminal.modulus
        branch.good.toCPolynomial := by
  simp only [packagePreprocessed, Option.map_eq_some_iff]
  constructor
  · rintro ⟨tagged, ht, rfl⟩
    obtain ⟨hd, rfl⟩ := makeTagged?_eq_some_iff.mp ht
    exact ⟨hd, rfl⟩
  · rintro ⟨hd, rfl⟩
    exact ⟨_, makeTagged?_eq_some_iff.mpr ⟨hd, rfl⟩, rfl⟩

/-- Preprocessing returns only positive components, with no materialized message coefficients. -/
theorem preprocessFiber_positive (r : TowerRepresentation (F := F))
    (separant : CPolynomial (CPolynomial F)) (hr : Preprocessable r)
    (out : TowerRepresentation (F := F)) (ho : out ∈ preprocessFiber r separant hr) :
    out.dimension ≠ 0 ∧ out.coefficients = [] := by
  obtain ⟨rt, hrt, st, hst, hp⟩ := (mem_preprocessFiber_iff r separant hr out).mp ho
  obtain ⟨hd, rfl⟩ := (packagePreprocessed_eq_some_iff _ _ _).mp hp
  exact ⟨hd, by simp [restrictTower]⟩

/-- Every retained point is an original fiber point with nonzero separant, including points over
ramified projection fibers. -/
theorem preprocessFiber_point_sound (p : ℕ) [Fact p.Prime] [CharP F p]
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) (hdegree : r.fiber.natDegree < p)
    (out : TowerRepresentation (F := F)) (ho : out ∈ preprocessFiber r separant hr)
    {L : Type} [Field L] (ι : F →+* L) (u v : L) (hp : out.Point ι u v) :
    r.Point ι u v ∧ TowerRepresentation.evalNested separant ι u v ≠ 0 := by
  obtain ⟨rt, hrt, st, hst, hpackage⟩ := (mem_preprocessFiber_iff r separant hr out).mp ho
  obtain ⟨_, rfl⟩ := (packagePreprocessed_eq_some_iff _ _ _).mp hpackage
  let radical := preprocessState r hr
  let state := separantState radical rt hrt (FiberPolynomial.ofCPolynomial separant)
  have hi := factorTower_terminal_invariants state st hst
  have hraw := (restrictTower_point_iff _ _ _ ι u v hi.2.1).mp hp
  have hbase := factorTower_root_sound radical ι u rt hrt
    (factorTower_root_sound state ι u st hst hraw.1)
  have hs := preprocessTower_branch_semantics p r.modulus radical.modulus_ne_zero hr.1 hr.2.1
    (FiberPolynomial.ofCPolynomial r.fiber) (FiberPolynomial.ofCPolynomial separant)
    (by simpa using hr.2.2) (by simpa using hdegree) rt hrt st hst ι u v hraw.1
  have hg : (specializeFiberCPolynomial (terminalGoodPolynomial state st) ι u).eval v = 0 := by
    simpa only [makePreprocessedBranch, FiberPolynomial.toCPolynomial_ofCPolynomial,
      TowerRepresentation.evalNested] using hraw.2
  have hretained := hs.2.mp hg
  exact ⟨⟨hbase, by simpa only [TowerRepresentation.evalNested,
    FiberPolynomial.specialize_ofCPolynomial] using hretained.1⟩,
    by simpa only [TowerRepresentation.evalNested,
      FiberPolynomial.specialize_ofCPolynomial] using hretained.2⟩

/-- Both D5 quotient stages retain monic good fibers on every positive base branch. -/
theorem preprocessed_good_monic (r : TowerRepresentation (F := F))
    (separant : CPolynomial (CPolynomial F)) (hr : Preprocessable r)
    (rt : TerminalGCDBranch (F := F)) (hrt : rt ∈ factorTower (preprocessState r hr))
    (st : TerminalGCDBranch (F := F))
    (hst : st ∈ factorTower (separantState (preprocessState r hr) rt hrt
      (FiberPolynomial.ofCPolynomial separant)))
    (hpos : 0 < st.modulus.natDegree) :
    (terminalGoodPolynomial (separantState (preprocessState r hr) rt hrt
      (FiberPolynomial.ofCPolynomial separant)) st).monic := by
  let radical := preprocessState r hr
  let state := separantState radical rt hrt (FiberPolynomial.ofCPolynomial separant)
  have hi := factorTower_terminal_invariants state st hst
  obtain ⟨u, hu⟩ := exists_base_root st.modulus hi.2.1 hpos
  have hru := factorTower_root_sound state (algebraMap F (AlgebraicClosure F)) u st hst hu
  have hri := factorTower_terminal_invariants radical rt hrt
  have hrpos : 0 < rt.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hri.1)
      (algebraMap F (AlgebraicClosure F)) hru
      (fun a ha => (algebraMap F (AlgebraicClosure F)).injective (ha.trans (map_zero _).symm))
  have hradMonic : radical.dividend.toCPolynomial.monic := by
    simpa [radical, preprocessState] using hr.2.2
  have hqmonic := terminalQuotientPolynomial_monic_of_ne_zero radical hradMonic rt hrt hrpos
    (terminalQuotientPolynomial_ne_zero radical hradMonic rt hrt hrpos)
  have hstateMonic : state.dividend.toCPolynomial.monic := by
    simpa [state, separantState, makeTerminalQuotientBranch] using hqmonic
  have hgmonic := factorTower_terminal_gcd_monic state hstateMonic st hst
  change (terminalGoodPolynomial state st).monic
  rw [terminalGoodPolynomial, if_pos hgmonic]
  exact terminalQuotientPolynomial_monic_of_ne_zero state hstateMonic st hst hpos
    (terminalQuotientPolynomial_ne_zero state hstateMonic st hst hpos)

/-- Every eligible input point survives both D5 passes and the explicit empty-component filter. -/
theorem preprocessFiber_point_complete (p : ℕ) [Fact p.Prime] [CharP F p]
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) (hdegree : r.fiber.natDegree < p)
    {L : Type} [Field L] (ι : F →+* L) (u v : L) (hp : r.Point ι u v)
    (hS : TowerRepresentation.evalNested separant ι u v ≠ 0) :
    ∃ out ∈ preprocessFiber r separant hr, out.Point ι u v := by
  let radical := preprocessState r hr
  obtain ⟨rt, hrt, hrtRoot⟩ := factorTower_root_complete radical ι u hp.1
  let state := separantState radical rt hrt (FiberPolynomial.ofCPolynomial separant)
  obtain ⟨st, hst, hstRoot⟩ := factorTower_root_complete state ι u hrtRoot
  have hi := factorTower_terminal_invariants state st hst
  have hpos : 0 < st.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hi.1) ι hstRoot
      (fun a ha => ι.injective (ha.trans ι.map_zero.symm))
  have hs := preprocessTower_branch_semantics p r.modulus radical.modulus_ne_zero hr.1 hr.2.1
    (FiberPolynomial.ofCPolynomial r.fiber) (FiberPolynomial.ofCPolynomial separant)
    (by simpa using hr.2.2) (by simpa using hdegree) rt hrt st hst ι u v hstRoot
  have hgoodRoot : TowerRepresentation.evalNested (terminalGoodPolynomial state st) ι u v = 0 :=
    hs.2.mpr ⟨by simpa only [FiberPolynomial.specialize_ofCPolynomial,
      TowerRepresentation.evalNested] using hp.2,
      by simpa only [FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hS⟩
  let out := restrictTower {r with coefficients := []} st.modulus (terminalGoodPolynomial state st)
  have hpoint : out.Point ι u v :=
    (restrictTower_point_iff _ _ _ ι u v hi.2.1).mpr ⟨hstRoot, hgoodRoot⟩
  have hgoodMonic := preprocessed_good_monic r separant hr rt hrt st hst hpos
  have hchildMonic := TowerRepresentation.monic_reduceBase hi.2.1 hpos hgoodMonic
  have hfiberPos : 0 < out.fiber.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    have houtMonic : out.fiber.toPoly.Monic :=
      (CPolynomial.monic_toPoly_iff _).mp hchildMonic
    have hm : (specializeFiberCPolynomial out.fiber ι u).Monic := houtMonic.map _
    have hd := Polynomial.natDegree_pos_of_eval₂_root hm.ne_zero (RingHom.id L)
      (by simpa only [Polynomial.eval₂_id, TowerRepresentation.evalNested] using hpoint.2)
      (fun a ha => ha)
    simpa only [specializeFiberCPolynomial,
      houtMonic.natDegree_map] using hd
  have hdim : out.dimension ≠ 0 := Nat.mul_ne_zero hpos.ne' hfiberPos.ne'
  refine ⟨out, (mem_preprocessFiber_iff r separant hr out).mpr ⟨rt, hrt, st, hst, ?_⟩, hpoint⟩
  apply (packagePreprocessed_eq_some_iff _ _ _).mpr
  simpa only [makePreprocessedBranch, FiberPolynomial.toCPolynomial_ofCPolynomial,
    out, state, radical] using
    And.intro hdim (rfl : out = out)

/-- Preprocessing retains exactly the input points at which the supplied separant is nonzero. -/
theorem preprocessFiber_correct (p : ℕ) [Fact p.Prime] [CharP F p]
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) (hdegree : r.fiber.natDegree < p)
    {L : Type} [Field L] (ι : F →+* L) (u v : L) :
    (∃ out ∈ preprocessFiber r separant hr, out.Point ι u v) ↔
      r.Point ι u v ∧ TowerRepresentation.evalNested separant ι u v ≠ 0 := by
  constructor
  · rintro ⟨out, ho, hp⟩
    exact preprocessFiber_point_sound p r separant hr hdegree out ho ι u v hp
  · rintro ⟨hp, hS⟩
    exact preprocessFiber_point_complete p r separant hr hdegree ι u v hp hS

/-- Each retained output is a canonical squarefree tower, ready for denominator inversion and
coefficient materialization. The output has width zero until that later operation. -/
theorem preprocessFiber_wellFormed (p : ℕ) [Fact p.Prime] [CharP F p]
    (r : TowerRepresentation (F := F)) (separant : CPolynomial (CPolynomial F))
    (hr : Preprocessable r) (hdegree : r.fiber.natDegree < p)
    (out : TowerRepresentation (F := F)) (ho : out ∈ preprocessFiber r separant hr) :
    out.WellFormed 0 := by
  obtain ⟨rt, hrt, st, hst, hpackage⟩ := (mem_preprocessFiber_iff r separant hr out).mp ho
  obtain ⟨hdim, rfl⟩ := (packagePreprocessed_eq_some_iff _ _ _).mp hpackage
  let radical := preprocessState r hr
  let state := separantState radical rt hrt (FiberPolynomial.ofCPolynomial separant)
  have hi := factorTower_terminal_invariants state st hst
  have hpos : 0 < st.modulus.natDegree := by
    by_contra hnot
    have hz := Nat.eq_zero_of_not_pos hnot
    apply hdim
    simp [TowerRepresentation.dimension, restrictTower, makePreprocessedBranch, hz]
  have hm := preprocessed_good_monic r separant hr rt hrt st hst hpos
  simp only [makePreprocessedBranch, FiberPolynomial.toCPolynomial_ofCPolynomial] at hdim ⊢
  apply restrictTower_wellFormed _ _ _ hi.2.1 hi.2.2 hdim
    (TowerRepresentation.monic_reduceBase hi.2.1 hpos hm) _ rfl
  intro L _ ι u hu
  exact (preprocessTower_branch_semantics p r.modulus radical.modulus_ne_zero hr.1 hr.2.1
    (FiberPolynomial.ofCPolynomial r.fiber) (FiberPolynomial.ofCPolynomial separant)
    (by simpa using hr.2.2) (by simpa using hdegree) rt hrt st hst ι u 0 hu).1

end ReedSolomon.ListDecoding.TowerAlgebra
