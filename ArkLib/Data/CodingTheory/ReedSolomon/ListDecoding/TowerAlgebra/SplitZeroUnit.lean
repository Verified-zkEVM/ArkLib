/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.BranchwiseQuotient

/-!
# Executable zero/unit splitting in a bounded-fiber tower

This is the `SplitZeroUnit` adapter from the paper.  It reuses the proved D5 factor tower to run
the Euclidean algorithm over `F[U]/G`, then emits the positive-dimensional gcd and complementary
quotient components.  Every message coefficient is restricted to the child tower in canonical
`U,V` form; no roots or field factors are runtime inputs.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial Polynomial.JetHornerMachine
open ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The geometric status of the tested element on a returned component. -/
inductive SplitTag
  | zero
  | unit
deriving DecidableEq, BEq

/-- Executable boolean view used by the recovery scanner (`true` means the residual vanishes). -/
def SplitTag.isZero : SplitTag → Bool
  | .zero => true
  | .unit => false

/-- One positive-dimensional child tower tagged by whether the tested element is zero or a unit. -/
structure TaggedTower where
  /-- Whether the tested residual is zero or invertible. -/
  tag : SplitTag
  /-- Canonical coefficient data restricted to the retained component. -/
  tower : TowerRepresentation (F := F)

/-- D5 state for computing the gcd of a tower fiber with a tested element. -/
def splitState (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) : TowerState (F := F) :=
  { modulus := r.modulus
    modulus_ne_zero := by
      exact (CPolynomial.toPoly_eq_zero_iff r.modulus).not.mp
        ((CPolynomial.monic_toPoly_iff r.modulus).mp hr.1).ne_zero
    modulus_monic := hr.1
    modulus_squarefree := hr.2.1
    dividend := FiberPolynomial.ofCPolynomial r.fiber
    divisor := FiberPolynomial.ofCPolynomial residual }

/-- Restrict the original coefficient family to a child base and fiber modulus. -/
def restrictTower (source : TowerRepresentation (F := F)) (modulus : CPolynomial F)
    (fiber : CPolynomial (CPolynomial F)) : TowerRepresentation (F := F) :=
  let reducedFiber := TowerRepresentation.reduceBase modulus fiber
  { modulus
    fiber := reducedFiber
    coefficients := source.coefficients.map
      (TowerRepresentation.reduceElement modulus reducedFiber) }

/-- Package a D5 child only when its base-by-fiber dimension is positive. -/
def makeTagged? (source : TowerRepresentation (F := F)) (tag : SplitTag)
    (modulus : CPolynomial F) (fiber : CPolynomial (CPolynomial F)) :
    Option (TaggedTower (F := F)) :=
  let child := restrictTower source modulus fiber
  if child.dimension = 0 then none else some ⟨tag, child⟩

/-- Emit the zero and unit pieces associated with one terminal D5 gcd branch. -/
def terminalChildren (source : TowerRepresentation (F := F)) (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) : List (TaggedTower (F := F)) :=
  [makeTagged? source .zero terminal.modulus terminal.gcdPolynomial.toCPolynomial,
    makeTagged? source .unit terminal.modulus
      (terminalQuotientPolynomial state terminal)].filterMap id

/-- Execute the paper's `SplitZeroUnit` procedure.

The proof argument supplies the squarefree-base invariants required by D5 and is erased at
runtime.  A failed symbolic operation has no fallback: D5 deterministically partitions the base,
and constant fiber pieces are discarded because they have no geometric points. -/
def splitZeroUnit (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) : List (TaggedTower (F := F)) :=
  let state := splitState r residual hr
  (factorTower state).flatMap (terminalChildren r state)

/-- Zero tags record an agreement. -/
@[simp] theorem splitTag_isZero_zero : SplitTag.zero.isZero = true := rfl

/-- Unit tags record a nonagreement. -/
@[simp] theorem splitTag_isZero_unit : SplitTag.unit.isZero = false := rfl

/-- Packaging succeeds exactly for a positive-dimensional restricted child. -/
theorem makeTagged?_eq_some_iff
    {source : TowerRepresentation (F := F)} {tag : SplitTag} {modulus : CPolynomial F}
    {fiber : CPolynomial (CPolynomial F)} {output : TaggedTower (F := F)} :
    makeTagged? source tag modulus fiber = some output ↔
      (restrictTower source modulus fiber).dimension ≠ 0 ∧
        output = ⟨tag, restrictTower source modulus fiber⟩ := by
  simp only [makeTagged?]
  split <;> simp_all [eq_comm]

/-- Concrete membership exposes the terminal D5 branch and whether the returned child is the
gcd (zero) or complementary quotient (unit) piece. -/
theorem mem_splitZeroUnit_iff
    {r : TowerRepresentation (F := F)} {residual : CPolynomial (CPolynomial F)}
    {width : ℕ} {hr : r.WellFormed width} {output : TaggedTower (F := F)} :
    output ∈ splitZeroUnit r residual hr ↔
      ∃ terminal ∈ factorTower (splitState r residual hr),
        makeTagged? r .zero terminal.modulus terminal.gcdPolynomial.toCPolynomial =
            some output ∨
          makeTagged? r .unit terminal.modulus
              (terminalQuotientPolynomial (splitState r residual hr) terminal) = some output := by
  simp only [splitZeroUnit, List.mem_flatMap, terminalChildren, List.mem_filterMap,
    List.mem_cons, List.not_mem_nil, or_false, id_eq]
  aesop

/-- Every emitted component has positive base-by-fiber dimension. -/
theorem dimension_ne_zero_of_mem_splitZeroUnit
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnit r residual hr) : output.tower.dimension ≠ 0 := by
  rw [splitZeroUnit] at houtput
  simp only [List.mem_flatMap] at houtput
  obtain ⟨terminal, _, houtput⟩ := houtput
  simp only [terminalChildren, List.mem_filterMap] at houtput
  obtain ⟨candidate, hcandidateMem, hcandidateEq⟩ := houtput
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcandidateMem
  rcases hcandidateMem with rfl | rfl
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hcandidateEq
    exact hdimension
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hcandidateEq
    exact hdimension

/-- Restriction preserves the represented message at every point of the child tower. -/
theorem restrictTower_specialize
    (source : TowerRepresentation (F := F)) (modulus : CPolynomial F)
    (fiber : CPolynomial (CPolynomial F))
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (hmodulus : modulus.monic)
    (hfiber : (TowerRepresentation.reduceBase modulus fiber).monic)
    (hpoint : (restrictTower source modulus fiber).Point phi u v) :
    source.specialize phi u v = (restrictTower source modulus fiber).specialize phi u v := by
  apply congrArg coefficientPolynomial
  simp only [restrictTower, List.map_map]
  apply List.map_congr_left
  intro coefficient _
  simp only [Function.comp_apply]
  symm
  exact TowerRepresentation.evalNested_reduceElement phi u v hmodulus hpoint.1 hfiber
    hpoint.2 coefficient

/-- The child fiber equation is the supplied raw fiber equation at every root of its base. -/
theorem restrictTower_point_iff
    (source : TowerRepresentation (F := F)) (modulus : CPolynomial F)
    (fiber : CPolynomial (CPolynomial F))
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (hmodulus : modulus.monic) :
    (restrictTower source modulus fiber).Point phi u v ↔
      modulus.toPoly.eval₂ phi u = 0 ∧ TowerRepresentation.evalNested fiber phi u v = 0 := by
  constructor
  · intro hpoint
    refine ⟨hpoint.1, ?_⟩
    rw [← TowerRepresentation.evalNested_reduceBase phi u v hmodulus hpoint.1 fiber]
    exact hpoint.2
  · rintro ⟨hu, hv⟩
    refine ⟨hu, ?_⟩
    change TowerRepresentation.evalNested
      (TowerRepresentation.reduceBase modulus fiber) phi u v = 0
    rw [TowerRepresentation.evalNested_reduceBase phi u v hmodulus hu fiber]
    exact hv

/-- Generic invariant packager for a positive-dimensional restricted child. -/
theorem restrictTower_wellFormed
    (source : TowerRepresentation (F := F)) (modulus : CPolynomial F)
    (fiber : CPolynomial (CPolynomial F)) {width : ℕ}
    (hmodulusMonic : modulus.monic) (hmodulusFree : Squarefree modulus.toPoly)
    (hdimension : (restrictTower source modulus fiber).dimension ≠ 0)
    (hfiberMonic : (TowerRepresentation.reduceBase modulus fiber).monic)
    (hfiberFree : ∀ (K : Type) [Field K] (phi : F →+* K) (u : K),
      modulus.toPoly.eval₂ phi u = 0 →
        Squarefree (specializeFiberCPolynomial fiber phi u))
    (hwidth : source.coefficients.length = width) :
    (restrictTower source modulus fiber).WellFormed width := by
  have hbaseNe : modulus.natDegree ≠ 0 := by
    intro hzero
    apply hdimension
    simp [TowerRepresentation.dimension, restrictTower, hzero]
  have hfiberNe : (TowerRepresentation.reduceBase modulus fiber).natDegree ≠ 0 := by
    intro hzero
    apply hdimension
    simp [TowerRepresentation.dimension, restrictTower, hzero]
  refine ⟨hmodulusMonic, hmodulusFree, Nat.pos_of_ne_zero hbaseNe,
    hfiberMonic, Nat.pos_of_ne_zero hfiberNe,
    TowerRepresentation.baseReduced_reduceBase hmodulusMonic fiber, ?_, ?_, ?_⟩
  · intro K _ phi u hu
    rw [show (restrictTower source modulus fiber).fiber =
      TowerRepresentation.reduceBase modulus fiber from rfl]
    rw [TowerRepresentation.reduceBase,
      specialize_reduceFiberCoefficients phi u hmodulusMonic hu]
    exact hfiberFree K phi u hu
  · simp [restrictTower, hwidth]
  · intro coefficient hcoefficient
    simp only [restrictTower, List.mem_map] at hcoefficient
    obtain ⟨original, _, rfl⟩ := hcoefficient
    exact TowerRepresentation.elementReduced_reduceElement hmodulusMonic hfiberMonic
      (Nat.pos_of_ne_zero hfiberNe) original

/-- A nonzero branchwise quotient of a monic dividend is again monic.  The proof uses only the
existing D5 terminal-gcd and executable monic-division invariants. -/
theorem terminalQuotientPolynomial_monic_of_ne_zero
    (state : TowerState (F := F)) (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower state)
    (hbasePos : 0 < terminal.modulus.natDegree)
    (hquotient : terminalQuotientPolynomial state terminal ≠ 0) :
    (terminalQuotientPolynomial state terminal).monic := by
  let divisor := terminal.gcdPolynomial.toCPolynomial
  let raw := state.dividend.toCPolynomial.divByMonic divisor
  have hdivisorMonic : divisor.monic :=
    factorTower_terminal_gcd_monic state hdividend terminal hterminal
  have hrawNe : raw ≠ 0 := by
    intro hzero
    apply hquotient
    rw [terminalQuotientPolynomial, show
      state.dividend.toCPolynomial.divByMonic terminal.gcdPolynomial.toCPolynomial = raw from rfl,
      hzero]
    exact FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero
      terminal.modulus (factorTower_terminal_invariants state terminal hterminal).2.1
  have hdegree : divisor.toPoly.degree ≤ state.dividend.toCPolynomial.toPoly.degree := by
    by_contra hnot
    have hlt : state.dividend.toCPolynomial.toPoly.degree < divisor.toPoly.degree :=
      lt_of_not_ge hnot
    have hzero : state.dividend.toCPolynomial.toPoly /ₘ divisor.toPoly = 0 :=
      (Polynomial.divByMonic_eq_zero_iff
        ((CPolynomial.monic_toPoly_iff divisor).mp hdivisorMonic)).mpr hlt
    apply hrawNe
    apply CPolynomial.toPoly_injective
    dsimp only [raw]
    rw [CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hdivisorMonic,
      CPolynomial.toPoly_zero]
    exact hzero
  have hrawMonic : raw.monic := by
    dsimp only [raw]
    rw [CPolynomial.monic_toPoly_iff, Polynomial.Monic.def]
    rw [CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hdivisorMonic,
      Polynomial.leadingCoeff_divByMonic_of_monic
        ((CPolynomial.monic_toPoly_iff divisor).mp hdivisorMonic) hdegree]
    exact ((CPolynomial.monic_toPoly_iff state.dividend.toCPolynomial).mp hdividend).leadingCoeff
  change (TowerRepresentation.reduceBase terminal.modulus raw).monic
  exact TowerRepresentation.monic_reduceBase
    (factorTower_terminal_invariants state terminal hterminal).2.1 hbasePos hrawMonic

/-- Every returned child point is a parent point, and its tag exactly records whether the tested
element vanishes there. -/
theorem splitZeroUnit_point_sound
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnit r residual hr)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : output.tower.Point phi u v) :
    r.Point phi u v ∧
      (output.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnit_iff.mp houtput
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitState r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hraw := (restrictTower_point_iff r terminal.modulus
      terminal.gcdPolynomial.toCPolynomial phi u v hinvariants.2.1).mp hpoint
    have hbase := factorTower_root_sound state phi u terminal hterminal hraw.1
    have hassociated := factorTower_terminal_fieldGCD_associated
      state phi u terminal hterminal hraw.1
    have hterminalRoot : (terminal.gcdPolynomial.specialize phi u).eval v = 0 := by
      change (specializeFiberCPolynomial terminal.gcdPolynomial.toCPolynomial phi u).eval v = 0
      exact hraw.2
    have hgcdRoot : (fieldGCD (state.dividend.specialize phi u)
        (state.divisor.specialize phi u)).eval v = 0 := by
      rcases hassociated with ⟨unit, hunit⟩
      have heval := congrArg (fun p : K[X] ↦ p.eval v) hunit
      simpa [Polynomial.eval_mul, hterminalRoot] using heval.symm
    have hgcdRoot' : (@EuclideanDomain.gcd K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)).eval v = 0 := by
      simpa [fieldGCD] using hgcdRoot
    have hHRoot : (state.dividend.specialize phi u).eval v = 0 := by
      obtain ⟨q, hq⟩ := @EuclideanDomain.gcd_dvd_left K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)
      rw [hq, Polynomial.eval_mul, hgcdRoot', zero_mul]
    have hSRoot : (state.divisor.specialize phi u).eval v = 0 := by
      obtain ⟨q, hq⟩ := @EuclideanDomain.gcd_dvd_right K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)
      rw [hq, Polynomial.eval_mul, hgcdRoot', zero_mul]
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hHRoot
    · constructor
      · intro _
        simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
          TowerRepresentation.evalNested] using hSRoot
      · intro _
        rfl
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitState r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hraw := (restrictTower_point_iff r terminal.modulus
      (terminalQuotientPolynomial state terminal) phi u v hinvariants.2.1).mp hpoint
    have hbase := factorTower_root_sound state phi u terminal hterminal hraw.1
    have hassociated := factorTower_terminal_fieldGCD_associated
      state phi u terminal hterminal hraw.1
    have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
      (by simpa [state, splitState] using hr.2.2.2.1)
      terminal hterminal phi u hraw.1
    have hfree : Squarefree (state.dividend.specialize phi u) := by
      simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial] using
        hr.2.2.2.2.2.2.1 K phi u hbase
    have hfiltered := squarefree_and_eval_complement_gcd_iff
      hfree.ne_zero hfree hassociated hfactor v
    have hquotientRoot :
        ((makeTerminalQuotientBranch state terminal).quotient.specialize phi u).eval v = 0 := by
      simpa [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hraw.2
    have hunitSemantics := hfiltered.2.mp hquotientRoot
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hunitSemantics.1
    · constructor
      · intro htag
        cases htag
      · intro hresidual
        exfalso
        apply hunitSemantics.2
        simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
          TowerRepresentation.evalNested] using hresidual

/-- Every parent point reaches a returned child, and it reaches a zero-tagged child exactly when
the tested element vanishes.  This is the exhaustive direction of `SplitZeroUnit`. -/
theorem splitZeroUnit_point_complete
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : r.Point phi u v) :
    ∃ output ∈ splitZeroUnit r residual hr,
      output.tower.Point phi u v ∧
        (output.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  let state := splitState r residual hr
  obtain ⟨terminal, hterminal, hterminalRoot⟩ :=
    factorTower_root_complete state phi u hpoint.1
  have hinvariants := factorTower_terminal_invariants state terminal hterminal
  have hbasePos : 0 < terminal.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hinvariants.1) phi hterminalRoot
      (fun x hx ↦ phi.injective (hx.trans phi.map_zero.symm))
  have hdividendMonic : state.dividend.toCPolynomial.monic := by
    simpa [state, splitState] using hr.2.2.2.1
  have hHRoot : (state.dividend.specialize phi u).eval v = 0 := by
    simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
      TowerRepresentation.Point, TowerRepresentation.evalNested] using hpoint.2
  have hassociated := factorTower_terminal_fieldGCD_associated
    state phi u terminal hterminal hterminalRoot
  by_cases hresidual : TowerRepresentation.evalNested residual phi u v = 0
  · have hSRoot : (state.divisor.specialize phi u).eval v = 0 := by
      simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hresidual
    have hgcdRoot : (fieldGCD (state.dividend.specialize phi u)
        (state.divisor.specialize phi u)).eval v = 0 := by
      let : DecidableEq K[X] := Classical.decEq K[X]
      rw [fieldGCD, EuclideanDomain.gcd_eq_gcd_ab]
      simp [Polynomial.eval_add, Polynomial.eval_mul, hHRoot, hSRoot]
    have hterminalFiberRoot :
        (terminal.gcdPolynomial.specialize phi u).eval v = 0 := by
      rcases hassociated.symm with ⟨unit, hunit⟩
      have heval := congrArg (fun p : K[X] ↦ p.eval v) hunit
      simpa [Polynomial.eval_mul, hgcdRoot] using heval.symm
    have hrawPoint : (restrictTower r terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).Point phi u v :=
      (restrictTower_point_iff r terminal.modulus terminal.gcdPolynomial.toCPolynomial
        phi u v hinvariants.2.1).mpr ⟨hterminalRoot, by
          exact hterminalFiberRoot⟩
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (restrictTower r terminal.modulus terminal.gcdPolynomial.toCPolynomial).fiber.monic := by
      exact TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    have hdimension : (restrictTower r terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).dimension ≠ 0 :=
      TowerRepresentation.dimension_ne_zero_of_point _ hinvariants.1 hchildMonic
        phi u v hrawPoint
    let output : TaggedTower (F := F) :=
      ⟨.zero, restrictTower r terminal.modulus terminal.gcdPolynomial.toCPolynomial⟩
    have hmade : makeTagged? r .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial = some output :=
      makeTagged?_eq_some_iff.mpr ⟨hdimension, rfl⟩
    refine ⟨output, mem_splitZeroUnit_iff.mpr
      ⟨terminal, hterminal, Or.inl hmade⟩, hrawPoint, ?_⟩
    simp [output, hresidual]
  · have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
      hdividendMonic terminal hterminal phi u hterminalRoot
    have hfree : Squarefree (state.dividend.specialize phi u) := by
      simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial] using
        hr.2.2.2.2.2.2.1 K phi u hpoint.1
    have hfiltered := squarefree_and_eval_complement_gcd_iff
      hfree.ne_zero hfree hassociated hfactor v
    have hSNonzero : (state.divisor.specialize phi u).eval v ≠ 0 := by
      simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hresidual
    have hquotientRoot := hfiltered.2.mpr ⟨hHRoot, hSNonzero⟩
    have hrawPoint : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).Point phi u v :=
      (restrictTower_point_iff r terminal.modulus
        (terminalQuotientPolynomial state terminal) phi u v hinvariants.2.1).mpr
          ⟨hterminalRoot, by
            simpa [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
              TowerRepresentation.evalNested] using hquotientRoot⟩
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      have hspecializedZero :
          (makeTerminalQuotientBranch state terminal).quotient.specialize phi u = 0 := by
        rw [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
          hzero, specializeFiberCPolynomial, CPolynomial.toPoly_zero, Polynomial.map_zero]
      exact hfiltered.1.ne_zero hspecializedZero
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).fiber.monic := by
      exact TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    have hdimension : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).dimension ≠ 0 :=
      TowerRepresentation.dimension_ne_zero_of_point _ hinvariants.1 hchildMonic
        phi u v hrawPoint
    let output : TaggedTower (F := F) :=
      ⟨.unit, restrictTower r terminal.modulus (terminalQuotientPolynomial state terminal)⟩
    have hmade : makeTagged? r .unit terminal.modulus
        (terminalQuotientPolynomial state terminal) = some output :=
      makeTagged?_eq_some_iff.mpr ⟨hdimension, rfl⟩
    refine ⟨output, mem_splitZeroUnit_iff.mpr
      ⟨terminal, hterminal, Or.inr hmade⟩, hrawPoint, ?_⟩
    simp [output, hresidual]

/-- Restricting the stored coefficient family to any returned split component preserves its
specialization at every point of that component. -/
theorem splitZeroUnit_specialize
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnit r residual hr)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : output.tower.Point phi u v) :
    r.specialize phi u v = output.tower.specialize phi u v := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnit_iff.mp houtput
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitState r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      have hne : terminal.modulus.natDegree ≠ 0 := by
        intro hzero
        apply hdimension
        simp [TowerRepresentation.dimension, restrictTower, hzero]
      exact Nat.pos_of_ne_zero hne
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitState] using hr.2.2.2.1
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (TowerRepresentation.reduceBase terminal.modulus
          terminal.gcdPolynomial.toCPolynomial).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    exact restrictTower_specialize r terminal.modulus terminal.gcdPolynomial.toCPolynomial
      phi u v hinvariants.2.1 hchildMonic hpoint
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitState r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      have hne : terminal.modulus.natDegree ≠ 0 := by
        intro hzero
        apply hdimension
        simp [TowerRepresentation.dimension, restrictTower, hzero]
      exact Nat.pos_of_ne_zero hne
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitState] using hr.2.2.2.1
    change (restrictTower r terminal.modulus
      (terminalQuotientPolynomial state terminal)).dimension ≠ 0 at hdimension
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      have hfiberZero : (restrictTower r terminal.modulus
          (terminalQuotientPolynomial state terminal)).fiber = 0 := by
        rw [restrictTower, hzero, TowerRepresentation.reduceBase]
        exact FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero
          terminal.modulus hinvariants.2.1
      apply hdimension
      rw [TowerRepresentation.dimension, hfiberZero]
      simp [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (TowerRepresentation.reduceBase terminal.modulus
        (terminalQuotientPolynomial state terminal)).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    exact restrictTower_specialize r terminal.modulus
      (terminalQuotientPolynomial state terminal) phi u v
      hinvariants.2.1 hchildMonic hpoint

/-- Every executable child retains the canonical tower invariants and the exact message width. -/
theorem splitZeroUnit_wellFormed
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.WellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnit r residual hr) : output.tower.WellFormed width := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnit_iff.mp houtput
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitState r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      by_contra hnot
      have hzeroDegree : terminal.modulus.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzeroDegree]
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitState] using hr.2.2.2.1
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (TowerRepresentation.reduceBase terminal.modulus
          terminal.gcdPolynomial.toCPolynomial).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    apply restrictTower_wellFormed r terminal.modulus
      terminal.gcdPolynomial.toCPolynomial hinvariants.2.1 hinvariants.2.2
      hdimension hchildMonic
    · intro K _ phi u hu
      have hparentRoot := factorTower_root_sound state phi u terminal hterminal hu
      have hparentFree : Squarefree (state.dividend.specialize phi u) := by
        simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial] using
          hr.2.2.2.2.2.2.1 K phi u hparentRoot
      have hassociated := factorTower_terminal_fieldGCD_associated
        state phi u terminal hterminal hu
      have hterminalDvd : terminal.gcdPolynomial.specialize phi u ∣
          state.dividend.specialize phi u :=
        hassociated.dvd_iff_dvd_left.mpr
          (@EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) _ _)
      have hterminalFree := hparentFree.squarefree_of_dvd hterminalDvd
      simpa only [FiberPolynomial.specialize] using hterminalFree
    · exact hr.2.2.2.2.2.2.2.1
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitState r residual hr
    change (restrictTower r terminal.modulus
      (terminalQuotientPolynomial state terminal)).dimension ≠ 0 at hdimension
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      by_contra hnot
      have hzeroDegree : terminal.modulus.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzeroDegree]
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitState] using hr.2.2.2.1
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzero,
        TowerRepresentation.reduceBase,
        FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero terminal.modulus hinvariants.2.1,
        CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (TowerRepresentation.reduceBase terminal.modulus
        (terminalQuotientPolynomial state terminal)).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    apply restrictTower_wellFormed r terminal.modulus
      (terminalQuotientPolynomial state terminal) hinvariants.2.1 hinvariants.2.2
      hdimension hchildMonic
    · intro K _ phi u hu
      have hparentRoot := factorTower_root_sound state phi u terminal hterminal hu
      have hparentFree : Squarefree (state.dividend.specialize phi u) := by
        simpa [state, splitState, FiberPolynomial.specialize_ofCPolynomial] using
          hr.2.2.2.2.2.2.1 K phi u hparentRoot
      have hfactor := terminal_gcd_mul_terminalQuotient_specialize
        state hdividendMonic terminal hterminal phi u hu
      have hquotientDvd :
          (makeTerminalQuotientBranch state terminal).quotient.specialize phi u ∣
            state.dividend.specialize phi u :=
        ⟨terminal.gcdPolynomial.specialize phi u, by
          rw [mul_comm, hfactor]⟩
      have hquotientFree := hparentFree.squarefree_of_dvd hquotientDvd
      simpa [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial] using
        hquotientFree
    · exact hr.2.2.2.2.2.2.2.1

end ReedSolomon.ListDecoding.TowerAlgebra
