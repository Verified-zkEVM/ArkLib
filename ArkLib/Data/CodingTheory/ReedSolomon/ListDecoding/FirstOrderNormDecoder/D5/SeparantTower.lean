/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.RadicalTower
import all
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.BranchwiseQuotient
import all
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.RadicalTower

/-!
# Branchwise separant filtering after D5 radicalization

After derivative-gcd removal, this file restricts the separant to every radical base factor and
runs the D5 tower a second time.  A monic terminal gcd is divided out normally.  The sole fallback
is the exact unit quotient when a nonmonic terminal gcd is the entire incoming radical fiber; it
is not an exceptional-fiber solver branch.

The resulting geometric fibers are squarefree and retain exactly the original fiber points where
the separant is nonzero.  Base-factor products and the sum of base degree times vertical degree
remain bounded by the original input block.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance separantTowerDecidableEqF : DecidableEq F := instDecidableEqOfLawfulBEq
local instance separantTowerDecidableEqCPolynomial : DecidableEq (CPolynomial F) :=
  instDecidableEqOfLawfulBEq

/-- Restrict a bounded fiber polynomial coefficientwise to a monic base factor. -/
def restrictFiber (modulus : CPolynomial F) (p : FiberPolynomial (F := F)) :
    FiberPolynomial (F := F) :=
  FiberPolynomial.ofCPolynomial (reduceFiberCoefficients modulus p.toCPolynomial)

/-- Restriction does not change specialization at a root of the new base modulus. -/
theorem restrictFiber_specialize
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {modulus : CPolynomial F} (hmodulus : modulus.monic)
    (hroot : modulus.toPoly.eval₂ phi x = 0) (p : FiberPolynomial (F := F)) :
    (restrictFiber modulus p).specialize phi x = p.specialize phi x := by
  rw [restrictFiber, FiberPolynomial.specialize_ofCPolynomial,
    specialize_reduceFiberCoefficients phi x hmodulus hroot]
  rfl

/-- The second D5 state removes the gcd of one radical branch with the restricted separant. -/
def separantState (radical : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower radical) (separant : FiberPolynomial (F := F)) :
    TowerState (F := F) :=
  let invariants := factorTower_terminal_invariants radical terminal hterminal
  { modulus := terminal.modulus
    modulus_ne_zero := invariants.1
    modulus_monic := invariants.2.1
    modulus_squarefree := invariants.2.2
    dividend := (makeTerminalQuotientBranch radical terminal).quotient
    divisor := restrictFiber terminal.modulus separant }

/-- A terminal gcd is either the incoming dividend itself or is globally monic.  The first
alternative occurs only before a normalized Euclidean divisor has become the dividend. -/
theorem factorTower_terminal_gcd_eq_dividend_or_monic
    (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    terminal.gcdPolynomial = state.dividend ∨ terminal.gcdPolynomial.toCPolynomial.monic := by
  induction state using factorTower.induct with
  | case1 state ih =>
      rw [factorTower.eq_def] at hterminal
      simp only [List.mem_flatMap] at hterminal
      obtain ⟨attached, _, hterminal⟩ := hterminal
      rcases attached with ⟨⟨modulus, coefficients, inverseOption⟩, hbranch⟩
      have hready := splitLeading_ready state.divisor.coefficients state.modulus
        (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
      cases coefficients with
      | nil =>
          cases inverseOption with
          | none =>
              simp only [List.mem_singleton] at hterminal
              rcases hterminal with rfl
              exact Or.inl rfl
          | some inverse => simp [LeadingBranch.Ready] at hready
      | cons leading lower =>
          cases inverseOption with
          | none => simp [LeadingBranch.Ready] at hready
          | some inverse =>
              let attached : {branch // branch ∈
                  splitLeading state.divisor.coefficients state.modulus} :=
                ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
              let next := nextUnitPair modulus inverse leading lower state.dividend
              have hnextDividend : next.dividend.toCPolynomial.monic := by
                rw [nextUnitPair_dividend_toCPolynomial]
                exact (CPolynomial.monic_toPoly_iff _).mpr
                  (normalizedDivisor_monic modulus inverse leading lower)
              by_cases hzero : next.divisor.toCPolynomial = 0
              · have hterminalEq : terminal =
                    (⟨modulus, next.dividend, .zeroRemainder⟩ :
                      TerminalGCDBranch (F := F)) := by
                  simpa [next, hzero] using hterminal
                rw [hterminalEq]
                exact Or.inr hnextDividend
              · have hzero' : reduceFiberCoefficients modulus
                    (state.dividend.toCPolynomial.modByMonic
                      (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                  simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                have hinvariants := splitLeading_child_invariants state
                  (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) hbranch
                have hterminalChild : terminal ∈ factorTower
                    { modulus := modulus
                      modulus_ne_zero := hinvariants.1
                      modulus_monic := hinvariants.2.1
                      modulus_squarefree := hinvariants.2.2
                      dividend := next.dividend
                      divisor := next.divisor } := by
                  simpa [hzero'] using hterminal
                rcases ih attached leading lower inverse rfl rfl hzero hterminalChild with
                  hsame | hmonic
                · exact Or.inr (hsame ▸ hnextDividend)
                · exact Or.inr hmonic

/-- The branch-local separant quotient.  A nonmonic terminal gcd must be the whole incoming
dividend, in which case the exact quotient is the constant one. -/
def terminalGoodPolynomial (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) : CPolynomial (CPolynomial F) :=
  if terminal.gcdPolynomial.toCPolynomial.monic then
    terminalQuotientPolynomial state terminal
  else 1

/-- One fully preprocessed branch. -/
structure PreprocessedBranch where
  radicalTerminal : TerminalGCDBranch (F := F)
  separantTerminal : TerminalGCDBranch (F := F)
  good : FiberPolynomial (F := F)

/-- Package one terminal separant quotient in canonical bounded-fiber form. -/
def makePreprocessedBranch (radicalTerminal separantTerminal : TerminalGCDBranch (F := F))
    (state : TowerState (F := F)) : PreprocessedBranch (F := F) :=
  { radicalTerminal
    separantTerminal
    good := FiberPolynomial.ofCPolynomial (terminalGoodPolynomial state separantTerminal) }

/-- Execute radicalization and separant filtering on every returned base factor. -/
def preprocessTower (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F)) :
    List (PreprocessedBranch (F := F)) :=
  let radical := radicalState g hg hgmonic hgfree h
  (factorTower radical).attach.flatMap fun attached =>
    let state := separantState radical attached.1 attached.2 separant
    (factorTower state).map fun terminal => makePreprocessedBranch attached.1 terminal state

/-- Every pair of first- and second-pass terminal branches occurs in the executable output. -/
theorem makePreprocessedBranch_mem_preprocessTower
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F))
    (radicalTerminal : TerminalGCDBranch (F := F))
    (hradical : radicalTerminal ∈ factorTower (radicalState g hg hgmonic hgfree h))
    (separantTerminal : TerminalGCDBranch (F := F))
    (hseparant : separantTerminal ∈ factorTower
      (separantState (radicalState g hg hgmonic hgfree h)
        radicalTerminal hradical separant)) :
    makePreprocessedBranch radicalTerminal separantTerminal
        (separantState (radicalState g hg hgmonic hgfree h)
          radicalTerminal hradical separant) ∈
      preprocessTower g hg hgmonic hgfree h separant := by
  rw [preprocessTower]
  apply List.mem_flatMap.mpr
  let attached : {terminal // terminal ∈
      factorTower (radicalState g hg hgmonic hgfree h)} := ⟨radicalTerminal, hradical⟩
  refine ⟨attached, by simp [attached], ?_⟩
  apply List.mem_map.mpr
  exact ⟨separantTerminal, by simpa [attached] using hseparant, by simp [attached]⟩

/-- Specialization of the monic terminal-quotient case is ordinary polynomial division. -/
theorem terminalGoodPolynomial_specialize_of_monic
    (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    (hmonic : terminal.gcdPolynomial.toCPolynomial.monic)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    specializeFiberCPolynomial (terminalGoodPolynomial state terminal) phi x =
      state.dividend.specialize phi x /ₘ terminal.gcdPolynomial.specialize phi x := by
  rw [terminalGoodPolynomial, if_pos hmonic]
  rw [terminalQuotientPolynomial,
    specialize_reduceFiberCoefficients phi x
      (factorTower_terminal_invariants state terminal hterminal).2.1 hroot,
    specializeFiberCPolynomial_divByMonic phi x _ _ hmonic]
  rfl

/-- In the monic case, the separant terminal gcd times the returned quotient equals the incoming
radical fiber after every rooted specialization. -/
theorem terminal_gcd_mul_terminalGood_specialize_of_monic
    (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    (hmonic : terminal.gcdPolynomial.toCPolynomial.monic)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    terminal.gcdPolynomial.specialize phi x *
        specializeFiberCPolynomial (terminalGoodPolynomial state terminal) phi x =
      state.dividend.specialize phi x := by
  have hterminalMonic : (terminal.gcdPolynomial.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp hmonic).map _
  have hassociated :=
    factorTower_terminal_fieldGCD_associated state phi x terminal hterminal hroot
  have hgcdDvd : fieldGCD (state.dividend.specialize phi x)
      (state.divisor.specialize phi x) ∣ state.dividend.specialize phi x :=
    @EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) _ _
  have hterminalDvd : terminal.gcdPolynomial.specialize phi x ∣
      state.dividend.specialize phi x :=
    hassociated.dvd_iff_dvd_left.mpr hgcdDvd
  have hmod : state.dividend.specialize phi x %ₘ
      terminal.gcdPolynomial.specialize phi x = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hterminalMonic).mpr hterminalDvd
  rw [terminalGoodPolynomial_specialize_of_monic state terminal hterminal hmonic phi x hroot]
  have hdivision := Polynomial.modByMonic_add_div
    (state.dividend.specialize phi x) (terminal.gcdPolynomial.specialize phi x)
  rw [hmod, zero_add] at hdivision
  exact hdivision

/-- For a squarefree input, quotienting by an associated gcd retains exactly the roots where the
tested polynomial is nonzero, and the quotient remains squarefree. -/
theorem squarefree_and_eval_complement_gcd_iff
    {K : Type*} [Field K] {H S D Q : K[X]}
    (hH : H ≠ 0) (hHfree : Squarefree H)
    (hassociated : Associated D (fieldGCD H S)) (hfactor : D * Q = H) (y : K) :
    Squarefree Q ∧ (Q.eval y = 0 ↔ H.eval y = 0 ∧ S.eval y ≠ 0) := by
  have hQDvd : Q ∣ H := ⟨D, by rw [mul_comm, hfactor]⟩
  have hQfree : Squarefree Q := hHfree.squarefree_of_dvd hQDvd
  have hDNe : D ≠ 0 := by
    intro hzero
    apply hH
    simpa [hzero] using hfactor.symm
  have hQNe : Q ≠ 0 := by
    intro hzero
    apply hH
    simpa [hzero] using hfactor.symm
  have hcoprime : IsRelPrime D Q :=
    IsRelPrime.of_squarefree_mul (hfactor ▸ hHfree)
  refine ⟨hQfree, ?_⟩
  constructor
  · intro hQRoot
    have hHRoot : H.eval y = 0 := by
      rw [← hfactor, Polynomial.eval_mul, hQRoot, mul_zero]
    refine ⟨hHRoot, ?_⟩
    intro hSRoot
    have hlinearDvdH : X - C y ∣ H :=
      Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hHRoot)
    have hlinearDvdS : X - C y ∣ S :=
      Polynomial.dvd_iff_isRoot.mpr (by simpa [Polynomial.IsRoot] using hSRoot)
    have hlinearDvdGCD : X - C y ∣ fieldGCD H S :=
      @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X]) _ _ _
        hlinearDvdH hlinearDvdS
    have hlinearDvdD : X - C y ∣ D :=
      hassociated.dvd_iff_dvd_right.mpr hlinearDvdGCD
    have hDRoot : D.eval y = 0 := by
      simpa [Polynomial.IsRoot] using Polynomial.dvd_iff_isRoot.mp hlinearDvdD
    rcases hcoprime.isCoprime with ⟨a, b, hab⟩
    have heval := congrArg (fun P : K[X] => P.eval y) hab
    simp [hDRoot, hQRoot] at heval
  · rintro ⟨hHRoot, hSNonzero⟩
    have hproduct : D.eval y * Q.eval y = 0 := by
      rw [← Polynomial.eval_mul, hfactor, hHRoot]
    rcases mul_eq_zero.mp hproduct with hDRoot | hQRoot
    · have hDDvdS : D ∣ S := by
        apply hassociated.dvd_iff_dvd_left.mpr
        exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance
          (Classical.decEq K[X]) H S
      obtain ⟨multiple, rfl⟩ := hDDvdS
      simp [Polynomial.eval_mul, hDRoot] at hSNonzero
    · exact hQRoot

/-- Every fully preprocessed rooted branch is squarefree and retains exactly the original fiber
roots on which the separant is nonzero. -/
theorem preprocessTower_branch_semantics
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic) (hhdegree : h.toCPolynomial.natDegree < p)
    (radicalTerminal : TerminalGCDBranch (F := F))
    (hradical : radicalTerminal ∈
      factorTower (radicalState g hg hgmonic hgfree h))
    (separantTerminal : TerminalGCDBranch (F := F))
    (hseparant : separantTerminal ∈ factorTower
      (separantState (radicalState g hg hgmonic hgfree h)
        radicalTerminal hradical separant))
    {K : Type*} [Field K] (phi : F →+* K) (x y : K)
    (hroot : separantTerminal.modulus.toPoly.eval₂ phi x = 0) :
    let state := separantState (radicalState g hg hgmonic hgfree h)
      radicalTerminal hradical separant
    let good := specializeFiberCPolynomial
      (terminalGoodPolynomial state separantTerminal) phi x
    Squarefree good ∧
      (good.eval y = 0 ↔
        (h.specialize phi x).eval y = 0 ∧ (separant.specialize phi x).eval y ≠ 0) := by
  dsimp only
  let _ : CharP K p := charP_of_injective_ringHom phi.injective p
  let radical := radicalState g hg hgmonic hgfree h
  let state := separantState radical radicalTerminal hradical separant
  have hradicalRoot : radicalTerminal.modulus.toPoly.eval₂ phi x = 0 :=
    factorTower_root_sound state phi x separantTerminal hseparant hroot
  have hradicalSemantics := radicalTower_branch_semantics
    g hg hgmonic hgfree h hhmonic radicalTerminal hradical phi x hradicalRoot
  have hradicalRootIff := radicalTower_branch_root_iff p g hg hgmonic hgfree h
    hhmonic hhdegree radicalTerminal hradical phi x y hradicalRoot
  have hstateDividendRootIff : (state.dividend.specialize phi x).eval y = 0 ↔
      (h.specialize phi x).eval y = 0 := by
    simpa [state, separantState, radical] using hradicalRootIff
  have hseparantSpecialize : state.divisor.specialize phi x = separant.specialize phi x := by
    exact restrictFiber_specialize phi x
      (factorTower_terminal_invariants radical radicalTerminal hradical).2.1
      hradicalRoot separant
  have hHMonic : (state.dividend.specialize phi x).Monic := by
    have hDMonic : (radicalTerminal.gcdPolynomial.specialize phi x).Monic :=
      ((CPolynomial.monic_toPoly_iff _).mp
        (factorTower_terminal_gcd_monic radical hhmonic radicalTerminal hradical)).map _
    have hInputMonic : (h.specialize phi x).Monic :=
      ((CPolynomial.monic_toPoly_iff _).mp hhmonic).map _
    exact hDMonic.of_mul_monic_left (hradicalSemantics.1 ▸ hInputMonic)
  have hassociated := factorTower_terminal_fieldGCD_associated
    state phi x separantTerminal hseparant hroot
  by_cases hmonic : separantTerminal.gcdPolynomial.toCPolynomial.monic
  · have hfactor := terminal_gcd_mul_terminalGood_specialize_of_monic
      state separantTerminal hseparant hmonic phi x hroot
    have hfiltered := squarefree_and_eval_complement_gcd_iff
      hHMonic.ne_zero hradicalSemantics.2 (by
        rw [hseparantSpecialize] at hassociated
        exact hassociated) hfactor y
    refine ⟨hfiltered.1, ?_⟩
    rw [hfiltered.2, hstateDividendRootIff]
  · have hwhole : separantTerminal.gcdPolynomial = state.dividend :=
      (factorTower_terminal_gcd_eq_dividend_or_monic state separantTerminal hseparant)
        |>.resolve_right hmonic
    have hHDvdS : state.dividend.specialize phi x ∣ state.divisor.specialize phi x := by
      rw [hwhole] at hassociated
      apply hassociated.dvd_iff_dvd_left.mpr
      exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance
        (Classical.decEq K[X]) _ _
    have hnoRetained : ¬((state.dividend.specialize phi x).eval y = 0 ∧
        (state.divisor.specialize phi x).eval y ≠ 0) := by
      rintro ⟨hHRoot, hSNonzero⟩
      obtain ⟨multiple, hmultiple⟩ := hHDvdS
      rw [hmultiple, Polynomial.eval_mul, hHRoot, zero_mul] at hSNonzero
      exact hSNonzero rfl
    have hgood : specializeFiberCPolynomial
        (terminalGoodPolynomial state separantTerminal) phi x = 1 := by
      rw [terminalGoodPolynomial, if_neg hmonic, specializeFiberCPolynomial,
        CPolynomial.toPoly_one, Polynomial.map_one]
    rw [hgood]
    refine ⟨squarefree_one, ?_⟩
    simp only [Polynomial.eval_one, one_ne_zero, false_iff]
    intro hretained
    apply hnoRetained
    rw [hseparantSpecialize]
    exact ⟨hstateDividendRootIff.mpr hretained.1, hretained.2⟩

/-- Every emitted good polynomial has fiber degree no larger than its incoming radical branch. -/
theorem terminalGoodPolynomial_natDegree_le
    (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (_hterminal : terminal ∈ factorTower state) :
    (terminalGoodPolynomial state terminal).natDegree ≤
      state.dividend.toCPolynomial.natDegree := by
  by_cases hmonic : terminal.gcdPolynomial.toCPolynomial.monic
  · rw [terminalGoodPolynomial, if_pos hmonic]
    let raw := state.dividend.toCPolynomial.divByMonic terminal.gcdPolynomial.toCPolynomial
    have hrawDegree : raw.natDegree ≤ state.dividend.toCPolynomial.natDegree := by
      rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
        CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hmonic]
      exact Polynomial.natDegree_le_natDegree (Polynomial.degree_divByMonic_le _ _)
    by_cases hquotient : terminalQuotientPolynomial state terminal = 0
    · rw [hquotient, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
        Polynomial.natDegree_zero]
      exact Nat.zero_le _
    · exact (natDegree_reduceFiberCoefficients_le terminal.modulus raw hquotient).trans
        hrawDegree
  · rw [terminalGoodPolynomial, if_neg hmonic, CPolynomial.natDegree_toPoly,
      CPolynomial.toPoly_one, Polynomial.natDegree_one]
    exact Nat.zero_le _

/-- One separant tower preserves the incoming base-factor product. -/
theorem separantTower_modulus_product
    (radical : TowerState (F := F))
    (radicalTerminal : TerminalGCDBranch (F := F))
    (hradical : radicalTerminal ∈ factorTower radical)
    (separant : FiberPolynomial (F := F)) :
    ((factorTower (separantState radical radicalTerminal hradical separant)).map
      TerminalGCDBranch.modulus).prod = radicalTerminal.modulus := by
  simpa [separantState] using factorTower_modulus_product
    (separantState radical radicalTerminal hradical separant)

/-- One separant tower stays within its incoming base-by-fiber degree budget. -/
theorem separantTower_weighted_sum_le
    (radical : TowerState (F := F))
    (radicalTerminal : TerminalGCDBranch (F := F))
    (hradical : radicalTerminal ∈ factorTower radical)
    (separant : FiberPolynomial (F := F)) :
    ((factorTower (separantState radical radicalTerminal hradical separant)).map
      fun terminal => terminal.modulus.natDegree *
        (terminalGoodPolynomial
          (separantState radical radicalTerminal hradical separant) terminal).natDegree).sum ≤
      radicalTerminal.modulus.natDegree *
        (terminalQuotientPolynomial radical radicalTerminal).natDegree := by
  let state := separantState radical radicalTerminal hradical separant
  have hpointwise : ∀ terminal ∈ factorTower state,
      terminal.modulus.natDegree * (terminalGoodPolynomial state terminal).natDegree ≤
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
    intro terminal hterminal
    exact Nat.mul_le_mul_left terminal.modulus.natDegree
      (terminalGoodPolynomial_natDegree_le state terminal hterminal)
  calc
    _ ≤ ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree).sum :=
      List.sum_le_sum hpointwise
    _ = ((factorTower state).map fun terminal => terminal.modulus.natDegree).sum *
        state.dividend.toCPolynomial.natDegree := by
      induction factorTower state with
      | nil => simp
      | cons terminal terminals ih => simp [ih, Nat.add_mul]
    _ = state.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
      rw [factorTower_natDegree_sum]
    _ = _ := by
      simp [state, separantState, makeTerminalQuotientBranch]

/-- Summing a function that ignores membership proofs over `List.attach` is the original sum. -/
theorem sum_map_attach {α : Type*} (entries : List α) (f : α → ℕ) :
    (entries.attach.map fun entry => f entry.1).sum = (entries.map f).sum := by
  have h := congrArg (fun list => (list.map f).sum) (List.attach_map_subtype_val entries)
  change (entries.attach.map (f ∘ Subtype.val)).sum = (entries.map f).sum
  simpa only [List.map_map] using h

/-- A weighted sum over a flattened list is the sum of the child weighted sums. -/
theorem sum_map_flatMap {α β : Type*} (entries : List α)
    (children : α → List β) (weight : β → ℕ) :
    ((entries.flatMap children).map weight).sum =
      (entries.map fun entry => ((children entry).map weight).sum).sum := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [ih]

/-- A product over a flattened list is the product of the child products. -/
theorem prod_map_flatMap {α β M : Type*} [CommMonoid M] (entries : List α)
    (children : α → List β) (weight : β → M) :
    ((entries.flatMap children).map weight).prod =
      (entries.map fun entry => ((children entry).map weight).prod).prod := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [ih]

/-- Products, like sums, ignore the membership proofs introduced by `List.attach`. -/
theorem prod_map_attach {α M : Type*} [CommMonoid M] (entries : List α) (f : α → M) :
    (entries.attach.map fun entry => f entry.1).prod = (entries.map f).prod := by
  have h := congrArg (fun list => (list.map f).prod) (List.attach_map_subtype_val entries)
  change (entries.attach.map (f ∘ Subtype.val)).prod = (entries.map f).prod
  simpa only [List.map_map] using h

/-- The fully flattened preprocessing output still has product exactly the original base
modulus. -/
theorem preprocessTower_modulus_product
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F)) :
    ((preprocessTower g hg hgmonic hgfree h separant).map fun branch =>
      branch.separantTerminal.modulus).prod = g := by
  let radical := radicalState g hg hgmonic hgfree h
  rw [preprocessTower, prod_map_flatMap]
  simp only [List.map_map, makePreprocessedBranch]
  calc
    _ = ((factorTower radical).attach.map fun attached => attached.1.modulus).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro attached _
      exact separantTower_modulus_product radical attached.1 attached.2 separant
    _ = ((factorTower radical).map TerminalGCDBranch.modulus).prod :=
      prod_map_attach (factorTower radical) TerminalGCDBranch.modulus
    _ = g := by simpa [radical] using factorTower_modulus_product radical

/-- Across both D5 passes, the nested sum of base degree times retained vertical degree stays
within the original block's base-by-fiber degree budget. -/
theorem preprocessTower_weighted_sum_le
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic) :
    let radical := radicalState g hg hgmonic hgfree h
    ((factorTower radical).attach.map fun attached =>
      ((factorTower (separantState radical attached.1 attached.2 separant)).map
        fun terminal => terminal.modulus.natDegree *
          (terminalGoodPolynomial
            (separantState radical attached.1 attached.2 separant) terminal).natDegree).sum).sum ≤
      g.natDegree * h.toCPolynomial.natDegree := by
  let radical := radicalState g hg hgmonic hgfree h
  have hfirst :
      ((factorTower radical).attach.map fun attached =>
        ((factorTower (separantState radical attached.1 attached.2 separant)).map
          fun terminal => terminal.modulus.natDegree *
            (terminalGoodPolynomial
              (separantState radical attached.1 attached.2 separant)
              terminal).natDegree).sum).sum ≤
        ((factorTower radical).attach.map fun attached =>
          attached.1.modulus.natDegree *
            (terminalQuotientPolynomial radical attached.1).natDegree).sum := by
    apply List.sum_le_sum
    intro attached _
    exact separantTower_weighted_sum_le radical attached.1 attached.2 separant
  calc
    _ ≤ ((factorTower radical).attach.map fun attached =>
        attached.1.modulus.natDegree *
          (terminalQuotientPolynomial radical attached.1).natDegree).sum := hfirst
    _ = ((factorTower radical).map fun terminal => terminal.modulus.natDegree *
        (terminalQuotientPolynomial radical terminal).natDegree).sum := by
      exact sum_map_attach (factorTower radical) fun terminal =>
        terminal.modulus.natDegree * (terminalQuotientPolynomial radical terminal).natDegree
    _ ≤ radical.modulus.natDegree * radical.dividend.toCPolynomial.natDegree :=
      terminalQuotient_weighted_sum_le radical hhmonic
    _ = g.natDegree * h.toCPolynomial.natDegree := rfl

/-- The executable flattened output satisfies the same base-by-fiber degree budget. -/
theorem preprocessTower_output_weighted_sum_le
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h separant : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic) :
    ((preprocessTower g hg hgmonic hgfree h separant).map fun branch =>
      branch.separantTerminal.modulus.natDegree * branch.good.toCPolynomial.natDegree).sum ≤
        g.natDegree * h.toCPolynomial.natDegree := by
  let radical := radicalState g hg hgmonic hgfree h
  rw [preprocessTower, sum_map_flatMap]
  simp only [List.map_map, makePreprocessedBranch]
  change ((factorTower radical).attach.map fun attached =>
    ((factorTower (separantState radical attached.1 attached.2 separant)).map
      fun terminal => terminal.modulus.natDegree *
        (FiberPolynomial.toCPolynomial (FiberPolynomial.ofCPolynomial
          (terminalGoodPolynomial
            (separantState radical attached.1 attached.2 separant)
            terminal))).natDegree).sum).sum ≤ _
  simp only [FiberPolynomial.toCPolynomial_ofCPolynomial]
  exact preprocessTower_weighted_sum_le g hg hgmonic hgfree h separant hhmonic

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
