/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
public import ArkLib.Data.Polynomial.Differential.SingularRecursion

/-!
# Separant chains

A separant chain of a differential polynomial `Q` over a commutative semiring `R` is the sequence
of equations visited by the singular recursion of [Kop15] when it is run on `Q` itself rather than
on one solution: each stage records an equation together with its computed highest active jet
`Y_s`, and the next equation is the separant `∂Q/∂Y_s`. The chain ends at a nonzero equation with
no active jet, that is, a nonzero polynomial in `X` alone.

The chain is built before any coefficient is evaluated. When `R = K[Z]` carries an unevaluated
challenge `Z`, one chain serves every specialization `Z ↦ z` at once: every solution of the
specialized equation that is not a solution of the specialized terminal equation is a regular
solution of some specialized stage. The terminal equation has a nonzero coefficient in `K[Z]` of
degree at most the challenge degree of `Q`, so outside at most that many values of `z` the
specialized terminal equation has no solution.

Along a chain, `jetTotalDegree` strictly decreases, so the chain has at most `jetTotalDegree Q`
stages. The highest active jets never increase, and the jet `Y_i` is selected at most
`jetDegree Q i` times.

## Main statements

* `SeparantChain`: the chain relation, with `SeparantStage` the type of its stages.
* `exists_separantChain`: a nonzero equation over a semiring without zero divisors, whose jet
  degrees satisfy the cast hypotheses `JetDegreeCastsNeZero`, has a separant chain;
  `exists_separantChain_of_ringChar` derives the cast hypotheses from a characteristic bound.
* `SeparantChain.length_le`, `SeparantChain.pairwise_stages`,
  `SeparantChain.length_filter_le_jetDegree`: the length bound, the ordering of stages, and the
  number of times each jet is selected.
* `SeparantChain.exists_jetPrefixPresentation_of_mem`: every stage equation has a presentation at
  its highest active jet, of the same total jet degree, whose top jet degree is at most the degree
  of the starting equation in that jet.
* `SeparantChain.exists_regular_stage`: a solution of the specialized equation that does not solve
  the specialized terminal equation is a regular solution of a specialized stage.
* `SeparantChain.exists_terminal_obstruction` and `SeparantChain.exists_finset_regular_stage`: over
  `R[X]`, a nonzero challenge polynomial of bounded degree controls the terminal equation, and
  outside its roots every solution reaches a regular stage.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.3 and Section 4.2.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- A stage of a separant chain: an equation and its highest active jet. -/
abbrev SeparantStage (R : Type*) [CommSemiring R] (d : ℕ) :=
  DifferentialPolynomial R d × Fin (d + 1)

/-- `SeparantChain Q stages terminal`: starting from `Q`, repeatedly replacing an equation by its
separant in its computed highest active jet visits the equations of `stages`, each paired with that
jet, and stops at `terminal`, a nonzero equation with no active jet. Every equation on the chain is
nonzero. -/
inductive SeparantChain : DifferentialPolynomial R d → List (SeparantStage R d) →
    DifferentialPolynomial R d → Prop where
  /-- A nonzero equation with no active jet is its own terminal equation. -/
  | terminal {Q} (hne : Q ≠ 0) (hterminal : highestActiveJet Q = none) : SeparantChain Q [] Q
  /-- A nonzero equation with highest active jet `Y_j` is followed by its separant in `Y_j`. -/
  | active {Q tail terminal} (j : Fin (d + 1)) (hne : Q ≠ 0)
      (hhighest : highestActiveJet Q = some j)
      (next : SeparantChain (separant Q j) tail terminal) :
      SeparantChain Q ((Q, j) :: tail) terminal

/-! ### Existence -/

/-- A nonzero equation over a commutative semiring without zero divisors has a separant chain when
it satisfies the cast hypotheses `JetDegreeCastsNeZero` at every jet. -/
theorem exists_separantChain [NoZeroDivisors R] {Q : DifferentialPolynomial R d} (hne : Q ≠ 0)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j) :
    ∃ stages terminal, SeparantChain Q stages terminal := by
  induction Q using (singularStep_wellFounded (F := R) (d := d)).induction with
  | _ Q ih =>
  cases hh : highestActiveJet Q with
  | none => exact ⟨[], Q, SeparantChain.terminal hne hh⟩
  | some j =>
      have hstep := singularStep_separant Q hh
      obtain ⟨hnext, hcastNext⟩ := singularStep_preserves hcast hstep
      obtain ⟨stages, terminal, hchain⟩ := ih _ hstep hnext hcastNext
      exact ⟨(Q, j) :: stages, terminal, SeparantChain.active j hne hh hchain⟩

/-- A nonzero equation over a commutative semiring without zero divisors has a separant chain when
the characteristic is zero or exceeds its total jet degree. -/
theorem exists_separantChain_of_ringChar [NoZeroDivisors R] {Q : DifferentialPolynomial R d}
    (hne : Q ≠ 0) (hchar : ringChar R = 0 ∨ jetTotalDegree Q < ringChar R) :
    ∃ stages terminal, SeparantChain Q stages terminal :=
  exists_separantChain hne fun j ↦ jetDegreeCastsNeZero_of_ringChar
    (hchar.imp_right (jetDegree_le_total Q j).trans_lt)

/-! ### Structure of a chain -/

namespace SeparantChain

variable {Q terminal : DifferentialPolynomial R d} {stages : List (SeparantStage R d)}

/-- The starting equation of a separant chain is nonzero. -/
theorem ne_zero (hc : SeparantChain Q stages terminal) : Q ≠ 0 := by
  cases hc with
  | terminal hne _ => exact hne
  | active _ hne _ _ => exact hne

/-- The terminal equation of a separant chain is nonzero. -/
theorem terminal_ne_zero (hc : SeparantChain Q stages terminal) : terminal ≠ 0 := by
  induction hc with
  | terminal hne _ => exact hne
  | active _ _ _ _ ih => exact ih

/-- The terminal equation of a separant chain has no active jet. -/
theorem highestActiveJet_terminal (hc : SeparantChain Q stages terminal) :
    highestActiveJet terminal = none := by
  induction hc with
  | terminal _ hterminal => exact hterminal
  | active _ _ _ _ ih => exact ih

/-- The terminal equation of a separant chain is a nonzero polynomial in `X` alone. -/
theorem exists_toMvPolynomial_eq_terminal (hc : SeparantChain Q stages terminal) :
    ∃ q : R[X], q ≠ 0 ∧ q.toMvPolynomial (none : JetVariable d) = terminal := by
  obtain ⟨q, hq⟩ :=
    exists_toMvPolynomial_eq_of_highestActiveJet_eq_none hc.highestActiveJet_terminal
  refine ⟨q, fun hz ↦ hc.terminal_ne_zero ?_, hq⟩
  rw [← hq, hz, map_zero]

/-- Every stage of a separant chain is nonzero, its jet is its computed highest active jet, and its
total and individual jet degrees are at most those of the starting equation. -/
private theorem stage_properties (hc : SeparantChain Q stages terminal) :
    ∀ stage ∈ stages, stage.1 ≠ 0 ∧ highestActiveJet stage.1 = some stage.2 ∧
      jetTotalDegree stage.1 ≤ jetTotalDegree Q ∧ ∀ j, jetDegree stage.1 j ≤ jetDegree Q j := by
  induction hc with
  | terminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      intro stage hstage
      rcases List.mem_cons.mp hstage with rfl | hstage
      · exact ⟨hne, hhighest, le_rfl, fun _ ↦ le_rfl⟩
      · obtain ⟨hn, hh, hw, hj⟩ := ih stage hstage
        exact ⟨hn, hh, hw.trans ((separant_total_le Q j).trans (Nat.sub_le _ _)),
          fun i ↦ (hj i).trans (jetDegree_separant_le Q j i)⟩

/-- Every stage equation of a separant chain is nonzero. -/
theorem ne_zero_of_mem (hc : SeparantChain Q stages terminal) {stage : SeparantStage R d}
    (hstage : stage ∈ stages) : stage.1 ≠ 0 :=
  (hc.stage_properties stage hstage).1

/-- The jet recorded at a stage is the computed highest active jet of its equation. -/
theorem highestActiveJet_eq_of_mem (hc : SeparantChain Q stages terminal)
    {stage : SeparantStage R d} (hstage : stage ∈ stages) :
    highestActiveJet stage.1 = some stage.2 :=
  (hc.stage_properties stage hstage).2.1

/-- A stage equation has total jet degree at most that of the starting equation. -/
theorem jetTotalDegree_le_of_mem (hc : SeparantChain Q stages terminal)
    {stage : SeparantStage R d} (hstage : stage ∈ stages) :
    jetTotalDegree stage.1 ≤ jetTotalDegree Q :=
  (hc.stage_properties stage hstage).2.2.1

/-- A stage equation has every individual jet degree at most that of the starting equation. -/
theorem jetDegree_le_of_mem (hc : SeparantChain Q stages terminal)
    {stage : SeparantStage R d} (hstage : stage ∈ stages) (j : Fin (d + 1)) :
    jetDegree stage.1 j ≤ jetDegree Q j :=
  (hc.stage_properties stage hstage).2.2.2 j

/-- A separant chain has at most `jetTotalDegree Q` stages. -/
theorem length_le (hc : SeparantChain Q stages terminal) :
    stages.length ≤ jetTotalDegree Q := by
  induction hc with
  | terminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      have hlt := jetTotalDegree_separant_lt
        (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      simp only [List.length_cons]
      omega

/-- Along a separant chain, the total jet degrees of the stage equations strictly decrease and
their highest active jets never increase. -/
theorem pairwise_stages (hc : SeparantChain Q stages terminal) :
    stages.Pairwise fun earlier later ↦
      jetTotalDegree later.1 < jetTotalDegree earlier.1 ∧ later.2 ≤ earlier.2 := by
  induction hc with
  | terminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      refine List.pairwise_cons.mpr ⟨fun stage hstage ↦ ⟨?_, ?_⟩, ih⟩
      · have hroot := isHighestActiveJet_of_highestActiveJet_eq_some hhighest
        exact (next.jetTotalDegree_le_of_mem hstage).trans_lt (jetTotalDegree_separant_lt hroot.1)
      · by_contra horder
        have hroot := isHighestActiveJet_of_highestActiveJet_eq_some hhighest
        apply hroot.2 stage.2 (lt_of_not_ge horder)
        have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
          (next.highestActiveJet_eq_of_mem hstage)).1
        exact hactive.trans_le ((next.jetDegree_le_of_mem hstage stage.2).trans
          (jetDegree_separant_le Q j stage.2))

/-- Along a separant chain, the jet `Y_i` is selected at most `jetDegree Q i` times, since each
selection lowers the degree in `Y_i` by at least one and no stage raises it. -/
theorem length_filter_le_jetDegree (hc : SeparantChain Q stages terminal) (i : Fin (d + 1)) :
    (stages.filter fun stage ↦ stage.2 = i).length ≤ jetDegree Q i := by
  induction hc with
  | terminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      by_cases hji : j = i
      · subst j
        have hp : 0 < jetDegree Q i :=
          (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
        have hd := jetDegree_separant_le_sub_one Q i
        simp only [List.filter_cons, decide_true, ite_true, List.length_cons]
        omega
      · simpa [List.filter_cons, hji] using ih.trans (jetDegree_separant_le Q j i)

/-- Every stage equation has a presentation at its highest active jet. The presentation is
nonzero, has the total jet degree of the stage equation, and its degree in the top variable is at
most the degree of the starting equation in the stage's jet. -/
theorem exists_jetPrefixPresentation_of_mem (hc : SeparantChain Q stages terminal)
    {stage : SeparantStage R d} (hstage : stage ∈ stages) :
    ∃ A : JetPrefixPresentation stage.1 stage.2, A.equation ≠ 0 ∧
      jetTotalDegree A.equation = jetTotalDegree stage.1 ∧
      jetDegree A.equation (Fin.last stage.2.val) ≤ jetDegree Q stage.2 := by
  obtain ⟨A⟩ := nonempty_jetPrefixPresentation stage.1
    (isHighestActiveJet_of_highestActiveJet_eq_some (hc.highestActiveJet_eq_of_mem hstage))
  exact ⟨A, A.equation_ne_zero (hc.ne_zero_of_mem hstage), A.jetTotalDegree_equation,
    A.jetDegree_equation_last ▸ hc.jetDegree_le_of_mem hstage stage.2⟩

/-! ### Solutions after a coefficient map -/

/-- Let `φ : R →+* E` map the coefficients. A solution `P` of the mapped starting equation that
does not solve the mapped terminal equation solves the mapped equation of some stage, and is not a
solution of the separant of that mapped equation in the stage's jet. -/
theorem exists_regular_stage {E : Type*} [CommSemiring E] (φ : R →+* E)
    (hc : SeparantChain Q stages terminal) {P : E[X]}
    (hroot : differentialSpecialization (MvPolynomial.map φ Q) P = 0)
    (hterminal : differentialSpecialization (MvPolynomial.map φ terminal) P ≠ 0) :
    ∃ stage ∈ stages,
      differentialSpecialization (MvPolynomial.map φ stage.1) P = 0 ∧
      differentialSpecialization (separant (MvPolynomial.map φ stage.1) stage.2) P ≠ 0 := by
  induction hc with
  | terminal => exact (hterminal hroot).elim
  | @active Q tail terminal j hne hhighest next ih =>
      by_cases hnext : differentialSpecialization (MvPolynomial.map φ (separant Q j)) P = 0
      · obtain ⟨stage, hstage, hs⟩ := ih hnext hterminal
        exact ⟨stage, List.mem_cons_of_mem _ hstage, hs⟩
      · exact ⟨(Q, j), List.mem_cons_self, hroot, by rwa [← map_separant]⟩

/-- Let `φ : R →+* E` map the coefficients. If the mapped terminal equation is nonzero, it has no
solution. -/
theorem differentialSpecialization_map_terminal_ne_zero {E : Type*} [CommSemiring E]
    (φ : R →+* E) (hc : SeparantChain Q stages terminal)
    (hmap : MvPolynomial.map φ terminal ≠ 0) (P : E[X]) :
    differentialSpecialization (MvPolynomial.map φ terminal) P ≠ 0 := fun hP ↦
  hmap (eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none
    (highestActiveJet_map_eq_none φ hc.highestActiveJet_terminal) hP)

end SeparantChain

/-! ### Polynomial coefficients -/

/-- Over the coefficient ring `R[X]`, a separant does not raise the maximal degree of a
coefficient: if every coefficient of `Q` has degree at most `h`, so does every coefficient of each
separant of `Q`. -/
theorem natDegree_coeff_separant_le {Q : DifferentialPolynomial R[X] d} (j : Fin (d + 1)) {h : ℕ}
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) (u : JetVariable d →₀ ℕ) :
    ((separant Q j).coeff u).natDegree ≤ h := by
  rw [separant, MvPolynomial.coeff_pderiv, ← Nat.cast_succ]
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_natCast, add_zero] using hQ (u + Finsupp.single (some j) 1))

namespace SeparantChain

variable {Q terminal : DifferentialPolynomial R[X] d} {stages : List (SeparantStage R[X] d)}
  {h : ℕ}

/-- Over `R[X]`, if every coefficient of the starting equation has degree at most `h`, so does
every coefficient of every stage equation. -/
theorem natDegree_coeff_le_of_mem (hc : SeparantChain Q stages terminal)
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) {stage : SeparantStage R[X] d}
    (hstage : stage ∈ stages) (u : JetVariable d →₀ ℕ) :
    (stage.1.coeff u).natDegree ≤ h := by
  induction hc with
  | terminal => simp at hstage
  | @active Q tail terminal j hne hhighest next ih =>
      rcases List.mem_cons.mp hstage with rfl | hstage
      · exact hQ u
      · exact ih (natDegree_coeff_separant_le j hQ) hstage

/-- Over `R[X]`, if every coefficient of the starting equation has degree at most `h`, so does
every coefficient of the terminal equation. -/
theorem natDegree_coeff_terminal_le (hc : SeparantChain Q stages terminal)
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) (u : JetVariable d →₀ ℕ) :
    (terminal.coeff u).natDegree ≤ h := by
  induction hc with
  | terminal => exact hQ u
  | active j _ _ _ ih => exact ih (natDegree_coeff_separant_le j hQ)

/-- Over `R[X]`, if every coefficient of the starting equation has degree at most `h`, some nonzero
`obstruction : R[X]` of degree at most `h` controls the terminal equation: for every coefficient
map `ι : R →+* E` and every `z : E` with `obstruction.eval₂ ι z ≠ 0`, the terminal equation
specialized at `X ↦ z` has no solution. -/
theorem exists_terminal_obstruction (hc : SeparantChain Q stages terminal)
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) :
    ∃ obstruction : R[X], obstruction ≠ 0 ∧ obstruction.natDegree ≤ h ∧
      ∀ {E : Type*} [CommSemiring E] (ι : R →+* E) (z : E),
        obstruction.eval₂ ι z ≠ 0 → ∀ P : E[X],
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) terminal) P ≠ 0 := by
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hc.terminal_ne_zero
  refine ⟨terminal.coeff u, MvPolynomial.mem_support_iff.mp hu,
    hc.natDegree_coeff_terminal_le hQ u, fun ι z hobs P ↦ ?_⟩
  refine hc.differentialSpecialization_map_terminal_ne_zero _ (fun hz ↦ hobs ?_) P
  have hcoeff := congrArg (fun p ↦ p.coeff u) hz
  rw [MvPolynomial.coeff_map] at hcoeff
  simpa using hcoeff

/-- Over `R[X]`, if every coefficient of the starting equation has degree at most `h`, then for an
injective map `ι : R →+* E` into a domain there is a set of at most `h` values `z` outside of
which the following holds for every `P : E[X]`: if `P` solves the starting equation specialized at
`X ↦ z`, it solves the specialized equation of some stage and does not solve the separant of that
equation in the stage's jet. -/
theorem exists_finset_regular_stage (hc : SeparantChain Q stages terminal)
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) {E : Type*} [CommRing E] [IsDomain E]
    (ι : R →+* E) (hι : Function.Injective ι) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ P : E[X],
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0 →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) stage.2) P ≠ 0 := by
  classical
  obtain ⟨obstruction, hne, hdegree, hcover⟩ := hc.exists_terminal_obstruction hQ
  have hmapne : obstruction.map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff hι).mpr hne
  refine ⟨(obstruction.map ι).roots.toFinset, ?_, fun z hz P hroot ↦ ?_⟩
  · exact ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans
      (Polynomial.natDegree_map_le.trans hdegree)
  · have hobs : obstruction.eval₂ ι z ≠ 0 := fun heval ↦ hz <| Multiset.mem_toFinset.mpr <|
      (Polynomial.mem_roots hmapne).mpr (by rwa [Polynomial.IsRoot, Polynomial.eval_map])
    exact hc.exists_regular_stage _ hroot (hcover ι z hobs P)

end SeparantChain

end

end PolynomialDifferential
