/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.SingularRecursion
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Symbolic separant chains with actual active orders

The coefficient ring may contain an unevaluated challenge. Each stage records its actual
highest active jet, and its successor is the corresponding formal partial derivative.
Total jet degree bounds the chain length; each individual jet degree bounds the number
of times that jet can be selected. Thus a first-derivative cap survives the construction.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative.SymbolicSeparantChain

noncomputable section

open Polynomial MvPolynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- Total degree in the jet variables, over an arbitrary coefficient semiring. -/
def jetWeight (Q : DifferentialPolynomial R d) : ℕ :=
  Q.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1))

/-- Individual jet exponents are bounded by the total jet weight. -/
theorem jetDegree_le_jetWeight (Q : DifferentialPolynomial R d) (j : Fin (d + 1)) :
    jetDegree Q j ≤ jetWeight Q := by
  classical
  apply degreeOf_le_iff.mpr
  intro u hu
  have h := le_weightedTotalDegree (fun v : JetVariable d ↦ v.elim 0 (fun _ ↦ 1)) hu
  have hsum : u (some j) ≤ ∑ i : Fin (d + 1), u (some i) :=
    Finset.single_le_sum (f := fun i : Fin (d + 1) ↦ u (some i))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hbound : (∑ i : Fin (d + 1), u (some i)) ≤ jetWeight Q := by
    simpa [jetWeight, Finsupp.weight_apply, Finsupp.sum_fintype] using h
  exact hsum.trans hbound

/-- Every formal separant lowers total jet weight by at least one. -/
theorem jetWeight_separant_le (Q : DifferentialPolynomial R d) (j : Fin (d + 1)) :
    jetWeight (separant Q j) ≤ jetWeight Q - 1 :=
  weightedTotalDegree_pderiv_le_sub _ _ Q

/-- Concrete nonvanishing of small natural scalars suffices for an active separant
to remain nonzero, including characteristic zero. -/
theorem separant_ne_zero_of_cast_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (Q : DifferentialPolynomial R d) (j : Fin (d + 1)) (hj : DependsOnJet Q j)
    (hcast : ∀ m : ℕ, 0 < m → m ≤ jetWeight Q → (m : R) ≠ 0) :
    separant Q j ≠ 0 := by
  classical
  have hsupp : Q.support.Nonempty := support_nonempty.mpr <|
    ne_zero_of_degreeOf_ne_zero (i := some j) (Nat.ne_of_gt hj)
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup Q.support hsupp fun u ↦ u (some j)
  rw [← degreeOf_eq_sup (some j) Q] at heq
  have huj : 0 < u (some j) := by
    have hp : 0 < degreeOf (some j) Q := hj
    rwa [heq] at hp
  have hscalar : (u (some j) : R) ≠ 0 :=
    hcast _ huj (by rw [← heq]; exact jetDegree_le_jetWeight Q j)
  let v := u - Finsupp.single (some j) 1
  have hv : v + Finsupp.single (some j) 1 = u :=
    Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt huj)
  have hvj : v (some j) + 1 = u (some j) := by
    dsimp [v]
    simp only [Finsupp.single_eq_same]
    omega
  intro hz
  have hc := congrArg (MvPolynomial.coeff v) hz
  have hcastEq : (↑(v (some j)) + 1 : R) = (u (some j) : R) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast : ℕ → R) hvj
  rw [separant, coeff_pderiv, hv, hcastEq, MvPolynomial.coeff_zero] at hc
  exact mul_ne_zero (mem_support_iff.mp hu) hscalar hc

/-- An active stage retains its equation and the actual highest active jet. -/
abbrev Stage (R : Type*) [CommSemiring R] (d : ℕ) :=
  DifferentialPolynomial R d × Fin (d + 1)

/-- A genuine finite chain, whose successors are literal formal separants. The
terminal equation is nonzero and independent of all jet variables. -/
inductive Chain : DifferentialPolynomial R d → List (Stage R d) →
    DifferentialPolynomial R d → Prop where
  | terminal {Q} (hne : Q ≠ 0) (hterminal : highestActiveJet Q = none) : Chain Q [] Q
  | active {Q tail terminal} (j : Fin (d + 1)) (hne : Q ≠ 0)
      (hhighest : highestActiveJet Q = some j)
      (next : Chain (separant Q j) tail terminal) :
      Chain Q ((Q, j) :: tail) terminal

/-- Construct the entire symbolic chain by induction on its actual total jet weight. -/
theorem exists_chain [NoZeroDivisors R] [Nontrivial R]
    (Q : DifferentialPolynomial R d) (hne : Q ≠ 0)
    (hcast : ∀ m : ℕ, 0 < m → m ≤ jetWeight Q → (m : R) ≠ 0) :
    ∃ stages terminal, Chain Q stages terminal := by
  induction hdeg : jetWeight Q using Nat.strong_induction_on generalizing Q with
  | h w ih =>
      cases hh : highestActiveJet Q with
      | none => exact ⟨[], Q, Chain.terminal hne hh⟩
      | some j =>
          have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some hh).1
          have hpos : 0 < jetWeight Q := hactive.trans_le (jetDegree_le_jetWeight Q j)
          have hstep := jetWeight_separant_le Q j
          have hlt : jetWeight (separant Q j) < w := by omega
          obtain ⟨stages, terminal, hchain⟩ := ih _ hlt (separant Q j)
            (separant_ne_zero_of_cast_ne_zero Q j hactive hcast)
            (fun m hm hmw ↦ hcast m hm (hmw.trans (hstep.trans (Nat.sub_le _ _)))) rfl
          exact ⟨(Q, j) :: stages, terminal, Chain.active j hne hh hchain⟩

/-- Characteristic zero supplies the scalar condition without a degree restriction. -/
theorem exists_chain_charZero [NoZeroDivisors R] [Nontrivial R] [CharZero R]
    (Q : DifferentialPolynomial R d) (hne : Q ≠ 0) :
    ∃ stages terminal, Chain Q stages terminal :=
  exists_chain Q hne (fun _ hm _ ↦ Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))

/-- Positive characteristic strictly larger than total jet degree supplies the scalar condition. -/
theorem exists_chain_of_lt_ringChar [NoZeroDivisors R] [Nontrivial R]
    (Q : DifferentialPolynomial R d) (hne : Q ≠ 0) (hchar : jetWeight Q < ringChar R) :
    ∃ stages terminal, Chain Q stages terminal := by
  apply exists_chain Q hne
  intro m hm hmw hz
  exact Nat.not_dvd_of_pos_of_lt hm (hmw.trans_lt hchar) ((ringChar.spec R m).mp hz)

/-- Chain length is bounded by total jet degree, not the sum of individual degrees. -/
theorem Chain.length_le {Q terminal : DifferentialPolynomial R d} {stages : List (Stage R d)}
    (hc : Chain Q stages terminal) : stages.length ≤ jetWeight Q := by
  induction hc with
  | terminal hne hterminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      have hp := (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      have hpos := hp.trans_le (jetDegree_le_jetWeight Q j)
      have hd := jetWeight_separant_le Q j
      simp only [List.length_cons]
      omega

/-- All stages retain their actual nonzero equation, actual highest active order,
and every individual derivative cap of the initial equation. -/
theorem Chain.stage_contract {Q terminal : DifferentialPolynomial R d}
    {stages : List (Stage R d)} (hc : Chain Q stages terminal) :
    ∀ stage ∈ stages, stage.1 ≠ 0 ∧ highestActiveJet stage.1 = some stage.2 ∧
      jetWeight stage.1 ≤ jetWeight Q ∧ ∀ j, jetDegree stage.1 j ≤ jetDegree Q j := by
  induction hc with
  | terminal hne hterminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      intro stage hstage
      rcases List.mem_cons.mp hstage with rfl | hstage
      · exact ⟨hne, hhighest, le_rfl, fun _ ↦ le_rfl⟩
      · obtain ⟨hn, hh, hw, hj⟩ := ih stage hstage
        exact ⟨hn, hh, hw.trans ((jetWeight_separant_le Q j).trans (Nat.sub_le _ _)),
          fun i ↦ (hj i).trans (jetDegree_separant_le Q j i)⟩

/-- Along the actual stage list, total jet degrees strictly decrease and highest
active orders never increase. -/
theorem Chain.ordered_stage_metadata {Q terminal : DifferentialPolynomial R d}
    {stages : List (Stage R d)} (hc : Chain Q stages terminal) :
    stages.Pairwise fun earlier later ↦
      jetWeight later.1 < jetWeight earlier.1 ∧ later.2 ≤ earlier.2 := by
  induction hc with
  | terminal hne hterminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro stage hstage
      obtain ⟨_, hs, hw, hcaps⟩ := next.stage_contract stage hstage
      have hroot := isHighestActiveJet_of_highestActiveJet_eq_some hhighest
      have hpos : 0 < jetWeight Q := hroot.1.trans_le (jetDegree_le_jetWeight Q j)
      have hstep := jetWeight_separant_le Q j
      refine ⟨by dsimp; omega, ?_⟩
      by_contra horder
      have hlt : j < stage.2 := lt_of_not_ge horder
      apply hroot.2 stage.2 hlt
      have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some hs).1
      exact hactive.trans_le ((hcaps stage.2).trans (jetDegree_separant_le Q j stage.2))

/-- Selecting a given derivative consumes its exponent cap, even if the highest
active order drops elsewhere along the chain. -/
theorem Chain.count_selected_le {Q terminal : DifferentialPolynomial R d}
    {stages : List (Stage R d)} (hc : Chain Q stages terminal) (i : Fin (d + 1)) :
    (stages.filter fun stage ↦ stage.2 = i).length ≤ jetDegree Q i := by
  classical
  induction hc with
  | terminal hne hterminal => simp
  | @active Q tail terminal j hne hhighest next ih =>
      by_cases hji : j = i
      · subst j
        have hp : 0 < jetDegree Q i :=
          (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
        have hd := degreeOf_pderiv_le_sub_one (some i) Q
        change jetDegree (separant Q i) i ≤ jetDegree Q i - 1 at hd
        simp only [List.filter_cons, decide_true, if_true, List.length_cons]
        omega
      · simpa [List.filter_cons, hji] using ih.trans (jetDegree_separant_le Q j i)

/-- The final equation is a nonzero polynomial in the distinguished variable over
the coefficient ring; with challenge coefficients this is a polynomial in `X,Z`. -/
theorem Chain.terminal_contract {Q terminal : DifferentialPolynomial R d}
    {stages : List (Stage R d)} (hc : Chain Q stages terminal) :
    terminal ≠ 0 ∧ highestActiveJet terminal = none ∧
      ∃ q : R[X], q ≠ 0 ∧ q.toMvPolynomial (none : JetVariable d) = terminal := by
  have hn : terminal ≠ 0 ∧ highestActiveJet terminal = none := by
    induction hc with
    | terminal hne hterminal => exact ⟨hne, hterminal⟩
    | active j hne hhighest next ih => exact ih
  obtain ⟨q, hq⟩ := exists_toMvPolynomial_eq_of_highestActiveJet_eq_none terminal hn.2
  refine ⟨hn.1, hn.2, q, ?_, hq⟩
  intro hz
  apply hn.1
  rw [← hq, hz]
  simp

/-- Every root not vanishing on the terminal equation reaches a regular stage,
uniformly under coefficient specialization to any extension field. -/
theorem Chain.regular_coverage {E : Type*} [Field E] (φ : R →+* E)
    {Q terminal : DifferentialPolynomial R d} {stages : List (Stage R d)}
    (hc : Chain Q stages terminal) (P : E[X])
    (hroot : differentialSpecialization (MvPolynomial.map φ Q) P = 0)
    (hterminal : differentialSpecialization (MvPolynomial.map φ terminal) P ≠ 0) :
    ∃ stage ∈ stages,
      differentialSpecialization (MvPolynomial.map φ stage.1) P = 0 ∧
      differentialSpecialization (separant (MvPolynomial.map φ stage.1) stage.2) P ≠ 0 := by
  induction hc with
  | terminal hne hlast => exact (hterminal hroot).elim
  | @active Q tail terminal j hne hhighest next ih =>
      by_cases hnext : differentialSpecialization (MvPolynomial.map φ (separant Q j)) P = 0
      · obtain ⟨stage, hstage, hs⟩ := ih hnext hterminal
        exact ⟨stage, List.mem_cons_of_mem _ hstage, hs⟩
      · refine ⟨(Q, j), List.mem_cons_self, hroot, ?_⟩
        simpa only [separant, pderiv_map] using hnext

variable {F : Type*} [Field F]

/-- A symbolic polynomial-coefficient chain exists under the usual characteristic
condition on the base field. The challenge remains an indeterminate throughout. -/
theorem exists_symbolic_chain (Q : DifferentialPolynomial F[X] d) (hne : Q ≠ 0)
    (hchar : ringChar F = 0 ∨ jetWeight Q < ringChar F) :
    ∃ stages terminal, Chain Q stages terminal := by
  apply exists_chain Q hne
  intro m hm hmw hz
  have hscalar : (m : F) = 0 := by
    simpa using congrArg (Polynomial.eval (0 : F)) hz
  have hdiv := (ringChar.spec F m).mp hscalar
  rcases hchar with hzero | hlt
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hm (hmw.trans_lt hlt) hdiv

/-- Symbolic challenge height cannot increase under a jet derivative. -/
theorem separant_challengeHeight_le (Q : DifferentialPolynomial F[X] d) (j : Fin (d + 1))
    {h : ℕ} (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    ∀ u, (MvPolynomial.coeff u (separant Q j)).natDegree ≤ h := by
  intro u
  rw [separant, coeff_pderiv]
  have hscalar : (↑(u (some j)) + 1 : F[X]).natDegree = 0 := by
    rw [show (↑(u (some j)) + 1 : F[X]) = Polynomial.C (↑(u (some j)) + 1 : F) by simp]
    exact Polynomial.natDegree_C _
  exact (Polynomial.natDegree_mul_le).trans (by
    simpa only [hscalar, add_zero] using hQ (u + Finsupp.single (some j) 1))

/-- A single height budget covers all symbolic stages and the terminal equation. -/
theorem Chain.challengeHeight_le {Q terminal : DifferentialPolynomial F[X] d}
    {stages : List (Stage F[X] d)} (hc : Chain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    (∀ stage ∈ stages, ∀ u, (MvPolynomial.coeff u stage.1).natDegree ≤ h) ∧
      ∀ u, (MvPolynomial.coeff u terminal).natDegree ≤ h := by
  induction hc with
  | terminal hne hterminal => exact ⟨by simp, hQ⟩
  | @active Q tail terminal j hne hhighest next ih =>
      obtain ⟨hs, ht⟩ := ih (separant_challengeHeight_le Q j hQ)
      refine ⟨?_, ht⟩
      intro stage hstage
      rcases List.mem_cons.mp hstage with rfl | hstage
      · exact hQ
      · exact hs stage hstage

/-- Coefficient specialization preserves the absence of all jet variables. -/
theorem highestActiveJet_map_eq_none {E : Type*} [CommSemiring E] (φ : R →+* E)
    (Q : DifferentialPolynomial R d) (hQ : highestActiveJet Q = none) :
    highestActiveJet (MvPolynomial.map φ Q) = none := by
  apply (highestActiveJet_eq_none_iff _).mpr
  intro j hj
  have hzero := jetDegree_eq_zero_of_highestActiveJet_eq_none Q hQ j
  have hle : jetDegree (MvPolynomial.map φ Q) j ≤ jetDegree Q j := by
    apply degreeOf_le_iff.mpr
    intro u hu
    exact monomial_le_degreeOf (some j) (support_map_subset φ Q hu)
  have hpos : 0 < jetDegree (MvPolynomial.map φ Q) j := hj
  omega

/-- One actual nonzero coefficient of the terminal equation gives a challenge
obstruction of degree at most the initial height. Outside its roots the terminal
equation admits no differential root, over every extension field. -/
theorem Chain.exists_terminal_obstruction {Q terminal : DifferentialPolynomial F[X] d}
    {stages : List (Stage F[X] d)} (hc : Chain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h) :
    ∃ obstruction : F[X], obstruction ≠ 0 ∧ obstruction.natDegree ≤ h ∧
      ∀ {E : Type*} [Field E] (iota : F →+* E) (z : E),
        obstruction.eval₂ iota z ≠ 0 → ∀ P : E[X],
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom iota z) terminal) P ≠ 0 := by
  obtain ⟨htne, htnone, _⟩ := hc.terminal_contract
  obtain ⟨u, hu⟩ := support_nonempty.mpr htne
  refine ⟨MvPolynomial.coeff u terminal, mem_support_iff.mp hu,
    hc.challengeHeight_le hQ |>.2 u, ?_⟩
  intro E _ iota z hobs P hroot
  let φ : F[X] →+* E := Polynomial.eval₂RingHom iota z
  have hmap : MvPolynomial.map φ terminal ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.coeff u) hz
    apply hobs
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, φ,
      Polynomial.coe_eval₂RingHom] using he
  have hnone := highestActiveJet_map_eq_none φ terminal htnone
  obtain ⟨q, hq⟩ := exists_toMvPolynomial_eq_of_highestActiveJet_eq_none _ hnone
  have hqzero : q = 0 := by
    rw [← differentialSpecialization_toMvPolynomial (d := d) q P, hq]
    exact hroot
  apply hmap
  rw [← hq, hqzero]
  simp

/-- A concrete height-bounded exceptional set suffices for regular-stage coverage
of every specialized differential root, simultaneously for all polynomials. -/
theorem Chain.exists_exceptional_regular_coverage
    {Q terminal : DifferentialPolynomial F[X] d} {stages : List (Stage F[X] d)}
    (hc : Chain Q stages terminal) {h : ℕ}
    (hQ : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    {E : Type*} [Field E] (iota : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ P : E[X],
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom iota z) Q) P = 0 →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1)
              stage.2) P ≠ 0 := by
  classical
  obtain ⟨obstruction, hne, hdegree, hcover⟩ := hc.exists_terminal_obstruction hQ
  let exceptional := (obstruction.map iota).roots.toFinset
  refine ⟨exceptional, ?_, ?_⟩
  · exact ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans
      (Polynomial.natDegree_map_le.trans hdegree)
  · intro z hz P hroot
    have hobs : obstruction.eval₂ iota z ≠ 0 := by
      intro heval
      apply hz
      apply Multiset.mem_toFinset.mpr
      have hmapne : obstruction.map iota ≠ 0 := by
        intro hz
        apply hne
        apply Polynomial.map_injective iota iota.injective
        simpa using hz
      apply (Polynomial.mem_roots hmapne).mpr
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using heval
    exact hc.regular_coverage (Polynomial.eval₂RingHom iota z) P hroot (hcover iota z hobs P)

end

end ReedSolomon.HiddenDerivative.SymbolicSeparantChain
