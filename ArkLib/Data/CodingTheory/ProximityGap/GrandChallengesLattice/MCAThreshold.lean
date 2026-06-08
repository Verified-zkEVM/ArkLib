/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCountRatio
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumErdosHeilbronn
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice.Radii

/-!
# GrandChallengesLattice — MCAThreshold

MCA lattice threshold definitions and uniqueness.

Split from `GrandChallengesLattice.lean` for longFile hygiene (#110).
-/

set_option linter.style.longFile 2000

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open Code

namespace GrandChallengesLattice

/-! ## The MCA lattice threshold

`mcaSatisfies C ε* j` says the lattice radius `j/n` keeps `ε_mca` within `ε*`. By
`epsMCA_mono` this predicate is *downward closed* in `j`, so the set of satisfying `j` is
an initial segment of `Fin (n+1)`; its maximum (when the set is nonempty) is the faithful
lattice threshold the paper asks to determine. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- At radius `1/n`, any witness set satisfying the MCA size clause is full or omits exactly
one coordinate. -/
theorem mcaEventWitness_j1_shape (S : Finset ι)
    (hS : (S.card : ℝ≥0) ≥
      (1 - mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1))) *
        (Fintype.card ι : ℝ≥0)) :
    S = Finset.univ ∨ ∃ i : ι, S = Finset.univ.erase i :=
  exists_eq_univ_or_eq_univ_erase_of_card_pred_le S
    (mcaEventWitness_card_pred_le_j1 S hS)

/-- Event-level radius-`1/n` inventory for the MCA/J1 proof: every bad event has a witness
window that is either all coordinates or all but one coordinate. -/
theorem mcaEvent_j1_witness_inventory
    {A : Type} [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (u₀ u₁ : ι → A) (γ : F)
    (h : mcaEvent (F := F) C
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ γ) :
    ∃ S : Finset ι,
      (S = Finset.univ ∨ ∃ i : ι, S = Finset.univ.erase i) ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn C S u₀ u₁ := by
  rcases h with ⟨S, hS, hline, hno⟩
  exact ⟨S, mcaEventWitness_j1_shape S hS, hline, hno⟩

/-- A radius-`1/n` MCA event over Reed-Solomon produces the ratio constraints needed for
the J1 quadratic/algebraic cap.

The theorem packages only the formal reduction.  The remaining hard input is the independent
algebraic statement that the set of scalars satisfying these constraints has cardinality at
most two. -/
theorem mcaEvent_j1_exists_window_ratio_constraints
    (domain : ι ↪ F) {k : ℕ} {u₀ u₁ : ι → F} {γ : F}
    (h : mcaEvent (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ γ) :
    ∃ S : Finset ι,
      (S = Finset.univ ∨ ∃ i : ι, S = Finset.univ.erase i) ∧
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁ ∧
      (∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
        cT domain k T (u₀ + γ • u₁) = 0) ∧
      ∃ T : Finset ι, T ⊆ S ∧ T.card = k + 1 ∧ cT domain k T u₁ ≠ 0 ∧
        γ = -(cT domain k T u₀) / cT domain k T u₁ := by
  rcases mcaEvent_j1_witness_inventory
      (C := (ReedSolomon.code domain k : Set (ι → F))) u₀ u₁ γ h with
    ⟨S, hshape, ⟨w, hw, hwline⟩, hpair⟩
  have hneS : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁ :=
    nonExtendable_of_mcaEvent (ReedSolomon.code domain k) hw hwline hpair
  have hconstraints :
      ∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
        cT domain k T (u₀ + γ • u₁) = 0 := by
    intro T hTS hTcard
    refine (extendable_iff_cT_eq_zero domain hTcard (u₀ + γ • u₁)).mp ?_
    exact ⟨w, hw, fun i hi => hwline i (hTS hi)⟩
  obtain ⟨T, hTS, hTcard, hneT⟩ := exists_card_eq_subset_nonExtendable domain hneS
  have hne0 : cT domain k T u₁ ≠ 0 := fun h0 =>
    hneT ((extendable_iff_cT_eq_zero domain hTcard u₁).mpr h0)
  have hline0 : cT domain k T (u₀ + γ • u₁) = 0 :=
    hconstraints T hTS hTcard
  have hlin : cT domain k T u₀ + γ * cT domain k T u₁ = 0 := by
    rw [← smul_eq_mul, ← map_smul, ← map_add]
    exact hline0
  have hγ : γ = -(cT domain k T u₀) / cT domain k T u₁ := by
    field_simp
    linear_combination hlin
  exact ⟨S, hshape, hneS, hconstraints, T, hTS, hTcard, hne0, hγ⟩

open Classical in
/-- The J1 finite-algebra constraint for one scalar: `γ` is supported by a full or one-omitted
window, `u₁` is non-extendable there, and every `(k+1)`-subset inside the window makes the
line word `u₀ + γ • u₁` locally Reed-Solomon extendable. -/
def j1RatioConstraint (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) (γ : F) : Prop :=
  ∃ S : Finset ι,
    (S = Finset.univ ∨ ∃ i : ι, S = Finset.univ.erase i) ∧
    NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁ ∧
    (∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
      cT domain k T (u₀ + γ • u₁) = 0)

/-- A J1 ratio constraint can always be witnessed on a one-point-omitted window.  The full-window
case contains a nonextendable `(k+1)`-subset; when `k+3 ≤ n` there is a coordinate outside that
subset, and enlarging the subset to the corresponding omitted window preserves non-extendability. -/
theorem j1RatioConstraint_to_omitted
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F))
        (Finset.univ.erase i) u₁ ∧
      ∀ T : Finset ι, T ⊆ Finset.univ.erase i → T.card = k + 1 →
        cT domain k T (u₀ + γ • u₁) = 0 := by
  classical
  rcases hγ with ⟨S, hshape, hneS, hconstraints⟩
  rcases hshape with rfl | ⟨i, rfl⟩
  · obtain ⟨T₀, _hT₀sub, hT₀card, hneT₀⟩ :=
      exists_card_eq_subset_nonExtendable domain hneS
    have hT₀lt : T₀.card < (Finset.univ : Finset ι).card := by
      rw [hT₀card, Finset.card_univ]
      omega
    obtain ⟨i, _hiuniv, hiT₀⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hT₀lt
    have hT₀_erase : T₀ ⊆ Finset.univ.erase i := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun hxi => hiT₀ (hxi ▸ hx), Finset.mem_univ x⟩
    refine ⟨i, ?_, ?_⟩
    · rintro ⟨v, hvC, hvagree⟩
      exact hneT₀ ⟨v, hvC, fun x hx => hvagree x (hT₀_erase hx)⟩
    · intro T _hTsub hTcard
      exact hconstraints T (Finset.subset_univ T) hTcard
  · exact ⟨i, hneS, hconstraints⟩

/-- If every `(k+1)`-subset of a window has vanishing `cT`, then the word extends to an
RS codeword on the whole window.  This is the contrapositive of the existing
`exists_card_eq_subset_nonExtendable` gluing lemma. -/
theorem extendableOn_of_forall_cT_eq_zero
    (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u : ι → F}
    (hvanish : ∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
      cT domain k T u = 0) :
    ∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ S, w i = u i := by
  classical
  by_contra hne
  have hneS : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u := by
    simpa [NonExtendableOn] using hne
  obtain ⟨T, hTS, hTcard, hneT⟩ := exists_card_eq_subset_nonExtendable domain hneS
  exact hneT ((extendable_iff_cT_eq_zero domain hTcard u).mpr (hvanish T hTS hTcard))

/-- High-coefficient bridge from local `cT` constraints.  Once all `(k+1)`-subset
coefficients vanish, the window interpolant is the degree-`< k` RS polynomial extending the word,
so every coefficient of degree at least `k` is zero. -/
theorem cT_vanish_on_window_highCoeff_zero
    (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u : ι → F}
    (hkS : k ≤ S.card)
    (hvanish : ∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
      cT domain k T u = 0)
    {d : ℕ} (hkd : k ≤ d) :
    (Lagrange.interpolate S (fun i => domain i) u).coeff d = 0 := by
  classical
  obtain ⟨w, hwC, hwagree⟩ := extendableOn_of_forall_cT_eq_zero domain hvanish
  rw [SetLike.mem_coe, ReedSolomon.mem_code_iff_exists_polynomial] at hwC
  obtain ⟨p, hpdeg, hp⟩ := hwC
  have hinj : Set.InjOn (fun i => domain i) (↑S : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  have hpdegS : p.degree < (S.card : WithBot ℕ) :=
    lt_of_lt_of_le hpdeg (by exact_mod_cast hkS)
  have hpeval : ∀ i ∈ S, p.eval (domain i) = u i := by
    intro i hi
    have hw_eval : w i = p.eval (domain i) := by
      have := congrFun hp i
      simpa [ReedSolomon.evalOnPoints] using this
    rw [← hw_eval, hwagree i hi]
  have hinterp :
      Lagrange.interpolate S (fun i => domain i) u = p :=
    (Lagrange.eq_interpolate_of_eval_eq
      (v := fun i => domain i) (r := u) (s := S) (f := p)
      hinj hpdegS hpeval).symm
  rw [hinterp]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    (lt_of_lt_of_le hpdeg (by exact_mod_cast hkd))

/-- Nonextendability on a window is detected by a nonzero coefficient at some degree `≥ k`
of the window interpolant. -/
theorem exists_highCoeff_ne_zero_of_nonExtendableOn
    (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u : ι → F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u) :
    ∃ d : ℕ, k ≤ d ∧
      (Lagrange.interpolate S (fun i => domain i) u).coeff d ≠ 0 := by
  classical
  by_contra hnone
  have hall : ∀ d : ℕ, k ≤ d →
      (Lagrange.interpolate S (fun i => domain i) u).coeff d = 0 := by
    intro d hkd
    by_contra hcoeff
    exact hnone ⟨d, hkd, hcoeff⟩
  let P := Lagrange.interpolate S (fun i => domain i) u
  have hPdeg : P.degree < (k : WithBot ℕ) := by
    dsimp [P]
    exact (Polynomial.degree_lt_iff_coeff_zero _ k).mpr hall
  have hinj : Set.InjOn (fun i => domain i) (↑S : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  have hPeval : ∀ i ∈ S, P.eval (domain i) = u i := by
    intro i hi
    dsimp [P]
    exact Lagrange.eval_interpolate_at_node u hinj hi
  refine hne ⟨ReedSolomon.evalOnPoints domain P, ?_, ?_⟩
  · rw [SetLike.mem_coe, ReedSolomon.mem_code_iff_exists_polynomial]
    exact ⟨P, hPdeg, rfl⟩
  · intro i hi
    change P.eval (domain i) = u i
    exact hPeval i hi

/-- Strong coefficient-ratio form of a J1 ratio constraint.  Every constrained scalar is obtained
from some omitted window and some nonzero high coefficient of the direction word. -/
theorem j1RatioConstraint_exists_omitted_highCoeff_ratio
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι, ∃ d : ℕ,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F))
        (Finset.univ.erase i) u₁ ∧
      k ≤ d ∧
      (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u₁).coeff d ≠ 0 ∧
      γ = - (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u₀).coeff d /
        (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u₁).coeff d := by
  classical
  obtain ⟨i, hne, hvanish⟩ := j1RatioConstraint_to_omitted domain hk hγ
  obtain ⟨d, hkd, hcoeff_ne⟩ := exists_highCoeff_ne_zero_of_nonExtendableOn domain hne
  let W : Finset ι := Finset.univ.erase i
  let Pγ := Lagrange.interpolate W (fun a => domain a) (u₀ + γ • u₁)
  let P₀ := Lagrange.interpolate W (fun a => domain a) u₀
  let P₁ := Lagrange.interpolate W (fun a => domain a) u₁
  have hcoeff : Pγ.coeff d = P₀.coeff d + γ * P₁.coeff d := by
    change ((Lagrange.interpolate W (fun a => domain a)) (u₀ + γ • u₁)).coeff d =
      ((Lagrange.interpolate W (fun a => domain a)) u₀).coeff d +
        γ * ((Lagrange.interpolate W (fun a => domain a)) u₁).coeff d
    rw [map_add, map_smul, Polynomial.coeff_add, Polynomial.coeff_smul]
    simp
  have hkW : k ≤ W.card := by
    dsimp [W]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  have hzero : Pγ.coeff d = 0 :=
    cT_vanish_on_window_highCoeff_zero domain hkW hvanish hkd
  have hlin : P₀.coeff d + γ * P₁.coeff d = 0 := by
    rw [← hcoeff]
    exact hzero
  have hcoeff_ne' : P₁.coeff d ≠ 0 := by
    simpa [P₁, W] using hcoeff_ne
  have hγeq : γ = -P₀.coeff d / P₁.coeff d := by
    field_simp
    linear_combination hlin
  refine ⟨i, d, hne, hkd, ?_, ?_⟩
  · simpa [P₁, W] using hcoeff_ne'
  · simpa [P₀, P₁, W] using hγeq

/-- Omitted-window interpolation is obtained from the full interpolant by cancelling its top
coefficient with the omitted-window nodal polynomial.  This is the division-free form of the
J1 high-coefficient bridge. -/
theorem interpolate_univ_erase_eq_full_sub_topCoeff_mul_nodal
    (domain : ι ↪ F) (i : ι) (u : ι → F) :
    Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u =
      Lagrange.interpolate Finset.univ (fun a => domain a) u -
        Polynomial.C ((Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1)) *
          Lagrange.nodal (Finset.univ.erase i) (fun a => domain a) := by
  classical
  let W : Finset ι := Finset.univ.erase i
  let P : Polynomial F := Lagrange.interpolate Finset.univ (fun a => domain a) u
  let Z : Polynomial F := Lagrange.nodal W (fun a => domain a)
  let R : Polynomial F := P - Polynomial.C (P.coeff (Fintype.card ι - 1)) * Z
  have hWcard : W.card = Fintype.card ι - 1 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hinjUniv : Set.InjOn (fun a => domain a) (↑(Finset.univ : Finset ι) : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  have hinjW : Set.InjOn (fun a => domain a) (↑W : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  have hPdeg : P.degree < (Fintype.card ι : WithBot ℕ) := by
    dsimp [P]
    simpa [Finset.card_univ] using
      (Lagrange.degree_interpolate_lt
        (s := (Finset.univ : Finset ι)) (v := fun a => domain a) (r := u) hinjUniv)
  have hZnat : Z.natDegree = Fintype.card ι - 1 := by
    simp [Z, hWcard]
  have hZmonic : Z.Monic := by
    dsimp [Z]
    exact Lagrange.nodal_monic
  have hZtop : Z.coeff (Fintype.card ι - 1) = 1 := by
    simpa [hZnat] using (Polynomial.Monic.coeff_natDegree hZmonic)
  have hZdeg : Z.degree = (W.card : WithBot ℕ) := by
    dsimp [Z]
    exact Lagrange.degree_nodal
  have hRdeg : R.degree < (W.card : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    by_cases hm_top : m = Fintype.card ι - 1
    · subst hm_top
      dsimp [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hZtop]
      ring
    · have hmW : W.card < m :=
        lt_of_le_of_ne hm (fun h => hm_top (h.symm.trans hWcard))
      have hnle : Fintype.card ι ≤ m := by
        rw [hWcard] at hmW
        have hnpos : 0 < Fintype.card ι := Fintype.card_pos
        omega
      have hPzero : P.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hPdeg (by exact_mod_cast hnle))
      have hZzero : Z.coeff m = 0 := by
        refine Polynomial.coeff_eq_zero_of_degree_lt ?_
        rw [hZdeg]
        exact_mod_cast hmW
      dsimp [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hPzero, hZzero, mul_zero, sub_zero]
  have hReval : ∀ a ∈ W, R.eval (domain a) = u a := by
    intro a ha
    have hPeval : P.eval (domain a) = u a := by
      dsimp [P]
      simpa using
        (Lagrange.eval_interpolate_at_node
          (s := (Finset.univ : Finset ι)) (v := fun a => domain a) (r := u)
          (i := a) hinjUniv (Finset.mem_univ a))
    have hZeval : Z.eval (domain a) = 0 := by
      dsimp [Z]
      simpa using
        (Lagrange.eval_nodal_at_node (s := W) (v := fun a => domain a) (i := a) ha)
    dsimp [R]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hPeval, hZeval,
      mul_zero, sub_zero]
  have hRinterp :
      R = Lagrange.interpolate W (fun a => domain a) u :=
    Lagrange.eq_interpolate_of_eval_eq
      (v := fun a => domain a) (r := u) (s := W) (f := R) hinjW hRdeg hReval
  change Lagrange.interpolate W (fun a => domain a) u = R
  exact hRinterp.symm

/-- Coefficient form of
`interpolate_univ_erase_eq_full_sub_topCoeff_mul_nodal`. -/
theorem interpolate_univ_erase_coeff_eq_full_sub_topCoeff_mul_nodal_coeff
    (domain : ι ↪ F) (i : ι) (u : ι → F) (d : ℕ) :
    (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u).coeff d =
      (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff d -
        (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1) *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff d := by
  rw [interpolate_univ_erase_eq_full_sub_topCoeff_mul_nodal domain i u,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul]

/-- The next-to-top coefficient of an omitted-window nodal polynomial is affine in the omitted
node, with constant term supplied by the full nodal polynomial. -/
theorem nodal_univ_erase_coeff_card_sub_two
    (domain : ι ↪ F) (i : ι) (hn : 2 ≤ Fintype.card ι) :
    (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
        (Fintype.card ι - 2) =
      (Lagrange.nodal Finset.univ (fun a => domain a)).coeff
        (Fintype.card ι - 1) + domain i := by
  classical
  let W : Finset ι := Finset.univ.erase i
  let Z : Polynomial F := Lagrange.nodal W (fun a => domain a)
  let N : Polynomial F := Lagrange.nodal Finset.univ (fun a => domain a)
  have hWcard : W.card = Fintype.card ι - 1 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hZnat : Z.natDegree = Fintype.card ι - 1 := by
    simp [Z, hWcard]
  have hZmonic : Z.Monic := by
    dsimp [Z]
    exact Lagrange.nodal_monic
  have hZtop : Z.coeff (Fintype.card ι - 1) = 1 := by
    simpa [hZnat] using (Polynomial.Monic.coeff_natDegree hZmonic)
  have hfactor : N = (Polynomial.X - Polynomial.C (domain i)) * Z := by
    dsimp [N, Z, W]
    exact Lagrange.nodal_eq_mul_nodal_erase (s := (Finset.univ : Finset ι))
      (v := fun a => domain a) (i := i) (Finset.mem_univ i)
  have hidx : Fintype.card ι - 2 + 1 = Fintype.card ι - 1 := by omega
  have hcoeff := congrArg
    (fun p : Polynomial F => p.coeff (Fintype.card ι - 2 + 1)) hfactor
  change N.coeff (Fintype.card ι - 2 + 1) =
      ((Polynomial.X - Polynomial.C (domain i)) * Z).coeff
        (Fintype.card ι - 2 + 1) at hcoeff
  rw [Polynomial.coeff_X_sub_C_mul] at hcoeff
  have hcoeff' : N.coeff (Fintype.card ι - 1) =
      Z.coeff (Fintype.card ι - 2) - domain i * Z.coeff (Fintype.card ι - 1) := by
    simpa [hidx] using hcoeff
  rw [hZtop, mul_one] at hcoeff'
  change Z.coeff (Fintype.card ι - 2) = N.coeff (Fintype.card ι - 1) + domain i
  rw [hcoeff']
  ring

/-- The second next-to-top coefficient of an omitted-window nodal polynomial satisfies the
recurrence obtained from `nodal univ = (X - C (domain i)) * nodal (univ.erase i)`. -/
theorem nodal_univ_erase_coeff_card_sub_three
    (domain : ι ↪ F) (i : ι) (hn : 3 ≤ Fintype.card ι) :
    (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
        (Fintype.card ι - 3) =
      (Lagrange.nodal Finset.univ (fun a => domain a)).coeff
        (Fintype.card ι - 2) +
      domain i *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
          (Fintype.card ι - 2) := by
  classical
  let W : Finset ι := Finset.univ.erase i
  let Z : Polynomial F := Lagrange.nodal W (fun a => domain a)
  let N : Polynomial F := Lagrange.nodal Finset.univ (fun a => domain a)
  have hfactor : N = (Polynomial.X - Polynomial.C (domain i)) * Z := by
    dsimp [N, Z, W]
    exact Lagrange.nodal_eq_mul_nodal_erase (s := (Finset.univ : Finset ι))
      (v := fun a => domain a) (i := i) (Finset.mem_univ i)
  have hidx : Fintype.card ι - 3 + 1 = Fintype.card ι - 2 := by omega
  have hcoeff := congrArg
    (fun p : Polynomial F => p.coeff (Fintype.card ι - 3 + 1)) hfactor
  change N.coeff (Fintype.card ι - 3 + 1) =
      ((Polynomial.X - Polynomial.C (domain i)) * Z).coeff
        (Fintype.card ι - 3 + 1) at hcoeff
  rw [Polynomial.coeff_X_sub_C_mul] at hcoeff
  have hcoeff' : N.coeff (Fintype.card ι - 2) =
      Z.coeff (Fintype.card ι - 3) - domain i * Z.coeff (Fintype.card ι - 2) := by
    simpa [hidx] using hcoeff
  change Z.coeff (Fintype.card ι - 3) =
    N.coeff (Fintype.card ι - 2) + domain i * Z.coeff (Fintype.card ι - 2)
  rw [hcoeff']
  ring

/-- J1 omitted-window high-coefficient bridge in the exact two-top-coefficient form needed for
the quadratic eliminant. -/
theorem cT_vanish_on_j1_window_two_top_coeffs
    (domain : ι ↪ F) {k : ℕ} {i : ι} {u : ι → F}
    (hk : k + 3 ≤ Fintype.card ι)
    (hvanish : ∀ T : Finset ι, T ⊆ Finset.univ.erase i → T.card = k + 1 →
      cT domain k T u = 0) :
    (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u).coeff
        (Fintype.card ι - 2) = 0 ∧
    (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a) u).coeff
        (Fintype.card ι - 3) = 0 := by
  classical
  have hkS : k ≤ (Finset.univ.erase i : Finset ι).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  constructor
  · exact cT_vanish_on_window_highCoeff_zero domain hkS hvanish (by omega)
  · exact cT_vanish_on_window_highCoeff_zero domain hkS hvanish (by omega)

/-- Full-interpolant coefficient equations forced by J1 local vanishing on an omitted window. -/
theorem cT_vanish_on_j1_window_full_top_coeff_equations
    (domain : ι ↪ F) {k : ℕ} {i : ι} {u : ι → F}
    (hk : k + 3 ≤ Fintype.card ι)
    (hvanish : ∀ T : Finset ι, T ⊆ Finset.univ.erase i → T.card = k + 1 →
      cT domain k T u = 0) :
    let P := Lagrange.interpolate Finset.univ (fun a => domain a) u
    let Zᵢ := Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)
    P.coeff (Fintype.card ι - 2) - P.coeff (Fintype.card ι - 1) * Zᵢ.coeff
        (Fintype.card ι - 2) = 0 ∧
    P.coeff (Fintype.card ι - 3) - P.coeff (Fintype.card ι - 1) * Zᵢ.coeff
        (Fintype.card ι - 3) = 0 := by
  classical
  obtain ⟨h₂, h₃⟩ := cT_vanish_on_j1_window_two_top_coeffs domain hk hvanish
  constructor
  · change
      (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 2) -
        (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1) *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
          (Fintype.card ι - 2) = 0
    exact
      (interpolate_univ_erase_coeff_eq_full_sub_topCoeff_mul_nodal_coeff
        domain i u (Fintype.card ι - 2)).symm.trans h₂
  · change
      (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 3) -
        (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1) *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
          (Fintype.card ι - 3) = 0
    exact
      (interpolate_univ_erase_coeff_eq_full_sub_topCoeff_mul_nodal_coeff
        domain i u (Fintype.card ι - 3)).symm.trans h₃

/-- The two full-interpolant equations from an omitted J1 window imply a single universal
quadratic relation among the full interpolant's top three coefficients.  The omitted coordinate
has been eliminated. -/
theorem full_top_quadratic_relation_of_j1_window_equations
    (domain : ι ↪ F) {i : ι} {u : ι → F}
    (hn : 3 ≤ Fintype.card ι)
    (h₂ :
      (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 2) -
        (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1) *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
          (Fintype.card ι - 2) = 0)
    (h₃ :
      (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 3) -
        (Lagrange.interpolate Finset.univ (fun a => domain a) u).coeff
          (Fintype.card ι - 1) *
        (Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)).coeff
          (Fintype.card ι - 3) = 0) :
    let P := Lagrange.interpolate Finset.univ (fun a => domain a) u
    let N := Lagrange.nodal Finset.univ (fun a => domain a)
    P.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 2) -
        N.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 2) +
      N.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 1) -
      P.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 3) = 0 := by
  classical
  let P := Lagrange.interpolate Finset.univ (fun a => domain a) u
  let N := Lagrange.nodal Finset.univ (fun a => domain a)
  let Zᵢ := Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)
  have hZ₂ : Zᵢ.coeff (Fintype.card ι - 2) =
      N.coeff (Fintype.card ι - 1) + domain i := by
    dsimp [Zᵢ, N]
    exact nodal_univ_erase_coeff_card_sub_two domain i (by omega)
  have hZ₃ : Zᵢ.coeff (Fintype.card ι - 3) =
      N.coeff (Fintype.card ι - 2) + domain i * Zᵢ.coeff (Fintype.card ι - 2) := by
    dsimp [Zᵢ, N]
    exact nodal_univ_erase_coeff_card_sub_three domain i hn
  have h₂₀ : P.coeff (Fintype.card ι - 2) -
      P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 2) = 0 := by
    dsimp [P, Zᵢ]
    exact h₂
  have h₃₀ : P.coeff (Fintype.card ι - 3) -
      P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 3) = 0 := by
    dsimp [P, Zᵢ]
    exact h₃
  have h₂' : P.coeff (Fintype.card ι - 2) =
      P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 2) :=
    sub_eq_zero.mp h₂₀
  have h₃' : P.coeff (Fintype.card ι - 3) =
      P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 3) :=
    sub_eq_zero.mp h₃₀
  change
    P.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 2) -
        N.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 2) +
      N.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 1) -
      P.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 3) = 0
  rw [h₂', h₃', hZ₃, hZ₂]
  ring

/-- J1 local vanishing on an omitted window implies the universal full-interpolant quadratic
relation. -/
theorem cT_vanish_on_j1_window_full_top_quadratic_relation
    (domain : ι ↪ F) {k : ℕ} {i : ι} {u : ι → F}
    (hk : k + 3 ≤ Fintype.card ι)
    (hvanish : ∀ T : Finset ι, T ⊆ Finset.univ.erase i → T.card = k + 1 →
      cT domain k T u = 0) :
    let P := Lagrange.interpolate Finset.univ (fun a => domain a) u
    let N := Lagrange.nodal Finset.univ (fun a => domain a)
    P.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 2) -
        N.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 2) +
      N.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 1) *
          P.coeff (Fintype.card ι - 1) -
      P.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 3) = 0 := by
  classical
  obtain ⟨h₂, h₃⟩ := cT_vanish_on_j1_window_full_top_coeff_equations domain hk hvanish
  exact full_top_quadratic_relation_of_j1_window_equations domain (by omega) h₂ h₃

/-- Direct coefficient form of a J1 ratio constraint: every constrained scalar has an omitted
window where `u₁` is non-extendable and the line word has the two top omitted-window coefficients
equal to zero. -/
theorem j1RatioConstraint_exists_omitted_two_top_coeffs
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F))
        (Finset.univ.erase i) u₁ ∧
      (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a)
          (u₀ + γ • u₁)).coeff (Fintype.card ι - 2) = 0 ∧
      (Lagrange.interpolate (Finset.univ.erase i) (fun a => domain a)
          (u₀ + γ • u₁)).coeff (Fintype.card ι - 3) = 0 := by
  classical
  obtain ⟨i, hne, hvanish⟩ := j1RatioConstraint_to_omitted domain hk hγ
  exact ⟨i, hne, cT_vanish_on_j1_window_two_top_coeffs domain hk hvanish⟩

/-- Full-interpolant coefficient form of a J1 ratio constraint.  This is the form used by the
remaining quadratic eliminant: the two top omitted-window vanishing equations become equations
in the full interpolant and the omitted-window nodal coefficients. -/
theorem j1RatioConstraint_exists_omitted_full_top_coeff_equations
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F))
        (Finset.univ.erase i) u₁ ∧
      (let P := Lagrange.interpolate Finset.univ (fun a => domain a) (u₀ + γ • u₁)
       let Zᵢ := Lagrange.nodal (Finset.univ.erase i) (fun a => domain a)
       P.coeff (Fintype.card ι - 2) -
           P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 2) = 0 ∧
       P.coeff (Fintype.card ι - 3) -
           P.coeff (Fintype.card ι - 1) * Zᵢ.coeff (Fintype.card ι - 3) = 0) := by
  classical
  obtain ⟨i, hne, hvanish⟩ := j1RatioConstraint_to_omitted domain hk hγ
  exact ⟨i, hne, cT_vanish_on_j1_window_full_top_coeff_equations domain hk hvanish⟩

/-- Universal quadratic relation forced by a J1 ratio constraint.  The omitted witness is still
returned for the nonextendability side condition, but the displayed polynomial relation no longer
contains the omitted coordinate. -/
theorem j1RatioConstraint_exists_omitted_full_top_quadratic_relation
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F))
        (Finset.univ.erase i) u₁ ∧
      (let P := Lagrange.interpolate Finset.univ (fun a => domain a) (u₀ + γ • u₁)
       let N := Lagrange.nodal Finset.univ (fun a => domain a)
       P.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 2) -
           N.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 1) *
             P.coeff (Fintype.card ι - 2) +
         N.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 1) *
             P.coeff (Fintype.card ι - 1) -
         P.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 3) = 0) := by
  classical
  obtain ⟨i, hne, hvanish⟩ := j1RatioConstraint_to_omitted domain hk hγ
  exact ⟨i, hne, cT_vanish_on_j1_window_full_top_quadratic_relation domain hk hvanish⟩

open Classical in
/-- The affine polynomial in the line scalar whose value is `a + γ * b`. -/
noncomputable def j1AffineCoeffPolynomial (a b : F) : Polynomial F :=
  Polynomial.C a + Polynomial.C b * Polynomial.X

@[simp] theorem j1AffineCoeffPolynomial_eval (a b γ : F) :
    (j1AffineCoeffPolynomial a b).eval γ = a + γ * b := by
  simp [j1AffineCoeffPolynomial]
  ring

open Classical in
/-- The universal quadratic eliminant for J1 ratio constraints.

Its coefficients are the top three full-interpolant coefficients of the base word `u₀`, the
direction word `u₁`, and the top two coefficients of the full nodal polynomial. -/
noncomputable def j1FullTopQuadratic
    (domain : ι ↪ F) (u₀ u₁ : ι → F) : Polynomial F :=
  let P₀ := Lagrange.interpolate Finset.univ (fun a => domain a) u₀
  let P₁ := Lagrange.interpolate Finset.univ (fun a => domain a) u₁
  let N := Lagrange.nodal Finset.univ (fun a => domain a)
  let q := j1AffineCoeffPolynomial
    (P₀.coeff (Fintype.card ι - 1)) (P₁.coeff (Fintype.card ι - 1))
  let r := j1AffineCoeffPolynomial
    (P₀.coeff (Fintype.card ι - 2)) (P₁.coeff (Fintype.card ι - 2))
  let s := j1AffineCoeffPolynomial
    (P₀.coeff (Fintype.card ι - 3)) (P₁.coeff (Fintype.card ι - 3))
  r * r - Polynomial.C (N.coeff (Fintype.card ι - 1)) * q * r +
    Polynomial.C (N.coeff (Fintype.card ι - 2)) * q * q - q * s

/-- Every J1 ratio-constraint scalar is a root of the universal top-coefficient quadratic. -/
theorem j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    (j1FullTopQuadratic domain u₀ u₁).eval γ = 0 := by
  classical
  obtain ⟨_i, _hne, hrel⟩ :=
    j1RatioConstraint_exists_omitted_full_top_quadratic_relation domain hk hγ
  let Pγ := Lagrange.interpolate Finset.univ (fun a => domain a) (u₀ + γ • u₁)
  let P₀ := Lagrange.interpolate Finset.univ (fun a => domain a) u₀
  let P₁ := Lagrange.interpolate Finset.univ (fun a => domain a) u₁
  let N := Lagrange.nodal Finset.univ (fun a => domain a)
  have hcoeff (d : ℕ) : Pγ.coeff d = P₀.coeff d + γ * P₁.coeff d := by
    change ((Lagrange.interpolate Finset.univ (fun a => domain a)) (u₀ + γ • u₁)).coeff d =
      ((Lagrange.interpolate Finset.univ (fun a => domain a)) u₀).coeff d +
        γ * ((Lagrange.interpolate Finset.univ (fun a => domain a)) u₁).coeff d
    rw [map_add, map_smul, Polynomial.coeff_add, Polynomial.coeff_smul]
    simp
  have hrelP :
      Pγ.coeff (Fintype.card ι - 2) * Pγ.coeff (Fintype.card ι - 2) -
          N.coeff (Fintype.card ι - 1) * Pγ.coeff (Fintype.card ι - 1) *
            Pγ.coeff (Fintype.card ι - 2) +
        N.coeff (Fintype.card ι - 2) * Pγ.coeff (Fintype.card ι - 1) *
            Pγ.coeff (Fintype.card ι - 1) -
        Pγ.coeff (Fintype.card ι - 1) * Pγ.coeff (Fintype.card ι - 3) = 0 := by
    change
      (let P := Lagrange.interpolate Finset.univ (fun a => domain a) (u₀ + γ • u₁)
       let N := Lagrange.nodal Finset.univ (fun a => domain a)
       P.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 2) -
           N.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 1) *
             P.coeff (Fintype.card ι - 2) +
         N.coeff (Fintype.card ι - 2) * P.coeff (Fintype.card ι - 1) *
             P.coeff (Fintype.card ι - 1) -
       P.coeff (Fintype.card ι - 1) * P.coeff (Fintype.card ι - 3) = 0)
    exact hrel
  have hpoly :
      (j1FullTopQuadratic domain u₀ u₁).eval γ =
      (P₀.coeff (Fintype.card ι - 2) + γ * P₁.coeff (Fintype.card ι - 2)) *
          (P₀.coeff (Fintype.card ι - 2) + γ * P₁.coeff (Fintype.card ι - 2)) -
        N.coeff (Fintype.card ι - 1) *
          (P₀.coeff (Fintype.card ι - 1) + γ * P₁.coeff (Fintype.card ι - 1)) *
          (P₀.coeff (Fintype.card ι - 2) + γ * P₁.coeff (Fintype.card ι - 2)) +
        N.coeff (Fintype.card ι - 2) *
          (P₀.coeff (Fintype.card ι - 1) + γ * P₁.coeff (Fintype.card ι - 1)) *
          (P₀.coeff (Fintype.card ι - 1) + γ * P₁.coeff (Fintype.card ι - 1)) -
        (P₀.coeff (Fintype.card ι - 1) + γ * P₁.coeff (Fintype.card ι - 1)) *
          (P₀.coeff (Fintype.card ι - 3) + γ * P₁.coeff (Fintype.card ι - 3)) := by
    simp [j1FullTopQuadratic, P₀, P₁, N]
  rw [hpoly]
  rw [← hcoeff (Fintype.card ι - 2), ← hcoeff (Fintype.card ι - 1),
    ← hcoeff (Fintype.card ι - 3)]
  exact hrelP

open Classical in
/-- The finite scalar set cut out by the J1 window ratio constraints.

The remaining J1 algebraic core is to show this set has cardinality at most two for every
stack `(u₀,u₁)`. -/
noncomputable def j1RatioConstraintBadScalars
    (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) : Finset F :=
  Finset.univ.filter (j1RatioConstraint domain k u₀ u₁)

open Classical in
@[simp] theorem mem_j1RatioConstraintBadScalars
    (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) (γ : F) :
    γ ∈ j1RatioConstraintBadScalars domain k u₀ u₁ ↔
      j1RatioConstraint domain k u₀ u₁ γ := by
  simp [j1RatioConstraintBadScalars]

/-- Finite-set form of the remaining J1 algebraic core: it is enough to rule out three
distinct scalars satisfying the J1 ratio constraint. -/
theorem j1RatioConstraintBadScalars_card_le_two_of_not_three
    (domain : ι ↪ F) {k : ℕ} (u₀ u₁ : ι → F)
    (hno : ¬ ∃ γ₀ γ₁ γ₂ : F,
      γ₀ ≠ γ₁ ∧ γ₀ ≠ γ₂ ∧ γ₁ ≠ γ₂ ∧
      j1RatioConstraint domain k u₀ u₁ γ₀ ∧
      j1RatioConstraint domain k u₀ u₁ γ₁ ∧
      j1RatioConstraint domain k u₀ u₁ γ₂) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2 := by
  classical
  by_contra hle
  have hgt : 2 < (j1RatioConstraintBadScalars domain k u₀ u₁).card :=
    Nat.lt_of_not_ge hle
  rw [Finset.two_lt_card_iff] at hgt
  rcases hgt with ⟨γ₀, γ₁, γ₂, hγ₀, hγ₁, hγ₂, h01, h02, h12⟩
  rw [mem_j1RatioConstraintBadScalars] at hγ₀
  rw [mem_j1RatioConstraintBadScalars] at hγ₁
  rw [mem_j1RatioConstraintBadScalars] at hγ₂
  exact hno ⟨γ₀, γ₁, γ₂, h01, h02, h12, hγ₀, hγ₁, hγ₂⟩

/-- Conditional J1 bad-count cap.  Once the independent finite-algebra theorem
`(j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2` is proved, every actual bad scalar
at radius `1/n` injects into that constraint set. -/
theorem mcaBadCount_j1_le_two_of_ratioConstraint_card_le_two
    (domain : ι ↪ F) {k : ℕ} (u₀ u₁ : ι → F)
    (hcard : (j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2) :
    mcaBadCount (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ ≤ 2 := by
  classical
  unfold mcaBadCount
  refine le_trans (Finset.card_le_card ?_) hcard
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  rw [mem_j1RatioConstraintBadScalars]
  rcases mcaEvent_j1_exists_window_ratio_constraints domain hγ.2 with
    ⟨S, hshape, hneS, hconstraints, _T, _hTS, _hTcard, _hne0, _hγ⟩
  exact ⟨S, hshape, hneS, hconstraints⟩

/-- Conditional J1 bad-count cap in the cleaner no-three form.  The remaining algebra can now
target `not_three_j1_ratioConstraints` directly. -/
theorem mcaBadCount_j1_le_two_of_not_three_ratioConstraints
    (domain : ι ↪ F) {k : ℕ} (u₀ u₁ : ι → F)
    (hno : ¬ ∃ γ₀ γ₁ γ₂ : F,
      γ₀ ≠ γ₁ ∧ γ₀ ≠ γ₂ ∧ γ₁ ≠ γ₂ ∧
      j1RatioConstraint domain k u₀ u₁ γ₀ ∧
      j1RatioConstraint domain k u₀ u₁ γ₁ ∧
      j1RatioConstraint domain k u₀ u₁ γ₂) :
    mcaBadCount (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ ≤ 2 :=
  mcaBadCount_j1_le_two_of_ratioConstraint_card_le_two domain u₀ u₁
    (j1RatioConstraintBadScalars_card_le_two_of_not_three domain u₀ u₁ hno)

/-- `ε_mca(C, j/n) ≤ ε*` at the lattice radius `j/n`. Decidable so the satisfying set is a
`Finset`. -/
def mcaSatisfies (C : Set (ι → F)) (ε_star : ℝ≥0) (j : Fin (Fintype.card ι + 1)) : Prop :=
  epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) ≤ (ε_star : ENNReal)

noncomputable instance (C : Set (ι → F)) (ε_star : ℝ≥0) :
    DecidablePred (mcaSatisfies C ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure.** If `j/n` keeps `ε_mca ≤ ε*` and `i ≤ j`, then so does `i/n`.
Direct consequence of `epsMCA_mono`. -/
theorem mcaSatisfies_downward_closed (C : Set (ι → F)) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : mcaSatisfies C ε_star j) :
    mcaSatisfies C ε_star i :=
  le_trans (epsMCA_mono (F := F) C (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points, as a `Finset (Fin (n+1))`. -/
noncomputable def mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (mcaSatisfies C ε_star)

@[simp] theorem mem_mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ mcaSatSet C ε_star ↔ mcaSatisfies C ε_star j := by
  simp [mcaSatSet]

/-- Bridge from the `Fin (n+1)` MCA lattice encoding to the canonical `Finset ℕ`
encoding in `GrandChallengeLattice.lean`. -/
theorem val_mem_mcaLatticeSet_iff_mcaSatisfies
    (C : Set (ι → F)) (ε_star : ℝ≥0) (j : Fin (Fintype.card ι + 1)) :
    j.val ∈ GrandChallenges.mcaLatticeSet C ε_star ↔ mcaSatisfies C ε_star j := by
  classical
  rw [GrandChallenges.mcaLatticeSet, Finset.mem_filter, Finset.mem_range]
  simp [mcaSatisfies, mcaLatticePoint, j.isLt]

/-- **Existence (nonemptiness) hypothesis.** The paper's "assuming `|F|` sufficiently large
so that such a `δ*_C` exists": some lattice radius keeps `ε_mca` within `ε*`. Equivalently,
the satisfying set is nonempty. This is the *only* hypothesis the lattice encoding needs;
once it holds, the threshold is a well-defined finite quantity. -/
def mcaThresholdExists (C : Set (ι → F)) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star j

theorem mcaSatSet_nonempty_iff_mcaLatticeSet_nonempty
    (C : Set (ι → F)) (ε_star : ℝ≥0) :
    (mcaSatSet C ε_star).Nonempty ↔ (GrandChallenges.mcaLatticeSet C ε_star).Nonempty := by
  classical
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, (val_mem_mcaLatticeSet_iff_mcaSatisfies C ε_star j).mpr
      ((mem_mcaSatSet C ε_star).mp hj)⟩
  · rintro ⟨j, hj⟩
    have hj_range : j < Fintype.card ι + 1 := by
      rw [GrandChallenges.mcaLatticeSet, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    exact ⟨⟨j, hj_range⟩, (mem_mcaSatSet C ε_star).mpr
      ((val_mem_mcaLatticeSet_iff_mcaSatisfies C ε_star ⟨j, hj_range⟩).mp hj)⟩

theorem mcaSatSet_nonempty_iff (C : Set (ι → F)) (ε_star : ℝ≥0) :
    (mcaSatSet C ε_star).Nonempty ↔ mcaThresholdExists C ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mpr hj⟩

/-- **The faithful MCA lattice threshold** `δ*_C = mcaThreshold / n`. Defined as the greatest
lattice index whose radius keeps `ε_mca` within `ε*`, under the existence hypothesis `hne`.
**Determining its value is the open ABF26 §1 Grand MCA Challenge** (the $1M problem); the
witnesses below merely bracket it. -/
noncomputable def mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) : Fin (Fintype.card ι + 1) :=
  (mcaSatSet C ε_star).max' ((mcaSatSet_nonempty_iff C ε_star).mpr hne)

/-- **Existence half.** The lattice threshold itself satisfies the MCA bound:
`ε_mca(C, mcaThreshold/n) ≤ ε*`. -/
theorem mcaThreshold_spec (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) :
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) := by
  have h := (mcaSatSet C ε_star).max'_mem ((mcaSatSet_nonempty_iff C ε_star).mpr hne)
  exact (mem_mcaSatSet C ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ mcaThreshold`. -/
theorem le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaSatisfies C ε_star j) :
    j ≤ mcaThreshold C ε_star hne :=
  (mcaSatSet C ε_star).le_max' j ((mem_mcaSatSet C ε_star).mpr hj)

/-- The `Fin (n+1)` MCA threshold and the canonical `Finset ℕ` MCA threshold have the
same value under `Fin.val`. -/
theorem mcaThreshold_val_eq_mcaLatticeThreshold
    (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne_fin : mcaThresholdExists C ε_star)
    (hne_nat : (GrandChallenges.mcaLatticeSet C ε_star).Nonempty) :
    (mcaThreshold C ε_star hne_fin).val =
      GrandChallenges.mcaLatticeThreshold C ε_star hne_nat := by
  classical
  apply le_antisymm
  · have hsat := mcaThreshold_spec C ε_star hne_fin
    exact Finset.le_max' (GrandChallenges.mcaLatticeSet C ε_star)
      (mcaThreshold C ε_star hne_fin).val
      ((val_mem_mcaLatticeSet_iff_mcaSatisfies C ε_star
        (mcaThreshold C ε_star hne_fin)).mpr hsat)
  · have hmem :=
      (GrandChallenges.mcaLatticeSet C ε_star).max'_mem hne_nat
    have hmem_set :
        GrandChallenges.mcaLatticeThreshold C ε_star hne_nat ∈
          GrandChallenges.mcaLatticeSet C ε_star := by
      simpa [GrandChallenges.mcaLatticeThreshold] using hmem
    have hrange : GrandChallenges.mcaLatticeThreshold C ε_star hne_nat <
        Fintype.card ι + 1 := by
      have h := hmem_set
      simp [GrandChallenges.mcaLatticeSet] at h
      exact Nat.lt_succ_of_le h.1
    have hsat :
        mcaSatisfies C ε_star
          ⟨GrandChallenges.mcaLatticeThreshold C ε_star hne_nat, hrange⟩ :=
      (val_mem_mcaLatticeSet_iff_mcaSatisfies C ε_star
        ⟨GrandChallenges.mcaLatticeThreshold C ε_star hne_nat, hrange⟩).mp hmem_set
    exact Fin.le_iff_val_le_val.mp (le_mcaThreshold C ε_star hne_fin hsat)

/-- **Strict failure above the threshold.** Any lattice point strictly above `mcaThreshold`
fails the bound: `ε_mca(C, j/n) > ε*`. This is the lattice analogue of the (collapse-broken)
real strict-failure clause, and it holds here precisely because we are on the lattice. -/
theorem gt_mcaThreshold_exceeds (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaThreshold C ε_star hne < j) :
    epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) > (ε_star : ENNReal) := by
  by_contra h
  exact absurd (le_mcaThreshold C ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `mcaThreshold` is the *unique* lattice index that both satisfies the
bound and is maximal among satisfying indices. Hence the lattice threshold is well-defined:
existence + uniqueness of the maximal `j`. -/
theorem mcaThreshold_unique (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : mcaSatisfies C ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star i → i ≤ j) :
    j = mcaThreshold C ε_star hne :=
  le_antisymm (le_mcaThreshold C ε_star hne hsat)
    (hmax _ (mcaThreshold_spec C ε_star hne))

end GrandChallengesLattice

end ProximityGap

