/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorCharZeroSolutions
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SharpCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.DerivativeCounting
/-!
# Cap-sensitive first-order differential list counting

For a first-order differential equation of total jet degree at most `μ`, whose degree in `Y₁`
is at most `M`, a separant chain can select the top jet at most `M` times. At total degree
`j`, an order-zero stage costs `j`; an order-one stage costs

```text
j (1 + τ (j - 1)) (n - k + 1) / (A - k + 1).
```

`firstOrderTightListWeight n A k K τ μ M` sums these charges, assigning the order-one
charge to the highest `min(M, μ)` stages. The main theorem accepts any sufficient Taylor
exponent `τ`, so concrete applications can use the first-order exponent `2 K - 3`.

## Reading the main theorem

* `Q` is any nonzero differential equation in `X,Y₀,Y₁` with the two degree caps.
  `S` is a finite set of degree-`< k` solutions, each agreeing with `received` at at least
  `A` distinct centers supplied by `domain`.
* `K` is the Taylor cutoff. The hypotheses `1 < K`, `k ≤ K`, and `K ≤ n` discharge
  the Taylor and binomial-pivot conditions; `τ` must suffice for both active orders.
* The field may have characteristic zero. In positive characteristic, the sufficient
  condition is `max (K - 1) μ < ringChar F`: the Taylor pivots only use indices below
  `K`, while the separant recursion only uses jet degrees at most `μ`.

## Proof route and scope

The proof follows one singular separant recursion. At a regular stage it restricts the
equation to its highest active jet and invokes the field-independent Taylor count. A `Y₁`
separant decreases the first-jet cap, while a stage headed by `Y₀` has no active `Y₁`.
Total jet degree drops at every singular step. Monotonicity of the recursive charge covers
skipped degrees and an early drop in active order.

The older `firstOrderListWeight` estimate follows by comparing charges with `τ = 2 K`
and replacing `n - k + 1` by `n`. It is a corollary of this same recursion.
The theorem bounds a supplied finite set; finiteness of the complete close-polynomial set
and transfers to interleavings or polynomial curves are separate results.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.2, Lemma 6.2 (cap-sensitive first-order transfer).
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F]

/-- The cap-sensitive sum of regular-branch fiber degrees.  The `M` highest total-jet-degree
stages receive the order-one Taylor factor; the remaining stages receive factor one. -/
def firstOrderListWeight (K : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1) + firstOrderListWeight K μ 0
  | μ + 1, M + 1 =>
      (μ + 1) * (1 + 2 * K * μ) + firstOrderListWeight K μ M

/-- The dimension-sensitive first-order list charge. Order-zero stages contribute their degree
directly. Order-one stages use the exact Taylor exponent and the coefficient-space incidence
ratio `(n-k+1)/(A-k+1)`. -/
def firstOrderTightListWeight (n A k K τ : ℕ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1 : ℚ) + firstOrderTightListWeight n A k K τ μ 0
  | μ + 1, M + 1 =>
      (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1)) τ : ℚ) *
          ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) +
        firstOrderTightListWeight n A k K τ μ M

/-- The dimension-sensitive list charge is nonnegative. -/
theorem firstOrderTightListWeight_nonneg (n A k K τ μ M : ℕ) :
    0 ≤ firstOrderTightListWeight n A k K τ μ M := by
  induction μ generalizing M with
  | zero => simp [firstOrderTightListWeight]
  | succ μ ih =>
      cases M with
      | zero =>
          simp only [firstOrderTightListWeight]
          exact add_nonneg (by positivity) (ih 0)
      | succ M =>
          simp only [firstOrderTightListWeight]
          exact add_nonneg (by positivity) (ih M)

open Classical in
private theorem finite_regular_solutions_card_le_derivativeCapped_of_exponent
    (Q : DifferentialPolynomial F 1) (K k j r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ) (hK : 1 < K)
    (hkK : k ≤ K)
    (hj : 0 < j) (hr : 0 < r) (hrj : r ≤ j)
    (hjet : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 1 ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 1)) P ≠ 0)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := AlgebraicClosure F
  let f := algebraMap F E
  let QE := MvPolynomial.map f Q
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family_of_exponent
    f Q K k τ hτ hkK S domain received hdegree hsol hsep hbin hagree
  by_cases hJempty : J = ∅
  · have hScard : S.card = 0 := by simpa [hJempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjetmem⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    intro hz
    exact (hJ jet hjetmem).2.1 (by rw [hz, map_zero])
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
      center QE K k j r τ hτ hτpos hK hsepE hj hr hrj
      (by
        rw [totalJetDegree_map_eq]
        rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
        exact hjet)
      (by
        change jetDegree QE 1 ≤ r
        simpa only [QE, jetDegree_map_eq f f.injective Q 1] using hderiv)
      domainE (fun i ↦ f (received i)) hk hkA hAn J
      (fun jet hjetmem ↦ ⟨(hJ jet hjetmem).1, (hJ jet hjetmem).2.1,
        fun l ↦ (hJ jet hjetmem).2.2.1 l.val l.property⟩)
      (fun jet hjetmem ↦ (hJ jet hjetmem).2.2.2)
  rw [hcard] at hcount
  exact hcount

/-- A regular branch whose highest active jet is `Y₀` costs only its total jet degree. -/
private theorem regularSolutions_card_le_of_agreement_orderZero
    (current : DifferentialPolynomial F 1) (s : Fin 2) (hsval : s.val = 0)
    (hhighest : highestActiveJet current = some s)
    (K k ν : ℕ) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree current ≤ ν)
    (regular : Finset (BoundedSolution current (k - 1)))
    (haccepts : ∀ solution ∈ regular,
      IsAgreementSolution domain received k A solution.polynomial)
    (hseparant : ∀ solution ∈ regular,
      differentialSpecialization (separant current s) solution.polynomial ≠ 0) :
    (regular.card : ℚ) ≤ ν := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective (fun solution : BoundedSolution current (k - 1) ↦
      solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card :=
    Finset.card_image_of_injective regular hinjective
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding s Q', hQ']
    exact hdegree
  have hv : 0 < jetTotalDegree Q' := by
    have hactive : 0 < jetDegree current s :=
      (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
    have hactive' : 0 < jetDegree Q' (Fin.last s.val) := by
      unfold jetDegree
      rw [← MvPolynomial.degreeOf_rename_of_injective
        (jetPrefixEmbedding s).injective (some (Fin.last s.val)),
        jetPrefixEmbedding_top, hQ']
      exact hactive
    exact hactive'.trans_le (jetDegree_le_total Q' (Fin.last s.val))
  have hstage := finite_regular_solutions_card_le Q' K k (by omega) hkK
    (by rw [← jetTotalDegree_eq_weightedTotalDegree_elim]; exact hv)
    domain received hk hkA hAn polys
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      have heqsep :
          differentialSpecialization (separant current s) solution.polynomial =
            differentialSpecialization (separant Q' (Fin.last s.val)) solution.polynomial := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding s)
                (separant Q' (Fin.last s.val))) solution.polynomial := by
              rw [← separant_rename_jetPrefixEmbedding, hQ']
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hs (heqsep.trans hz))
    (fun i _hi _hiK ↦ by simp [hsval])
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).2)
  rw [hcard, ← jetTotalDegree_eq_weightedTotalDegree_elim] at hstage
  have hstage' : (regular.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) := by
    simpa [hsval] using hstage
  exact hstage'.trans (by exact_mod_cast hQ'Degree)

private theorem regularSolutions_card_le_of_agreement_derivativeCapped_of_exponent
    (current : DifferentialPolynomial F 1)
    (hhighest : highestActiveJet current = some (1 : Fin 2))
    (K k ν ρ τ : ℕ) (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree current ≤ ν) (hderiv : jetDegree current 1 ≤ ρ)
    (hρ : 0 < ρ) (hρν : ρ ≤ ν)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : F) ≠ 0)
    {D : ℕ}
    (regular : Finset (BoundedSolution current D))
    (haccepts : ∀ solution ∈ regular,
      IsAgreementSolution domain received k A solution.polynomial)
    (hseparant : ∀ solution ∈ regular,
      differentialSpecialization (separant current 1) solution.polynomial ≠ 0) :
    (regular.card : ℚ) ≤ firstOrderCurveFiberStageOne K ν ρ τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current (1 : Fin 2)
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective (fun solution : BoundedSolution current D ↦
      solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card :=
    Finset.card_image_of_injective regular hinjective
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding (1 : Fin 2) Q', hQ']
    exact hdegree
  have hQ'Deriv : jetDegree Q' 1 ≤ ρ := by
    have hlast : jetDegree Q' (Fin.last (1 : Fin 2).val) ≤ ρ := by
      unfold jetDegree at hderiv ⊢
      rw [← MvPolynomial.degreeOf_rename_of_injective
        (jetPrefixEmbedding (1 : Fin 2)).injective
          (some (Fin.last (1 : Fin 2).val)),
        jetPrefixEmbedding_top (1 : Fin 2), hQ']
      simpa using hderiv
    simpa using hlast
  have hstage := finite_regular_solutions_card_le_derivativeCapped_of_exponent
    Q' K k ν ρ τ hτ hτpos hK hkK (by omega) hρ hρν hQ'Degree hQ'Deriv
      domain received hk hkA hAn polys
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      have hsepPoly := separant_rename_jetPrefixEmbedding (1 : Fin 2) Q'
      rw [hQ'] at hsepPoly
      have heqsep :
          differentialSpecialization (separant current (1 : Fin 2)) solution.polynomial =
            differentialSpecialization (separant Q' (Fin.last (1 : Fin 2).val))
              solution.polynomial := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding (1 : Fin 2))
                (separant Q' (Fin.last (1 : Fin 2).val))) solution.polynomial := by
              rw [hsepPoly]
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hs (heqsep.trans hz))
    hbin
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).2)
  rwa [hcard] at hstage

/-- Dimension-sensitive first-order list counting.  The exact Taylor exponent is retained in
the order-one charge, while order-zero stages incur no agreement-ratio loss. -/
theorem finite_firstOrder_agreement_solutions_card_le_tight_of_exponent
    (Q : DifferentialPolynomial F 1) (K k μ M τ : ℕ)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ μ)
    (hfirst : jetDegree Q (1 : Fin 2) ≤ M)
    (hτ : ∀ r ≤ 1, TaylorExponentSufficient r K τ)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤ firstOrderTightListWeight n A k K τ μ M := by
  classical
  have hτpos : 0 < τ := by
    have ht := hτ 0 (by omega) (⟨1, hK⟩ : Fin K)
    norm_num [TaylorExponentSufficient] at ht
    omega
  let toRoot : {P // P ∈ S} → BoundedSolution Q (k - 1) := fun P ↦
    ⟨⟨P.1, by
      rw [Polynomial.mem_degreeLT]
      simpa [Nat.sub_add_cancel hk] using (haccept P.1 P.2).1⟩, hsol P.1 P.2⟩
  let roots : Finset (BoundedSolution Q (k - 1)) := S.attach.image toRoot
  have htoRoot : Function.Injective toRoot := by
    intro left right heq
    apply Subtype.ext
    exact congrArg BoundedSolution.polynomial heq
  have hcard : roots.card = S.card := by
    change (S.attach.image toRoot).card = S.card
    rw [Finset.card_image_of_injective _ htoRoot, Finset.card_attach]
  have hroots : ∀ solution ∈ roots,
      IsAgreementSolution domain received k A solution.polynomial := by
    intro solution hsolution
    change solution ∈ S.attach.image toRoot at hsolution
    rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, rfl⟩
    exact haccept source.1 source.2
  have recurse : ∀ (μ M : ℕ) (current : DifferentialPolynomial F 1), current ≠ 0 →
      jetTotalDegree current ≤ μ → jetDegree current (1 : Fin 2) ≤ M →
      (ringChar F = 0 ∨ max (K - 1) μ < ringChar F) →
      ∀ currentRoots : Finset (BoundedSolution current (k - 1)),
        (∀ solution ∈ currentRoots,
          IsAgreementSolution domain received k A solution.polynomial) →
        (currentRoots.card : ℚ) ≤ firstOrderTightListWeight n A k K τ μ M := by
    intro bound
    induction bound with
    | zero =>
        intro M current hcurrent hcurrentDegree _ _ currentRoots _
        have hterminal : highestActiveJet current = none := by
          apply (highestActiveJet_eq_none_iff current).mpr
          intro j hj
          have := hj.trans_le ((jetDegree_le_total current j).trans hcurrentDegree)
          omega
        let _ : IsEmpty (BoundedSolution current (k - 1)) :=
          isEmpty_boundedSolution_of_highestActiveJet_eq_none current hcurrent hterminal
        have hempty : currentRoots = ∅ := by
          ext solution
          exact isEmptyElim solution
        simp [hempty, firstOrderTightListWeight]
    | succ bound ih =>
        intro M current hcurrent hcurrentDegree hcurrentFirst hcurrentChar currentRoots
          hcurrentRoots
        cases hactive : highestActiveJet current with
        | none =>
            let _ : IsEmpty (BoundedSolution current (k - 1)) :=
              isEmpty_boundedSolution_of_highestActiveJet_eq_none current hcurrent hactive
            have hempty : currentRoots = ∅ := by
              ext solution
              exact isEmptyElim solution
            rw [hempty]
            simp only [Finset.card_empty, Nat.cast_zero]
            exact firstOrderTightListWeight_nonneg n A k K τ (bound + 1) M
        | some s =>
            let regularRoots := regularSolutions current s (k - 1) currentRoots
            let singularRoots := singularSolutions current s (k - 1) currentRoots
            let nextRoots := singularDescendants current s (k - 1) currentRoots
            have hactiveJet : DependsOnJet current s :=
              (isHighestActiveJet_of_highestActiveJet_eq_some hactive).1
            have hnextNe : separant current s ≠ 0 := by
              rcases hcurrentChar with hzero | hpos
              · let _ : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
                let _ : CharZero F := CharP.charP_to_charZero F
                exact separant_ne_zero_of_dependsOnJet_charZero current s hactiveJet
              · exact separant_ne_zero_of_dependsOnJet_of_lt_ringChar current s hactiveJet
                    ((jetDegree_le_total current s).trans hcurrentDegree |>.trans_lt
                    ((Nat.le_max_right (K - 1) (bound + 1)).trans_lt hpos))
            have hregularAccepts : ∀ solution ∈ regularRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              apply hcurrentRoots solution
              exact (Finset.mem_filter.mp (show
                solution ∈ currentRoots.filter fun candidate ↦
                  differentialSpecialization (separant current s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).1
            have hregularSep : ∀ solution ∈ regularRoots,
                differentialSpecialization (separant current s) solution.polynomial ≠ 0 := by
              intro solution hsolution
              exact (Finset.mem_filter.mp (show
                solution ∈ currentRoots.filter fun candidate ↦
                  differentialSpecialization (separant current s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).2
            have hnextAccepts : ∀ solution ∈ nextRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              change solution ∈ singularDescendants current s (k - 1) currentRoots at hsolution
              unfold singularDescendants at hsolution
              rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, heq⟩
              rw [← heq]
              apply hcurrentRoots source.1
              exact (Finset.mem_filter.mp source.2).1
            have hnextDegree : jetTotalDegree (separant current s) ≤ bound := by
              have hsep := separant_total_le current s
              omega
            have hnextChar : ringChar F = 0 ∨ max (K - 1) bound < ringChar F :=
              hcurrentChar.imp_right fun hpos ↦
                (max_le_max_left (K - 1) (Nat.le_succ bound)).trans_lt hpos
            cases M with
            | zero =>
                have hs : s = (0 : Fin 2) := by
                  fin_cases s
                  · rfl
                  · have := hactiveJet.trans_le hcurrentFirst
                    omega
                subst s
                have hnextFirst : jetDegree (separant current (0 : Fin 2)) (1 : Fin 2) ≤ 0 :=
                  (jetDegree_separant_le current (0 : Fin 2) (1 : Fin 2)).trans
                    hcurrentFirst
                have hnext := ih 0 (separant current (0 : Fin 2)) hnextNe hnextDegree
                  hnextFirst hnextChar nextRoots hnextAccepts
                have hregular := regularSolutions_card_le_of_agreement_orderZero
                  current (0 : Fin 2) rfl hactive K k (bound + 1) hkK domain received
                    hk hkA hAn hcurrentDegree regularRoots hregularAccepts hregularSep
                have hpartition : regularRoots.card + singularRoots.card = currentRoots.card :=
                  card_regular_add_card_singular current (0 : Fin 2) (k - 1) currentRoots
                have hsingular : (singularRoots.card : ℚ) ≤
                    firstOrderTightListWeight n A k K τ bound 0 := by
                  rw [← card_singularDescendants current (0 : Fin 2) (k - 1) currentRoots]
                  exact hnext
                calc
                  (currentRoots.card : ℚ) =
                      (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
                    exact_mod_cast hpartition.symm
                  _ ≤ _ := add_le_add hregular hsingular
                  _ = firstOrderTightListWeight n A k K τ (bound + 1) 0 := by
                    simp only [firstOrderTightListWeight]
                    push_cast
                    ring
            | succ cap =>
                have hnextFirst : jetDegree (separant current s) (1 : Fin 2) ≤ cap := by
                  fin_cases s
                  · have hzero : jetDegree current (1 : Fin 2) = 0 := by
                      apply Nat.eq_zero_of_not_pos
                      exact (isHighestActiveJet_of_highestActiveJet_eq_some hactive).2
                        (1 : Fin 2) (by decide)
                    exact (jetDegree_separant_le current (0 : Fin 2) (1 : Fin 2)).trans
                      (by omega)
                  · have hd := MvPolynomial.degreeOf_pderiv_le_sub_one
                        (some (1 : Fin 2)) current
                    change jetDegree (separant current (1 : Fin 2)) (1 : Fin 2) ≤
                      jetDegree current (1 : Fin 2) - 1 at hd
                    exact hd.trans (by omega)
                have hnext := ih cap (separant current s) hnextNe hnextDegree hnextFirst
                  hnextChar nextRoots hnextAccepts
                have hregular : (regularRoots.card : ℚ) ≤
                    (firstOrderCurveFiberStageOne K (bound + 1)
                      (min (cap + 1) (bound + 1)) τ : ℕ) *
                        ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
                  fin_cases s
                  · have hzero := regularSolutions_card_le_of_agreement_orderZero
                      current (0 : Fin 2) rfl hactive K k (bound + 1) hkK domain received
                        hk hkA hAn hcurrentDegree regularRoots hregularAccepts hregularSep
                    have hratio : (1 : ℚ) ≤
                        ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
                      rw [le_div_iff₀ (by exact_mod_cast (show 0 < A - k + 1 by omega))]
                      norm_cast
                      omega
                    have hhead : (bound + 1 : ℚ) ≤
                        (firstOrderCurveFiberStageOne K (bound + 1)
                          (min (cap + 1) (bound + 1)) τ : ℕ) := by
                      exact_mod_cast le_firstOrderCurveFiberStageOne (K := K)
                        (j := bound + 1) (r := min (cap + 1) (bound + 1))
                        (τ := τ) (by omega)
                    calc
                      (regularRoots.card : ℚ) ≤ bound + 1 := by
                        simpa only [Nat.cast_add, Nat.cast_one] using hzero
                      _ ≤ (firstOrderCurveFiberStageOne K (bound + 1)
                          (min (cap + 1) (bound + 1)) τ : ℕ) := hhead
                      _ ≤ (firstOrderCurveFiberStageOne K (bound + 1)
                            (min (cap + 1) (bound + 1)) τ : ℕ) *
                          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
                        simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (by positivity :
                          (0 : ℚ) ≤ firstOrderCurveFiberStageOne K (bound + 1)
                            (min (cap + 1) (bound + 1)) τ)
                      _ = _ := by ring
                  · have hcurrentDerivative : jetDegree current (1 : Fin 2) ≤
                        min (cap + 1) (bound + 1) := by
                      apply le_min hcurrentFirst
                      exact (jetDegree_le_total current 1).trans hcurrentDegree
                    have hactiveDerivative : 0 < jetDegree current (1 : Fin 2) :=
                      (isHighestActiveJet_of_highestActiveJet_eq_some hactive).1
                    simpa only [mul_div_assoc] using
                      regularSolutions_card_le_of_agreement_derivativeCapped_of_exponent
                      current hactive K k (bound + 1) (min (cap + 1) (bound + 1)) τ
                        (hτ 1 (by omega)) hτpos hK hkK domain received hk hkA hAn
                        hcurrentDegree hcurrentDerivative (by omega) (min_le_right _ _)
                        (fun i hri hiK ↦ binomial_pivots_of_characteristic
                          (hcurrentChar.imp_right fun hpos ↦ by
                            have hKm1 : K - 1 < ringChar F :=
                              (Nat.le_max_left (K - 1) (bound + 1)).trans_lt hpos
                            omega) 1 i hri hiK)
                        regularRoots hregularAccepts hregularSep
                have hpartition : regularRoots.card + singularRoots.card = currentRoots.card :=
                  card_regular_add_card_singular current s (k - 1) currentRoots
                have hsingular : (singularRoots.card : ℚ) ≤
                    firstOrderTightListWeight n A k K τ bound cap := by
                  rw [← card_singularDescendants current s (k - 1) currentRoots]
                  exact hnext
                calc
                  (currentRoots.card : ℚ) =
                      (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
                    exact_mod_cast hpartition.symm
                  _ ≤ _ := add_le_add hregular hsingular
                  _ = firstOrderTightListWeight n A k K τ (bound + 1) (cap + 1) := by
                    simp only [firstOrderTightListWeight]
  have hbound := recurse μ M Q hQ hdegree hfirst hchar roots hroots
  rwa [hcard] at hbound


/-- The exact dimension-sensitive charge is bounded by the earlier uniform cap-sensitive
expression. This comparison lets existing consumers keep `firstOrderListWeight` without a
second separant induction. -/
theorem firstOrderTightListWeight_two_mul_le (n A k K μ M : ℕ)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n) :
    firstOrderTightListWeight n A k K (2 * K) μ M ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hdenNat : 0 < A - k + 1 := by omega
  have hden : (0 : ℚ) < (A - k + 1 : ℕ) := by exact_mod_cast hdenNat
  have hone : (1 : ℚ) ≤ (n : ℚ) / (A - k + 1 : ℕ) := by
    rw [le_div_iff₀ hden]
    norm_cast
    omega
  have hratio : ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ) ≤
      (n : ℚ) / (A - k + 1 : ℕ) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (show n - k + 1 ≤ n by omega)
    · exact hden.le
  induction μ generalizing M with
  | zero => simp [firstOrderTightListWeight, firstOrderListWeight]
  | succ μ ih =>
      cases M with
      | zero =>
          simp only [firstOrderTightListWeight, firstOrderListWeight]
          have hhead : (μ : ℚ) + 1 ≤
              ((μ : ℚ) + 1) * ((n : ℚ) / (A - k + 1 : ℕ)) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℚ) ≤ μ + 1))
          calc
            (μ : ℚ) + 1 + firstOrderTightListWeight n A k K (2 * K) μ 0 ≤
                ((μ : ℚ) + 1) * ((n : ℚ) / (A - k + 1 : ℕ)) +
                  ((n * firstOrderListWeight K μ 0 : ℕ) : ℚ) /
                    ((A - k + 1 : ℕ) : ℚ) := add_le_add hhead (ih 0)
            _ = ((n * ((μ + 1) + firstOrderListWeight K μ 0) : ℕ) : ℚ) /
                  ((A - k + 1 : ℕ) : ℚ) := by
              push_cast
              field_simp
      | succ M =>
          simp only [firstOrderTightListWeight, firstOrderListWeight]
          have hstageNat := firstOrderCurveFiberStageOne_le_full
            (K := K) (j := μ + 1) (r := min (M + 1) (μ + 1)) (τ := 2 * K)
            (min_le_right _ _)
          have hstage :
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) ≤
                ((μ + 1) * (1 + 2 * K * μ) : ℕ) := by
            simpa [firstOrderTaylorTotalCap] using (show
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) ≤
                  ((μ + 1) * firstOrderTaylorTotalCap (μ + 1) (2 * K) : ℕ) by
                    exact_mod_cast hstageNat)
          push_cast at hstage
          have hhead :
              (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                (2 * K) : ℚ) *
                  ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ) ≤
                ((μ : ℚ) + 1) * (1 + 2 * (K : ℚ) * μ) *
                  (n : ℚ) / (A - k + 1 : ℕ) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul hstage (by exact_mod_cast (show n - k + 1 ≤ n by omega))
                (by positivity) (by positivity)
            · exact hden.le
          calc
            (firstOrderCurveFiberStageOne K (μ + 1) (min (M + 1) (μ + 1))
                  (2 * K) : ℚ) *
                  ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ) +
                firstOrderTightListWeight n A k K (2 * K) μ M ≤
              ((μ : ℚ) + 1) * (1 + 2 * (K : ℚ) * μ) *
                  (n : ℚ) / (A - k + 1 : ℕ) +
                ((n * firstOrderListWeight K μ M : ℕ) : ℚ) /
                  ((A - k + 1 : ℕ) : ℚ) := add_le_add hhead (ih M)
            _ = ((n * ((μ + 1) * (1 + 2 * K * μ) +
                  firstOrderListWeight K μ M) : ℕ) : ℚ) /
                    ((A - k + 1 : ℕ) : ℚ) := by
              push_cast
              field_simp

/-- Every finite family of accepted solutions of a first-order equation is bounded by the
cap-sensitive sum. `μ` bounds total jet degree and `M` bounds the degree in `Y₁`. -/
theorem finite_firstOrder_agreement_solutions_card_le_sharp
    (Q : DifferentialPolynomial F 1) (K k μ M : ℕ)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ μ)
    (hfirst : jetDegree Q (1 : Fin 2) ≤ M)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  exact (finite_firstOrder_agreement_solutions_card_le_tight_of_exponent
    Q K k μ M (2 * K) hQ hdegree hfirst
      (fun r _ ↦ taylorExponentSufficient_two_mul r K) domain received
      hK hkK hKn hk hkA hAn hchar S hsol haccept).trans
        (firstOrderTightListWeight_two_mul_le n A k K μ M hk hkA hAn)

end

end ReedSolomon.HiddenDerivative
