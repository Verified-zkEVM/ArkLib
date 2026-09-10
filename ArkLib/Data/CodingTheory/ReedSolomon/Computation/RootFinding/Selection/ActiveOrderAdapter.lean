/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.SeparantChainRefinement
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Step
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.JetPrefix
/-!
# Proof-only active-order presentations of unchanged sparse equations

The root machines consume materialized natural-index sparse terms. Their concrete-polynomial
representation contract concerns the represented polynomial, so cancelled terms and higher
zero-exponent factors need no runtime trimming. This adapter restricts the semantic equation to
its active prefix and supplies a concrete presentation at that order without executing a conversion.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ActiveOrderAdapter

open PolynomialDifferential
open MvPolynomial CompPoly Polynomial
open MvPolynomial.EvaluationMachine (Term sparsePolynomial)
open HighestJetTransport (encodeJet)

variable {F : Type*} [Field F] {d r : ℕ}

/-- Finite indices corresponding to `X, Y₀, ..., Y_r`. -/
def jetIndex : JetVariable r → Fin (r + 2)
  | none => 0
  | some j => j.succ

private theorem finToJet_jetIndex (v : JetVariable r) :
    finToJetVariable r (jetIndex v) = v := by
  cases v <;> rfl

/-- Concrete finite-variable presentation, used only by semantic proofs. -/
noncomputable def concrete (Q : DifferentialPolynomial F r) : CPoly.CMvPolynomial (r + 2) F :=
  CPoly.toCMvPolynomial (rename jetIndex Q)

/-- Interpreting the proof-only concrete presentation recovers the exact equation. -/
theorem semantic_concrete (Q : DifferentialPolynomial F r) : semanticEquation (concrete Q) = Q := by
  classical
  unfold semanticEquation concrete
  rw [CPoly.fromCMvPolynomial_toCMvPolynomial, rename_rename]
  have he : finToJetVariable r ∘ jetIndex = id := by funext v; exact finToJet_jetIndex v
  rw [he, rename_id]
  rfl

/-- The concrete presentation uses the same natural-variable polynomial encoding. -/
theorem natural_concrete (Q : DifferentialPolynomial F r) :
    rename Fin.val (CPoly.fromCMvPolynomial (concrete Q)) = rename encodeJet Q := by
  unfold concrete
  rw [CPoly.fromCMvPolynomial_toCMvPolynomial, rename_rename]
  congr 2
  funext v
  cases v <;> rfl

/-- Every concrete equation has the same natural encoding as its differential interpretation. -/
theorem natural_semantic (Q : CPoly.CMvPolynomial (r + 2) F) :
    rename encodeJet (semanticEquation Q) = rename Fin.val (CPoly.fromCMvPolynomial Q) := by
  unfold semanticEquation
  rw [rename_rename]
  congr 2
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- Prefix inclusion does not change the natural index of any retained variable. -/
theorem natural_prefix (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) :
    rename encodeJet (rename (jetPrefixEmbedding s) Q) = rename encodeJet Q := by
  rw [rename_rename]
  congr 2
  funext v
  cases v <;> rfl

/-- The exact concrete representation seam consumed by the current-order root machines. -/
structure Presentation (ts : List (Term F)) (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) where
  polynomial : CPoly.CMvPolynomial (s.val + 2) F
  sparse_eq : sparsePolynomial ts = rename Fin.val (CPoly.fromCMvPolynomial polynomial)
  ambient_eq : rename (jetPrefixEmbedding s) (semanticEquation polynomial) = Q

/-- Restrict to the selected highest jet without changing any materialized sparse term. -/
theorem exists_presentation (ts : List (Term F)) (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hrep : sparsePolynomial ts = rename encodeJet Q)
    (hs : highestActiveJet Q = some s) : Nonempty (Presentation ts Q s) := by
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial Q s
    (isHighestActiveJet_of_highestActiveJet_eq_some hs)
  refine ⟨⟨concrete Q', ?_, ?_⟩⟩
  · rw [natural_concrete, hrep, ← hQ', natural_prefix]
  · rw [semantic_concrete]
    exact hQ'

/-- A presentation also recovers the original ambient natural-polynomial representation. -/
theorem Presentation.natural_eq {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) : sparsePolynomial ts = rename encodeJet Q := by
  calc
    sparsePolynomial ts = rename Fin.val (CPoly.fromCMvPolynomial A.polynomial) := A.sparse_eq
    _ = rename encodeJet (semanticEquation A.polynomial) := (natural_semantic A.polynomial).symm
    _ = rename encodeJet (rename (jetPrefixEmbedding s) (semanticEquation A.polynomial)) :=
      (natural_prefix s _).symm
    _ = rename encodeJet Q := congrArg (rename encodeJet) A.ambient_eq

/-- All differential specializations agree on every polynomial candidate. -/
theorem Presentation.specialization {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (P : F[X]) :
    differentialSpecialization (semanticEquation A.polynomial) P =
      differentialSpecialization Q P := by
  rcases A with ⟨poly, _, he⟩
  dsimp only
  rw [← he, differentialSpecialization_rename_jetPrefixEmbedding]

/-- The current-order top separant is exactly the ambient highest-jet separant. -/
theorem Presentation.separant {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) :
    rename (jetPrefixEmbedding s) (PolynomialDifferential.separant (semanticEquation A.polynomial)
      (Fin.last s.val)) = PolynomialDifferential.separant Q s := by
  rcases A with ⟨poly, _, he⟩
  dsimp only
  rw [← he, separant_rename_jetPrefixEmbedding]

/-- Regular jets of polynomial candidates are equivalent at ambient and current order. -/
theorem Presentation.regular_iff {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (a : F) (P : F[X]) :
    IsRegularJet (semanticEquation A.polynomial) (Fin.last s.val) a (polynomialJet a P) ↔
      IsRegularJet Q s a (polynomialJet a P) := by
  rcases A with ⟨poly, _, he⟩
  dsimp only
  rw [← he, isRegularJet_rename_jetPrefixEmbedding_iff]

/-- Restriction preserves nonzeroness. -/
theorem Presentation.nonzero {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (hQ : Q ≠ 0) :
    semanticEquation A.polynomial ≠ 0 := by
  intro h
  apply hQ
  rw [← A.ambient_eq, h, map_zero]

/-- Individual degrees of every retained jet agree exactly. -/
theorem Presentation.jetDegree {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (j : Fin (s.val + 1)) :
    PolynomialDifferential.jetDegree (semanticEquation A.polynomial) j =
      PolynomialDifferential.jetDegree Q
        ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) s.isLt⟩ := by
  rcases A with ⟨poly, _, he⟩
  dsimp only
  rw [← he]
  exact (degreeOf_rename_of_injective (jetPrefixEmbedding s).injective (some j)).symm

/-- Prefix restriction requires no stronger characteristic bound on the equation. -/
theorem Presentation.characteristic {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s)
    (hchar : ∀ j, PolynomialDifferential.jetDegree Q j < ringChar F) :
    ∀ j, PolynomialDifferential.jetDegree (semanticEquation A.polynomial) j < ringChar F := by
  intro j
  rw [A.jetDegree]
  exact hchar _

/-- Differential weights agree exactly on a retained prefix, so its weighted degree is unchanged. -/
theorem weightedDegree_prefix (D : ℕ) (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) :
    differentialWeightedDegree D (rename (jetPrefixEmbedding s) Q) =
      differentialWeightedDegree D Q := by
  classical
  unfold differentialWeightedDegree weightedTotalDegree
  rw [support_rename_of_injective (jetPrefixEmbedding s).injective, Finset.sup_image]
  congr 1
  funext u
  simp only [Function.comp_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (by intro v; simp) (by intro v a b; simp [add_mul])]
  congr 1
  funext v n
  cases v <;> rfl

/-- The current-order root theorem can reuse the exact original weighted-degree budget. -/
theorem Presentation.weightedDegree {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (D : ℕ) :
    differentialWeightedDegree D (semanticEquation A.polynomial) =
      differentialWeightedDegree D Q := by
  rcases A with ⟨poly, _, he⟩
  dsimp only
  rw [← he, weightedDegree_prefix]

/-- The selected exponent is the literal top-coordinate degree in the current-order presentation. -/
theorem Presentation.top_degree {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) :
    PolynomialDifferential.jetDegree (semanticEquation A.polynomial) (Fin.last s.val) =
      PolynomialDifferential.jetDegree Q s := A.jetDegree (Fin.last s.val)

/-- The current-order highest jet is its literal top coordinate. -/
theorem Presentation.highest {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (A : Presentation ts Q s) (hs : highestActiveJet Q = some s) :
    highestActiveJet (semanticEquation A.polynomial) = some (Fin.last s.val) := by
  have hp : DependsOnJet (semanticEquation A.polynomial) (Fin.last s.val) := by
    rw [DependsOnJet, A.top_degree]
    exact (isHighestActiveJet_of_highestActiveJet_eq_some hs).1
  have hn : (activeJets (semanticEquation A.polynomial)).Nonempty :=
    ⟨Fin.last s.val, mem_activeJets.mpr hp⟩
  rw [highestActiveJet_eq_some_max _ hn]
  congr 1
  exact le_antisymm (Fin.le_last _) (Finset.le_max' _ _ (mem_activeJets.mpr hp))

/-- An active jet forces its specialization weight into the polynomial's weighted-degree budget. -/
theorem active_weight_le (D : ℕ) (Q : DifferentialPolynomial F r) (j : Fin (r + 1))
    (hj : DependsOnJet Q j) : D - j.val ≤ differentialWeightedDegree D Q := by
  classical
  have hex : ∃ u ∈ Q.support, 0 < u (some j) := by
    by_contra! hn
    have hz : PolynomialDifferential.jetDegree Q j ≤ 0 := degreeOf_le_iff.mpr hn
    exact (Nat.not_le_of_gt hj) hz
  obtain ⟨u, hu, hp⟩ := hex
  apply le_trans _ (MvPolynomial.le_weightedTotalDegree (differentialWeight D) hu)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · have hb := Finset.single_le_sum
      (fun v _ => Nat.zero_le (u v • differentialWeight D v)) (Finset.mem_univ (some j))
    have hm := Nat.mul_le_mul_right (D - j.val) (show 1 ≤ u (some j) by omega)
    simpa only [one_mul, nsmul_eq_mul, differentialWeight_some] using hm.trans hb
  · intro v
    simp

/-- The root solver's lookup bound follows from the same weighted-degree budget at active order. -/
theorem lookup_of_highest (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hs : highestActiveJet Q = some s)
    (D L : ℕ) (hweight : differentialWeightedDegree D Q < L) : D - s.val < L :=
  (active_weight_le D Q s (isHighestActiveJet_of_highestActiveJet_eq_some hs).1).trans_lt hweight

variable [DecidableEq F]

/-- A represented chain-stage equation never exceeds the original differential weighted degree. -/
theorem record_weight {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (MvPolynomial.SeparantChainMachine.Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q out) (D : ℕ)
    (record : MvPolynomial.SeparantChainMachine.Stage F) (hmem : record ∈ out)
    (R : DifferentialPolynomial F d)
    (hrep : sparsePolynomial record.equation = rename encodeJet R) :
    differentialWeightedDegree D R ≤ differentialWeightedDegree D Q := by
  induction hchain with
  | @terminal Q ts layout rep nonzero last =>
      have he : record = _ := List.mem_singleton.mp hmem
      subst record
      have heq : R = Q := rename_injective encodeJet HighestJetTransport.encodeJet_injective
        (hrep.symm.trans rep)
      subst R
      exact le_rfl
  | @active Q ts tail j layout rep nonzero highest next ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have heq : R = Q := rename_injective encodeJet HighestJetTransport.encodeJet_injective
          (hrep.symm.trans rep)
        subst R
        exact le_rfl
      · exact (ih hmem).trans (weightedTotalDegree_pderiv_le (differentialWeight D) (some j) Q)

/-- The current-order root solver reuses the original depth, lookup, weight and characteristic
bounds. Only its sparse-polynomial representation changes, through the proof-only presentation. -/
theorem root_bounds {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (MvPolynomial.SeparantChainMachine.Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q out) (D L : ℕ) (hdepth : d ≤ D)
    (hchar : IsBelowCharacteristic D Q) (hweight : differentialWeightedDegree D Q < L)
    (record : MvPolynomial.SeparantChainMachine.Stage F) (hmem : record ∈ out)
    (R : DifferentialPolynomial F d) (s : Fin (d + 1))
    (A : Presentation record.equation R s) (hs : highestActiveJet R = some s) :
    s.val ≤ D ∧ D - s.val < L ∧ differentialWeightedDegree D (semanticEquation A.polynomial) < L ∧
      IsBelowCharacteristic D (semanticEquation A.polynomial) := by
  have hw := (record_weight hchain D record hmem R A.natural_eq).trans_lt hweight
  obtain ⟨R', hrep, hne, hselected, hc⟩ := hchain.record_contract hchar.2 record hmem
  have he : R' = R := rename_injective encodeJet HighestJetTransport.encodeJet_injective
    (hrep.symm.trans A.natural_eq)
  subst R'
  refine ⟨(Nat.le_of_lt_succ s.isLt).trans hdepth, lookup_of_highest R s hs D L hw, ?_,
    hchar.1, A.characteristic hc⟩
  rw [A.weightedDegree]
  exact hw

/-- Each active actual chain record supplies the unchanged-term concrete root representation,
with the exact selected order and the inherited equation contract. -/
theorem of_chain_record {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (MvPolynomial.SeparantChainMachine.Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q out)
    (hchar : ∀ j, PolynomialDifferential.jetDegree Q j < ringChar F)
    (record : MvPolynomial.SeparantChainMachine.Stage F) (hmem : record ∈ out)
    (i e : ℕ) (hselected : record.selected = some (i, e)) :
    ∃ R : DifferentialPolynomial F d, ∃ s : Fin (d + 1), ∃ A : Presentation record.equation R s,
      i = s.val + 1 ∧
      e = PolynomialDifferential.jetDegree (semanticEquation A.polynomial) (Fin.last s.val) ∧
      s.val ≤ d ∧ semanticEquation A.polynomial ≠ 0 ∧
      highestActiveJet (semanticEquation A.polynomial) = some (Fin.last s.val) ∧
      (∀ D, differentialWeightedDegree D (semanticEquation A.polynomial) ≤
        differentialWeightedDegree D Q) ∧
      ∀ j, PolynomialDifferential.jetDegree (semanticEquation A.polynomial) j < ringChar F := by
  obtain ⟨R, hrep, hne, hs, hc⟩ := hchain.record_contract hchar record hmem
  rw [hselected] at hs
  cases hr : highestActiveJet R with
  | none => simp [hr] at hs
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨A⟩ := exists_presentation record.equation R s hrep hr
      refine ⟨R, s, A, hs.1, hs.2.trans A.top_degree.symm, Nat.le_of_lt_succ s.isLt,
        A.nonzero hne, A.highest hr, ?_, A.characteristic hc⟩
      intro D
      rw [A.weightedDegree]
      exact record_weight hchain D record hmem R hrep

end ReedSolomon.HiddenDerivative.ActiveOrderAdapter
