/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.CanonicalSound
/-!
# Duplicate-free canonical root selection

Per-center polynomial uniqueness is combined with the guard's unique center. Across stages,
the earlier accepted separant excludes the immediately next root equation and all later prefixes.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalRootSelection

open Polynomial CompPoly PolynomialDifferential
open StageRootsMachine (Record Stage Term Context)

variable {F : Type*} [Field F] [DecidableEq F]

/-- A duplicate-free alphabet yields duplicate-free center/polynomial pairs. -/
theorem center_pairs_nodup {r D : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (hn : alphabet.Nodup) :
    (alphabet.flatMap (CenterRootsMachine.centerSpec Q alphabet D)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _ha
    exact (JetRootsMachine.tuples_jetSolution_nodup Q a D alphabet hn).map
      (fun f g h ↦ (Prod.mk.inj h).2)
  · apply List.Pairwise.imp _ hn
    intro a b hab
    change List.Disjoint (CenterRootsMachine.centerSpec Q alphabet D a)
      (CenterRootsMachine.centerSpec Q alphabet D b)
    rw [List.disjoint_left]
    intro pair ha hb
    obtain ⟨f, _hf, he⟩ := List.mem_map.mp ha
    obtain ⟨g, _hg, he'⟩ := List.mem_map.mp hb
    exact hab ((congrArg Prod.fst he).trans (congrArg Prod.fst he').symm)

/-- Within one actual stage, the guard retains at most one center and one vector per polynomial. -/
theorem center_selection_nodup (d D : ℕ) (samples : List F) (context : Context F)
    (candidates : List (CenterRootsMachine.Record F))
    (hwidth : ∀ c ∈ candidates, c.2.length = D + 1)
    (hn : (candidates.map CenterRootsMachine.recordPolynomial).Nodup) :
    (polynomials d samples (candidates.map (StageRootsMachine.tagged context))).Nodup := by
  let kept := candidates.filter (fun c ↦ accepted d samples (StageRootsMachine.tagged context c))
  have hk : kept.Nodup := (hn.of_map _).filter _
  have hmap : (kept.map (fun c ↦ JetHornerMachine.coefficientPolynomial c.2)).Nodup := by
    apply hk.map_on
    intro x hx y hy hp
    obtain ⟨hx, ha⟩ := List.mem_filter.mp hx
    obtain ⟨hy, hb⟩ := List.mem_filter.mp hy
    have hcs := coefficients_unique x.2 y.2 ((hwidth x hx).trans (hwidth y hy).symm) hp
    have hcenter : x.1 = y.1 := by
      change CanonicalGuardMachine.result ⟨x.2, samples, d, x.1, context.separant⟩
        context.previous = true at ha
      change CanonicalGuardMachine.result ⟨y.2, samples, d, y.1, context.separant⟩
        context.previous = true at hb
      rw [← hcs] at hb
      exact CanonicalGuardMachine.accepted_center_unique x.2 samples d context.separant
        context.previous context.previous x.1 y.1 ha hb
    exact Prod.ext hcenter hcs
  simpa only [polynomials, selected, List.filter_map, List.map_map, Function.comp_def,
    StageRootsMachine.tagged, kept] using hmap

/-- Guard-selected polynomials from the actual ordered stage specification contain no duplicates. -/
theorem polynomials_nodup {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hn : input.alphabet.Nodup) (hdepth : d ≤ D)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} {pre : List (List (Term F))}
    (hspec : StageRootsMachine.Specification input D L samples stages pre out) :
    (polynomials d samples out).Nodup := by
  induction hspec generalizing ts Q with
  | terminal ts pre => simp [polynomials, selected]
  | @active stage next stages pre r e candidates out c selected run tail ih =>
      cases hchain with
      | @active Q ts tailStages j layout rep nonzero highest nextChain =>
          have hs := Option.some.inj selected
          have hr : r = j.val := by have hi := (Prod.mk.inj hs).1; omega
          subst r
          obtain ⟨A⟩ := ActiveOrderAdapter.exists_presentation ts Q j rep highest
          have hw : differentialWeightedDegree D (semanticEquation A.polynomial) < L := by
            rwa [A.weightedDegree]
          have hl := ActiveOrderAdapter.lookup_of_highest Q j highest D L hweight
          obtain ⟨actual, ca, hactual, hpoly, hwidth, _hcount, _hcost⟩ :=
            CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet ts
              points samples hsamples hq A.sparse_eq
              ((Nat.le_of_lt_succ j.isLt).trans hdepth) hl hw
          change CenterRootsMachine.runFuel
            (StageRootsMachine.centerInput input ⟨ts, some (j.val + 1, jetDegree Q j)⟩ j.val) D L
            (CenterRootsMachine.fuel
              (StageRootsMachine.centerInput input ⟨ts, some (j.val + 1, jetDegree Q j)⟩ j.val)
              D L samples.length) (.start samples) = (.done (some actual), ca) at hactual
          have heq := run.symm.trans hactual
          cases heq
          have hpairs : (candidates.map CenterRootsMachine.recordPolynomial).Nodup := by
            rw [hpoly]
            exact center_pairs_nodup A.polynomial input.alphabet hn
          have hctail : ∀ k, jetDegree (separant Q j) k < ringChar F := fun k ↦
            (jetDegree_separant_le Q j k).trans_lt (hchar k)
          have hwtail : differentialWeightedDegree D (separant Q j) < L :=
            (weightedTotalDegree_pderiv_le (differentialWeight D) (some j) Q).trans_lt hweight
          have hntail := ih nextChain hctail hwtail
          let context : Context F :=
            ⟨⟨ts, some (j.val + 1, jetDegree Q j)⟩, pre, next.equation⟩
          have hnhead := center_selection_nodup d D samples context candidates hwidth hpairs
          change List.Nodup
            (polynomials d samples (candidates.map (StageRootsMachine.tagged context) ++ out))
          simp only [polynomials, CanonicalRootSelection.selected, List.filter_append,
            List.map_append, List.nodup_append]
          refine ⟨hnhead, hntail, ?_⟩
          intro f hf g hg hefg
          obtain ⟨earlier, hearlier, hef⟩ := List.mem_map.mp hf
          obtain ⟨hearlier, ha⟩ := List.mem_filter.mp hearlier
          obtain ⟨candidate, hcand, rfl⟩ := List.mem_map.mp hearlier
          obtain ⟨later, hlater, hlg⟩ := List.mem_map.mp hg
          obtain ⟨hlater, hb⟩ := List.mem_filter.mp hlater
          obtain ⟨hlwidth, hlzero⟩ := current_zero input points samples hsamples hq hdepth
            nextChain hctail hwtail tail later hlater
          have hepoly : JetHornerMachine.coefficientPolynomial candidate.2 =
              JetHornerMachine.coefficientPolynomial later.coefficients :=
            hef.trans (hefg.trans hlg.symm)
          have hcoeff := coefficients_unique candidate.2 later.coefficients
            ((hwidth candidate hcand).trans hlwidth.symm) hepoly
          exact excludes_later tail (StageRootsMachine.tagged context candidate) later hlater
            rfl hcoeff ha hb hlzero

/-- Canonical acceptance gives a unique full stage/context/center/vector record for each root. -/
theorem accepted_record_unique {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hn : input.alphabet.Nodup) (hdepth : d ≤ D)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)}
    (hspec : StageRootsMachine.Specification input D L samples stages [] out)
    (x y : Record F) (hx : x ∈ selected d samples out) (hy : y ∈ selected d samples out)
    (hpoly : JetHornerMachine.coefficientPolynomial x.coefficients =
      JetHornerMachine.coefficientPolynomial y.coefficients) : x = y := by
  have hp := polynomials_nodup input points samples hsamples hq hn hdepth hchain hchar hweight hspec
  have hs : (selected d samples out).Nodup := hp.of_map _
  exact ((List.nodup_map_iff_inj_on hs).mp hp) x hx y hy hpoly

/-- The guard-selected polynomial list enumerates each bounded initial root exactly once. -/
theorem selection_correct {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ x : F, x ∈ input.alphabet)
    (hn : input.alphabet.Nodup) (hdepth : d ≤ D)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q)
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hne : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)}
    (hspec : StageRootsMachine.Specification input D L samples stages [] out) :
    (polynomials d samples out).Nodup ∧ ∀ f : F[X],
      f ∈ polynomials d samples out ↔ f.natDegree ≤ D ∧ differentialSpecialization Q f = 0 := by
  have hq : 0 < input.alphabet.length := List.length_pos_of_mem (hall 0)
  refine ⟨polynomials_nodup input points samples hsamples hq hn hdepth hchain hchar.2 hweight hspec,
    ?_⟩
  intro f
  constructor
  · intro hm
    obtain ⟨record, hr, hpoly⟩ := List.mem_map.mp hm
    have hs := selected_sound input points samples hsamples hq hdepth hQ hchain hchar.2
      hweight hspec record hr
    simpa only [hpoly] using hs
  · rintro ⟨hd, hroot⟩
    have hmem : f ∈ Polynomial.degreeLT F (D + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hd)
    let P : BoundedSolution Q D := ⟨⟨f, hmem⟩, hroot⟩
    obtain ⟨record, hr, hp⟩ := selected_complete input points samples hsamples hall hdepth
      hchain hne hchar hweight hspec P
    exact List.mem_map.mpr ⟨record, hr, hp⟩

end ReedSolomon.HiddenDerivative.CanonicalRootSelection
