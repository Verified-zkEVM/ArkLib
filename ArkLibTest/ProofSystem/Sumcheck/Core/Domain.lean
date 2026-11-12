/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.DomainEquivalence
public import ArkLib.ProofSystem.Sumcheck.Core.Indexed

/-! # Multiplicity of indexed Sumcheck domains -/

@[expose] public section

namespace Sumcheck.Core.DomainTest
open Polynomial Finset

/-- The constant polynomial one has indexed sum two over the list of two zeroes. -/
example : roundSum ([0, 0] : List ℕ).get (0 : Fin 2) Fin.elim0
    (1 : MvPolynomial (Fin 1) ℕ) = 2 := by
  simp [roundSum]

/-- The list specialization counts both occurrences of the same evaluation point. -/
example : (∑ i : Fin ([0, 0] : List ℕ).length, (1 : ℕ[X]).eval
    (([0, 0] : List ℕ).get i)) = 2 := by
  rw [sum_domain_list ([0, 0] : List ℕ) (fun x => (1 : ℕ[X]).eval x)]
  simp

/-- The singleton embedding enumerates the deduplicated domain containing zero. -/
def zeroDomain : Fin 1 ↪ ℕ :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Deduplicating the two zeroes changes the constant polynomial's sum to one. -/
example : (∑ x ∈ univ.map zeroDomain, (1 : ℕ[X]).eval x) = 1 := by
  simp

run_cmd
  for decl in [``Sumcheck.Core.sum_domain_embedding, ``Sumcheck.Core.sum_domain_list,
      ``Sumcheck.Core.roundSum, ``Sumcheck.Core.projectedRoundPolynomial,
      ``Sumcheck.Core.projectedRoundPolynomial_embedding, ``Sumcheck.Core.sum_evalExcept_indices,
      ``Sumcheck.Core.sum_projectedRoundPolynomial, ``Sumcheck.Core.roundSum_succ] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.DomainTest

namespace Sumcheck.Core.DomainTest
open Polynomial MvPolynomial

/-- Repeating zero twice makes the initial sum of the constant-one input equal to two. -/
example : indexedRelation ([0, 0] : List ℕ).get (0 : Fin 2) ⟨2, Fin.elim0⟩
    (⟨1, by rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]; intro i; simp⟩ :
      ℕ⦃≤ 0⦄[X Fin 1]) := by
  simp [indexedRelation, roundSum]

/-- Replacing the repeated domain by a singleton changes the truth of the claim. -/
example : ¬ indexedRelation ([0] : List ℕ).get (0 : Fin 2) ⟨2, Fin.elim0⟩
    (⟨1, by rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]; intro i; simp⟩ :
      ℕ⦃≤ 0⦄[X Fin 1]) := by
  simp [indexedRelation, roundSum]

/-- Multiplicities are counted independently in every variable of the remaining sum. -/
example : roundSum ([0, 0] : List ℕ).get (0 : Fin 3) Fin.elim0
    (1 : MvPolynomial (Fin 2) ℕ) = 4 := by
  simp [roundSum]

run_cmd
  for decl in [``Sumcheck.Core.indexedRelation, ``Sumcheck.Core.indexedRelation_last] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.DomainTest

namespace Sumcheck.Core.DomainExecutionTest
open Polynomial PFunctor FreeM Interaction.Core Interaction.Oracle OracleComp

/-- The general deterministic list equation needs no sampling, finiteness or distinctness. -/
example {R : Type} [CommSemiring R] [DecidableEq R] {deg : ℕ} {ι : Type}
    (ambient : OracleSpec ι) (domain : List R)
    (data : ∀ i, PolynomialData R 1 deg i) (q : R⦃≤ deg⦄[X]) (target r : R) :
    indexedExecute domain.get ambient (QueryImpl.id' ambient) (pure r) data q target =
      pure ⟨roundTranscript q r, (q.val.eval r, r),
        if (domain.map (fun x => q.val.eval x)).sum = target then
          some (⟨q.val.eval r, Fin.snoc Fin.elim0 r⟩, data) else none⟩ :=
  indexedExecuteAt_list_eq ambient domain data q target r

/-- The general honest list equation keeps the legacy univariate input and message parameters. -/
example {R : Type} [CommSemiring R] [DecidableEq R] {deg : ℕ} {ι : Type}
    (ambient : OracleSpec ι) (domain : List R) (p : R⦃≤ deg⦄[X]) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    indexedExecute domain.get ambient (QueryImpl.id' ambient) (pure r)
      (fun _ => univariateData p) p target =
      pure ⟨roundTranscript p r, (p.val.eval r, r),
        some (⟨p.val.eval r, Fin.snoc Fin.elim0 r⟩, fun _ => univariateData p)⟩ :=
  indexedExecuteAt_univariate_honest ambient domain p target r h

/-- A degree-zero natural-number message, where there is no finite uniform sampler. -/
noncomputable def natOne : ℕ⦃≤ 0⦄[X] := ⟨1, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- The actual deterministic run in the interaction layer over two zeroes accepts target two at
every challenge. -/
example {ι : Type} (ambient : OracleSpec ι) (r : ℕ) :
    indexedExecute ([0, 0] : List ℕ).get ambient (QueryImpl.id' ambient) (pure r)
      (fun _ => univariateData natOne) natOne 2 =
      pure ⟨roundTranscript natOne r, (1, r),
        some (⟨1, Fin.snoc Fin.elim0 r⟩, fun _ => univariateData natOne)⟩ := by
  simpa [natOne] using
    indexedExecuteAt_univariate_honest ambient [0, 0] natOne 2 r (by simp [natOne])

/-- A target obtained by deduplicating the list explicitly rejects, for every challenge. -/
example {ι : Type} (ambient : OracleSpec ι) (r : ℕ) :
    indexedExecute ([0, 0] : List ℕ).get ambient (QueryImpl.id' ambient) (pure r)
      (fun _ => univariateData natOne) natOne 1 =
      pure ⟨roundTranscript natOne r, (1, r), none⟩ := by
  rw [indexedExecuteAt_list_eq]
  simp [natOne]

/-- Honest closing observes the retained input polynomial in an actual deterministic run. -/
example {ι : Type} (ambient : OracleSpec ι) (r : ℕ) :
    (fun obs => obs.2.2.map
      (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target)) <$>
      indexedExecute ([0, 0] : List ℕ).get ambient (QueryImpl.id' ambient) (pure r)
        (fun _ => univariateData natOne) natOne 2 = pure (some True) := by
  simpa only [LawfulApplicative.map_pure] using
    indexedExecute_univariate_complete ambient (QueryImpl.id' ambient) (pure r)
      [0, 0] natOne 2 (by simp [natOne])

/-- The degree bound of a message follows from its carrier. -/
example : natOne.val.degree ≤ (0 : ℕ) := message_degree natOne

/-- The degree bound and honest closing hold together in an actual deterministic run. -/
example {ι : Type} (ambient : OracleSpec ι) (r : ℕ) :
    natOne.val.degree ≤ (0 : ℕ) ∧
      (fun obs => obs.2.2.map
        (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target)) <$>
        indexedExecute ([0, 0] : List ℕ).get ambient (QueryImpl.id' ambient) (pure r)
          (fun _ => univariateData natOne) natOne 2 = pure (some True) := by
  have h := indexedExecute_univariate_degree_complete ambient (QueryImpl.id' ambient) (pure r)
    [0, 0] natOne 2 (by simp [natOne])
  exact ⟨h.1, by simpa only [LawfulApplicative.map_pure] using h.2⟩

/-- Rejection preserves challenge mass as a separate property of the actual run. -/
example {ι : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient ProbComp)
    (challenge : ProbComp ℕ) :
    Pr{let _ ← (indexedExecute ([0, 0] : List ℕ).get ambient impl challenge
      (fun _ => univariateData natOne) natOne 1)}[True] = Pr{let _ ← challenge}[True] :=
  indexedExecute_failure _ ambient impl challenge (fun _ => univariateData natOne) natOne 1

/-- Every supported honest arbitrary challenge program produces a valid accepted claim. -/
example {ι : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient ProbComp)
    (challenge : ProbComp ℕ) :
    Pr{let obs ← (indexedExecute ([0, 0] : List ℕ).get ambient impl challenge
      (fun _ => univariateData natOne) natOne 2)}[
        obs.2.2.map (fun out => (out.2 ()).val.eval out.1.challenges = out.1.target) =
          some True] = 1 :=
  indexedExecute_univariate_perfectCompleteness ambient impl challenge [0, 0] natOne 2
    (by simp [natOne])

run_cmd
  for decl in [``Sumcheck.Core.indexedVerifier_run_one, ``Sumcheck.Core.indexedExecute_eq,
      ``Sumcheck.Core.indexedExecuteAt_eq, ``Sumcheck.Core.indexedExecuteAt_list_eq,
      ``Sumcheck.Core.indexedExecuteAt_univariate_honest,
      ``Sumcheck.Core.indexedRoundResult_rejects, ``Sumcheck.Core.indexedExecute_failure,
      ``Sumcheck.Core.indexedRoundResult_true_iff, ``Sumcheck.Core.univariateData_eval,
      ``Sumcheck.Core.indexedExecute_univariate_honest_eq,
      ``Sumcheck.Core.indexedExecute_univariate_complete,
      ``Sumcheck.Core.message_degree,
      ``Sumcheck.Core.indexedExecute_univariate_degree_complete,
      ``Sumcheck.Core.indexedExecute_univariate_support,
      ``Sumcheck.Core.indexedExecute_univariate_perfectCompleteness,
      ``Sumcheck.Core.indexedExecute_univariate_measureCompleteness,
      ``Sumcheck.Core.simulateQ_indexedSumQueries_monad] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.DomainExecutionTest
