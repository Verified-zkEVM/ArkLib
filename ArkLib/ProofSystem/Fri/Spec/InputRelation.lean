/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Spec.General
public import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# The FRI input relation and Reed–Solomon proximity

The input word and strict Reed–Solomon proximity language are defined here, independently
of the probabilistic soundness argument. A word in that language supplies a computational
polynomial witness for the specification's closed-ball input relation.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- The input word, extracted from the initial singleton oracle history. -/
def initialOracle
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j) :
    (ω.subdomain 0).toFinset → F :=
  cast (by
    simp only [OracleStatement, finRangeTo, Fin.val_zero, List.take_zero,
      List.toFinset_nil, Finset.sum_empty]
    rfl) (stmt.2 0)

/-- Words at relative distance strictly less than `δ` from the initial Reed–Solomon code. -/
def proximityLanguage (δ : ℝ) : Set ((ω.subdomain 0).toFinset → F) :=
  {f | ∃ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
    (Code.relHammingDist (fun z ↦ f (initialQuery z)) u : ℝ) < δ}

/-- A witness close to the indexed initial word satisfies the input relation. -/
theorem mem_inputRelation_of_relHammingDist_le
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (p : Witness F s d (0 : Fin (k + 2)))
    (hclose : (Code.relHammingDist (fun z ↦ initialOracle s stmt (initialQuery z))
      (fun z ↦ p.1.eval (ω z)) : ℝ) ≤ δ) :
    (stmt, p) ∈ inputRelation k s d hdom δ := by
  let e := (ω.subdomain 0).equivToFinset
  have he (z : Fin (2 ^ n)) : e z = initialQuery z := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hdist : Code.relHammingDist ((initialOracle s stmt) ∘ e)
      ((fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e) =
      Code.relHammingDist (initialOracle s stmt) (fun x ↦ p.1.eval x.val) := by
    unfold Code.relHammingDist
    rw [hammingDist_comp_equiv, Fintype.card_congr e]
  have hf : initialOracle s stmt ∘ e = (fun z ↦ initialOracle s stmt (initialQuery z)) :=
    funext (fun z ↦ congrArg (initialOracle s stmt) (he z))
  have hp : (fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e =
      (fun z ↦ p.1.eval (ω z)) := by
    funext z
    rw [Function.comp_apply, he]
    rfl
  have hprox : Code.relHammingDist (initialOracle s stmt) (fun x ↦ p.1.eval x.val) ≤ δ := by
    have h : (Code.relHammingDist (initialOracle s stmt) (fun x ↦ p.1.eval x.val) : ℝ) ≤ δ := by
      rw [← hdist, hf, hp]
      exact hclose
    exact_mod_cast h
  cases k <;> exact hprox


/-- The input relation bounds the distance of the indexed initial word to its witness. -/
theorem relHammingDist_le_of_mem_inputRelation
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (p : Witness F s d (0 : Fin (k + 2)))
    (hmem : (stmt, p) ∈ inputRelation k s d hdom δ) :
    (Code.relHammingDist (fun z ↦ initialOracle s stmt (initialQuery z))
      (fun z ↦ p.1.eval (ω z)) : ℝ) ≤ δ := by
  let e := (ω.subdomain 0).equivToFinset
  have he (z : Fin (2 ^ n)) : e z = initialQuery z := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hdist : Code.relHammingDist ((initialOracle s stmt) ∘ e)
      ((fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e) =
      Code.relHammingDist (initialOracle s stmt) (fun x ↦ p.1.eval x.val) := by
    unfold Code.relHammingDist
    rw [hammingDist_comp_equiv, Fintype.card_congr e]
  have hf : initialOracle s stmt ∘ e = (fun z ↦ initialOracle s stmt (initialQuery z)) :=
    funext (fun z ↦ congrArg (initialOracle s stmt) (he z))
  have hp : (fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e =
      (fun z ↦ p.1.eval (ω z)) := by
    funext z
    rw [Function.comp_apply, he]
    rfl
  have hprox : Code.relHammingDist (initialOracle s stmt) (fun x ↦ p.1.eval x.val) ≤ δ := by
    cases k <;> exact hmem
  rw [← hdist, hf, hp] at hprox
  exact_mod_cast hprox

/-- A word strictly within radius `δ` of the initial code has a witness in the existing
FRI input relation, which uses a closed proximity ball. -/
theorem mem_inputLanguage_of_proximity
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (hclose : initialOracle s stmt ∈ proximityLanguage s d (δ : ℝ)) :
    stmt ∈ (inputRelation k s d hdom (ω := ω) δ).language := by
  classical
  obtain ⟨u, hu, hclose⟩ := hclose
  obtain ⟨p, hp, rfl⟩ := (mem_code_iff_exists_polynomial).mp hu
  let pc : CompPoly.CPolynomial F := ⟨p.toImpl, CompPoly.CPolynomial.Raw.isCanonical_toImpl p⟩
  have hpc : pc.toPoly = p := CompPoly.CPolynomial.toPoly_mk_toImpl p
  have hdegree : pc ∈ Witness F s d (0 : Fin (k + 2)) := by
    rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT, hpc]
    simp only [finRangeTo, Fin.val_zero, List.take_zero, List.toFinset_nil,
      Finset.sum_empty, Nat.sub_zero]
    exact hp
  rw [Set.mem_language_iff]
  refine ⟨⟨pc, hdegree⟩, ?_⟩
  apply mem_inputRelation_of_relHammingDist_le s d hdom δ stmt ⟨pc, hdegree⟩
  simpa [CompPoly.CPolynomial.eval_toPoly, hpc, ReedSolomon.evalOnPoints] using hclose.le

end Fri.Spec
