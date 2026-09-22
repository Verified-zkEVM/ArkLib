/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.AdaptiveSoundness
import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# The FRI input relation and Reed–Solomon proximity

This connects the computational polynomial witness in the existing specification with
the existing Reed–Solomon code. Coordinate reindexing uses the domain's canonical equivalence.
-/

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

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
  let e := (ω.subdomain 0).equivToFinset
  have he (z : Fin (2 ^ n)) : e z = initialQuery z := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have heval : (fun x : (ω.subdomain 0).toFinset ↦ pc.eval x.val) ∘ e =
      evalOnPoints ω p := by
    funext z
    rw [Function.comp_apply, CompPoly.CPolynomial.eval_toPoly, hpc, he]
    rfl
  have hdist : Code.relHammingDist ((initialOracle s stmt) ∘ e)
      ((fun x : (ω.subdomain 0).toFinset ↦ pc.eval x.val) ∘ e) =
      Code.relHammingDist (initialOracle s stmt) (fun x ↦ pc.eval x.val) := by
    unfold Code.relHammingDist
    rw [hammingDist_comp_equiv, Fintype.card_congr e]
  have hprox : (Code.relHammingDist (initialOracle s stmt) (fun x ↦ pc.eval x.val) : ℝ) < δ := by
    rw [← hdist, heval]
    have hf : initialOracle s stmt ∘ e = (fun z ↦ initialOracle s stmt (initialQuery z)) :=
      funext (fun z ↦ congrArg (initialOracle s stmt) (he z))
    rw [hf]
    exact hclose
  have hprox' : Code.relHammingDist (initialOracle s stmt) (fun x ↦ pc.eval x.val) ≤ δ := by
    exact_mod_cast hprox.le
  rw [Set.mem_language_iff]
  refine ⟨⟨pc, hdegree⟩, ?_⟩
  cases k <;> exact hprox'

end Fri.Spec
