/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.PersistenceDescent
public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.TraceChart
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ExceptionalCount

/-!
# Nonpersistent coefficient vectors of the Reed–Muller affine combiner

Let `K₀ ⊆ F` be finite fields with `q₀ = |K₀|`, and let `n = q₀ᵏ` be the grid size.
Let `L` be an extension of degree `k` of `K₀` with basis `b` and trace coordinates `ψ`.
Let `E` be an algebraically closed field containing `F` and `L`, compatibly over `K₀`.
Write `e = q₀ᵏ⁻¹`, with natural-number subtraction.

The generic chart count runs over `E` with challenges `α ∈ F^{k+1}`.
The multipliers are the substituted `L̃_α`, the family is the trace family, and `|κ| = k + 1`.
The high cuts cut out the substituted polynomials of total degree at most `d`.

An excluded chart point gives a second challenge and a substituted polynomial.
The difference with the candidate is explained by `H / L_σ` on `B + e` agreement points.
The identities descend to `F`, and dropping the zeros of `L_σ` gives persistence.

Hence, outside at most `D² + (2 d e M n / (A - B - e + 1)) ^ (k + 1) D ^ (k + 2)` vectors,
every candidate with `A` agreements is persistent at threshold `B`.
Here `D` and `M` are the degree budgets of an interpolant on `L` over `E`.

This is the nonpersistent count of Appendix A of [CWYZ26], with `v = n / (A - B - e + 1)`.
The paper's bound is `(2 ρ n M v) ^ (k + 1) D ^ (k + 2)`, with `ρ n = d e`.
The count here also covers the excluded set `E` of the paper, with its bound `D²`.
The paper's case split of Claim 4.8 is replaced by the descent of the ratio to `F`.
The statement assumes `1 ≤ d`, `d e < B + e` and `B + e ≤ A`.
The paper's condition `B > (d + 1) e` implies the second one.
The persistent set and the final numerics are not here.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.isAffinePersistent_of_mem_chartExcluded`: an excluded chart point of a
  transported candidate makes the candidate persistent.
* `ReedMuller.exists_finset_card_le_isAffinePersistent`: outside few coefficient vectors,
  every candidate with `A` agreements is persistent.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open Polynomial FiniteField Finset

variable {K₀ L F E : Type*} [Field K₀] [Fintype K₀] [Field L] [Algebra K₀ L] [Field F]
  [Field E] [Algebra L E] [Algebra F E] [Algebra K₀ F] [Algebra K₀ E] [IsScalarTower K₀ L E]
  [IsScalarTower K₀ F E] [DecidableEq F] {k : ℕ}

omit [Fintype K₀] [DecidableEq F] in
/-- Mapping `L_α` from `F` to `E` gives `L_{φ ∘ α}`, where `φ` is the embedding. -/
private theorem map_affineMultiplier (α : Fin (k + 1) → F) :
    (affineMultiplier α).map (algebraMap F E) = affineMultiplier (algebraMap F E ∘ α) := by
  simp [affineMultiplier]

omit [Fintype K₀] [DecidableEq F] in
/-- A grid point over `F`, mapped into `E`, is the grid point over `E`. -/
private theorem comp_gridPoint (z : Fin k → K₀) :
    algebraMap F E ∘ gridPoint F z = gridPoint E z := by
  funext i
  simp [IsScalarTower.algebraMap_apply K₀ F E]

/-- A transported candidate whose chart point is excluded is persistent.

Let `b` be a basis of `L` over `K₀` with trace coordinates `ψ`, and `q₀ = |K₀|`.
Let `e = q₀ᵏ⁻¹`, with natural-number subtraction.
Let `p` be the exponential characteristic of `E`, and `s = p ^ r`.
The chart uses the trace family and the coefficients `α` mapped by the inverse of `x ↦ x ^ s`.
Let `P` have total degree at most `d`, and let `P̃` be its trace substitution in `E`.
Assume `P̃(X ^ s)` is a root of `R` with nonzero derivative in `Z` at `c`.
Assume the cuts cut out the substituted polynomials of total degree at most `d`.
If the chart point is excluded at threshold `B + e`, then `P` is persistent at threshold `B`. -/
theorem isAffinePersistent_of_mem_chartExcluded (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F) {d B : ℕ} {cuts : List (E[X] →ₗ[E] E)}
    (hcuts : IsTraceImageCuts b d cuts) (c : E) (R : MvPolynomial ReedSolomon.AffineVar E)
    (p r : ℕ) [ExpChar E p] [PerfectRing E p] {α : Fin (k + 1) → F}
    {P : MvPolynomial (Fin k) F} (hP : P.totalDegree ≤ d)
    (hroot : ReedSolomon.multiplierEval (ReedSolomon.familyMultiplier
        (fun j ↦ (traceFamily E b j).map ((iterateFrobeniusEquiv E p r).symm : E →+* E))
        fun j ↦ (iterateFrobeniusEquiv E p r).symm (algebraMap F E (α j)))
      (Polynomial.expand E (p ^ r) (traceSubstitution b (P.map (algebraMap F E)))) R = 0)
    (hsep : (ReedSolomon.multiplierEval (ReedSolomon.familyMultiplier
        (fun j ↦ (traceFamily E b j).map ((iterateFrobeniusEquiv E p r).symm : E →+* E))
        fun j ↦ (iterateFrobeniusEquiv E p r).symm (algebraMap F E (α j)))
      (Polynomial.expand E (p ^ r) (traceSubstitution b (P.map (algebraMap F E))))
      (MvPolynomial.pderiv none R)).eval c ≠ 0)
    (hex : ReedSolomon.chartPoint c (p ^ r)
        (fun j ↦ (iterateFrobeniusEquiv E p r).symm (algebraMap F E (α j)))
        (traceSubstitution b (P.map (algebraMap F E))) ∈
      ReedSolomon.chartExcluded c
        (fun j ↦ (traceFamily E b j).map ((iterateFrobeniusEquiv E p r).symm : E →+* E)) R
        (p ^ r) (d * Fintype.card K₀ ^ (k - 1)) B (Fintype.card K₀ ^ (k - 1)) cuts
        (fun x : L ↦ Polynomial.leval (algebraMap L E x)) (traceChartTarget E b f g (p ^ r))) :
    IsAffinePersistent f g d B α P := by
  classical
  have hfr (x : E) : (iterateFrobeniusEquiv E p r).symm x ^ p ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  set φ := algebraMap F E
  set ψ := traceCoordinateEquiv K₀ b
  have hPmap : (P.map φ).totalDegree ≤ d :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ P)).trans hP
  have hP' : (traceSubstitution b (P.map φ)).degree ≤ (d * Fintype.card K₀ ^ (k - 1) : ℕ) :=
    degree_le_of_natDegree_le ((natDegree_traceSubstitution_le b _).trans
      (Nat.mul_le_mul_right _ hPmap))
  obtain ⟨U, hU, hcut, pt', -, hhigh', hcut', hne⟩ := hex
  rw [ReedSolomon.chartPolynomial_point c _ R rfl hP' hroot hsep] at hcut
  -- The candidate agrees with the first challenge on `U`, read on the grid.
  have hagreeE : ∀ x ∈ U, MvPolynomial.eval (gridPoint E (ψ x)) (P.map φ) =
      φ (f (ψ x)) + MvPolynomial.eval (gridPoint E (ψ x)) (affineMultiplier (φ ∘ α)) *
        φ (g (ψ x)) := by
    intro x hx
    have h := hcut x hx
    simp only [Polynomial.leval_apply, Sum.elim_comp_inr, ReedSolomon.chartPoint,
      aeval_traceChartTarget, hfr, eval_traceSubstitution] at h
    rw [h, eval_familyMultiplier_traceFamily]
    rfl
  -- The other challenge reconstructs a substituted polynomial `H'`.
  obtain ⟨H', hH', hH'eq⟩ := hcuts.exists_traceSubstitution_eq _
    (ReedSolomon.degree_chartPolynomial_le _ _ _ _ _ _) hhigh'
  set σ : Fin (k + 1) → E := (fun j ↦ pt' (.inr j) ^ p ^ r) - φ ∘ α
  have hexpl : ∀ x ∈ U, MvPolynomial.eval (gridPoint E (ψ x)) (H' - P.map φ) =
      MvPolynomial.eval (gridPoint E (ψ x)) (affineMultiplier σ) * φ (g (ψ x)) := by
    intro x hx
    have h := hcut' x hx
    rw [← hH'eq] at h
    simp only [Polynomial.leval_apply, aeval_traceChartTarget, eval_traceSubstitution,
      eval_familyMultiplier_traceFamily, Function.comp_apply] at h
    rw [map_sub, h, hagreeE x hx, affineMultiplier_sub, map_sub]
    ring
  -- The challenges differ, so `σ ≠ 0`.
  have hσ : σ ≠ 0 := by
    intro hσ0
    refine hne (funext fun j ↦ ?_)
    have hj := sub_eq_zero.mp (congrFun hσ0 j)
    simp only [Function.comp_apply, ReedSolomon.chartPoint, Sum.elim_inr] at hj ⊢
    rw [← hj, ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]
  -- The identities descend to `F`.
  obtain ⟨H₀, σ₀, hσ₀, hH₀, h₀⟩ := exists_affineRatioWitness_of_map φ
    (fun x : U ↦ gridPoint F (ψ x)) (fun x ↦ g (ψ x)) d hσ
    ((MvPolynomial.totalDegree_sub _ _).trans (max_le hH' hPmap)) fun x ↦ by
      rw [comp_gridPoint]
      exact hexpl x x.2
  set T := U.map ψ.toEquiv.toEmbedding
  have hT : B + Fintype.card K₀ ^ (k - 1) ≤ #T := by rwa [card_map]
  have hagree : T ⊆ agreementSet (combinedWord f g (affineMultiplier α)) P := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    rw [mem_agreementSet, combinedWord_apply]
    apply φ.injective
    have h := hagreeE x hx
    rw [← map_affineMultiplier, eval_gridPoint_map, eval_gridPoint_map] at h
    simpa [map_add, map_mul] using h
  refine isAffinePersistent_of_commonAgreement f g T hT hagree hσ₀ hH₀ fun z hz ↦ ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
  exact h₀ ⟨x, hx⟩

/-- Outside few coefficient vectors, every candidate with `A` agreements is persistent.

Let `K₀ ⊆ F` be finite fields with `q₀ = |K₀|`, and let `n = q₀ᵏ` be the grid size.
Let `b` be a basis of `L` over `K₀`, with trace coordinates `ψ`.
Let `E` be algebraically closed and contain `F` and `L` compatibly over `K₀`.
Let `e = q₀ᵏ⁻¹`, with natural-number subtraction.
Let `Q` be an interpolant on `L ⊆ E` for the words `f ∘ ψ` and `g ∘ ψ` mapped into `E`.
It is for multipliers of degree at most `e` and candidates of degree at most `d e`.
Its `(Y, Z)`-degree is at most `D` and its `Z`-degree at most `M`.
Assume `1 ≤ d`, `d e < B + e` and `B + e ≤ A`.
At most `D² + (2 d e M n / (A - B - e + 1)) ^ (k + 1) D ^ (k + 2)` vectors are left out.
The subtraction `A - B - e` is natural-number subtraction.
Outside them, every `P` of total degree at most `d` with `A` agreements with `f + L_α g`
is persistent at threshold `B`. -/
theorem exists_finset_card_le_isAffinePersistent [Finite F] [Fintype L] [DecidableEq E]
    [IsAlgClosed E] (b : Module.Basis (Fin k) K₀ L) (f g : (Fin k → K₀) → F)
    {d A B m D M : ℕ} {Q : MvPolynomial ReedSolomon.AffineVar E}
    (hQ : ReedSolomon.IsMultiplierInterpolant (ReedSolomon.algebraMapDomain L E)
      (fun x ↦ algebraMap F E (f (traceCoordinateEquiv K₀ b x)))
      (fun x ↦ algebraMap F E (g (traceCoordinateEquiv K₀ b x))) (Fintype.card K₀ ^ (k - 1))
      (d * Fintype.card K₀ ^ (k - 1)) A m D M Q)
    (hd : 1 ≤ d) (hdB : d * Fintype.card K₀ ^ (k - 1) < B + Fintype.card K₀ ^ (k - 1))
    (hBA : B + Fintype.card K₀ ^ (k - 1) ≤ A) :
    ∃ Ex : Finset (Fin (k + 1) → F), (#Ex : ℝ) ≤ D ^ 2 +
        (2 * (d * Fintype.card K₀ ^ (k - 1) : ℕ) * M * ((Fintype.card K₀ ^ k : ℕ) /
          (A - B - Fintype.card K₀ ^ (k - 1) + 1 : ℕ))) ^ (k + 1) * D ^ (k + 2) ∧
      ∀ α ∉ Ex, ∀ P : MvPolynomial (Fin k) F, P.totalDegree ≤ d →
        A ≤ #(agreementSet (combinedWord f g (affineMultiplier α)) P) →
        IsAffinePersistent f g d B α P := by
  classical
  set e := Fintype.card K₀ ^ (k - 1)
  set p := ringExpChar E
  set φ := algebraMap F E
  have hcardL : Fintype.card L = Fintype.card K₀ ^ k := by
    rw [Module.card_fintype b, Fintype.card_fin]
  by_cases hAn : A ≤ Fintype.card K₀ ^ k
  swap
  · -- No candidate has more agreements than grid points.
    refine ⟨∅, by rw [card_empty, Nat.cast_zero]; positivity,
      fun α _ P _ hA ↦ absurd ((hA.trans (card_le_univ _)).trans ?_) hAn⟩
    simp
  have hfr (r : ℕ) (x : E) : (iterateFrobeniusEquiv E p r).symm x ^ p ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have he : 1 ≤ e := Nat.one_le_pow _ _ Fintype.card_pos
  obtain ⟨cuts, hcuts⟩ := exists_isTraceImageCuts E b d
  obtain ⟨Ex, hEx, hgood⟩ := ReedSolomon.exists_interpolantRoots_finset_card_le
    (κ := Fin (k + 1)) (Γ := Fin (k + 1) → F) p hQ.ne_zero (d := d * e) (B := B) (e := e)
    (Nat.mul_le_mul hd he) (by omega) hBA (hcardL ▸ hAn) hQ.yzDegree_le hQ.rootDegree_le
    (fun α ↦ ReedSolomon.familyMultiplier (traceFamily E b) (φ ∘ α))
    (familyMultiplier_traceFamily_injective b)
    (fun r j ↦ (traceFamily E b j).map ((iterateFrobeniusEquiv E p r).symm : E →+* E))
    (fun r α j ↦ (iterateFrobeniusEquiv E p r).symm (φ (α j)))
    (fun r α α' h ↦ funext fun j ↦ φ.injective
      (((iterateFrobeniusEquiv E p r).symm.injective) (congrFun h j)))
    (fun r α ↦ map_familyMultiplier_traceFamily b _ _)
    cuts (fun x : L ↦ Polynomial.leval (algebraMap L E x))
    (fun x ↦ φ (f (traceCoordinateEquiv K₀ b x))) (fun x ↦ φ (g (traceCoordinateEquiv K₀ b x)))
    (fun r ↦ traceChartTarget E b f g (p ^ r))
    (fun r ↦ totalDegree_traceChartTarget_le b f g _)
    (fun r α x ↦ by
      rw [aeval_traceChartTarget]
      simp only [hfr, Polynomial.leval_apply]
      rfl)
    (separatesDegree_of_isTraceImageCuts hcuts hdB)
    (fun α P' ↦ ∀ P : MvPolynomial (Fin k) F, P.totalDegree ≤ d →
      P' = traceSubstitution b (P.map φ) → IsAffinePersistent f g d B α P)
    (fun r R c α P' _ hroot hc hex P hP hPP' ↦ by
      subst hPP'
      exact isAffinePersistent_of_mem_chartExcluded b f g hcuts c R p r hP hroot hc hex)
  have hPmap (P : MvPolynomial (Fin k) F) (hP : P.totalDegree ≤ d) :
      (P.map φ).totalDegree ≤ d :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ P)).trans hP
  refine ⟨Ex, ?_, fun α hα P hP hA ↦ hgood α hα _
    (multiplierEval_traceSubstitution_eq_zero b f g hQ α hP hA)
    (degree_le_of_natDegree_le ((natDegree_traceSubstitution_le b _).trans
      (Nat.mul_le_mul_right _ (hPmap P hP))))
    (hcuts.apply_traceSubstitution_eq_zero _ (hPmap P hP)) ?_ P hP rfl⟩
  · rw [Fintype.card_fin, hcardL] at hEx
    exact hEx
  · simp only [Polynomial.leval_apply]
    rw [ncard_eval_traceSubstitution_eq]
    exact hA

end ReedMuller
