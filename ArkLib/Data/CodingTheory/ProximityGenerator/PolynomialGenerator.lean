/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
## Main Results

- Statement of Theorem 8.2 (MCA for polynomial generators) [BCGM25].
- Statement of Lemma 9.3 [BCGM25] - sorried out. It depends on the Guruswami-Sudan part of Proximity
Gaps.
- Statement and proof (using Lemma 9.3.) of Theorem 9.2 (Polynomial Generators have MCA for
Reed-Solomon codes up to the Johnson bound) [BCGM25].

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

namespace PolynomialGenIsMCA

open unitInterval CoreDefinitions

variable {F : Type} [Field F] [Fintype F]
         {ι : Type} [Fintype ι] [Nonempty ι]

/-- A function assinging the maximum degree in the `i`-the variable of the collection of
polynomials `P`. -/
noncomputable def deg_max {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F) :
    Fin s → ℕ := fun i => Finset.sup Fintype.elems (fun j => (P j).degreeOf i)

/-- Definition 8.1 (MCA error for univariate powers) [BCGM25].
Note: In the paper, there is a hypothesis `η ∈ (0,1)`. This is omitted in the definition of `ξ`
since the hypothesis is not required to define `ξ`. However, we include it in statement that rely on
or utilise `ξ`. -/
noncomputable def ξ [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) :
  I → ℝ :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (LC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_d : ℝ := 1 - (ρ_C + η) ^ (1 / (d + 1) : ℝ)
  fun γ =>
    if γ < (δ_C / (d + 2) : ℝ) then
      letI m' : ℝ := max (n * γ) 1
      m' * (d / m : ℝ)
    else
      if γ ≤ 1 - (ρ_C + η) ^ (1 / (d + 2) : ℝ) then
          (n * γ_d / η) * (d / m) +
          max (2 * d / (η * ((ρ_C + η) ^ (1 / (d + 2) : ℝ) - (ρ_C + η) ^ (1 / (d + 1) : ℝ)) * m))
              ((d + 1) * (d + 2) / (η * m) : ℝ)
      else
      1

/-- Theorem 8.2 (MCA for polynomial generators) [BCGM25]. -/
theorem polynomial_gen_MCA [DecidableEq F] {ℓ : Type} [Fintype ℓ] (LC : LinearCode ι F) (d : ℕ)
  (η : ℝ) (hη : 0 < η ∧ η < 1) {s : ℕ}
  (S : Fin s → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
  (G : Generator (∀ i, S i) ℓ F)
  (P : ℓ → MvPolynomial (Fin s) F) (hG : IsPolynomialGeneratorOf S G P)
  (hℓ : 2 ≤ Fintype.card ℓ) (hS : ∀ i : Fin s, (deg_max P i + 1) ≤ (Set.ncard (S i))) :
  letI ε : I → ℝ := ∑ i : Fin s, (ξ LC (deg_max P i) (Set.ncard (S i)) η)
  IsMCAGenerator G ε LC := by
  sorry

end PolynomialGenIsMCA

namespace RSCode

open unitInterval CoreDefinitions PolynomialGenIsMCA LinearTransformations LinearCode MvPolynomial
  Matrix
open scoped ProbabilityTheory ENNReal BigOperators

variable {F : Type} [Field F]
         {ι : Type} [Fintype ι]
         (k : ℕ) -- degree of the polynomials
         (D : ι ↪ F) -- the domain of evaluation


/-- Definition 9.1 [BCGM25]. -/
noncomputable def ε_mca_RS [Fintype F] (n d m : ℕ) : I → ℝ :=
  let ρ_sqrt := ReedSolomon.sqrtRate k D
  fun γ =>
    if γ ≤ 1 - (1 + (1 / 2 * m : ℝ)) * ρ_sqrt then
      (|Fintype.card F| : ℝ)⁻¹  *  (m + 1 / 2) ^ 7  * (3 * (ρ_sqrt) ^ 3)⁻¹.toReal * d * n ^ 2
    else
      1

/-- Let `F` be a field and `k, n, d, m ∈ ℕ` with `m ≥ 3`. Then the univariate powers generator has
MCA for a Reed-Solomon code over a domain `D` and degree `k` with error `ε_mca_RS` as defined
above.
Lemma 9.3 [BCGM25]. -/
lemma univarite_powers_MCA [Fintype F] (n d m : ℕ) (hm : 3 ≤ m) :
    IsMCAGenerator (UnivariatePowers d) (ε_mca_RS k D n d m) (ReedSolomon.code D k) := by
  sorry

/-- The `s`-fold tensor product of univariate powers generators. This is the generator defined in
the proof of Theorem 9.2 [BCGM25].
`tilde{G} : (x_1, ..., x_s) ↦ ⊗_{i ∈ [s]} (1, x_i, ..., x_i^{d_i})`. -/
def tensor_of_univ {s : ℕ} (d : Fin s → ℕ) :
    Generator (Fin s → F) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, x i ^ (j i : ℕ)

/-- The multi-index (as a finitely supported function) associated to a bounded exponent vector. -/
noncomputable def exponentFinsupp {s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) → Fin (d i + 1)) :
    Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

/-- Evaluating the monomial of a bounded exponent vector recovers that vector's entries. -/
@[simp] lemma exponentFinsupp_apply {s : ℕ} {d : Fin s → ℕ}
    (e : (i : Fin s) → Fin (d i + 1)) (i : Fin s) :
    exponentFinsupp e i = (e i : ℕ) := by
  simp [exponentFinsupp]

/-- Distinct bounded exponent vectors give distinct monomials.  This lets a sum over the monomials
in the box `d` be rewritten as a sum over the finite index type `(i : Fin s) → Fin (d i + 1)`,
via `Finset.sum_image`. -/
lemma exponentFinsupp_injective {s : ℕ} {d : Fin s → ℕ} :
    Function.Injective (exponentFinsupp (d := d)) := by
  intro e₁ e₂ h
  funext i
  have := congrArg (fun f => (f i : ℕ)) h
  simpa using Fin.val_injective (by simpa [exponentFinsupp] using this)

/-- Conversely, every monomial lying inside the box `d` is `exponentFinsupp` of some bounded
exponent vector.  Together with `exponentFinsupp_injective` this identifies the box index type with
the set of monomials of individual degree at most `d`. -/
lemma exists_exponentFinsupp_eq {s : ℕ} {d : Fin s → ℕ} {mo : Fin s →₀ ℕ} (h : ∀ i, mo i ≤ d i) :
    ∃ e, exponentFinsupp (d := d) e = mo :=
  ⟨fun i => ⟨mo i, Nat.lt_succ_of_le (h i)⟩, by ext i; simp [exponentFinsupp]⟩

/-- The coefficient matrix expressing the polynomial generator `G` as a right multiplication of the
tensor generator: the entry at `(e, j)` is the coefficient of the monomial `exponentFinsupp e` in
the polynomial `P j`.

This is the matrix `A ∈ F^{k×ℓ}` of [BCGM25, Section 2.2], with `k = ∏ᵢ (dᵢ + 1)`.  Equivalently, it
is `Aᵀ` for the `A ∈ F^{ℓ×k}` used in the proof of Theorem 9.2 [BCGM25]. -/
noncomputable def coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F)
    (d : Fin s → ℕ) : Matrix ((i : Fin s) → Fin (d i + 1)) ℓ F :=
  fun e j => (P j).coeff (exponentFinsupp e)

/-- The `s`-fold tensor product of univariate powers generators has MCA for any linear code
`LC`, with error the sum `∑ i, ε (d i)` of the factors' errors, provided each univariate powers
generator has MCA for `LC` with error `ε e`.
This is the `s`-fold iteration of Lemma 4.4 (tensor products preserve MCA) [BCGM25]. -/
lemma tensor_of_univ_is_MCA [Fintype F] (LC : LinearCode ι F) (ε : ℕ → I → ℝ)
    (huniv : ∀ e : ℕ, IsMCAGenerator (UnivariatePowers e) (ε e) LC) :
    ∀ {s : ℕ} (d : Fin s → ℕ),
      IsMCAGenerator (tensor_of_univ d) (fun γ => ∑ i, ε (d i) γ) LC := by
  intro s
  induction s with
  | zero =>
    intro d U γ
    classical
    have hfalse : ∀ x : Fin 0 → F, ¬ IsMCA (tensor_of_univ d) LC x U γ := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : Matrix.vecMul (tensor_of_univ d x) U = U j := by
        funext w
        simp only [Matrix.vecMul, dotProduct]
        rw [Fintype.sum_subsingleton _ j]
        simp [tensor_of_univ]
      rwa [hvec] at hmem
    rw [prob_uniform_eq_ofReal, Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  | succ s ih =>
    intro d
    set eS : (Fin (s + 1) → F) ≃ (F × (Fin s → F)) :=
      (Fin.consEquiv (fun _ => F)).symm with heS
    set eL : (Fin (d 0 + 1) × ((i : Fin s) → Fin (Fin.tail d i + 1)))
        ≃ ((i : Fin (s + 1)) → Fin (d i + 1)) :=
      Fin.consEquiv (fun i => Fin (d i + 1)) with heL
    have hBin := tensor_of_MCA_is_MCA_tight LC
      (UnivariatePowers (d 0)) (ε (d 0)) (huniv (d 0))
      (tensor_of_univ (Fin.tail d)) (fun γ => ∑ i, ε (Fin.tail d i) γ)
      (ih (Fin.tail d))
    have hR := isMCAGenerator_reindex LC
      (TensorGenerator_Explicit (UnivariatePowers (d 0)) (tensor_of_univ (Fin.tail d)))
      _ hBin eS eL
    have hgen : (fun (x' : Fin (s + 1) → F) (j' : (i : Fin (s + 1)) → Fin (d i + 1)) =>
        TensorGenerator_Explicit (UnivariatePowers (d 0)) (tensor_of_univ (Fin.tail d))
          (eS x') (eL.symm j')) = tensor_of_univ d := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, Fin.consEquiv_symm_apply,
        UnivariatePowers, tensor_of_univ, Fin.tail, Fin.prod_univ_succ]
      simp_all only [Fin.consEquiv_symm_apply, eS, eL]
      rfl
    have herr : ((ε (d 0)) + fun γ => ∑ i, ε (Fin.tail d i) γ)
        = (fun γ => ∑ i, ε (d i) γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ, Fin.tail]
    rw [hgen, herr] at hR
    exact hR

/-- The polynomial generator `G` is the right multiplication of the tensor generator by the
coefficient matrix. (`G = G̃ · Aᵀ` in the proof of Theorem 9.2 [BCGM25]). -/
lemma generatorByRightMul_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (Fin s → F) ℓ F) (hG : ∀ x, G x = MvPolynomial.eval x ∘ P) :
    generatorByRightMul (tensor_of_univ d) (coeffMatrix P d) = G := by
  funext x j
  rw [hG]
  simp only [Function.comp_apply, generatorByRightMul, Matrix.vecMul, dotProduct, tensor_of_univ,
    coeffMatrix]
  have hsub : (P j).support ⊆ Finset.univ.image (exponentFinsupp (d := d)) := by
    intro mo hmo
    obtain ⟨e, he⟩ :=
      exists_exponentFinsupp_eq fun i => le_trans (monomial_le_degreeOf i hmo) (hdeg j i)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
  rw [eval_eq', Finset.sum_subset hsub
      (fun mo _ hmo => by simp [MvPolynomial.notMem_support_iff.mp hmo]),
    Finset.sum_image (fun a _ b _ h => exponentFinsupp_injective h)]
  exact Finset.sum_congr rfl fun e _ => by simp [mul_comm]

/-- The coefficient matrix has a left inverse. -/
lemma coeffMatrix_hasLeftPseudoInverse {s : ℕ} {ℓ : Type} [Fintype ℓ] [DecidableEq ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i) (hP : LinearIndependent F P) :
    HasLeftPseudoInverse (coeffMatrix P d) := by
  set A := coeffMatrix P d with hA
  have hinj : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    set Q : MvPolynomial (Fin s) F := ∑ j, v j • P j with hQ
    have hcoeff : ∀ e : (i : Fin s) → Fin (d i + 1), Q.coeff (exponentFinsupp e) = 0 := by
      intro e
      have hve := congrFun hv e
      simpa [hA, coeffMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct, hQ,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, mul_comm] using hve
    have hQ0 : Q = 0 := by
      ext mo
      rw [MvPolynomial.coeff_zero]
      by_cases hmem : ∀ i, mo i ≤ d i
      · obtain ⟨e, he⟩ := exists_exponentFinsupp_eq hmem
        exact he ▸ hcoeff e
      · simp only [not_forall, not_le] at hmem
        obtain ⟨i, hi⟩ := hmem
        apply MvPolynomial.notMem_support_iff.mp
        intro hmo
        rw [hQ] at hmo
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
        have hj' : mo ∈ (P j).support := MvPolynomial.support_smul hj
        exact absurd (le_trans (monomial_le_degreeOf i hj') (hdeg j i)) (by omega)
    exact funext fun j => Fintype.linearIndependent_iff.mp hP v (hQ.symm.trans hQ0) j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hcomp : LinearMap.toMatrix' (g.comp A.mulVecLin) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp]
    congr 1
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [hg, LinearMap.toMatrix'_id] at hcomp
  exact hcomp.symm

/-- Take a Reed–Solomon code of polynomials of degree less than `k` over an evaluation domain
`D`. Let `G` be a polynomial generator where each `S` is the whole field `F`.
Then, for every `m ≥ 3`, `G` has MCA for with error `∑ i, ε_mca_RS`.
Theorem 9.2 [BCGM25]. -/
lemma PolyGen_MCA_RScode [Fintype F] (n m : ℕ) (hm : 3 ≤ m) {ℓ : Type} [Fintype ℓ] {s : ℕ}
    {P : ℓ → MvPolynomial (Fin s) F} (G : Generator ((Fin s) → F) ℓ F)
    (hG : IsPolynomialGeneratorOfFull G P) :
    letI ε := ∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m
    IsMCAGenerator G ε (ReedSolomon.code D k) := by
  classical
  show IsMCAGenerator G (∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m) (ReedSolomon.code D k)
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ deg_max P i := by
    intro j i
    simpa [deg_max] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Fintype.complete j)
  have htensor := tensor_of_univ_is_MCA (ReedSolomon.code D k) (fun e => ε_mca_RS k D n e m)
    (fun e => univarite_powers_MCA k D n e m hm) (deg_max P)
  have hmul := pseudoinverseGen (tensor_of_univ (deg_max P))
    (fun γ => ∑ i, ε_mca_RS k D n (deg_max P i) m γ) (ReedSolomon.code D k) htensor
    (coeffMatrix P (deg_max P))
    (coeffMatrix_hasLeftPseudoInverse P (deg_max P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix P (deg_max P) hdeg G hG.2] at hmul
  rwa [_root_.funext fun γ => (Finset.sum_apply γ Finset.univ _).symm] at hmul

end RSCode
