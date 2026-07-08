/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.Prelims
import Mathlib


/-!
## Main Results

-

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
    Fin s → ℕ :=
  fun i => Finset.sup Fintype.elems (fun j => (P j).degreeOf i)

/-- Definition 8.1 [BCGM25]. -/
noncomputable def ξ [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) (hη : 0 < η ∧ η < 1) :
  I → ℝ :=
  let n : ℝ := Fintype.card ι
  let δ : ℝ := (Code.minRelHammingDistCode (LC.carrier) : ℝ)
  let ρ : ℝ := 1 - δ
  let γ_d : ℝ := 1 - (ρ + η) ^ (1 / (d + 1) : ℝ)
  fun γ =>
    if γ < (δ / (d + 2) : ℝ) then
      let m' : ℝ := max (n * γ) 1
      m' * (d / m : ℝ)
    else
      if γ ≤ 1 - (ρ + η) ^ (1 / (d + 2) : ℝ) then
          (n * γ_d / η) * (d / m) +
          max (2 * d / (η * ((ρ + η) ^ (1 / (d + 2) : ℝ) - (ρ + η) ^ (1 / (d + 1) : ℝ)) * m))
              ((d + 1) * (d + 2) / (η * m) : ℝ)
      else
      1

/-- Theorem 8.2. [BCGM25] -/
theorem polynomial_gen_MCA [DecidableEq F] {ℓ : Type} [Fintype ℓ] (LC : LinearCode ι F) (d : ℕ)
  (η : ℝ) (hη : 0 < η ∧ η < 1) {s : ℕ}
  (S : Fin s → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
  (G : Generator (∀ i, S i) ℓ F)
  (P : ℓ → MvPolynomial (Fin s) F) (hG : IsPolynomialGeneratorOf S G P)
  (hℓ : 2 ≤ Fintype.card ℓ) (hS : ∀ i : Fin s, (deg_max P i + 1) ≤ (Set.ncard (S i))) :
  letI ε : I → ℝ := ∑ i : Fin s, (ξ LC (deg_max P i) (Set.ncard (S i)) η hη)
  IsMCAGenerator G ε LC := by
  sorry

end PolynomialGenIsMCA


namespace RSCode

open unitInterval CoreDefinitions PolynomialGenIsMCA LinearTransformations LinearCode MvPolynomial
  Matrix
open scoped ProbabilityTheory ENNReal BigOperators

variable {F : Type} [Field F] [Fintype F]
         {ι : Type} [Fintype ι]
         (k : ℕ) -- degree of the polynomials
         (D : ι ↪ F) -- the domain of evaluation


/-- Definition 9.1 [BCGM25]. -/
noncomputable def ε_mca_RS (n d m : ℕ) : I → ℝ :=
  let ρ_sqrt := ReedSolomon.sqrtRate k D
  fun γ =>
    if γ ≤ 1 - (1 + (1 / 2 * m : ℝ)) * ρ_sqrt then
      (|Fintype.card F| : ℝ)⁻¹  *  (m + 1/2) ^ 7  * (3 * (ρ_sqrt) ^ 3)⁻¹.toReal * d * n ^ 2
    else
      1

/-- Lemma 9.3 [BCGM25]. -/
lemma univarite_powers_MCA (n d m : ℕ) (hm : 3 ≤ m) :
    IsMCAGenerator (UnivariatePowers d) (ε_mca_RS k D n d m) (ReedSolomon.code D k) := by
  sorry

/-! ### The reduction of Theorem 9.2 to Lemma 9.3

Following the proof of Theorem 9.2 [BCGM25], a polynomial generator `G` is written as a linear
transformation of the tensor product `⊗ᵢ (1, Xᵢ, …, Xᵢ^{dᵢ})` of univariate powers generators.  We
build this tensor generator explicitly (`tensorUniv`), transport the MCA error of univariate powers
across the tensor product (`tensorUniv_MCA`, using the toolbox lemmas `tensor_of_MCA_is_MCA_tight`
and `isMCAGenerator_reindex`), and finally express `G` as a right multiplication of `tensorUniv` by
the coefficient matrix (`coeffMatrix`), whose left invertibility follows from the linear
independence of the defining polynomials. -/

/-- The `s`-fold tensor product of univariate powers generators.  Its output coordinate indexed by a
bounded exponent vector `j : ∀ i, Fin (d i + 1)` is the monomial `∏ i, xᵢ ^ (j i)`.  This is the
generator `⊗ᵢ (1, Xᵢ, …, Xᵢ^{dᵢ})` appearing in the proof of Theorem 9.2 [BCGM25]. -/
def tensorUniv {s : ℕ} (d : Fin s → ℕ) :
    Generator (Fin s → F) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, x i ^ (j i : ℕ)

/-- The multi-index (as a finitely supported function) associated to a bounded exponent vector. -/
noncomputable def boxIdx {s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) → Fin (d i + 1)) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

@[simp] lemma boxIdx_apply {s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) → Fin (d i + 1)) (i : Fin s) :
    boxIdx e i = (e i : ℕ) := by
  simp [boxIdx]

lemma boxIdx_injective {s : ℕ} {d : Fin s → ℕ} :
    Function.Injective (boxIdx (d := d)) := by
  intro e₁ e₂ h
  funext i
  have := congrArg (fun f => (f i : ℕ)) h
  simpa [boxIdx_apply] using Fin.val_injective (by simpa [boxIdx_apply] using this)

/-- The coefficient matrix expressing the polynomial generator `G` as a right multiplication of the
tensor generator: `A e j` is the coefficient of the monomial `boxIdx e` in the polynomial `P j`. -/
noncomputable def coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F)
    (d : Fin s → ℕ) : Matrix ((i : Fin s) → Fin (d i + 1)) ℓ F :=
  fun e j => (P j).coeff (boxIdx e)

/-- The tensor product of univariate powers generators has MCA for the Reed–Solomon code with error
`∑ i, ε_mca_RS … (d i) …`, provided each univariate powers generator does (Lemma 9.3 [BCGM25]).
This is the tensor-product step in the proof of Theorem 9.2 [BCGM25]. -/
lemma tensorUniv_MCA (n m : ℕ)
    (huniv : ∀ e : ℕ,
      IsMCAGenerator (UnivariatePowers e) (ε_mca_RS k D n e m) (ReedSolomon.code D k)) :
    ∀ {s : ℕ} (d : Fin s → ℕ),
      IsMCAGenerator (tensorUniv d) (fun γ => ∑ i, ε_mca_RS k D n (d i) m γ)
        (ReedSolomon.code D k) := by
  intro s
  induction s with
  | zero =>
    intro d U γ
    classical
    -- With no variables the output type is a subsingleton, so the MCA event never holds.
    have hfalse : ∀ x : Fin 0 → F, ¬ IsMCA (tensorUniv d) (ReedSolomon.code D k) x U γ := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : Matrix.vecMul (tensorUniv d x) U = U j := by
        funext w
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.sum_eq_single j]
        · simp [tensorUniv]
        · exact fun b _ hb => absurd (Subsingleton.elim b j) hb
        · exact fun h => absurd (Finset.mem_univ j) h
      rwa [hvec] at hmem
    rw [prob_uniform_eq_ofReal]
    have hempty : (Finset.univ.filter
        (fun x : Fin 0 → F => IsMCA (tensorUniv d) (ReedSolomon.code D k) x U γ)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact hfalse x
    rw [hempty]
    simp
  | succ s ih =>
    intro d
    -- Split off the first variable via the `cons` equivalences on seeds and output coordinates.
    set eS : (Fin (s + 1) → F) ≃ (F × (Fin s → F)) :=
      (Fin.consEquiv (fun _ => F)).symm with heS
    set eL : (Fin (d 0 + 1) × ((i : Fin s) → Fin (Fin.tail d i + 1)))
        ≃ ((i : Fin (s + 1)) → Fin (d i + 1)) :=
      Fin.consEquiv (fun i => Fin (d i + 1)) with heL
    have hBin := tensor_of_MCA_is_MCA_tight (ReedSolomon.code D k)
      (UnivariatePowers (d 0)) (ε_mca_RS k D n (d 0) m) (huniv (d 0))
      (tensorUniv (Fin.tail d)) (fun γ => ∑ i, ε_mca_RS k D n (Fin.tail d i) m γ)
      (ih (Fin.tail d))
    have hR := isMCAGenerator_reindex (ReedSolomon.code D k)
      (TensorGenerator_Explicit (UnivariatePowers (d 0)) (tensorUniv (Fin.tail d)))
      _ hBin eS eL
    have hgen : (fun (x' : Fin (s + 1) → F) (j' : (i : Fin (s + 1)) → Fin (d i + 1)) =>
        TensorGenerator_Explicit (UnivariatePowers (d 0)) (tensorUniv (Fin.tail d))
          (eS x') (eL.symm j')) = tensorUniv d := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, Equiv.toFun_as_coe, Fin.consEquiv_symm_apply,
        UnivariatePowers, tensorUniv, Fin.tail, Fin.prod_univ_succ]
    have herr : ((ε_mca_RS k D n (d 0) m) +
          fun γ => ∑ i, ε_mca_RS k D n (Fin.tail d i) m γ)
        = (fun γ => ∑ i, ε_mca_RS k D n (d i) m γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ, Fin.tail]
    rw [hgen, herr] at hR
    exact hR

/-- The polynomial generator `G` is the right multiplication of the tensor generator by the
coefficient matrix.  This is the algebraic identity `G = G̃ · Aᵀ` in the proof of Theorem 9.2
[BCGM25], phrased with the `vecMul` convention of `generatorByRightMul`. -/
lemma generatorByRightMul_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (Fin s → F) ℓ F) (hG : ∀ x, G x = MvPolynomial.eval x ∘ P) :
    generatorByRightMul (tensorUniv d) (coeffMatrix P d) = G := by
  classical
  funext x j
  rw [hG]
  simp only [Function.comp_apply, generatorByRightMul, Matrix.vecMul, dotProduct, tensorUniv,
    coeffMatrix]
  -- `∑ e, (∏ i, xᵢ^{eᵢ}) * coeff (boxIdx e) (P j) = eval x (P j)`.
  set g : (Fin s →₀ ℕ) → F := fun mo => (P j).coeff mo * ∏ i, x i ^ (mo i) with hg
  have hsub : (P j).support ⊆ Finset.univ.image (boxIdx (d := d)) := by
    intro mo hmo
    rw [Finset.mem_image]
    refine ⟨fun i => ⟨mo i, Nat.lt_succ_of_le (le_trans (monomial_le_degreeOf i hmo) (hdeg j i))⟩,
      Finset.mem_univ _, ?_⟩
    ext i
    simp
  rw [eval_eq', Finset.sum_subset hsub
      (fun mo _ hmo => by simp [hg, MvPolynomial.notMem_support_iff.mp hmo]),
    Finset.sum_image (fun a _ b _ h => boxIdx_injective h)]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [hg, boxIdx_apply]
  ring

/-- The coefficient matrix has a left inverse, because the defining polynomials are linearly
independent and supported within the exponent box.  This is the full row rank claim for `A` in the
proof of Theorem 9.2 [BCGM25]. -/
lemma coeffMatrix_hasLeftPseudoInverse {s : ℕ} {ℓ : Type} [Fintype ℓ] [DecidableEq ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i) (hP : LinearIndependent F P) :
    HasLeftPseudoInverse (coeffMatrix P d) := by
  classical
  set A := coeffMatrix P d with hA
  -- `A.mulVecLin` is injective: `A *ᵥ v = 0` forces the polynomial `∑ vⱼ • Pⱼ` to vanish.
  have hinj : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    set Q : MvPolynomial (Fin s) F := ∑ j, v j • P j with hQ
    have hcoeff : ∀ e : (i : Fin s) → Fin (d i + 1), Q.coeff (boxIdx e) = 0 := by
      intro e
      have hve := congrFun hv e
      simpa [hA, coeffMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct, hQ,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, mul_comm] using hve
    have hQ0 : Q = 0 := by
      ext mo
      rw [MvPolynomial.coeff_zero]
      by_cases hmem : ∀ i, mo i ≤ d i
      · have hbox : mo = boxIdx (fun i => ⟨mo i, Nat.lt_succ_of_le (hmem i)⟩) := by ext i; simp
        rw [hbox]; exact hcoeff _
      · simp only [not_forall, not_le] at hmem
        obtain ⟨i, hi⟩ := hmem
        apply MvPolynomial.notMem_support_iff.mp
        intro hmo
        rw [hQ] at hmo
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
        have hj' : mo ∈ (P j).support := MvPolynomial.support_smul hj
        exact absurd (le_trans (monomial_le_degreeOf i hj') (hdeg j i)) (by omega)
    by_contra hne
    exact LinearCombination.linearCombination_ne_zero hP hne hQ0
  -- Turn injectivity into an explicit left inverse and transport to matrices.
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hcomp : LinearMap.toMatrix' (g.comp A.mulVecLin) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp]
    congr 1
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [hg, LinearMap.toMatrix'_id] at hcomp
  exact hcomp.symm

/-- Let `C` be a Reed–Solomon code of polynomials of degree less than `k` over an evaluation domain
`D` . Let `G` be a polynomial generator where each `S` is the whole field `F`.
Then, for every `m ≥ 3`, `G` has MCA for with error `∑ i, ε_mca_RS`. Theorem 9.2 [BCGM25]. -/
lemma PolyGen_MCA_RScode (n d m : ℕ) (hm : 3 ≤ m) {ℓ : Type} [Fintype ℓ] {s : ℕ}
    {P : ℓ → MvPolynomial (Fin s) F} (G : Generator ((Fin s) → F) ℓ F)
    (hG : IsPolynomialGeneratorOfFull G P) :
    letI ε := ∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m
    IsMCAGenerator G ε (ReedSolomon.code D k) := by
  classical
  show IsMCAGenerator G (∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m) (ReedSolomon.code D k)
  -- Each individual degree is bounded by the corresponding entry of `deg_max`.
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ deg_max P i := by
    intro j i
    simpa [deg_max] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Fintype.complete j)
  -- The tensor generator of univariate powers has the stated MCA error (using Lemma 9.3).
  have htensor := tensorUniv_MCA k D n m
    (fun e => univarite_powers_MCA k D n e m hm) (deg_max P)
  -- `G` is a left-invertible right multiplication of the tensor generator, inheriting the error.
  have hmul := pseudoinverseGen (tensorUniv (deg_max P))
    (fun γ => ∑ i, ε_mca_RS k D n (deg_max P i) m γ) (ReedSolomon.code D k) htensor
    (coeffMatrix P (deg_max P))
    (coeffMatrix_hasLeftPseudoInverse P (deg_max P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix P (deg_max P) hdeg G hG.2] at hmul
  have herr : (fun γ => ∑ i, ε_mca_RS k D n (deg_max P i) m γ)
      = (∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m) := by
    funext γ; rw [Finset.sum_apply]
  rwa [herr] at hmul

end RSCode
