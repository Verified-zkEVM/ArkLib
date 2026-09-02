/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
import ArkLib.Data.CodingTheory.ProximityGenerator.TensorGenerator

/-!
# Mutual correlated agreement for polynomial generators

A polynomial generator sends a seed `(x₁, …, xₛ)`, drawn from a product of subsets of a field,
to the evaluations of a fixed linearly independent family of multivariate polynomials at that
seed. This file proves that polynomial generators have mutual correlated agreement (MCA), by
factoring each one through an iterated tensor product of univariate powers generators followed
by right multiplication with a coefficient matrix that has a left inverse.

## Main results

- `PolynomialGenIsMCA.powersMCAError`: the MCA error function of a univariate powers generator.
- `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi` and
  `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi_tight`: iterated tensor products of MCA
  generators have MCA with the factors' errors adding; the `tight` variant is proved, from a
  factor hypothesis quantified over module codes of a fixed relative distance.
- `PolynomialGenIsMCA.isMCAGenerator_of_isPolynomialGeneratorOf`: a polynomial generator over
  restricted seed sets has MCA for every linear code. Its only unproved input is
  `isMCAGenerator_of_isMDSGenerator`.
- `RSCode.reedSolomonMCAError`: the MCA error function for Reed-Solomon codes.
- `RSCode.isMCAGenerator_univariatePowersGenerator` (sorried): the univariate powers generator
  has MCA for Reed-Solomon codes up to the Johnson bound.
- `RSCode.isMCAGenerator_of_isPolynomialGeneratorOfFull`: a full-field polynomial generator has
  MCA for Reed-Solomon codes up to the Johnson bound, assuming the previous item and the open
  `isMCAGenerator_tensorGenerator_tight`.

These results formalize §8 and §9 of [BCGM25] (Definitions 8.1 and 9.1, Theorem 8.2, Lemma 9.3,
Theorem 9.2); the per-declaration correspondence is catalogued in
`docs/kb/audits/bcgm25-mca-generators.md`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
  with Mutual Correlated Agreement*][BCGM25]. https://eprint.iacr.org/2025/2051
-/

namespace PolynomialGenIsMCA

open unitInterval NNReal Probability CoreDefinitions LinearTransformations

variable {F : Type} [Field F]
         {ι : Type} [Fintype ι] [Nonempty ι]

/-- A function assigning the maximum degree in the `i`-th variable of the collection of
polynomials `P`. -/
noncomputable def maxDegreeOf {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F) :
    Fin s → ℕ := fun i => Finset.sup Finset.univ (fun j => (P j).degreeOf i)

/-- The MCA error function of the univariate powers generator of degree `d` with `m` seeds,
for a linear code `LC`, at slack parameter `η`. As a function of the proximity parameter `γ` it
is a step function with three regimes: a unique-decoding bound below `δ_C / (d + 2)`, a
list-decoding bound up to `1 - (ρ_C + η) ^ (1 / (d + 2))`, and the trivial bound `1` beyond.

The slack hypothesis `0 < η < 1` is not needed to define the function, so it is omitted here
and required only by the statements that consume it. Valued in `ℝ≥0` to match `IsMCAGenerator`,
clamping the underlying real expression at `0` via `Real.toNNReal`; the clamp is not lossy in
the intended parameter range. -/
noncomputable def powersMCAError [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) :
  I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (LC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_d : ℝ := 1 - (ρ_C + η) ^ (1 / (d + 1) : ℝ)
  fun γ =>
    Real.toNNReal <|
      if γ < (δ_C / (d + 2) : ℝ) then
        letI m' : ℝ := max (n * γ) 1
        m' * (d / m : ℝ)
      else
        if γ ≤ 1 - (ρ_C + η) ^ (1 / (d + 2) : ℝ) then
            (n * γ_d / η) * (d / m) +
            max (2 * d /
                  (η * ((ρ_C + η) ^ (1 / (d + 2) : ℝ) - (ρ_C + η) ^ (1 / (d + 1) : ℝ)) * m))
                ((d + 1) * (d + 2) / (η * m) : ℝ)
        else
        1

/-- The MDS error bound `mdsMCAError` for output size `d + 1` (the univariate powers generator of
degree `d`, whose code has dimension `d + 1`) coincides with the univariate-powers error
`powersMCAError` of degree `d`. -/
lemma mdsMCAError_eq_powersMCAError [DecidableEq F] (LC : LinearCode ι F) (d m : ℕ) (η : ℝ) :
    LinearTransformations.mdsMCAError LC (d + 1) m η = powersMCAError LC d m η := by
  funext γ
  simp only [LinearTransformations.mdsMCAError, powersMCAError, Nat.cast_add, Nat.cast_one]
  rw [show (↑d + 1 + 1 : ℝ) = ↑d + 2 from by ring,
    show (↑d + 1 - 1 : ℝ) = ↑d from by ring]

/-- The iterated tensor product of a finite family of generators `Gᵢ : αᵢ → 𝔽^{ℓᵢ}`, over the
product seed space `∏ᵢ αᵢ`: `(x₁, ..., xₛ) ↦ ⊗ᵢ Gᵢ(xᵢ)`.  Both the full-field tensor
`RSCode.tensorGeneratorPiUnivariate` and the subset tensor `tensorGeneratorPiUnivariateOn` are
instances of this construction. -/
def tensorGeneratorPi {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
    (G : ∀ i, Generator (α i) (ℓ i) F) : Generator (∀ i, α i) (∀ i, ℓ i) F :=
  fun x j => ∏ i, G i (x i) (j i)

omit [Nonempty ι] in
/-- The iterated tensor product of a family of MCA generators has MCA for any module code `MC`,
with error the sum `∑ᵢ εᵢ` of the factors' errors. The inductive step is the open
`isMCAGenerator_tensorGenerator_tight`, which this lemma therefore inherits; see
`isMCAGenerator_tensorGeneratorPi_tight` for the proved variant with a stronger factor
hypothesis.

The seeds and generator entries stay over `F` — it is only the code alphabet that is a general
`F`-module, which is all the induction needs: both `isMCAGenerator_tensorGenerator_tight` and
`isMCAGenerator_reindex` are already stated at that generality. At `A := F` this is the
linear-code statement, since `LinearCode ι F` and `ModuleCode ι F F` are the same type. -/
lemma isMCAGenerator_tensorGeneratorPi {A : Type} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) :
    ∀ {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
      [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, Fintype (ℓ i)]
      (G : ∀ i, Generator (α i) (ℓ i) F) (ε : Fin s → I → ℝ≥0),
      (∀ i, IsMCAGenerator (G i) (ε i) MC) →
      IsMCAGenerator (tensorGeneratorPi G) (fun γ => ∑ i, ε i γ) MC := by
  intro s
  induction s with
  | zero =>
    intro α ℓ _ _ _ G ε _ γ
    classical
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : (∀ i : Fin 0, α i), ¬ IsMCA (tensorGeneratorPi G) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', tensorGeneratorPi G x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [tensorGeneratorPi]
      rwa [hvec] at hmem
    rw [prob_uniform_eq_ofReal, Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  | succ s ih =>
    intro α ℓ _ _ _ G ε hmca
    let : ∀ i : Fin s, Fintype (Fin.tail α i) := fun i => inferInstanceAs (Fintype (α i.succ))
    let : ∀ i : Fin s, Nonempty (Fin.tail α i) := fun i => inferInstanceAs (Nonempty (α i.succ))
    let : ∀ i : Fin s, Fintype (Fin.tail ℓ i) := fun i => inferInstanceAs (Fintype (ℓ i.succ))
    set eS : (∀ i : Fin (s + 1), α i) ≃ (α 0 × (∀ i : Fin s, Fin.tail α i)) :=
      (Fin.consEquiv α).symm with heS
    set eL : (ℓ 0 × (∀ i : Fin s, Fin.tail ℓ i)) ≃ (∀ i : Fin (s + 1), ℓ i) :=
      Fin.consEquiv ℓ with heL
    have hBin := isMCAGenerator_tensorGenerator_tight MC
      (G 0) (ε 0) (hmca 0)
      (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G))
      (fun γ => ∑ i, Fin.tail ε i γ)
      (ih (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G) (Fin.tail ε)
        (fun i => hmca (Fin.succ i)))
    have hR := isMCAGenerator_reindex MC
      (TensorGenerator_Explicit (G 0)
        (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)))
      _ hBin eS eL
    have hgen : (fun (x' : ∀ i : Fin (s + 1), α i) (j' : ∀ i : Fin (s + 1), ℓ i) =>
        TensorGenerator_Explicit (G 0)
          (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)) (eS x') (eL.symm j'))
        = tensorGeneratorPi G := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, tensorGeneratorPi, Fin.tail, Fin.prod_univ_succ]
      simp_all only [eS, eL]
      rfl
    have herr : ((ε 0) + fun γ => ∑ i, Fin.tail ε i γ) = (fun γ => ∑ i, ε i γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ]
      rfl
    rw [hgen, herr] at hR
    exact hR

/-- Proved variant of `isMCAGenerator_tensorGeneratorPi`, with the factor hypothesis anchored on
a relative-distance value `δ₀` and quantified over alphabets: each factor must have MCA, with
its fixed error `ε i`, for *every* module code over `ι` of relative distance `δ₀`.

That hypothesis is closed under the interleavings the induction steps through
(`Code.minRelHammingDistCode_moduleInterleavedCode`), so the inductive step can use the proved
`TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` instead of the open
`isMCAGenerator_tensorGenerator_tight`. The hypothesis is supplied by any generator whose MCA
error reads the code only through its block length and relative distance — in particular by
`isMCAGenerator_of_isMDSGenerator`, whose error `mdsMCAError` does (`mdsMCAError_congr`). -/
lemma isMCAGenerator_tensorGeneratorPi_tight {δ₀ : ℚ≥0} :
    ∀ {s : ℕ} {α : Fin s → Type} {ℓ : Fin s → Type}
      [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, Fintype (ℓ i)] [∀ i, Nonempty (ℓ i)]
      (G : ∀ i, Generator (α i) (ℓ i) F) (ε : Fin s → I → ℝ≥0),
      (∀ i, ∀ {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
        (MC : ModuleCode ι F A), Code.minRelHammingDistCode MC.carrier = δ₀ →
        IsMCAGenerator (G i) (ε i) MC) →
      ∀ {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
        (MC : ModuleCode ι F A), Code.minRelHammingDistCode MC.carrier = δ₀ →
        IsMCAGenerator (tensorGeneratorPi G) (fun γ => ∑ i, ε i γ) MC := by
  intro s
  induction s with
  | zero =>
    intro α ℓ _ _ _ _ G ε _ A _ _ _ MC _ γ
    classical
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : (∀ i : Fin 0, α i), ¬ IsMCA (tensorGeneratorPi G) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', tensorGeneratorPi G x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [tensorGeneratorPi]
      rwa [hvec] at hmem
    rw [prob_uniform_eq_ofReal, Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  | succ s ih =>
    intro α ℓ _ _ _ _ G ε hmca A _ _ _ MC hδ
    let : ∀ i : Fin s, Fintype (Fin.tail α i) := fun i => inferInstanceAs (Fintype (α i.succ))
    let : ∀ i : Fin s, Nonempty (Fin.tail α i) := fun i => inferInstanceAs (Nonempty (α i.succ))
    let : ∀ i : Fin s, Fintype (Fin.tail ℓ i) := fun i => inferInstanceAs (Fintype (ℓ i.succ))
    let : ∀ i : Fin s, Nonempty (Fin.tail ℓ i) := fun i => inferInstanceAs (Nonempty (ℓ i.succ))
    set eS : (∀ i : Fin (s + 1), α i) ≃ (α 0 × (∀ i : Fin s, Fin.tail α i)) :=
      (Fin.consEquiv α).symm with heS
    set eL : (ℓ 0 × (∀ i : Fin s, Fin.tail ℓ i)) ≃ (∀ i : Fin (s + 1), ℓ i) :=
      Fin.consEquiv ℓ with heL
    -- the (ℓ 0)-fold interleaving has the same δᵣ, so the anchored hypotheses apply there
    have hδI : Code.minRelHammingDistCode
        (Code.ModuleCode.moduleInterleavedCode F A (ℓ 0) ι MC).carrier = δ₀ := by
      rw [Code.minRelHammingDistCode_moduleInterleavedCode]; exact hδ
    have hTail := ih (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G) (Fin.tail ε)
      (fun i {A'} _ _ _ MC' hMC' => hmca i.succ MC' hMC')
      (Code.ModuleCode.moduleInterleavedCode F A (ℓ 0) ι MC) hδI
    have hBin := TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode
      (G 0) (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G))
      (ε 0) (fun γ => ∑ i, Fin.tail ε i γ) MC
      (hmca 0 MC hδ) hTail
    have hR := isMCAGenerator_reindex MC
      (TensorGenerator_Explicit (G 0)
        (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)))
      _ hBin eS eL
    have hgen : (fun (x' : ∀ i : Fin (s + 1), α i) (j' : ∀ i : Fin (s + 1), ℓ i) =>
        TensorGenerator_Explicit (G 0)
          (tensorGeneratorPi (α := Fin.tail α) (ℓ := Fin.tail ℓ) (Fin.tail G)) (eS x') (eL.symm j'))
        = tensorGeneratorPi G := by
      funext x' j'
      rw [heS, heL]
      simp only [TensorGenerator_Explicit, tensorGeneratorPi, Fin.tail, Fin.prod_univ_succ]
      simp_all only [eS, eL]
      rfl
    have herr : ((ε 0) + fun γ => ∑ i, Fin.tail ε i γ) = (fun γ => ∑ i, ε i γ) := by
      funext γ
      simp only [Pi.add_apply, Fin.sum_univ_succ]
      rfl
    rw [hgen, herr] at hR
    exact hR

end PolynomialGenIsMCA

namespace RSCode

open unitInterval NNReal CoreDefinitions PolynomialGenIsMCA LinearTransformations MvPolynomial
  Matrix

variable {F : Type} [Field F]
         {ι : Type} [Fintype ι]
         (k : ℕ) -- degree of the polynomials
         (D : ι ↪ F) -- the domain of evaluation


/-- The MCA error function for the Reed-Solomon code of degree `k` over the domain `D`, for the
univariate powers generator of degree `d`, at sharpness parameter `m`: up to the Johnson-type
radius `1 - (1 + 1/(2m))√ρ` the error is `(d n²/|F|) · (m + 1/2)⁷ / (3 ρ^{3/2})`, and beyond it
the trivial bound `1`. Valued in `ℝ≥0`, clamping the underlying real expression at `0` via
`Real.toNNReal`. -/
noncomputable def reedSolomonMCAError [Fintype F] [NeZero k] (d m : ℕ) : I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  let ρ_sqrt := ReedSolomon.sqrtRate k D
  fun γ =>
    Real.toNNReal <|
      if γ ≤ 1 - (1 + (1 / (2 * m : ℝ))) * ρ_sqrt then
        (Fintype.card F : ℝ)⁻¹  *  (m + 1 / 2) ^ 7  * (3 * (ρ_sqrt) ^ 3)⁻¹.toReal * d * n ^ 2
      else
        1

/-- The univariate powers generator of degree `d` has MCA for the Reed-Solomon code of degree
`k` over the domain `D`, with error `reedSolomonMCAError k D d m`, for every `m ≥ 3`.

Sorried: the proof requires the Guruswami-Sudan list-decoding machinery, which is not yet
available in this development. -/
lemma isMCAGenerator_univariatePowersGenerator [Fintype F] [NeZero k] (d m : ℕ) (hm : 3 ≤ m) :
    IsMCAGenerator (univariatePowersGenerator F d) (reedSolomonMCAError k D d m)
      (ReedSolomon.code D k) := by
  sorry

/-- The multi-index (as a finitely supported function) associated to a bounded exponent vector. -/
noncomputable def exponentFinsupp {s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) → Fin (d i + 1)) :
    Fin s →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

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
exponent vector. Together with `exponentFinsupp_injective` this identifies the box index type with
the set of monomials of individual degree at most `d`. -/
lemma exists_exponentFinsupp_eq {s : ℕ} {d : Fin s → ℕ} {mo : Fin s →₀ ℕ} (h : ∀ i, mo i ≤ d i) :
    ∃ e, exponentFinsupp (d := d) e = mo :=
  ⟨fun i => ⟨mo i, Nat.lt_succ_of_le (h i)⟩, by ext i; simp [exponentFinsupp]⟩

/-- The `s`-fold tensor product of univariate powers generators, over the seed space `Fˢ`:
`(x₁, …, xₛ) ↦ ⊗ᵢ (1, xᵢ, …, xᵢ^{dᵢ})`. -/
def tensorGeneratorPiUnivariate {s : ℕ} (d : Fin s → ℕ) :
    Generator (Fin s → F) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, x i ^ (j i : ℕ)

/-- The `s`-fold tensor product of univariate powers generators has MCA for any module code
`MC`, with error the sum `∑ i, ε (d i)` of the factors' errors, provided each univariate powers
generator has MCA for `MC` with error `ε e`. Routed through `isMCAGenerator_tensorGeneratorPi`,
so it inherits the open `isMCAGenerator_tensorGenerator_tight`.

Only the code alphabet is generalised: the generator `x ↦ (1, x, …, x^e)` is still over `F`.
At `A := F` this is the linear-code statement. -/
lemma isMCAGenerator_tensorGeneratorPiUnivariate [Fintype F]
    {A : Type} [AddCommMonoid A] [Module F A] (MC : ModuleCode ι F A)
    (ε : ℕ → I → ℝ≥0)
    (huniv : ∀ e : ℕ, IsMCAGenerator (univariatePowersGenerator F e) (ε e) MC) :
    ∀ {s : ℕ} (d : Fin s → ℕ),
      IsMCAGenerator (tensorGeneratorPiUnivariate d) (fun γ => ∑ i, ε (d i) γ) MC := by
  intro s d
  exact isMCAGenerator_tensorGeneratorPi MC (fun i => univariatePowersGenerator F (d i))
    (fun i => ε (d i)) (fun i => huniv (d i))

/-- The coefficient matrix expressing the polynomial generator `G` as a right multiplication of
the tensor generator of powers: the entry at `(e, j)` is the coefficient of the monomial
`exponentFinsupp e` in the polynomial `P j` (see `generatorByRightMul_coeffMatrix`). -/
noncomputable def coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F)
    (d : Fin s → ℕ) : Matrix ((i : Fin s) → Fin (d i + 1)) ℓ F :=
  fun e j => (P j).coeff (exponentFinsupp e)

/-- A generator that evaluates the polynomials `P` is the right multiplication of the tensor
generator of powers by the coefficient matrix of `P`. -/
lemma generatorByRightMul_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (Fin s → F) ℓ F) (hG : ∀ x, G x = MvPolynomial.eval x ∘ P) :
    generatorByRightMul (tensorGeneratorPiUnivariate d) (coeffMatrix P d) = G := by
  funext x j
  rw [hG]
  simp only [Function.comp_apply, generatorByRightMul, Matrix.vecMul, dotProduct,
    tensorGeneratorPiUnivariate, coeffMatrix]
  have hsub : (P j).support ⊆ Finset.univ.image (exponentFinsupp (d := d)) := by
    intro mo hmo
    obtain ⟨e, he⟩ :=
      exists_exponentFinsupp_eq fun i => le_trans (monomial_le_degreeOf i hmo) (hdeg j i)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩
  rw [eval_eq', Finset.sum_subset hsub
      (fun mo _ hmo => by simp [MvPolynomial.notMem_support_iff.mp hmo]),
    Finset.sum_image (fun a _ b _ h => exponentFinsupp_injective h)]
  exact Finset.sum_congr rfl fun e _ => by simp [mul_comm, exponentFinsupp]

/-- The coefficient matrix of a linearly independent family of polynomials whose individual
degrees are bounded by the box `d` has a left inverse. -/
lemma hasLeftPseudoInverse_coeffMatrix {s : ℕ} {ℓ : Type} [Fintype ℓ] [DecidableEq ℓ]
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

/-- A full-field polynomial generator has MCA for the Reed-Solomon code of degree `k` over the
domain `D`, with error `∑ i, reedSolomonMCAError k D (maxDegreeOf P i) m`, for every `m ≥ 3`.

The proof factors the generator through `tensorGeneratorPiUnivariate` via `coeffMatrix` and
consumes two unproved inputs: `isMCAGenerator_univariatePowersGenerator` for each factor, and —
through `isMCAGenerator_tensorGeneratorPiUnivariate` — the open
`isMCAGenerator_tensorGenerator_tight`. -/
lemma isMCAGenerator_of_isPolynomialGeneratorOfFull [Fintype F] [NeZero k] (m : ℕ) (hm : 3 ≤ m)
    {ℓ : Type} [Fintype ℓ] {s : ℕ} {P : ℓ → MvPolynomial (Fin s) F}
    (G : Generator ((Fin s) → F) ℓ F) (hG : IsPolynomialGeneratorOfFull G P) :
    letI ε := ∑ i : Fin s, reedSolomonMCAError k D (maxDegreeOf P i) m
    IsMCAGenerator G ε (ReedSolomon.code D k) := by
  classical
  show IsMCAGenerator G (∑ i : Fin s, reedSolomonMCAError k D (maxDegreeOf P i) m)
    (ReedSolomon.code D k)
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ maxDegreeOf P i := by
    intro j i
    simpa [maxDegreeOf] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Finset.mem_univ j)
  have htensor := isMCAGenerator_tensorGeneratorPiUnivariate (ReedSolomon.code D k)
    (fun e => reedSolomonMCAError k D e m)
    (fun e => isMCAGenerator_univariatePowersGenerator k D e m hm) (maxDegreeOf P)
  have hmul := pseudoinverseGen (tensorGeneratorPiUnivariate (maxDegreeOf P))
    (fun γ => ∑ i, reedSolomonMCAError k D (maxDegreeOf P i) m γ) (ReedSolomon.code D k) htensor
    (coeffMatrix P (maxDegreeOf P))
    (hasLeftPseudoInverse_coeffMatrix P (maxDegreeOf P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix P (maxDegreeOf P) hdeg G hG.2] at hmul
  rwa [_root_.funext fun γ => (Finset.sum_apply γ Finset.univ _).symm] at hmul

end RSCode

namespace PolynomialGenIsMCA

open CoreDefinitions LinearTransformations LinearCode RSCode ReedSolomon
open unitInterval NNReal Probability

variable {F : Type} [Field F]

/-- The univariate powers generator of degree `d` with its seed space restricted to a subset
`s ⊆ F`: `x ↦ (1, x, …, x^d)`. -/
def univariatePowersGeneratorOn (s : Set F) (d : ℕ) : Generator s (Fin (d + 1)) F :=
  fun x j => (x : F) ^ (j : ℕ)

/-- The code `C_G` of the restricted univariate powers generator is the Reed–Solomon code of
degree less than `d + 1` over `s`: its `M_G` matrix is the non-square Vandermonde matrix. -/
lemma univariatePowersGeneratorOn_code_eq_reedSolomon (s : Set F) [Fintype s] [Nonempty s] (d : ℕ) :
    fromColGenMat (M_G (univariatePowersGeneratorOn s d))
      = ReedSolomon.code (Function.Embedding.subtype (· ∈ s)) (d + 1) := by
  have hMG : M_G (univariatePowersGeneratorOn s d)
      = Vandermonde.nonsquare (d + 1) ((Function.Embedding.subtype (· ∈ s)) : s → F) := by
    ext x j
    simp [M_G, univariatePowersGeneratorOn, Vandermonde.nonsquare]
  rw [hMG, genMatIsVandermonde]

/-- The restricted univariate powers generator is an MDS generator (its code is Reed–Solomon,
hence MDS). Note that this holds for every degree `d`, with no bound relating `d` to `#s`. -/
lemma isMDSGenerator_univariatePowersGeneratorOn [DecidableEq F] (s : Set F) [Fintype s]
    [Inhabited s] (d : ℕ) : IsMDSGenerator (univariatePowersGeneratorOn s d) := by
  unfold IsMDSGenerator
  rw [univariatePowersGeneratorOn_code_eq_reedSolomon]
  exact ReedSolomon.isMDS_code

/-- The restricted univariate powers generator has MCA, with error `powersMCAError LC`, for
every module code over `ι` whose relative distance equals that of `LC` — in particular for `LC`
itself (`MC := LC`, `hδ := rfl`) and for every iterated interleaving of `LC`.

For `d ≥ 1` this is `isMCAGenerator_of_isMDSGenerator` (sorried) together with the
identifications `mdsMCAError_congr` (as `mdsMCAError` reads the code only through `δᵣ`) and
`mdsMCAError_eq_powersMCAError`; for `d = 0` the MCA event is vacuous at any alphabet, so the
error `0 ≤ powersMCAError` suffices. -/
lemma isMCAGenerator_univariatePowersGeneratorOn {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq F]
    (s : Set F) [Fintype s] [Inhabited s]
    (LC : LinearCode ι F) (d : ℕ) (η : ℝ) (hη : 0 < η ∧ η < 1)
    (h : d + 1 ≤ Fintype.card ↥s)
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A] (MC : ModuleCode ι F A)
    (hδ : Code.minRelHammingDistCode MC.carrier = Code.minRelHammingDistCode LC.carrier) :
    IsMCAGenerator (univariatePowersGeneratorOn s d)
      (powersMCAError LC d (Fintype.card ↥s) η) MC := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    classical
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    intro γ
    refine iSup_le fun U => ?_
    have hfalse : ∀ x : ↥s, ¬ IsMCA (univariatePowersGeneratorOn s 0) MC x U (γ : ℝ) := by
      rintro x ⟨T, hT, hmem, j, hj⟩
      apply hj
      have hvec : (fun k => ∑ j', univariatePowersGeneratorOn s 0 x j' • U j' k) = U j := by
        funext w
        rw [Fintype.sum_subsingleton _ j]
        simp [univariatePowersGeneratorOn]
      rwa [hvec] at hmem
    rw [prob_uniform_eq_ofReal, Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  · have hℓ : 2 ≤ Fintype.card (Fin (d + 1)) := by rw [Fintype.card_fin]; omega
    have hdim : LinearCode.dim (fromColGenMat (M_G (univariatePowersGeneratorOn s d)))
        = Fintype.card (Fin (d + 1)) := by
      rw [univariatePowersGeneratorOn_code_eq_reedSolomon, ReedSolomon.dim_eq_deg_of_le h,
        Fintype.card_fin]
    have hmca := isMCAGenerator_of_isMDSGenerator (univariatePowersGeneratorOn s d)
      (isMDSGenerator_univariatePowersGeneratorOn s d) hdim η hη hℓ MC
    rwa [Fintype.card_fin, mdsMCAError_congr LC MC (d + 1) (Fintype.card ↥s) η hδ,
      mdsMCAError_eq_powersMCAError] at hmca

/-- The `s`-fold tensor product of restricted univariate powers generators, over the product seed
space `∏ᵢ Sᵢ`: `(x₁, …, xₛ) ↦ ⊗ᵢ (1, xᵢ, …, xᵢ^{dᵢ})`. -/
def tensorGeneratorPiUnivariateOn {s : ℕ} (S : Fin s → Set F) (d : Fin s → ℕ) :
    Generator (∀ i, (S i)) ((i : Fin s) → Fin (d i + 1)) F :=
  fun x j => ∏ i, ((x i) : F) ^ (j i : ℕ)

/-- The tensor product of the restricted univariate powers generators has MCA for any linear
code `LC`, with error the sum `∑ᵢ powersMCAError LC dᵢ` of the factors' errors. Proved through
`isMCAGenerator_tensorGeneratorPi_tight`: `isMCAGenerator_univariatePowersGeneratorOn` supplies
each factor's MCA at every module code of relative distance `δᵣ LC`, which covers the iterated
interleavings the induction routes through, so the open `isMCAGenerator_tensorGenerator_tight`
is not needed. -/
lemma isMCAGenerator_tensorGeneratorPiUnivariateOn {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq F] (LC : LinearCode ι F) (η : ℝ) (hη : 0 < η ∧ η < 1)
    {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Inhabited ↥(S i)]
    (d : Fin s → ℕ) (hcard : ∀ i, d i + 1 ≤ Fintype.card ↥(S i)) :
    IsMCAGenerator (tensorGeneratorPiUnivariateOn S d)
      (fun γ => ∑ i, powersMCAError LC (d i) (Fintype.card ↥(S i)) η γ) LC :=
  isMCAGenerator_tensorGeneratorPi_tight
    (δ₀ := Code.minRelHammingDistCode LC.carrier)
    (fun i => univariatePowersGeneratorOn (S i) (d i))
    (fun i => powersMCAError LC (d i) (Fintype.card ↥(S i)) η)
    (fun i {_A} _ _ _ MC hMC =>
      isMCAGenerator_univariatePowersGeneratorOn (S i) LC (d i) η hη (hcard i) MC hMC)
    LC rfl

/-- A generator that evaluates the polynomials `P` on restricted seed sets is the right
multiplication of the restricted tensor generator of powers by the coefficient matrix of `P`. -/
lemma generatorByRightMul_coeffMatrix_on {s : ℕ} {ℓ : Type} [Fintype ℓ]
    (S : Fin s → Set F) (P : ℓ → MvPolynomial (Fin s) F) (d : Fin s → ℕ)
    (hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ d i)
    (G : Generator (∀ i, ↥(S i)) ℓ F)
    (hG : ∀ x, G x = MvPolynomial.eval (fun i => (↑(x i) : F)) ∘ P) :
    generatorByRightMul (tensorGeneratorPiUnivariateOn S d) (coeffMatrix P d) = G := by
  funext x
  set xc : Fin s → F := fun i => (↑(x i) : F) with hxc
  have hsub : tensorGeneratorPiUnivariateOn S d x = tensorGeneratorPiUnivariate d xc := by
    funext e; simp [tensorGeneratorPiUnivariateOn, tensorGeneratorPiUnivariate, hxc]
  have hgbm := generatorByRightMul_coeffMatrix P d hdeg
    (fun y => MvPolynomial.eval y ∘ P) (fun _ => rfl)
  calc generatorByRightMul (tensorGeneratorPiUnivariateOn S d) (coeffMatrix P d) x
      = Matrix.vecMul (tensorGeneratorPiUnivariateOn S d x) (coeffMatrix P d) := rfl
    _ = Matrix.vecMul (tensorGeneratorPiUnivariate d xc) (coeffMatrix P d) := by rw [hsub]
    _ = generatorByRightMul (tensorGeneratorPiUnivariate d) (coeffMatrix P d) xc := rfl
    _ = (MvPolynomial.eval xc ∘ P) := congrFun hgbm _
    _ = G x := (hG x).symm

/-- A polynomial generator over restricted seed sets `Sᵢ` with `|Sᵢ| ≥ dᵢ + 1` has MCA for
every linear code `LC`, with error `∑ᵢ powersMCAError LC dᵢ |Sᵢ| η`, for every `0 < η < 1`.

Its only unproved input is `isMCAGenerator_of_isMDSGenerator`: the tensor stage is
`isMCAGenerator_tensorGeneratorPi_tight`, which reaches the unscaled error sum through the
proved interleaved-hypothesis lemma rather than the open
`isMCAGenerator_tensorGenerator_tight`. -/
theorem isMCAGenerator_of_isPolynomialGeneratorOf {ι : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq F] {ℓ : Type} [Fintype ℓ] (LC : LinearCode ι F)
    (η : ℝ) (hη : 0 < η ∧ η < 1)
    {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype (S i)] [∀ i, Inhabited (S i)]
    (G : Generator (∀ i, S i) ℓ F)
    (P : ℓ → MvPolynomial (Fin s) F) (hG : IsPolynomialGeneratorOf S G P)
    (hS : ∀ i : Fin s, (maxDegreeOf P i + 1) ≤ (Set.ncard (S i))) :
    letI ε : I → ℝ≥0 := ∑ i : Fin s, (powersMCAError LC (maxDegreeOf P i) (Set.ncard (S i)) η)
    IsMCAGenerator G ε LC := by
  classical
  show IsMCAGenerator G (∑ i : Fin s, powersMCAError LC (maxDegreeOf P i) (Set.ncard (S i)) η) LC
  have hcard : ∀ i : Fin s, Set.ncard (S i) = Fintype.card (S i) := by
    intro i
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hdeg : ∀ (j : ℓ) (i : Fin s), (P j).degreeOf i ≤ maxDegreeOf P i := by
    intro j i
    simpa [maxDegreeOf] using
      Finset.le_sup (f := fun j => (P j).degreeOf i) (Finset.mem_univ j)
  have hcard_deg : ∀ i : Fin s, maxDegreeOf P i + 1 ≤ Fintype.card (S i) := by
    intro i
    rw [← hcard i]
    exact hS i
  have htensor := isMCAGenerator_tensorGeneratorPiUnivariateOn LC η hη S (maxDegreeOf P) hcard_deg
  have hmul := pseudoinverseGen (tensorGeneratorPiUnivariateOn S (maxDegreeOf P))
    (fun γ => ∑ i, powersMCAError LC (maxDegreeOf P i) (Fintype.card ↥(S i)) η γ) LC htensor
    (coeffMatrix P (maxDegreeOf P))
    (hasLeftPseudoInverse_coeffMatrix P (maxDegreeOf P) hdeg hG.1)
  rw [generatorByRightMul_coeffMatrix_on S P (maxDegreeOf P) hdeg G hG.2] at hmul
  have herr : (∑ i : Fin s, powersMCAError LC (maxDegreeOf P i) (Set.ncard (S i)) η)
      = (fun γ => ∑ i, powersMCAError LC (maxDegreeOf P i) (Fintype.card ↥(S i)) η γ) := by
    funext γ
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcard i])
  rwa [herr]

end PolynomialGenIsMCA
