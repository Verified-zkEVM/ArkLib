/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# Proximity Generators fundamental definitions

Define the fundamental concepts for different types of generators functions used in coding theory.

## Main Definitions

- `generator`: a generator `G` over a field `F` with output size `ℓ` is a function that maps a seed
`x` in a set `S` to a coefficient vector in `F^ℓ`
- `zero-evading generators`: a generator is zero-evading with a zero-evading error `ε_ze` if the
probability of obtaining a zero output from a non-zero vector is bounded above by `ε_ze`
- `polynomial generator`: the output is defined by `ℓ` linearly independent multivariate polynomials
- `MDS generator`: A generator is MDS if the matrix whose rows are the outputs of the generator
function is a generator matrix for an MDS code
- `MCA generator`: A generator has mutual correlated agreement (MCA) with error `ε_mca` if the
probability that the generator satisfies the MCA condition is bounded above by `ε_mca`.
- `tensor product of generators`: given two generators over a field `F` of output sizes `ℓ` and `ℓ'`
respectively, we can define their tensor product componentwise. This is a generator on `F^ℓ ⊗ 𝔽^ℓ'`

## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

section

namespace CoreDefinitions

open NNReal ENNReal unitInterval LinearCode
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ : Type} [Fintype ℓ]

/-- The type of generators, where a generator `G` over a field `F` with output size `ℓ` is a
function that maps a seed `x` in a set `S` to a coefficient vector in `F^ℓ`.
Definition 3.10 [BCGM25]. -/
abbrev Generator (S ℓ F : Type) : Type := S → (ℓ → F)

/-- A generator `G` is zero-evading with a zero-evading error `ε_ze` if the probability of obtaining
a zero output from a non-zero vector is bounded above by `ε_ze`.
Definition 3.11 [BCGM25]. -/
def IsZeroEvadingGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_ze : I) :
  Prop :=
  (sSup {y | ∃ v : ℓ → F, v ≠ 0 ∧ y = Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]})
    ≤ ENNReal.ofReal ε_ze

/-- Let the set `S` be a product of `ℓ` subsets of `F`. A polynomial generator is a generator if
there exist `ℓ` linearly independent multivariate polynomials, such that the output is an evaluation
of the seed at each of these polynomials.
Definition 3.19 [BCGM25]. -/
def IsPolynomialGenerator {s : ℕ} (S : Fin s → Set F) (G : Generator (∀ i, S i) ℓ F) : Prop :=
  ∃ P : ℓ → MvPolynomial (Fin s) F, LinearIndependent F P ∧
  ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ (x i : F)) ∘ P

def IsPolynomialGeneratorOf {s : ℕ} (S : Fin s → Set F) (G : Generator (∀ i, S i) ℓ F)
  (P : ℓ → MvPolynomial (Fin s) F) : Prop :=
  LinearIndependent F P ∧ ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ (x i : F)) ∘ P

/-- A matrix whose rows are the outputs of the generator function.
Defined inside Definition 3.12 [BCGM25]. -/
def M_G {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Matrix S ℓ F :=
  Matrix.of G

noncomputable example {S : Type} [Nonempty S] [Fintype S] [DecidableEq F] (G : Generator S ℓ F) :
  LinearCode S F := LinearCode.fromColGenMat (M_G G)

/-- A generator `G` is MDS if the matrix `M_G` whose rows are the outputs of the generator
function is a generator matrix for an MDS code.
Definition 3.12 [BCGM25]. -/
def IsMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F] (G : Generator S ℓ F) :
  Prop := LinearCode.IsMDS (LinearCode.fromColGenMat (M_G G))

/-- The condition for MCA generator. -/
def IsMCA {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (LC : LinearCode ι F)
  (x : S) (U : ℓ → (ι → F)) (γ : I) : Prop :=
  let v := Matrix.vecMul (G x) (U)
  ∃ (T : Finset ι), (T.card : ℝ) ≥ (Fintype.card ι) * (1 - γ) ∧
  projectedWord v T ∈ projectedCode LC T ∧
  ∃ j : ℓ, projectedWord (U j) T ∉ projectedCode LC T

/-- A generator has mutual correlated agreement (MCA) with error `ε_mca` if the probability that the
generator satisfies the MCA condition is bounded above by `ε_mca`.
Definition 3.14 [BCGM25]. -/
def IsMCAGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I)
  (LC : LinearCode ι F) : Prop :=
  ∀ U : ℓ → (ι → F), ∀ γ : I,
    Pr_{let x ←$ᵖ S}[(IsMCA G LC x U γ)] ≤ ENNReal.ofReal (ε_mca γ)

/-- Let `G : S →F^ℓ` and `G′: S′→F^ℓ` be two generators. Their tensor product is the generator
`G ⊗ G′: S × S′→ F^ℓ ⊗ F^ℓ′` defined by `(x,x′) ↦ G(x) ⊗ G′(x′)`.
Definition 4.3 [BCGM25]. -/
def TensorGenerator {ℓ' : Type} [Fintype ℓ'] {S S' : Type}
  (G : Generator S ℓ F) (G' : Generator S' ℓ' F) :
  (S × S') → TensorProduct F (ℓ → F) (ℓ' → F)
| (x, x') => TensorProduct.tmul F (G x) (G' x')

/-- Explicit construction of the tensor generator. The output type here is a generator
`G ⊗ G′: S × S′→ F^(ℓ * ℓ')`.
Definition 4.3 [BCGM25]. -/
def TensorGenerator_Explicit {ℓ' : Type} [Fintype ℓ'] {S S' : Type}
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F) :
    Generator (S × S') (ℓ × ℓ') F
  | (x, x'), (i, j) => G x i * G' x' j

/-- The canonical linear isomorphism between the tensor product of function spaces
and the function space on the product type. -/
noncomputable def tensorProductPiFunEquiv (F : Type) [Field F] (ℓ ℓ' : Type)
    [Fintype ℓ] [DecidableEq ℓ] [Fintype ℓ'] [DecidableEq ℓ'] :
    TensorProduct F (ℓ → F) (ℓ' → F) ≃ₗ[F] (ℓ × ℓ' → F) :=
  ((Pi.basisFun F ℓ).tensorProduct (Pi.basisFun F ℓ')).equivFun

/-- The tensor product generator `TensorGenerator` and the explicit componentwise generator
`TensorGenerator_Explicit` agree under the canonical isomorphism between
`F^ℓ ⊗ F^ℓ′` and `(ℓ × ℓ') → F`. -/
theorem TensorGenerator_eq_TensorGenerator_Explicit {ℓ' : Type} [Fintype ℓ'] [DecidableEq ℓ]
  [DecidableEq ℓ'] {S S' : Type} (G : Generator S ℓ F) (G' : Generator S' ℓ' F) (p : S × S') :
    tensorProductPiFunEquiv F ℓ ℓ' (TensorGenerator G G' p) = TensorGenerator_Explicit G G' p := by
  unfold tensorProductPiFunEquiv TensorGenerator TensorGenerator_Explicit
  convert (Pi.basisFun F ℓ).tensorProduct (Pi.basisFun F ℓ') |> fun b =>
                                                     b.equivFun_apply ( G p.1 ⊗ₜ[F] G' p.2 ) using 1
  ext ⟨i, j⟩
  simp only [Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_repr, smul_eq_mul]
  ring

end CoreDefinitions

namespace PolynomialGenerator

open NNReal ENNReal unitInterval MvPolynomial LinearCombination CoreDefinitions
open scoped ProbabilityTheory ENNReal NNReal BigOperators

lemma error_in_unit_interval (d : ℕ) (m : ℕ) (hm_pos : 0 < m) (hdm : d ≤ m) : (d / m : ℝ) ∈ I := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg d) (le_of_lt (Nat.cast_pos.mpr hm_pos))
  · have hdm' : (d : ℝ) ≤ m := by exact_mod_cast hdm
    have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm_pos
    exact (div_le_one hm_pos').mpr hdm'

/-- The minimum of the cardinality of a family of sets nonempty sets, indexed by a possibly empty
set. Returns 1 if the indexing set is empty. -/
def minSeedCard {F : Type} {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype ↥(S i)] : ℕ :=
  if h : 0 < s then
    Finset.inf' Finset.univ (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h))
      (fun i => Fintype.card ↥(S i))
  else 1

/-- The minimum of the cardinality of a family of nonempty sets indexed by a posibly empty set is
greater than zero. -/
lemma minSeedCard_pos {F : Type} {s : ℕ} (S : Fin s → Set F)
    [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)] :
    0 < minSeedCard S := by
  unfold minSeedCard
  have hne : ∀ i, (S i).Nonempty := fun i => Set.nonempty_coe_sort.mp inferInstance
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro i _
    exact Fintype.card_pos_iff.mpr (Set.nonempty_coe_sort.2 (hne i))
  · norm_num

/-- The minimum of the cardinality of a family of nonempty sets is smaller than the cardinality of
each set in the family. -/
lemma minSeedCard_le {F : Type} {s : ℕ} (S : Fin s → Set F)
    [∀ i, Fintype ↥(S i)] (hs : 0 < s) (i : Fin s) :
    minSeedCard S ≤ (S i).toFinset.card := by
  unfold minSeedCard
  split_ifs
  aesop

noncomputable local instance {F : Type} [Fintype F] {S : Set F} : Fintype S := Fintype.ofFinite ↑S

/-- If `G` is a polynomial generator, then `G` is zero-evading with error the maximum of the total
degrees of the individual polynomials divided by the size of the smallest evaluation sets `S i`.
Remark 3.20, the version of the statement in the brackets [BCGM25].
Note: Remark 3.20 provides two ways of viewing a polynomial generator as a zero-evading generator.
one in terms of individual degrees, and one in terms of total degrees. We choose the total degree
approach. Ultimately, the reasoning is the same. The difference is the version of Schwartz-Zippel
used to obtain the upper bound. -/
theorem poly_gen_is_zero_evading
  {F : Type} [Field F] [Fintype F]
  {ℓ : Type} [Fintype ℓ]
  {s : ℕ}
  {S : Fin s → Set F} [∀ i, Nonempty ↥(S i)]
  {P : ℓ → MvPolynomial (Fin s) F}
  {G : Generator (∀ i, ↥(S i)) ℓ F} (hG : IsPolynomialGeneratorOf S G P)
  (hdm : MvPolynomial.maxTotalDegree P ≤ minSeedCard S)
  : IsZeroEvadingGenerator G ⟨(maxTotalDegree P : ℝ) / minSeedCard S,
    error_in_unit_interval (maxTotalDegree P) (minSeedCard S) (minSeedCard_pos S) hdm⟩ := by
  classical
  unfold IsZeroEvadingGenerator
  simp only [ne_eq, bind_pure_comp, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index,
    and_imp]
  intros b x hx hb
  rw [hb]
  convert prob_eval_zero_le_div (∑ j, x j • P j) _ (maxTotalDegree P) (minSeedCard S) _ _ _ using 1
  any_goals intro i; exact minSeedCard_le S (Fin.pos_iff_nonempty.mpr ⟨i⟩) i
  any_goals assumption
  · convert rfl
    ext; simp +decide [MvPolynomial.dotProduct_eq_eval_linearCombination, hG.2]
  · rw [ENNReal.ofReal_div_of_pos] <;> norm_cast
    exact minSeedCard_pos S
  · exact LinearCombination.linearCombination_ne_zero hG.1 hx
  · exact MvPolynomial.totalDegree_linearCombination_le _ _ _ fun j =>
                Finset.le_sup (f := fun j => (P j |> MvPolynomial.totalDegree)) (Finset.mem_univ j)
  · exact minSeedCard_pos S

end PolynomialGenerator

end
