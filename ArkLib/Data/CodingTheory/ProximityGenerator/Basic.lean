/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.Data.Probability.Instances

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
probability that the generator satisfies the MCA condition is bounded above by `ε_mca`. Stated
over module codes `ModuleCode ι F A`, matching [BCGM25]'s alphabet generality (Definition 3.2).
`mcaError` is the worst-case error *value* and is the primitive; `IsMCAGenerator` is defined as a
bound on it, so `isMCAGenerator_iff_mcaError_le` is `Iff.rfl` rather than a bridge between two
parallel definitions.
- `tensor product of generators`: given two generators over a field `F` of output sizes `ℓ` and `ℓ'`
respectively, we can define their tensor product componentwise. This is a generator on `F^ℓ ⊗ 𝔽^ℓ'`
- `affine line generator`: A generator of the form `G : F → F²` such that `x ↦ (1,x)`.
- `affine space generator`: A generator of the form `G : F^ℓ → F^(ℓ + 1)` such that
 `x ↦ (1,x)`.

The correspondence to [BCGM25]'s numbered statements is in
`docs/kb/audits/bcgm25-mca-generators.md`.

## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

section

namespace CoreDefinitions

open NNReal ENNReal unitInterval LinearCode
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ : Type} [Fintype ℓ]

/-- The type of generators, where a generator `G` over a field `F` with output size `ℓ` is a
function that maps a seed `x` in a set `S` to a coefficient vector in `F^ℓ`. -/
abbrev Generator (S ℓ F : Type) : Type := S → (ℓ → F)

/-- A generator `G` is zero-evading with a zero-evading error `ε_ze` if the probability of obtaining
a zero output from a non-zero vector is bounded above by `ε_ze`. -/
def IsZeroEvadingGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_ze : I) :
    Prop :=
  (sSup {y | ∃ v : ℓ → F, v ≠ 0 ∧ y = Pr_{let x ←$ᵖ S}[dotProduct (G x) v = 0]})
    ≤ ENNReal.ofReal ε_ze

/-- Let the set `S` be a product of `s` subsets of `F`. A polynomial generator is a generator if
there exist `ℓ` linearly independent multivariate polynomials, such that the output is an evaluation
of the seed at each of these polynomials. -/
def IsPolynomialGenerator {s : ℕ} (S : Fin s → Set F) (G : Generator (∀ i, S i) ℓ F) : Prop :=
  ∃ P : ℓ → MvPolynomial (Fin s) F, LinearIndependent F P ∧
  ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ (x i : F)) ∘ P

/-- The generator `G` evaluates the given linearly independent family of polynomials `P`:
the witness-carrying form of `IsPolynomialGenerator`. -/
def IsPolynomialGeneratorOf {s : ℕ} (S : Fin s → Set F) (G : Generator (∀ i, S i) ℓ F)
    (P : ℓ → MvPolynomial (Fin s) F) : Prop :=
  LinearIndependent F P ∧ ∀ x : (∀ i, S i), G x = MvPolynomial.eval (fun i ↦ (x i : F)) ∘ P

/-- A polynomial generator where each `S i` is the whole field `F`. -/
def IsPolynomialGeneratorOfFull {s : ℕ} (G : Generator (Fin s → F) ℓ F)
    (P : ℓ → MvPolynomial (Fin s) F) : Prop :=
  LinearIndependent F P ∧ ∀ x : Fin s → F, G x = MvPolynomial.eval x ∘ P

/-- The matrix whose rows are the outputs of the generator function. -/
def M_G {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) : Matrix S ℓ F :=
  Matrix.of G

noncomputable example {S : Type} [Nonempty S] [Fintype S] [DecidableEq F] (G : Generator S ℓ F) :
  LinearCode S F := LinearCode.fromColGenMat (M_G G)

/-- A generator `G` is MDS if the matrix `M_G` whose rows are the outputs of the generator
function is a generator matrix for an MDS code. -/
def IsMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F] (G : Generator S ℓ F) :
    Prop := LinearCode.IsMDS (LinearCode.fromColGenMat (M_G G))

/-- The condition for MCA generator.

Stated over a module code `MC : ModuleCode ι F A`, so the alphabet may be any `F`-module: the
combination
`∑ j, G x j • U j` replaces `Matrix.vecMul (G x) U`, which requires a ring structure on the
alphabet. At `A := F` the two agree — see `vecMul_eq_smul_sum`.

The radius is `δ : ℝ`, not `I`, for the same reason `Code.Lambda`'s is: it is an *argument to a
value*, and narrowing it only relocates a membership obligation to every call site. The size
clause is total and honest at every real — no `T` can meet `|T| ≥ n·(1 - δ)` when `δ < 0`, and
the clause is vacuous once `δ ≥ 1` — so nothing outside `[0,1]` is asserted that is not already
asserted at the endpoints. The `[0,1]` typing lives on the *error bound*: `IsMCAGenerator`
quantifies `δ : I`. See
`docs/wiki/proximity-error-conventions.md`. -/
def IsMCA {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A)
  (x : S) (U : ℓ → (ι → A)) (δ : ℝ) : Prop :=
  let v : ι → A := fun k => ∑ j, G x j • U j k
  ∃ (T : Finset ι), (T.card : ℝ) ≥ (Fintype.card ι) * (1 - δ) ∧
  projectedWord v T ∈ projectedCodeSubmod MC T ∧
  ∃ j : ℓ, projectedWord (U j) T ∉ projectedCodeSubmod MC T

omit [Fintype ι] in
/-- Over the alphabet `A := F`, the linear combination in `IsMCA` is the matrix-vector
product used by the original `F`-alphabet definition. -/
lemma vecMul_eq_smul_sum {S : Type} (G : Generator S ℓ F) (x : S) (U : ℓ → (ι → F)) :
    Matrix.vecMul (G x) (Matrix.of U) = fun k => ∑ j, G x j • U j k := by
  funext k
  simp [Matrix.vecMul, dotProduct, smul_eq_mul]

/-- At the field alphabet `A := F`, where `ModuleCode ι F F` and `LinearCode ι F` are the same
type, `IsMCA` is the `Matrix.vecMul`-shaped predicate: the linear combination `∑ j, G x j • U j`
is the matrix-vector product `G x ᵥ* U`.

The proof is `Iff.rfl`, so the two agree definitionally and not merely propositionally. Any edit
that weakens that breaks this declaration rather than silently changing what every field-alphabet
consumer means. -/
theorem isMCA_iff_vecMul {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (LC : LinearCode ι F) (x : S) (U : ℓ → (ι → F)) (δ : ℝ) :
    IsMCA G LC x U δ ↔
      ∃ T : Finset ι, (T.card : ℝ) ≥ (Fintype.card ι) * (1 - δ) ∧
        projectedWord (Matrix.vecMul (G x) (Matrix.of U)) T ∈ projectedCodeSubmod LC T ∧
        ∃ j : ℓ, projectedWord (U j) T ∉ projectedCodeSubmod LC T :=
  Iff.rfl

/-- The mutual correlated agreement error of a generator for a module code: the worst-case,
over families `U`, probability of the MCA event.

This is the primitive of the layer: `IsMCAGenerator` is defined as a bound on it, and the generator
transport lemmas are stated on it directly, so they mention no error function at all. A value can
be *assigned* to a code family rather than merely bounded, which is what a claim about a specific
code needs.

The supremum is over `ℓ → (ι → A)`, which is inhabited whenever `A` is — and `A` carries `Zero`
— so this is never a degenerate `⨆` over an empty family.

The radius is `ℝ`, matching `Code.Lambda`; see `IsMCA`. -/
noncomputable def mcaError {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A]
    [Module F A] (G : Generator S ℓ F) (MC : ModuleCode ι F A) : ℝ → ENNReal :=
  fun δ => ⨆ U : ℓ → (ι → A), Pr_{let x ←$ᵖ S}[IsMCA G MC x U δ]

/-- A generator has mutual correlated agreement (MCA) with error `ε_mca` if the probability that
the generator satisfies the MCA condition is bounded above by `ε_mca`.

The body is the `mcaError` bound, so `isMCAGenerator_iff_mcaError_le` is `Iff.rfl`: `exact`,
`refine` and `apply` see through to the value inequality, and only `rw`/`simp` need the bridge.
The pointwise reading — the bound at one individual family `U` — is `IsMCAGenerator.prob_le`.

The radius is quantified over `I`, the closed unit interval: this is the bound, and the bound is
where `[0,1]` belongs, while the value underneath is total in the radius. See
`docs/wiki/proximity-error-conventions.md`. -/
def IsMCAGenerator {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (ε_mca : I → ℝ≥0) (MC : ModuleCode ι F A) : Prop :=
  ∀ δ : I, mcaError G MC (δ : ℝ) ≤ (ε_mca δ : ENNReal)

/-- **Unfolding lemma for `IsMCAGenerator`.** It *is* the `mcaError` bound, by definition; this is
the entry point for `rw` and `simp only`, which do not see through a semireducible `def`. -/
lemma isMCAGenerator_iff_mcaError_le {S : Type} [Nonempty S] [Fintype S] {A : Type}
    [AddCommMonoid A] [Module F A] (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
    (MC : ModuleCode ι F A) :
    IsMCAGenerator G ε_mca MC ↔ ∀ δ : I, mcaError G MC (δ : ℝ) ≤ (ε_mca δ : ENNReal) := Iff.rfl

/-- The pointwise reading: an MCA bound holds at each individual family `U`, not merely at the
supremum. This is the form every consumer of an `IsMCAGenerator` hypothesis wants, and the reason
quantifying over `U` inside the definition costs nothing after it is stated at the value. -/
lemma IsMCAGenerator.prob_le {S : Type} [Nonempty S] [Fintype S] {A : Type}
    [AddCommMonoid A] [Module F A] {G : Generator S ℓ F} {ε_mca : I → ℝ≥0}
    {MC : ModuleCode ι F A} (h : IsMCAGenerator G ε_mca MC) (U : ℓ → (ι → A)) (δ : I) :
    Pr_{let x ←$ᵖ S}[IsMCA G MC x U (δ : ℝ)] ≤ (ε_mca δ : ENNReal) :=
  le_trans (le_iSup (fun U => Pr_{let x ←$ᵖ S}[IsMCA G MC x U (δ : ℝ)]) U) (h δ)

/-- The MCA error is a probability: it never exceeds `1`, and in particular is never `⊤`.

Needed wherever the value has to cross back into `ℝ≥0` — e.g. to compare a `mcaError` against an
`I → ℝ≥0` bound in the other direction, or to do `ENNReal` arithmetic that is only valid away
from `⊤`. -/
lemma mcaError_le_one {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A]
    [Module F A] (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ) :
    mcaError G MC δ ≤ 1 :=
  iSup_le fun _ => PMF.coe_le_one _ True

lemma mcaError_ne_top {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A]
    [Module F A] (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ) :
    mcaError G MC δ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (mcaError_le_one G MC δ)

/-- The MCA error is monotone in the distance: enlarging `δ` weakens the size clause
`|T| ≥ n·(1 - δ)`, so more witness sets qualify and the bad event can only grow.

Monotonicity is specific to this notion: it holds because the event carries no
distance-*anti*monotone conjunct. Errors whose event carries a guard do, and are not monotone —
see `docs/wiki/proximity-error-conventions.md`. -/
lemma mcaError_mono {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A]
    [Module F A] (G : Generator S ℓ F) (MC : ModuleCode ι F A) {δ δ' : ℝ} (h : δ ≤ δ') :
    mcaError G MC δ ≤ mcaError G MC δ' := by
  refine iSup_mono fun U => Probability.Pr_le_Pr_of_implies _ _ _ fun x hx => ?_
  obtain ⟨T, hT, hmem, hbad⟩ := hx
  exact ⟨T, le_trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) hT,
    hmem, hbad⟩

/-- The size clause `|T| ≥ n·(1 - δ)` is an *integer* condition on the complement: it says the
`n - |T|` positions outside `T` number at most `⌊δ·n⌋`. Hence `δ` enters only through that
floor. -/
lemma mul_one_sub_le_card_iff_sub_card_le_floor (T : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ) :
    (T.card : ℝ) ≥ (Fintype.card ι) * (1 - δ) ↔
      Fintype.card ι - T.card ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
  have hTn : T.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ T
  rw [Nat.le_floor_iff (by positivity), Nat.cast_sub hTn]
  constructor <;> intro hh <;> nlinarith [hh]

/-- **`mcaError` is a step function on the `1/n` grid.** Two radii with the same `⌊δ·n⌋` give the
same error, because the size clause only ever compares `n - |T|` against that floor.

So a challenge radius is really an integer grid index: a claim stated at an arbitrary real `δ` is
either unattained or ambiguous, whereas one stated at `k/n` is neither. -/
lemma mcaError_eq_of_floor_eq {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A]
    [Module F A] (G : Generator S ℓ F) (MC : ModuleCode ι F A) {δ δ' : ℝ}
    (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (h : ⌊δ * (Fintype.card ι : ℝ)⌋₊ = ⌊δ' * (Fintype.card ι : ℝ)⌋₊) :
    mcaError G MC δ = mcaError G MC δ' := by
  refine iSup_congr fun U => Probability.Pr_congr fun x => ?_
  refine exists_congr fun T => and_congr_left fun _ => ?_
  rw [mul_one_sub_le_card_iff_sub_card_le_floor T hδ,
    mul_one_sub_le_card_iff_sub_card_le_floor T hδ', h]

/-- Let `G : S → F^ℓ` and `G′: S′ → F^ℓ` be two generators. Their tensor product is the generator
`G ⊗ G′: S × S′→ F^ℓ ⊗ F^ℓ′` defined by `(x , x′) ↦ G(x) ⊗ G′(x′)`. -/
def TensorGenerator {ℓ' : Type} [Fintype ℓ'] {S S' : Type}
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F) :
  (S × S') → TensorProduct F (ℓ → F) (ℓ' → F)
| (x, x') => TensorProduct.tmul F (G x) (G' x')

/-- Explicit construction of the tensor generator. The output type here is a generator
`G ⊗ G′: S × S′→ F^(ℓ * ℓ')`. -/
def TensorGenerator_Explicit {ℓ' : Type} [Fintype ℓ'] {S S' : Type}
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F) :
    Generator (S × S') (ℓ × ℓ') F
  | (x, x'), (i, j) => G x i * G' x' j

omit [Fintype ι] in
/-- The tensor generator combination of a family `U : ℓ × ℓ' → (ι → F)` factors: it is the
`G x`-combination of the rows `i ↦ Matrix.vecMul (G' x') (U (i, ·))`, each of which is the
`G' x'`-combination of the `i`-th row of `U`. -/
lemma vecMul_tensorGenerator_explicit {ℓ' : Type} [Fintype ℓ'] {S S' : Type}
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F) (U : ℓ × ℓ' → (ι → F)) (x : S) (x' : S') :
    Matrix.vecMul (TensorGenerator_Explicit G G' (x, x')) U
      = Matrix.vecMul (G x) (fun i => Matrix.vecMul (G' x') (fun j => U (i, j))) := by
  funext k
  simp [Matrix.vecMul, dotProduct, TensorGenerator_Explicit, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

/-- The canonical linear isomorphism between the tensor product of function spaces
and the function space on the product type. -/
noncomputable def tensorProductPiFunEquiv (F : Type) [Field F] (ℓ ℓ' : Type)
    [Fintype ℓ] [DecidableEq ℓ] [Fintype ℓ'] [DecidableEq ℓ'] :
    TensorProduct F (ℓ → F) (ℓ' → F) ≃ₗ[F] (ℓ × ℓ' → F) :=
  ((Pi.basisFun F ℓ).tensorProduct (Pi.basisFun F ℓ')).equivFun

/-- The tensor product generator `TensorGenerator` and the explicit componentwise generator
`TensorGenerator_Explicit` agree under the canonical isomorphism between `F^ℓ ⊗ F^ℓ′` and
`(ℓ × ℓ') → F`. -/
theorem TensorGenerator_eq_TensorGenerator_Explicit {ℓ' : Type} [Fintype ℓ'] [DecidableEq ℓ]
    [DecidableEq ℓ'] {S S' : Type} (G : Generator S ℓ F) (G' : Generator S' ℓ' F) (p : S × S') :
    tensorProductPiFunEquiv F ℓ ℓ' (TensorGenerator G G' p) = TensorGenerator_Explicit G G' p := by
  unfold tensorProductPiFunEquiv TensorGenerator TensorGenerator_Explicit
  convert (Pi.basisFun F ℓ).tensorProduct (Pi.basisFun F ℓ') |> fun b =>
                                                     b.equivFun_apply (G p.1 ⊗ₜ[F] G' p.2) using 1
  ext ⟨i, j⟩
  simp only [Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_repr, smul_eq_mul]
  ring

/-- Let `F` be a field.
The affine line generator is a generator of the form `G : F → F²` such that `x ↦ (1,x)`. -/
abbrev AffineLineGenerator (F : Type) [Field F] : Generator F (Fin 2) F :=
  fun x => ![1, x]

/-- Let `F` be a field.
The affine space generator is a generator of the form `G : F^ℓ → F^(ℓ + 1) ` such that
`x ↦ (1,x)`. -/
abbrev AffineSpaceGenerator (F : Type) [Field F] (ℓ : ℕ) : Generator (Fin ℓ → F) (Fin (ℓ + 1)) F :=
  fun x => Fin.cons 1 x

/-- The univariate-powers generator `x ↦ (1, x, …, x^k)`. -/
abbrev univariatePowersGenerator (F : Type) [Field F] (k : ℕ) :
    Generator F (Fin (k + 1)) F :=
  fun x i => x ^ (i : ℕ)

end CoreDefinitions

namespace PolynomialGenerator

open NNReal ENNReal unitInterval MvPolynomial LinearCombination CoreDefinitions
open scoped ProbabilityTheory ENNReal NNReal BigOperators

/-- Auxiliary lemma to prove that an error is in the unit interval. -/
lemma error_in_unit_interval (d : ℕ) (m : ℕ) (hm_pos : 0 < m) (hdm : d ≤ m) : (d / m : ℝ) ∈ I := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg d) (le_of_lt (Nat.cast_pos.mpr hm_pos))
  · have hdm' : (d : ℝ) ≤ m := by exact_mod_cast hdm
    have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm_pos
    exact (div_le_one hm_pos').mpr hdm'

/-- The minimum of the cardinality of a family of nonempty sets, indexed by a possibly empty set.
Returns `1` if the indexing set is empty. -/
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

This is the total-degree reading. An individual-degree reading of the same fact is also available;
the reasoning is the same and only the version of Schwartz–Zippel used for the upper bound
differs. -/
theorem poly_gen_is_zero_evading
    {F : Type} [Field F] [Fintype F]
  {ℓ : Type} [Fintype ℓ]
  {s : ℕ}
  {S : Fin s → Set F} [∀ i, Nonempty ↥(S i)]
  {P : ℓ → MvPolynomial (Fin s) F}
  {G : Generator (∀ i, ↥(S i)) ℓ F} (hG : IsPolynomialGeneratorOf S G P)
  (hdm : MvPolynomial.maxTotalDegree P ≤ minSeedCard S) :
    IsZeroEvadingGenerator G ⟨(maxTotalDegree P : ℝ) / minSeedCard S,
    error_in_unit_interval (maxTotalDegree P) (minSeedCard S) (minSeedCard_pos S) hdm⟩ := by
  classical
  unfold IsZeroEvadingGenerator
  simp only [ne_eq, bind_pure_comp, sSup_le_iff, Set.mem_ofPred_eq, forall_exists_index,
    and_imp]
  intros b x hx hb
  rw [hb]
  change ((fun a => G a ⬝ᵥ x = 0) <$> $ᵖ ((i : Fin s) → ↥(S i))) True ≤ _
  rw [show (fun a => G a ⬝ᵥ x = 0) = fun a =>
      MvPolynomial.eval (fun i => (a i : F)) (∑ j, x j • P j) = 0 by
    funext a
    simp +decide [MvPolynomial.dotProduct_eq_eval_linearCombination, hG.2]]
  refine (prob_eval_zero_le_div (∑ j, x j • P j)
    (LinearCombination.linearCombination_ne_zero hG.1 hx)
    (maxTotalDegree P) (minSeedCard S)
    (MvPolynomial.totalDegree_linearCombination_le _ _ _ fun j =>
      Finset.le_sup (f := fun j => (P j |> MvPolynomial.totalDegree)) (Finset.mem_univ j))
    (minSeedCard_pos S)
    (fun i => minSeedCard_le S (Fin.pos_iff_nonempty.mpr ⟨i⟩) i)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos] <;> norm_cast
  exact minSeedCard_pos S

end PolynomialGenerator

end
