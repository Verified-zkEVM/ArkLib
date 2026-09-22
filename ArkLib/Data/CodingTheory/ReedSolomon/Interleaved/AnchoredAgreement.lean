/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PointCollisionProbability
public import ArkLib.Data.Probability.Uniform
public import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement

/-!
# Anchored agreement for interleaved Reed–Solomon codes

Fix a received array `received : ι → κ → F` on an evaluation domain `domain : ι ↪ F`. The
*candidate set* `candidateSet domain received K a` contains every tuple `Q : κ → F[X]` of
polynomials of degree below `K` whose evaluation `evalTuple domain Q` agrees with `received` in
at least `a` columns. For `K ≤ |ι|` evaluation is injective on these tuples, so the candidate set
is bounded by the list size `Lambda` of the interleaved code `code domain K ^⋈ κ` at relative
radius `1 - a / |ι|`.

Anchors `x : ι' → F`, sampled before any later data, *separate* the candidate set when
`evalTuple x` is injective on it. By `Polynomial.prob_not_injOn_evalTuple_le_of_encard_le`,
anchors sampled through an injective map from a finite type `Ω` fail to separate with probability
at most `choose L 2 * (K - 1) ^ |ι'| / |Ω|`. For two ordered distinct anchors outside the domain,
`|Ω| = (|F| - |ι|) (|F| - |ι| - 1)`.

When the anchors separate the candidate set, for every array `c` of claimed anchor values there
is an option, fixed before any later data, that is `some Q` exactly for the candidate with anchor
values `c`. A later reconstruction `D * q + I` from a divisor `D` vanishing at the anchors, a
quotient `q` whose quotient equation agrees with the residual `received - I` in at least `a`
columns, and an interpolant `I` with anchor values `c` is a candidate with anchor values `c`, so
it equals the selected option. For the cubic divisor `(X - s₁) (X - s₂) (X - z)` this holds for
every later point `z`.

## Main definitions

* `ReedSolomon.AnchoredAgreement.candidateSet`: the degree-bounded tuples with at least `a`
  simultaneous agreements.

## Main statements

* `ReedSolomon.AnchoredAgreement.injOn_evalTuple_of_degree_lt`: evaluation on the domain is
  injective on tuples of degree below `K ≤ |ι|`.
* `ReedSolomon.AnchoredAgreement.encard_candidateSet_le_Lambda` and
  `ReedSolomon.AnchoredAgreement.finite_candidateSet_of_Lambda_le`: the candidate set is bounded
  by `Lambda` at radius `1 - a / |ι|`.
* `ReedSolomon.AnchoredAgreement.prob_not_injOn_candidateSet_le` and
  `ReedSolomon.AnchoredAgreement.prob_not_injOn_candidateSet_offDiag_le`: the anchors fail to
  separate the candidate set with small probability.
* `ReedSolomon.AnchoredAgreement.agree_evalTuple_mul_add` and
  `ReedSolomon.AnchoredAgreement.mul_add_mem_candidateSet`: agreement of a quotient equation is
  agreement of the reconstruction.
* `ReedSolomon.AnchoredAgreement.exists_selected_before_reconstruction`: separating anchors fix
  every later reconstruction in advance, for any divisor vanishing at the anchors.
* `ReedSolomon.AnchoredAgreement.exists_selectedCandidate_before_later`: the cubic-divisor form.

## References

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AnchoredAgreement.lean`:

* `tupleEvaluation` is `Polynomial.evalTuple domain`, with `Fin n` and `Fin width` generalized to
  finite types `ι` and `κ`. `tuple_eq_of_evaluation_eq` and `candidateSet_injective` are
  `injOn_evalTuple_of_degree_lt`, without the source's `0 < k`.
* `CandidateSet domain received T A` is `candidateSet domain received (T + 3) A`: the degree
  bound `K` is a parameter instead of `T + 3`.
* `candidateSet_finite`, `candidateFamily`, `mem_candidateFamily` and `candidateFamily_card_le`
  are replaced by `encard_candidateSet_le_Lambda` and `finite_candidateSet_of_Lambda_le`, which
  bound the set itself instead of a `Finset` built from a finiteness proof. The source's radius
  `capacityRadius delta n (T + 3)` with the threshold `agreementThreshold delta n (T + 3) ≤ A`
  is replaced by the radius `1 - A / n`, which is at most the source radius under that
  threshold; the conversion is `Code.encard_setOf_le_agree_encode_le_Lambda`. The hypotheses
  `0 ≤ delta` and `0 < n` are not needed.
* `badAnchorPairs`, `badAnchorRate`, `badAnchorRate_eq`,
  `not_mem_collisionSet_of_sampled_of_not_mem_badAnchorPairs`, `badAnchorRate_le` and
  `candidateFamily_badAnchorRate_le` are replaced by the event
  `¬ Set.InjOn (evalTuple ![s₁, s₂]) (candidateSet …)` and its probability bounds
  `prob_not_injOn_candidateSet_le` (any finite sample space of anchor tuples) and
  `prob_not_injOn_candidateSet_offDiag_le` (the source's space of ordered distinct pairs outside
  the domain, with the source's denominator). The source's rate
  `choose L 2 * ((T + 2) / (q - n - 1)) ^ 2` is at least the bound here,
  `choose L 2 * (T + 2) ^ 2 / ((q - n) (q - n - 1))`; the test file derives the source form.
  `natDegree_le_add_two_of_degree_lt_add_three` is the step `degree < K → natDegree ≤ K - 1`
  inside `prob_not_injOn_candidateSet_le`.
* `twoAnchorValues` is `evalTuple ![s₁, s₂]`, and `twoAnchorValues_injOn_of_good` and
  `eq_of_claimed_twoAnchorValues_of_good` are the separation event itself.
* `cubicQuotientWord`, `cubicResidualWord` and `cubicReconstructedTuple_agreement` are
  generalized to any divisor `D` in `agree_evalTuple_mul_add`, which is an equality.
  `cubicReconstructedTuple` is `fun j ↦ cubicAnchorReconstruct s₁ s₂ z (q j) (I j)`.
* `LaterCubicReconstruction`, `SuccessfulCubicReconstruction` and
  `successfulCubicReconstruction_mem_and_values` are replaced by the unbundled hypotheses of
  `exists_selected_before_reconstruction` and `exists_selectedCandidate_before_later`. The
  source's conditions `s₁ ≠ s₂`, `z ≠ s₁`, `z ≠ s₂`, the claimed value at `z`, and `0 < T` are
  not used by the conclusion and are dropped.
* `exists_selectedCandidate_before_later` is ported with the separation event as hypothesis in
  place of the sampled-pair and bad-set hypotheses, and with an `↔` characterization of the
  selected option. Its list-size and threshold hypotheses are not needed, since separation is a
  hypothesis.
* `traceRemainderTuple`, `traceRemainderTuple_degree_lt`, `traceRemainderTuple_eval_eq` and
  `exists_selectedTrace_before_later` are not ported as declarations: the remainder of a tuple is
  `fun j ↦ Q j %ₘ (X ^ T - C 1)`, its properties are `ReedSolomon.traceRemainder_degree_lt` and
  `ReedSolomon.traceRemainder_eval_eq` in each coordinate, and the trace statement is
  `Option.map` applied to `exists_selectedCandidate_before_later`, as the test file shows.

The source file `ArkLib/Data/Probability/TwoPointPolynomialCollision.lean` is covered by
`ArkLib.Data.Polynomial.PointCollision`.

Deferred: the application-level statements of the source's consumers, which combine these
results with a concrete list-size bound for `Lambda`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.AnchoredAgreement

open Polynomial Code
open scoped ProbabilityTheory

section Field

variable {F ι κ : Type*} [Field F] [DecidableEq F] [Fintype ι] [Fintype κ]

/-- **Candidate tuples.** The tuples `Q : κ → F[X]` whose coordinates have degree below `K` and
whose evaluations on the domain agree with the received array `received` in at least `a`
columns. A column `i` agrees when `(Q j).eval (domain i) = received i j` for every `j`. -/
def candidateSet (domain : ι ↪ F) (received : ι → κ → F) (K a : ℕ) : Set (κ → F[X]) :=
  {Q | (∀ j, (Q j).degree < K) ∧ a ≤ agree (evalTuple domain Q) received}

@[simp] theorem mem_candidateSet {domain : ι ↪ F} {received : ι → κ → F} {K a : ℕ}
    {Q : κ → F[X]} :
    Q ∈ candidateSet domain received K a ↔
      (∀ j, (Q j).degree < K) ∧ a ≤ agree (evalTuple domain Q) received := Iff.rfl

omit [DecidableEq F] [Fintype ι] [Fintype κ] in
/-- **Evaluations of degree-bounded tuples are interleaved codewords.** If every coordinate of `Q`
has degree below `K`, the evaluation of `Q` on the domain lies in `code domain K ^⋈ κ`. -/
theorem evalTuple_mem_interleavedCodeSet (domain : ι ↪ F) {K : ℕ} {Q : κ → F[X]}
    (hQ : ∀ j, (Q j).degree < K) :
    evalTuple domain Q ∈ interleavedCodeSet (κ := κ) (code domain K : Set (ι → F)) :=
  fun j ↦ evalOnPoints_mem_code_of_degree_lt (hQ j)

omit [DecidableEq F] [Fintype κ] in
/-- **Evaluation is injective on degree-bounded tuples.** For `K ≤ |ι|`, two tuples whose
coordinates have degree below `K` and which agree at every domain point are equal.

`K ≤ |ι|` is needed: for `ι = Unit`, `K = 2` and the domain point `0`, the polynomials `X` and `0`
have degree below `2` and the same value at `0`. -/
theorem injOn_evalTuple_of_degree_lt (domain : ι ↪ F) {K : ℕ} (hK : K ≤ Fintype.card ι) :
    Set.InjOn (evalTuple (domain : ι → F)) {Q : κ → F[X] | ∀ j, (Q j).degree < K} := by
  classical
  intro P hP Q hQ h
  have hK' : (K : WithBot ℕ) ≤ (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ]
    exact_mod_cast hK
  funext j
  refine eq_of_degrees_lt_of_eval_index_eq Finset.univ domain.injective.injOn
    ((hP j).trans_le hK') ((hQ j).trans_le hK') fun i _ ↦ ?_
  exact congrFun (congrFun h i) j

/-- The number of agreeing columns of an evaluated tuple is the size of
`interleavedPolynomialAgreementSet`, the agreement set used for interleaved power agreement. -/
theorem card_interleavedPolynomialAgreementSet (domain : ι ↪ F)
    (received : ι → κ → F) (Q : κ → F[X]) :
    (interleavedPolynomialAgreementSet domain received Q).card =
      agree (evalTuple domain Q) received := by
  unfold agree interleavedPolynomialAgreementSet
  congr 1
  ext i
  simp [funext_iff]

/-- **The candidate set is bounded by `Lambda`.** For `K ≤ |ι|`, the candidate set at degree
bound `K` and agreement `a` has at most `Lambda (code domain K ^⋈ κ) (1 - a / |ι|)` elements.

`K ≤ |ι|` is needed, as in `injOn_evalTuple_of_degree_lt`: for `K > |ι|` distinct candidates can
have the same evaluation and are counted once by `Lambda`. -/
theorem encard_candidateSet_le_Lambda (domain : ι ↪ F) (received : ι → κ → F) {K : ℕ}
    (hK : K ≤ Fintype.card ι) (a : ℕ) :
    (candidateSet domain received K a).encard ≤
      Lambda (interleavedCodeSet (κ := κ) (code domain K : Set (ι → F)))
        (1 - (a : ℝ) / Fintype.card ι) :=
  encard_setOf_le_agree_encode_le_Lambda _ received a (injOn_evalTuple_of_degree_lt domain hK)
    fun _ hQ ↦ evalTuple_mem_interleavedCodeSet domain hQ

/-- **A finite list bound makes the candidate set finite.** -/
theorem finite_candidateSet_of_Lambda_le (domain : ι ↪ F) (received : ι → κ → F) {K a L : ℕ}
    (hK : K ≤ Fintype.card ι)
    (hΛ : Lambda (interleavedCodeSet (κ := κ) (code domain K : Set (ι → F)))
      (1 - (a : ℝ) / Fintype.card ι) ≤ L) :
    (candidateSet domain received K a).Finite :=
  Set.finite_of_encard_le_coe ((encard_candidateSet_le_Lambda domain received hK a).trans hΛ)

/-- **Anchors separate the candidate set with high probability.** Sample `ω` uniformly from a
finite nonempty type `Ω` and use the anchors `pt ω : ι' → F`. If `pt` is injective, `K ≤ |ι|`,
and the list size at radius `1 - a / |ι|` is at most `L`, the anchors fail to separate the
candidate set with probability at most `choose L 2 * (K - 1) ^ |ι'| / |Ω|`.

This is `Polynomial.prob_not_injOn_evalTuple_le_of_encard_le` with the bound
`encard_candidateSet_le_Lambda`; a coordinate of degree below `K` has natural degree at most
`K - 1`. -/
theorem prob_not_injOn_candidateSet_le {ι' : Type*} [Fintype ι'] {Ω : Type} [Fintype Ω]
    [SampleableType Ω] {pt : Ω → ι' → F} (hpt : Function.Injective pt) (domain : ι ↪ F)
    (received : ι → κ → F) {K a L : ℕ} (hK : K ≤ Fintype.card ι)
    (hΛ : Lambda (interleavedCodeSet (κ := κ) (code domain K : Set (ι → F)))
      (1 - (a : ℝ) / Fintype.card ι) ≤ L) :
    Pr{let ω ← $ᵗ Ω}[¬ Set.InjOn (evalTuple (pt ω)) (candidateSet domain received K a)] ≤
      ENNReal.ofReal ((L.choose 2 * (K - 1) ^ Fintype.card ι' : ℕ) / (Fintype.card Ω : ℝ)) := by
  refine prob_not_injOn_evalTuple_le_of_encard_le hpt
    ((encard_candidateSet_le_Lambda domain received hK a).trans hΛ) fun Q hQ j ↦ ?_
  by_cases h0 : Q j = 0
  · simp [h0]
  · have := (natDegree_lt_iff_degree_lt h0).mpr (hQ.1 j)
    omega

/-- **Agreement of a quotient equation.** For any points `x`, divisor `D`, quotients `q` and
interpolants `I`, the number of columns `i` where `D(x i) * q j (x i) = received i j - I j (x i)`
for all `j` equals the number of columns where the reconstruction `D * q j + I j` agrees with
`received`. The equation is used as stated, so `D(x i)` may be zero. -/
theorem agree_evalTuple_mul_add (x : ι → F) (received : ι → κ → F) (D : F[X])
    (q I : κ → F[X]) :
    agree (evalTuple x fun j ↦ D * q j + I j) received =
      agree (fun i j ↦ D.eval (x i) * (q j).eval (x i))
        (fun i j ↦ received i j - (I j).eval (x i)) := by
  unfold agree
  congr 1
  ext i
  simp [funext_iff, eq_sub_iff_add_eq]

/-- **Reconstructions are candidates.** Let `D` have natural degree at most `e`, `q` have degree
below `k` and `I` have degree below `e`, with `k + e ≤ K`. If the quotient equation
`D(domain i) * q j (domain i) = received i j - I j (domain i)` holds for all `j` in at least `a`
columns, the reconstruction `D * q j + I j` is in the candidate set at degree bound `K`.

The bound on `I` is needed: for `D = 1`, `e = 0` and `q = 0`, a nonzero constant `I` has
degree `0`, which is not below `k + e = 0`. -/
theorem mul_add_mem_candidateSet (domain : ι ↪ F) (received : ι → κ → F) {D : F[X]}
    {e k K a : ℕ} (hD : D.natDegree ≤ e) (hK : k + e ≤ K) {q I : κ → F[X]}
    (hq : ∀ j, (q j).degree < k) (hI : ∀ j, (I j).degree < e)
    (hagree : a ≤ agree (fun i j ↦ D.eval (domain i) * (q j).eval (domain i))
      (fun i j ↦ received i j - (I j).eval (domain i))) :
    (fun j ↦ D * q j + I j) ∈ candidateSet domain received K a :=
  ⟨fun j ↦ (degree_mul_add_lt hD (hq j) (hI j)).trans_le (by exact_mod_cast hK), by
    rwa [agree_evalTuple_mul_add]⟩

/-- **Separating anchors fix every later reconstruction.** Suppose the anchors `x` separate the
candidate set at degree bound `K` and agreement `a`, and let `c` be claimed anchor values. Then
there is an option, depending only on the anchors, the candidate set and `c`, such that:

* it is `some Q` exactly for the candidate `Q` with anchor values `c`;
* every later reconstruction `D * q j + I j` equals it, where `D` vanishes at the anchors and
  has natural degree at most `e`, `q` has degree below `k`, `I` has degree below `e` and anchor
  values `c`, `k + e ≤ K`, and the quotient equation holds in at least `a` columns.

The later data `D`, `e`, `k`, `q` and `I` are quantified after the option is chosen, so they may
depend on randomness sampled after the anchors. -/
theorem exists_selected_before_reconstruction (domain : ι ↪ F) (received : ι → κ → F)
    {ι' : Type*} {x : ι' → F} {K a : ℕ}
    (hgood : Set.InjOn (evalTuple x) (candidateSet domain received K a)) (c : ι' → κ → F) :
    ∃ selected : Option (κ → F[X]),
      (∀ Q, selected = some Q ↔ Q ∈ candidateSet domain received K a ∧ evalTuple x Q = c) ∧
      ∀ (D : F[X]) (e k : ℕ) (q I : κ → F[X]), (∀ i, D.eval (x i) = 0) → D.natDegree ≤ e →
        k + e ≤ K → (∀ j, (q j).degree < k) → (∀ j, (I j).degree < e) → evalTuple x I = c →
        a ≤ agree (fun i j ↦ D.eval (domain i) * (q j).eval (domain i))
          (fun i j ↦ received i j - (I j).eval (domain i)) →
        selected = some (fun j ↦ D * q j + I j) := by
  obtain ⟨o, ho⟩ := exists_option_eq_some_iff_of_injOn_evalTuple hgood c
  refine ⟨o, ho, fun D e k q I hx hD hK hq hI hIc hagree ↦ (ho _).mpr ⟨?_, ?_⟩⟩
  · exact mul_add_mem_candidateSet domain received hD hK hq hI hagree
  · rw [evalTuple_mul_add_of_eval_eq_zero hx]
    exact hIc

/-- **Two anchors fix every later cubic reconstruction.** Suppose the anchors `s₁, s₂` separate
the candidate set at degree bound `T + 3` and agreement `a`, and let `c₁, c₂` be claimed anchor
values. Then there is an option, chosen before any later data, such that:

* it is `some Q` exactly for the candidate `Q` with `Q j (s₁) = c₁ j` and `Q j (s₂) = c₂ j`;
* for every later point `z`, quotients `q` of degree below `T` and interpolants `I` of degree
  below `3` with anchor values `c₁, c₂`, if the cubic quotient equation
  `(X - s₁)(X - s₂)(X - z)(domain i) * q j (domain i) = received i j - I j (domain i)` holds in
  at least `a` columns, the option is `some` of the reconstruction
  `cubicAnchorReconstruct s₁ s₂ z (q j) (I j)`.

No distinctness of `s₁`, `s₂` and `z` and no positivity of `T` is needed. -/
theorem exists_selectedCandidate_before_later (domain : ι ↪ F) (received : ι → κ → F)
    {T a : ℕ} {s₁ s₂ : F}
    (hgood : Set.InjOn (evalTuple ![s₁, s₂]) (candidateSet domain received (T + 3) a))
    (c₁ c₂ : κ → F) :
    ∃ selected : Option (κ → F[X]),
      (∀ Q, selected = some Q ↔ Q ∈ candidateSet domain received (T + 3) a ∧
        (∀ j, (Q j).eval s₁ = c₁ j) ∧ (∀ j, (Q j).eval s₂ = c₂ j)) ∧
      ∀ (z : F) (q I : κ → F[X]), (∀ j, (q j).degree < T) → (∀ j, (I j).degree < 3) →
        (∀ j, (I j).eval s₁ = c₁ j) → (∀ j, (I j).eval s₂ = c₂ j) →
        a ≤ agree (fun i j ↦ (cubicAnchorDivisor s₁ s₂ z).eval (domain i) * (q j).eval (domain i))
          (fun i j ↦ received i j - (I j).eval (domain i)) →
        selected = some (fun j ↦ cubicAnchorReconstruct s₁ s₂ z (q j) (I j)) := by
  have hvals (Q : κ → F[X]) : evalTuple ![s₁, s₂] Q = ![c₁, c₂] ↔
      (∀ j, (Q j).eval s₁ = c₁ j) ∧ (∀ j, (Q j).eval s₂ = c₂ j) := by
    simp [funext_iff, Fin.forall_fin_two]
  obtain ⟨o, ho, hlater⟩ :=
    exists_selected_before_reconstruction domain received hgood ![c₁, c₂]
  refine ⟨o, fun Q ↦ (ho Q).trans (and_congr_right fun _ ↦ hvals Q), ?_⟩
  intro z q I hq hI h₁ h₂ hagree
  have hD : (cubicAnchorDivisor s₁ s₂ z).natDegree ≤ 3 := by
    rw [cubicAnchorDivisor_eq_nodal, Lagrange.natDegree_nodal]
    simp
  exact hlater _ 3 T q I (fun i ↦ by fin_cases i <;> simp [cubicAnchorDivisor]) hD le_rfl hq hI
    ((hvals I).mpr ⟨h₁, h₂⟩) hagree

end Field

section OffDiag

variable {F : Type} {ι κ : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [Fintype κ]

omit [Field F] [Fintype κ] in
/-- The ordered pairs of distinct points outside the domain number
`(|F| - |ι|) (|F| - |ι| - 1)`. -/
theorem card_offDiag_compl_map (domain : ι ↪ F) :
    ((Finset.univ.map domain)ᶜ.offDiag).card =
      (Fintype.card F - Fintype.card ι) * (Fintype.card F - Fintype.card ι - 1) := by
  rw [Finset.offDiag_card, Finset.card_compl, Finset.card_map, Finset.card_univ,
    Nat.mul_sub_one]

omit [Field F] [Fintype κ] in
/-- There are two distinct points outside the domain when `|ι| + 1 < |F|`. -/
theorem nonempty_offDiag_compl_map (domain : ι ↪ F)
    (hspace : Fintype.card ι + 1 < Fintype.card F) :
    Nonempty ((Finset.univ.map domain)ᶜ.offDiag) := by
  refine Finset.Nonempty.to_subtype (Finset.card_pos.mp ?_)
  rw [card_offDiag_compl_map]
  exact Nat.mul_pos (by omega) (by omega)

/-- **Two anchors outside the domain.** Sample an ordered pair `(s₁, s₂)` of distinct points
outside the domain uniformly. If `K ≤ |ι|` and the list size at radius `1 - a / |ι|` is at most
`L`, the anchors fail to separate the candidate set with probability at most
`choose L 2 * (K - 1) ^ 2 / ((|F| - |ι|) (|F| - |ι| - 1))`.

The sample space is nonempty exactly when `|ι| + 1 < |F|`; see `nonempty_offDiag_compl_map`. -/
theorem prob_not_injOn_candidateSet_offDiag_le (domain : ι ↪ F) (received : ι → κ → F)
    {K a L : ℕ} (hK : K ≤ Fintype.card ι)
    (hΛ : Lambda (interleavedCodeSet (κ := κ) (code domain K : Set (ι → F)))
      (1 - (a : ℝ) / Fintype.card ι) ≤ L)
    [Nonempty ((Finset.univ.map domain)ᶜ.offDiag)] :
    Pr{let p ← $ᵗ ((Finset.univ.map domain)ᶜ.offDiag)}[
        ¬ Set.InjOn (evalTuple ![p.1.1, p.1.2]) (candidateSet domain received K a)] ≤
      ENNReal.ofReal ((L.choose 2 * (K - 1) ^ 2 : ℕ) /
        ((Fintype.card F - Fintype.card ι) * (Fintype.card F - Fintype.card ι - 1) : ℕ)) := by
  have hpt : Function.Injective
      fun p : ((Finset.univ.map domain)ᶜ.offDiag) ↦ ![p.1.1, p.1.2] := by
    intro p p' h
    exact Subtype.ext (Prod.ext (congrFun h 0) (congrFun h 1))
  have h := prob_not_injOn_candidateSet_le hpt domain received hK hΛ
  rwa [Fintype.card_fin, Fintype.card_coe, card_offDiag_compl_map] at h

end OffDiag

end ReedSolomon.AnchoredAgreement
