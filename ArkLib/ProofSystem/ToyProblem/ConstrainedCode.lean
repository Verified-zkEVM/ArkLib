/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds

/-!
# The toy-protocol soundness experiment is the MCA experiment of the constrained code

This file formalizes the observation (G. Fenzi) that the soundness experiment of
the §6 toy reduction `T[C, t]` is the mutual-correlated-agreement (MCA) experiment
of the **constrained code** — the code obtained by adjoining the extra linear
constraint `⟨m, v⟩ = μ` to `C`. Two results, of increasing fidelity:

* `gamma_transition_prob_le_constrained` — an upper bound `toy γ-event ≤
  ε_mca(C_v, δ)` against the **stock** MCA error of the appended-coordinate code
  `C_v` (see the caveat: this over-counts, so it is only a bound).
* `gammaEvent_iff_constrainedMCAEvent` / `gammaEvent_prob_eq_constrainedMCAEvent` —
  a per-instance **equivalence**: under `hNoWit`, the toy γ-event coincides with the
  *constraint-pinned* event `ConstrainedMCAEvent` (constraint coordinate mandatory,
  proximity measured on the data coordinates). NB this is a restatement in MCA shape,
  **not** an equality with the library MCA experiment (`IsMCA`) of `constrainedCode` —
  `ConstrainedMCAEvent` is bespoke, phrased directly in `enc`/`v`, and its `¬`-clause
  is redundant under `hNoWit`; see the theorem docstring. The genuine reduction to the
  constrained code's MCA bad event is the `≤` bound above.

Concretely, for the scalar alphabet `A = F` we adjoin the constraint value
`⟨m, v⟩` as one extra coordinate (indexed by `Unit`):

  `constrainedCode enc v := range (m ↦ Sum.elim (enc m) (fun _ ↦ ⟨m, v⟩)) ⊆ (ι ⊕ Unit) → F`.

This keeps the code `F`-additive (it is the range of a linear map), turns the
affine constraint into an *exact* coordinate match, and makes the folded target
`μ₁ + γ·μ₂` the value of the line `f₁ + γ·f₂` at the extra coordinate.

The main result, `gamma_transition_prob_le_constrained`, shows that the
γ-round transition probability of the toy reduction (the event of
`ToyProblem.gamma_transition_prob_le` / the private `gammaEvent`) is bounded by

  `mcaError(AffineLineGenerator F, constrainedCode enc v, δ)`,

a **single** MCA quantity in which the linear constraint is internalized as a code
coordinate, so no separate `|Λ|/|F|` list-size term appears (compare the paper's
split bound `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` proved by
`ToyProblem.gamma_transition_prob_le`).

The proof is purely structural — no coding-theory external is invoked. The toy bad
event implies `IsMCA (AffineLineGenerator F) (constrainedCode enc v) γ U δ`, taking
the agreement set `S' = S ∪ {extra coordinate}`; the `+1` slack from the extra
coordinate absorbs the `(1-δ)` factor, so the *same* `δ` works with no proximity
rescaling.

## Caveat: this is an upper bound, not an equality or a proven improvement

The result is `toy γ-event ≤ mcaError(AffineLineGenerator F, C_v, δ)`, established by a
single `le_iSup`.
Two things it does **not** establish, and should not be read to:

* **Not an equality.** `IsMCA` (hence `mcaError`) quantifies over *all* agreement
  sets `S'` of size `≥ (1-δ)(n+1)`, including sets that *omit* the extra `Unit`
  coordinate. On such an `S'` the constraint is never tested, so that branch
  reduces to a plain base-code-`C` MCA bad event (at the larger `(1-δ)(n+1)` size
  budget). Hence `ε_mca(C_v, δ)` *over-counts* relative to the toy soundness and is
  only an upper bound on it, not equal to it. (No comparison with
  `mcaError(AffineLineGenerator F, C, δ)` is
  proved here in either direction: embedding a base agreement set `S ⊆ ι` into
  `ι ⊕ Unit` must clear the strictly larger `(1-δ)(n+1)` threshold, so the naive
  monotonicity argument fails.) The per-instance *equivalence* uses the **constraint-pinned**
  MCA event `ConstrainedMCAEvent` (constraint coordinate mandatory; proximity on the
  data coordinates `ι`) — see `gammaEvent_iff_constrainedMCAEvent`. Pinning into the
  *full* index `ι ⊕ Unit` with the stock `(1-δ)(n+1)` size budget does **not** give
  an equality: the backward direction loses a `δ` of slack (recovering only
  `|S ∩ ι| ≥ (1-δ)n - δ`), so the pinned event must measure size on `ι` only.

* **Not a proven improvement.** Whether `ε_mca(C_v, δ) ≤ ε_mca(C, δ) + |Λ|/|F|`
  (i.e. whether this single quantity is tighter than / equal to the paper's split
  bound, rather than looser) is **not** proved here, and is non-trivial: the
  `|Λ|/|F|` control on the constraint-pinned part of `mcaError` for `C_v` would itself
  need the counting argument of `gamma_transition_prob_le`. Treat the relationship
  to the paper bound as open.

## Scope

This is stated for the **scalar** specialization `A = F`,
where the `F`-valued constraint coordinate lives in the same alphabet as the
codeword. The general `F`-module alphabet `A` (folded RS, `A = Fin s → F`) would
require the constrained code to live in `(ι → A) × F`, i.e. a heterogeneous-alphabet
generalization of the current `mcaError` ambient — left as future work.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace ToyProblem

open Code InterleavedCode ProximityGap CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory
open Probability

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-- Linear encoder obtained by adjoining the scalar constraint coordinate. -/
def constrainedEncoder {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F))
    (v : Fin k → F) : (Fin k → F) →ₗ[F] ((ι ⊕ Unit) → F) where
  toFun m := Sum.elim (enc m) (fun _ ↦ ∑ j, m j * v j)
  map_add' m₁ m₂ := by
    funext x
    cases x with
    | inl i => simp
    | inr u =>
      cases u
      simp only [Sum.elim_inr, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c m := by
    funext x
    cases x with
    | inl i => simp
    | inr u =>
      cases u
      simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_assoc]

/-- **The constrained code** (scalar alphabet `A = F`).

Adjoin the linear-constraint value `⟨m, v⟩ = ∑ j, m j * v j` as one extra
coordinate (indexed by `Unit`), so the affine constraint becomes an exact
coordinate match and the code stays `F`-additive (it is the range of a linear
map). Its MCA error upper-bounds the toy-protocol soundness experiment
(`gamma_transition_prob_le_constrained`; see that lemma's caveat — the bound is
one-directional, not an equality). -/
def constrainedCode {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F)) (v : Fin k → F) :
    ModuleCode (ι ⊕ Unit) F F :=
  LinearMap.range (constrainedEncoder enc v)

/-- **The toy-protocol γ-round soundness experiment is bounded by the MCA error of
the constrained code.** For an instance `(v, μ₁, μ₂, f₁, f₂)` of the toy reduction
admitting **no** relaxed-relation witness (`hNoWit`), the probability over a
uniform challenge `γ` that some message `m` satisfies the post-`γ` knowledge
state is at most `mcaError(AffineLineGenerator F, constrainedCode enc v, δ)`.

This is the constrained-code reformulation of `ToyProblem.gamma_transition_prob_le`
(`A = F`): the linear constraint is internalized as a code coordinate, so the bound
is a single MCA quantity with no separate `|Λ(C^{≡2}, δ)| / |F|` term.

**Caveat (one-directional).** This is an upper bound, established by a single
`le_iSup`. It is *not* an equality (`mcaError` for `C_v` over-counts: `IsMCA` admits
agreement sets omitting the constraint coordinate, which reduce to base-code-`C`
MCA events), and it is *not* shown to be `≤` the paper's split bound `ε_mca(C,δ) +
|Λ|/|F|`. See the module docstring's caveat section.

Directly, the toy bad event implies
`IsMCA (AffineLineGenerator F) (constrainedCode enc v) γ U δ`, witnessed by the agreement set
`S' = S ∪ {extra coordinate}`. -/
theorem gamma_transition_prob_le_constrained {k : ℕ} [DecidableEq ι]
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F)
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j) :
    Pr_{let γ ← $ᵖ F}[∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j]
      ≤ mcaError (AffineLineGenerator F) (constrainedCode enc v) (δ : ℝ) := by
  classical
  set U₀ : (ι ⊕ Unit) → F := Sum.elim f₁ (fun _ ↦ μ₁) with hU₀
  set U₁ : (ι ⊕ Unit) → F := Sum.elim f₂ (fun _ ↦ μ₂) with hU₁
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (fun γ ↦ IsMCA (AffineLineGenerator F) (constrainedCode enc v)
        γ ![U₀, U₁] (δ : ℝ)) (fun γ hγ ↦ ?_)) ?_
  · -- The toy bad event implies the constrained code's MCA bad event.
    obtain ⟨m, hconstr, S, hScard, hagree⟩ := hγ
    set S' : Finset (ι ⊕ Unit) := insert (Sum.inr ()) (S.image Sum.inl) with hS'
    have hmem_inr : Sum.inr () ∈ S' := by rw [hS']; exact Finset.mem_insert_self _ _
    have hmem_inl : ∀ {j : ι}, j ∈ S → Sum.inl j ∈ S' := fun hj => by
      rw [hS']; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)
    refine ⟨S', ?_, ?_, ?_⟩
    · -- Size: `(1-δ)·(n+1) ≤ |S|+1`, the `+1` slack absorbing the `(1-δ)` factor.
      have hcard_S' : S'.card = S.card + 1 := by
        rw [hS', Finset.card_insert_of_notMem (by simp),
          Finset.card_image_of_injective _ Sum.inl_injective]
      have hcard_univ : Fintype.card (ι ⊕ Unit) = Fintype.card ι + 1 := by
        rw [Fintype.card_sum, Fintype.card_unit]
      rw [ge_iff_le, hcard_S', hcard_univ]
      push_cast
      nlinarith [hScard, NNReal.coe_nonneg δ]
    · rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨constrainedEncoder enc v m, ⟨m, rfl⟩, ?_⟩
      funext x
      rcases x with ⟨x, hx⟩
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      cases x with
      | inl j =>
          have hj : j ∈ S := by
            rw [hS', Finset.mem_insert, Finset.mem_image] at hx
            rcases hx with hbad | ⟨j', hj', heq⟩
            · exact (Sum.inl_ne_inr hbad).elim
            · exact Sum.inl.inj heq ▸ hj'
          simpa [AffineLineGenerator, Fin.sum_univ_two, hU₀, hU₁,
            constrainedEncoder] using hagree j hj
      | inr u =>
          simpa [AffineLineGenerator, Fin.sum_univ_two, hU₀, hU₁,
            constrainedEncoder, smul_eq_mul] using hconstr.symm
    · by_contra hnot
      push Not at hnot
      have hrow (r : Fin 2) :=
        (LinearCode.mem_projectedCodeSubmod_iff
          (constrainedCode enc v) S'
          (LinearCode.projectedWord (![U₀, U₁] r) S')).mp (hnot r)
      obtain ⟨w₀, hw₀, hp₀⟩ := hrow 0
      obtain ⟨w₁, hw₁, hp₁⟩ := hrow 1
      obtain ⟨M₀, rfl⟩ := hw₀
      obtain ⟨M₁, rfl⟩ := hw₁
      apply hNoWit
      refine ⟨![M₀, M₁], ?_, S, hScard, ?_⟩
      · intro r
        fin_cases r
        · have h := congrFun hp₀ ⟨Sum.inr (), hmem_inr⟩
          simpa [LinearCode.projectedWord, hU₀, constrainedEncoder] using h.symm
        · have h := congrFun hp₁ ⟨Sum.inr (), hmem_inr⟩
          simpa [LinearCode.projectedWord, hU₁, constrainedEncoder] using h.symm
      · intro r j hj
        fin_cases r
        · have h := congrFun hp₀ ⟨Sum.inl j, hmem_inl hj⟩
          simpa [LinearCode.projectedWord, hU₀, constrainedEncoder] using h
        · have h := congrFun hp₁ ⟨Sum.inl j, hmem_inl hj⟩
          simpa [LinearCode.projectedWord, hU₁, constrainedEncoder] using h
  · exact le_iSup
      (fun U : Fin 2 → ((ι ⊕ Unit) → F) ↦
        Pr_{let γ ← $ᵖ F}[IsMCA (AffineLineGenerator F)
          (constrainedCode enc v) γ U (δ : ℝ)]) ![U₀, U₁]

/-! ## The per-instance equivalence (constraint-pinned event, proximity on data coordinates)

The `≤` bound above over-counts, because `IsMCA` over `ι ⊕ Unit` admits agreement
sets that omit the constraint coordinate. An exact restatement of the toy γ-event in
MCA shape requires (i) the constraint coordinate to be mandatory and (ii) proximity
measured on the data coordinates `ι` only — pinning into the full index with the stock
`(1-δ)(n+1)` budget loses a `δ` of slack in the backward direction and fails to give an
equality. The resulting `ConstrainedMCAEvent` is a bespoke event (not the library
`IsMCA`/`mcaError` experiment of any code), so the equivalence below is a per-instance
restatement, not a reduction to the library MCA experiment.
-/

set_option linter.unusedFintypeInType false in
/-- **Constraint-pinned MCA event of the constrained code** (proximity measured on
the data coordinates `ι`; the constraint coordinate is mandatory but outside the
size budget). The folded constrained codeword (target `μ₁ + γ·μ₂`) agrees with the
folded word on `S`, while no constrained-codeword *pair* (targets `μ₁, μ₂`) agrees
with `(f₁, f₂)` on `S`. -/
def ConstrainedMCAEvent {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F)) (v : Fin k → F)
    (δ : ℝ≥0) (μ₁ μ₂ : F) (f₁ f₂ : ι → F) (γ : F) : Prop :=
  ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
    (∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧ ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j) ∧
    ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      (∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j)

set_option linter.unusedFintypeInType false in
/-- **Per-instance equivalence (constraint-pinned).** Under `hNoWit` (the instance
admits no relaxed-relation witness), the toy γ-event is equivalent, for every `γ`,
to `ConstrainedMCAEvent` — the toy event augmented with the (under `hNoWit`
automatically-satisfied) clause that no constrained-codeword *pair* agrees on `S`.

This is a per-instance restatement, **not** a reduction to the library MCA
experiment of `constrainedCode`: `ConstrainedMCAEvent` is a bespoke event phrased
directly in terms of `enc`/`v`, not via `constrainedCode` or `mcaError`, and the
added `¬`-clause is redundant under `hNoWit`. The genuine reduction to the
constrained code's MCA bad event is the upper bound
`gamma_transition_prob_le_constrained` above; that is the headline result.

Forward (`mp`, uses `hNoWit`): the toy event's witness set `S` satisfies the
`¬`-clause because a local witness on `S` would be a global witness. Backward
(`mpr`, no `hNoWit`): drop the `¬`-clause and read off the message `m`. -/
theorem gammaEvent_iff_constrainedMCAEvent {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F)
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j) (γ : F) :
    (∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j)
      ↔ ConstrainedMCAEvent enc v δ μ₁ μ₂ f₁ f₂ γ := by
  constructor
  · rintro ⟨m, hconstr, S, hScard, hagree⟩
    refine ⟨S, hScard, ⟨m, hconstr, hagree⟩, ?_⟩
    rintro ⟨M, hMc, hMa⟩
    exact hNoWit ⟨M, hMc, S, hScard, hMa⟩
  · rintro ⟨S, hScard, ⟨m, hconstr, hagree⟩, _⟩
    exact ⟨m, hconstr, S, hScard, hagree⟩

set_option linter.unusedFintypeInType false in
/-- **Probability form of the equality**: the toy γ-round transition probability
equals the probability of the constraint-pinned MCA event of the constrained code. -/
theorem gammaEvent_prob_eq_constrainedMCAEvent {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F)
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j) :
    Pr_{let γ ← $ᵖ F}[∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j]
      = Pr_{let γ ← $ᵖ F}[ConstrainedMCAEvent enc v δ μ₁ μ₂ f₁ f₂ γ] := by
  refine le_antisymm ?_ ?_
  · exact Pr_le_Pr_of_implies ($ᵖ F) _ _
      (fun γ h ↦ (gammaEvent_iff_constrainedMCAEvent enc δ v μ₁ μ₂ f₁ f₂ hNoWit γ).mp h)
  · exact Pr_le_Pr_of_implies ($ᵖ F) _ _
      (fun γ h ↦ (gammaEvent_iff_constrainedMCAEvent enc δ v μ₁ μ₂ f₁ f₂ hNoWit γ).mpr h)

end ToyProblem
