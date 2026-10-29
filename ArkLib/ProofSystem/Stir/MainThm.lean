/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority)
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.OracleReduction.VectorIOR
public import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# ArkLib.ProofSystem.Stir.MainThm

Parameters and relations for Section 5 of [ACFY24stir]. `Params` and `ParamConditions` record
Construction 5.2's numerical and domain conditions, and `CodeParams` records the inner-round
list-decoding assumptions. `stirRelation` describes completeness on codewords;
`stirOpenRelation` describes the soundness language with its strict distance bound.

Construction 5.2, Lemma 5.4 and Theorem 5.1 remain unformalized targets. A concrete STIR prover,
verifier and transcript are needed: existence of an arbitrary protocol with numerical error and
proof-length bounds alone also permits an exhaustive exact-membership verifier. The construction
must sample from the specified domains and their complements, and its analysis must track each
challenge's error and the verifier's queries.

## Round-by-round soundness target (Lemma 5.4)

Fix `P : Params ι F` satisfying `ParamConditions ι P` and an out-of-domain repetition parameter `s`.
Write `dᵢ = deg / ∏_{j<i} kⱼ`, `kᵢ = foldingParamᵢ`, `tᵢ = repeatParamᵢ` and
`ρᵢ = rate (code φᵢ dᵢ)`. The protocol must depend only on these construction parameters,
before distances `δᵢ` and list sizes `ℓᵢ` are chosen. Assume `0 < δ₀ < 1 - B⋆(ρ₀)` and, for
`0 < i ≤ M`, list decodability at `(δᵢ, ℓᵢ)` with
`0 < δᵢ < min(1 - ρᵢ - 1/|Lᵢ|, 1 - B⋆(ρᵢ))`. For oracles at least `δ₀`-far from the
initial code, the intended per-challenge error vector is
`(ε_fold, ε_out₁, ε_shift₁, …, ε_out_M, ε_shift_M, ε_fin)`, with

* `ε_fold ≤ err⋆(d₀/k₀, ρ₀, δ₀, k₀)`;
* `ε_outᵢ ≤ ℓᵢ²/2 * (dᵢ / (|F| - |Lᵢ|))^s` for `0 < i ≤ M`;
* `ε_shiftᵢ ≤ (1 - δᵢ₋₁)^tᵢ₋₁ + err⋆(dᵢ, ρᵢ, δᵢ, tᵢ₋₁ + s)
  + err⋆(dᵢ/kᵢ, ρᵢ, δᵢ, kᵢ)` for `0 < i ≤ M`;
* `ε_fin ≤ (1 - δ_M)^t_M`, including `M = 0`.

Here `err⋆` is `STIR.proximityError`. The paper's `2M + 1` interactive rounds and final
randomized decision must be represented with their actual challenge distributions.

## Main theorem target (Theorem 5.1)

For a smooth Reed–Solomon code of power-of-two degree `d`, rate `ρ = d/|L|`, security parameter
`λ`, distance `0 < δ < 1 - 1.05 * √ρ`, and power-of-two folding parameter `k ≥ 4`, the paper
claims a public-coin IOPP with round-by-round error `2^(-λ)`, `O(log_k d)` rounds, proof length
`|L| + Oₖ(log d)`, input query complexity `λ / (-log(1 - δ))`, and proof query complexity
`Oₖ(log d + λ * log(log d / log(1/ρ)))`, under
`|F| = Ω(λ * 2^λ * d² * |L|^(7/2) / log(1/ρ))`.

The constants must be uniform in the protocol parameters, except that the `Oₖ` constants may
depend on `k`. Query accounting must use the paper's convention of counting `k` grouped points
as one symbol. The January 2025 revision's Appendix C.1 has an additional field-size dependence
on `1/(-log(1 - δ'))`, absent from the displayed Theorem 5.1; deriving uniform constants requires
resolving this discrepancy.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

@[expose] public section

open BigOperators Finset Code NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

/-- **Per‑round protocol parameters:**
  For a fixed depth `M`, the reduction runs `M + 1` rounds.
  In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
  evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
  and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type*) where
  deg : ℕ -- initial degree
  foldingParam : Fin (M + 1) → ℕ
  φ : (i : Fin (M + 1)) → (ι i) ↪ F
  repeatParam : Fin (M + 1) → ℕ

/-- **Degree after `i` folds:**
  The starting degree is `deg`;
  every fold divides it by `foldingParamⱼ (j<i)` to obtain `degreeᵢ`.
  Note that division rounds down for `ℕ`. -/
def degree (P : Params ι F) : Fin (M + 1) → ℕ :=
  fun i => P.deg / ∏ j < i, (P.foldingParam j)

omit [Field F] [Fintype F] [DecidableEq F] [∀ i : Fin (M + 1), Fintype (ι i)] in
/-- Before any fold the degree is the initial degree. -/
lemma degree_zero (P : Params ι F) : degree ι P 0 = P.deg := by
  have hIio : Finset.Iio (0 : Fin (M + 1)) = ∅ := by
    ext j
    simp
  simp [degree, hIio]

/-- **Conditions that protocol parameters must satisfy.**
  - `h_deg` : initial degree `deg` is a power of 2
  - `h_foldingParams` : each folding parameter `foldingParamᵢ` is a power of 2
  - `h_deg_ge` : `deg ≥ ∏ i foldingParamᵢ`
  - `h_smooth` : each `φᵢ` must embed a smooth evaluation domain
  - `h_smooth_lt` : `degreeᵢ < |ιᵢ|`
  - `h_repeatP_le` : `repeatParamᵢ + 1 ≤ degreeᵢ₊₁` for `i < M`, the paper's
    `tᵢ + 1 ≤ d / ∏_{j ≤ i} kⱼ`; `repeatParam_M` is not constrained -/
structure ParamConditions (P : Params ι F) where
  h_deg : ∃ k : ℕ, P.deg = 2^k
  h_foldingParams : ∀ i : Fin (M + 1), ∃ k : ℕ, (P.foldingParam i) = 2^k
  h_deg_ge : P.deg ≥ ∏ i : Fin (M + 1), (P.foldingParam i)
  h_smooth : ∀ i : Fin (M + 1), Smooth (P.φ i)
  h_smooth_lt : ∀ i : Fin (M + 1), degree ι P i < Fintype.card (ι i)
  h_repeatP_le : ∀ i : Fin M, P.repeatParam i.castSucc + 1 ≤ degree ι P i.succ

/-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) where
  δ : Fin (M + 1) → ℝ≥0
  l : Fin (M + 1) → ℝ≥0

/-- Family of Reed–Solomon codes expected by the verifier, we have
  `codeᵢ = RS[F, ιᵢ, degreeᵢ]` and for `i ∈ {1,…,M}`
  `hlistDecode: codeᵢ` is `(δᵢ,lᵢ)`-list decodable
-/
structure CodeParams (P : Params ι F) (Dist : Distances M) where
  C : ∀ i : Fin (M + 1), Set ((ι i) → F)
  h_code : ∀ i : Fin (M + 1), C i = code (P.φ i) (degree ι P i)
  h_listDecode : ∀ i : Fin (M + 1), i ≠ 0 → IsListDecodable (C i) (Dist.δ i) (Dist.l i)

section MainTheorem

/-- `OracleStatement` defines the oracle message type for a multi-indexed setting:
  given base input type `ι`, and field `F`, the output type at each index
  is a function `ι → F` representing an evaluation over `ι`.
-/
@[reducible]
def OracleStatement (ι F : Type) : Unit → Type :=
    fun _ => ι → F

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

/-- STIR relation: the oracle's output is δᵣ-close to a Reed-Solomon codeword
  of degree less than `degree` over domain `φ`, within error `err`.
-/
def stirRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (degree : ℕ) (φ : ι ↪ F) (err : ℝ≥0) : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ => δᵣ(oracle (), ReedSolomon.code φ degree) ≤ err

/-- Strict version of `stirRelation`: the oracle's output is *strictly* closer than `err` to a
  Reed-Solomon codeword of degree less than `degree` over domain `φ`.

  This is the soundness relation of an IOPP of proximity: its complement is "at least `err`-far",
  which is the case the soundness statements of [ACFY24stir] cover (`δ₀ ≤ Δ(f, RS)` in Lemma 5.4).
  Completeness is stated with `stirRelation degree φ 0`, the codewords. -/
def stirOpenRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (degree : ℕ) (φ : ι ↪ F) (err : ℝ≥0) : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ => δᵣ(oracle (), ReedSolomon.code φ degree) < err

end MainTheorem

end StirIOP
