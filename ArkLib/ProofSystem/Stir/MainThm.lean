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

Section 5 of [ACFY24stir]: the parameters of Construction 5.2 (`Params`, `ParamConditions`), the
round-by-round soundness of STIR (Lemma 5.4, `stir_rbr_soundness`) and the main theorem
(Theorem 5.1, `stir_main`).

Both results are stated as the existence of a vector IOPP with the bounds of the paper. ArkLib does
not yet formalize Construction 5.2 or the number of queries a verifier makes, so they do not force
the protocol to be STIR; the docstrings say what is and is not stated.

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

/-- **Theorem 5.1 of [ACFY24stir]: STIR.**

  There are constants `c_F`, `c_M > 0` and `c_len : ℕ → ℝ` such that the following holds for every
  security parameter `secpar`, Reed-Solomon code `RS[F, ι, degree]` of rate `ρ = degree / |ι|`
  (`degree` a power of 2, `φ` embedding a smooth domain), proximity parameter
  `δ ∈ (0, 1 - 1.05 * √ρ)` and folding parameter `k ≥ 4` that is a power of 2.
  If `|F| ≥ c_F * secpar * 2^secpar * degree² * |ι|^{7/2} / log(1/ρ)`, there is a vector IOPP `π`
  for the code, with `2M + 2` challenges from the verifier, that is complete and round-by-round
  sound against the oracles that are at least `δ`-far from the code (`stirOpenRelation`), with
  - round-by-round soundness error `≤ 2^(-secpar)`,
  - `M ≤ c_M * log_k degree`,
  - proof length `≤ |ι| + c_len k * log degree`.

  The constants are chosen before the parameters, so these are the paper's `Ω` and `O` bounds
  (`Oₖ` for the proof length, whose constant may depend on `k`). The exponent `7/2` of the field
  size is the one of the January 2025 revision of ePrint 2024/390.

  Not stated: the two query-complexity items of the theorem, `secpar / (- log(1-δ))` queries to the
  input and `Oₖ(log degree + secpar * log(log degree / log(1/ρ)))` queries to the proof strings.
  `VectorIOP` has no notion of the number of queries a verifier makes
  (`OracleVerifier.numQueries` is a stub), and the paper counts the `k` points read together as one
  symbol. Without them this is an existence statement that does not force `π` to be STIR: a
  verifier that reads its whole oracle is not excluded. -/
theorem stir_main :
    ∃ c_F : ℝ, 0 < c_F ∧ ∃ c_M : ℝ, 0 < c_M ∧ ∃ c_len : ℕ → ℝ,
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
      (secpar : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (φ : ι ↪ F) [Smooth φ]
      (degree : ℕ) (hdeg : ∃ p : ℕ, degree = 2 ^ p)
      (k : ℕ) (hk : ∃ p : ℕ, k = 2 ^ p) (hkGe : 4 ≤ k)
      (δ : ℝ≥0) (hδPos : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
      (hF : c_F * (secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι : ℝ) ^ ((7 : ℝ) / 2) /
            Real.log (1 / rate (code φ degree))) ≤ Fintype.card F),
    ∃ (M n : ℕ) (vPSpec : ProtocolSpec.VectorSpec n),
      Fintype.card vPSpec.ChallengeIdx = 2 * M + 2 ∧
      ∃ (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
        (π : VectorIOP Unit (OracleStatement ι F) Unit vPSpec F),
        IsSecureWithGap (stirRelation degree φ 0) (stirOpenRelation degree φ δ) ε_rbr π ∧
        (∀ i, ε_rbr i ≤ 1 / 2 ^ secpar) ∧
        (M : ℝ) ≤ c_M * (Real.log degree / Real.log k) ∧
        (vPSpec.totalMessageLength : ℝ) ≤ Fintype.card ι + c_len k * Real.log degree := by
  sorry

end MainTheorem

section RBRSoundness

open LinearCode

/-- **Lemma 5.4 of [ACFY24stir]: round-by-round soundness of STIR.**

  Indices start at `0`. Consider:
  - `ι = {ιᵢ}_{i = 0, …, M}`, the smooth evaluation domains `Lᵢ`;
  - `P : Params ι F`, the parameters of Construction 5.2: the initial degree `deg`, the folding
    parameters `kᵢ = foldingParamᵢ`, the embeddings `φᵢ` and the repetition parameters
    `tᵢ = repeatParamᵢ`; and `s`, the out-of-domain repetition;
  - `hParams : ParamConditions ι P`, the conditions that these parameters must satisfy.

  Write `dᵢ = degree ι P i = deg / ∏_{j<i} kⱼ` and `ρᵢ = rate (code φᵢ dᵢ)`, the rate of
  `RS[F, Lᵢ, dᵢ]`. Then there is a vector IOP `π` with `2M + 2` challenges from the verifier, which
  depends on these parameters only, such that for all
  - `Dist` and `Codes : CodeParams ι P Dist`, the distances `δᵢ` and list sizes `ℓᵢ = lᵢ`, with
    `RS[F, Lᵢ, dᵢ]` being `(δᵢ, ℓᵢ)`-list decodable for `0 < i ≤ M`;
  - `0 < δ₀ < 1 - B⋆(ρ₀)` and, for `0 < i ≤ M`, `0 < δᵢ < 1 - ρᵢ - 1/|Lᵢ|` and
    `δᵢ < 1 - B⋆(ρᵢ)`,

  `π` is complete for `RS[F, L₀, d₀]` and round-by-round sound against the oracles that are at least
  `δ₀`-far from it (`stirOpenRelation`), with errors `ε_fold`, `ε_outᵢ`, `ε_shiftᵢ` and `ε_fin`
  such that
  - `ε_fold ≤ err⋆(d₀/k₀, ρ₀, δ₀, k₀)`
  - `ε_outᵢ ≤ ℓᵢ²/2 * (dᵢ / (|F| - |Lᵢ|))^s`
  - `ε_shiftᵢ ≤ (1 - δᵢ₋₁)^{tᵢ₋₁} + err⋆(dᵢ, ρᵢ, δᵢ, tᵢ₋₁ + s) + err⋆(dᵢ/kᵢ, ρᵢ, δᵢ, kᵢ)`
  - `ε_fin ≤ (1 - δ_M)^{t_M}`.

  The paper's round `i ∈ {1, …, M}` is `j + 1` for `j : Fin M`, so `ε_out j` and `ε_shift j` are
  the errors of round `j + 1`. Every challenge is given the maximum of the four families as its
  error, which is weaker than the paper's vector of per-round errors.

  **Limitation.** This is an existence statement. ArkLib has neither Construction 5.2 nor a count
  of the queries of a verifier, so the statement does not force `π` to be STIR: it records the
  error bounds that Construction 5.2 achieves. -/
theorem stir_rbr_soundness
    [SampleableType F] {s : ℕ}
    {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    (hParams : ParamConditions ι P) :
    ∃ n : ℕ,
    -- There exists an `n`-message vector IOPP,
    ∃ vPSpec : ProtocolSpec.VectorSpec n,
    -- such that there are `2 * M + 2` challenges from the verifier to the prover,
    Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2 ∧
    -- ∃ vector IOPP π with the aforementioned `vPSpec`, and for
    -- `Statement = Unit, Witness = Unit, OracleStatement(ι₀, F)` such that, for all distances and
    -- list sizes `Dist` of the lemma,
    ∃ π : VectorIOP Unit (OracleStatement (ι 0) F) Unit vPSpec F,
    ∀ {Dist : Distances M} (Codes : CodeParams ι P Dist)
      (hδ₀Pos : 0 < Dist.δ 0)
      (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) (degree ι P 0)))))
      (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        0 < Dist.δ j ∧
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j))))),
    -- there are round-by-round errors `ε_fold`, `ε_out`, `ε_shift`, `ε_fin` of `π`, whose maximum
    -- is the error of every challenge, such that
    ∃ (ε_fold : ℝ≥0) (ε_out ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0),
    (IsSecureWithGap (stirRelation (degree ι P 0) (P.φ 0) 0)
                    (stirOpenRelation (degree ι P 0) (P.φ 0) (Dist.δ 0))
                    (fun _ => ε_fold ⊔ ε_fin ⊔ univ.sup ε_out ⊔ univ.sup ε_shift) π) ∧
    -- `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, foldingParam₀)`
      ε_fold ≤ proximityError F (degree ι P 0 / P.foldingParam 0)
                 (rate (code (P.φ 0) (degree ι P 0))) (Dist.δ 0) (P.foldingParam 0)
      ∧
      -- Note here that `j : Fin M`, so we need to cast into `Fin (M + 1)` for indexing of
      -- `Dist.δ` and `P.repeatParam`. To get `j`, we use `.castSucc`, whereas to get `j + 1`,
      -- we use `.succ`.
      -- Because of the difference in indexing between the paper and the code, we essentially have
      -- `j = i - 1` compared to the paper.
      -- `ε_out_{j+1} ≤ l_{j+1}²/2 * (degree_{j+1} / (|F| - |ι_{j+1}|))^s`
      (∀ j : Fin M,
        ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s
        ∧
        -- `ε_shift_{j+1} ≤ (1 - δ_j)^repeatParam_j`
        -- `+ errStar(degree_{j+1}, ρ_{j+1}, δ_{j+1}, repeatParam_j + s)`
        -- `+ errStar(degree_{j+1}/foldingParam_{j+1}, ρ_{j+1}, δ_{j+1}, foldingParam_{j+1})`
        ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc)  +
          -- proximityError(degree_{j+1}, ρ(code_{j+1}), δ_{j+1}, repeatParam_j + s),
          -- where code_{j+1} = code φ_{j+1} degree_{j+1}
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc + s) +
          -- proximityError(degree_{j+1} / foldingParam_{j+1}, ρ(code_{j+1}), δ_{j+1},
          -- foldingParam_{j+1})
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.foldingParam j.succ)) ∧
      -- `ε_fin ≤ (1 - δ_M)^repeatParam_M`
      ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M)) := by
  sorry

end RBRSoundness

end StirIOP
