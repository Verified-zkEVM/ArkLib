/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Stir.ProximityBound


/-!Section 5 STIR[ACFY24], Theorem 5.1 and Lemma 5.4 -/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP

namespace StirIOP

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M+1) → Type) [∀ i : Fin (M+1), Fintype (ι i)]
         [∀ i : Fin (M+1), DecidableEq (ι i)]

/-- Per‑round protocol parameters:
  For a fixed depth `M`, the reduction runs `M + 1` rounds.
  In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
  evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
  and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type*) where
  foldingParam : Fin (M+1) → ℕ
  φ : (i : Fin (M+1)) → (ι i) ↪ F
  repeatParam : Fin (M+1) → ℕ

/-- Degree after `i` folds:
  The starting degree is `deg`;
  every fold divides it by `foldingParamⱼ (j<i)` to obtain `degreeᵢ`.
  We assume divisibility so that the result is an integar. -/
def degree (deg : ℕ) (P : Params ι F) : Fin (M + 1) → ℕ :=
  fun i => deg / ∏ j < i, (P.foldingParam j)

/-- ** Conditions that protocol parameters must satisfy. **
  h_deg : initial degree `deg` is a power of 2
  h_foldingParams : ∑ i : Fin (M+1), foldingParamᵢ is a power of 2
  h_deg_ge : deg ≥ ∏ i foldingParamᵢ
  h_smooth : each φᵢ must embed a smooth evaluation domain
  h_smooth_le : |ιᵢ| ≤ degreeᵢ
  h_repeatP_le : ∀ i : Fin (M+1), repeatParamᵢ + 1 ≤ degreeᵢ -/
structure ParamConditions (P : Params ι F) where
  deg : ℕ -- initial degree
  h_deg : ∃ k : ℕ, deg = 2^k
  h_foldingParams : ∀ i : Fin (M+1), ∃ k : ℕ, (P.foldingParam i) = 2^k
  h_deg_ge : deg ≥ ∏ i < (M+1), (P.foldingParam i)
  h_smooth : ∀ i : Fin (M+1), Smooth (P.φ i)
  h_smooth_le : ∀ i : Fin (M+1), Fintype.card (ι i) ≤ (degree ι deg P i)
  h_repeatP_le : ∀ i : Fin (M+1), P.repeatParam i + 1 ≤ (degree ι deg P i)

/-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) where
  δ : Fin (M + 1) → ℝ≥0
  l : Fin (M + 1) → ℝ≥0

/-- Family of Reed–Solomon codes expected by the verifier, we have
  `codeᵢ = RS[F, ιᵢ, degreeᵢ]` and
  `hlistDecode: codeᵢ` is `(δᵢ,lᵢ)`-list decodable-/
structure CodeParams (d : ℕ) (P : Params ι F) (Dist : Distances M) where
  C : ∀ i : Fin (M+1), Set ((ι i) → F)
  h_code : ∀ i : Fin (M+1), C i = code (P.φ i) (degree ι d P i)
  hlistDecode : ∀ i : Fin (M+1), listDecodable (C i) (Dist.δ i) (Dist.l i)

/-- Predecessor inside `Fin n` (requires `i ≠ 0`). -/
def predFin {n : ℕ} (i : Fin n) (h : i.val ≠ 0) : Fin n :=
  ⟨i.val - 1, Nat.lt_trans (Nat.pred_lt h) i.isLt⟩

section MainTheorem

open OracleComp OracleSpec ProtocolSpec LinearCode

variable {n : ℕ}

/--Statement for the STIR Vector IOPP consisting of a field `F`, evaluation domain `ι` and
  degree parameter `degree` -/
structure Statement
  (F : Type) [Field F] [Fintype F] [DecidableEq F]
  (ι : Type) [Fintype ι]
  (degree : ℕ)
  where
    eval : ι → F

/--`OracleStatement` defines the oracle message type for a multi-indexed setting:
  given index type `ιₛ`, base input type `ι`, and field `F`, the output type at each index `i : ιₛ`
  is a function `ι → F` representing an evaluation over `ι`.-/
@[reducible]
def OracleStatement (ιₛ ι F : Type) : ιₛ → Type :=
    fun _ => ι → F

/--Given a statement `stmt` and a collection of oracles, this relation
returns `true` if the distance between the statement's evaluation function `stmt.eval`
and the Reed–Solomon code `code F ι φ degree` is at least `δ`.-/
def stirRelation
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι]
  {degree : ℕ} {ιₛ: Type} (φ : ι ↪ F) (err : ℝ)
  : (Statement F ι degree × ∀ i, (OracleStatement ιₛ ι F i)) → Unit → Prop :=
  let C := code φ degree
  fun ⟨stmt, _oracles⟩ _ =>
    δᵣ(stmt.eval, C) ≤ err

/--Theorem 5.1 : STIR main theorem
  Consider the following ingrediants,
  a security parameter `secpar`
  a ReedSolomon code `RS[F, ι, degree]` with rate `ρ = degree/ |ι|`, where ι is a smooth domain
  a proximity parameter `δ ∈ (0, 1 - 1.05 * √ρ)`
  a folding parameter `k ≥ 4`, being a power of 2
  if `|F| ≤ secpar • 2^{secpar • degree² • |ι|^3.5 / log(1/ρ)}`, then
  there exists a `vector IOPP π` for `RS` with
  with `round by round soundness error ≤ 2 ^ (- secpar)`.
  -/
theorem stir_main
  (secpar : ℕ) [VCVCompatible F]
  {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
  (δ : ℝ) (hδ0 : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
  (k : ℕ) (hk : ∃ m, k = 2 ^ m) (hk4 : 4 ≤ k)
  (hF : Fintype.card F ≤
        secpar • 2 ^ secpar • degree^2 • (Fintype.card ι)^(7/2) /
        Real.log (1 / rate (code φ degree)))
  (vPSpec : ProtocolSpec.VectorSpec n)
  (oSpec : OracleSpec ι) [oSpec.FiniteRange]
  {ιₛ : Type}
  [∀ i, OracleInterface (OracleStatement ιₛ ι F i)]
  (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
  ∃ π : VectorIOP vPSpec F oSpec (Statement F ι degree) Unit (OracleStatement ιₛ ι F),
    IsSecureWithGap (stirRelation φ 0)
                    (stirRelation φ (1 / 2^secpar))
                    ε_rbr π := by sorry

end MainTheorem

section RBRSoundness

open LinearCode

variable {n : ℕ}

/--Lemma 5.4: Round-by-round soundness of the STIR IOPP
  Consider parameters:
  `ι = {ιᵢ}_{i ∈ [M]}` be smooth evaluation domains
  `P : Params ι F` containing required protocol parameters -
    folding parameters `foldingParamᵢ`, embedding `φᵢ`, repetition parameters `repeatParamᵢ`
  `hParams : ParamConditions ι P`, stating conditions that parameters of P must satisfy
  `degreeᵢ = deg / ∏ j<i foldingParamⱼ`, where `deg = degree₀`
  `rateᵢ = degreeᵢ / |ιᵢ|`
  `Codes : CodeParams ι degree P Dist`, containing smooth ReedSolomon codes `RS[F, ιᵢ, degreeᵢ]`
    where `RS[F, ιᵢ, degreeᵢ]` is `(δᵢ,lᵢ)`-list decodable
  for every `f₀ ∉ RS[F, ι₀, degree₀]`,
  `δ₀ ∈ (0, δᵣ(f, RS[F, ι₀, degree₀]) ∩ (1 - BStar(ρ₀)))`
  `∀ i ∈ [M], δᵢ ∈ (0, min{ 1 - ρᵢ - 1/|ιᵢ|, 1 - BStar(ρᵢ)})`
  then there exists a `vector IOPP π` with parameters as above such that
  `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, repeatParam₀)`
  `ε_outᵢ ≤ lᵢ²/2 • (degreeᵢ/ |F| - |ιᵢ|)^s`
  `ε_shiftᵢ ≤ (1 - δ_{i-1})^repeatParam_{i-1} + errStar(degreeᵢ, ρᵢ, δᵢ, t_{i-1} + s)`
    `+ errStar(degreeᵢ/foldingParamᵢ, ρᵢ, δᵢ, repeatParamᵢ)`
  `ε_fin ≤ (1 - δ_M)^repeatParam_M`
  -/
theorem stir_rbr_soundness
    [VCVCompatible F] {ιₒ ιₛ : Type} {s : ℕ}
    {P : Params ι F} {φ : (i : Fin (M+1)) → (ι i ↪ F)}
    {h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)}
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι hParams.deg P Dist}
    (h_not_code : ∀ f₀ : (ι 0) → F, f₀ ∉ (Codes.C 0))
    (hδ₀Le : ∀ f₀ : (ι 0) → F, Dist.δ 0 ≤ (δᵣ(f₀, (Codes.C 0)) : ℝ) ∧
      Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) hParams.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι hParams.deg P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι hParams.deg P j)))))
    (vPSpec : ProtocolSpec.VectorSpec n)
    [∀ i, OracleInterface (OracleStatement ιₛ (ι 0) F i)]
    (oSpec : OracleSpec ιₒ) [oSpec.FiniteRange]
    (ε_fold : ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin (M + 1) → ℝ≥0) (ε_fin : ℝ≥0)
    (ε_sound : ℝ≥0) (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0) :
    -- ∃ vector IOPP π with Statement(F, ι₀, deg), Witness = Unit, OracleStatement(ιₛ, ι₀, F) such that
    ∃ π : VectorIOP vPSpec F oSpec (Statement F (ι 0) (hParams.deg)) Unit (OracleStatement ιₛ (ι 0) F),
    -- ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, repeatParam₀)
      ε_fold ≤ err' F (hParams.deg / P.foldingParam 0) (rate (code (P.φ 0) hParams.deg))
                 (Dist.δ 0) (P.repeatParam 0)
      ∧
      -- ε_outⱼ ≤ lᵢ²/2 • (degreeⱼ/ |F| - |ιⱼ|)^s
      ∀ {j : Fin (M + 1)} (hⱼ : j.val ≠ 0),
        ε_out j ≤ ((Dist.l j : ℝ) ^ 2 / 2) *
          ((degree ι hParams.deg P j : ℝ) / (Fintype.card F - Fintype.card (ι j))) ^ s
        ∧
        -- ε_shiftⱼ ≤ (1 - δ_{j-1})^repeatParam_{j-1}
        -- + errStar(degreeⱼ, ρⱼ, δⱼ, repeatParam_{j-1} + s)
        -- + errStar(degreeⱼ/foldingParamⱼ, ρⱼ, δⱼ, repeatParamⱼ)
        let jPred := predFin j hⱼ
        ε_shift j ≤
          (1 - Dist.δ jPred) ^ (P.repeatParam jPred)  +
          -- err'(degreeⱼ, ρ(codeⱼ), δⱼ, repeatParam_{j-1} + s), where codeⱼ = code φⱼ degreeⱼ
           err' F (degree ι hParams.deg P j) (rate (code (P.φ j) (degree ι hParams.deg P j)))
            (Dist.δ j) (P.repeatParam jPred) + s +
          -- err'(degreeⱼ / foldingParamⱼ, ρ(codeⱼ), δⱼ, repeatParamⱼ)
           err' F ((degree ι hParams.deg P j) / P.foldingParam j)
            (rate (code (P.φ j) (degree ι hParams.deg P j)))
            (Dist.δ j) (P.repeatParam j)
        ∧
        -- ε_fin ≤ (1 - δ_M)^repeatParam_M
        ε_fin ≤ (1 - Dist.δ M) ^ (P.repeatParam M)  :=
by
  sorry

end RBRSoundness

end StirIOP
