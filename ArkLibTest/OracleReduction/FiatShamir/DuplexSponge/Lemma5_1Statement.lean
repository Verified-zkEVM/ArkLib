/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

/-!
# Regression tests for the Lemma 5.1 interfaces

`Lemma5_1Statement` consumes `NondegenerateRounds`, `IsLemma5_1QueryBound`, `ηStar` and
`θStar`. The sponge examples pin the facts behind the `NondegenerateRounds` docstring.
-/

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS DuplexSpongeFS.KeyLemma

section Statement

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : Codec pSpec U] {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U] [∀ i, DecidableEq (pSpec.Message i)]
  {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- `Lemma5_1Statement` takes the nondegenerate-schedule and query-bound hypotheses and gives
the `η★` distance bound and the `θ★` query bound. -/
example (oSpecImpl : QueryImpl oSpec ProbComp) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ)
    (h : Lemma5_1Statement (U := U) (δ := δ) (Salt := Salt) T_H T_P oSpecImpl V
      tₕ tₚ tₚᵢ)
    (hND : NondegenerateRounds pSpec) (P : MaliciousProver oSpec pSpec StmtIn U δ)
    (hP : IsLemma5_1QueryBound P tₕ tₚ tₚᵢ) :
    IsD2SAlgoChallengeQueryBound
      (ProverTransform.d2sAlgo (Salt := Salt) (T_H := T_H) (T_P := T_P) P)
      (θStar tₕ tₚ tₚᵢ) :=
  (h hND P hP).2

/-- The "Moreover" clause of Lemma 5.1 is a theorem: `D2SAlgo(𝒫̃)` makes at most `θ★ = t_p`
challenge queries. -/
example (P : MaliciousProver oSpec pSpec StmtIn U δ) (tₕ tₚ tₚᵢ : ℕ)
    (hP : IsLemma5_1QueryBound P tₕ tₚ tₚᵢ) :
    IsD2SAlgoChallengeQueryBound
      (ProverTransform.d2sAlgo (Salt := Salt) (T_H := T_H) (T_P := T_P) P)
      (θStar tₕ tₚ tₚᵢ) :=
  isD2SAlgoChallengeQueryBound_d2sAlgo P tₕ tₚ tₚᵢ hP

/-- A prover that makes no oracle query compiles to a `D2SAlgo` prover that makes no challenge
query. -/
example (out : StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsD2SAlgoChallengeQueryBound
      (ProverTransform.d2sAlgo (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (pure out : MaliciousProver oSpec pSpec StmtIn U δ)) 0 :=
  isD2SAlgoChallengeQueryBound_d2sAlgo (pure out) 0 0 0 ⟨trivial, trivial, trivial⟩

end Statement

section SpongeZeroLength

variable {U : Type} [SpongeUnit U] [SpongeSize] (sponge : CanonicalDuplexSponge U)

/-- A zero-length challenge leaves no trace: `squeeze 0` returns the sponge unchanged. -/
example : DuplexSponge.squeeze sponge 0 = pure (#v[], sponge) := rfl

/-- A zero-length message does not disappear: `absorb []` queries nothing but sets
`squeezePos := R`, so the next squeeze permutes. -/
example : DuplexSponge.absorb sponge [] =
    pure { sponge with squeezePos := Fin.last SpongeSize.R } := rfl

end SpongeZeroLength
