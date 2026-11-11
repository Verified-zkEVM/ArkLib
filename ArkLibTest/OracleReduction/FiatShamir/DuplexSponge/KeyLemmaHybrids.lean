import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS DuplexSpongeFS.KeyLemma

section AbortFallback

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : Codec pSpec U] {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]

/-- In `Hyb₄`, an aborting compiled prover behaves exactly like a prover that outputs the
fallback `(default, (SaltCodec.encode default, default))`, which is the proof `hybridGame`
(`Hyb₁`–`Hyb₃`) substitutes and `hybridGameDist` reports on a prover abort. -/
example (V : Verifier oSpec StmtIn StmtOut pSpec) :
    basicFiatShamirGame (U := U) (δ := δ) (Salt := Salt) V failure =
      basicFiatShamirGame (U := U) (δ := δ) (Salt := Salt) V
        (pure (default, (SaltCodec.encode (U := U) (δ := δ) default, default))) := by
  have hfail : (failure : AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) (StmtIn × FSSaltedProof pSpec Salt)) =
      OptionT.mk (pure none) := rfl
  have hpure : ∀ x, (pure x : AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)) (StmtIn × FSSaltedProof pSpec Salt)) =
      OptionT.mk (pure (some x)) := fun _ => rfl
  simp [basicFiatShamirGame, hfail, hpure, OptionT.mk]

end AbortFallback

section VerifierMemo

open DuplexSpongeFS.ProverTransform

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [∀ i, DecidableEq (pSpec.Message i)]
  {T_H T_P : Type} [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
  {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M]

/-- The verifier phase of a hybrid game resumes the prover's `D2SQuery` state but starts its
inner `gImpl` state (Hyb₃'s `tr_i` memo) from `default`, whatever state the prover phase left. -/
example
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (P : MaliciousProver oSpec pSpec StmtIn U δ) :
    hybridGame (T_H := T_H) (T_P := T_P) gImpl V P = (do
      let ⟨proverTriple?, proveQueryLogRaw⟩ ← (simulateQ loggingOracle
        (d2fRaw (T_H := T_H) (T_P := T_P) gImpl P default).run).run
      let ⟨stmtIn, proof, d2sState₁⟩ :=
        match proverTriple? with
        | some ⟨⟨⟨stmtIn, proof⟩, d2sState₁⟩, _⟩ => (stmtIn, proof, d2sState₁)
        | none => (default, default, default)
      let verifierComp := d2fRawFrom (T_H := T_H) (T_P := T_P)
        gImpl (runForwardVerifierWide δ V stmtIn proof) d2sState₁ (default : M)
      let ⟨verifierTriple?, verifyQueryLogRaw⟩ ←
        (simulateQ loggingOracle verifierComp.run).run
      let stmtOut? :=
        match verifierTriple? with
        | some ⟨⟨stmtOut?, _⟩, _⟩ => stmtOut?
        | none => none
      let taggedP := (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
        proveQueryLogRaw).map fun e => (SourceTag.prover, e)
      let taggedV := (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
        verifyQueryLogRaw).map fun e => (SourceTag.verifier, e)
      return ⟨stmtIn, ← stmtOut?.getM, proof, taggedP ++ taggedV⟩) := rfl

end VerifierMemo

section MemoMiss

open DuplexSpongeFS.ProverTransform

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [codec : Codec pSpec U] {δ : ℕ}
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- The `default` memo is empty. -/
example : (default : D2SAlgoMemo StmtIn U δ Salt pSpec) = [] := rfl

/-- From the empty memo, a Hyb₃ `gᵢ` call is a memo miss: it runs the codec bridge
`ψ⁻¹ ∘ f ∘ φ⁻¹`, which queries `fᵢ`, and records the answer. (On a memo hit the call is `pure`
and queries nothing; that was the verifier's behavior when it resumed the prover's memo.) -/
example (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    (d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) q).run [] =
      (do
        let r ← d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) q
        pure (r, [D2SAlgoMemoEntry.mk q.1 q.2.1
          (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) q.2.2.1) q.2.2.2 r])) := by
  simp [d2sCodecBridgeImplMemo, lookupD2SAlgoMemo, insertD2SAlgoMemo]

end MemoMiss
