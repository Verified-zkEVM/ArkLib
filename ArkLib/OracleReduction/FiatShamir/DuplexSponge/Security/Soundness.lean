/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.FiatShamir.SingleSalt
import ArkLib.ToVCVio.Tactic.VCVNorm

/-!
# Soundness and Knowledge Soundness of Duplex Sponge Fiat–Shamir (CO25 §6)

This file formalizes Theorems 6.1 and 6.2 from CO25 and Construction 6.3.

## Main results

- **Theorem 6.1** (`duplex_sponge_fiat_shamir_soundness`): if the interactive proof IP has
  state-restoration soundness, then the DSFS scheme is sound with the repaired Section-6 error
  `κ + ηStarTotal`, where the collision budget is
  `max(t, L_totalRateBlocks δ pSpec + 1)` and includes the salt blocks.

- **Construction 6.3** (`dsfsStraightlineExtractor`): straightline extractor that
  reconstructs the IP transcript from the DSFS proof (via the sponge) and calls the IP SR
  extractor `E_IP` on the reconstructed transcript and separated prover/verifier logs.

- **Theorem 6.2** (`theorem_6_2_straightline`): if IP has SR-KS, then the DSFS scheme has
  straightline KS (via Construction 6.3) with error `κ + ηStarTotal`, concluding CO25 Def 3.6
  (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG, query-bounded.

## Proof strategy

```
DSFS KS game  ≈  Hyb_0   (oracle identification using hyb0Init/hyb0Impl)
Hyb_0 ≈ Hyb_4 + η★        (Key Lemma 5.1)
Hyb_4 = IP SR game        (fsChallengeOracle = srChallengeOracle, alias)
IP SR game ≤ κ             (IP SR-soundness/KS hypothesis)
```

The Section 5 proof is deliberately outside this file. Both public theorems take
`KeyLemmaSecurityWitness` explicitly; all remaining steps, including the Fiat–Shamir lifting
through Theorems 3.18 and 3.19, are proved here. This keeps the Section 6 derivations free of
`sorryAx` while making Lemma 5.1 the visible deferred boundary.

## Type-level compatibility

- `Verifier.duplexSpongeFiatShamirSalted δ V` is a `NonInteractiveVerifier` (0
  challenge rounds), so its `srChallengeOracle` is empty and SR prover = plain
  `OracleComp` against `duplexSpongeChallengeOracle` = `MaliciousProver`.

- `hyb0Init`/`hyb0Impl oSpecImpl` (from `KeyLemma.lean`) are the canonical
  `(init, impl)` for `Verifier.soundness`/`.knowledgeSoundness` on the DSFS verifier.

- `fsChallengeOracle = srChallengeOracle` (alias), so `Hyb_4`'s oracle IS the
  SR challenge oracle for the salt-augmented IP `saltedIPVerifier V`.
-/

open OracleComp OracleSpec ProtocolSpec

-- `vcv_norm` / `vcv_strip_log` / `vcv_init_peel` / `vcv_congr` / `vcv` / `vcv_event` are global
-- tactics from `ArkLib.ToVCVio.Tactic.VCVNorm`; their supporting lemmas live in the
-- `ToVCVio.VCVNorm` namespace.
open ToVCVio.VCVNorm
  (simulateQ_bind_congr logging_strip₂ logging_strip₃ simulateQ_optionT_map optionT_liftM_eq_lift
   simulateQ_optionT_mk)

/-- **Probability transfer across total-variation distance** (the `Pr`-level form of
`tvDist`).  For any event `p` and two probabilistic computations, the event probability under
`mx` is at most its probability under `my` plus `tvDist mx my`.  This is the standard fact
`μ(E) ≤ ν(E) + d_TV(μ, ν)`, lifted from VCVio's `Bool`-valued
`abs_probOutput_toReal_sub_le_tvDist` to a general `Prop`-valued event via the indicator map
`b ↦ decide (p b)`. -/
theorem probEvent_le_probEvent_add_ofReal_tvDist
    {β : Type} (mx my : ProbComp β) (p : β → Prop) :
    Pr[ p | mx] ≤ Pr[ p | my] + ENNReal.ofReal (tvDist mx my) := by
  classical
  -- Indicator map collapsing the event to a `Bool`.
  let g : β → Bool := fun b => decide (p b)
  -- `Pr[= true | g <$> mz] = Pr[p | mz]` for any `mz`.
  have key : ∀ mz : ProbComp β, Pr[= true | g <$> mz] = Pr[ p | mz] := by
    intro mz
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_ext fun x _ => ?_
    simp [g, Function.comp]
  -- Bool-level transfer, then rewrite via `key`, then absorb `tvDist_map_le`.
  have hbool := abs_probOutput_toReal_sub_le_tvDist (g <$> mx) (g <$> my)
  rw [key mx, key my] at hbool
  have hmap : tvDist (g <$> mx) (g <$> my) ≤ tvDist mx my := tvDist_map_le g mx my
  have hreal : Pr[ p | mx].toReal ≤ Pr[ p | my].toReal + tvDist mx my := by
    have hle := (abs_le.mp hbool).2
    linarith
  -- Lift the real inequality back to `ℝ≥0∞`.
  have hd : 0 ≤ tvDist mx my := tvDist_nonneg mx my
  have ha : Pr[ p | mx] ≠ ⊤ := probEvent_ne_top
  have hb : Pr[ p | my] ≠ ⊤ := probEvent_ne_top
  have hsum_ne : Pr[ p | my] + ENNReal.ofReal (tvDist mx my) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩
  refine (ENNReal.toReal_le_toReal ha hsum_ne).mp ?_
  rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hd]
  exact hreal

/-- **Averaging / law-of-total-probability bound** (reusable toolkit). If the event `q` has
probability at most `r` under `f a` for *every* intermediate value `a`, then it has probability at
most `r` under `mx >>= f`, no matter how `mx` is distributed. -/
theorem probEvent_bind_le_const {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (q : β → Prop) (r : ENNReal) (h : ∀ a, Pr[ q | f a] ≤ r) :
    Pr[ q | mx >>= f] ≤ r := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' a, Pr[= a | mx] * Pr[ q | f a]
      ≤ ∑' a, Pr[= a | mx] * r := by gcongr with a; exact h a
    _ = (∑' a, Pr[= a | mx]) * r := ENNReal.tsum_mul_right
    _ ≤ 1 * r := by gcongr; exact tsum_probOutput_le_one
    _ = r := one_mul r

namespace DuplexSpongeFS

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage
open DuplexSpongeFS.KeyLemma

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U]
  {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

noncomputable section

-- Sampling structures carry computational data, so the `VCVCompatible` bridges are installed
-- only in this section rather than exported as global instances.
local instance : SampleableType U := VCVCompatible.toSampleableType
local instance (i : pSpec.ChallengeIdx) : SampleableType (pSpec.Challenge i) :=
  VCVCompatible.toSampleableType

/-! ## Section 6 error bound -/

/-- CO25 Section 6's uniform error function. `max t (L + 1)` accounts for the verifier's
deterministic permutation trace in addition to the malicious prover's total query budget `t`. -/
def ηStarTotal (U : Type) [SpongeUnit U] [Fintype U]
    (t L : ℕ) (εcodec : CodecBias (pSpec := pSpec)) : ℝ :=
  let T : ℝ := (max t (L + 1) : ℕ)
  let cardPow : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  25 * T ^ 2 / cardPow
    + (t : ℝ) * iSup (fun i => (εcodec i : ℝ))
    + ∑ i, (εcodec i : ℝ)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- The exact Lemma 5.1 error is bounded by the Section 6 error whenever the three oracle-family
budgets fit within the total malicious-prover budget `t`. -/
lemma etaStar_le_etaStarTotal (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L t : ℕ) (εcodec : CodecBias (pSpec := pSpec)) (hTotal : tₕ + tₚ + tₚᵢ ≤ t) :
    ηStar U tₕ tₚ tₚᵢ L εcodec ≤ ηStarTotal U t L εcodec := by
  let x : ℝ := (tₕ + tₚ + tₚᵢ : ℕ)
  let l : ℝ := (L : ℝ) + 1
  let T : ℝ := (max t (L + 1) : ℕ)
  let q : ℝ := ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C
  have hx0 : 0 ≤ x := by positivity
  have hl0 : 0 ≤ l := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hxt : x ≤ (t : ℝ) := by
    dsimp [x]
    exact_mod_cast hTotal
  have htT : (t : ℝ) ≤ T := by
    dsimp [T]
    exact_mod_cast Nat.le_max_left t (L + 1)
  have hlT : l ≤ T := by
    dsimp [l, T]
    norm_cast
    exact Nat.le_max_right t (L + 1)
  have hxT : x ≤ T := hxt.trans htT
  have hxx : x ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_nonneg (T - x)]
  have hll : l ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_nonneg (T - l)]
  have hxl : l * x ≤ T ^ 2 := by
    calc
      l * x ≤ l * T := mul_le_mul_of_nonneg_left hxT hl0
      _ ≤ T * T := mul_le_mul_of_nonneg_right hlT hT0
      _ = T ^ 2 := by ring
  have hnumerator :
      7 * x ^ 2 + 28 * l * x + 14 * l ^ 2 - 3 * x - 13 * l ≤ 50 * T ^ 2 := by
    nlinarith
  have hcardNat : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ⟨0⟩
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hperm :
      (7 * x ^ 2 + 28 * l * x + 14 * l ^ 2 - 3 * x - 13 * l) / (2 * q)
        ≤ 25 * T ^ 2 / q := by
    have hdiv := div_le_div_of_nonneg_right hnumerator (le_of_lt (by positivity : 0 < 2 * q))
    have hrewrite : 50 * T ^ 2 / (2 * q) = 25 * T ^ 2 / q := by
      field_simp
      ring
    rwa [hrewrite] at hdiv
  have htₚt : (tₚ : ℝ) ≤ (t : ℝ) := by
    have : tₚ ≤ t := by omega
    exact_mod_cast this
  have hcodecNonneg : 0 ≤ iSup (fun i => (εcodec i : ℝ)) := by
    exact Real.iSup_nonneg fun _ => NNReal.zero_le_coe
  have hcodec :
      (tₚ : ℝ) * iSup (fun i => (εcodec i : ℝ))
        ≤ (t : ℝ) * iSup (fun i => (εcodec i : ℝ)) :=
    mul_le_mul_of_nonneg_right htₚt hcodecNonneg
  unfold ηStar ηStarTotal θStar
  change
    (7 * x ^ 2 + 28 * l * x + 14 * l ^ 2 - 3 * x - 13 * l) / (2 * q)
        + (tₚ : ℝ) * iSup (fun i => (εcodec i : ℝ)) + ∑ i, (εcodec i : ℝ)
      ≤ 25 * T ^ 2 / q + (t : ℝ) * iSup (fun i => (εcodec i : ℝ)) + ∑ i, (εcodec i : ℝ)
  gcongr

/-- The explicit Section 5 boundary consumed by Theorems 6.1 and 6.2. Keeping the unproved
Lemma 5.1 obligation as an argument makes the Section 6 derivations independently axiom-free. -/
structure KeyLemmaSecurityWitness
    [DecidableEq ι]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ) : Prop where
  valid : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
    IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
      tvDist
          (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver
            (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
          (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver
            (ProverTransform.d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        ≤ ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias
      ∧ IsD2SAlgoChallengeQueryBound
          (ProverTransform.d2sAlgo (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) maliciousProver)
          (θStar tₕ tₚ tₚᵢ)

/-!
## Construction 6.3: DSFS straightline extractor

`saltedIPVerifier`, `langInSalted`, and `relInSalted` are defined in
`ArkLib.OracleReduction.FiatShamir.SingleSalt` (available here via `KeyLemma`'s import).
-/

/-- CO25 **Construction 6.3** — DSFS straightline extractor, built from the **basic-FS NARG-KS
extractor `E_std`** (delivered by Theorem 3.19,
`single_salt_fiat_shamir_straightline_knowledge_soundness`). -/
noncomputable def dsfsStraightlineExtractor
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      UnitSampleM (U := U) (α := WitIn)) :
    -- Bare straightline-extractor shape; query-spec is just the `(Unit →ₒ U)` sampler (Def 3.14:
    -- the extractor reads challenges from the trace, queries no challenge oracle).
    StmtIn →
      FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        UnitSampleM (U := U) (α := WitIn) :=
  fun stmtIn transcript proveQueryLog verifyQueryLog =>
    let taggedP := proveQueryLog.map fun e => (SourceTag.prover, e)
    let taggedV := verifyQueryLog.map fun e => (SourceTag.verifier, e)
    let queryLog : TaggedQueryLog _ := taggedP ++ taggedV
    -- The single P→V message *is* the DSFS proof `(τ, messages)`; regroup as a basic-FS proof.
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := transcript 0
    let fsProof : FSSaltedProof pSpec Salt := (SaltCodec.encode saltedProof.1, saltedProof.2)
    do
      -- step 1: `tr_std := D2STrace(tr ‖ tr_𝒱)` (real `d2sTraceSalted`; samples 𝒰(Σ)).  On a
      -- bad-trace abort (paper `tr = ⊥`), fall back to the EMPTY trace and still run `E_std`,
      -- matching `mappedDSFSGameDist`/`Hyb₀`'s `none → []` branch (the bad event is bounded in η★,
      -- not a special extractor path) — so the §6.2 game-match `hL1` is an exact equality.
      let tr_std_raw? ← OptionT.lift
        (d2sTraceSalted (T_H := T_H) (T_P := T_P) (Salt := Salt) (δ := δ)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          queryLog).run
      let tr_std_raw := tr_std_raw?.getD []
      -- step 2: split into prover / verifier logs (both already bare `oSpec + srChallenge`).
      -- `E_std` reads only this *oracle* transcript (Def 3.14); the prover's `𝒰(Σ)`/`unifSpec`
      -- sampling coins are never part of what the extractor sees, matching the coin-stripped
      -- (`tr.fst`) feed in `adaptiveNARGKnowledgeSoundnessExpWithCoins`.
      let tr_stdP := TaggedQueryLog.proverLog tr_std_raw
      let tr_stdV : QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) :=
        TaggedQueryLog.verifierLog tr_std_raw
      -- steps 3-4: run `E_std` (Thm 3.19) on `(tr_stdP, tr_stdV)` — same `(Unit →ₒ U)` spec.
      E_std stmtIn fsProof tr_stdP tr_stdV

/-! ## Theorem 6.1: IP SR-soundness → DSFS soundness -/

/-- The **false-acceptance event** for the DSFS soundness game, read off a
`BasicFiatShamirGameOutput` (the common output type of `Hyb_0` … `Hyb_4`): the malicious prover
submitted a statement `stmtIn ∉ langIn` yet the verifier accepted into `stmtOut ∈ langOut`.
`none` (an aborted run) is not a soundness break. -/
def dsfsSoundnessEvent (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) → Prop
  | some out => out.1 ∉ langIn ∧ out.2.1 ∈ langOut
  | none => False

/-- The **raw** false-acceptance event on a `DSFSGameOutput`, matching CO25's
`ε_NARG = Pr[ |𝕩| ≤ n ∧ 𝕩 ∉ ℒ(ℛ) ∧ 𝒱^{h,p}(𝕩,π) = 1 ]`. Same shape as `dsfsSoundnessEvent`,
but on the duplex-sponge game output *before* the §5.8 line-4 trace map is applied. -/
def dsfsRawEvent (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) → Prop
  | some out => out.1 ∉ langIn ∧ out.2.1 ∈ langOut
  | none => False

/-- **The DSFS scheme as a NARG verifier** — the verify map `𝒱^{h,p}(𝕩, ·)` of the duplex-sponge FS
NARG, packaged in CO25 Def 3.5/3.6 shape (`StmtIn → Proof → OptionT (OracleComp …) StmtOut`).  This
is exactly the verify portion of `dsfsGame` (the §5.8 forward verifier `runForwardVerifierWide`, as
an `OptionT`); using it as the `verify` argument of `adaptiveNARGSoundness` /
`adaptiveNARGKnowledgeSoundness` makes those Def-3.5/3.6 notions *be about the DSFS NARG* (prover =
`MaliciousProver`, oracle spec `oSpec + duplexSpongeChallengeOracle StmtIn U`).  The DSFS scheme's
NARG experiment then equals `dsfsGameDist`/`dsfsKSGameDist` up to the marginalized prover/verify
query logs — see `dsfsNargSoundnessExp_eq_dsfsGame` / `dsfsNargKSExp_eq_dsfsKSGame`. -/
def dsfsNargVerify (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → DSSaltedProof (pSpec := pSpec) (U := U) δ →
      OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) StmtOut :=
  fun stmtIn proof => OptionT.mk (runForwardVerifierWide δ V stmtIn proof)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [VCVCompatible Salt] [VCVCompatible U] [DecidableEq StmtIn] [DecidableEq U] in
/-- `Verifier.dsfsNargNIV`'s `verify` on the length-1 transcript is definitionally the bare §5.8
forward verifier `dsfsNargVerify V x π` (`Fin.cons … 0 = π` by `rfl`).  Lets the game-equivalence
proofs below recover their `dsfsNargVerify`-form goal via `simp only [dsfsNargNIV_verify]` after
unfolding a NIV-shaped `adaptiveNARG*Exp … (Verifier.dsfsNargNIV δ V)` experiment. -/
lemma dsfsNargNIV_verify (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    (Verifier.dsfsNargNIV δ V).verify x (Fin.cons π (fun i => i.elim0))
      = dsfsNargVerify V x π :=
  rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- **CO25 §6.1 step L1** — `ε_NARG = Pr[Hyb₀]`. -/
theorem dsfsGame_falseAccept_eq_hyb0
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sTraceTransform : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    Pr[ dsfsRawEvent langIn langOut |
        dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver]
      = Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sTraceTransform] := by
  classical
  -- Expose `Hyb₀ = dsfsGameDist >>= F`, then decompose both probabilities over the game output `a`.
  unfold hyb_0 mappedDSFSGameDist
  rw [probEvent_bind_eq_tsum]
  conv_lhs => rw [← bind_pure (dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver)]
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  congr 1
  -- Per game output `a`: the post-processor `F a` and the raw event agree on `(𝕩, stmtOut)`.
  rcases a with _ | ⟨stmtIn, stmtOut, proof, fullTraceDS⟩
  · -- aborted game run: both sides reject.
    simp [dsfsRawEvent, dsfsSoundnessEvent]
  · -- accepting run: trace map keeps `(stmtIn, stmtOut)`; event is constant over the trace
    -- sampling.
    rw [probEvent_bind_of_const _
      (r := if stmtIn ∉ langIn ∧ stmtOut ∈ langOut then (1 : ENNReal) else 0)
      (fun o _ => by
        rcases o with _ | t <;>
          by_cases h : stmtIn ∉ langIn ∧ stmtOut ∈ langOut <;>
          simp [dsfsSoundnessEvent, h])]
    simp [dsfsRawEvent]
    by_cases h : stmtIn ∉ langIn ∧ stmtOut ∈ langOut <;> simp [h]

/-! ### Canonical state-restoration oracle model matching `Hyb_4`

`Hyb_4` samples its Fiat–Shamir oracle eagerly from `D_IP_salted = OracleDistribution.uniform
(fsChallengeOracle (StmtIn × Salt) pSpec)`, whose carrier `OracleFamily (fsChallengeOracle …) =
(q : Domain) → Range q` is *definitionally* `QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id`
(recall `fsChallengeOracle = srChallengeOracle` and `Id α = α`).  The two definitions below package
that same uniform-function model as the `(init, impl)` pair consumed by
`Verifier.StateRestoration.soundness`, so the IP's SR-soundness hypothesis is stated against
exactly the oracle distribution `Hyb_4` uses. -/

/-- Canonical SR challenge-oracle `init` matching `Hyb_4`'s eager `𝒟_IP_salted` sampling:
draw one uniform Fiat–Shamir challenge function. -/
def srInitDIP :
    ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) :=
  (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec).sample

/-- Canonical SR shared-oracle handler: answer `oSpec` queries via `oSpecImpl`, ignoring the
(pre-sampled, never-mutated) challenge function held in the state — matching the `.inl` branch of
`hybChallengeImpl`. -/
def srImplLift (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
  fun q => StateT.lift (oSpecImpl q)

/-- The sampler for `D2SAlgo`'s private coins `(Unit →ₒ U) + unifSpec`: alphabet samples via
`d2sUnitSampleImpl`, uniform `unifSpec` samples forwarded. This is the `auxImpl` that the
coin-bearing SR-soundness experiment uses to answer the compiled prover's coins — exactly what
`hybChallengeImpl`'s auxiliary branches do in `Hyb₄`. -/
def d2sAuxImpl [SampleableType U] :
    QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp :=
  d2sUnitSampleImpl.addLift (fun q => (query (spec := unifSpec) q : ProbComp _))

/-- The §6.1 canonical SR handler for `Hyb₄`'s oracle model, written as an explicit 4-slot handler
(avoiding nested-`addLift` elaboration): `oSpec` via `srImplLift oSpecImpl`, the pre-sampled FS
challenge function via `srChallengeQueryImpl'`, `D2SAlgo`'s `(Unit →ₒ U)` coins via
`d2sUnitSampleImpl`, and its `unifSpec` coins forwarded.  This is exactly the per-slot reduction of
`(srImplLift oSpecImpl).addLift (srChallengeQueryImpl'.addLift d2sAuxImpl)` used by
`coinSRExperimentProb` (each `addLift` slot unfolds via `add_apply_inl/inr` + `liftTarget`). -/
def srHyb4Impl (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec + ((Unit →ₒ U) + unifSpec)))
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
  fun
  | .inl qS => StateT.lift (oSpecImpl qS)
  | .inr (.inl qC) => srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec) qC
  | .inr (.inr (.inl qU)) => StateT.lift (d2sUnitSampleImpl (U := U) qU)
  | .inr (.inr (.inr qN)) => StateT.lift (query (spec := unifSpec) qN)

omit [SpongeUnit U] [SpongeSize] [SaltCodec U δ Salt] codec [DecidableEq StmtIn] [DecidableEq U] in
/-- **DSFS §6.1 handler identity.** The eager 4-slot hybrid handler `hybChallengeImpl` for the
salted FS oracle `𝒟_IP_salted` answers each of its four query slots *exactly* as the canonical SR
handler `srHyb4Impl`.  The only non-`rfl` slot is the challenge oracle: the eagerly-sampled uniform
function-table answers a query by applying the table
(`𝒟_IP_salted.toImpl k q = tableQueryImpl k q = pure (k q)`), which is precisely
`srChallengeQueryImpl'`; the other three slots are `StateT.lift`s of the same per-slot samplers
(the eager `get` is discarded). -/
theorem hybChallengeImpl_eq_srAddLift (oSpecImpl : QueryImpl oSpec ProbComp) :
    hybChallengeImpl (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
        oSpecImpl (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec)
      = srHyb4Impl oSpecImpl := by
  ext q : 1
  rcases q with qS | qC | qU | qN
  · -- `oSpec` slot: `StateT.lift (oSpecImpl qS)` (the eager `get` is discarded).
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift]
    rfl
  · -- challenge slot: `𝒟_IP_salted.toImpl k qC = pure (k qC)`, matching `srChallengeQueryImpl'`.
    funext s
    simp only [hybChallengeImpl, srHyb4Impl, srChallengeQueryImpl', D_IP_salted]
    rfl
  · -- `(Unit →ₒ U)` coin slot: `StateT.lift (d2sUnitSampleImpl qU)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift]
    rfl
  · -- `unifSpec` coin slot: `StateT.lift (query unifSpec qN)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift]
    rfl

/-- Regroups the oracle sum for spec restoration. -/
def srReassocImpl :
    QueryImpl (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec + ((Unit →ₒ U) + unifSpec)))
      (OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))) :=
  fun
  | .inl qO => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inl qO))
  | .inr (.inl qC) => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inr qC))
  | .inr (.inr qA) => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inr qA)

/-- Reassociate a wide Hyb₄ query log in the same way as `srReassocImpl`. -/
private def srReassocQueryLog
    (log : QueryLog (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
      ((Unit →ₒ U) + unifSpec)))) :
    QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) +
      ((Unit →ₒ U) + unifSpec)) :=
  log.map fun
    | ⟨.inl q, r⟩ => ⟨.inl (.inl q), r⟩
    | ⟨.inr (.inl q), r⟩ => ⟨.inl (.inr q), r⟩
    | ⟨.inr (.inr q), r⟩ => ⟨.inr q, r⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem srReassocQueryLog_fst
    (log : QueryLog (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
      ((Unit →ₒ U) + unifSpec)))) :
    (srReassocQueryLog log).fst =
      filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) log := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨q, r⟩ := e
    rcases q with q | q | q
    · change _ :: (srReassocQueryLog log).fst =
        _ :: filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) log
      rw [ih]
    · change _ :: (srReassocQueryLog log).fst =
        _ :: filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) log
      rw [ih]
    · change (srReassocQueryLog log).fst =
        filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) log
      exact ih

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem withQueryLog_simulateQ_srReassoc_query
    (q : (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
      ((Unit →ₒ U) + unifSpec))).Domain) :
    (simulateQ loggingOracle
        (simulateQ srReassocImpl
          (liftM (OracleSpec.query q) : OracleComp
            (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
              ((Unit →ₒ U) + unifSpec))) _))).run =
      (fun p => (p.1, srReassocQueryLog p.2)) <$>
        simulateQ srReassocImpl
          (simulateQ loggingOracle
            (liftM (OracleSpec.query q) : OracleComp
              (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
                ((Unit →ₒ U) + unifSpec))) _)).run := by
  rcases q with q | q | q <;>
    simp [srReassocImpl, OracleSpec.loggingOracle, QueryImpl.withLogging_apply,
      WriterT.run_tell, srReassocQueryLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem withQueryLog_simulateQ_srReassoc {α : Type}
    (X : OracleComp (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
      ((Unit →ₒ U) + unifSpec))) α) :
    (simulateQ loggingOracle (simulateQ srReassocImpl X)).run =
      (fun p => (p.1, srReassocQueryLog p.2)) <$>
        simulateQ srReassocImpl (simulateQ loggingOracle X).run := by
  induction X using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    rw [simulateQ_bind]
    change (simulateQ srReassocImpl
        (liftM (OracleSpec.query q) : OracleComp _ _) >>= fun r =>
          simulateQ srReassocImpl (k r)).withQueryLog = _
    rw [OracleComp.withQueryLog_bind]
    have hq := withQueryLog_simulateQ_srReassoc_query
      (StmtIn := StmtIn) (U := U) (Salt := Salt) q
    change (simulateQ srReassocImpl
        (liftM (OracleSpec.query q) : OracleComp _ _)).withQueryLog = _ at hq
    rw [hq, OracleComp.run_simulateQ_loggingOracle_query_bind]
    have hqSource := OracleComp.withQueryLog_query q
    change (simulateQ loggingOracle
        (liftM (OracleSpec.query q) : OracleComp _ _)).run = _ at hqSource
    rw [hqSource]
    simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, map_bind, bind_map_left,
      pure_bind, bind_assoc]
    refine bind_congr fun r => ?_
    have hih := ih r
    change (simulateQ srReassocImpl (k r)).withQueryLog = _ at hih
    rw [hih]
    simp [srReassocQueryLog]

/-- Embed a basic-FS query log into the wide Hyb₄ oracle sum. -/
private def liftFSQueryLog
    (log : QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) :
    QueryLog (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec +
      ((Unit →ₒ U) + unifSpec))) :=
  log.map fun
    | ⟨.inl q, r⟩ => ⟨.inl q, r⟩
    | ⟨.inr q, r⟩ => ⟨.inr (.inl q), r⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem filter_liftFSQueryLog
    (log : QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) :
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
      (liftFSQueryLog (U := U) log) = log := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    obtain ⟨q, r⟩ := e
    rcases q with q | q
    · change _ :: filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
        (liftFSQueryLog (U := U) log) = _ :: log
      rw [ih]
    · change _ :: filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
        (liftFSQueryLog (U := U) log) = _ :: log
      rw [ih]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem withQueryLog_simulateQ_liftFS_query
    (q : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain) :
    (simulateQ loggingOracle
        (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
          (liftM (OracleSpec.query q) :
            OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) _))).run =
      (fun p => (p.1, liftFSQueryLog (U := U) p.2)) <$>
        simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
          (simulateQ loggingOracle
            (liftM (OracleSpec.query q) :
              OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) _)).run := by
  rcases q with q | q <;>
    simp [liftFSSaltedQueriesToD2SChallengePlusUnit, OracleSpec.loggingOracle,
      QueryImpl.withLogging_apply, WriterT.run_tell, liftFSQueryLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem withQueryLog_simulateQ_liftFS {α : Type}
    (X : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) α) :
    (simulateQ loggingOracle
        (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U)) X)).run =
      (fun p => (p.1, liftFSQueryLog (U := U) p.2)) <$>
        simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
          (simulateQ loggingOracle X).run := by
  induction X using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    rw [simulateQ_bind]
    change (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
        (liftM (OracleSpec.query q) : OracleComp _ _) >>= fun r =>
          simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U)) (k r)).withQueryLog = _
    rw [OracleComp.withQueryLog_bind]
    have hq := withQueryLog_simulateQ_liftFS_query
      (StmtIn := StmtIn) (U := U) (Salt := Salt) q
    change (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
        (liftM (OracleSpec.query q) : OracleComp _ _)).withQueryLog = _ at hq
    rw [hq, OracleComp.run_simulateQ_loggingOracle_query_bind]
    have hqSource := OracleComp.withQueryLog_query q
    change (simulateQ loggingOracle
        (liftM (OracleSpec.query q) : OracleComp _ _)).run = _ at hqSource
    rw [hqSource]
    simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, map_bind, bind_map_left,
      pure_bind, bind_assoc]
    refine bind_congr fun r => ?_
    have hih := ih r
    change (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
      (k r)).withQueryLog = _ at hih
    rw [hih]
    simp [liftFSQueryLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] codec
  [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
private theorem filter_withQueryLog_simulateQ_liftFS {α : Type}
    (X : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) α) :
    (fun p => (p.1,
        filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) p.2)) <$>
        (simulateQ loggingOracle
          (simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U)) X)).run =
      simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit (U := U))
        (simulateQ loggingOracle X).run := by
  rw [withQueryLog_simulateQ_liftFS]
  simp only [Functor.map_map, filter_liftFSQueryLog, Prod.eta]
  change id <$> _ = _
  rw [id_map]

omit [VCVCompatible StmtIn] [SpongeUnit U] [SpongeSize] [∀ i, VCVCompatible (pSpec.Message i)]
  [SaltCodec U δ Salt] codec [VCVCompatible Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- **§6.1 infra lemma 1 — prover spec-reassoc collapse.** Composing the SR experiment
handler with the associator `srReassocImpl` recovers the eager `Hyb₄` handler. -/
theorem srHyb4Impl_eq_expHandler_compose_srReassoc (oSpecImpl : QueryImpl oSpec ProbComp) :
    ((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
            (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
          QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
              (d2sAuxImpl (U := U)) :
        QueryImpl ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) ∘ₛ
        srReassocImpl)
      = srHyb4Impl oSpecImpl := by
  ext q : 1
  rcases q with qO | qC | (qU | qN)
  · funext s
    simp only [QueryImpl.apply_compose, srReassocImpl]
    rw [simulateQ_HasQuery_query]
    simp only [srHyb4Impl, QueryImpl.addLift, StateT.lift,
      ChallengeIdx, Challenge, QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_self]
    change StateT.run (liftM (oSpecImpl qO) : StateT _ ProbComp _) s = _
    rw [StateT.run_liftM]
    rfl
  · funext s
    simp only [QueryImpl.apply_compose, srReassocImpl]
    rw [simulateQ_HasQuery_query]
    simp only [srHyb4Impl, QueryImpl.addLift, srChallengeQueryImpl',
      ChallengeIdx, Challenge, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      PFunctor.Handler.liftTarget_self]
  · funext s
    simp only [QueryImpl.apply_compose, srReassocImpl]
    rw [simulateQ_HasQuery_query]
    simp only [srHyb4Impl, QueryImpl.addLift, d2sAuxImpl, StateT.lift,
      QueryImpl.add_apply_inr, PFunctor.Handler.liftTarget_self]
    change StateT.run (liftM (d2sUnitSampleImpl (U := U) qU) : StateT _ ProbComp _) s = _
    rw [StateT.run_liftM]
    rfl
  · funext s
    simp only [QueryImpl.apply_compose, srReassocImpl]
    rw [simulateQ_HasQuery_query]
    simp only [srHyb4Impl, QueryImpl.addLift, d2sAuxImpl, StateT.lift,
      QueryImpl.add_apply_inr, PFunctor.Handler.liftTarget_self]
    change StateT.run
      (liftM (query (spec := unifSpec) qN : ProbComp _) : StateT _ ProbComp _) s = _
    rw [StateT.run_liftM]
    rfl

omit [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [DecidableEq U] codec in
/-- **§6.1 infra lemma 2 — verifier transcript-routing collapse.** The eager `Hyb₄` handler
composed with `liftFSSaltedQueriesToD2SChallengePlusUnit` equals the bare SR verifier handler. -/
theorem expVerifyHandler_eq_hybChallengeImpl_compose_liftFS (oSpecImpl : QueryImpl oSpec ProbComp) :
    ((hybChallengeImpl (oSpec := oSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
          oSpecImpl (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec))
        ∘ₛ liftFSSaltedQueriesToD2SChallengePlusUnit)
      = ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
          (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
        QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) := by
  ext q : 1
  rcases q with qO | qC <;>
    funext s <;>
    simp [QueryImpl.compose, liftFSSaltedQueriesToD2SChallengePlusUnit,
      QueryImpl.addLift, srImplLift, srChallengeQueryImpl', StateT.lift] <;>
    simp [hybChallengeImpl, D_IP_salted, StateT.lift] <;>
    rfl

/-- The compiled prover `D2SAlgo^f(𝒫̃)` as a coin-bearing NARG prover for the single-salt FS:
de-abort with `default` (matching `basicFiatShamirGame`'s `·.getD default`), then `srReassocImpl`
regroups `oSpec + (chal + aux) → (oSpec + chal) + aux`.  No output reassoc (the NARG prover output
`StmtIn × FSSaltedProof` is the compiled prover's output verbatim). -/
def nargInducedProver
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt) :=
  simulateQ srReassocImpl ((fun o => o.getD default) <$> (d2sAlgoTransform maliciousProver).run)

/-- Basic-FS challenge queries in the regrouped single-salt prover surface. -/
def isSaltedFSChallengeQuery :
    ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- Aggregate bound on the basic-FS challenge calls of a regrouped single-salt prover. -/
abbrev IsSaltedFSChallengeQueryBound {α : Type}
    (prover : OracleComp
      ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) α)
    (t : ℕ) : Prop := by
    classical
    exact OracleComp.IsQueryBoundP prover
      (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
        (pSpec := pSpec) (U := U)) t

omit [SpongeSize] in
/-- Predicate-bound transport through a stateless query simulation.  Unlike VCVio's generic
lemma, this proof does not assume the target oracle surface is uniformly samplable: regrouping
only forwards queries, and the ambient `oSpec` is intentionally arbitrary in §6. -/
private theorem isQueryBoundP_simulateQ_of_step
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α : Type} {p : ι₁ → Prop} [DecidablePred p] {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec₁ (OracleComp spec₂)}
    {oa : OracleComp spec₁ α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → OracleComp.IsQueryBoundP (impl t) q 1)
    (hstep_np : ∀ t, ¬ p t → OracleComp.IsQueryBoundP (impl t) q 0) :
    OracleComp.IsQueryBoundP (simulateQ impl oa) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      have hlift : OracleComp.IsQueryBoundP (impl t) q (if p t then 1 else 0) := by
        by_cases hpt : p t
        · simpa [if_pos hpt] using hstep_p t hpt
        · simpa [if_neg hpt] using hstep_np t hpt
      have hrest : ∀ u, OracleComp.IsQueryBoundP (simulateQ impl (mx u)) q
          (if p t then n - 1 else n) := fun u => ih u (h.2 u)
      have hbound : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by
        by_cases hpt : p t
        · simp only [if_pos hpt]
          rcases h.1 with hnp | hn
          · exact absurd hpt hnp
          · omega
        · simp only [if_neg hpt]
          omega
      simpa [hbound] using OracleComp.isQueryBoundP_bind hlift (fun u _ => hrest u)

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] codec
  [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- Regrouping the D2S output preserves its aggregate basic-FS challenge-query budget. -/
private theorem isSaltedFSChallengeBound_nargInducedProver
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {t : ℕ}
    (hBound : IsD2SAlgoChallengeQueryBound (d2sAlgoTransform maliciousProver) t) :
    IsSaltedFSChallengeQueryBound (nargInducedProver maliciousProver d2sAlgoTransform) t := by
  classical
  unfold nargInducedProver
  rw [simulateQ_map]
  change OracleComp.IsQueryBoundP
    ((fun o => o.getD default) <$> simulateQ srReassocImpl
      (d2sAlgoTransform maliciousProver).run)
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) t
  rw [OracleComp.isQueryBoundP_map_iff]
  refine isQueryBoundP_simulateQ_of_step hBound ?_ ?_
  · rintro (qO | qC | qA) hq
    · simp [isD2SAlgoChallengeQuery] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 1
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengeQuery] at hq
  · rintro (qO | qC | qA) hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengeQuery] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] codec
  [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- The single-salt SR-KS wrapper only repackages the compiled prover's output, so it preserves
the same aggregate basic-FS challenge-query bound. -/
private theorem isSaltedFSChallengeBound_srInducedProverKS
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {t : ℕ}
    (hBound : IsD2SAlgoChallengeQueryBound (d2sAlgoTransform maliciousProver) t) :
    IsSaltedFSChallengeQueryBound
      (srInducedProverKS (nargInducedProver maliciousProver d2sAlgoTransform)) t := by
  classical
  rw [srInducedProverKS_eq_map]
  change OracleComp.IsQueryBoundP
    ((fun p => ((p.1, p.2.1), p.2.2, ())) <$>
      nargInducedProver maliciousProver d2sAlgoTransform)
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) t
  rw [OracleComp.isQueryBoundP_map_iff]
  exact isSaltedFSChallengeBound_nargInducedProver maliciousProver d2sAlgoTransform hBound

/-- The basic-FS prover class produced by a fixed D2S algorithm transform. -/
def basicFSCompiledKSBound
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt) → Prop :=
  fun prover => ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
    IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ ∧
      prover = nargInducedProver maliciousProver d2sAlgoTransform

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U] codec
  [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- The Lemma-5.1 output bound places every compiled prover in the corresponding SR-KS class. -/
private theorem basicFSCompiledKSBound_to_sr
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hD2SBound : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        IsD2SAlgoChallengeQueryBound (d2sAlgoTransform maliciousProver) (θStar tₕ tₚ tₚᵢ))
    (prover : OracleComp
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt))
    (hBound : basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ prover) :
    IsSaltedFSChallengeQueryBound (srInducedProverKS prover) (θStar tₕ tₚ tₚᵢ) := by
  classical
  obtain ⟨maliciousProver, hMaliciousBound, rfl⟩ := hBound
  exact isSaltedFSChallengeBound_srInducedProverKS maliciousProver d2sAlgoTransform
    (hD2SBound maliciousProver hMaliciousBound)

omit codec [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- Theorem 3.19 instantiated with the compiled provers supplied by Lemma 5.1.  Isolating this
typed instantiation keeps Theorem 6.2's hybrid calculation independent of elaborator details. -/
theorem basicFS_straightlineKS_withCompiledBound
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (tₕ tₚ tₚᵢ : ℕ)
    (hD2SBound : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        IsD2SAlgoChallengeQueryBound (d2sAlgoTransform maliciousProver) (θStar tₕ tₚ tₚᵢ))
    (ε_sr : ENNReal)
    (h_IP_SR_KS : Verifier.StateRestoration.knowledgeSoundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (relInSalted relIn) (unitOutputRelation langOut) (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins (WitIn := WitIn)
      (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
      (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
        srChallengeQueryImpl')
      d2sAuxImpl (d2sUnitSampleImpl (U := U))
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      relIn langOut
      (bound := basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ)
      ε_sr := by
  classical
  exact single_salt_fiat_shamir_straightline_knowledge_soundness
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (WitIn := WitIn)
    (pSpec := pSpec) (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl
    (Unit →ₒ U) (d2sUnitSampleImpl (U := U)) V relIn langOut
    (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
    (srBound := fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ))
    (bound := basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ)
    (hBound := basicFSCompiledKSBound_to_sr d2sAlgoTransform tₕ tₚ tₚᵢ hD2SBound)
    (ε := ε_sr) (h_sr_ks := h_IP_SR_KS)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [SpongeUnit U]
  [SpongeSize] [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Message i)] [SaltCodec U δ Salt]
  codec [DecidableEq StmtIn] [DecidableEq U] in
/-- **§6.1 infra lemma 3 — `basicFSVerifierComp` IS `fsSaltedVerify` routed through `liftFS`.** -/
theorem basicFSVerifierComp_eq_simulateQ_liftFS
    (V : Verifier oSpec StmtIn StmtOut pSpec) (p : StmtIn × FSSaltedProof pSpec Salt) :
    basicFSVerifierComp (Salt := Salt) (U := U) V p
      = simulateQ (liftFSSaltedQueriesToD2SChallengePlusUnit
          (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((fsSaltedVerify (Salt := Salt) V p.1 p.2).run) := rfl

omit [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] codec in
/-- **§6.1 HELPER — `Hyb₄` proj-marginal = induced coin-NARG-experiment distribution.** The heart
of `hyb4_eq_coinNARGgame` as a *distribution* equality, abstracting the FS↔SR handler identities
and `OptionT` plumbing. -/
theorem hyb4_hdist
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (Option.map (fun o : BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt) => (o.1, o.2.1))) <$>
      hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
        d2sAlgoTransform
      = adaptiveNARGSoundnessExpWithCoins
          (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
          ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
            (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))) d2sAuxImpl
          (Verifier.singleSaltFiatShamir (Salt := Salt) V)
          (nargInducedProver maliciousProver d2sAlgoTransform) := by
  classical
  unfold hyb_4 basicFiatShamirGameDist adaptiveNARGSoundnessExpWithCoins
  -- `Verifier.singleSaltFiatShamir`'s verify is defeq to `fsSaltedVerify` (`fsSaltedNIV_verify`);
  simp only [hybChallengeInit, srInitDIP, fsSaltedNIV_verify]
  rw [map_bind]
  refine bind_congr fun s => ?_
  rw [← StateT.run'_map', ← simulateQ_map]
  simp only [nargInducedProver, simulateQ_map]
  -- `hsm`: `simulateQ H` commutes with the `OptionT` functor map as the `Option.map` of its image.
  -- (Now the reusable global lemma `simulateQ_optionT_map`, not a local `have`.)
  -- `keyA_hyb4`: proj-marginal of `basicFiatShamirGame` = clean double-`loggingOracle` strip.
  -- `simp only [-loggingOracle.run_simulateQ_bind_fst]; vcv_norm` does the whole normalization
  -- (plumbing + value-marginal log strip); no local
  -- `hgetM`/`helim` `have`s and no explicit `logging_strip₂` rewrite are needed.
  have keyA_hyb4 :
      ((fun o : BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt) => (o.1, o.2.1)) <$>
        basicFiatShamirGame V (d2sAlgoTransform maliciousProver) :
        OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec))) (StmtIn × StmtOut))
      = OptionT.mk ((d2sAlgoTransform maliciousProver).run >>= fun a =>
          basicFSVerifierComp V (a.getD default) >>= fun b =>
            pure (b.map (fun st => ((a.getD default).1, st)))) := by
    apply OptionT.ext
    rw [OptionT.run_map]
    unfold basicFiatShamirGame
    vcv_norm
    rfl
  -- Assemble: collapse both handlers to `Hyb₄`/`SR`, then reconcile the LHS (base-monad bind, from
  -- `keyA`) and RHS (the experiment's `OptionT` body) by reducing to `.run` and expanding both into
  -- the common base-monad bind-tree.
  refine congrArg (fun c => StateT.run' c s) ?_
  rw [← simulateQ_optionT_map, keyA_hyb4]
  -- Phase 1 — push `simulateQ` to the leaves and collapse the **prover** handler
  -- (`ExpHandler ∘ₛ srReassoc → Hyb₄`) and the **LHS verifier**
  -- (`basicFSVerifierComp = fsSaltedVerify` via `liftFS`, then `expVerifyHandler_eq_…`).
  -- `OptionT.mk` is unfolded so the LHS bind and the experiment's verify expose their bodies.
  simp only [OptionT.mk, optionT_liftM_eq_lift, simulateQ_bind, simulateQ_optionT_bind,
    simulateQ_optionT_lift, simulateQ_map, simulateQ_pure,
    ← QueryImpl.simulateQ_compose, srHyb4Impl_eq_expHandler_compose_srReassoc,
    ← hybChallengeImpl_eq_srAddLift, basicFSVerifierComp_eq_simulateQ_liftFS,
    expVerifyHandler_eq_hybChallengeImpl_compose_liftFS]
  -- Phase 2 — collapse the **RHS verifier**: `d2sAuxImpl`'s target differs from `SR`'s, so the
  -- `.addLift` is a `liftTarget` sum; unfold it (`addLift_def`), drop the trivial `SR` `liftTarget`
  -- (`liftTarget_self`), then strip the auxiliary lift (`simulateQ_add_liftComp_left`).
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left]
  -- Phase 3 — reconcile the two bind presentations: reduce to `.run` and expand the RHS `OptionT`
  -- binds (`OptionT.run_*`) into base-monad binds, matching the LHS read-out.
  apply OptionT.ext (m := StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)
  simp only [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_map_left,
    pure_bind, bind_assoc, Option.elim_some]
  simp only [OptionT.run]
  -- Final read-out: `pure (Option.map (·,·) x_1)` (LHS) = `x_1.elim (pure none) (fun st =>
  -- pure (…))`
  -- (RHS, the `OptionT`-bind short-circuit), via `simulateQ_pure` + `optionT_elim_pure_map`.
  refine bind_congr fun x => bind_congr fun x_1 => ?_
  cases x_1 <;> rfl

omit [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] codec in
/-- **CO25 §6.1 step L3a — `Hyb₄ = basic-FS NARG game`.** `Hyb₄` (the eager basic-FS game on the
compiled prover) equals the coin-bearing NARG soundness experiment (CO25 Def 3.5) for the induced
prover, under the canonical model. -/
theorem hyb4_eq_coinNARGgame
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform]
      = Pr[ (fun out => match out with
              | some (x, s) => x ∉ langIn ∧ s ∈ langOut
              | none => False) |
          adaptiveNARGSoundnessExpWithCoins
            (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
              (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))) d2sAuxImpl
            (Verifier.singleSaltFiatShamir (Salt := Salt) V)
            (nargInducedProver maliciousProver d2sAlgoTransform) ] := by
  classical
  -- `dsfsSoundnessEvent` reads `(𝕩, stmtOut)` off the `BasicFiatShamirGameOutput`; that is the
  -- `projBFS`-image, so it suffices to equate the *distributions* on that marginal (`hdist`).
  have hev : ((fun out => match out with
          | some (x, s) => x ∉ langIn ∧ s ∈ langOut
          | none => False) ∘
        Option.map (fun o : BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt) => (o.1, o.2.1)))
      = dsfsSoundnessEvent langIn langOut := by
    funext o; rcases o with _ | out <;> rfl
  have hdist := hyb4_hdist V oSpecImpl maliciousProver d2sAlgoTransform
  calc Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform]
      = Pr[ ((fun out => match out with
              | some (x, s) => x ∉ langIn ∧ s ∈ langOut
              | none => False) ∘
            Option.map (fun o : BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt) => (o.1, o.2.1))) |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform] := by rw [hev]
    _ = Pr[ (fun out => match out with
              | some (x, s) => x ∉ langIn ∧ s ∈ langOut
              | none => False) |
          Option.map (fun o : BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt) => (o.1, o.2.1)) <$>
            hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
              oSpecImpl V maliciousProver d2sAlgoTransform] := by rw [probEvent_map]
    _ = Pr[ (fun out => match out with
              | some (x, s) => x ∉ langIn ∧ s ∈ langOut
              | none => False) |
          adaptiveNARGSoundnessExpWithCoins
            (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
              (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))) d2sAuxImpl
            (Verifier.singleSaltFiatShamir (Salt := Salt) V)
            (nargInducedProver maliciousProver d2sAlgoTransform) ] := by rw [hdist]

omit codec [SaltCodec U δ Salt] [DecidableEq StmtIn] [DecidableEq U] in
/-- **CO25 §6.1 step L3 (two-hop):** false acceptance in `Hyb₄` is bounded by the basic-FS NARG
soundness error.  Combines `hyb4_eq_coinNARGgame` (L3a) with the coin-bearing NARG soundness
hypothesis (delivered by Thm 3.18 from IP SR soundness, L3b) applied to the induced prover. -/
theorem hyb4_falseAccept_le_nargSoundness
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
    (hD2SBound : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        IsD2SAlgoChallengeQueryBound (d2sAlgoTransform maliciousProver)
          (θStar tₕ tₚ tₚᵢ))
    (ε_sr : ENNReal)
    -- Coin-bearing IP SR soundness (the same hypothesis as
    -- `duplex_sponge_fiat_shamir_soundness`).
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
        (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform] ≤ ε_sr := by
  classical
  -- L3b: FS NARG soundness from IP SR soundness (Thm 3.18), coin-bearing.
  have h_NARG := single_salt_fiat_shamir_soundness
    (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl V
    langIn langOut (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
    (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ))
    (fun prover => ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ ∧
        prover = nargInducedProver maliciousProver d2sAlgoTransform)
    (fun prover hProver => by
      classical
      obtain ⟨maliciousProver, hBound, rfl⟩ := hProver
      rw [srInducedProver_eq_map]
      change OracleComp.IsQueryBoundP
        ((fun p => ((p.1, p.2.1), p.2.2)) <$>
          nargInducedProver maliciousProver d2sAlgoTransform)
        (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
          (pSpec := pSpec) (U := U)) (θStar tₕ tₚ tₚᵢ)
      rw [OracleComp.isQueryBoundP_map_iff]
      exact isSaltedFSChallengeBound_nargInducedProver maliciousProver d2sAlgoTransform
        (hD2SBound maliciousProver hBound))
    ε_sr h_IP_SR_sound
  -- L3a: Hyb₄ = the coin-bearing NARG game; apply NARG soundness to the induced prover.
  rw [hyb4_eq_coinNARGgame V oSpecImpl langIn langOut maliciousProver d2sAlgoTransform]
  exact h_NARG (nargInducedProver maliciousProver d2sAlgoTransform)
    ⟨maliciousProver, hMaliciousBound, rfl⟩

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- **DSFS NARG soundness experiment = sponge soundness game** (CO25 §6 game-equivalence).  The
Def-3.5 experiment for the DSFS NARG (`adaptiveNARGSoundnessExp` at the NARG verifier
`Verifier.dsfsNargNIV δ V`)
and the duplex-sponge game `dsfsGameDist` assign the same false-acceptance probability: both run the
malicious prover then the §5.8 forward verifier and read off `(𝕩, stmtOut)`, differing only in the
(event-irrelevant) prover/verify query logs that `dsfsGame` records via `loggingOracle`.  Provable
by `loggingOracle` value-marginalization. -/
theorem dsfsNargSoundnessExp_eq_dsfsGame
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargSoundFailEvent langIn langOut |
        adaptiveNARGSoundnessExp hyb0Init (hyb0Impl oSpecImpl)
          (Verifier.dsfsNargNIV δ V) maliciousProver ]
      = Pr[ dsfsRawEvent langIn langOut |
          dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver ] := by
  classical
  -- The §5.8 forward verifier read-out `(𝕩, stmtOut)` is the `proj`-marginal of the sponge game
  -- output `DSFSGameOutput`; the events agree under it, so it suffices to equate the
  -- *distributions* on that marginal (`hdist`) — where the `loggingOracle` logs are dropped.
  have hev2 : (nargSoundFailEvent langIn langOut) ∘
        (Option.map (fun out : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) => (out.1, out.2.1)))
      = dsfsRawEvent langIn langOut := by
    funext o; rcases o with _ | out <;> rfl
  have hdist :
      adaptiveNARGSoundnessExp hyb0Init (hyb0Impl oSpecImpl)
          (Verifier.dsfsNargNIV δ V) maliciousProver
        = Option.map (fun out : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) => (out.1, out.2.1)) <$>
          dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver := by
    -- `keyA`: the experiment's `OptionT`-body equals the `proj`-image of `dsfsGame` — the two run
    -- the same prover + forward verifier; `dsfsGame`'s only extra is the `loggingOracle` logs,
    -- which
    -- `proj` drops and `run_simulateQ_bind_fst` then strips.  Stated with the *OptionT* functor
    -- so `OptionT.ext` exposes `.run` and the `OptionT.run_*` lemmas fire.
    have keyA :
        ((do
          let ⟨x, π⟩ ← maliciousProver
          let stmtOut ← dsfsNargVerify V x π
          return (x, stmtOut)) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) (StmtIn × StmtOut))
        = (fun out : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) => (out.1, out.2.1)) <$>
          dsfsGame V maliciousProver := by
      unfold dsfsNargVerify dsfsGame
      apply OptionT.ext
      have hgetM : ∀ (o : Option StmtOut),
          OptionT.run (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) o.getM
            = pure o := fun o => by cases o <;> rfl
      have helim : ∀ {γ : Type} (g : StmtOut → γ) (o : Option StmtOut),
          (o.elim (pure none) (fun s => pure (some (g s))) :
            OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option γ))
            = pure (o.map g) :=
        fun g o => by cases o <;> rfl
      simp only [OptionT.run_bind, Option.elimM, OptionT.run_monadLift, monadLift_eq_self,
        OptionT.run_mk, OptionT.run_pure, pure_bind, bind_map_left, map_bind,
        Option.elim_some, hgetM, helim, map_pure]
      rw [loggingOracle.run_simulateQ_bind_fst (oa := maliciousProver)
            (ob := fun p => (simulateQ loggingOracle (runForwardVerifierWide δ V p.1 p.2)).run >>=
              fun s => pure (Option.map (fun a => (p.1, a)) s.1))]
      refine bind_congr fun p => ?_
      rw [loggingOracle.run_simulateQ_bind_fst (oa := runForwardVerifierWide δ V p.1 p.2)
            (ob := fun s? => pure (Option.map (fun a => (p.1, a)) s?))]
    -- `hsm`: `simulateQ` commutes with the `OptionT` functor map as the `Option.map` of its image —
    -- bridges `keyA`'s `OptionT`-functor to the `Option.map`/`ProbComp`-functor of the goal.
    have hsm : ∀ {β γ : Type} (f : β → γ)
        (m : OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) β),
        simulateQ (hyb0Impl oSpecImpl) ((f <$> m : OptionT _ γ))
          = Option.map f <$> simulateQ (hyb0Impl oSpecImpl) m := by
      intro β γ f m
      rw [← simulateQ_map]; congr 1; apply OptionT.ext; rw [OptionT.run_map]; rfl
    unfold adaptiveNARGSoundnessExp dsfsGameDist
    -- `Verifier.dsfsNargNIV`'s verify is defeq to `dsfsNargVerify` (`Fin.cons … 0 = π`); rewrite to
    -- the bare-function form so `keyA` matches.
    simp only [dsfsNargNIV_verify]
    rw [keyA, hsm]
    simp only [StateT.run'_map', ← map_bind]
  calc Pr[ nargSoundFailEvent langIn langOut |
        adaptiveNARGSoundnessExp hyb0Init (hyb0Impl oSpecImpl)
          (Verifier.dsfsNargNIV δ V) maliciousProver ]
      = Pr[ nargSoundFailEvent langIn langOut |
          Option.map (fun out : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) => (out.1, out.2.1)) <$>
            dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver ] := by rw [hdist]
    _ = Pr[ (nargSoundFailEvent langIn langOut) ∘
            (Option.map (fun out : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) => (out.1, out.2.1))) |
          dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver ] := by rw [probEvent_map]
    _ = Pr[ dsfsRawEvent langIn langOut |
          dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver ] := by rw [hev2]

/-- **Theorem 6.1** — Soundness of the duplex-sponge Fiat–Shamir scheme.
For a malicious prover whose three DSFS oracle-family budgets fit in the total budget `t`, its
false-acceptance probability `ε_NARG` is at most `ε_sr + η★(t, L)`, where the Section-6 error
uses `max(t, L_totalRateBlocks δ pSpec + 1)` to include the salted verifier's deterministic
collision-analysis trace. -/
theorem duplex_sponge_fiat_shamir_soundness
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (tₕ tₚ tₚᵢ : ℕ)
    (t : ℕ) (hTotal : tₕ + tₚ + tₚᵢ ≤ t)
    (ε_sr : ENNReal)
    (hKeyLemma : KeyLemmaSecurityWitness (δ := δ) (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (T_H := T_H) (T_P := T_P) oSpecImpl V tₕ tₚ tₚᵢ)
    -- IP SR-soundness against coin-bearing provers (canonical model `Hyb_4` uses: FS oracle sampled
    -- uniformly by `srInitDIP`, `oSpec` by `oSpecImpl`, the `D2SAlgo` coins by `d2sAuxImpl`).
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
      -- ε_NARG(λ, (tₕ,tₚ,tₚ⁻¹), n) — CO25 **Def 3.5** as a property of the DSFS NARG *verifier*
      -- `Verifier.dsfsNargNIV δ V` (= `𝒱^{h,p}`), query-bounded attacker.
      (Verifier.dsfsNargNIV δ V).adaptiveNARGSoundness
        (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
        langIn langOut
        (bound := fun maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ =>
          IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ)
        (ε_sr + ENNReal.ofReal
          (ηStarTotal U t (L_totalRateBlocks δ pSpec) codec.decodingBias)) := by
  -- CO25 Def 3.5 (`adaptiveNARGSoundness`) at the DSFS NARG verifier `Verifier.dsfsNargNIV δ V`:
  -- unfold the `∀`-quantifier over query-bounded provers, then run the §6.1 hybrid proof verbatim.
  intro maliciousProver hBound
  -- Step 0: the DSFS NARG soundness experiment (Def 3.5) IS the sponge game `dsfsGameDist` on the
  -- false-acceptance marginal (`dsfsNargSoundnessExp_eq_dsfsGame`); rewrite to the sponge game
  -- so the §6.1 hybrid calc applies verbatim.
  rw [dsfsNargSoundnessExp_eq_dsfsGame V oSpecImpl langIn langOut maliciousProver]
  -- Seam #1 (Theorem 5.1 / Key Lemma): use the explicit Section 5 hypothesis with its concrete
  -- D2SAlgo prover transform and D2STrace map.
  let d2sAlgoTransform := ProverTransform.d2sAlgo
    (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  let d2sTraceTransform := d2sTraceSalted
    (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  have hKeyProver := hKeyLemma.valid maliciousProver hBound
  have hTv := hKeyProver.1
  -- L3 (paper two-hop): false acceptance in Hyb₄ ≤ basic-FS NARG soundness (L3a) ≤ IP SR
  -- soundness ε_sr (L3b, Thm 3.18). Matches CO25 §6.1 Eq. lines 1950–1957.
  have hL3 := hyb4_falseAccept_le_nargSoundness V oSpecImpl langIn langOut
    maliciousProver d2sAlgoTransform tₕ tₚ tₚᵢ hBound
    (fun maliciousProver hBound => by
      simpa only [d2sAlgoTransform] using (hKeyLemma.valid maliciousProver hBound).2)
    ε_sr h_IP_SR_sound
  -- §6.1 derivation (`hKeyLemma` at L2, `hyb4_falseAccept_le_nargSoundness` at L3):
  --   ε_NARG = Pr[ |𝕩|≤n ∧ 𝕩∉ℒ(ℛ) ∧ 𝒱^{h,p}(𝕩,π)=1 | (h,p,p⁻¹)←𝒟_𝔖; (𝕩,π)←𝒫̃^{h,p,p⁻¹} ]
  --     = Pr[ ... | Hyb₀ ]                                   -- (L1) trace map preserves acceptance
  --     ≤ Pr[ 𝒱_std^f(𝕩,π)=1 ∧ 𝕩∉ℒ | f←𝒟_IP; (𝕩,π)←D2SAlgo^f(𝒫̃) ] + η★   -- (L2, Thm 5.1)
  --     ≤ ε_IP^sr(δ⋆, θ⋆(tₕ,tₚ,tₚ⁻¹), n) + η★                 -- (L3, Hyb₄ ≡ IP SR game; direct)
  calc Pr[ dsfsRawEvent langIn langOut |
        dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver]
      = Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sTraceTransform] :=
        dsfsGame_falseAccept_eq_hyb0 V oSpecImpl langIn langOut maliciousProver
          d2sTraceTransform
    _ ≤ Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal
              (tvDist
                (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sTraceTransform)
                (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sAlgoTransform)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal
            (ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hTv)
        -- (L3, Hyb₄ ≡ IP SR game) ≤ ε_IP^sr(δ⋆, θ⋆, n) + η★ — directly from SR soundness.
    _ ≤ ε_sr + ENNReal.ofReal
          (ηStar U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec) codec.decodingBias) :=
        add_le_add hL3 (le_refl _)
    _ ≤ ε_sr + ENNReal.ofReal
          (ηStarTotal U t (L_totalRateBlocks δ pSpec) codec.decodingBias) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal
          (etaStar_le_etaStarTotal U tₕ tₚ tₚᵢ (L_totalRateBlocks δ pSpec)
            t codec.decodingBias hTotal))


end

end DuplexSpongeFS
