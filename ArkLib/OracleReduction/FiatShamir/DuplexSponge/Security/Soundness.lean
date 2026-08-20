/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.FiatShamir.SingleSalt
import ArkLib.ToVCVio.Tactic.VCVNorm

/-!
# Soundness and Knowledge Soundness of Duplex Sponge Fiat–Shamir (CO25 §6)

This file formalizes Theorems 6.1 and 6.2 from CO25 and Construction 6.3.

## Main results

- **Theorem 6.1** (`theorem_6_1_soundness`): if the interactive proof IP has
  state-restoration soundness, then the DSFS scheme is sound with error `κ + η★`.

- **Construction 6.3** (`dsfsStraightlineExtractor`): straightline extractor that
  reconstructs the IP transcript from the DSFS proof (via the sponge) and calls the IP SR
  extractor `E_IP` (with `default` logs, matching the SR-KS experiment).

- **Theorem 6.2** (`theorem_6_2_straightline`): if IP has SR-KS, then the DSFS scheme has
  straightline KS (via Construction 6.3) with error `κ + η★`, concluding CO25 Def 3.6
  (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG, query-bounded.

## Proof strategy

```
DSFS KS game  ≈  Hyb_0   (oracle identification using hyb0Init/hyb0Impl)
Hyb_0 ≈ Hyb_4 + η★        (Key Lemma 5.1)
Hyb_4 = IP SR game        (fsChallengeOracle = srChallengeOracle, alias)
IP SR game ≤ κ             (IP SR-soundness/KS hypothesis)
```

Steps 1–2 use `lemma_5_1`.  Step 3 (Hyb_4 = IP SR game) requires the
**Fiat–Shamir lifting theorem** — currently
absent from `Implications.lean`.  See `SingleSalt.lean` for the single-salt
version (`theorem_3_18_soundness`, `theorem_3_19_straightline_ks`), from which
these theorems follow as corollaries.

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

/-- Compose the five high-level inequalities in the revised §6.2 route without unfolding any
hybrid.  Keeping this arithmetic shell polymorphic is intentional: the Section 6 proof should
depend only on the endpoint interfaces, not on definitional equality of large game programs. -/
theorem hybridKSBound_of_bridges
    {α β : Type} (M : ProbComp β) (H0 H4Absorbing H4Legacy : ProbComp α)
    (k : α → ProbComp β) (target : ProbComp β) (event : β → Prop)
    (ε : ENNReal) (η : ℝ)
    (hL1 : Pr[ event | M] = Pr[ event | H0 >>= k])
    (hTV : tvDist H0 H4Absorbing ≤ η)
    (hAbsorbing : Pr[ event | H4Absorbing >>= k] ≤ Pr[ event | H4Legacy >>= k])
    (hL3 : Pr[ event | H4Legacy >>= k] = Pr[ event | target])
    (hTarget : Pr[ event | target] ≤ ε) :
    Pr[ event | M] ≤ ε + ENNReal.ofReal η := by
  calc
    Pr[ event | M]
      = Pr[ event | H0 >>= k] := hL1
    _ ≤ Pr[ event | H4Absorbing >>= k]
          + ENNReal.ofReal (tvDist (H0 >>= k) (H4Absorbing >>= k)) :=
      probEvent_le_probEvent_add_ofReal_tvDist (H0 >>= k) (H4Absorbing >>= k) event
    _ ≤ Pr[ event | H4Absorbing >>= k] + ENNReal.ofReal (tvDist H0 H4Absorbing) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le k H0 H4Absorbing))
    _ ≤ Pr[ event | H4Absorbing >>= k] + ENNReal.ofReal η :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal hTV)
    _ ≤ Pr[ event | H4Legacy >>= k] + ENNReal.ofReal η :=
      add_le_add hAbsorbing le_rfl
    _ = Pr[ event | target] + ENNReal.ofReal η := by rw [hL3]
    _ ≤ ε + ENNReal.ofReal η := add_le_add hTarget le_rfl

namespace DuplexSpongeFS

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage
open DuplexSpongeFS.KeyLemma

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : CodecCore pSpec U]
  {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

noncomputable section

-- The `Fintype`/`DecidableEq` instances below are not referenced in the theorem *types*, but
-- are required in the proof *bodies* (by `dsfsStraightlineExtractor` and `lemma_5_1`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
## Construction 6.3: DSFS straightline extractor

`saltedIPVerifier`, `langInSalted`, and `relInSalted` are defined in
`ArkLib.OracleReduction.FiatShamir.SingleSalt` (available here via `KeyLemma`'s import).
-/

/-- CO25 **Construction 6.3** — DSFS straightline extractor, built from the **basic-FS NARG-KS
extractor `E_std`** (delivered by Theorem 3.19, `theorem_3_19_straightline_ks`). -/
noncomputable def dsfsStraightlineExtractor
    [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      UnitSampleM (U := U) (α := WitIn)) :
    -- Bare straightline-extractor shape; query-spec is just the `(Unit →ₒ U)` sampler (Def 3.14:
    -- the extractor reads challenges from the trace, queries no challenge oracle).
    StmtIn → WitOut →
      FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        UnitSampleM (U := U) (α := WitIn) :=
  fun stmtIn witOut transcript proveQueryLog verifyQueryLog =>
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
      E_std stmtIn witOut fsProof tr_stdP tr_stdV

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

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
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
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
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
      (fun o _ => by rcases o with _ | t <;> simp [dsfsSoundnessEvent])]
    simp [dsfsRawEvent]

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
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
    rfl
  · -- challenge slot: `𝒟_IP_salted.toImpl k qC = pure (k qC)`, matching `srChallengeQueryImpl'`.
    funext s
    simp only [hybChallengeImpl, srHyb4Impl, srChallengeQueryImpl', D_IP_salted,
      OracleReduction.OracleDistribution.uniform, OracleReduction.OracleDistribution.functionTable,
      OracleReduction.tableQueryImpl]
    rfl
  · -- `(Unit →ₒ U)` coin slot: `StateT.lift (d2sUnitSampleImpl qU)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
    rfl
  · -- `unifSpec` coin slot: `StateT.lift (query unifSpec qN)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
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
  rcases q with qO | qC | (qU | qN) <;>
    funext s <;>
    simp [QueryImpl.compose, srReassocImpl, srHyb4Impl, QueryImpl.addLift, srImplLift, d2sAuxImpl,
      srChallengeQueryImpl', StateT.lift] <;>
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
  rw [hybChallengeImpl_eq_srAddLift]
  ext q : 1
  rcases q with qO | qC <;>
    funext s <;>
    simp [QueryImpl.compose, liftFSSaltedQueriesToD2SChallengePlusUnit,
      QueryImpl.addLift, srImplLift, srChallengeQueryImpl', StateT.lift] <;>
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

instance : DecidablePred
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) := by
  classical
  exact fun _ => inferInstance

/-- Aggregate bound on the basic-FS challenge calls of a regrouped single-salt prover. -/
abbrev IsSaltedFSChallengeQueryBound {α : Type}
    (prover : OracleComp
      ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) α)
    (t : ℕ) : Prop :=
  by
    classical
    exact OracleComp.IsQueryBoundP prover
      (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
        (pSpec := pSpec) (U := U)) t

/-- Predicate-bound transport through a stateless query simulation. -/
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

/-- Regrouping the D2S output preserves its aggregate basic-FS challenge-query budget. -/
private theorem isSaltedFSChallengeBound_nargInducedProver
    [DecidableEq ι]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ) :
    IsSaltedFSChallengeQueryBound (nargInducedProver maliciousProver d2sAlgoTransform)
      (θStar tₕ tₚ tₚᵢ) := by
  classical
  unfold nargInducedProver
  rw [simulateQ_map]
  change OracleComp.IsQueryBoundP
    ((fun o => o.getD default) <$> simulateQ srReassocImpl
      (d2sAlgoTransform maliciousProver).run)
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) (θStar tₕ tₚ tₚᵢ)
  rw [OracleComp.isQueryBoundP_map_iff]
  refine isQueryBoundP_simulateQ_of_step hBound ?_ ?_
  · rintro (qO | qC | qA) hq
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 1
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
  · rintro (qO | qC | qA) hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]

/-- The DSFS proof-only attacker as a **Def-3.6 NARG adversary**. -/
def nargInducedProverKS [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt × WitOut) :=
  simulateQ srReassocImpl
    ((fun o => let p := o.getD default; (p.1, p.2, (default : WitOut))) <$>
      (d2sAlgoTransform maliciousProver).run)

/-- The KS output repackaging does not affect the compiled prover's challenge-query budget. -/
private theorem isSaltedFSChallengeBound_nargInducedProverKS
    [DecidableEq ι] [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ) :
    IsSaltedFSChallengeQueryBound (nargInducedProverKS (WitOut := WitOut)
      maliciousProver d2sAlgoTransform) (θStar tₕ tₚ tₚᵢ) := by
  classical
  unfold nargInducedProverKS
  rw [simulateQ_map]
  change OracleComp.IsQueryBoundP
    ((fun o => let p := o.getD default; (p.1, p.2, (default : WitOut))) <$>
      simulateQ srReassocImpl (d2sAlgoTransform maliciousProver).run)
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) (θStar tₕ tₚ tₚᵢ)
  rw [OracleComp.isQueryBoundP_map_iff]
  refine isQueryBoundP_simulateQ_of_step hBound ?_ ?_
  · rintro (qO | qC | qA) hq
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 1
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
  · rintro (qO | qC | qA) hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]
    · simp [isD2SAlgoChallengePoint, isD2SChallengePoint] at hq
    · simp only [srReassocImpl]
      change OracleComp.IsQueryBoundP (liftM (OracleSpec.query _) : OracleComp _ _)
        isSaltedFSChallengeQuery 0
      rw [OracleComp.isQueryBoundP_query_iff]
      simp [isSaltedFSChallengeQuery]

/-- The single-salt SR-KS wrapper only repackages the compiled prover's output. -/
private theorem isSaltedFSChallengeBound_srInducedProverKS
    [DecidableEq ι] [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ) :
    IsSaltedFSChallengeQueryBound
      (srInducedProverKS (nargInducedProverKS (WitOut := WitOut)
        maliciousProver d2sAlgoTransform)) (θStar tₕ tₚ tₚᵢ) := by
  rw [srInducedProverKS_eq_map]
  change OracleComp.IsQueryBoundP
    ((fun p => ((p.1, p.2.1.1), p.2.1.2, p.2.2)) <$>
      nargInducedProverKS (WitOut := WitOut) maliciousProver d2sAlgoTransform)
    (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
      (pSpec := pSpec) (U := U)) (θStar tₕ tₚ tₚᵢ)
  rw [OracleComp.isQueryBoundP_map_iff]
  exact isSaltedFSChallengeBound_nargInducedProverKS (WitOut := WitOut)
    maliciousProver d2sAlgoTransform tₕ tₚ tₚᵢ hBound

/-- The basic-FS prover class produced by a fixed D2S algorithm transform. -/
def basicFSCompiledKSBound [DecidableEq ι] [Inhabited WitOut]
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ) :
    OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt × WitOut) → Prop :=
  fun prover => ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
    IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ ∧
      prover = nargInducedProverKS (WitOut := WitOut) maliciousProver d2sAlgoTransform

/-- Every compiled basic-FS prover maps to the corresponding bounded SR-KS class. -/
private theorem basicFSCompiledKSBound_to_sr
    [DecidableEq ι] [Inhabited WitOut]
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hD2SBound : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ)
    (prover : OracleComp
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt × WitOut))
    (hBound : basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ prover) :
    IsSaltedFSChallengeQueryBound (srInducedProverKS prover) (θStar tₕ tₚ tₚᵢ) := by
  obtain ⟨maliciousProver, hMaliciousBound, rfl⟩ := hBound
  exact isSaltedFSChallengeBound_srInducedProverKS (WitOut := WitOut)
    maliciousProver d2sAlgoTransform tₕ tₚ tₚᵢ (hD2SBound maliciousProver hMaliciousBound)

/-- Theorem 3.19 instantiated with the compiled provers supplied by Lemma 5.1. -/
private theorem basicFS_straightlineKS_withCompiledBound
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (tₕ tₚ tₚᵢ : ℕ)
    (hD2SBound : ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
        IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ)
    (ε_sr : ENNReal)
    (h_IP_SR_KS : Verifier.StateRestoration.knowledgeSoundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (relInSalted relIn) relOut (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins (WitIn := WitIn) (WitOut := WitOut)
      (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
      (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
        srChallengeQueryImpl')
      d2sAuxImpl (d2sUnitSampleImpl (U := U))
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      relIn relOut
      (bound := basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ)
      ε_sr := by
  exact theorem_3_19_straightline_ks
    (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (WitIn := WitIn) (WitOut := WitOut)
    (pSpec := pSpec) (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl
    (Unit →ₒ U) (d2sUnitSampleImpl (U := U)) V relIn relOut
    (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
    (srBound := fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ))
    (bound := basicFSCompiledKSBound d2sAlgoTransform tₕ tₚ tₚᵢ)
    (hBound := basicFSCompiledKSBound_to_sr d2sAlgoTransform tₕ tₚ tₚᵢ hD2SBound)
    (ε := ε_sr) (h_sr_ks := h_IP_SR_KS)

/-- The DSFS proof-only attacker as a CO25 **Def-3.6 NARG adversary**: the malicious prover `𝒫̃`
outputs `(𝕩, π)` and claims the trivial `default` output witness (a NARG / public-coin IP has no
output witness; for the DSFS-of-IP case `WitOut = Unit` this is `()`).  This is the prover the DSFS
Def-3.6 experiment runs in `theorem_6_2_straightline`'s conclusion. -/
def dsfsKSAdversary [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ × WitOut) :=
  (fun p => (p.1, p.2, (default : WitOut))) <$> maliciousProver

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
    [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] [DecidableEq ι]
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
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
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

omit [DecidableEq U] in
/-- **CO25 §6.1 step L3 (two-hop):** false acceptance in `Hyb₄` is bounded by the basic-FS NARG
soundness error.  Combines `hyb4_eq_coinNARGgame` (L3a) with the coin-bearing NARG soundness
hypothesis (delivered by Thm 3.18 from IP SR soundness, L3b) applied to the induced prover. -/
theorem hyb4_falseAccept_le_nargSoundness
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
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
        IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ)
    (ε_sr : ENNReal)
    -- Coin-bearing IP SR soundness (the same hypothesis as `theorem_6_1_soundness`).
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
  -- L3b: FS NARG soundness from IP SR soundness (Thm 3.18), coin-bearing.
  have h_NARG := theorem_3_18_soundness (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl V
    langIn langOut (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
    (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ))
    (fun prover => ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ ∧
        prover = nargInducedProver maliciousProver d2sAlgoTransform)
    (fun prover hProver => by
      obtain ⟨maliciousProver, hBound, rfl⟩ := hProver
      rw [srInducedProver_eq_map]
      change OracleComp.IsQueryBoundP
        ((fun p => ((p.1, p.2.1), p.2.2)) <$>
          nargInducedProver maliciousProver d2sAlgoTransform)
        (isSaltedFSChallengeQuery (oSpec := oSpec) (StmtIn := StmtIn) (Salt := Salt)
          (pSpec := pSpec) (U := U)) (θStar tₕ tₚ tₚᵢ)
      rw [OracleComp.isQueryBoundP_map_iff]
      exact isSaltedFSChallengeBound_nargInducedProver maliciousProver d2sAlgoTransform
        tₕ tₚ tₚᵢ (hD2SBound maliciousProver hBound))
    ε_sr h_IP_SR_sound
  -- L3a: Hyb₄ = the coin-bearing NARG game; apply NARG soundness to the induced prover.
  rw [hyb4_eq_coinNARGgame V oSpecImpl langIn langOut maliciousProver d2sAlgoTransform]
  exact h_NARG (nargInducedProver maliciousProver d2sAlgoTransform)
    ⟨maliciousProver, hMaliciousBound, rfl⟩

/-- **Revised §6.1 endpoint bridge.**  The absorbing H₄ game agrees with the legacy game on
every successful compiled-prover run.  On a source abort it returns `none`, which cannot satisfy
`dsfsSoundnessEvent`; the legacy game may instead run the verifier on a default proof.  Hence the
absorbing false-acceptance probability is only *dominated* by the legacy one, not equal to it.

This is the exact Section 6 interface required by the revised paper's absorbing Hyb₄ convention.
The proof factors both games at the common compiled-prover execution and compares the two
continuations pointwise. -/
theorem hyb4Absorbing_falseAccept_le_hyb4
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [DecidableEq ι]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform]
      ≤ Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform] := by
  classical
  unfold hyb4Absorbing hyb_4 basicFiatShamirGameAbsorbingDist basicFiatShamirGameDist
  refine probEvent_bind_mono ?_
  intro s _
  change
    Pr[ dsfsSoundnessEvent langIn langOut |
      (fun x => x.1) <$>
        (simulateQ (hybChallengeImpl oSpecImpl pSpec.D_IP_salted)
          (basicFiatShamirGameAbsorbing V (d2sAlgoTransform maliciousProver)).run).run s]
      ≤ Pr[ dsfsSoundnessEvent langIn langOut |
        (fun x => x.1) <$>
          (simulateQ (hybChallengeImpl oSpecImpl pSpec.D_IP_salted)
            (basicFiatShamirGame V (d2sAlgoTransform maliciousProver)).run).run s]
  unfold basicFiatShamirGameAbsorbing basicFiatShamirGame
  simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_pure, Option.elimM]
  vcv_norm
  simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  rw [probEvent_map, probEvent_map]
  refine probEvent_bind_mono ?_
  rintro ⟨⟨stmtAndProof?, proveQueryLogRaw⟩, state⟩ _
  cases stmtAndProof? with
  | none =>
      simp [dsfsSoundnessEvent]
  | some stmtAndProof =>
      simp

/-- **Revised §6.1 L3.**  Combine abort-safe endpoint domination with the existing standard-FS
soundness reduction.  No additional statistical term is introduced. -/
theorem hyb4Absorbing_falseAccept_le_nargSoundness
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [DecidableEq ι]
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
        IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ)
    (ε_sr : ENNReal)
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
        (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform] ≤ ε_sr :=
  (hyb4Absorbing_falseAccept_le_hyb4 V oSpecImpl langIn langOut maliciousProver
    d2sAlgoTransform).trans
    (hyb4_falseAccept_le_nargSoundness V oSpecImpl langIn langOut maliciousProver
      d2sAlgoTransform tₕ tₚ tₚᵢ hMaliciousBound hD2SBound ε_sr h_IP_SR_sound)

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
For a query-bounded malicious prover, its false-acceptance probability `ε_NARG`
is at most `ε_sr + η★`. -/
theorem theorem_6_1_soundness
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Section5Nonempty pSpec]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (tₕ tₚ tₚᵢ : ℕ)
    (ε_sr : ENNReal)
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
          (ηStar U tₕ tₚ tₚᵢ
            (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias)) := by
  -- CO25 Def 3.5 (`adaptiveNARGSoundness`) at the DSFS NARG verifier `Verifier.dsfsNargNIV δ V`:
  -- unfold the `∀`-quantifier over query-bounded provers, then run the §6.1 hybrid proof verbatim.
  intro maliciousProver hBound
  -- Step 0: the DSFS NARG soundness experiment (Def 3.5) IS the sponge game `dsfsGameDist` on the
  -- false-acceptance marginal (`dsfsNargSoundnessExp_eq_dsfsGame`); rewrite to the sponge game
  -- so the §6.1 hybrid calc applies verbatim.
  rw [dsfsNargSoundnessExp_eq_dsfsGame V oSpecImpl langIn langOut maliciousProver]
  -- Seam #1 (Theorem 5.1 / Key Lemma): the D2SAlgo prover transform, the D2STrace map, and the
  -- bound `tvDist (Hyb₀, Hyb₄) ≤ η★` for this query-bounded prover.
  obtain ⟨d2sAlgoTransform, d2sTraceTransform, hKey⟩ :=
    lemma_5_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P) (U := U)
      oSpecImpl V tₕ tₚ tₚᵢ
  have hTv := (hKey maliciousProver hBound).1
  -- L3 (paper two-hop): false acceptance in Hyb₄ ≤ basic-FS NARG soundness (L3a) ≤ IP SR
  -- soundness ε_sr (L3b, Thm 3.18). Matches CO25 §6.1 Eq. lines 1950–1957.
  have hL3 := hyb4Absorbing_falseAccept_le_nargSoundness V oSpecImpl langIn langOut
    maliciousProver d2sAlgoTransform tₕ tₚ tₚᵢ hBound
    (fun maliciousProver hBound => (hKey maliciousProver hBound).2) ε_sr h_IP_SR_sound
  -- §6.1 derivation (open seams: Lemma 5.1 at L2 and the absorbing-Hyb₄ L3 bridge):
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
          hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal
              (tvDist
                (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sTraceTransform)
                (hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sAlgoTransform)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ dsfsSoundnessEvent langIn langOut |
          hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ
            (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hTv)
        -- (L3, Hyb₄ ≡ IP SR game) ≤ ε_IP^sr(δ⋆, θ⋆, n) + η★ — directly from SR soundness.
    _ ≤ ε_sr + ENNReal.ofReal
          (ηStar U tₕ tₚ tₚᵢ
            (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) :=
        add_le_add hL3 (le_refl _)
  -- (E, by CO25 Eq. 5) Unfolding `ηStar tₕ tₚ tₚ⁻¹` and using `tₕ + tₚ + tₚ⁻¹ ≤ t`, this bound is:
  --   ε_NARG(λ, (tₕ,tₚ,tₚ⁻¹), n)
  --     ≤ ε_IP^sr(δ⋆, θ⋆(t), n)
  --       + (7(tₕ+tₚ+tₚ⁻¹)² + 28(L+1)(tₕ+tₚ+tₚ⁻¹) + 14(L+1)² − 3(tₕ+tₚ+tₚ⁻¹) − 13(L+1)) / (2·|Σ|^c)
  --       + θ⋆·maxᵢ ε_cdc,ᵢ + Σᵢ ε_cdc,ᵢ
  --     ≤ ε_IP^sr(δ⋆, θ⋆(t), n) + 25t²/|Σ|^c + t·maxᵢ ε_cdc,ᵢ + Σᵢ ε_cdc,ᵢ
  --     = ε_IP^sr(δ⋆, θ⋆(t), n) + η★(λ, t).
  -- We keep `ηStar tₕ tₚ tₚ⁻¹` in the un-simplified form above (the same quantity).

/-! ## Theorem 6.2: IP SR-KS → DSFS straightline KS

Bespoke, query-bounded form mirroring `theorem_6_1_soundness`.  (An earlier attempt phrased the
conclusion in the *generic* library `Verifier.knowledgeSoundness`; that notion is selective +
**unbounded**, so it cannot carry the query-bounded `η★` term — `theorem_6_2_straightline` instead
concludes CO25 Def 3.6 `adaptiveNARGKnowledgeSoundness` with a query-bounded adversary class.) -/

/-- The DSFS **straightline knowledge-soundness game** (bespoke, query-bounded).
Runs the malicious prover and the DSFS verifier, then runs the straightline extractor
on the proof and combined query log. -/
def dsfsKSGameDist [Inhabited WitOut]
    -- Bare straightline-extractor shape (matching the Def-3.6 experiment): the extractor's spec
    -- carries its own `(Unit →ₒ U)` sampler slot (Construction 6.3's D2STrace), answered by
    -- `d2sUnitSampleImpl` in the same eager block as the prover/verifier.
    (dsfsExtractor : StmtIn → WitOut →
      FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) := do
  -- Prover + §5.8 forward verifier under the eager sponge `hyb0Impl`; their logs `tr, tr_𝒱` are
  -- read out as DATA (kept separate, CO25 Construction 6.3).  Then the extractor runs separately
  -- over its own `(Unit →ₒ U)` sampler (`d2sUnitSampleImpl`) — reading challenges from the logs,
  -- querying no challenge oracle (Def 3.14), so it never sees the sponge state `σ`.
  -- Same 6-tuple shape as the generic `adaptiveNARGKnowledgeSoundnessExp` (the proof-only
  -- attacker's witness slot is `default`), so the Def-3.6 experiment ⟷ game bridge
  -- (`dsfsNargKSExp_eq_dsfsKSGame`) is `rfl` once the adversary's witOut-wrapper map normalizes.
  let ⟨stmtIn, proof, _witOut, proveLog, stmtOut?, verifyLog⟩ ←
    (simulateQ (hyb0Impl oSpecImpl) (do
      let ⟨⟨stmtIn, proof⟩, proveLog⟩ ← (simulateQ loggingOracle maliciousProver).run
      let ⟨stmtOut?, verifyLog⟩ ←
        (simulateQ loggingOracle (runForwardVerifierWide δ V stmtIn proof)).run
      pure (stmtIn, proof, (default : WitOut), proveLog, stmtOut?, verifyLog))).run' (← hyb0Init)
  -- Per the `Extractor.Straightline` contract, feed the prover's claimed output witness.  The DSFS
  -- attacker (`MaliciousProver`) is proof-only — it produces no output witness — so its claim is
  -- the trivial `default`; `E_std` receives it (Construction 6.3 recovers the *input* witness from
  -- the trace, not the output one).  Using the literal `default` (not the read-out's `_witOut`
  -- slot, which is the same value) keeps the read-out aligned with `ksFactKernel`/the Def-3.6
  -- experiment.
  let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
    (dsfsExtractor stmtIn (default : WitOut)
      (Fin.cons proof (fun i => i.elim0) :
        FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
      proveLog verifyLog).run
  pure (stmtIn, witIn?, stmtOut?, (default : WitOut))

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [DecidableEq StmtIn] [DecidableEq U] in
/-- **§6.2 de-abort lemma (KS).**  The de-aborted, tagged §5.8 game `dsfsGame` equals the *raw*
prover+verifier read-out (the read-out `dsfsKSGameDist` keeps — including the query logs) composed
with de-abort+tag.  KS analog of the proven `dsfsNargSoundnessExp_eq_dsfsGame`'s `keyA`, but
**keeping the query logs** (Construction 6.3's `E_std` consumes them, so they cannot be stripped).
-/
theorem dsfsGame_run_eq_deabortTag [Inhabited WitOut]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    (dsfsGame (δ := δ) V maliciousProver :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ))))
      = (fun six : StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ × WitOut ×
            QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) × Option StmtOut ×
            QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) =>
          six.2.2.2.2.1.map (fun s =>
            ((six.1, s, six.2.1,
              six.2.2.2.1.map (fun e => (SourceTag.prover, e)) ++
                six.2.2.2.2.2.map (fun e => (SourceTag.verifier, e))) :
              DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
                (pSpec := pSpec) (U := U) (δ := δ))))
        <$> (do
          let ⟨⟨stmtIn, proof⟩, proveLog⟩ ← (simulateQ loggingOracle maliciousProver).run
          let ⟨stmtOut?, verifyLog⟩ ←
            (simulateQ loggingOracle (runForwardVerifierWide δ V stmtIn proof)).run
          pure (stmtIn, proof, (default : WitOut), proveLog, stmtOut?, verifyLog)) := by
  change OptionT.run (dsfsGame (δ := δ) V maliciousProver) = _
  unfold dsfsGame
  vcv_norm

/-- **§6.2 extractor kernel `k`**. Runs the basic-FS NARG-KS extractor `E_std`
on the basic-FS game output. -/
noncomputable def ksFactKernel [Inhabited WitOut]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn) :
    Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) →
      ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) :=
  fun out => match out with
    -- `Hyb` produced no output (game abort): a non-accepting 4-tuple (`stmtOut? = none`), which
    -- `nargKSFailEvent` reads as no break.  The `default` statement is never inspected.
    | none => pure ((default : StmtIn), none, none, (default : WitOut))
    | some result => do
        -- Recover `(tr_𝒫, tr_𝒱)` from the combined tagged log by source.
        let tr := result.2.2.2
        let trP := TaggedQueryLog.proverLog tr
        let trV := TaggedQueryLog.verifierLog tr
        -- `E_std` reads its challenges from `trP, trV` (CO25 Def 3.14 — no challenge-oracle query);
        -- its only oracle is the `𝒰(Σ)` sampler `(Unit →ₒ U)`, answered by `d2sUnitSampleImpl`.
        -- Both logs are already the bare `oSpec + srChallenge` transcript (no prover coins) —
        -- matching the coin-stripped `tr.fst` feed in the Def-3.6 experiment.
        let witIn? ← simulateQ (d2sUnitSampleImpl (U := U))
          (E_std result.1 (default : WitOut) result.2.2.1 trP trV).run
        pure (result.1, witIn?, some result.2.1, (default : WitOut))

set_option maxHeartbeats 300000 in
-- The de-abort rewrite then `probEvent_bind_congr'` over the wide read-out tuple is
-- elaboration-heavy, so the heartbeat budget is raised.
omit [VCVCompatible Salt] in
/-- **§6.2 HELPER `hL1` (Hyb₀ step).**  KS analog of the proven soundness
`dsfsGame_falseAccept_eq_hyb0`: the DSFS straightline-KS game (Construction 6.3 over `E_std`) equals
`Hyb₀ >>= ksFactKernel E_std` on the `nargKSFailEvent` marginal (the §5.8 `D2STrace` line-4 map
preserves the read-out; the `E_std` kernel is threaded through). -/
theorem dsfsKSGame_hL1
    [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargKSFailEvent relIn relOut |
        dsfsKSGameDist (WitOut := WitOut)
          (dsfsStraightlineExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
          oSpecImpl V maliciousProver ]
      = Pr[ nargKSFailEvent relIn relOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver
            (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            >>= ksFactKernel E_std ] := by
  classical
  -- A Pr-level (marginal) equality, NOT a distribution equality.  `dsfsKSGameDist` runs the
  -- extractor on EVERY run (incl. verifier-reject), while `hyb_0 >>= k` de-aborts a reject run to
  -- `(default, none, none, default)` and never runs `E_std` there.  These distributions genuinely
  -- DIFFER on reject (the extractor may even `failure`), but `nargKSFailEvent` is blind to a reject
  -- run (`stmtOut? = none ⇒ False`), so the *marginals* agree: both `0` on reject, identical on
  -- accept (same `E_std`, same logs).  `dsfsGame_run_eq_deabortTag` makes both factor through the
  -- SAME raw prover+verifier read-out; we then compare per read-out `six`.
  conv_rhs =>
    simp only [hyb_0, mappedDSFSGameDist, dsfsGameDist]
    rw [dsfsGame_run_eq_deabortTag (WitOut := WitOut), simulateQ_map]
    simp only [ksFactKernel, StateT.run'_map', bind_map_left, map_bind, bind_assoc]
  conv_lhs =>
    simp only [dsfsKSGameDist, dsfsStraightlineExtractor, runSection58TraceMap]
  refine probEvent_bind_congr' _ _ (fun s => ?_)
  refine probEvent_bind_congr' _ _ (fun six => ?_)
  obtain ⟨stmtIn, proof, witOut, proveLog, stmtOut?, verifyLog⟩ := six
  rcases stmtOut? with _ | st
  · -- reject (`stmtOut? = none`): `nargKSFailEvent` is `False` on every output (both sides yield a
    -- `none` statement-out), so both marginals are `0` — the differing reject behaviour (incl. a
    -- possible `E_std` `failure` on the LHS) is invisible to the event.
    dsimp only
    simp only [Option.map_none, pure_bind]
    refine (probEvent_eq_zero fun x hx => ?_).trans (probEvent_eq_zero fun x hx => ?_).symm
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      obtain ⟨_, _, rfl⟩ := hx
      simp [nargKSFailEvent]
    · simp only [ksFactKernel, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp [nargKSFailEvent]
  · -- accept: `dsfsKSGameDist`'s fused `D2STrace ≫ E_std` equals `k`'s split version (same `E_std`,
    -- same logs), so the two read-out distributions coincide and the marginals are equal.
    refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
    dsimp only
    simp only [Option.map_some, Fin.cons_zero, OptionT.run_bind, OptionT.run_lift, Option.elimM,
      simulateQ_bind, pure_bind, bind_assoc]
    rw [evalDist_bind, evalDist_bind]; congr 1; funext x
    cases x <;> simp only [Option.elim, Option.getD, pure_bind] <;> rfl

/-- Transport a response-dependent query log through an oracle implementation, applying a
log-homomorphism entry-by-entry.  This is the log-preserving counterpart of the usual
`loggingOracle` marginalization lemma. -/
private theorem map_logged_simulation_eq_trace_append
    {ι ξ : Type} {spec : OracleSpec ι} {loggedSpec : OracleSpec ξ}
    {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (so : QueryImpl spec m) (f : QueryLog spec → QueryLog loggedSpec)
    (h_nil : f [] = [])
    (h_append : ∀ l₁ l₂ : QueryLog spec, f (l₁ ++ l₂) = f l₁ ++ f l₂)
    (oa : OracleComp spec α) :
    (Prod.map id f <$> (simulateQ (so.writerTMapBase loggingOracle) oa).run)
      = (simulateQ (so.withTraceAppend (fun t u => f [⟨t, u⟩])) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp [h_nil]
  | query_bind t k ih =>
      vcv_norm
      simp [QueryImpl.writerTMapBase, loggingOracle, QueryImpl.withLogging_apply,
        QueryImpl.withTraceAppend_apply]
      refine bind_congr fun a => ?_
      calc
        (fun a₁ => (a₁.1, f (⟨t, a⟩ :: a₁.2))) <$>
            (simulateQ (so.writerTMapBase loggingOracle) (k a)).run
          = (fun a₁ => (a₁.1, f [⟨t, a⟩] ++ a₁.2)) <$>
              (Prod.map id f <$>
                (simulateQ (so.writerTMapBase loggingOracle) (k a)).run) := by
              rw [Functor.map_map]
              congr 1
              funext a₁
              rcases a₁ with ⟨x, l⟩
              change (x, f ([⟨t, a⟩] ++ l)) = (x, f [⟨t, a⟩] ++ f l)
              rw [h_append]
        _ = _ := by rw [ih a]

private theorem filter_d2s_log_nil
    {κ : Type} {challengeSpec : OracleSpec κ} :
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
      (challengeSpec := challengeSpec) [] = [] := rfl

private theorem filter_d2s_log_append
    {κ : Type} {challengeSpec : OracleSpec κ}
    (l₁ l₂ : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)) :
    filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
      (challengeSpec := challengeSpec) (l₁ ++ l₂)
      = filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
          (challengeSpec := challengeSpec) l₁ ++
        filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)
          (challengeSpec := challengeSpec) l₂ := by
  simp [filterD2SChallengePlusUnitQueryLog]

/-- Re-associating the D2S challenge-plus-coin oracle surface preserves the *filtered* query
log.  Unlike `hyb4_hdist`, this lemma retains the log because the straightline extractor consumes
it. -/
private theorem sr_hyb4_filtered_log_transport
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec)) α) :
    Prod.map id (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)) <$>
        (simulateQ ((srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
          (U := U) oSpecImpl).writerTMapBase loggingOracle) oa).run
      = Prod.map id QueryLog.fst <$>
          (simulateQ
            (((((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
                (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
              QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
                (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
                  (d2sAuxImpl (U := U))) : QueryImpl
                ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
                (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).writerTMapBase
              loggingOracle)
            (simulateQ srReassocImpl oa)).run := by
  let hybImpl := srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec)
    (U := U) oSpecImpl
  let srImpl : QueryImpl
      ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
    ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
      (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) :
        QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
          (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
        (d2sAuxImpl (U := U))
  calc
    _ = (simulateQ (hybImpl.withTraceAppend (fun t u =>
          filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩])) oa).run :=
      map_logged_simulation_eq_trace_append hybImpl
        (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U))
        filter_d2s_log_nil filter_d2s_log_append oa
    _ = (simulateQ ((srImpl.withTraceAppend (fun t u => QueryLog.fst [⟨t, u⟩])) ∘ₛ
          srReassocImpl) oa).run := by
      have h_handler : hybImpl.withTraceAppend (fun t u =>
          filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩])
          = (srImpl.withTraceAppend (fun t u => QueryLog.fst [⟨t, u⟩])) ∘ₛ srReassocImpl := by
        ext q : 1
        rcases q with qO | qC | qU | qN <;>
          funext s <;>
          simp [hybImpl, srImpl, QueryImpl.compose, srReassocImpl, srHyb4Impl,
            QueryImpl.addLift, srImplLift, d2sAuxImpl, srChallengeQueryImpl', StateT.lift,
            QueryImpl.withTraceAppend_apply] <;>
          rfl
      rw [h_handler]
    _ = (simulateQ (srImpl.withTraceAppend (fun t u => QueryLog.fst [⟨t, u⟩]))
          (simulateQ srReassocImpl oa)).run := by
      rw [← QueryImpl.simulateQ_compose]
    _ = _ := (map_logged_simulation_eq_trace_append srImpl QueryLog.fst rfl
      (by intro l₁ l₂; simp only [QueryLog.fst, List.filterMap_append])
      (simulateQ srReassocImpl oa)).symm

/-- The analogous transport for the standard-FS verifier.  Its wide execution contains no
auxiliary D2S sampling queries, so routing it through `liftFSSaltedQueriesToD2SChallengePlusUnit`
turns the filtered wide log into the ordinary SR log. -/
private theorem sr_hyb4_filtered_verifier_log_transport
    {α : Type} (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) α) :
    Prod.map id id <$>
        (simulateQ
          (((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
            (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))).writerTMapBase
              loggingOracle)
          oa).run
      = Prod.map id (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U)) <$>
          (simulateQ
            ((srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) (U := U)
              oSpecImpl).writerTMapBase loggingOracle)
            (simulateQ
              (liftFSSaltedQueriesToD2SChallengePlusUnit
                (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
              oa)).run := by
  let hybImpl := srHyb4Impl (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) (U := U)
    oSpecImpl
  let srImpl : QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
      (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
  calc
    _ = (simulateQ (srImpl.withTraceAppend (fun t u => [⟨t, u⟩])) oa).run :=
      map_logged_simulation_eq_trace_append srImpl id rfl
        (by intro l₁ l₂; rfl) oa
    _ = (simulateQ ((hybImpl.withTraceAppend (fun t u =>
          filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩])) ∘ₛ
          liftFSSaltedQueriesToD2SChallengePlusUnit
            (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) oa).run := by
      have h_handler : srImpl.withTraceAppend (fun t u => [⟨t, u⟩])
          = (hybImpl.withTraceAppend (fun t u =>
            filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩])) ∘ₛ
            liftFSSaltedQueriesToD2SChallengePlusUnit
              (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
        ext q : 1
        rcases q with qO | qC
        · change srImpl.withTraceAppend (fun t u => [⟨t, u⟩]) (Sum.inl qO)
            = simulateQ (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
              (liftM ((oSpec + D2SChallengePlusUnitOracle
                (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec)).query (Sum.inl qO)) :
                OracleComp (oSpec + D2SChallengePlusUnitOracle
                  (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec)) _)
          calc
            _ = (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
                  (Sum.inl qO) := by
                simp [hybImpl, srImpl, QueryImpl.compose,
                  liftFSSaltedQueriesToD2SChallengePlusUnit, srImplLift,
                  srChallengeQueryImpl', srHyb4Impl,
                  filterD2SChallengePlusUnitQueryLog, QueryImpl.withTraceAppend_apply]
            _ = _ := (simulateQ_spec_query
              (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
              (Sum.inl qO)).symm
        · change srImpl.withTraceAppend (fun t u => [⟨t, u⟩]) (Sum.inr qC)
            = simulateQ (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
              (liftM ((oSpec + D2SChallengePlusUnitOracle
                (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec)).query
                  (Sum.inr (Sum.inl qC))) :
                OracleComp (oSpec + D2SChallengePlusUnitOracle
                  (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec)) _)
          calc
            _ = (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
                  (Sum.inr (Sum.inl qC)) := by
                simp [hybImpl, srImpl, QueryImpl.compose,
                  liftFSSaltedQueriesToD2SChallengePlusUnit, srImplLift,
                  srChallengeQueryImpl', srHyb4Impl,
                  filterD2SChallengePlusUnitQueryLog, QueryImpl.withTraceAppend_apply]
            _ = _ := (simulateQ_spec_query
              (hybImpl.withTraceAppend (fun t u =>
                filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
              (Sum.inr (Sum.inl qC))).symm
      rw [h_handler]
      rfl
    _ = (simulateQ (hybImpl.withTraceAppend (fun t u =>
          filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) [⟨t, u⟩]))
          (simulateQ
            (liftFSSaltedQueriesToD2SChallengePlusUnit
              (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            oa)).run := by
      rw [QueryImpl.simulateQ_compose]
      rfl
    _ = _ := (map_logged_simulation_eq_trace_append hybImpl
      (filterD2SChallengePlusUnitQueryLog (oSpec := oSpec) (U := U))
      filter_d2s_log_nil filter_d2s_log_append
      (simulateQ
        (liftFSSaltedQueriesToD2SChallengePlusUnit
          (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        oa)).symm

/-- **§6.2 HELPER `hL3` (the Hyb₄ problem).**  KS twin of the soundness `hyb4_hdist`:
`Hyb₄ >>= ksFactKernel E_std` *is* the coin-bearing basic-FS NARG straightline-KS experiment
(Def 3.6) for `nargInducedProverKS`, verifier `fsSaltedVerify V`, extractor `E_std` — the
eager↔presampled / `deriveTranscript` / prover-de-abort game-equivalence (shared in substance with
§6.1's `hyb4_hdist`). -/
theorem dsfsKSGame_hL3
    [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ nargKSFailEvent relIn relOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform >>= ksFactKernel E_std ]
      = Pr[ nargKSFailEvent relIn relOut |
          adaptiveNARGKnowledgeSoundnessExpWithCoins
            (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            (impl := (srImplLift (StmtIn := StmtIn) (Salt := Salt)
              (pSpec := pSpec) oSpecImpl).addLift (srChallengeQueryImpl'
                (Statement := StmtIn × Salt) (pSpec := pSpec)))
            d2sAuxImpl (d2sUnitSampleImpl (U := U))
            (Verifier.singleSaltFiatShamir (Salt := Salt) V)
            E_std
          (nargInducedProverKS maliciousProver d2sAlgoTransform) ] := by
  classical
  unfold hyb_4 basicFiatShamirGameDist adaptiveNARGKnowledgeSoundnessExpWithCoins
  simp only [hybChallengeInit, srInitDIP, fsSaltedNIV_verify, bind_assoc]
  refine probEvent_bind_congr' _ _ (fun s => ?_)
  unfold basicFiatShamirGame ksFactKernel nargInducedProverKS
  simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_pure, Option.elimM,
    simulateQ_bind, simulateQ_map, pure_bind, bind_assoc]
  sorry

/-- **Revised §6.2 endpoint bridge.**  Applying the straightline-extraction kernel preserves the
one-sided comparison from absorbing Hyb₄ to legacy Hyb₄.  On a source abort the absorbing game
feeds `none` to `ksFactKernel`, whose result has `stmtOut? = none`; therefore
`nargKSFailEvent` is false.  The legacy game may instead run the standard verifier on its default
proof.  Thus this bridge is a domination statement, deliberately not an equality. -/
theorem hyb4Absorbing_ksFail_le_hyb4
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [DecidableEq ι] [Inhabited WitOut]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ nargKSFailEvent relIn relOut |
        hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform >>= ksFactKernel E_std ]
      ≤ Pr[ nargKSFailEvent relIn relOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform >>= ksFactKernel E_std ] := by
  classical
  unfold hyb4Absorbing hyb_4 basicFiatShamirGameAbsorbingDist basicFiatShamirGameDist
  simp only [bind_assoc]
  refine probEvent_bind_mono ?_
  intro s _
  change
    Pr[ nargKSFailEvent relIn relOut |
      ((fun x => x.1) <$>
        (simulateQ (hybChallengeImpl oSpecImpl pSpec.D_IP_salted)
          (basicFiatShamirGameAbsorbing V (d2sAlgoTransform maliciousProver)).run).run s)
        >>= ksFactKernel E_std]
      ≤ Pr[ nargKSFailEvent relIn relOut |
        ((fun x => x.1) <$>
          (simulateQ (hybChallengeImpl oSpecImpl pSpec.D_IP_salted)
            (basicFiatShamirGame V (d2sAlgoTransform maliciousProver)).run).run s)
          >>= ksFactKernel E_std]
  unfold basicFiatShamirGameAbsorbing basicFiatShamirGame
  simp only [OptionT.run_bind, OptionT.run_pure, Option.elimM]
  simp only [simulateQ_pure, simulateQ_bind, simulateQ_map, simulateQ_option_elim,
    simulateQ_optionT_lift, StateT.run'_map', StateT.run'_bind', StateT.run'_pure',
    pure_bind, bind_map_left, map_bind, map_pure, Option.map_map, Function.comp_def]
  simp only [StateT.run_bind, StateT.run_pure, map_bind, bind_assoc]
  refine probEvent_bind_mono ?_
  intro p hp
  rcases p with ⟨source?, state⟩
  cases source? with
  | none =>
      simp [ksFactKernel, nargKSFailEvent]
  | some source =>
      rcases source with ⟨stmtAndProof?, proveQueryLogRaw⟩
      cases stmtAndProof? with
      | none =>
          simp [ksFactKernel, nargKSFailEvent]
      | some stmtAndProof =>
          simp

set_option maxHeartbeats 300000 in
/-- **Revised §6.2 L2/L3 interface.**  This is the complete endpoint bound consumed by Theorem
6.2: apply Lemma 5.1 to the common extraction kernel, then replace absorbing Hyb₄ by legacy Hyb₄
through `hyb4Absorbing_ksFail_le_hyb4`.  Its proof is a direct total-variation/data-processing
calculation followed by that domination; it introduces no additional error term. -/
theorem hyb0_ksFail_le_hyb4_add_eta
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] [DecidableEq ι] [Inhabited WitOut]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Section5Nonempty pSpec]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) (hBound : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ nargKSFailEvent relIn relOut |
        hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
          (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          >>= ksFactKernel E_std ]
      ≤ Pr[ nargKSFailEvent relIn relOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
          (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          >>= ksFactKernel E_std ]
        + ENNReal.ofReal
            (ηStar U tₕ tₚ tₚᵢ
              (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) := by
  let H0 := hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
    (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  let H4Absorbing := hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
    oSpecImpl V maliciousProver
    (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  let H4Legacy := hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
    (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  let eta := ηStar U tₕ tₚ tₚᵢ (verifierPermCallCount (pSpec := pSpec) (δ := δ))
    codec.decodingBias
  change Pr[ nargKSFailEvent relIn relOut | H0 >>= ksFactKernel E_std]
    ≤ Pr[ nargKSFailEvent relIn relOut | H4Legacy >>= ksFactKernel E_std] + ENNReal.ofReal eta
  have hTv : tvDist H0 H4Absorbing ≤ eta := by
    convert (lemma_5_1_inner (δ := δ) (Salt := Salt) (U := U) (T_H := T_H) (T_P := T_P)
      oSpecImpl V tₕ tₚ tₚᵢ maliciousProver hBound).1
  have hAbs : Pr[ nargKSFailEvent relIn relOut | H4Absorbing >>= ksFactKernel E_std]
      ≤ Pr[ nargKSFailEvent relIn relOut | H4Legacy >>= ksFactKernel E_std] := by
    exact hyb4Absorbing_ksFail_le_hyb4 E_std V oSpecImpl relIn relOut maliciousProver
      (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  calc
    Pr[ nargKSFailEvent relIn relOut | H0 >>= ksFactKernel E_std]
      ≤ Pr[ nargKSFailEvent relIn relOut | H4Absorbing >>= ksFactKernel E_std]
          + ENNReal.ofReal (tvDist (H0 >>= ksFactKernel E_std) (H4Absorbing >>= ksFactKernel E_std)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ nargKSFailEvent relIn relOut | H4Absorbing >>= ksFactKernel E_std]
          + ENNReal.ofReal (tvDist H0 H4Absorbing) :=
        add_le_add le_rfl
          (ENNReal.ofReal_le_ofReal <| tvDist_bind_right_le (ksFactKernel E_std) H0 H4Absorbing)
    _ ≤ Pr[ nargKSFailEvent relIn relOut | H4Absorbing >>= ksFactKernel E_std]
          + ENNReal.ofReal eta :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hTv)
    _ ≤ Pr[ nargKSFailEvent relIn relOut | H4Legacy >>= ksFactKernel E_std]
          + ENNReal.ofReal eta := add_le_add hAbs le_rfl

/-- **Construction 6.3 in CO25 Def-3.6 (NARG) shape** — the straightline extractor witnessing the
DSFS NARG's `adaptiveNARGKnowledgeSoundness`.  Wraps `dsfsStraightlineExtractor E_std` (the
`Extractor.Straightline` form) into the Def-3.6 extractor type: build the non-interactive transcript
from the proof `π`, pass a dummy `default` output witness (ignored), and thread the prover log `tr`
and verifier log `tr_𝒱` through to `dsfsStraightlineExtractor`'s two slots. -/
noncomputable def dsfsNargExtractor [Inhabited WitOut]
    {T_H : Type} {T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn) :
    (stmtIn : StmtIn) → (π : DSSaltedProof (pSpec := pSpec) (U := U) δ) →
    (tr_P : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) →
    (tr_V : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) →
    OptionT (OracleComp (Unit →ₒ U)) WitIn :=
  -- Construction 6.3 in NARG shape: wrap `dsfsStraightlineExtractor` (which runs the REAL
  -- `D2STrace(tr ‖ tr_V)` over its `(Unit →ₒ U)` sampler slot, splits into prover/verifier logs by
  -- source tag, and feeds `E_std`).  `T_H/T_P` are passed explicitly (undetermined at the call).
  fun stmtIn proof tr_P tr_V =>
    dsfsStraightlineExtractor (T_H := T_H) (T_P := T_P) (stmtIn : StmtIn) (default : WitOut)
      (E_std := E_std)
      ((Fin.cons proof (fun i => i.elim0)) :
        FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
      tr_P tr_V

omit [VCVCompatible Salt] in
/-- **DSFS NARG-KS experiment = sponge KS game** (CO25 §6.2 game-equivalence). -/
theorem dsfsNargKSExp_eq_dsfsKSGame [Inhabited WitOut]
    (E_std : StmtIn → WitOut → FSSaltedProof pSpec Salt →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
        OptionT (OracleComp (Unit →ₒ U)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargKSFailEvent relIn relOut |
        adaptiveNARGKnowledgeSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (d2sUnitSampleImpl (U := U))
          (Verifier.dsfsNargNIV δ V)
          (dsfsNargExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
          (dsfsKSAdversary (WitOut := WitOut) maliciousProver) ]
      = Pr[ nargKSFailEvent relIn relOut |
          dsfsKSGameDist (WitOut := WitOut)
            (dsfsStraightlineExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
            oSpecImpl V maliciousProver ] := by
  classical
  -- Both sides produce the Def-3.6 4-tuple directly (no read-out re-encoding); the failure
  -- probability follows from the distribution equality `experiment = game`.
  have hdist :
      adaptiveNARGKnowledgeSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (d2sUnitSampleImpl (U := U))
          (Verifier.dsfsNargNIV δ V)
          (dsfsNargExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
          (dsfsKSAdversary (WitOut := WitOut) maliciousProver)
        = dsfsKSGameDist (WitOut := WitOut)
            (dsfsStraightlineExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
            oSpecImpl V maliciousProver := by
    -- Post-decoupling BOTH sides split identically (prover/verifier under `hyb0Impl`, then
    -- `E_std` separately under `d2sUnitSampleImpl`); the only gap is the proof-only→witOut
    -- wrapper, which is `simulateQ`/`Writer` functoriality.  `dsfsNargVerify`/`dsfsNargExtractor`
    -- unfold to the game's `runForwardVerifierWide`/`dsfsStraightlineExtractor` defeq.
    unfold adaptiveNARGKnowledgeSoundnessExp dsfsKSGameDist dsfsKSAdversary dsfsNargExtractor
    -- `Verifier.dsfsNargNIV`'s verify is defeq to `dsfsNargVerify` (`Fin.cons … 0 = π`); rewrite to
    -- the bare-function form, then unfold it to the game's `runForwardVerifierWide`.
    simp only [dsfsNargNIV_verify]
    unfold dsfsNargVerify
    simp [OptionT.run_mk, simulateQ_map, map_bind, bind_map_left,
      bind_assoc]
  rw [hdist]

-- Needed because unfolding `adaptiveNARGKnowledgeSoundnessExp` and `dsfsKSGameDist` generates large
-- proof states
set_option maxHeartbeats 300000 in
-- The endpoint applications carry full oracle implementations and need this bounded elaboration
-- budget; the proof itself delegates all game reasoning to named interfaces above.
/-- **Theorem 6.2** — Straightline knowledge soundness of the duplex-sponge Fiat–Shamir scheme.
For a query-bounded malicious prover, the extraction-failure probability
is at most `ε_sr + η★`. -/
theorem theorem_6_2_straightline
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Section5Nonempty pSpec]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (tₕ tₚ tₚᵢ : ℕ)
    (ε_sr : ENNReal)
    (h_IP_SR_KS : Verifier.StateRestoration.knowledgeSoundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (relInSalted relIn) relOut (saltedIPVerifier (Salt := Salt) V)
        (fun prover => IsSaltedFSChallengeQueryBound prover (θStar tₕ tₚ tₚᵢ)) ε_sr) :
    -- CO25 **Def 3.6** (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG: oracle model
    -- `hyb0Init`/`hyb0Impl`, verifier `dsfsNargVerify V`, acceptance `(stmtOut, witOut) ∈ relOut`;
    -- adversary class = the query-bounded proof-only DSFS attacker `dsfsKSAdversary 𝒫̃`.
    (Verifier.dsfsNargNIV δ V).adaptiveNARGKnowledgeSoundness (WitIn := WitIn) (WitOut := WitOut)
      (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
      (auxImplE := d2sUnitSampleImpl (U := U))
      (relIn := relIn) (relOut := relOut)
      (bound := fun P =>
        ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
          IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ ∧
            P = dsfsKSAdversary maliciousProver)
      (error := ε_sr + ENNReal.ofReal
        (ηStar U tₕ tₚ tₚᵢ
          (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias)) := by
  -- CO25 Def 3.6 (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG verifier `Verifier.dsfsNargNIV
  -- δ V`: provide the Construction-6.3 extractor (`use`) and run the §6.2 proof verbatim.
  -- **Step 4 (Theorem 3.19).** IP SR-KS ⟹ basic-FS NARG straightline-KS, delivering `E_std`.
  letI : ∀ i, DecidableEq (pSpec.Message i) :=
    fun _ => instDecidableEqOfVCVCompatible
  obtain ⟨E_std, hE_std⟩ := -- constructor for the DSFS-transformed NARG
    basicFS_straightlineKS_withCompiledBound
      (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      V oSpecImpl relIn relOut tₕ tₚ tₚᵢ
      (fun maliciousProver hBound => by
        exact d2sAlgoRevised_challengeQueryBound (T_H := T_H) (T_P := T_P)
          (Salt := Salt) maliciousProver tₕ tₚ tₚᵢ hBound
      )
      ε_sr h_IP_SR_KS
  -- Extractor witness: Construction 6.3 in NARG shape (`dsfsNargExtractor`) over `E_std`.
  use dsfsNargExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std
  intro P hBound -- arbitrary bound-query prover
  -- The DSFS attacker is a query-bounded proof-only `MaliciousProver` claiming `default` witOut.
  obtain ⟨maliciousProver, hQB, rfl⟩ := hBound
  -- Step 0: the DSFS NARG-KS experiment (Def 3.6) IS the sponge KS game `dsfsKSGameDist` on the
  -- extraction-failure marginal (`dsfsNargKSExp_eq_dsfsKSGame`); rewrite to the sponge game so the
  -- §6.2 hybrid calc applies verbatim.
  rw [dsfsNargKSExp_eq_dsfsKSGame (WitOut := WitOut) E_std V oSpecImpl relIn relOut
      maliciousProver]
  -- The arithmetic is factored through a polymorphic shell so these large hybrid programs remain
  -- opaque.  The only new Section 6 fact is the explicit absorbing-to-legacy domination below.
  calc
    Pr[ nargKSFailEvent relIn relOut |
        dsfsKSGameDist (WitOut := WitOut)
          (dsfsStraightlineExtractor (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std)
          oSpecImpl V maliciousProver ]
      = Pr[ nargKSFailEvent relIn relOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
            (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            >>= ksFactKernel E_std ] :=
      dsfsKSGame_hL1 (WitOut := WitOut) (T_H := T_H) (T_P := T_P) E_std V oSpecImpl
        relIn relOut maliciousProver
    _ ≤ Pr[ nargKSFailEvent relIn relOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U) oSpecImpl V maliciousProver
            (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            >>= ksFactKernel E_std ]
          + ENNReal.ofReal
              (ηStar U tₕ tₚ tₚᵢ
                (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) :=
      hyb0_ksFail_le_hyb4_add_eta (T_H := T_H) (T_P := T_P) E_std V oSpecImpl relIn relOut
        maliciousProver tₕ tₚ tₚᵢ hQB
    _ = Pr[ nargKSFailEvent relIn relOut |
          adaptiveNARGKnowledgeSoundnessExpWithCoins
            (init := srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            (impl :=
              (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
              (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)))
            d2sAuxImpl (d2sUnitSampleImpl (U := U))
            (Verifier.singleSaltFiatShamir (Salt := Salt) V) E_std
            (nargInducedProverKS maliciousProver
              (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
                (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))]
          + ENNReal.ofReal
              (ηStar U tₕ tₚ tₚᵢ
                (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) := by
      rw [dsfsKSGame_hL3 E_std V oSpecImpl relIn relOut maliciousProver
        (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
          (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))]
    _ ≤ ε_sr + ENNReal.ofReal
            (ηStar U tₕ tₚ tₚᵢ
              (verifierPermCallCount (pSpec := pSpec) (δ := δ)) codec.decodingBias) := by
      exact add_le_add
        (hE_std
          (nargInducedProverKS maliciousProver
            (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
              (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
          ⟨maliciousProver, hQB, rfl⟩)
        le_rfl

end

end DuplexSpongeFS
