/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents.Core

/-!
# Bad-event probability bound

The eager real/simulator trace experiments and probability statement for CO25 Lemma 5.8.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## Lemma 5.8 — closed-form bound
This section is consistency-free: `lemma_5_8` bounds `Pr[E]` directly via birthday-style
counting on freshly-sampled values. -/
section Lemma_5_8

/-- CO25 Lemma 5.8 — Closed-form upper bound on `max{Pr[E | 𝒟_𝔖], Pr[E | 𝒟_Σ]}`.
For a `(tₕ, tₚ, tₚᵢ)`-query prover with `L` verifier permutation queries, the bound is:

```
(7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`. -/
noncomputable def lemma5_8Bound (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U]
  [∀ i, Fintype (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 Lemma 5.8 — aggregate DS hash queries in the combined empty-plus-DS surface. -/
def isLemma5_8HashQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- CO25 Lemma 5.8 — aggregate DS forward-permutation queries in the combined surface. -/
def isLemma5_8PermQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inl _)) => True
  | _ => False

/-- CO25 Lemma 5.8 — aggregate DS inverse-permutation queries in the combined surface. -/
def isLemma5_8PermInvQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- CO25 Lemma 5.8 — semantic aggregate `(tₕ, tₚ, tₚᵢ)` query bound for the salted §5.6 prover.
Each counter ranges over its entire oracle family, rather than resetting for every oracle input. -/
abbrev IsLemma5_8QueryBound
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop := by
  classical
  exact OracleComp.IsQueryBoundP maliciousProver isLemma5_8HashQuery tₕ ∧
    OracleComp.IsQueryBoundP maliciousProver isLemma5_8PermQuery tₚ ∧
    OracleComp.IsQueryBoundP maliciousProver isLemma5_8PermInvQuery tₚᵢ

/-- CO25 §5.6 — Project a `[]ₒ + DS` combined trace log down to just the DS component.
The empty-oracle branch is unreachable, so we discard it via `PEmpty.elim`. -/
def lemma5_8ProjectTraceLog
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, _⟩ => PEmpty.elim q
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- The empty-oracle branch is uncallable in any target monad. Used to build
`QueryImpl ([]ₒ + DS) (OptionT (StateT _ ProbComp))` via `QueryImpl.+`. -/
private def lemma5_8EmptyQueryImplGeneric {m : Type → Type} : QueryImpl []ₒ m :=
  fun q => PEmpty.elim q

/-- CO25 §5.6 (Option G) — Monad-reorder + logging wrapper. Reorders `StateT σ (OptionT ProbComp)`
into `OptionT (StateT (σ × QueryLog) ProbComp)` so the log survives an abort (paper line 1417:
"abort halts execution; trace is partial"), and appends `⟨q, a⟩` on each successful query. -/
private def lemma5_8LoggingWrapper {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  fun q => OptionT.mk fun st => do
    let r ← (impl q st.1).run
    match r with
    | none => pure (none, st)
    | some (a, s') => pure (some a, (s', st.2 ++ [⟨q, a⟩]))

/-- CO25 §5.6 (Option G) — Abortable Lemma-5.8 trace experiment, mirroring the §5.8 hybrid skeleton
(`KeyLemma.dsfsGame` / `hybridGame`): the salted `maliciousProver` runs under `impl`, then the
forward-only verifier `𝒱^{h,p} := V.toDSFS δ` (paper Figure 4 line 3) runs on its output, with the
carrier `σ` (e.g. `D_𝔖.Carrier` / `D2SQueryState`) threaded throughout.

Returns `(tr_P̃, tr_V)`; the bad event `E` (Def 5.7) is evaluated on `tr_P̃ ++ tr_V`. -/
noncomputable def lemma5_8ProjectedTraceDistAbortable
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp)))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let s₀ ← init
  -- Log each DS query into the wide `[]ₒ + DS` log (tagged `Sum.inr`); the log is kept on abort.
  let wrappedDSImpl :
      QueryImpl (duplexSpongeChallengeOracle StmtIn U)
        (OptionT
          (StateT (σ ×
            QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
    fun q => OptionT.mk fun st => do
      let r ← (impl q st.1).run
      match r with
      | none => pure (none, st)
      | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))
  -- The `[]ₒ` summand is unreachable, so compose it via the generic empty impl.
  let combinedImpl :
      QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
        (OptionT
          (StateT (σ ×
            QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
    (lemma5_8EmptyQueryImplGeneric
      (m := OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)))
    + wrappedDSImpl
  -- Prover phase on a fresh log `[]`; the log accumulates the prover trace `tr_P̃`.
  let proverResult ← ((simulateQ combinedImpl maliciousProver).run) (s₀, [])
  match proverResult with
  | (none, (_, trP)) =>
      -- Abort (paper line 1417): execution halts, `V` never runs, so `tr_V = []`.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP, [])
  | (some ⟨stmtIn, proof⟩, (s₁, trP)) =>
      -- Success: verifier reuses carrier `s₁` but a fresh log, so `tr_V` is verifier-only.
      -- `runForwardVerifierWide` lifts the forward verifier to the wide spec (shared log surface).
      let verifyCompWide :
          OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
        runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof
      let verifierResult ← ((simulateQ combinedImpl verifyCompWide).run) (s₁, [])
      let trV := verifierResult.2.2
      -- Project both `[]ₒ + DS` logs down to bare DS.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP,
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trV)

/-- CO25 §5.6 (Option G) — Trivially lift a total `StateT σ ProbComp` DS implementation to the
abortable shape `StateT σ (OptionT ProbComp)` required by `lemma5_8ProjectedTraceDistAbortable`.
The lifted impl never produces `none`. -/
private def lemma5_8TotalAbortLift {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)) :=
  fun q s => OptionT.lift (impl q s)

/-- CO25 Lemma 5.8 — Left-hand-side trace distribution (Option G — paper-faithful abort).
Real DS execution under the explicit `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` implementation. The eager impl is
total (never aborts), so the `OptionT`-layer is a dummy. Returns the pair `(tr_P̃, tr_V)`. -/
noncomputable def lemma5_8RealTraceDist
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    initReal
    (lemma5_8TotalAbortLift (StmtIn := StmtIn) (U := U) implReal)
    V maliciousProver

/-- CO25 Lemma 5.8 — Right-hand-side trace distribution (Option G — paper-faithful abort).
Simulator execution under eager `g ← 𝒟_Σ(λ, n)` with `D2SQuery` as the oracle implementation.
The `d2sQueryImpl` runs in `StateT D2SQueryState (OptionT ProbComp)`: an `OptionT`-abort halts the
experiment (paper line 1417). Returns the pair `(tr_P̃, tr_V)`.

The `g` carrier is sampled **once** at experiment start from `𝒟_Σ`, captured by closure,
and consulted deterministically by every `gᵢ` query. This mirrors `lemma5_8RealTraceDist`'s
eager `(h, p, p⁻¹) ← 𝒟_𝔖` sampling — CO25 Def. 4.2 + Lemma 5.8 statement. -/
noncomputable def lemma5_8SigmaTraceDist
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let k_g ←
    (D_Sigma (instSampleable := instSampleableTypeEncodedChallengeOracle)
      (U := U) StmtIn pSpec δ).sample
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    (init := pure default)
    (impl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := fun q => OptionT.lift
        ((D_Sigma (instSampleable := instSampleableTypeEncodedChallengeOracle)
          (U := U) StmtIn pSpec δ).toImpl k_g q))
      (auxImpl := fun aux => OptionT.lift
        ((ProverTransform.d2sUnitSampleImpl
            (instSampleable := VCVCompatible.toSampleableType) (U := U) +
          QueryImpl.id' unifSpec) aux)))
    V maliciousProver


/-- CO25 Lemma 5.8 — Bad-event probability bound (eager statement).
For every salted `(tₕ, tₚ, tₚᵢ)`-query malicious prover P̃, let
`L_totalRateBlocks δ pSpec = Lδ + Lₚ + Lᵥ` be the conservative upper bound that accounts for
both the initial salt absorption and the verifier's protocol execution. This is the common `L`
instantiation in `claim_5_21`, `claim_5_24`, and the final `ηStar` bound.

```
max{ Pr[E(tr_P̃ ‖ tr_V) | 𝒟_𝔖], Pr[E(tr_P̃ ‖ tr_V) | 𝒟_Σ] }
  ≤ (7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L_totalRateBlocks δ pSpec + tₚᵢ`. Relative to the printed lemma,
the salt-aware `L` accounts for the logged verifier's salt absorption. This statement also omits
the paper's `tₚ ≥ Lₚ + Lᵥ` condition: it is unnecessary for the birthday-bound argument, so this
is an intentional strengthening. The experiment distributions match CO25 Lemma 5.8, but `E`
uses the documented bidirectional strengthening of the paper's one-sided `E_func`; this
statement intentionally retains the same closed-form bound for that stronger event. The
left-hand side samples `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` once at the start of the experiment (eager
sampling, CO25 Def. 4.2) and corresponds to `KeyLemma.dsfsGame` (`Hyb_0`); the right-hand side
runs `g ← 𝒟_Σ(λ, n)` via the `D2SQuery` simulator and corresponds to `KeyLemma.hybridGame`
instantiated as `Hyb_1`. -/
theorem lemma_5_8
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : -- `(tₕ, tₚ, tₚᵢ)`-query bound prover
      IsLemma5_8QueryBound
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        maliciousProver tₕ tₚ tₚᵢ) :
    max
        (Pr[fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              BadEventDS.E (tr.1 ++ tr.2) |
          lemma5_8RealTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (δ := δ)
            (D_𝔖 StmtIn U).sample
            ((D_𝔖 StmtIn U).eagerImpl)
            V maliciousProver])
        (Pr[fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              BadEventDS.E (tr.1 ++ tr.2) |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P) (δ := δ)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U)
            V maliciousProver])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ (L := L_totalRateBlocks δ pSpec)) := by
  let _ := hMaliciousBound
  sorry

end Lemma_5_8

end BadEventDS

end DuplexSpongeFS
