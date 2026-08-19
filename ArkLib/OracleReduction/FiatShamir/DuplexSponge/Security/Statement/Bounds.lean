/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventDefs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.Data.Hash.DuplexSponge
import ArkLib.ToVCVio.OracleComp.EvalDist
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

/-!
# Statement layer — module 1: schedule, exact verifier bounds, and concrete events

This module is the dependency-acyclic home of the *exact* verifier permutation-call count
`N_𝒱` and of the bound functions that carry it, now tied to the **concrete** trace and event
types of the revised paper:

- `verifierPermCallCount pSpec δ` — the paper's exact `N_𝒱` (eqs. 4a–4b), imported from the
  canonical `BacktrackSchedule`;
- `badEventBound B` (eq. 26a/27), `Ccap` (eq. 28), `Dcap` (eq. 29), with their exceptional
  `(T, nV) = (0,0)` specifications;
- `etaStar` (eq. 5) with the exact `N_𝒱` in the fourth (count) argument;
- the **concrete trace type** `Trace StmtIn U` (= the real `(duplexSpongeChallengeOracle
  StmtIn U).QueryLog`) and the **concrete bad event** `BadEvent` / `BadEventDup` /
  `BadEventFunc` — plain re-exports of `BadEventDS.E` / `.E_dup` / `.E_func` from the acyclic
  `BadEventDefs` module;
- the **concrete probability / distance** wiring: `EventProbability` (real `Pr[E | exp]` over
  `ProbComp`), `HybridTVDist` (real `tvDist`), and `IdenticalDistributions` (real `tvDist = 0`);
- the concrete Lemma 5.8 / Claim 5.21 / Claim 5.24 **core statement shapes** stated over these
  concrete probability / distance quantities.

Rules honoured: **no** rounded ceiling (`totalNumPermQueries*`, `L`, `Lbar`,
`phaseQueryBudget`) occupies any `N_𝒱` slot here; **no** theorem-with-`sorry` and **no**
placeholder; **no** abstract specimen whose key semantic clause is an unconstrained `Prop`
parameter — every clause below is a concrete predicate / real quantity over real types.  This
module imports no live Section 5 algorithm (only `Defs`, sponge foundations, the canonical
schedule layer `BacktrackSchedule`, the acyclic `BadEventDefs`, and the VCVio probability layer).

**Single-source note:** the canonical source of stateful-schedule semantics — the
`PhaseShape` / `ScheduleCursor` machinery, `buildPhaseSchedule`, `scheduleQueryCount`,
`protocolPhases`, and `verifierPermCallCount` — lives **only** in `BacktrackSchedule.lean`.
This module no longer mirrors that arithmetic; it imports the canonical definitions and refers
to them directly (no statement-layer duplicates).  There is exactly one semantic definition of
`verifierPermCallCount` / the schedule replay, in `BacktrackSchedule.lean`, which this module
imports.
-/

open scoped BigOperators

namespace DuplexSpongeFS

namespace Statement

/-! ## Canonical schedule names (referred, not redefined)

The single source is `BacktrackSchedule.lean`; there are **no** statement-layer duplicates.
Downstream statement modules refer to the canonical names directly:

- `DuplexSpongeFS.Backtrack.ScheduleCursor.PhaseShape` / `.buildPhaseSchedule` /
  `.scheduleQueryCount` — the stateful replay machinery (CO25 eq. 4b);
- `DuplexSpongeFS.protocolPhases` — the flat direction-labelled `Act_𝒱` phase list (eq. 4a);
- `DuplexSpongeFS.verifierPermCallCount` — the exact `N_𝒱`.

This module's bound functions take the count `nV` as a `ℕ` parameter, so they never re-derive an
`N_𝒱`; the exact count is imported from `BacktrackSchedule` where needed.
-/

/-! ## Concrete trace and event -/

open DuplexSpongeFS.BadEventDS

/-- The concrete trace type of the statement layer: the real `(query, answer)` log of the
duplex-sponge challenge oracle — exactly the type on which `BadEventDS.E` is defined.  This is
the same `List`-backed log as `DSTraceStorage.DuplexSpongeTrace`; we name it here so downstream
statement modules share one spelling. -/
abbrev Trace (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  (OracleSpec.duplexSpongeChallengeOracle StmtIn U).QueryLog

/-- The concrete combined bad event `E` (CO25 Def 5.7): a real predicate on the concrete trace —
plain re-export of the acyclic `BadEventDS.E`.  This is the event whose probability Lemma 5.8
and the hybrid claims bound. -/
def BadEvent {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  BadEventDS.E trace

/-- The concrete capacity-segment duplication event `E_dup` (CO25 Def 5.7 / eqs. 23–25):
re-export of `BadEventDS.capacitySegmentDup`. -/
def BadEventDup {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  BadEventDS.capacitySegmentDup trace

/-- The concrete functional-inconsistency event `E_func` (CO25 Def 5.7 / eq. 26):
re-export of `BadEventDS.E_func`. -/
def BadEventFunc {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  BadEventDS.E_func trace

/-! ## Concrete probability / distance quantities

These bind the raw real quantities that the earlier abstract specimens left unconstrained.  The
experiments are left as parameters of the concrete monadic type `ProbComp` (the VCVio
probability monad); the executable wiring that manufactures a particular experiment is supplied
by a later refinement.
-/

/-- The real probability that the concrete bad event `E` holds on the output trace of the
(concrete monadic) experiment `exp`.  This is `Pr[E | exp].toReal`, the quantity bounded on the
left of Lemma 5.8's conclusion.  The `EventProbability` of an *any*-event-over-trace experiment
`exp` is the concrete real the bound is stated over. -/
noncomputable def EventProbability {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (exp : ProbComp (Trace StmtIn U)) : ℝ :=
  (Pr[ fun trace : Trace StmtIn U => BadEvent trace | exp ]).toReal

/-- The concrete real statistical distance `Δ(exp₁, exp₂)` between two (concrete monadic)
experiments: the VCVio total-variation distance `tvDist exp₁ exp₂`.  Claims 5.19–5.24 and the
hybrid-chain bound of Lemma 5.1 are stated over this quantity. -/
noncomputable def HybridTVDist {α : Type} (exp₁ exp₂ : ProbComp α) : ℝ :=
  tvDist exp₁ exp₂

/-- The concrete "identical distributions" fact for the exceptional `(T,nV)=(0,0)` case: the
two experiments have zero total-variation distance.  (For finite distributions TV-distance zero
means the two distributions agree pointwise.) -/
noncomputable def IdenticalDistributions {α : Type} (exp₁ exp₂ : ProbComp α) : Prop :=
  tvDist exp₁ exp₂ = 0

/-! ## Bound functions -/

/-- Capacity space size `Q = |Σ|^c`, as a real (matches the `ℝ`-valued bound convention of
`badEventBound` / `Ccap` / `Dcap` / `etaStar`). -/
noncomputable def capacitySize (U : Type) [Fintype U] [SpongeSize] : ℝ :=
  ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C

/-- CO25 §5.6 (eq. 26a/27): `B(u) = (7u² − 3u)/(2Q)`.  The Lemma 5.8 coefficient, preserved
verbatim. -/
noncomputable def badEventBound (U : Type) [Fintype U] [SpongeSize]
    (u : ℕ) : ℝ :=
  (7 * ((u : ℝ) ^ 2) - 3 * (u : ℝ)) / (2 * capacitySize U)

/-- CO25 §5.6 (eq. 28): `C(T,v) = ((6v+4)T + 3v² + 5v)/(2Q)`, the charge of a stop experiment
whose verifier makes exactly `v` forward calls over an `E`-good prefix of ≤ `T` entries. -/
noncomputable def Ccap (U : Type) [Fintype U] [SpongeSize]
    (T v : ℕ) : ℝ :=
  ((6 * (v : ℝ) + 4) * (T : ℝ) + 3 * ((v : ℝ) ^ 2) + 5 * (v : ℝ)) / (2 * capacitySize U)

/-- CO25 §5.6 (eq. 29): `D(T,N_𝒱) = (14(N_𝒱+1)T + 7(N_𝒱+1)² − 10(N_𝒱+1))/(2Q)`, the
uniformized bound replacing `v` by `N_𝒱`.  The numerator is a real (may be formally negative at
`(0,0)`); the paper and the ledger **deliberately never invoke** that formal value, so the
`(T,N_𝒱)=(0,0)` exceptional case is split off by `ExceptionalEmpty` / `Lemma58StoppedCore`. -/
noncomputable def Dcap (U : Type) [Fintype U] [SpongeSize]
    (T nV : ℕ) : ℝ :=
  let n : ℝ := ((nV + 1 : ℕ) : ℝ)
  (14 * n * (T : ℝ) + 7 * (n ^ 2) - 10 * n) / (2 * capacitySize U)

/-- Record of the exceptional case `(T, nV) = (0,0)`, at which `Dcap` is a negative formal
value and both the Lemma 5.8 stopped clause and Claim 5.24 instead assert exact agreement
(probability zero / identical distributions).  This is the paper's own case split. -/
def ExceptionalEmpty (T nV : ℕ) : Prop := T = 0 ∧ nV = 0

/-- CO25 eq. (5), algebraic term: `T := tₕ+tₚ+tₚᵢ` and the exact `nV` in the count slot,
`(7T² + 28(nV+1)T + 14(nV+1)² − 3T − 13(nV+1))/(2Q)`. -/
noncomputable def etaStarFirstTerm (U : Type) [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ nV : ℕ) : ℝ :=
  let T : ℝ := ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
  let n : ℝ := ((nV + 1 : ℕ) : ℝ)
  (7 * (T ^ 2) + 28 * n * T + 14 * (n ^ 2) - 3 * T - 13 * n) / (2 * capacitySize U)

/-- CO25 eq. (5), codec term `θ_* · max_i ε_cdc,i + Σ_i ε_cdc,i` with `θ_* = t_p`.  The max
and sum over the protocol rounds are supplied as their (real) values; this keeps the module free
of the cdc indexing while recording the term's shape. -/
noncomputable def etaStarCodecTerm (θStar : ℝ) (maxCodecBias : ℝ) (sumCodecBias : ℝ) : ℝ :=
  θStar * maxCodecBias + sumCodecBias

/-- CO25 eq. (5): `ηStar` with the exact `N_𝒱` in the fourth numeric argument.  The revised
Section 5 has no separate lower-bound premise on `tₚ`: its algebraic role is only the
adversary's actual permutation-query count. -/
noncomputable def etaStar (U : Type) [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ nV : ℕ) (codecTerm : ℝ) : ℝ :=
  etaStarFirstTerm U tₕ tₚ tₚᵢ nV + codecTerm

/-! ## Core statement shapes (BF-1 / BF-2) — concrete

These are named proposition *specifications* (not theorems — nothing is claimed here) of the
final exact-`N_𝒱` core statements.  Unlike the earlier abstract versions, every semantic clause
is now a **concrete** quantity: the left-hand side of each is `EventProbability exp`
(`Pr[E|exp].toReal`) or `HybridTVDist exp₁ exp₂` (`tvDist exp₁ exp₂`), the right-hand side
an exact `N_𝒱`-carrying bound.  The concrete experiment `exp` is a parameter; the executable
wiring that manufactures it is supplied by a later refinement.
-/

/-- The δ-parametric Lemma 5.8 **core** (plan M2a / BF-1): over an abstract count `n` with
`hn : verifierPermCallCount pSpec δ = n`, an execution `exp` whose base trace has at most
`T + 1 + n` entries satisfies `Pr[E|exp] ≤ B(T+1+n)`.  `exp : ProbComp (Trace StmtIn U)` is the
concrete monadic experiment, `EventProbability exp` its concrete bad-event probability. -/
def Lemma58Core {StmtIn U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    (exp : ProbComp (Trace StmtIn U)) (T n : ℕ) : Prop :=
  EventProbability exp ≤ badEventBound U (T + 1 + n)

/-- The δ-parametric Lemma 5.8 **stopped** core (BF-2): over an `E`-good prefix of ≤ `T` base
entries, the probability that the verifier extension (one hash + exactly `nV` forward calls)
creates its first new `E` is at most `Dcap T nV` in the nontrivial case, and exactly `0` in the
exceptional empty case.  The `(0,0)` split is structurally required by the paper (a case split,
not a new idea).  `exp` is the concrete stopped experiment, `EventProbability exp` its concrete
first-new-`E` probability. -/
def Lemma58StoppedCore {StmtIn U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    (exp : ProbComp (Trace StmtIn U)) (T nV : ℕ) : Prop :=
  (ExceptionalEmpty T nV → EventProbability exp = 0) ∧
    (¬ ExceptionalEmpty T nV → EventProbability exp ≤ Dcap U T nV)

/-- Claim 5.21 core (BF-1): `Δ(Hyb₀,Hyb₁) ≤ B(T+1+nV)` in the nontrivial case, and exact
agreement in the exceptional case.  `exp₀ exp₁` are the concrete monadic hybrids,
`HybridTVDist exp₀ exp₁` the concrete statistical distance, and `IdenticalDistributions exp₀
exp₁` the concrete exceptional-agreement fact. -/
def Claim521Core {U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    {α : Type} (exp₀ exp₁ : ProbComp α) (T nV : ℕ) : Prop :=
  (ExceptionalEmpty T nV → IdenticalDistributions exp₀ exp₁) ∧
    (¬ ExceptionalEmpty T nV → HybridTVDist exp₀ exp₁ ≤ badEventBound U (T + 1 + nV))

/-- Claim 5.24 core (BF-1 + BF-2): `Δ(Hyb₃,Hyb₄) ≤ Dcap T nV` in the nontrivial case, and
exact agreement in the exceptional case.  Claim 5.24 must use the `Dcap` exceptional split,
**not** a fictitious negative `Dcap 0 0` bound. -/
def Claim524Core {U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    {α : Type} (exp₃ exp₄ : ProbComp α) (T nV : ℕ) : Prop :=
  (ExceptionalEmpty T nV → IdenticalDistributions exp₃ exp₄) ∧
    (¬ ExceptionalEmpty T nV → HybridTVDist exp₃ exp₄ ≤ Dcap U T nV)

/-! ## Ceiling compatibility (never an `N_𝒱`-slot bound)

The non-final relaxation `N_𝒱 ≤ Lbar` (paper eqs. 6–7 +
`buildPhaseSchedule_queryIndex_le`) is recorded here purely as a compatibility specification,
kept away from every `N_𝒱` final bound.  It is stated as a `Prop` (a specification of what the
schedule layer proves), not proved here. -/

def nV_le_Lbar (nV Lbar : ℕ) : Prop := nV ≤ Lbar

end Statement

end DuplexSpongeFS
