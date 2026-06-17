/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Rewinding.Coupling

/-!
  # `oSpec`-randomness-as-tape (`SeededReplay` / `LawfulSeededReplay`)

  The ArkLib analog of VCVio's `seededOracle`, as the abstract hypothesis under which a replay fork
  is deterministic in its edited challenge: the ambient `oSpec` randomness is fixed as a **second
  tape** alongside the challenge tape. Data (`SeededReplay`) carries the tape factorization; laws
  (`LawfulSeededReplay`) are a proof-irrelevant `Prop` class. `oSpec`-generic; no CWSS.

  See `docs/general-replay-fork-design.md` §3 and `docs/cwss-seeded-replay-plan.md` §2.3.

  `consistent` and `lawful_ofDeterministic` are proved; the `ofUniformSeed` / truth-table-RO
  constructors are future work.
-/

noncomputable section

open OracleComp OracleSpec

namespace QueryImpl

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Data**: the `oSpec`-tape factorization of `impl` w.r.t. an initial-state draw `init`. `pin t`
  is the deterministic per-tape implementation; `genTape` draws the tape, `pinInit t` the matching
  initial state. -/
structure SeededReplay (impl : QueryImpl oSpec (StateT σ ProbComp)) (init : ProbComp σ) where
  /-- The tape type (e.g. `Unit` for empty `oSpec`, a `QuerySeed` for a uniform RO). -/
  Tape : Type
  /-- Draw a tape. -/
  genTape : ProbComp Tape
  /-- The initial ambient state matching a tape. -/
  pinInit : Tape → ProbComp σ
  /-- The pinned (tape-indexed) implementation. -/
  pin : Tape → QueryImpl oSpec (StateT σ ProbComp)

/-- **Laws** (proof-irrelevant): each `pin t` is deterministic and stateless, and drawing the tape
  then pinning faithfully reproduces the live `evalDist`. `consistent` (replay-consistency of each
  `pin t`) is derived from `det ∧ stateless`. -/
class LawfulSeededReplay {impl : QueryImpl oSpec (StateT σ ProbComp)} {init : ProbComp σ}
    (s : SeededReplay impl init) : Prop where
  /-- Each pinned implementation is deterministic (subsingleton support per state). -/
  det : ∀ t, (s.pin t).IsDeterministic
  /-- Each pinned implementation is stateless: the answer is a function of `(t, q)` only. -/
  stateless : ∀ (t : s.Tape) (q : ι), ∃ a : oSpec.Range q,
    ∀ (st : σ) (a' : oSpec.Range q) (st' : σ),
      (a', st') ∈ support ((s.pin t q).run st) → a' = a
  /-- Drawing the tape then pinning faithfully reproduces the live `evalDist`. -/
  faithful : ∀ {α : Type} (oa : OracleComp oSpec α),
    evalDist (do let t ← s.genTape; let st ← s.pinInit t; (simulateQ (s.pin t) oa).run st)
      = evalDist (do let st ← init; (simulateQ impl oa).run st)

/-- **Derived**: each pinned implementation is replay-consistent (from `det ∧ stateless`). This is
  what lets the structural fork guarantees apply under `s.pin t` with no standalone
  `impl.ReplayConsistent`. -/
theorem LawfulSeededReplay.consistent {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {init : ProbComp σ} (s : SeededReplay impl init) [LawfulSeededReplay s] (t : s.Tape) :
    (s.pin t).ReplayConsistent := by
  -- `stateless` already pins each answer to a common witness; `det`/reachability are not needed.
  intro q sa s₁ a hmem₁ s₂ _hreach a' s₃ hmem₂
  obtain ⟨a₀, ha₀⟩ := (‹LawfulSeededReplay s›).stateless t q
  exact (ha₀ s₂ a' s₃ hmem₂).trans (ha₀ sa a s₁ hmem₁).symm

/-- Trivial tape for an empty/deterministic `oSpec`: `Tape := Unit`, `pin _ := impl`. -/
def SeededReplay.ofDeterministic (impl : QueryImpl oSpec (StateT σ ProbComp)) (init : ProbComp σ) :
    SeededReplay impl init where
  Tape := Unit
  genTape := pure ()
  pinInit := fun _ => init
  pin := fun _ => impl

/-- Laws for `ofDeterministic`, given the impl is deterministic and stateless: `pin _ = impl`,
  `genTape = pure ()`, and `pinInit _ = init`, so `det`/`stateless` are the hypotheses and
  `faithful` collapses by `pure_bind`. The empty-`oSpec` instance is the special case where the
  hypotheses are vacuous; the uniform-RO instance (`ofUniformSeed`, TODO) discharges `faithful`
  from VCVio's `probOutput_generateSeed_bind_map_simulateQ`. -/
theorem SeededReplay.lawful_ofDeterministic (impl : QueryImpl oSpec (StateT σ ProbComp))
    (init : ProbComp σ) (hdet : impl.IsDeterministic)
    (hstateless : ∀ (q : ι), ∃ a : oSpec.Range q,
      ∀ (st : σ) (a' : oSpec.Range q) (st' : σ),
        (a', st') ∈ support ((impl q).run st) → a' = a) :
    LawfulSeededReplay (SeededReplay.ofDeterministic impl init) := by
  -- `pin _ = impl`, `genTape = pure ()`, `pinInit _ = init`, so the laws are the hypotheses and
  -- `faithful` collapses by `pure_bind`.
  refine ⟨fun _ => hdet, fun _ q => hstateless q, ?_⟩
  intro α oa
  simp only [SeededReplay.ofDeterministic, pure_bind]

end QueryImpl
