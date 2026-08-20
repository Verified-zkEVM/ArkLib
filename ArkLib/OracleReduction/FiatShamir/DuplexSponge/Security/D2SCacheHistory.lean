/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRateOnlyCache

/-!
# State for the rate-only D2S cache

This file retains its historical import path, but the obsolete full-state `Cache_p` and its
history have been removed.  The revised simulator stores only a keyed, rate-only tail.  A
capacity is sampled exactly when a forward query consumes that tail.
-/

open OracleComp OracleSpec ProtocolSpec
namespace DuplexSpongeFS.ProverTransform
open Backtrack DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : Nat}

local instance : Inhabited U := ⟨0⟩
noncomputable section

section D2SCacheHistory

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 Item 1 — internal mutable state of the revised `D2SQuery` wrapper.

- `trace` (`tr`) is the insertion-ordered query trace.
- `rateCacheP` (`Cache_p`) maps a state key to a pending rate-only continuation.  It contains no
  output capacity and hence no latent full permutation pair.
- `trΔ` (`tr_∇`) is the deduplicated lookup index for the trace.

The `gᵢ` response memo remains at the `D2SAlgo` bridge layer, as in the paper. -/
structure D2SQueryState where
  /-- `tr`: insertion-ordered `h`/`p`/`p⁻¹` query-answer pairs. -/
  trace : QueryLog (duplexSpongeChallengeOracle StmtIn U) := []
  /-- Revised `Cache_p`: a state key and pending rate blocks only. -/
  rateCacheP : List (RateOnlyCacheEntry (U := U)) := []
  /-- `tr_∇`: deduplicated index for `inlu`/`outlu` lookups. -/
  trΔ : TraceNabla T_H T_P StmtIn U :=
    ⟨TraceTableOps.empty, TraceTableOps.empty⟩
  /-- Every table entry occurs in `trace`. -/
  h_inv : trΔ.IsSubsetOfQueryLog trace
  /-- The tables contain exactly the distinct normalized entries of `trace`. -/
  h_mirror : trΔ.MirrorsQueryLog trace
  /-- Binds the protocol parameters without placing the `gᵢ` memo in this state. -/
  _phantom : Option (BacktrackOutput
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := none

instance : Inhabited (D2SQueryState
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  ⟨{ h_inv := TraceNabla.IsSubsetOfQueryLog_empty_nil
     h_mirror := TraceNabla.MirrorsQueryLog_empty_nil }⟩

end D2SCacheHistory

end

end DuplexSpongeFS.ProverTransform
