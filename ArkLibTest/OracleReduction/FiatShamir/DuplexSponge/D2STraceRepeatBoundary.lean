/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLibTest.OracleReduction.FiatShamir.DuplexSponge.D2SQueryCachePop

/-!
# Repeated round-boundary queries in the line-4 traces

Regression test for the CO25 Lemma 5.1 trace comparison. `D2SAlgo` answers a repeated `gᵢ` key
from its `tr_i` memo without querying `f` (§5.4 D2SAlgo Item 3(a)), so the `Hyb₄` prover trace
has one entry per distinct key. StdTrace adds an entry for every repeat of a round-boundary
`p`-query (§5.5.1 Item 4(a)ivA), so `D2STrace` must keep only the first entry of each key per
source segment for the two traces to agree.

* `d2sTraceSalted_repeatBoundary`: a prover that queries the same boundary state twice yields
  one prover entry (it yielded two before `dedupChallengesPerSource`).
* `d2sTraceSalted_nodup`, `hyb1Line4Trace_nodup`, `hyb2Line4Trace_nodup`: no line-4 trace map
  repeats a challenge query within a source.
* `dedupChallengesPerSource_of_nodup` (in the library) keeps a `Hyb₄`-shaped trace unchanged.
-/

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS DuplexSpongeFS.TraceTransform
open DuplexSpongeFS.DSTraceStorage DuplexSpongeFS.Backtrack DuplexSpongeFS.Lookahead

namespace ArkLibTest.D2STraceRepeatBoundary

section Generic

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} [DecidableEq StmtIn]
  {n : ℕ} {pSpec : ProtocolSpec n} {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [codec : Codec pSpec U] [∀ i, Fintype (pSpec.Message i)] {δ : ℕ}
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U] {Salt : Type} [SaltCodec U δ Salt]

/-- A prover that hashes `x` and then queries the same round-boundary state `s` twice. -/
def repeatLog (x : StmtIn) (c : Vector U SpongeSize.C) (s o : CanonicalSpongeState U) :
    TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) :=
  [(.prover, ⟨.inr (.inl x), c⟩), (.prover, ⟨.inr (.inr (.inl s)), o⟩),
   (.prover, ⟨.inr (.inr (.inl s)), o⟩)]

/-- The duplex-sponge trace of `repeatLog`. -/
def repeatTrace (x : StmtIn) (c : Vector U SpongeSize.C) (s o : CanonicalSpongeState U) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  [⟨.inl x, c⟩, ⟨.inr (.inl s), o⟩, ⟨.inr (.inl s), o⟩]

/-- When `BackTrack` recognises `s` as a round boundary, `D2STrace` of `repeatLog` holds a single
prover entry for that round, as the `Hyb₄` prover trace does. -/
theorem d2sTraceSalted_repeatBoundary
    (x : StmtIn) (c : Vector U SpongeSize.C) (s o : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (ρ : Vector U (challengeSize out.roundIdx))
    (e : Sigma (fsChallengeOracle (StmtIn × Salt) pSpec))
    (hBT : backTrackFwd (δ := δ) (pSpec := pSpec) (repeatTrace x c s o)
      (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) (repeatTrace x c s o))
      (TraceNabla.ofQueryLogForwardOnly_isSubset _) s 4 = .some out)
    (hImg : stdTraceInCodecImage out = true)
    (hLA : lookAhead (pSpec := pSpec)
      (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) (repeatTrace x c s o)).p
      s out.roundIdx = pure (.some ρ))
    (hMap : stdTraceEntryToFSQuerySalted? (Salt := Salt) ⟨out, ρ⟩ = some e) :
    (d2sTraceSalted (T_H := T_H) (T_P := T_P) (Salt := Salt) (δ := δ) (pSpec := pSpec)
      (repeatLog (oSpec := oSpec) x c s o)).run =
      pure (some [(.prover, ⟨.inr e.1, e.2⟩)]) := by
  have hds : dsTraceOfLog (oSpec := oSpec) (TaggedQueryLog.untagged (repeatLog x c s o)) =
      repeatTrace x c s o := rfl
  simp only [d2sTraceSalted, hds]
  simp only [repeatLog, d2sTraceSalted.go, stdTraceHandlePQuery, stdTraceDelta]
  simp only [repeatTrace] at hBT hLA
  simp only [repeatTrace, List.length_cons, List.length_nil, hBT]
  simp only [stdTraceHandleBacktrackTuple, hImg, ite_true, stdTraceLookupOrLookAhead]
  simp [lookupStdTraceMemo, hLA, StdTraceState.appendMemoAndEntry, StdTraceState.appendEntry,
    insertStdTraceMemo, hMap, dedupChallengesPerSource, dedupChallengesPerSourceAux]

/-- `D2STrace` never repeats a challenge query within a source segment. -/
theorem d2sTraceSalted_nodup
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (h : some out ∈ support (d2sTraceSalted (T_H := T_H) (T_P := T_P) (Salt := Salt) (δ := δ)
      (pSpec := pSpec) log).run) :
    (challengeKeys out).Nodup := by
  simp only [d2sTraceSalted, OptionT.run_map, support_map, Set.mem_image] at h
  obtain ⟨y, -, hy⟩ := h
  cases y with
  | none => simp at hy
  | some y =>
      simp only [Option.map_some, Option.some.injEq] at hy
      exact hy ▸ nodup_challengeKeys_dedupChallengesPerSource y

omit [DecidableEq StmtIn] [SpongeSize] in
/-- The `Hyb₁` line-4 map never repeats a challenge query within a source segment. -/
theorem hyb1Line4Trace_nodup
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ))
    (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (h : some out ∈ support (hyb1Line4Trace (Salt := Salt) log).run) :
    (challengeKeys out).Nodup := by
  simp only [hyb1Line4Trace, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq] at h
  exact h ▸ nodup_challengeKeys_dedupChallengesPerSource _

omit [DecidableEq StmtIn] [SpongeSize] in
/-- The `Hyb₂` line-4 map never repeats a challenge query within a source segment. -/
theorem hyb2Line4Trace_nodup
    (log : TaggedQueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ))
    (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (h : some out ∈ support (hyb2Line4Trace (Salt := Salt) log).run) :
    (challengeKeys out).Nodup := by
  simp only [hyb2Line4Trace, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
    Option.some.injEq] at h
  exact h ▸ nodup_challengeKeys_dedupChallengesPerSource _

end Generic

/-! ### The hypotheses of `d2sTraceSalted_repeatBoundary` hold on a toy run

One round with `r = c = 1`, `ℓ_P = ℓ_V = 1` and `δ = 0` (the toy of `D2SQueryCachePop`): the
prover hashes `()` to `10`, absorbs its message into `s = (0, 10)` and queries `p(s)` twice.
`BackTrack` recognises `s` as the boundary of the only round, and `LookAhead` returns the rate of
`p(s)` without drawing any randomness, so it is `pure`. (The codec image check and the `φ⁻¹`
remap succeed because the message type is `Unit`.) -/

section Toy

open ArkLibTest.D2SQueryCachePop

local instance : SpongeSize := ⟨2, 1, by omega⟩

/-- The duplex-sponge trace of the toy prover. -/
def toyTrace : QueryLog (duplexSpongeChallengeOracle Unit UInt8) :=
  repeatTrace () #v[10] #v[0, 10] #v[1, 11]

/-- The toy forward-only `tr_∇`. -/
def toyIndex : ListBacked.DefaultTraceDelta Unit UInt8 :=
  TraceNabla.ofQueryLogForwardOnly toyTrace

/-- `BackTrack`'s answer at `s`: the recovered round index, or `none`/`err`. -/
def toyBackTrack : String :=
  letI := codecPS 1 1
  match backTrackFwd (δ := 0) (pSpec := pS 1) toyTrace toyIndex
      (TraceNabla.ofQueryLogForwardOnly_isSubset _) #v[0, 10] 4 with
  | .some out => s!"some (round {out.roundIdx.1.val})"
  | .noResult => "none"
  | .err => "err"

/-- `LookAhead`'s answer at `s` and the number of `𝒰(Σ)` draws it made. -/
def toyLookAhead : String × ℕ :=
  letI := codecPS 1 1
  let impl : QueryImpl (Unit →ₒ UInt8) (StateM ℕ) := fun () => do
    modify (· + 1)
    pure 0
  let (r, draws) := (simulateQ impl (lookAhead (pSpec := pS 1) toyIndex.p #v[0, 10]
    ⟨1, by decide⟩)).run 0
  match r with
  | .some ρ => (s!"some {ρ.toList}", draws)
  | .noResult => ("none", draws)
  | .err => ("err", draws)

/-- info: "some (round 1)" -/
#guard_msgs in
#eval toyBackTrack

/-- info: ("some [1]", 0) -/
#guard_msgs in
#eval toyLookAhead

end Toy

/-! ### `dedupChallengesPerSource` on a concrete log -/

section Dedup

/-- A log over an ambient `Bool` oracle and a challenge oracle `ℕ → ℕ`. -/
abbrev Log := TaggedQueryLog ((Unit →ₒ Bool) + (ℕ →ₒ ℕ))

/-- The prover asks challenge `1` twice (with an ambient query in between); the verifier asks
challenges `1` and `2`. -/
def toyLog : Log :=
  [(.prover, ⟨.inr 1, (5 : ℕ)⟩), (.prover, ⟨.inl (), true⟩), (.prover, ⟨.inr 1, (5 : ℕ)⟩),
   (.verifier, ⟨.inr 1, (5 : ℕ)⟩), (.verifier, ⟨.inr 2, (7 : ℕ)⟩)]

/-- Only the prover's repeat of challenge `1` is dropped; the verifier keeps its own copy. -/
example : dedupChallengesPerSource toyLog =
    [(.prover, ⟨.inr 1, (5 : ℕ)⟩), (.prover, ⟨.inl (), true⟩),
     (.verifier, ⟨.inr 1, (5 : ℕ)⟩), (.verifier, ⟨.inr 2, (7 : ℕ)⟩)] := by
  simp [dedupChallengesPerSource, dedupChallengesPerSourceAux, toyLog]

end Dedup

end ArkLibTest.D2STraceRepeatBoundary
