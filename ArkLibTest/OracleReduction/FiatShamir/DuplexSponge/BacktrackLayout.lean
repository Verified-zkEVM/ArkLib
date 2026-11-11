/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack

/-!
# BackTrack against the real duplex-sponge layout

These checks run the real `DuplexSponge.absorb` and `DuplexSponge.squeeze`, the calls of
`Messages.deriveTranscriptDSFSSalted`, on a concrete mixing permutation of `UInt8^(r+4)`. They
log every permutation call, and run `backTrackFwd` at every permutation input of the honest run,
on the trace before that call:

- at the first permutation call of the challenge-`i` squeeze, BackTrack returns
  `(i, x, τ, α̂_1, …, α̂_i)`;
- at every other permutation input, BackTrack returns `none`.

The protocols alternate `k` messages and challenges. The grid covers `r ∈ {1, 2, 3}`,
`δ ∈ {0, …, 4}`, `k ∈ {1, 2}` with message and challenge lengths in `{1, 2, 3}`, and selected
`k = 3` schedules.
-/

open DuplexSpongeFS DuplexSpongeFS.Backtrack DuplexSpongeFS.DSTraceStorage ProtocolSpec
  OracleComp OracleSpec

namespace BacktrackLayoutTest

abbrev St [SpongeSize] := CanonicalSpongeState UInt8

/-- A bijection of `UInt8^N` that mixes every unit: three passes of `v[i] += f(v[i+1 mod N]) + i`.
-/
def perm [SpongeSize] (s : St) : St := Id.run do
  let mut v : Vector UInt8 SpongeSize.N := s
  for pass in List.range 3 do
    for i in List.range SpongeSize.N do
      let y := v.toArray.getD ((i + 1) % SpongeSize.N) 0
      let d : UInt8 := y * y * 29 + 17 * y + 91 + pass.toUInt8 * 13 + i.toUInt8
      v := Vector.ofFn fun k => if k.val = i then v[k] + d else v[k]
  return v

/-- Answer `p` with `perm` and log the query-answer pair. -/
def logImpl [SpongeSize] : QueryImpl (forwardPermutationOracle St) (StateM (List (St × St))) :=
  fun s => do
    let o := perm s
    modify (· ++ [(s, o)])
    pure o

def runP [SpongeSize] {α : Type} (c : OracleComp (forwardPermutationOracle St) α)
    (log : List (St × St)) : α × List (St × St) :=
  (simulateQ logImpl c).run log

/-- The capacity `h(x)` of the statement `x = ()`. -/
def cap0 [SpongeSize] : Vector UInt8 SpongeSize.C := Vector.ofFn fun k => 70 + k.val.toUInt8

/-- `DS.Start(x)`: the state `(0^r, h(x))`, `i_A = 0`, `i_S = r`. -/
def startSponge [SpongeSize] : CanonicalDuplexSponge UInt8 :=
  { state := (Vector.replicate SpongeSize.R (0 : UInt8) ++ cap0).cast (by
      have := SpongeSize.R_lt_N; simp only [SpongeSize.C]; omega)
    absorbPos := 0, squeezePos := Fin.last SpongeSize.R }

/-- The `(h, p)`-trace of a run: the `h` query of `Start`, then the logged permutation calls. -/
def toTrace [SpongeSize] (log : List (St × St)) : DuplexSpongeTrace Unit UInt8 :=
  (⟨.inl (), cap0⟩ : duplexSpongeTraceEntry (StartType := Unit) (U := UInt8)) ::
    log.map fun (a, b) =>
      (⟨.inr (.inl a), b⟩ : duplexSpongeTraceEntry (StartType := Unit) (U := UInt8))

/-- `k` alternating rounds `P, V, …, P, V`. -/
def altSpec (k : Nat) : ProtocolSpec (2 * k) :=
  ⟨fun i => if i.val % 2 = 0 then .P_to_V else .V_to_P, fun _ => Unit⟩

/-- A comparable view of a BackTrack result: `none` for `err`; otherwise `none` for paper-`none`,
or the flat challenge index, the salt and the messages. -/
abbrev View := Option (Nat × List UInt8 × List (List UInt8))

def view [SpongeSize] {n : ℕ} {pS : ProtocolSpec n} [HasMessageSize pS] [HasChallengeSize pS]
    {δ : Nat} :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := Unit) (pSpec := pS) (U := UInt8)) →
      Option View
  | .err => none
  | .noResult => some none
  | .some o => some (some (o.roundIdx.1.val, o.salt.toList,
      (List.finRange n).filterMap fun j =>
        if h : pS.dir j = .P_to_V ∧ j.val < o.roundIdx.1.val then
          some (o.encodedMessages ⟨⟨j, h.1⟩, by simpa using h.2⟩).toList else none))

/-- `backTrackFwd` on the trace of `log`, with StdTrace's forward-only `tr_∇`. -/
def runBT [SpongeSize] {n : ℕ} (pS : ProtocolSpec n) [HasMessageSize pS] [HasChallengeSize pS]
    (δ : Nat) (log : List (St × St)) (s : St) : Option View :=
  let trace := toTrace log
  let trΔ : ListBacked.DefaultTraceDelta Unit UInt8 := TraceNabla.ofQueryLogForwardOnly trace
  view (backTrackFwd (δ := δ) (pSpec := pS) trace trΔ
    (TraceNabla.ofQueryLogForwardOnly_isSubset trace) s)

def saltOf (δ : Nat) : List UInt8 := (List.range δ).map fun t => (100 + t).toUInt8

def msgOf (i ℓ : Nat) : List UInt8 := (List.range ℓ).map fun t => (16 * (i + 1) + t).toUInt8

/-- The honest run `Start; Absorb(τ); Absorb(α̂_1); Squeeze(ℓ_V(1)); …`. Returns the permutation
log and, for each challenge, the index of its first permutation call, read off the real sponge as
the log length when the squeeze starts. -/
def honest [SpongeSize] (δ : Nat) (lp lv : List Nat) : List (St × St) × List Nat := Id.run do
  let (s, log) := runP (DuplexSponge.absorb startSponge (saltOf δ)) []
  let mut s := s
  let mut log := log
  let mut bds : List Nat := []
  for i in List.range lp.length do
    let (s', log') := runP (DuplexSponge.absorb s (msgOf i (lp.getD i 0))) log
    bds := bds ++ [log'.length]
    let ((_, s''), log'') := runP (DuplexSponge.squeeze s' (lv.getD i 0)) log'
    s := s''
    log := log''
  return (log, bds)

/-- Run `body` with the protocol, the honest log and the boundary indices of one schedule. -/
def withSchedule [SpongeSize] {α : Type} (lp lv : List Nat) (δ : Nat)
    (body : (pS : ProtocolSpec (2 * lp.length)) → [HasMessageSize pS] → [HasChallengeSize pS] →
      List (St × St) → List Nat → α) : α :=
  let pS := altSpec lp.length
  letI : HasMessageSize pS := ⟨fun j => lp.getD (j.1.val / 2) 0⟩
  letI : HasChallengeSize pS := ⟨fun j => lv.getD (j.1.val / 2) 0⟩
  let (log, bds) := honest δ lp lv
  body pS log bds

/-- The expected BackTrack view at the first permutation call of the `i`-th challenge. -/
def expected (δ : Nat) (lp : List Nat) (i : Nat) : View :=
  some (2 * i + 1, saltOf δ, (List.range (i + 1)).map fun j => msgOf j (lp.getD j 0))

/-- Permutation indices `q` where BackTrack disagrees with the honest run. -/
def honestFailures [SpongeSize] (δ : Nat) (lp lv : List Nat) : List Nat :=
  withSchedule lp lv δ fun pS _ _ log bds =>
    (List.range log.length).filter fun q =>
      let got := runBT pS δ (log.take q) (log.getD q (perm 0, perm 0)).1
      match bds.idxOf? q with
      | some i => got != some (expected δ lp i)
      | none => got != some none

/-- Boundary indices `q` where changing one unit of the state still gives the honest tuple. -/
def injectivityFailures [SpongeSize] (δ : Nat) (lp lv : List Nat) : List Nat :=
  withSchedule lp lv δ fun pS _ _ log bds =>
    (List.range bds.length).filterMap fun i =>
      let q := bds.getD i 0
      let s := (log.getD q (perm 0, perm 0)).1
      if (List.range SpongeSize.N).any fun u =>
          runBT pS δ (log.take q) (Vector.ofFn fun k => if k.val = u then s[k] + 1 else s[k]) ==
            some (expected δ lp i)
      then some q else none

/-- All schedules of `k` rounds with lengths in `sizes`. -/
def schedules (sizes : List Nat) (k : Nat) : List (List Nat × List Nat) :=
  let vecs := (List.range k).foldl (fun acc _ => acc.flatMap fun v => sizes.map (v ++ [·])) [[]]
  vecs.flatMap fun lp => vecs.map fun lv => (lp, lv)

/-- Selected three-round schedules. -/
def threeRound : List (List Nat × List Nat) :=
  [([1, 1, 1], [1, 1, 1]), ([2, 3, 1], [3, 1, 2]), ([4, 1, 3], [1, 4, 2]), ([3, 4, 4], [4, 3, 1])]

def grid : List (Nat × List Nat × List Nat) :=
  (List.range 5).flatMap fun δ =>
    (schedules [1, 2, 3] 1 ++ schedules [1, 2, 3] 2 ++ threeRound).map fun (lp, lv) => (δ, lp, lv)

def honestGridOk [SpongeSize] : Bool :=
  grid.all fun (δ, lp, lv) => (honestFailures δ lp lv).isEmpty

def injectiveGridOk [SpongeSize] : Bool :=
  grid.all fun (δ, lp, lv) => (injectivityFailures δ lp lv).isEmpty

abbrev sz1 : SpongeSize := { N := 5, R := 1 }
abbrev sz2 : SpongeSize := { N := 6, R := 2 }
abbrev sz3 : SpongeSize := { N := 7, R := 3 }

/-! ## Honest recovery (packing-aware layout)

With `r = 2`, `δ = 1`, a printed-paper layout returns `none` for round 1 and labels `α̂_2` as
`α̂_1` at round 2. With `δ = 0`, it never recognizes round 2. -/

/-- info: true -/
#guard_msgs in
#eval (letI := sz2; honestFailures 1 [1, 1] [1, 1]).isEmpty
/-- info: true -/
#guard_msgs in
#eval (letI := sz2; honestFailures 0 [1, 1] [1, 1]).isEmpty
/-- info: true -/
#guard_msgs in
#eval (letI := sz1; honestGridOk)
/-- info: true -/
#guard_msgs in
#eval (letI := sz2; honestGridOk)
/-- info: true -/
#guard_msgs in
#eval (letI := sz3; honestGridOk)

/-! ## Injectivity at challenge boundaries

Every rate unit of every chain input is either returned as absorbed data or compared with the
preceding state, including the units of the `Start` block that the absorbed data does not reach
(`0^r`). So changing any unit of an honest boundary state never gives the honest tuple. -/

/-- The three states of the review's distinguisher: `r = 2`, `δ = 0`, `ℓ_P = 1`, trace `[h() ↦ c]`.
Only the honest state `(11, 0, c)`, whose `Start` rate tail is `0`, maps to round 1. -/
def startTail [SpongeSize] (u : UInt8) : Option View :=
  let pS := altSpec 1
  letI : HasMessageSize pS := ⟨fun _ => 1⟩
  letI : HasChallengeSize pS := ⟨fun _ => 1⟩
  runBT pS 0 [] (Vector.ofFn fun k => if k.val = 0 then 11 else if k.val < SpongeSize.R then u
    else cap0.toArray.getD (k.val - SpongeSize.R) 0)

/-- info: [some (some (1, [], [[11]])), some none, some none] -/
#guard_msgs in
#eval (letI := sz2; [startTail 0, startTail 1, startTail 200])
/-- info: true -/
#guard_msgs in
#eval (letI := sz1; injectiveGridOk)
/-- info: true -/
#guard_msgs in
#eval (letI := sz2; injectiveGridOk)
/-- info: true -/
#guard_msgs in
#eval (letI := sz3; injectiveGridOk)

end BacktrackLayoutTest
