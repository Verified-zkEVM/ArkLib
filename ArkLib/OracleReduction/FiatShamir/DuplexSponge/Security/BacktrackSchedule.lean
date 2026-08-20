/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.QueryCounting

/-!
# Stateful schedule for BackTrack

This is the value-free part of the Section 5.2 repair.  It records the three
pieces of state that a scalar `L_ptr` loses: the number of emitted forward
permutation queries and the current absorb/squeeze positions.  It deliberately
contains no trace search or candidate extraction; those layers consume this
schedule to generate write locations and untouched-coordinate frames.
-/

namespace DuplexSpongeFS.Backtrack

open OracleComp OracleSpec

/-- The value-free cursor of a lazy duplex sponge.  `queryIndex` is the number
of forward permutation calls already emitted; `absorbOffset` and `squeezeOffset`
are positions in the current rate block. -/
structure ScheduleCursor where
  queryIndex : ℕ
  absorbOffset : ℕ
  squeezeOffset : ℕ
deriving DecidableEq, Repr

namespace ScheduleCursor

/-- A rate coordinate of a prospective permutation-query input.  The location
`(q, x)` means the `x`-th rate element of `in_q`; `q` can name the terminal
upcoming input of a backtrack chain. -/
structure RateLocation where
  queryIndex : ℕ
  rateOffset : ℕ
deriving DecidableEq, Repr

/-- Public lengths of one prover-message / verifier-challenge phase.  This is
the length-only projection of a DSFS round used by the parser layout. -/
structure RoundShape where
  messageLength : ℕ
  challengeLength : ℕ
deriving DecidableEq, Repr

/-- One actual protocol phase.  Unlike `RoundShape`, this form does not assume
that prover-message and verifier-challenge phases alternate.  The generic
`ProtocolSpec` permits consecutive phases of either direction, so the
stateful BackTrack parser replays this representation. -/
inductive PhaseShape where
  | absorb (messageLength : ℕ)
  | squeeze (challengeLength : ℕ)
deriving DecidableEq, Repr

/-- Ceiling-style upper bound for one actual protocol phase.  It is an upper
bound, not an asserted exact count: a phase may resume a partially used rate
block and emit fewer permutation queries. -/
def phaseQueryBound (R : ℕ) : PhaseShape → ℕ
  | .absorb len => (len + R - 1) / R
  | .squeeze len => (len + R - 1) / R

/-- Additive static upper bound for a list of actual protocol phases. -/
def phaseQueryBudget (R : ℕ) (phases : List PhaseShape) : ℕ :=
  (phases.map (phaseQueryBound R)).sum

/-- Layout facts for one protocol round.  `firstSqueezeQuery` is absent exactly
when the verifier challenge is empty; `postSqueezeQuery` is the next query
index after the round. -/
structure RoundLayout where
  messageLocations : List RateLocation
  firstSqueezeQuery : Option ℕ
  postSqueezeQuery : ℕ
deriving DecidableEq, Repr

/-- A complete value-free parser layout.  The eventual candidate validator
uses its location lists to recover source units and its first-squeeze markers
to decide whether the terminal query is programmable. -/
structure Layout where
  saltLocations : List RateLocation
  roundLayouts : List RoundLayout
  finalCursor : ScheduleCursor
deriving DecidableEq, Repr

/-- Layout facts for one actual protocol phase.  Only absorb phases contain
source locations; only nonempty squeezes beginning at a rate boundary contain
a programming point. -/
structure PhaseLayout where
  sourceLocations : List RateLocation
  firstSqueezeQuery : Option ℕ
  postQuery : ℕ
deriving DecidableEq, Repr

/-- Complete layout for an arbitrary sequence of protocol phases. -/
structure PhaseSchedule where
  saltLocations : List RateLocation
  phaseLayouts : List PhaseLayout
  finalCursor : ScheduleCursor
deriving DecidableEq, Repr

/-- One absorb write.  If the rate is full, the permutation preceding that
write is emitted first.  Every absorb invalidates the squeeze cursor. -/
def absorbOne (R : ℕ) (cursor : ScheduleCursor) : ScheduleCursor :=
  if cursor.absorbOffset = R then
    { queryIndex := cursor.queryIndex + 1, absorbOffset := 1, squeezeOffset := R }
  else
    { queryIndex := cursor.queryIndex, absorbOffset := cursor.absorbOffset + 1,
      squeezeOffset := R }

/-- Location written by the next absorbed unit.  When the absorb cursor is
full, `DS.Absorb` first emits query `q`, so that unit belongs to the following
prospective input `in_(q+1)` at rate offset zero. -/
def absorbWriteLocation (R : ℕ) (cursor : ScheduleCursor) : RateLocation :=
  if cursor.absorbOffset = R then
    ⟨cursor.queryIndex + 1, 0⟩
  else
    ⟨cursor.queryIndex, cursor.absorbOffset⟩

/-- Simulate `DS.Absorb` on a string of the given length, ignoring its values. -/
def absorb (R : ℕ) : ScheduleCursor → ℕ → ScheduleCursor
  | cursor, 0 => { cursor with squeezeOffset := R }
  | cursor, len + 1 => absorb R (absorbOne R cursor) len

/-- The write locations and final cursor for a value-free absorb.  Its list
order is the source-string order, so a salt/message can be recovered by
reading these locations in order from a validated backtrack chain. -/
def absorbWithLocations (R : ℕ) : ScheduleCursor → ℕ → List RateLocation × ScheduleCursor
  | cursor, 0 => ([], absorb R cursor 0)
  | cursor, len + 1 =>
      let tail := absorbWithLocations R (absorbOne R cursor) len
      (absorbWriteLocation R cursor :: tail.1, tail.2)

/-- One squeeze read.  If the rate is exhausted, the permutation supplying the
next output unit is emitted first.  A nonempty squeeze clears the absorb cursor. -/
def squeezeOne (R : ℕ) (cursor : ScheduleCursor) : ScheduleCursor :=
  if cursor.squeezeOffset = R then
    { queryIndex := cursor.queryIndex + 1, absorbOffset := 0, squeezeOffset := 1 }
  else
    { queryIndex := cursor.queryIndex, absorbOffset := 0,
      squeezeOffset := cursor.squeezeOffset + 1 }

/-- Simulate `DS.Squeeze` on an output of the given length, ignoring output values. -/
def squeeze (R : ℕ) : ScheduleCursor → ℕ → ScheduleCursor
  | cursor, 0 => cursor
  | cursor, len + 1 => squeeze R (squeezeOne R cursor) len

/-- The terminal query classification used by BackTrack.  It is a programming
point only at the first query of a nonempty squeeze that starts at a rate
boundary. -/
def firstSqueezeQuery? (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) : Option ℕ :=
  if len = 0 ∨ cursor.squeezeOffset ≠ R then none else some cursor.queryIndex

/-- Schedule one message/challenge pair.  The first-squeeze marker is computed
after the message absorb, so it correctly handles a message that begins or
ends within a partially used rate block. -/
def scheduleRound (R : ℕ) (cursor : ScheduleCursor) (shape : RoundShape) :
    RoundLayout × ScheduleCursor :=
  let messagePhase := absorbWithLocations R cursor shape.messageLength
  let first := firstSqueezeQuery? R messagePhase.2 shape.challengeLength
  let afterChallenge := squeeze R messagePhase.2 shape.challengeLength
  ({ messageLocations := messagePhase.1
     firstSqueezeQuery := first
     postSqueezeQuery := afterChallenge.queryIndex }, afterChallenge)

/-- Replay one actual protocol phase without inserting a fictitious empty
absorb before a challenge. -/
def schedulePhase (R : ℕ) (cursor : ScheduleCursor) : PhaseShape → PhaseLayout × ScheduleCursor
  | .absorb len =>
      let phase := absorbWithLocations R cursor len
      ({ sourceLocations := phase.1, firstSqueezeQuery := none, postQuery := phase.2.queryIndex },
        phase.2)
  | .squeeze len =>
      let first := firstSqueezeQuery? R cursor len
      let after := squeeze R cursor len
      ({ sourceLocations := [], firstSqueezeQuery := first, postQuery := after.queryIndex }, after)

/-- Replay an arbitrary protocol-phase list.  This is separate from
`buildPhaseSchedule` so its length and prefix properties can be used by the
BackTrack parser and the Section 5 hybrid arguments. -/
def schedulePhases (R : ℕ) : ScheduleCursor →
    List PhaseShape → List PhaseLayout × ScheduleCursor
  | cursor, [] => ([], cursor)
  | cursor, phase :: rest =>
      let current := schedulePhase R cursor phase
      let tail := schedulePhases R current.2 rest
      (current.1 :: tail.1, tail.2)

/-- Build the layout used by BackTrack: absorb the salt first, then schedule
each actual message/challenge round in protocol order. -/
def buildLayout (R : ℕ) (cursor : ScheduleCursor) (saltLength : ℕ) :
    List RoundShape → Layout
  | [] =>
      let saltPhase := absorbWithLocations R cursor saltLength
      { saltLocations := saltPhase.1, roundLayouts := [], finalCursor := saltPhase.2 }
  | shapes =>
      let saltPhase := absorbWithLocations R cursor saltLength
      let rec go : ScheduleCursor → List RoundShape → List RoundLayout × ScheduleCursor
        | cur, [] => ([], cur)
        | cur, shape :: rest =>
            let current := scheduleRound R cur shape
            let tail := go current.2 rest
            (current.1 :: tail.1, tail.2)
      let rounds := go saltPhase.2 shapes
      { saltLocations := saltPhase.1, roundLayouts := rounds.1, finalCursor := rounds.2 }

/-- Build the stateful schedule for the actual direction-labelled protocol
sequence.  Salt is the sole initial absorb; phases are then replayed exactly
in protocol order. -/
def buildPhaseSchedule (R : ℕ) (cursor : ScheduleCursor) (saltLength : ℕ)
    (phases : List PhaseShape) : PhaseSchedule :=
  let saltPhase := absorbWithLocations R cursor saltLength
  let scheduled := schedulePhases R saltPhase.2 phases
  { saltLocations := saltPhase.1
    phaseLayouts := scheduled.1
    finalCursor := scheduled.2 }

/-- The terminal cursor of a scheduled phase list is the ordinary left fold of the one-phase
cursor transition.  This is the value-free composition law used by the stateful replay executor:
the layout component carries locations and markers, while this lemma exposes its exact cursor
semantics without discarding partially used rate positions. -/
lemma schedulePhases_final_eq_foldl (R : ℕ) (cursor : ScheduleCursor)
    (phases : List PhaseShape) :
    (schedulePhases R cursor phases).2 =
      phases.foldl (fun current phase => (schedulePhase R current phase).2) cursor := by
  induction phases generalizing cursor with
  | nil => rfl
  | cons phase rest ih =>
      simp only [schedulePhases, List.foldl_cons]
      exact ih (schedulePhase R cursor phase).2

@[simp] lemma absorb_zero (R : ℕ) (cursor : ScheduleCursor) :
    absorb R cursor 0 = { cursor with squeezeOffset := R } := rfl

@[simp] lemma squeeze_zero (R : ℕ) (cursor : ScheduleCursor) : squeeze R cursor 0 = cursor := rfl

@[simp] lemma absorbWithLocations_zero (R : ℕ) (cursor : ScheduleCursor) :
    absorbWithLocations R cursor 0 = ([], absorb R cursor 0) := rfl

/-- Neither duplex operation can decrease the number of emitted permutation calls.  These
elementary monotonicity facts are kept separate from ceiling bounds: they are what lets the
stateful Section 5 replay reason about the *first actual* squeeze call, rather than a nominal
block offset. -/
lemma queryIndex_le_absorb (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) :
    cursor.queryIndex ≤ (absorb R cursor len).queryIndex := by
  induction len generalizing cursor with
  | zero => simp
  | succ len ih =>
      rw [absorb]
      exact Nat.le_trans (by unfold absorbOne; split <;> simp)
        (ih (absorbOne R cursor))

/-- Squeezing is likewise monotone in the emitted-permutation counter. -/
lemma queryIndex_le_squeeze (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) :
    cursor.queryIndex ≤ (squeeze R cursor len).queryIndex := by
  induction len generalizing cursor with
  | zero => simp
  | succ len ih =>
      rw [squeeze]
      exact Nat.le_trans (by unfold squeezeOne; split <;> simp)
        (ih (squeezeOne R cursor))

/-- The location list contains exactly one coordinate for each absorbed unit. -/
lemma absorbWithLocations_length (R : ℕ) (cursor : ScheduleCursor) :
    ∀ len : ℕ, (absorbWithLocations R cursor len).1.length = len := by
  intro len
  induction len generalizing cursor with
  | zero => rfl
  | succ len ih =>
      simp only [absorbWithLocations]
      exact congrArg Nat.succ (ih (absorbOne R cursor))

/-- Location construction and cursor construction are the same replay: the
second component is exactly `absorb`, not an approximation. -/
lemma absorbWithLocations_cursor (R : ℕ) (cursor : ScheduleCursor) :
    ∀ len : ℕ, (absorbWithLocations R cursor len).2 = absorb R cursor len := by
  intro len
  induction len generalizing cursor with
  | zero => rfl
  | succ len ih =>
      simp only [absorbWithLocations, absorb]
      exact ih (absorbOne R cursor)

/-- Scheduling one direction-labelled action never rewinds the permutation-call counter. -/
lemma queryIndex_le_schedulePhase (R : ℕ) (cursor : ScheduleCursor) (phase : PhaseShape) :
    cursor.queryIndex ≤ (schedulePhase R cursor phase).2.queryIndex := by
  cases phase with
  | absorb len =>
      change cursor.queryIndex ≤ (absorbWithLocations R cursor len).2.queryIndex
      rw [absorbWithLocations_cursor]
      exact queryIndex_le_absorb R cursor len
  | squeeze len =>
      simp only [schedulePhase]
      exact queryIndex_le_squeeze R cursor len

/-- A scheduled suffix preserves every already-emitted permutation call. -/
lemma queryIndex_le_schedulePhases (R : ℕ) (cursor : ScheduleCursor) :
    ∀ phases : List PhaseShape,
      cursor.queryIndex ≤ (schedulePhases R cursor phases).2.queryIndex := by
  intro phases
  induction phases generalizing cursor with
  | nil => simp [schedulePhases]
  | cons phase rest ih =>
      change cursor.queryIndex ≤
        (schedulePhases R (schedulePhase R cursor phase).2 rest).2.queryIndex
      exact Nat.le_trans (queryIndex_le_schedulePhase R cursor phase)
        (ih (schedulePhase R cursor phase).2)

/-- A nonempty squeeze beginning at an untouched rate block emits a real permutation call.
This is the stateful form of the paper's first-marker observation: it counts an actual call rather
than attributing a rounded block to the challenge in advance. -/
lemma squeeze_queryIndex_pos_of_zero_full (R : ℕ) (cursor : ScheduleCursor) (len : ℕ)
    (hquery : cursor.queryIndex = 0) (hfull : cursor.squeezeOffset = R) (hlen : 0 < len) :
    0 < (squeeze R cursor len).queryIndex := by
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  rw [squeeze]
  have hfirst : (squeezeOne R cursor).queryIndex = 1 := by
    simp [squeezeOne, hquery, hfull]
  have htail := queryIndex_le_squeeze R (squeezeOne R cursor) len
  omega

/-- At every point in a schedule started from a fresh rate block, either a forward permutation
call has already occurred or the next squeeze begins at a fresh rate block.  This tiny invariant
is the exact stateful replacement for the paper's informal "the first nonempty challenge makes a
call" argument. -/
def QueryStartedOrSqueezeFull (R : ℕ) (cursor : ScheduleCursor) : Prop :=
  0 < cursor.queryIndex ∨ cursor.squeezeOffset = R

/-- One protocol phase preserves the disjunction needed to find the first actual squeeze call. -/
lemma schedulePhase_queryStartedOrSqueezeFull (R : ℕ) (cursor : ScheduleCursor)
    (h : QueryStartedOrSqueezeFull R cursor) (phase : PhaseShape) :
    QueryStartedOrSqueezeFull R (schedulePhase R cursor phase).2 := by
  rcases h with hq | hs
  · left
    exact lt_of_lt_of_le hq (queryIndex_le_schedulePhase R cursor phase)
  · cases phase with
    | absorb len =>
        right
        change (absorbWithLocations R cursor len).2.squeezeOffset = R
        rw [absorbWithLocations_cursor]
        induction len generalizing cursor with
        | zero => rfl
        | succ len ih =>
            rw [absorb]
            exact ih (absorbOne R cursor) (by
              unfold absorbOne
              split <;> rfl)
    | squeeze len =>
        by_cases hlen : len = 0
        · right
          simp [schedulePhase, hlen, hs]
        · cases hquery : cursor.queryIndex with
          | zero =>
              left
              simpa [schedulePhase] using
                squeeze_queryIndex_pos_of_zero_full R cursor len hquery hs
                  (Nat.pos_of_ne_zero hlen)
          | succ q =>
              left
              exact lt_of_lt_of_le (by simp [hquery])
                (queryIndex_le_schedulePhase R cursor (.squeeze len))

/-- A phase list containing a nonempty verifier squeeze emits at least one actual forward
permutation call.  It is intentionally a trace-count fact, not a rounded block-count estimate. -/
lemma schedulePhases_queryIndex_pos_of_mem_nonempty_squeeze (R : ℕ) (cursor : ScheduleCursor)
    (hStarted : QueryStartedOrSqueezeFull R cursor) :
    ∀ phases : List PhaseShape,
      (∃ len, PhaseShape.squeeze len ∈ phases ∧ 0 < len) →
        0 < (schedulePhases R cursor phases).2.queryIndex := by
  intro phases
  induction phases generalizing cursor with
  | nil =>
      simp
  | cons phase rest ih =>
      rintro ⟨len, hmem, hlen⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases phase with
        | absorb messageLength => simp at hhead
        | squeeze challengeLength =>
            injection hhead with hLengths
            subst challengeLength
            have hCurrent : 0 < (schedulePhase R cursor (.squeeze len)).2.queryIndex := by
              rcases hStarted with hq | hs
              · exact lt_of_lt_of_le hq (queryIndex_le_schedulePhase R cursor (.squeeze len))
              · cases hquery : cursor.queryIndex with
                | zero =>
                    simpa [schedulePhase] using
                      squeeze_queryIndex_pos_of_zero_full R cursor len hquery hs hlen
                | succ q =>
                    exact lt_of_lt_of_le (by simp [hquery])
                      (queryIndex_le_schedulePhase R cursor (.squeeze len))
            exact lt_of_lt_of_le hCurrent
              (queryIndex_le_schedulePhases R (schedulePhase R cursor (.squeeze len)).2 rest)
      · have hNext : QueryStartedOrSqueezeFull R (schedulePhase R cursor phase).2 :=
          schedulePhase_queryStartedOrSqueezeFull R cursor hStarted phase
        exact ih (schedulePhase R cursor phase).2 hNext ⟨len, htail, hlen⟩

/-- At a nonfull absorb offset, the next source unit is written into the
current prospective query input. -/
lemma absorbWriteLocation_of_ne (R : ℕ) (cursor : ScheduleCursor)
    (h : cursor.absorbOffset ≠ R) :
    absorbWriteLocation R cursor = ⟨cursor.queryIndex, cursor.absorbOffset⟩ := by
  simp [absorbWriteLocation, h]

/-- At a full absorb offset, the next source unit is written into the input
after the just-emitted permutation query. -/
lemma absorbWriteLocation_of_eq (R : ℕ) (cursor : ScheduleCursor)
    (h : cursor.absorbOffset = R) :
    absorbWriteLocation R cursor = ⟨cursor.queryIndex + 1, 0⟩ := by
  simp [absorbWriteLocation, h]

@[simp] lemma firstSqueezeQuery?_zero (R : ℕ) (cursor : ScheduleCursor) :
    firstSqueezeQuery? R cursor 0 = none := by
  simp [firstSqueezeQuery?]

/-- A stateful parser programming point can only come from a nonempty
squeeze.  This is the schedule-side justification for D2SQuery's defensive
zero-length fallback. -/
lemma firstSqueezeQuery?_some_positive (R : ℕ) (cursor : ScheduleCursor)
    {len queryIndex : ℕ}
    (h : firstSqueezeQuery? R cursor len = some queryIndex) : 0 < len := by
  cases len with
  | zero => simp at h
  | succ _ => omega

/-- Cursor offsets which correspond to a concrete lazy duplex state.  The
query index itself is unrestricted; only rate offsets need this invariant. -/
def IsWellFormed (R : ℕ) (cursor : ScheduleCursor) : Prop :=
  cursor.absorbOffset ≤ R ∧ cursor.squeezeOffset ≤ R

/-- One absorb transition preserves valid rate offsets when the rate is
positive. -/
lemma absorbOne_wellFormed (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) :
    IsWellFormed R (absorbOne R cursor) := by
  unfold IsWellFormed at hcursor ⊢
  by_cases hFull : cursor.absorbOffset = R
  · simp [absorbOne, hFull]
    omega
  · simp [absorbOne, hFull]
    omega

/-- One squeeze transition preserves valid rate offsets when the rate is
positive. -/
lemma squeezeOne_wellFormed (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) :
    IsWellFormed R (squeezeOne R cursor) := by
  unfold IsWellFormed at hcursor ⊢
  by_cases hFull : cursor.squeezeOffset = R
  · simp [squeezeOne, hFull]
    omega
  · simp [squeezeOne, hFull]
    omega

/-- A whole absorb replay preserves the concrete cursor invariant. -/
lemma absorb_wellFormed (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) :
    ∀ len : ℕ, IsWellFormed R (absorb R cursor len) := by
  intro len
  induction len generalizing cursor with
  | zero =>
      exact ⟨hcursor.1, le_rfl⟩
  | succ len ih =>
      simpa [absorb] using ih (absorbOne R cursor)
        (absorbOne_wellFormed R hR cursor hcursor)

/-- A whole squeeze replay preserves the concrete cursor invariant. -/
lemma squeeze_wellFormed (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) :
    ∀ len : ℕ, IsWellFormed R (squeeze R cursor len) := by
  intro len
  induction len generalizing cursor with
  | zero => exact hcursor
  | succ len ih =>
      simpa [squeeze] using ih (squeezeOne R cursor)
        (squeezeOne_wellFormed R hR cursor hcursor)

/-- Any absorb, including an empty one, leaves the squeeze cursor at the rate
boundary.  This is the operational reason that a subsequent nonempty verifier
squeeze begins with a permutation query. -/
lemma absorb_squeezeOffset (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) :
    (absorb R cursor len).squeezeOffset = R := by
  induction len generalizing cursor with
  | zero => rfl
  | succ len ih =>
      exact ih (absorbOne R cursor)

/-- After an absorb, a nonempty squeeze is classified at its first emitted
permutation query, whose input index is the current cursor index. -/
lemma firstSqueezeQuery?_after_absorb (R : ℕ) (cursor : ScheduleCursor) (absorbLen len : ℕ)
    (hlen : 0 < len) :
    firstSqueezeQuery? R (absorb R cursor absorbLen) len =
      some (absorb R cursor absorbLen).queryIndex := by
  have hlen0 : len ≠ 0 := Nat.ne_of_gt hlen
  have hs : (absorb R cursor absorbLen).squeezeOffset = R :=
    absorb_squeezeOffset R cursor absorbLen
  simp [firstSqueezeQuery?, hlen0, hs]

/-- A scheduled message has one recorded input-rate location per message unit. -/
lemma scheduleRound_messageLocations_length (R : ℕ) (cursor : ScheduleCursor)
    (shape : RoundShape) :
    (scheduleRound R cursor shape).1.messageLocations.length = shape.messageLength := by
  unfold scheduleRound
  exact absorbWithLocations_length R cursor shape.messageLength

/-- Empty verifier challenges are never parser programming points. -/
lemma scheduleRound_firstSqueezeQuery_empty (R : ℕ) (cursor : ScheduleCursor)
    (messageLength : ℕ) :
    (scheduleRound R cursor ⟨messageLength, 0⟩).1.firstSqueezeQuery = none := by
  change firstSqueezeQuery? R (absorbWithLocations R cursor messageLength).2 0 = none
  exact firstSqueezeQuery?_zero R (absorbWithLocations R cursor messageLength).2

/-- A nonempty verifier challenge is programmed at the cursor immediately
after its message absorb, irrespective of partial rate-block reuse. -/
lemma scheduleRound_firstSqueezeQuery_nonempty (R : ℕ) (cursor : ScheduleCursor)
    (messageLength challengeLength : ℕ) (h : 0 < challengeLength) :
    (scheduleRound R cursor ⟨messageLength, challengeLength⟩).1.firstSqueezeQuery =
      some (absorb R cursor messageLength).queryIndex := by
  change firstSqueezeQuery? R (absorbWithLocations R cursor messageLength).2 challengeLength =
    some (absorb R cursor messageLength).queryIndex
  rw [absorbWithLocations_cursor]
  exact firstSqueezeQuery?_after_absorb R cursor messageLength challengeLength h

/-- An absorb phase records exactly its message-length many source locations. -/
lemma schedulePhase_absorb_sourceLocations_length (R : ℕ) (cursor : ScheduleCursor)
    (messageLength : ℕ) :
    (schedulePhase R cursor (.absorb messageLength)).1.sourceLocations.length = messageLength := by
  unfold schedulePhase
  exact absorbWithLocations_length R cursor messageLength

/-- A squeeze phase never creates an absorb-source location. -/
@[simp] lemma schedulePhase_squeeze_sourceLocations (R : ℕ) (cursor : ScheduleCursor)
    (challengeLength : ℕ) :
    (schedulePhase R cursor (.squeeze challengeLength)).1.sourceLocations = [] := rfl

/-- Empty squeeze phases are never BackTrack programming points. -/
lemma schedulePhase_squeeze_first_empty (R : ℕ) (cursor : ScheduleCursor) :
    (schedulePhase R cursor (.squeeze 0)).1.firstSqueezeQuery = none := by
  exact firstSqueezeQuery?_zero R cursor

/-- A nonempty squeeze phase is marked precisely when it starts at a rate
boundary; this includes the usual phase immediately following an absorb. -/
lemma schedulePhase_squeeze_first (R : ℕ) (cursor : ScheduleCursor)
    (challengeLength : ℕ) :
    (schedulePhase R cursor (.squeeze challengeLength)).1.firstSqueezeQuery =
      firstSqueezeQuery? R cursor challengeLength := rfl

/-- The cursor returned by an absorb phase is exactly its absorb replay. -/
lemma schedulePhase_absorb_cursor (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) :
    (schedulePhase R cursor (.absorb len)).2 = absorb R cursor len := by
  unfold schedulePhase
  exact absorbWithLocations_cursor R cursor len

/-- The cursor returned by a squeeze phase is exactly its squeeze replay. -/
@[simp] lemma schedulePhase_squeeze_cursor (R : ℕ) (cursor : ScheduleCursor) (len : ℕ) :
    (schedulePhase R cursor (.squeeze len)).2 = squeeze R cursor len := rfl

/-- Scheduling does not drop or insert protocol phases. -/
lemma schedulePhases_layouts_length (R : ℕ) (cursor : ScheduleCursor) :
    ∀ phases : List PhaseShape, (schedulePhases R cursor phases).1.length = phases.length := by
  intro phases
  induction phases generalizing cursor with
  | nil => rfl
  | cons phase rest ih =>
      simp only [schedulePhases, List.length_cons]
      exact congrArg Nat.succ (ih (schedulePhase R cursor phase).2)

/-- The salt part of a phase schedule has exactly one recorded coordinate for
each salt unit, even when the first protocol absorb resumes its final block. -/
lemma buildPhaseSchedule_saltLocations_length (R : ℕ) (cursor : ScheduleCursor)
    (saltLength : ℕ) (phases : List PhaseShape) :
    (buildPhaseSchedule R cursor saltLength phases).saltLocations.length = saltLength := by
  unfold buildPhaseSchedule
  exact absorbWithLocations_length R cursor saltLength

/-- A phase schedule has one layout per protocol operation. -/
lemma buildPhaseSchedule_phaseLayouts_length (R : ℕ) (cursor : ScheduleCursor)
    (saltLength : ℕ) (phases : List PhaseShape) :
    (buildPhaseSchedule R cursor saltLength phases).phaseLayouts.length = phases.length := by
  unfold buildPhaseSchedule
  exact schedulePhases_layouts_length R (absorbWithLocations R cursor saltLength).2 phases

/-- One absorb step advances the forward-query counter iff the absorb cursor
was already at the rate boundary. -/
lemma absorbOne_queryIndex (R : ℕ) (cursor : ScheduleCursor) :
    (absorbOne R cursor).queryIndex =
      cursor.queryIndex + if cursor.absorbOffset = R then 1 else 0 := by
  unfold absorbOne
  split <;> simp

/-- One squeeze step advances the forward-query counter iff the squeeze cursor
was already at the rate boundary. -/
lemma squeezeOne_queryIndex (R : ℕ) (cursor : ScheduleCursor) :
    (squeezeOne R cursor).queryIndex =
      cursor.queryIndex + if cursor.squeezeOffset = R then 1 else 0 := by
  unfold squeezeOne
  split <;> simp

/-- The value-free replay cursor agrees with a concrete lazy duplex sponge exactly when its two
rate offsets are the sponge's live absorb/squeeze positions.  The query counter is intentionally
not part of this predicate: the companion exact-count lemmas relate it to the counting-oracle
trace, while this predicate supplies the state-position invariant required to compose phases. -/
def SpongeCursorAgrees {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]
    (sponge : DuplexSponge U C) (cursor : ScheduleCursor) : Prop :=
  sponge.absorbPos.val = cursor.absorbOffset ∧
    sponge.squeezePos.val = cursor.squeezeOffset

/-- The cursor-position invariant for every symbolic support path of one lazy absorb.  Unlike the
counting-oracle version below, this lemma works directly on the live `OracleComp` support, so it
can be composed through `deriveTranscriptDSFSAux`. -/
lemma absorb_support_cursor_agrees_live {U C : Type} [SpongeUnit U] [SpongeSize]
    [SpongeState U C] (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (ls : List U)
    (z : DuplexSponge U C) (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (DuplexSponge.absorb sponge ls)) :
    SpongeCursorAgrees z (absorb SpongeSize.R cursor ls.length) := by
  induction ls generalizing sponge cursor z with
  | nil =>
      rw [DuplexSponge.absorb.eq_def, mem_support_pure_iff] at hz
      subst z
      unfold SpongeCursorAgrees
      constructor
      · exact hcursor.1
      · simp [absorb]
  | cons x xs ih =>
      unfold DuplexSponge.absorb at hz
      by_cases hfull : (sponge.absorbPos : ℕ) = SpongeSize.R
      · rw [if_pos hfull] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [mem_support_bind_iff] at hz
        rcases hz with ⟨permuted, _hquery, htail⟩
        let next : DuplexSponge U C := {
          state := SpongeState.modify permuted (Vector.set · 0 x),
          absorbPos := 1,
          squeezePos := Fin.last SpongeSize.R }
        have hcursor' : SpongeCursorAgrees next (absorbOne SpongeSize.R cursor) := by
          have hfull' : cursor.absorbOffset = SpongeSize.R := hcursor.1.symm.trans hfull
          simp [SpongeCursorAgrees, next, absorbOne, hfull']
        simpa [absorb, next] using
          ih next (absorbOne SpongeSize.R cursor) z hcursor' htail
      · let next : DuplexSponge U C := {
          state := SpongeState.modify sponge.state (Vector.set · (sponge.absorbPos : ℕ) x),
          absorbPos := sponge.absorbPos + 1,
          squeezePos := Fin.last SpongeSize.R }
        rw [if_neg hfull] at hz
        have hcursor' : SpongeCursorAgrees next (absorbOne SpongeSize.R cursor) := by
          have hpos : cursor.absorbOffset ≠ SpongeSize.R := by simpa [hcursor.1] using hfull
          have hlt : sponge.absorbPos.val < SpongeSize.R :=
            lt_of_le_of_ne (Fin.is_le sponge.absorbPos) hfull
          simp [SpongeCursorAgrees, next, absorbOne, hpos,
            Fin.val_add_one_of_lt hlt, hcursor.1]
        simpa [absorb, next] using
          ih next (absorbOne SpongeSize.R cursor) z hcursor' hz

/-- The cursor-position invariant for every symbolic support path of one lazy squeeze.  This is
the live-support counterpart of `squeeze_support_cursor_agrees`, and therefore handles a squeeze
that resumes inside a rate block without assigning it a fictitious fresh block. -/
lemma squeeze_support_cursor_agrees_live {U C : Type} [SpongeUnit U] [SpongeSize]
    [SpongeState U C] (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (len : ℕ)
    (z : Vector U len × DuplexSponge U C) (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (DuplexSponge.squeeze sponge len)) :
    SpongeCursorAgrees z.2 (squeeze SpongeSize.R cursor len) := by
  induction len generalizing sponge cursor with
  | zero =>
      rw [DuplexSponge.squeeze.eq_def, mem_support_pure_iff] at hz
      subst z
      exact hcursor
  | succ n ih =>
      unfold DuplexSponge.squeeze at hz
      by_cases hfull : (sponge.squeezePos : ℕ) = SpongeSize.R
      · rw [if_pos hfull] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [mem_support_bind_iff] at hz
        rcases hz with ⟨permuted, _hquery, htail⟩
        simp at htail
        rcases htail with ⟨a, b, htail, hresult⟩
        let next : DuplexSponge U C := {
          state := permuted, absorbPos := 0, squeezePos := 1 }
        have hcursor' : SpongeCursorAgrees next (squeezeOne SpongeSize.R cursor) := by
          have hfull' : cursor.squeezeOffset = SpongeSize.R := hcursor.2.symm.trans hfull
          simp [SpongeCursorAgrees, next, squeezeOne, hfull']
        have hrec := ih next (squeezeOne SpongeSize.R cursor) (a, b) hcursor' htail
        have hb : b = z.2 := congrArg Prod.snd hresult
        rw [← hb]
        simpa [next, squeeze] using hrec
      · rw [if_neg hfull] at hz
        simp at hz
        rcases hz with ⟨a, b, htail, hresult⟩
        subst z
        let next : DuplexSponge U C := {
          state := sponge.state, absorbPos := 0, squeezePos := sponge.squeezePos + 1 }
        have hcursor' : SpongeCursorAgrees next (squeezeOne SpongeSize.R cursor) := by
          have hpos : cursor.squeezeOffset ≠ SpongeSize.R := by simpa [hcursor.2] using hfull
          have hlt : sponge.squeezePos.val < SpongeSize.R :=
            lt_of_le_of_ne (Fin.is_le sponge.squeezePos) hfull
          simp [SpongeCursorAgrees, next, squeezeOne, hpos,
            Fin.val_add_one_of_lt hlt, hcursor.2]
        simpa [next, squeeze] using
          ih next (squeezeOne SpongeSize.R cursor) (a, b) hcursor' htail

/-- The two standard DSFS lifts preserve the cursor-position invariant of a live squeeze.
`deriveTranscriptDSFSAux` uses exactly this route: forward permutation queries are first embedded
beside the ambient oracle, then beside the duplex hash oracle. -/
lemma lifted_squeeze_support_cursor_agrees_live {ι U StmtIn : Type} {oSpec : OracleSpec ι}
    [SpongeUnit U] [SpongeSize]
    (sponge : CanonicalDuplexSponge U) (cursor : ScheduleCursor) (len : ℕ)
    (z : Vector U len × CanonicalDuplexSponge U) (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (liftM (DuplexSponge.squeeze sponge len) :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) _)) :
    SpongeCursorAgrees z.2 (squeeze SpongeSize.R cursor len) := by
  change z ∈ support
    (OracleComp.liftComp
      (OracleComp.liftComp (DuplexSponge.squeeze sponge len)
        (oSpec + forwardPermutationOracle (CanonicalSpongeState U)))
      (oSpec + duplexSpongeForwardOracle StmtIn U)) at hz
  rw [OracleComp.mem_support_liftComp_iff] at hz
  rw [OracleComp.mem_support_liftComp_iff] at hz
  exact squeeze_support_cursor_agrees_live sponge cursor len z hcursor hz

/-- The absorb counterpart of `lifted_squeeze_support_cursor_agrees_live`.  It is the operational
bridge for salt and prover-message absorbs performed by the live transcript derivation. -/
lemma lifted_absorb_support_cursor_agrees_live {ι U StmtIn : Type} {oSpec : OracleSpec ι}
    [SpongeUnit U] [SpongeSize]
    (sponge : CanonicalDuplexSponge U) (cursor : ScheduleCursor) (ls : List U)
    (z : CanonicalDuplexSponge U) (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (liftM (DuplexSponge.absorb sponge ls) :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) _)) :
    SpongeCursorAgrees z (absorb SpongeSize.R cursor ls.length) := by
  change z ∈ support
    (OracleComp.liftComp
      (OracleComp.liftComp (DuplexSponge.absorb sponge ls)
        (oSpec + forwardPermutationOracle (CanonicalSpongeState U)))
      (oSpec + duplexSpongeForwardOracle StmtIn U)) at hz
  rw [OracleComp.mem_support_liftComp_iff] at hz
  rw [OracleComp.mem_support_liftComp_iff] at hz
  exact absorb_support_cursor_agrees_live sponge cursor ls z hcursor hz

/-- One concrete lazy absorb path and the value-free absorb cursor finish at identical rate
positions.  This is value-independent: permutation answers can change the sponge state but never
its two rate cursors. -/
lemma absorb_support_cursor_agrees {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]
    [DecidableEq C]
    (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (ls : List U)
    (z : DuplexSponge U C × OracleSpec.QueryCount C)
    (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (countingOracle.simulate (DuplexSponge.absorb sponge ls) 0)) :
    SpongeCursorAgrees z.1 (absorb SpongeSize.R cursor ls.length) := by
  induction ls generalizing sponge cursor z with
  | nil =>
      rw [DuplexSponge.absorb.eq_def, countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      unfold SpongeCursorAgrees
      constructor
      · exact hcursor.1
      · simp [absorb]
  | cons x xs ih =>
      unfold DuplexSponge.absorb at hz
      by_cases hfull : (sponge.absorbPos : ℕ) = SpongeSize.R
      · rw [if_pos hfull] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
        rcases hz with ⟨_, permuted, htail⟩
        let next : DuplexSponge U C := {
          state := SpongeState.modify permuted (Vector.set · 0 x),
          absorbPos := 1
          squeezePos := Fin.last SpongeSize.R }
        have hcursor' : SpongeCursorAgrees next (absorbOne SpongeSize.R cursor) := by
          have hfull' : cursor.absorbOffset = SpongeSize.R := hcursor.1.symm.trans hfull
          simp [SpongeCursorAgrees, next, absorbOne, hfull']
        simpa [absorb, next] using ih next (absorbOne SpongeSize.R cursor)
          (z.1, Function.update z.2 sponge.state (z.2 sponge.state - 1)) hcursor' htail
      · let next : DuplexSponge U C := {
          state := SpongeState.modify sponge.state (Vector.set · (sponge.absorbPos : ℕ) x),
          absorbPos := sponge.absorbPos + 1
          squeezePos := Fin.last SpongeSize.R }
        rw [if_neg hfull] at hz
        have hcursor' : SpongeCursorAgrees next (absorbOne SpongeSize.R cursor) := by
          have hpos : cursor.absorbOffset ≠ SpongeSize.R := by simpa [hcursor.1] using hfull
          have hlt : sponge.absorbPos.val < SpongeSize.R :=
            lt_of_le_of_ne (Fin.is_le sponge.absorbPos) hfull
          simp [SpongeCursorAgrees, next, absorbOne, hpos,
            Fin.val_add_one_of_lt hlt, hcursor.1]
        simpa [absorb, next] using ih next (absorbOne SpongeSize.R cursor) z hcursor' hz

/-- One concrete lazy squeeze path and the value-free squeeze cursor finish at identical rate
positions.  As for absorb, this is independent of the sampled permutation answers. -/
lemma squeeze_support_cursor_agrees {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]
    [DecidableEq C]
    (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (len : ℕ)
    (z : (Vector U len × DuplexSponge U C) × OracleSpec.QueryCount C)
    (hcursor : SpongeCursorAgrees sponge cursor)
    (hz : z ∈ support (countingOracle.simulate (DuplexSponge.squeeze sponge len) 0)) :
    SpongeCursorAgrees z.1.2 (squeeze SpongeSize.R cursor len) := by
  induction len generalizing sponge cursor with
  | zero =>
      rw [DuplexSponge.squeeze.eq_def, countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      exact hcursor
  | succ n ih =>
      unfold DuplexSponge.squeeze at hz
      by_cases hfull : (sponge.squeezePos : ℕ) = SpongeSize.R
      · rw [if_pos hfull] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
        rcases hz with ⟨_, permuted, htail⟩
        simp [countingOracle.simulate] at htail
        rcases htail with ⟨a, b, htail, hresult⟩
        let next : DuplexSponge U C :=
          { state := permuted, absorbPos := 0, squeezePos := 1 }
        have hcursor' : SpongeCursorAgrees next (squeezeOne SpongeSize.R cursor) := by
          have hfull' : cursor.squeezeOffset = SpongeSize.R := hcursor.2.symm.trans hfull
          simp [SpongeCursorAgrees, next, squeezeOne, hfull']
        have htail' : ((a, b), Function.update z.2 sponge.state (z.2 sponge.state - 1)) ∈
            support (countingOracle.simulate (DuplexSponge.squeeze next n) 0) := by
          simpa [next, countingOracle.simulate] using htail
        have hrec := ih next (squeezeOne SpongeSize.R cursor)
          ((a, b), Function.update z.2 sponge.state (z.2 sponge.state - 1)) hcursor' htail'
        have hb : b = z.1.2 := congrArg Prod.snd hresult
        rw [← hb]
        simpa [next, squeeze] using hrec
      · rw [if_neg hfull] at hz
        simp [countingOracle.simulate] at hz
        rcases hz with ⟨a, b, qc, htail, hresult⟩
        subst z
        let next : DuplexSponge U C :=
          { state := sponge.state, absorbPos := 0, squeezePos := sponge.squeezePos + 1 }
        have hcursor' : SpongeCursorAgrees next (squeezeOne SpongeSize.R cursor) := by
          have hpos : cursor.squeezeOffset ≠ SpongeSize.R := by simpa [hcursor.2] using hfull
          have hlt : sponge.squeezePos.val < SpongeSize.R :=
            lt_of_le_of_ne (Fin.is_le sponge.squeezePos) hfull
          simp [SpongeCursorAgrees, next, squeezeOne, hpos,
            Fin.val_add_one_of_lt hlt, hcursor.2]
        have htail' : ((a, b), qc) ∈
            support (countingOracle.simulate (DuplexSponge.squeeze next n) 0) := by
          simpa [next, countingOracle.simulate] using htail
        simpa [next, squeeze] using
          ih next (squeezeOne SpongeSize.R cursor) ((a, b), qc) hcursor' htail'

/-- The stateful absorb schedule emits exactly the same number of queries as
the concrete lazy `DuplexSponge.absorb` recursion. -/
lemma absorb_queryIndex (R : ℕ) (cursor : ScheduleCursor) :
    ∀ len : ℕ,
      (absorb R cursor len).queryIndex = cursor.queryIndex +
        spongeOpCount R cursor.absorbOffset len := by
  intro len
  induction len generalizing cursor with
  | zero => simp [absorb, spongeOpCount]
  | succ len ih =>
      rw [absorb, ih, spongeOpCount_succ, absorbOne_queryIndex]
      by_cases hFull : cursor.absorbOffset = R
      · simp [hFull, absorbOne]
        omega
      · simp [hFull, absorbOne]

/-- The stateful squeeze schedule emits exactly the same number of queries as
the concrete lazy `DuplexSponge.squeeze` recursion. -/
lemma squeeze_queryIndex (R : ℕ) (cursor : ScheduleCursor) :
    ∀ len : ℕ,
      (squeeze R cursor len).queryIndex = cursor.queryIndex +
        spongeOpCount R cursor.squeezeOffset len := by
  intro len
  induction len generalizing cursor with
  | zero => simp [squeeze, spongeOpCount]
  | succ len ih =>
      rw [squeeze, ih, spongeOpCount_succ, squeezeOne_queryIndex]
      by_cases hFull : cursor.squeezeOffset = R
      · simp [hFull, squeezeOne]
        omega
      · simp [hFull, squeezeOne]

/-- The ordinary query-bound proof for an absorb phase has the exact stateful cost selected by
the replay cursor.  This is the bridge used when composing the live transcript derivation: it
does not replace that cost by a per-message ceiling. -/
lemma absorb_isQueryBoundP_cursor {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]
    (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (ls : List U)
    (hcursor : SpongeCursorAgrees sponge cursor) :
    IsQueryBoundP (DuplexSponge.absorb sponge ls) (fun _ => True)
      ((absorb SpongeSize.R cursor ls.length).queryIndex - cursor.queryIndex) := by
  rw [absorb_queryIndex]
  simpa [hcursor.1] using (absorb_isQueryBoundP ls sponge)

/-- The ordinary query-bound proof for a squeeze phase likewise has the exact stateful replay
cost.  In particular, this cost is zero precisely when the concrete squeeze crosses no exhausted
rate boundary; no fictitious full rate block is charged. -/
lemma squeeze_isQueryBoundP_cursor {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]
    (sponge : DuplexSponge U C) (cursor : ScheduleCursor) (len : ℕ)
    (hcursor : SpongeCursorAgrees sponge cursor) :
    IsQueryBoundP (DuplexSponge.squeeze sponge len) (fun _ => True)
      ((squeeze SpongeSize.R cursor len).queryIndex - cursor.queryIndex) := by
  rw [squeeze_queryIndex]
  simpa [hcursor.2] using (squeeze_isQueryBoundP len sponge)

/-- An absorb phase uses no more forward permutation queries than the ceiling
number of rate blocks of its input, even when it resumes a partial block. -/
lemma absorb_queryIndex_le (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) (len : ℕ) :
    (absorb R cursor len).queryIndex ≤
      cursor.queryIndex + (len + R - 1) / R := by
  rw [absorb_queryIndex]
  exact Nat.add_le_add_left (spongeOpCount_le R hR cursor.absorbOffset len hcursor.1) _

/-- A squeeze phase uses no more forward permutation queries than the ceiling
number of rate blocks of its requested output, independently of the current
squeeze offset. -/
lemma squeeze_queryIndex_le (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) (len : ℕ) :
    (squeeze R cursor len).queryIndex ≤
      cursor.queryIndex + (len + R - 1) / R := by
  rw [squeeze_queryIndex]
  exact Nat.add_le_add_left (spongeOpCount_le R hR cursor.squeezeOffset len hcursor.2) _

/-- One scheduled operation preserves a valid cursor. -/
lemma schedulePhase_wellFormed (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) (phase : PhaseShape) :
    IsWellFormed R (schedulePhase R cursor phase).2 := by
  cases phase with
  | absorb len =>
      change IsWellFormed R (absorbWithLocations R cursor len).2
      rw [absorbWithLocations_cursor]
      exact absorb_wellFormed R hR cursor hcursor len
  | squeeze len =>
      simpa [schedulePhase] using squeeze_wellFormed R hR cursor hcursor len

/-- One scheduled operation advances the query index by at most its
ceiling-style phase bound. -/
lemma schedulePhase_queryIndex_le (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) (phase : PhaseShape) :
    (schedulePhase R cursor phase).2.queryIndex ≤
      cursor.queryIndex + phaseQueryBound R phase := by
  cases phase with
  | absorb len =>
      change (absorbWithLocations R cursor len).2.queryIndex ≤
        cursor.queryIndex + (len + R - 1) / R
      rw [absorbWithLocations_cursor]
      exact absorb_queryIndex_le R hR cursor hcursor len
  | squeeze len =>
      simpa [schedulePhase, phaseQueryBound] using
        squeeze_queryIndex_le R hR cursor hcursor len

/-- The full stateful schedule emits no more permutation queries than the sum
of the ceiling bounds of its actual protocol phases.  This is the local
replacement for every old use of an exact scalar block offset. -/
lemma schedulePhases_queryIndex_le (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) :
    ∀ phases : List PhaseShape,
      (schedulePhases R cursor phases).2.queryIndex ≤
        cursor.queryIndex + phaseQueryBudget R phases := by
  intro phases
  induction phases generalizing cursor with
  | nil => simp [schedulePhases, phaseQueryBudget]
  | cons phase rest ih =>
      have hCurrentWellFormed : IsWellFormed R (schedulePhase R cursor phase).2 :=
        schedulePhase_wellFormed R hR cursor hcursor phase
      have hCurrentBound : (schedulePhase R cursor phase).2.queryIndex ≤
          cursor.queryIndex + phaseQueryBound R phase :=
        schedulePhase_queryIndex_le R hR cursor hcursor phase
      have hTail := ih (schedulePhase R cursor phase).2 hCurrentWellFormed
      change (schedulePhases R (schedulePhase R cursor phase).2 rest).2.queryIndex ≤
        cursor.queryIndex + phaseQueryBudget R (phase :: rest)
      calc
        (schedulePhases R (schedulePhase R cursor phase).2 rest).2.queryIndex ≤
            (schedulePhase R cursor phase).2.queryIndex + phaseQueryBudget R rest := hTail
        _ ≤ cursor.queryIndex + phaseQueryBound R phase + phaseQueryBudget R rest := by omega
        _ = cursor.queryIndex + phaseQueryBudget R (phase :: rest) := by
          simp [phaseQueryBudget, Nat.add_assoc]

/-- Global layout bound: salt absorption plus every actual protocol phase uses
at most the sum of their ceiling bounds.  This is the precise form of
`N_DS ≤ L_delta + L_P + L_V`; it deliberately makes no exact-count claim. -/
lemma buildPhaseSchedule_queryIndex_le (R : ℕ) (hR : 0 < R) (cursor : ScheduleCursor)
    (hcursor : IsWellFormed R cursor) (saltLength : ℕ) (phases : List PhaseShape) :
    (buildPhaseSchedule R cursor saltLength phases).finalCursor.queryIndex ≤
      cursor.queryIndex + (saltLength + R - 1) / R + phaseQueryBudget R phases := by
  change (schedulePhases R (absorbWithLocations R cursor saltLength).2 phases).2.queryIndex ≤
    cursor.queryIndex + (saltLength + R - 1) / R + phaseQueryBudget R phases
  rw [absorbWithLocations_cursor]
  have hSaltWellFormed : IsWellFormed R (absorb R cursor saltLength) :=
    absorb_wellFormed R hR cursor hcursor saltLength
  have hSaltBound : (absorb R cursor saltLength).queryIndex ≤
      cursor.queryIndex + (saltLength + R - 1) / R :=
    absorb_queryIndex_le R hR cursor hcursor saltLength
  have hPhases := schedulePhases_queryIndex_le R hR (absorb R cursor saltLength)
    hSaltWellFormed phases
  calc
    (schedulePhases R (absorb R cursor saltLength) phases).2.queryIndex ≤
        (absorb R cursor saltLength).queryIndex + phaseQueryBudget R phases := hPhases
    _ ≤ cursor.queryIndex + (saltLength + R - 1) / R + phaseQueryBudget R phases := by omega

/-- The first nonempty squeeze after an absorb emits its first permutation
immediately.  The remaining `len - 1` reads follow the standard lazy squeeze
schedule. -/
lemma squeeze_queryIndex_after_absorb (R : ℕ) (cursor : ScheduleCursor)
    (absorbLen len : ℕ) (hlen : 0 < len) :
    (squeeze R (absorb R cursor absorbLen) len).queryIndex =
      (absorb R cursor absorbLen).queryIndex + 1 + spongeOpCount R 1 (len - 1) := by
  rw [squeeze_queryIndex, absorb_squeezeOffset]
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  simp [spongeOpCount_succ]
  omega

end ScheduleCursor

end DuplexSpongeFS.Backtrack

namespace DuplexSpongeFS
namespace Backtrack
namespace ScheduleCursor

section NVCount

/-- Exact stateful permutation-call count for an arbitrary phase list: replay the salt
absorb of `saltLength` units then `phases` from the paper's starting cursor
`(q,a,s)=(0,0,r)`, and read off the final `queryIndex`.  CO25 eq. (4b) `q_final`. -/
def scheduleQueryCount (R : ℕ) (saltLength : ℕ) (phases : List PhaseShape) : ℕ :=
  (buildPhaseSchedule R ⟨0, 0, R⟩ saltLength phases).finalCursor.queryIndex

@[simp]
lemma scheduleQueryCount_eq_finalQueryIndex (R : ℕ) (saltLength : ℕ)
    (phases : List PhaseShape) :
    scheduleQueryCount R saltLength phases =
      (buildPhaseSchedule R ⟨0, 0, R⟩ saltLength phases).finalCursor.queryIndex := rfl

/-- The exact stateful call count is bounded by the usual sum of per-phase ceilings.

This is only a compatibility inequality: partial-block reuse can make the left-hand side strictly
smaller.  In particular, later Section 5 bounds continue to use `scheduleQueryCount` (and hence
`N_𝒱`) exactly; this lemma is available only when a legacy ceiling-valued wrapper is needed. -/
lemma scheduleQueryCount_le_phaseQueryBudget (R : ℕ) (hR : 0 < R) (saltLength : ℕ)
    (phases : List PhaseShape) :
    scheduleQueryCount R saltLength phases ≤
      (saltLength + R - 1) / R + phaseQueryBudget R phases := by
  have hInitial : IsWellFormed R ⟨0, 0, R⟩ := by
    exact ⟨Nat.zero_le R, le_rfl⟩
  simpa [scheduleQueryCount_eq_finalQueryIndex] using
    buildPhaseSchedule_queryIndex_le R hR ⟨0, 0, R⟩ hInitial saltLength phases

/-- An empty replay costs no permutation calls. -/
@[simp]
lemma scheduleQueryCount_eq_zero (R : ℕ) :
    scheduleQueryCount R 0 [] = 0 := by
  simp [scheduleQueryCount_eq_finalQueryIndex, buildPhaseSchedule, schedulePhases,
    absorb, absorbWithLocations]

/-- A zero-length squeeze is a no-op: `S(0)` makes no query and leaves the cursor, hence
the count, unchanged. -/
@[simp]
lemma scheduleQueryCount_squeeze_zero (R : ℕ) (saltLength : ℕ) :
    scheduleQueryCount R saltLength [PhaseShape.squeeze 0] =
      scheduleQueryCount R saltLength [] := by
  simp [scheduleQueryCount_eq_finalQueryIndex, buildPhaseSchedule, schedulePhases,
    schedulePhase, squeeze, firstSqueezeQuery?]

end NVCount

end ScheduleCursor
end Backtrack

section VerifierPermCallCount
open Backtrack ScheduleCursor

variable {n : ℕ} (pSpec : ProtocolSpec n)

/-- Round `i` of the protocol as a sponge phase: absorb for a prover-message round, squeeze
for a verifier-challenge round.  One entry of `Act_𝒱` (eq. 4a) per round, the leading salt
phase being the separate salt absorb in `buildPhaseSchedule`. -/
noncomputable def phaseOf [ProtocolSpec.HasMessageSize pSpec] [ProtocolSpec.HasChallengeSize pSpec]
    (i : Fin n) : PhaseShape :=
  match h : pSpec.dir i with
  | .P_to_V => PhaseShape.absorb (ProtocolSpec.messageSize ⟨i, h⟩)
  | .V_to_P => PhaseShape.squeeze (ProtocolSpec.challengeSize ⟨i, h⟩)

/-- The protocol phase list in round order (`Act_𝒱` minus the leading `A(δ)` salt). -/
noncomputable def protocolPhases [ProtocolSpec.HasMessageSize pSpec] [ProtocolSpec.HasChallengeSize pSpec] :
    List PhaseShape :=
  List.ofFn (phaseOf pSpec)

/-- Exact number of forward permutation calls the stateful verifier executes over
`Act_𝒱 = [Start, A(δ), A(ℓ_P(1)), S(ℓ_V(1)), …]`: the final `queryIndex` of the
`buildPhaseSchedule` replay from the paper's start cursor `(q,a,s)=(0,0,r)`.
CO25 eq. (4b) `N_𝒱 := q_final`. -/
noncomputable def verifierPermCallCount [ProtocolSpec.HasMessageSize pSpec] [ProtocolSpec.HasChallengeSize pSpec]
    [sz : SpongeSize] (δ : ℕ) : ℕ :=
  scheduleQueryCount sz.R δ (protocolPhases pSpec)

/-- Exposed final `queryIndex` of the exact replay. -/
@[simp]
lemma verifierPermCallCount_eq_finalQueryIndex [ProtocolSpec.HasMessageSize pSpec] [ProtocolSpec.HasChallengeSize pSpec]
    [sz : SpongeSize] (δ : ℕ) :
    verifierPermCallCount (pSpec := pSpec) (δ := δ) =
      (buildPhaseSchedule sz.R ⟨0, 0, sz.R⟩ δ (protocolPhases pSpec)).finalCursor.queryIndex :=
  rfl


end VerifierPermCallCount

/-!
## Operational cursor correspondence

The query-count schedule above is value-free.  These declarations connect it
to the actual DSFS transcript derivation: every supported execution has the
absorb/squeeze cursor prescribed by the same prefix of protocol actions.  This
is the first executable bridge needed to use the exact count `N_𝒱` as proof
fuel, rather than reverting to a rounded block budget.
-/

section TranscriptCursor

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- The schedule cursor after the first `k` protocol actions in the live DSFS
transcript derivation.  The dependent direction match deliberately follows
`deriveTranscriptDSFSAux` verbatim. -/
noncomputable def deriveTranscriptCursor [pSpec.HasMessageSize] [pSpec.HasChallengeSize]
    (R : ℕ) (initial : Backtrack.ScheduleCursor) (k : Fin (n + 1)) :
    Backtrack.ScheduleCursor :=
  Fin.induction initial
    (fun i current =>
      match h : pSpec.dir i with
      | .V_to_P =>
          Backtrack.ScheduleCursor.squeeze R current (challengeSize ⟨i, h⟩)
      | .P_to_V =>
          Backtrack.ScheduleCursor.absorb R current (messageSize ⟨i, h⟩))
    k

lemma deriveTranscriptCursor_succ_v [pSpec.HasMessageSize] [pSpec.HasChallengeSize]
    (R : ℕ) (initial : Backtrack.ScheduleCursor) (i : Fin n)
    (hdir : pSpec.dir i = .V_to_P) :
    deriveTranscriptCursor (pSpec := pSpec) R initial i.succ =
      Backtrack.ScheduleCursor.squeeze R
        (deriveTranscriptCursor (pSpec := pSpec) R initial i.castSucc)
        (challengeSize ⟨i, hdir⟩) := by
  rw [deriveTranscriptCursor, Fin.induction_succ]
  split
  · congr 1
  · rename_i h
    have hfalse : Direction.P_to_V = Direction.V_to_P := h.symm.trans hdir
    cases hfalse

lemma deriveTranscriptCursor_succ_p [pSpec.HasMessageSize] [pSpec.HasChallengeSize]
    (R : ℕ) (initial : Backtrack.ScheduleCursor) (i : Fin n)
    (hdir : pSpec.dir i = .P_to_V) :
    deriveTranscriptCursor (pSpec := pSpec) R initial i.succ =
      Backtrack.ScheduleCursor.absorb R
        (deriveTranscriptCursor (pSpec := pSpec) R initial i.castSucc)
        (messageSize ⟨i, hdir⟩) := by
  rw [deriveTranscriptCursor, Fin.induction_succ]
  split
  · rename_i h
    have hfalse : Direction.V_to_P = Direction.P_to_V := h.symm.trans hdir
    cases hfalse
  · congr 1

/-- Every transcript prefix preserves the already-emitted permutation-call
count.  This supplies the subtraction side condition for exact per-phase query
costs in the live verifier proof. -/
lemma deriveTranscriptCursor_queryIndex_le [pSpec.HasMessageSize] [pSpec.HasChallengeSize]
    (R : ℕ) (initial : Backtrack.ScheduleCursor) (k : Fin (n + 1)) :
    initial.queryIndex ≤
      (deriveTranscriptCursor (pSpec := pSpec) R initial k).queryIndex := by
  induction k using Fin.induction with
  | zero => simp [deriveTranscriptCursor]
  | succ i ih =>
      rw [deriveTranscriptCursor, Fin.induction_succ]
      split
      · exact Nat.le_trans ih
          (Backtrack.ScheduleCursor.queryIndex_le_squeeze R
            (deriveTranscriptCursor (pSpec := pSpec) R initial i.castSucc) _)
      · exact Nat.le_trans ih
          (Backtrack.ScheduleCursor.queryIndex_le_absorb R
            (deriveTranscriptCursor (pSpec := pSpec) R initial i.castSucc) _)

/-- Every support point of the actual DSFS transcript derivation has the
stateful cursor obtained by replaying the same protocol-action prefix. -/
theorem deriveTranscriptDSFSAux_support_cursor_agrees_live
    {ι U StmtIn : Type} {oSpec : OracleSpec ι} [SpongeUnit U] [SpongeSize] [pSpec.CodecCore U]
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages)
    (initial : Backtrack.ScheduleCursor)
    (hinitial : Backtrack.ScheduleCursor.SpongeCursorAgrees sponge initial) :
    ∀ (k : Fin (n + 1)) (z : CanonicalDuplexSponge U × pSpec.Transcript k),
      z ∈ support (ProtocolSpec.Messages.deriveTranscriptDSFSAux
        (pSpec := pSpec) (oSpec := oSpec) (StmtIn := StmtIn) sponge messages k) →
      Backtrack.ScheduleCursor.SpongeCursorAgrees z.1
        (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial k) := by
  intro k
  induction k using Fin.induction with
  | zero =>
      intro z hz
      simp [ProtocolSpec.Messages.deriveTranscriptDSFSAux] at hz
      subst z
      simpa [deriveTranscriptCursor] using hinitial
  | succ i ih =>
      rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux] at ih
      intro z hz
      rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux, Fin.induction_succ] at hz
      rw [mem_support_bind_iff] at hz
      rcases hz with ⟨⟨curSponge, prevTranscript⟩, hx, hrest⟩
      have hprev : Backtrack.ScheduleCursor.SpongeCursorAgrees curSponge
          (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R initial i.castSucc) := by
        simpa using ih ⟨curSponge, prevTranscript⟩ hx
      simp at hrest
      split at hrest
      · rename_i hdir
        rw [support_map] at hrest
        rcases hrest with ⟨pair, hp, hpair⟩
        subst z
        rw [deriveTranscriptCursor_succ_v (initial := initial) (i := i) _ hdir]
        simpa using
          (Backtrack.ScheduleCursor.lifted_squeeze_support_cursor_agrees_live
            curSponge _ _ _ hprev hp)
      · rename_i hdir
        rw [support_map] at hrest
        rcases hrest with ⟨newSponge, hp, hnewSponge⟩
        subst z
        rw [deriveTranscriptCursor_succ_p (initial := initial) (i := i) _ hdir]
        simpa using
          (Backtrack.ScheduleCursor.lifted_absorb_support_cursor_agrees_live
            curSponge _ _ _ hprev hp)

private lemma fin_induction_castSucc_eq
    {α : Type} {n : ℕ} (initial : α) (step : (i : Fin (n + 1)) → α → α)
    (k : Fin (n + 1)) :
    @Fin.induction (n + 1) (fun _ => α) initial step k.castSucc =
      @Fin.induction n (fun _ => α) initial
        (fun i current => step i.castSucc current) k := by
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have hcast : i.succ.castSucc = (i.castSucc).succ := by rfl
      rw [hcast, Fin.induction_succ, Fin.induction_succ]
      exact congrArg (step i.castSucc) ih

private theorem fin_induction_last_eq_list_foldl
    {α : Type} (n : ℕ) (initial : α) (step : (i : Fin n) → α → α) :
    Fin.induction initial step (Fin.last n) =
      (List.ofFn fun i : Fin n => step i).foldl (fun current action => action current) initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hlast : Fin.last (n + 1) = (Fin.last n).succ := by rfl
      rw [hlast, Fin.induction_succ, fin_induction_castSucc_eq, ih]

/-- At the final transcript index, the operational cursor is exactly the
value-free schedule cursor after all protocol phases. -/
theorem deriveTranscriptCursor_last_eq_schedulePhases
    [pSpec.HasMessageSize] [pSpec.HasChallengeSize]
    (R : ℕ) (initial : Backtrack.ScheduleCursor) :
    deriveTranscriptCursor (pSpec := pSpec) R initial (Fin.last n) =
      (Backtrack.ScheduleCursor.schedulePhases R initial (protocolPhases pSpec)).2 := by
  rw [deriveTranscriptCursor, fin_induction_last_eq_list_foldl]
  rw [Backtrack.ScheduleCursor.schedulePhases_final_eq_foldl]
  unfold protocolPhases
  have hactions :
      List.ofFn (fun i current =>
        match h : pSpec.dir i with
        | .V_to_P => Backtrack.ScheduleCursor.squeeze R current (challengeSize ⟨i, h⟩)
        | .P_to_V => Backtrack.ScheduleCursor.absorb R current (messageSize ⟨i, h⟩)) =
        List.map (fun phase : Backtrack.ScheduleCursor.PhaseShape =>
          fun current => (Backtrack.ScheduleCursor.schedulePhase R current phase).2)
          (List.ofFn (phaseOf pSpec)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    funext cursor
    unfold phaseOf
    simp only [Function.comp_apply]
    split
    · rename_i hV
      split
      · rename_i hP
        have hfalse : Direction.V_to_P = Direction.P_to_V := hV.symm.trans hP
        cases hfalse
      · simp [Backtrack.ScheduleCursor.schedulePhase]
    · rename_i hP
      split
      · simp only [Backtrack.ScheduleCursor.schedulePhase]
        rw [Backtrack.ScheduleCursor.absorbWithLocations_cursor]
      · rename_i hV
        have hfalse : Direction.P_to_V = Direction.V_to_P := hP.symm.trans hV
        cases hfalse
  rw [hactions, List.foldl_map]

/-- The final cursor of the live transcript schedule has exactly the public
stateful verifier count `N_𝒱`.  The salt can end inside a rate block; its
effect is therefore replayed before, rather than rounded into, this count. -/
theorem deriveTranscriptCursor_last_queryIndex_eq_verifierPermCallCount
    [pSpec.HasMessageSize] [pSpec.HasChallengeSize] [SpongeSize]
    (δ : ℕ) :
    (deriveTranscriptCursor (pSpec := pSpec) SpongeSize.R
      (Backtrack.ScheduleCursor.absorb SpongeSize.R ⟨0, 0, SpongeSize.R⟩ δ)
      (Fin.last n)).queryIndex =
      verifierPermCallCount (pSpec := pSpec) (δ := δ) := by
  rw [deriveTranscriptCursor_last_eq_schedulePhases]
  rw [verifierPermCallCount_eq_finalQueryIndex]
  simp only [Backtrack.ScheduleCursor.buildPhaseSchedule]
  rw [Backtrack.ScheduleCursor.absorbWithLocations_cursor]

end TranscriptCursor

end DuplexSpongeFS
