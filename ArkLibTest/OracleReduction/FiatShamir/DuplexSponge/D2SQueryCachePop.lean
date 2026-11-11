/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# `D2SQuery` keeps `Cache_p` answers in `tr_∇.p`

Regression test for CO25 §5.4 Item 4(c)i. An honest prover and the honest verifier run the
same duplex-sponge derivation under one shared `D2SQuery` state, as in the §5.8 hybrids. With
`L_V(1) ≥ 2`, the second squeeze query of the prover is answered from `Cache_p`. The verifier
replays that query, so the popped pair must be in `tr_∇.p`: otherwise the replay is resampled,
the two parties derive different challenges and the bad event `E` holds on an honest trace.

The checks run one round (`k = 1`) so that they do not depend on how `BackTrack` recognises
later rounds.
-/

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS DuplexSpongeFS.ProverTransform
open DuplexSpongeFS.DSTraceStorage

namespace ArkLibTest.D2SQueryCachePop

/-- Direction of the one-round schedule `P → V`, `V → P`. -/
def pSDir : Fin 2 → Direction
  | ⟨0, _⟩ => .P_to_V
  | _ => .V_to_P

/-- Message type `Unit`, challenge type `Σ^{ℓ_V}`. -/
def pSType (lV : ℕ) : Fin 2 → Type
  | ⟨0, _⟩ => Unit
  | _ => Vector UInt8 lV

/-- The one-round protocol specification. -/
def pS (lV : ℕ) : ProtocolSpec 2 := ⟨pSDir, pSType lV⟩

instance (lV : ℕ) : ∀ i, Fintype ((pS lV).Message i)
  | ⟨⟨0, _⟩, _⟩ => inferInstanceAs (Fintype Unit)
  | ⟨⟨1, _⟩, h⟩ => by simp [pS, pSDir] at h

instance (lV : ℕ) : ∀ i, DecidableEq ((pS lV).Message i)
  | ⟨⟨0, _⟩, _⟩ => inferInstanceAs (DecidableEq Unit)
  | ⟨⟨1, _⟩, h⟩ => by simp [pS, pSDir] at h

/-- Codec: the message encodes as `0^{ℓ_P}`, the challenge decodes as the identity. -/
@[reducible] def codecPS (lP lV : ℕ) : Codec (pS lV) UInt8 where
  messageSize := fun _ => lP
  challengeSize := fun _ => lV
  encode := fun _ _ => Vector.replicate lP 0
  encode_injective
    | ⟨⟨0, _⟩, _⟩ => fun a b _ => Subsingleton.elim (α := Unit) a b
    | ⟨⟨1, _⟩, h⟩ => by simp [pS, pSDir] at h
  decode
    | ⟨⟨0, _⟩, h⟩, _ => by simp [pS, pSDir] at h
    | ⟨⟨1, _⟩, _⟩, v => v
  decodingBias := fun _ => 1
  decode_isBiased := fun _ _ _ _ _ => PMF.tvDist_le_one _ _
  decode_surjective
    | ⟨⟨0, _⟩, h⟩ => by simp [pS, pSDir] at h
    | ⟨⟨1, _⟩, _⟩ => fun v => ⟨v, rfl⟩

/-- The (unique) prover message. -/
def msgs (lV : ℕ) : (pS lV).Messages
  | ⟨⟨0, _⟩, _⟩ => ()
  | ⟨⟨1, _⟩, h⟩ => by simp [pS, pSDir] at h

/-- Deterministic sampler: a counter for `𝒰(Σ)` draws (starting at 10) and a `g`-call count. -/
abbrev M := OptionT (StateM (ℕ × ℕ))

/-- Observable outcome of one prover-then-verifier run. -/
structure Outcome where
  proverChallenge : List UInt8
  verifierChallenge : List UInt8
  /-- `(kind, input, output)` for each entry of the simulator trace `tr`. -/
  trace : List (String × List UInt8 × List UInt8)
  gCalls : ℕ
  /-- No two forward entries share an input but differ in output. -/
  pFunctional : Bool
  /-- The live `tr_∇.p` and StdTrace's `tr_∇.p` (built from the whole trace) hold the same pairs. -/
  onlineIndexIsOffline : Bool
  deriving Repr

section Harness

variable [SpongeSize]

/-- Run the honest sponge derivation twice (prover, then verifier) under one `D2SQuery` state.
`g` answers every key with `(1, 2, …, ℓ_V)`, a frozen sample of a random function. -/
def run (lP lV δ : ℕ) : Option Outcome :=
  letI := codecPS lP lV
  let St := CanonicalSpongeState UInt8
  let TH := ListBacked.ListTraceTable Unit (Vector UInt8 SpongeSize.C)
  let TP := ListBacked.ListTraceTable St St
  let gImpl : QueryImpl (gSpec (U := UInt8) Unit (pS lV) δ) M := fun _ => do
    modify fun (c, g) => (c, g + 1)
    pure (Vector.ofFn fun j => (j.val + 1).toUInt8)
  let auxImpl : QueryImpl ((Unit →ₒ UInt8) + unifSpec) M := fun
    | .inl () => do
        let (c, g) ← get
        set (c + 1, g)
        pure (10 + c).toUInt8
    | .inr n => pure (0 : Fin (n + 1))
  let simImpl : QueryImpl ([]ₒ + duplexSpongeChallengeOracle Unit UInt8)
      (StateT (D2SQueryState (δ := δ) (T_H := TH) (T_P := TP) (StmtIn := Unit)
        (pSpec := pS lV) (U := UInt8)) M) := fun
    | .inl q => PEmpty.elim q
    | .inr q => d2sQueryImpl (δ := δ) (T_H := TH) (T_P := TP) (StmtIn := Unit) (pSpec := pS lV)
        (U := UInt8) gImpl auxImpl q
  let honestRun : OracleComp ([]ₒ + duplexSpongeChallengeOracle Unit UInt8) (List UInt8) := do
    let ⟨_, tr⟩ ← liftComp
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := []ₒ) (pSpec := pS lV)
        (U := UInt8) (δ := δ) () (Vector.replicate δ 0) (msgs lV))
      ([]ₒ + duplexSpongeChallengeOracle Unit UInt8)
    pure (Vector.toList (n := lV) (tr ⟨1, by decide⟩))
  let comp := do
    let cP ← simulateQ simImpl honestRun
    let cV ← simulateQ simImpl honestRun
    pure (cP, cV)
  match ((comp.run default).run.run (0, 0)) with
  | (some ((cP, cV), st), (_, g)) =>
      let fwd : List (St × St) := st.trace.filterMap fun
        | ⟨.inr (.inl a), b⟩ => some (a, b)
        | _ => none
      let online := TraceTableOps.entries (V := St) st.trΔ.p
      let offline := TraceTableOps.entries (V := St)
        (TraceNabla.ofQueryLogForwardOnly (T_H := TH) (T_P := TP) st.trace).p
      some
        { proverChallenge := cP
          verifierChallenge := cV
          trace := st.trace.map fun
            | ⟨.inl _, c⟩ => ("h", [], c.toList)
            | ⟨.inr (.inl a), b⟩ => ("p", a.toList, b.toList)
            | ⟨.inr (.inr b), a⟩ => ("p⁻¹", b.toList, a.toList)
          gCalls := g
          pFunctional := fwd.all fun (a, b) => fwd.all fun (a', b') => a ≠ a' || b == b'
          onlineIndexIsOffline := online.all (· ∈ offline) && offline.all (· ∈ online) }
  | (none, _) => none

/-- The honest run is consistent: both parties derive the same challenge, `g` is reached once
per party (the round boundary is recognised), the simulated `p` is a function, and the online
index agrees with StdTrace's offline index. -/
def consistent (lP lV δ : ℕ) : Bool :=
  match run lP lV δ with
  | some o => o.proverChallenge == o.verifierChallenge && o.gCalls == 2 && o.pFunctional &&
      o.onlineIndexIsOffline
  | none => false

end Harness

section RateOne

local instance : SpongeSize := ⟨2, 1, by omega⟩

-- `r = c = 1`, `ℓ_P = 1`, `ℓ_V = 2`, `δ = 0`: the prover's second squeeze `p(s₁)` pops
-- `s₂ = (2, 12)` from `Cache_p`, and the verifier's replay must get the same answer.
/-- info: some [1, 2] -/
#guard_msgs in
#eval (run 1 2 0).map (·.proverChallenge)

/-- info: some [1, 2] -/
#guard_msgs in
#eval (run 1 2 0).map (·.verifierChallenge)

/--
info: some
  [("h", [], [10]), ("p", [0, 10], [1, 11]), ("p", [1, 11], [2, 12]), ("h", [], [10]), ("p", [0, 10], [1, 11]),
    ("p", [1, 11], [2, 12])]
-/
#guard_msgs (whitespace := lax) in
#eval (run 1 2 0).map (·.trace)

-- Sweep `ℓ_P ∈ {1,2,3}`, `ℓ_V ∈ {1,…,4}`, `δ ∈ {0,…,3}`.
/-- info: true -/
#guard_msgs in
#eval [0, 1, 2, 3].all fun δ => [1, 2, 3].all fun lP => [1, 2, 3, 4].all fun lV =>
  consistent lP lV δ

end RateOne

section RateTwo

local instance : SpongeSize := ⟨3, 2, by omega⟩

-- `r = 2`, `c = 1`, block-aligned salts `δ ∈ {0, 2, 4}`. (For `r ∤ δ` the salt shares the
-- first message block, which the one-round `BackTrack` does not recognise yet.)
/-- info: true -/
#guard_msgs in
#eval [0, 2, 4].all fun δ => [1, 2, 3].all fun lP => [1, 2, 3, 4].all fun lV =>
  consistent lP lV δ

end RateTwo

/-! ### The honest trace of the `ℓ_V = 2` run is free of bad events -/

section BadEvent

open BadEventDS

local instance : SpongeSize := ⟨2, 1, by omega⟩

/-- A state of the toy sponge. -/
abbrev St := CanonicalSpongeState UInt8
/-- A trace entry of the toy sponge. -/
abbrev Ent := Sigma (duplexSpongeChallengeOracle Unit UInt8)
/-- A trace of the toy sponge. -/
abbrev L := QueryLog (duplexSpongeChallengeOracle Unit UInt8)

/-- A hash entry `('h', (), c)`. -/
def hE (c : Vector UInt8 SpongeSize.C) : Ent := ⟨.inl (), c⟩
/-- A forward permutation entry `('p', a, b)`. -/
def pE (a b : St) : Ent := ⟨.inr (.inl a), b⟩

/-- Hash answer. -/
def c0 : Vector UInt8 SpongeSize.C := #v[10]
/-- Absorb state. -/
def s0 : St := #v[0, 10]
/-- First squeeze output (programmed from `g`). -/
def s1 : St := #v[1, 11]
/-- Second squeeze output (the `Cache_p` pair). -/
def s2 : St := #v[2, 12]

/-- The trace of `run 1 2 0`, as pinned by the `#guard` above. -/
def trHonest : L := [hE c0, pE s0 s1, pE s1 s2, hE c0, pE s0 s1, pE s1 s2]

lemma aux_cons_keep (e : Ent) (rest acc : L) (h : ¬ isRedundantEntryOfPrefix acc e) :
    getBaseTraceAux (e :: rest) acc = getBaseTraceAux rest (acc ++ [e]) := by
  simp only [getBaseTraceAux, h, ↓reduceDIte]

lemma aux_cons_drop (e : Ent) (rest acc : L) (h : isRedundantEntryOfPrefix acc e) :
    getBaseTraceAux (e :: rest) acc = getBaseTraceAux rest acc := by
  simp only [getBaseTraceAux, h, ↓reduceDIte]

/-- Keep the head entry of a base-trace scan. -/
macro "keep" : tactic => `(tactic| (
  rw [aux_cons_keep _ _ _ (by
    simp [isRedundantEntryOfPrefix, hE, pE, s0, s1, s2, c0] <;> (try constructor) <;>
      intro h <;> exact absurd (congrArg Sigma.fst h) (by simp))]
  simp only [List.nil_append, List.cons_append]))

/-- Drop the head entry of a base-trace scan as redundant. -/
macro "drop" : tactic => `(tactic| (
  rw [aux_cons_drop _ _ _ (by simp [isRedundantEntryOfPrefix, hE, pE, s0, s1, s2, c0])]))

lemma base_trHonest : getBaseTrace trHonest = [hE c0, pE s0 s1, pE s1 s2] := by
  unfold getBaseTrace trHonest
  keep; keep; keep; drop; drop; drop
  simp only [getBaseTraceAux]

/-! The event bodies of `E`, stated over an explicit base trace (definitionally equal). -/

/-- `E_dup` hash part over a list. -/
def dupHashOn (bt : L) : Prop :=
  ∃ j : Fin bt.length, ∃ capSeg : Vector UInt8 SpongeSize.C,
    (∃ stmt : Unit, bt[j] = ⟨.inl stmt, capSeg⟩) ∧ isDuplicatedPriorCapacity bt j capSeg
/-- `E_dup` forward part over a list. -/
def dupPermOn (bt : L) : Prop :=
  ∃ j : Fin bt.length, ∃ capSeg : Vector UInt8 SpongeSize.C,
    (∃ stateIn stateOut, bt[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      CanonicalSpongeState.capacitySegment stateOut = capSeg) ∧
    isDuplicatedPriorCapacity bt j capSeg
/-- `E_dup` inverse part over a list. -/
def dupPermInvOn (bt : L) : Prop :=
  ∃ j : Fin bt.length, ∃ capSeg : Vector UInt8 SpongeSize.C,
    (∃ stateOut stateIn, bt[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      CanonicalSpongeState.capacitySegment stateIn = capSeg) ∧
    isDuplicatedPriorCapacity bt j capSeg
/-- `E_func` over a list. -/
def funcOn (bt : L) : Prop :=
  ∃ j : Fin bt.length, ∃ stateIn stateOut : St,
    (bt[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : St, bt[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : St, bt[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (bt[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      ∃ j' < j,
        (∃ stateIn1 : St, bt[j'] = ⟨.inr <|.inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : St, bt[j'] = ⟨.inr <|.inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

lemma E_iff (tr : L) : E tr ↔ (dupHashOn (getBaseTrace tr) ∨ dupPermOn (getBaseTrace tr) ∨
    dupPermInvOn (getBaseTrace tr)) ∨ funcOn (getBaseTrace tr) := Iff.rfl

@[simp] lemma ne_s0_s1 : (s0 = s1) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma ne_s1_s0 : (s1 = s0) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma ne_s1_s2 : (s1 = s2) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma ne_s2_s1 : (s2 = s1) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma ne_s0_s2 : (s0 = s2) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma ne_s2_s0 : (s2 = s0) ↔ False :=
  ⟨fun h => absurd (congrArg Vector.toList h) (by decide), False.elim⟩
@[simp] lemma v1_eq (a b : UInt8) : ((#v[a] : Vector UInt8 SpongeSize.C) = #v[b]) ↔ a = b :=
  ⟨fun h => by simpa using congrArg Vector.toList h, fun h => h ▸ rfl⟩
@[simp] lemma cap_s0 : CanonicalSpongeState.capacitySegment s0 = #v[10] := rfl
@[simp] lemma cap_s1 : CanonicalSpongeState.capacitySegment s1 = #v[11] := rfl
@[simp] lemma cap_s2 : CanonicalSpongeState.capacitySegment s2 = #v[12] := rfl
@[simp] lemma heq_vec (a : (duplexSpongeChallengeOracle Unit UInt8) (Sum.inl ()))
    (b : Vector UInt8 SpongeSize.C) : (a ≍ b) ↔ a = b := heq_iff_eq

/-- Discharge a `Vector` (in)equality between distinct toy constants. -/
macro "closeVec" : tactic => `(tactic| (
  first
  | exact absurd (congrArg Vector.toList (eq_of_heq ‹_›)) (by decide)
  | exact absurd (congrArg Vector.toList ‹_›) (by decide)))

/-- Case-split an `E_dup` witness over the three base-trace positions. -/
macro "kill" : tactic => `(tactic| (
  rintro ⟨j, capSeg, hj, hdup⟩
  fin_cases j <;>
  simp_all [isDuplicatedPriorCapacity, Fin.exists_fin_succ, Fin.lt_def, Fin.le_def,
    Sigma.ext_iff, hE, pE, heq_iff_eq] <;> (try subst_vars) <;>
    (try simp_all (config := {decide := true}) [Vector.ext_iff])))

lemma honest_dupHash : ¬ dupHashOn [hE c0, pE s0 s1, pE s1 s2] := by kill

lemma honest_dupPerm : ¬ dupPermOn [hE c0, pE s0 s1, pE s1 s2] := by
  kill
  all_goals (rename_i h; rcases h with ⟨_, h⟩ | h | h | h <;> closeVec)

lemma honest_dupPermInv : ¬ dupPermInvOn [hE c0, pE s0 s1, pE s1 s2] := by kill

lemma honest_func : ¬ funcOn [hE c0, pE s0 s1, pE s1 s2] := by
  rintro ⟨j, sIn, sOut, h⟩
  fin_cases j <;>
  simp_all [Fin.exists_fin_succ, Fin.lt_def, Sigma.ext_iff, hE, pE]
  all_goals (obtain ⟨⟨rfl, rfl⟩, h0, -⟩ := h; simp at h0)

/-- The honest prover-then-verifier trace under `D2SQuery` (pinned by the `#guard` above) has no
bad event. Before the Item 4(c)i fix, the verifier's replay `p(s₁)` was resampled and `E_func`
held on this run. -/
theorem honest_not_E : ¬ E trHonest := by
  rw [E_iff, base_trHonest]
  rintro ((h | h | h) | h)
  · exact honest_dupHash h
  · exact honest_dupPerm h
  · exact honest_dupPermInv h
  · exact honest_func h

end BadEvent

end ArkLibTest.D2SQueryCachePop

/--
info: 'ArkLibTest.D2SQueryCachePop.honest_not_E' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLibTest.D2SQueryCachePop.honest_not_E
