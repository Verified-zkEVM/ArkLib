/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Fri.Spec.Extraction.Program
import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomial
import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluation
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled FRI extractor checks

Small immutable histories exercise the named measured extractor and its exact instruction counts.
Arithmetic corner cases protect the pinned raw-array interpolation semantics.
-/

namespace FriExtractorRuntime

open Domain CompPoly Fri.Spec Fri.Spec.Extractor OracleComp OracleSpec

abbrev F := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
instance : NonBinaryField F where
  char_neq_2 := by decide

/-- A shifted eight-point domain, with ratio `9` of order eight. -/
def domain8 : SmoothCosetFftDomain 3 F where
  subgroupDomain := {
    toFun := fun i ↦ Units.mk0 (9 ^ i.toAdd.val) (pow_ne_zero _ (by decide))
    map_one' := by decide
    map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := Units.mk0 3 (by decide)

/-- The smallest domain supporting one binary fold. -/
def domain2 : SmoothCosetFftDomain 1 F where
  subgroupDomain := {
    toFun := fun i ↦ Units.mk0 ((-1 : F) ^ i.toAdd.val) (pow_ne_zero _ (by decide))
    map_one' := by decide
    map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := Units.mk0 3 (by decide)

/-- A shifted full multiplicative group, with ratio `3` of order sixteen. -/
def domain16 : SmoothCosetFftDomain 4 F where
  subgroupDomain := {
    toFun := fun i ↦ Units.mk0 (3 ^ i.toAdd.val) (pow_ne_zero _ (by decide))
    map_one' := by decide
    map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := Units.mk0 5 (by decide)

/-- A singleton domain with nontrivial shift. -/
def domain1 : SmoothCosetFftDomain 0 F where
  subgroupDomain := 1
  subgroupDomain_inj := by decide
  cosetGenerator := Units.mk0 3 (by decide)

/-- One binary folding round. -/
def schedule : Fin 1 → ℕ+ := fun _ ↦ 1

/-- Retain one arbitrary word followed by a transmitted final polynomial. -/
def history {n : ℕ} (ω : SmoothCosetFftDomain n F) (f : F → F)
    (p : CPolynomial F) : ∀ j, FinalOracleStatement schedule ω j := by
  intro j
  unfold FinalOracleStatement
  split
  · exact p
  · exact fun x ↦ f x.val

/-- The single folding challenge is zero. -/
def challenges : FinalStatement F 0 := fun _ ↦ 0

/-- Run the actual extraction program and retain its complete instruction profile. -/
def measured (d : ℕ+) (f : F → F) (p : CPolynomial F) :=
  profile schedule (history domain8 f p) challenges
    (extractProgram schedule d (by decide) (history domain8 f p) challenges)

/-- Inspect the actual scan before interpolation, including its bounded ordered sample cache. -/
def scanSnapshot (d : ℕ+) (f : F → F) : Option (ℕ × List ℕ × Array F × Array F) :=
  (profile schedule (history domain8 f 0) challenges (do
    let input? ← prepareInputs schedule (history domain8 f 0) challenges d
    match input? with
    | none => pure none
    | some input =>
      let state ← scan schedule (history domain8 f 0) challenges (by decide) input.generator
        (checkPosition schedule (history domain8 f 0) challenges (by decide) input)
        (foldingDegree schedule d 0)
      pure (some (state.val.count, state.val.selected.map Fin.val,
        state.val.nodes, state.val.values)))).1

/-- Two binary folding rounds. -/
def scheduleTwo : Fin 2 → ℕ+ := ![1, 1]
/-- A binary fold followed by a fold of factor four. -/
def scheduleHeterogeneous : Fin 2 → ℕ+ := ![1, 2]

/-- Retain two arbitrary words followed by a transmitted final polynomial. -/
def historyTwo {n : ℕ} (ω : SmoothCosetFftDomain n F) (s : Fin 2 → ℕ+)
    (f g : F → F) (p : CPolynomial F) : ∀ j, FinalOracleStatement s ω j := by
  intro j
  unfold FinalOracleStatement
  split
  · exact p
  · exact fun x ↦ if j.val = 0 then f x.val else g x.val

/-- Both folding challenges are zero. -/
def challengesTwo : FinalStatement F 1 := fun _ ↦ 0

/-- A final challenge and zero polynomial, before query sampling. -/
def finalTranscript : (FinalFoldPhase.pSpec F).FullTranscript
  | ⟨0, _⟩ => (0 : F)
  | ⟨1, _⟩ => (0 : CPolynomial F)

/-- Full transcripts differing only in their sampled query vector. -/
def transcript (queries : Fin 3 → (domain8.subdomain 0).toFinset) :
    (pSpec 0 (ω := domain8) schedule 3).FullTranscript :=
  ProtocolSpec.FullTranscript.append
    (ProtocolSpec.FullTranscript.append
      (pSpec₁ := pSpecFold 0 (ω := domain8) schedule) (fun i ↦ Fin.elim0 i)
      finalTranscript)
    (fun | ⟨0, _⟩ => queries)

/-- A zero polynomial output witness. -/
def zeroOutput : Witness F schedule 1 (Fin.last 1) :=
  ⟨0, CPolynomial.mem_degreeLT_iff_size_le.mpr (by change 0 ≤ _; omega)⟩

/-- A different well-typed output witness, independent of the retained transcript. -/
def oneOutput : Witness F schedule 1 (Fin.last 1) :=
  ⟨CPolynomial.C 1, CPolynomial.mem_degreeLT_iff_size_le.mpr (by
    apply (CPolynomial.size_C_le (1 : F)).trans
    apply Nat.succ_le_iff.mpr
    positivity)⟩

/-- Observe the public straightline wrapper through the empty ambient oracle. -/
def extracted (queries : Fin 3 → (domain8.subdomain 0).toFinset)
    (w : Witness F schedule 1 (Fin.last 1)) : Option (Array F) :=
  ((simulateQ (r := Id) (fun i ↦ PEmpty.elim i)
      ((extract schedule 1 (by decide) 3
        ⟨Fin.elim0, fun _ _ ↦ 0⟩ w (transcript queries) [] []).run)) :
      Option (Witness F schedule 1 0)).map (fun p ↦ p.val.val)

/-- Fail the executable when a delayed assertion is false. -/
def check (label : String) (ok : Unit → Bool) : IO Unit := do
  unless ok () do throw (IO.userError s!"FRI extractor runtime check failed: {label}")
  IO.println s!"ok: {label}"

/-- Coordinate order: add, subtract, multiply, invert, compare, coefficient, node, value,
then metadata. -/
def arithmeticCounts (cost : ArithmeticCost) : List ℕ :=
  [.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead, .valueRead, .metadata].map cost

/-- Protect exact padded arithmetic and data-dependent trim behavior. -/
def arithmeticChecks : IO Unit := do
  let rightEmpty := profileArithmetic (Arithmetic.mulRaw (#[3, 4] : Array F) #[])
  check "raw convolution keeps shifted empty-right padding" fun _ ↦
    rightEmpty.1.val == #[0] &&
    arithmeticCounts rightEmpty.2 == [1, 0, 0, 0, 0, 4, 0, 0, 8]
  let leftEmpty := profileArithmetic (Arithmetic.mulRaw (#[] : Array F) #[3, 4])
  check "empty raw left has one terminal tick" fun _ ↦
    leftEmpty.1.val.isEmpty &&
    arithmeticCounts leftEmpty.2 == [0, 0, 0, 0, 0, 0, 0, 0, 1]
  let emptyEval := profileArithmetic (Arithmetic.evalRaw (#[] : Array F) 3)
  check "empty power sum has one terminal tick" fun _ ↦
    emptyEval.1.val == 0 &&
    arithmeticCounts emptyEval.2 == [0, 0, 0, 0, 0, 0, 0, 0, 1]
  let emptyInterp := profileArithmetic (Arithmetic.interpolate (#[] : Array F) #[] 0)
  check "empty interpolation has two terminal ticks" fun _ ↦
    emptyInterp.1.val.val.isEmpty &&
    arithmeticCounts emptyInterp.2 == [0, 0, 0, 0, 0, 0, 0, 0, 2]
  let zeroInterp := profileArithmetic (Arithmetic.interpolate (#[3] : Array F) #[0] 1)
  check "zero sample retains raw singleton scalar before trimming" fun _ ↦
    zeroInterp.1.val.val.isEmpty &&
    arithmeticCounts zeroInterp.2 == [2, 0, 1, 0, 2, 8, 0, 1, 14]
  let collide := profileArithmetic (Arithmetic.interpolate (#[3, 3] : Array F) #[0, 0] 2)
  check "colliding nodes still request every inverse" fun _ ↦ collide.2 .inv == 2
  let zeros := profileArithmetic (Arithmetic.trimRaw (#[0, 0, 0] : Array F))
  let stop := profileArithmetic (Arithmetic.trimRaw (#[0, 0, 3] : Array F))
  check "trim counts zero scans and stops at a nonzero last coefficient" fun _ ↦
    zeros.1.val.isEmpty && stop.1.val == #[0, 0, 3] &&
    arithmeticCounts zeros.2 == [0, 0, 0, 0, 3, 3, 0, 0, 4] &&
    arithmeticCounts stop.2 == [0, 0, 0, 0, 1, 1, 0, 0, 1]

/-- Exercise retained histories, guard ordering, sample caches, and exact small profiles. -/
def extractorChecks : IO Unit := do
  let zero := measured 1 (fun _ ↦ 0) 0
  check "all eight accepting positions recover zero on a shifted domain" fun _ ↦
    scanSnapshot 1 (fun _ ↦ 0) == some (8, [0, 1], #[3, 10], #[0, 0]) &&
    (zero.1.map fun w ↦ w.val.val) == some #[] &&
    zero.2 (.inr .wordRead) == 18 && zero.2 (.inl .inv) == 19 &&
    zero.2 (.inr .domainRead) == 2 && zero.2 (.inr .challengeRead) == 1
  let constant := measured 1 (fun _ ↦ 7) (CPolynomial.C 7)
  check "constant retained word recovers its canonical constant" fun _ ↦
    (constant.1.map fun w ↦ w.val.val) == some #[7]
  let largePolynomial := CPolynomial.monomial 4096 (1 : F)
  let oversized := measured 1 (fun _ ↦ 0) largePolynomial
  check "large final polynomial rejects before other input accesses" fun _ ↦
    largePolynomial.val.size == 4097 && largePolynomial.natDegree == 4096 &&
    oversized.1.isNone && oversized.2 (.inr .finalPolynomialRead) == 1 &&
    oversized.2 (.inl .metadata) == 1 &&
    oversized.2 (.inr .wordRead) == 0 && oversized.2 (.inr .domainRead) == 0 &&
    oversized.2 (.inr .challengeRead) == 0 && oversized.2 (.inl .coefficientRead) == 0 &&
    oversized.2 (.inl .add) == 0 && oversized.2 (.inl .sub) == 0 &&
    oversized.2 (.inl .mul) == 0 && oversized.2 (.inl .inv) == 0 &&
    oversized.2 (.inl .eq) == 0 && oversized.2 (.inl .nodeRead) == 0 &&
    oversized.2 (.inl .valueRead) == 0
  let exact := measured 1 (fun x ↦ if x = 3 ∨ x = -3 then 0 else 1) 0
  check "exactly two accepting positions fill the recovery cache" fun _ ↦
    scanSnapshot 1 (fun x ↦ if x = 3 ∨ x = -3 then 0 else 1) ==
      some (2, [0, 4], #[3, 14], #[0, 0]) &&
    (exact.1.map fun w ↦ w.val.val) == some #[] && exact.2 (.inr .wordRead) == 18
  let fewer := measured 2 (fun x ↦ if x = 3 ∨ x = -3 then 0 else 1) 0
  check "nonempty acceptance below the required degree rejects" fun _ ↦
    scanSnapshot 2 (fun x ↦ if x = 3 ∨ x = -3 then 0 else 1) ==
      some (2, [0, 4], #[3, 14], #[0, 0]) &&
    fewer.1.isNone && fewer.2 (.inr .wordRead) == 18
  let excessiveDimension := measured 5 (fun _ ↦ 0) 0
  check "degree dimension beyond domain size remains total and rejects" fun _ ↦
    excessiveDimension.1.isNone && excessiveDimension.2 (.inr .wordRead) == 24 &&
    excessiveDimension.2 (.inl .inv) == 17 &&
    excessiveDimension.2 (.inr .finalPolynomialRead) == 1
  let small := profile schedule (history domain2 (fun _ ↦ 0) 0) challenges
    (extractProgram schedule 1 (by decide) _ challenges)
  check "smallest binary domain recovers at the full-rate boundary" fun _ ↦
    (small.1.map fun w ↦ w.val.val) == some #[] &&
    small.2 (.inr .wordRead) == 6 && small.2 (.inl .inv) == 7
  let malicious := profile scheduleTwo
    (historyTwo domain8 scheduleTwo (fun _ ↦ 0) (fun _ ↦ 1) 0) challengesTwo
    (extractProgram scheduleTwo 1 (by decide) _ challengesTwo)
  check "arbitrary inconsistent intermediate word short-circuits each position" fun _ ↦
    malicious.1.isNone && malicious.2 (.inr .wordRead) == 24 &&
    malicious.2 (.inl .inv) == 17
  let heterogeneous := profile scheduleHeterogeneous
    (historyTwo domain16 scheduleHeterogeneous (fun x ↦ x + 5) (fun _ ↦ 5)
      (CPolynomial.C 5)) challengesTwo
    (extractProgram scheduleHeterogeneous 1 (by decide) _ challengesTwo)
  check "heterogeneous folds preserve shifted-domain order and exact counts" fun _ ↦
    (heterogeneous.1.map fun w ↦ w.val.val) == some #[5, 1] &&
    heterogeneous.2 (.inr .wordRead) == 120 && heterogeneous.2 (.inl .inv) == 281 &&
    heterogeneous.2 (.inr .domainRead) == 2 && heterogeneous.2 (.inr .challengeRead) == 2
  check "public wrapper ignores repeated queries and the output witness" fun _ ↦
    extracted (fun _ ↦ initialQuery (ω := domain8) 0) zeroOutput == some #[] &&
    extracted (fun i ↦ initialQuery (ω := domain8) ⟨i.val + 1, by omega⟩) oneOutput == some #[]
  let single := profile schedule (history domain1 (fun _ ↦ 0) 0) challenges
    (initGenerator schedule _ challenges)
  check "singleton generic generator reads one shifted point without arithmetic" fun _ ↦
    single.1.point0 == 3 && single.1.ratio == 1 &&
    single.2 (.inr .domainRead) == 1 && single.2 (.inl .inv) == 0 &&
    single.2 (.inl .mul) == 0

end FriExtractorRuntime

def main : IO Unit := do
  FriExtractorRuntime.arithmeticChecks
  FriExtractorRuntime.extractorChecks
