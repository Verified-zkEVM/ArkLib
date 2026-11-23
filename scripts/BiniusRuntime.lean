/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.FRIBinius.Executable
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import CompPoly.Fields.Binary.Tower.Concrete.Algebra
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Compiled FRI-Binius checks

The fixtures use GF(16) over GF(2) with the low-bit-first tower basis. A scripted oracle supplies
fixed inputs to the uniform samplers, so the challenge schedule and output values are reproducible.
-/

open ConcreteBinaryTower Module OracleSpec OracleComp ProtocolSpec

namespace BiniusRuntime

open Binius.BinaryBasefold AdditiveNTT
open RingSwitching.Packing.TensorPrefix.Computable

private abbrev noOutputOracle (i : Empty) : OracleInterface Unit := nomatch i

abbrev K := ConcreteBTField 0
abbrev L := ConcreteBTField 2

def wordEquiv (k : ℕ) : Fin (2 ^ (2 ^ k)) ≃ ConcreteBTField k where
  toFun i := ConcreteBinaryTower.fromNat i.val
  invFun x := ⟨x.toNat, x.toNat_lt⟩
  left_inv i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  right_inv := ConcreteBTField.fromNat_toNat

local instance fintypeK : Fintype K := Fintype.ofEquiv (Fin 2) (wordEquiv 0)
local instance fintypeL : Fintype L := Fintype.ofEquiv (Fin 16) (wordEquiv 2)
local instance : Fact (Fintype.card K = 2) :=
  ⟨(Fintype.card_congr (wordEquiv 0)).symm.trans (Fintype.card_fin 2)⟩

local instance : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
local instance : SampleableType L := SampleableType.ofEquiv (wordEquiv 2)
local instance algebra : Algebra K L := ConcreteBTFieldAlgebra (h_le := by decide)

def coords (x : L) (i : Fin 4) : K :=
  ConcreteBTField.ofBitVec (x.toBitVec.extractLsb' i.val 1)

def fromCoords (f : Fin 4 → K) : L :=
  ConcreteBTField.ofBitVec <| (f 3).toBitVec ++ (f 2).toBitVec ++ (f 1).toBitVec ++ (f 0).toBitVec

def asFinsupp (f : Fin 4 → K) : Fin 4 →₀ K where
  support := Finset.univ.filter (fun i => f i ≠ 0)
  toFun := f
  mem_support_toFun i := by simp

theorem coords_fromCoords (f : Fin 4 → K) (i : Fin 4) : coords (fromCoords f) i = f i := by
  apply ConcreteBTField.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  fin_cases i <;>
    simp only [coords, fromCoords, ConcreteBTField.toBitVec_ofBitVec, Nat.pow_zero, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Order.lt_one_iff, BitVec.getLsbD_eq_getElem,
      BitVec.getElem_extractLsb', Nat.add_zero]
  all_goals
    rw [BitVec.getLsbD_eq_getElem] <;> norm_num
    repeat' (rw [BitVec.getElem_append]; norm_num)

theorem fromCoords_coords (x : L) : fromCoords (coords x) = x := by
  apply ConcreteBTField.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 4 at hj
  interval_cases j <;>
    simp only [coords, fromCoords, ConcreteBTField.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_append] <;> norm_num

theorem coords_add (x y : L) (i : Fin 4) : coords (x + y) i = coords x i + coords y i := by
  apply ConcreteBTField.ext
  change (x.toBitVec ^^^ y.toBitVec).extractLsb' i.val 1 =
    x.toBitVec.extractLsb' i.val 1 ^^^ y.toBitVec.extractLsb' i.val 1
  exact BitVec.extractLsb'_xor

theorem coords_smul (a : K) (x : L) (i : Fin 4) : coords (a • x) i = a • coords x i := by
  rcases concrete_eq_zero_or_eq_one (a := a) (h_k_zero := rfl) with rfl | rfl
  · change coords ((0 : K) • x) i = (0 : K) • coords x i
    rw [zero_smul, zero_smul]
    change ConcreteBTField.ofBitVec (k := 0) ((0#4).extractLsb' i.val 1) = _
    rw [BitVec.extractLsb'_zero]
    rfl
  · change coords ((1 : K) • x) i = (1 : K) • coords x i
    simp

def basis : Basis (Fin 4) K L := .ofRepr {
  toFun := fun x => asFinsupp (coords x)
  invFun := fun f => fromCoords f
  left_inv := fromCoords_coords
  right_inv := fun f => Finsupp.ext fun i => coords_fromCoords f i
  map_add' := fun x y => Finsupp.ext fun i => by
    change coords (x + y) i = (asFinsupp (coords x) + asFinsupp (coords y)) i
    rw [Finsupp.add_apply]
    exact coords_add x y i
  map_smul' := fun a x => Finsupp.ext fun i => by
    change coords (a • x) i = (a • asFinsupp (coords x)) i
    rw [Finsupp.smul_apply]
    exact coords_smul a x i
}

theorem basis_zero : basis 0 = 1 := by
  change fromCoords (Finsupp.single 0 1) = 1
  apply ConcreteBTField.ext
  simp only [fromCoords, ConcreteBTField.toBitVec_ofBitVec, Finsupp.single_apply]
  decide

def basisWord (i : Fin 4) : L := fromNat (2 ^ i.val)

theorem basis_eq_word (i : Fin 4) : basis i = basisWord i := by
  change fromCoords (Finsupp.single i 1) = fromNat (2 ^ i.val)
  apply ConcreteBTField.ext
  fin_cases i <;>
    simp only [fromCoords, ConcreteBTField.toBitVec_ofBitVec, Finsupp.single_apply] <;> decide

theorem coords_eq_repr (x : L) (i : Fin 4) : coords x i = basis.repr x i := rfl

local instance independentBasis : Fact (LinearIndependent K basisWord) :=
  ⟨(funext basis_eq_word) ▸ basis.linearIndependent⟩

local instance : Fact (basisWord 0 = 1) := ⟨(basis_eq_word 0).symm.trans basis_zero⟩

def cubeBasis (u : Cube 2) : L := basisWord (finFunctionFinEquiv u)
def cubeCoords (x : L) (u : Cube 2) : K := coords x (finFunctionFinEquiv u)

theorem cubeCoords_spec : ∃ b : Basis (Fin 4) K L,
    (⇑b) = basisWord ∧ cubeCoords = fun x u => b.repr x (finFunctionFinEquiv u) :=
  ⟨basis, funext basis_eq_word, rfl⟩

/-- Interpret a Boolean cube coordinate as an element of the small field. -/
def bit (i : Fin 2) : K := if i.val = 0 then 0 else 1

/-- The source polynomial is `X₀ + X₂`. -/
def sourceOne (y : Fin 3 → Fin 2) : K := bit (y 0) + bit (y 2)

/-- The source polynomial is `X₀ + X₂X₃`. -/
def sourceTwo (y : Fin 4 → Fin 2) : K := bit (y 0) + bit (y 2) * bit (y 3)

def pointOne : Fin 3 → L := ![1, 0, 0]
def pointTwo : Fin 4 → L := ![1, 0, 0, 0]

def packedOne (i : Fin 2) : L := fromNat (![10, 5] i)
def packedTwo (i : Fin 4) : L := fromNat (![10, 10, 10, 5] i)

private theorem rateOne : 1 + 1 < 4 := by decide
private theorem rateTwo : 2 + 1 < 4 := by decide

local instance (m : ℕ) : Fact ((1 : ℕ) ∣ m) := ⟨one_dvd m⟩

/-- With `R = 1`, one folding block starts from four coded symbols. -/
def firstOne : Fin 4 → L :=
  firstOracleEncodingTable (ℓ := 1) (𝓡 := 1) basisWord rateOne packedOne

/-- With `R = 1`, two folding blocks start from eight coded symbols. -/
def firstTwo : Fin 8 → L :=
  firstOracleEncodingTable (ℓ := 2) (𝓡 := 1) basisWord rateTwo packedTwo

/-- At round zero, the domain index is the low-bit-first tower word. -/
abbrev InitialOracles {m : ℕ} [NeZero m] (hRate : m + 1 < 4)
    (ϑ : ℕ := 1) [NeZero ϑ] :=
  ∀ j, OracleStatement K basisWord (h_ℓ_add_R_rate := hRate) ϑ (0 : Fin (m + 1)) j

/-- Read the coded word, optionally changing the value queried at zero. -/
def firstFamily {m : ℕ} [NeZero m] (hRate : m + 1 < 4)
    (encoded : Fin (2 ^ (m + 1)) → L) (tamper : Bool)
    (ϑ : ℕ := 1) [NeZero ϑ] : InitialOracles hRate ϑ :=
  fun _ x =>
    let result := encoded (Fin.ofNat (2 ^ (m + 1)) x.val.toNat)
    if tamper && x.val.toNat == 0 then result + 1 else result

def foldedPoint (j : Fin 4) : sDomain K basisWord (ℓ := 2) (R_rate := 1) rateTwo (1 : Fin 4) :=
  finToSDomainExecutable (h_ℓ_add_R_rate := rateTwo) basisWord (1 : Fin 4) (by decide) j

def firstPoint (j : Fin 4) : sDomain K basisWord (ℓ := 1) (R_rate := 1) rateOne (0 : Fin 4) :=
  finToSDomainExecutable (h_ℓ_add_R_rate := rateOne) basisWord (0 : Fin 4) (by decide) j

/-- Two batching coordinates precede the optional separate sum-check, folding, and one query. -/
def challenges (prefixRounds : ℕ) (folding : List ℕ) (queryBound : ℕ) : List (ℕ × ℕ) :=
  List.replicate (2 + prefixRounds) (15, 0) ++ folding.map (15, ·) ++ [(queryBound, 0)]

structure SampleScript where
  remaining : List (ℕ × ℕ)
  valid : Bool := true

/-- Interpret each scripted answer and record a mismatch in its expected sampling bound. -/
def fixedUniform : QueryImpl unifSpec (StateM SampleScript) := fun n => do
  let state ← get
  match state.remaining with
  | [] =>
      set { state with valid := false }
      pure 0
  | (bound, a) :: rest =>
      set (SampleScript.mk rest (state.valid && n == bound && decide (a ≤ n)))
      pure (Fin.ofNat (n + 1) a)

def SampleScript.finished (s : SampleScript) : Bool :=
  s.valid && s.remaining.isEmpty

def challengeScript {n : ℕ} {wire : ProtocolSpec n}
    [∀ j, SampleableType (wire.Challenge j)] :
    QueryImpl ([]ₒ + [wire.Challenge]ₒ'challengeOracleInterface) (StateM SampleScript)
  | .inl i => nomatch i
  | .inr q => simulateQ fixedUniform (challengeQueryImpl (pSpec := wire) q)

structure OpeningObservation where
  samplesMatched : Bool
  proverAccepted : Bool
  honest : Option Bool
  wrongClaim : Option Bool
  wrongFirstWord : Option Bool
  tamperedTranscriptVerdict : Option (Option Bool)
  wireValues : List ℕ
  deriving Repr

/-- Replay the honest transcript against the honest statement and each changed input. -/
def observe {n : ℕ} {wire : ProtocolSpec n} {Stmt Witness Out WitOut : Type}
    [∀ j, SampleableType (wire.Challenge j)]
    (R : Reduction []ₒ Stmt Witness Out WitOut wire) (readVerdict : Out → Bool)
    (stmts : Stmt × Stmt × Stmt) (witness : Witness) (samples : List (ℕ × ℕ))
    (readWire : wire.FullTranscript → List ℕ)
    (tamperTranscript : Option (wire.FullTranscript → wire.FullTranscript) := none) :
    OpeningObservation :=
  let ((tr, st, _), script) :=
    (simulateQ challengeScript (R.prover.run stmts.1 witness)).run (SampleScript.mk samples true)
  let verify s transcript := (R.verifier.run s transcript).run.runEmpty.map readVerdict
  ⟨script.finished, readVerdict st, verify stmts.1 tr, verify stmts.2.1 tr,
    verify stmts.2.2 tr, tamperTranscript.map (fun tamper => verify stmts.1 (tamper tr)),
    readWire tr⟩

def OpeningObservation.passes (o : OpeningObservation) (expectedWire : List ℕ)
    (expectTamper : Bool) : Bool :=
  o.samplesMatched && o.proverAccepted && o.honest == some true && o.wrongClaim == none &&
    o.wrongFirstWord == none &&
    o.tamperedTranscriptVerdict == (if expectTamper then some none else none) &&
    o.wireValues == expectedWire

def observeOne {n : ℕ} {wire : ProtocolSpec n} {Out WitOut : Type}
    [∀ j, SampleableType (wire.Challenge j)]
    (R : Reduction []ₒ (((Fin 3 → L) × L) × InitialOracles rateOne) (Cube 3 → K)
        Out WitOut wire)
    (verdict : Out → Bool) (prefixRounds : ℕ) (readFinal : wire.FullTranscript → L) :
    OpeningObservation :=
  let oracle := firstFamily rateOne firstOne false
  let badOracle := firstFamily rateOne firstOne true
  observe R verdict (((pointOne, 1), oracle), ((pointOne, 0), oracle), ((pointOne, 1), badOracle))
    sourceOne (challenges prefixRounds [0] 3) (fun tr => [(readFinal tr).toNat])

def observeTwo {n : ℕ} {wire : ProtocolSpec n} {Out WitOut : Type}
    [∀ j, SampleableType (wire.Challenge j)]
    (R : Reduction []ₒ (((Fin 4 → L) × L) × InitialOracles rateTwo) (Cube 4 → K)
        Out WitOut wire)
    (verdict : Out → Bool) (prefixRounds : ℕ) (readFinal : wire.FullTranscript → L)
    (readCommit : wire.FullTranscript → (sDomain K basisWord (ℓ := 2) (R_rate := 1)
      rateTwo (1 : Fin 4) → L)) :
    OpeningObservation :=
  let oracle := firstFamily rateTwo firstTwo false
  let badOracle := firstFamily rateTwo firstTwo true
  observe R verdict (((pointTwo, 1), oracle), ((pointTwo, 0), oracle), ((pointTwo, 1), badOracle))
    sourceTwo (challenges prefixRounds [2, 4] 7) fun tr =>
      let committed := readCommit tr
      [(committed (foldedPoint 0)).toNat, (committed (foldedPoint 1)).toNat, (readFinal tr).toNat]

def check (label : String) (ok : Unit → Bool) : IO Unit := do
  unless ok () do throw (IO.userError s!"Binius runtime check failed: {label}")
  IO.println s!"ok: {label}"

def checkOpening (label : String) (expectedWire : List ℕ)
    (run : Unit → OpeningObservation) (expectTamper : Bool := false) : IO Unit := do
  let result := run ()
  unless result.passes expectedWire expectTamper do
    throw (IO.userError s!"Binius runtime check failed: {label}: {repr result}")
  IO.println s!"ok: {label}"

def fieldChecks : IO Unit := do
  check "tower basis and exact finite sampling" fun _ =>
    let (word, script) := (simulateQ fixedUniform ($ᵗ L)).run (SampleScript.mk [(15, 7)] true)
    let words := (List.ofFn basisWord).map ConcreteBTField.toNat
    words == [1, 2, 4, 8] && word.toNat == 7 && script.finished &&
      Fintype.card K == 2 && Fintype.card L == 16

def packingChecks : IO Unit := do
  check "both source evaluations at the opening points are one" fun _ =>
    pointOne 0 + pointOne 2 == 1 && pointTwo 0 + pointTwo 2 * pointTwo 3 == 1
  check "packing to one and two retained variables" fun _ =>
    let one := pack cubeBasis (ℓ := 3) (m := 1) rfl sourceOne
    let two := pack cubeBasis (ℓ := 4) (m := 2) rfl sourceTwo
    List.ofFn (one ∘ finFunctionFinEquiv.symm) == List.ofFn packedOne &&
      List.ofFn (two ∘ finFunctionFinEquiv.symm) == List.ofFn packedTwo
  check "carrier columns, reconstruction, and nonzero batching coordinates" fun _ =>
    let r : Fin 3 → L := ![fromNat 2, fromNat 4, fromNat 4]
    let c : Fin 2 → L := ![fromNat 2, fromNat 4]
    let α := honestMessage (ℓ := 3) (m := 1) (κ := 2) rfl r sourceOne
    (List.ofFn (α ∘ finFunctionFinEquiv.symm)).map ConcreteBTField.toNat == [4, 5, 4, 5] &&
      ((headVerify cubeBasis cubeCoords (ℓ := 3) (m := 1) rfl (r, fromNat 6) α c).map
        (fun result => result.target.toNat)) == some 14

/-- As univariate polynomials in the tower, the initial novel-coordinate tables give
`10 + 5x` and `10 + 15x² + 5x³`, with coefficients written as stored words. -/
def encodingChecks : IO Unit := do
  check "one-block initial encoding" fun _ =>
    (List.ofFn firstOne).map ConcreteBTField.toNat == [10, 15, 0, 5]
  check "two-block initial encoding" fun _ =>
    (List.ofFn firstTwo).map ConcreteBTField.toNat == [10, 0, 5, 10, 4, 0, 1, 0]
  check "round-one normalized domain order" fun _ =>
    (List.ofFn fun j : Fin 4 => (foldedPoint j).val.toNat) == [0, 1, 13, 12]

def packedWitnessOne : Cube 1 → L := packedOne ∘ finFunctionFinEquiv

@[macro_inline] def honestInitialOne (_ : Unit) : InitialOracles rateOne :=
  honestInitialOracleStatementExecutable K basisWord 1 (h_ℓ_add_R_rate := rateOne)
    (Binius.FRIBinius.tableWitnessEquiv packedWitnessOne)

open RingSwitching in
/-- Open the packed polynomial `10 + 15Y₀` at tower word `2`. Its value is `15`, and folding
at the scripted challenge zero exposes the independent constant `10`. -/
def basefoldChecks : IO Unit := do
  check "standalone Binary Basefold honest commitment" fun _ =>
    let oracle := honestInitialOne ()
    let words := List.ofFn fun j : Fin 4 =>
      (oracle ⟨0, by decide⟩ (firstPoint j)).toNat
    words == [10, 15, 0, 5]
  checkOpening "standalone Binary Basefold opening and rejection" [10] fun _ =>
    let evalStmt : MLPEvalStatement L 1 → MLPEvalStatement L 1 := id
    let R := Opening.openingReduction K basisWord evalStmt
      Binius.FRIBinius.tableWitnessEquiv 1 (ϑ := 1) (h_rate := rateOne)
    let honest : MLPEvalStatement L 1 := ⟨![fromNat 2], fromNat 15⟩
    let wrong : MLPEvalStatement L 1 := ⟨![fromNat 2], fromNat 14⟩
    let oracle := honestInitialOne ()
    let badOracle := firstFamily rateOne firstOne true
    observe (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst
      ((honest, oracle), (wrong, oracle), (honest, badOracle))
      packedWitnessOne [(15, 0), (3, 0)] fun tr =>
        [(show L from tr.messages ⟨2, by decide⟩).toNat]

/-- Run the query verifier with two width-one blocks and log its reads even on rejection.
With zero words the first repetition carries zero into the second block. Changing that block's
word to one forces a carry mismatch before the second repetition can read any oracles. -/
private def queryObservation (corruptSecondBlock : Bool) (finalConstant : L) :
    Option Bool × Option (List (ℕ × ℕ)) :=
  let querySpec := pSpecQuery K basisWord 2 (h_ℓ_add_R_rate := rateTwo)
  let queryPoint (index : Fin 8) :=
    finToSDomainExecutable (𝔽q := K) (h_ℓ_add_R_rate := rateTwo)
      basisWord (0 : Fin 4) (by decide) index
  let transcript := FullTranscript.mk1 (pSpec := querySpec) ![queryPoint 0, queryPoint 2]
  let stmt : FinalSumcheckStatementOut (L := L) (ℓ := 2) :=
    { sumcheck_target := 0, challenges := ![fromNat 2, fromNat 4], finalConstant }
  let oracles : ∀ j, OracleStatement K basisWord (h_ℓ_add_R_rate := rateTwo) 1 (Fin.last 2) j :=
    fun j _ => if corruptSecondBlock && j.val == 1 then 1 else 0
  let verifier := QueryPhase.queryOracleVerifierExecutable K basisWord 2 (ϑ := 1)
    (h_ℓ_add_R_rate := rateTwo)
  let program := (verifier.verify (Oₛₒ := noOutputOracle) stmt transcript.challenges).run
  let (verdict, log) := (simulateQ (OracleInterface.simOracle2 []ₒ oracles transcript.messages)
    program.withQueryLog).runEmpty
  let reads := log.mapM fun entry => match entry.1 with
    | .inr (.inl ⟨block, point⟩) => some (block.val, point.val.toNat)
    | _ => none
  (verdict, reads)

/-- Check the expected order in field words, independently of the fiber helpers under test. -/
private def queryChecks : IO Unit := do
  let firstRepetition : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1)]
  let secondRepetition : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 0), (1, 1)]
  check "query verifier: both repetitions read their fibers in order" fun _ =>
    queryObservation false 0 == (some true, some (firstRepetition ++ secondRepetition))
  check "query verifier: carry mismatch prevents the next repetition" fun _ =>
    queryObservation true 0 == (none, some firstRepetition)
  check "query verifier: final constant mismatch prevents the next repetition" fun _ =>
    queryObservation false 1 == (none, some firstRepetition)

open Binius.FRIBinius.Executable in
/-- The two-block packed polynomial is `10 + 15Y₀Y₁`, with field words for the coefficients.
The first fold at word `2` yields the Boolean table `[10, 15]`, whose coded values at indices
`0, 1` are `10, 5`. The second fold at word `4` leaves constant `7`. -/
def openingChecks : IO Unit := do
  checkOpening "modular, one block: accept honest and reject both mutations" [10] fun _ =>
    let R := modularReduction (K := K) (κ := 2) (ℓ' := 1) (R := 1) (ϑ := 1)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateOne 1 cubeCoords_spec
    observeOne (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst 1
      (fun tr => tr.messages ⟨7, by decide⟩)
  checkOpening "modular, two blocks: accept honest and reject both mutations" [10, 5, 7] fun _ =>
    let R := modularReduction (K := K) (κ := 2) (ℓ' := 2) (R := 1) (ϑ := 1)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateTwo 1 cubeCoords_spec
    observeTwo (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst 2
      (fun tr => tr.messages ⟨12, by decide⟩) (fun tr => tr.messages ⟨9, by decide⟩)
  checkOpening "unrolled, one block: accept honest and reject both mutations" [10] fun _ =>
    let R := unrolledReduction (K := K) (κ := 2) (ℓ' := 1) (R := 1) (ϑ := 1)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateOne 1 cubeCoords_spec
    observeOne (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst 0
      (fun tr => tr.messages ⟨4, by decide⟩)
  checkOpening "unrolled, two blocks: accept honest and reject both mutations" [10, 5, 7] fun _ =>
    let R := unrolledReduction (K := K) (κ := 2) (ℓ' := 2) (R := 1) (ϑ := 1)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateTwo 1 cubeCoords_spec
    observeTwo (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst 0
      (fun tr => tr.messages ⟨7, by decide⟩) (fun tr => tr.messages ⟨4, by decide⟩)

local instance : Fact ((2 : ℕ) ∣ 2) := ⟨dvd_rfl⟩

private abbrev wideOpeningPSpec :=
  Binius.FRIBinius.Executable.openingPSpec (K := K) (κ := 2) (ℓ' := 2) (R := 1) (ϑ := 2)
    basisWord (hIndependent := independentBasis) rateTwo 2

/-- Two polynomial/challenge pairs precede the final scalar in the width-two suffix. -/
private def wideFinalPos : Fin 6 := ⟨4, by decide⟩

private def wideFinalScalar (tr : wideOpeningPSpec.FullTranscript) : L :=
  tr wideFinalPos

/-- Replace only the final scalar in the common Binary BaseFold suffix. -/
private def changeWideFinalScalar (tr : wideOpeningPSpec.FullTranscript) :
    wideOpeningPSpec.FullTranscript :=
  Function.update tr wideFinalPos (wideFinalScalar tr + 1)

/-- Open the same packed polynomial as in the two-block cases, but fold at words 2 and 4
within a single block. The source point is off the Boolean cube. The batching challenges
are words 2 and 4; the modular relocation challenges are words 3 and 5. The two query
repetitions use domain indices 0 and 7. -/
private def observeWide {n : ℕ} {prefixSpec : ProtocolSpec n} {Out WitOut : Type}
    [∀ j, SampleableType ((prefixSpec ++ₚ wideOpeningPSpec).Challenge j)]
    (R : Reduction []ₒ (((Fin 4 → L) × L) × InitialOracles rateTwo 2) (Cube 4 → K)
      Out WitOut (prefixSpec ++ₚ wideOpeningPSpec))
    (verdict : Out → Bool) (relocation : List ℕ) : OpeningObservation :=
  let point : Fin 4 → L := ![fromNat 2, fromNat 4, fromNat 4, fromNat 2]
  let claim := point 0 + point 2 * point 3
  let oracle := firstFamily rateTwo firstTwo false 2
  let badOracle := firstFamily rateTwo firstTwo true 2
  let samples := ([2, 4] ++ relocation ++ [2, 4]).map (15, ·) ++ [(7, 0), (7, 7)]
  observe (wire := prefixSpec ++ₚ wideOpeningPSpec) R verdict
    (((point, claim), oracle), ((point, claim + 1), oracle),
      ((point, claim), badOracle))
    sourceTwo samples
    (fun tr => [(wideFinalScalar tr.snd).toNat])
    (some fun tr => tr.fst ++ₜ changeWideFinalScalar tr.snd)

open Binius.FRIBinius.Executable in
def wideChecks : IO Unit := do
  checkOpening "modular, two folds in one block: reject a changed final scalar" [7]
      (expectTamper := true) fun _ =>
    let R := modularReduction (K := K) (κ := 2) (ℓ' := 2) (R := 1) (ϑ := 2)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateTwo 2 cubeCoords_spec
    observeWide (prefixSpec := ringSwitchPSpec L 2 2) (R.toReduction (Oₛₒ := noOutputOracle))
      Prod.fst [3, 5]
  checkOpening "unrolled, two folds in one block: reject a changed final scalar" [7]
      (expectTamper := true) fun _ =>
    let R := unrolledReduction (K := K) (κ := 2) (ℓ' := 2) (R := 1) (ϑ := 2)
      basisWord (hIndependent := independentBasis) cubeCoords rfl rateTwo 2 cubeCoords_spec
    observeWide (prefixSpec := headPSpec L 2) (R.toReduction (Oₛₒ := noOutputOracle)) Prod.fst []

end BiniusRuntime

def main : IO Unit := do
  BiniusRuntime.fieldChecks
  BiniusRuntime.packingChecks
  BiniusRuntime.encodingChecks
  BiniusRuntime.basefoldChecks
  BiniusRuntime.queryChecks
  BiniusRuntime.openingChecks
  BiniusRuntime.wideChecks
