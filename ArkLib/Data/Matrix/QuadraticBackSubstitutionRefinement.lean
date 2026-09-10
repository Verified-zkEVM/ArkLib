/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticBackSubstitutionMachine
public import ArkLib.Data.Matrix.QuadraticPivotSolveRefinement
public import ArkLib.Data.Matrix.QuadraticForwardEchelonRefinement

/-!
# Same-execution coordinate back substitution

Pointwise representation preserves complete residual rows, pivot indices, order and suspended
row states. The actual execution solves all echelon equations and preserves supplied free
coordinates; contradictory residuals are detected by base equality instructions. Bounds depend
only on input dimensions. Nonsquareness certifies inverse semantics, never runtime dispatch.
-/

@[expose] public section

namespace Matrix.QuadraticBackSubstitutionMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

abbrev mapRows {K J : Type*} (f : K → J) (rows : List (ForwardEchelonMachine.Row K)) :=
  QuadraticSelectionMachine.mapRows f rows
abbrev mapPivots {K J : Type*} (f : K → J) (ps : List (ForwardEchelonMachine.Pivot K)) :=
  QuadraticForwardEchelonMachine.mapPivots f ps

/-- Preserve all source phases, indices, order, original vectors and partial row states. -/
def mapState {K J : Type*} (f : K → J) :
    BackSubstitutionMachine.Configuration K → BackSubstitutionMachine.Configuration J
  | .check rs ps v => .check (mapRows f rs) (mapPivots f ps) (v.map f)
  | .reverse ps out v => .reverse (mapPivots f ps) (mapPivots f out) (v.map f)
  | .solve ps v => .solve (mapPivots f ps) (v.map f)
  | .row p v ps s => .row (p.1, QuadraticSelectionMachine.mapRow f p.2) (v.map f)
      (mapPivots f ps) (QuadraticPivotSolveMachine.mapState f s)
  | .done v => .done (v.map f)
  | .inconsistent => .inconsistent
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding an encoded state recovers the entire source state. -/
theorem decode_encode_state (a : F)
    (s : BackSubstitutionMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, mapPivots, QuadraticForwardEchelonMachine.mapPivots, mapRows,
    QuadraticSelectionMachine.mapRows, QuadraticSelectionMachine.mapRow, List.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode,
    QuadraticPivotSolveMachine.decode_encode_state]

omit [DecidableEq F] in
/-- Any materialized coordinate phase has its canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : BackSubstitutionMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, mapPivots, QuadraticForwardEchelonMachine.mapPivots, mapRows,
    QuadraticSelectionMachine.mapRows, QuadraticSelectionMachine.mapRow, List.map_map,
    Function.comp_def, encode, ArithmeticMachine.decode,
    QuadraticPivotSolveMachine.encode_decode_state]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every equality instruction retains its cost and adds the driver wrapper. -/
theorem arithmetic_trace {a : F} (rs : List (Row F)) (ps : List (Pivot F)) (v : List (Pair F))
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a n (.checking rs ps v payload s) d (.checking rs ps v payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a (.checking rs ps v payload s) =
          some (.checking rs ps v payload u, delegated c) := by simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- Retained row instructions keep their entire ledger and pay each outer dispatch. -/
theorem row_trace {a : F} {input : QuadraticPivotSolveMachine.Input F} (ps : List (Pivot F))
    {n : ℕ} {s t : QuadraticPivotSolveMachine.Configuration F} {c : Cost}
    (h : QuadraticPivotSolveMachine.Trace input n s c t) :
    ∃ d, Trace a n (.row input ps s) d (.row input ps t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Actual equality checks the full RHS pair, with charged zero and payload initialization. -/
theorem check_lowering (a : F) (r : Row F) (rs : List (Row F)) (ps : List (Pivot F))
    (v : List (Pair F)) (b : Bool)
    (hb : ArithmeticMachine.specification ⟨a, r.2, (0, 0)⟩ .equal = .boolean b) :
    ∃ n c, Trace a n (.ready (.check (r :: rs) ps v)) c (checked rs ps v b).1 ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, r.2, (0, 0)⟩ .equal
  rw [hb] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) rs ps v ht
  have hr : (checked rs ps v b).2.total ≤ 9 := by cases b <;> dsimp [checked] <;> decide
  refine ⟨n + 1 + 1, (launch + zeroSeed) + (c + (checked rs ps v b).2),
    .cons rfl (hc.trans (single rfl)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .equal
  simp only [total_add]
  rw [he]
  change n + 1 + 1 + (11 + ((ArithmeticMachine.cost .equal).total + 3 * n + _)) ≤ 256
  omega

/-- Source steps lower to identical represented states, including failure and partial rows. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : BackSubstitutionMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : BackSubstitutionMachine.Cost}, BackSubstitutionMachine.Step s c t →
      ∃ n d, Trace a n (enter a (mapState encode s)) d (enter a (mapState encode t)) ∧
        n + d.total ≤ 2048 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  have small {s t : Configuration F}
      (h : ∃ n d, Trace a n s d t ∧ n + d.total ≤ 256) :
      ∃ n d, Trace a n s d t ∧ n + d.total ≤ 2048 := by
    obtain ⟨n, d, hd, hb⟩ := h
    exact ⟨n, d, hd, by omega⟩
  cases h with
  | check =>
      apply small
      exact check_lowering a _ _ _ _ true (by
        simp [ArithmeticMachine.specification, QuadraticSelectionMachine.mapRow, encode])
  | @contradiction r rs ps v hx =>
      have hz : ¬(r.2.re = 0 ∧ r.2.im = 0) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      apply small
      apply check_lowering a _ _ _ _ false
      by_cases hr : r.2.re = 0
      · have hi : r.2.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
        simp [ArithmeticMachine.specification, encode, QuadraticSelectionMachine.mapRow, hr, hi]
      · simp [ArithmeticMachine.specification, encode, QuadraticSelectionMachine.mapRow, hr]
  | checkEnd =>
      exact ⟨1, administrative BackSubstitutionMachine.checkEndCost, single rfl, by decide⟩
  | reverse =>
      exact ⟨1, administrative BackSubstitutionMachine.reverseCost + allocation 1,
        single rfl, by decide⟩
  | reverseEnd =>
      exact ⟨1, administrative BackSubstitutionMachine.reverseEndCost, single rfl, by decide⟩
  | call =>
      exact ⟨1, (administrative BackSubstitutionMachine.callCost + allocation 4) + zeroSeed,
        single rfl, by decide⟩
  | inner h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticPivotSolveMachine.step_lowering a ha _ _ _ h
      obtain ⟨d, hd, he⟩ := row_trace (a := a) _ hc
      exact ⟨n, d, hd, by omega⟩
  | returned =>
      exact ⟨1, administrative BackSubstitutionMachine.returnCost, single rfl, by decide⟩
  | failed => exact ⟨1, administrative BackSubstitutionMachine.rejectCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative BackSubstitutionMachine.emitCost, single rfl, by decide⟩

/-- Same-endpoint traces compose without omitting row or arithmetic child work. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : BackSubstitutionMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : BackSubstitutionMachine.Cost}, BackSubstitutionMachine.Trace n s c t →
      ∃ k d, Trace a k (enter a (mapState encode s)) d (enter a (mapState encode t)) ∧
        k + d.total ≤ 2048 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source execution lowers to the exact represented endpoint. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a) (fuel : ℕ)
    (s : BackSubstitutionMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a k (enter a (mapState encode s)) =
      (enter a (mapState encode (BackSubstitutionMachine.runFuel fuel s).1), d) ∧
      k + d.total ≤ 2048 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := BackSubstitutionMachine.runFuel_refines fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate states reach the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (ha : ¬IsSquare a) (fuel : ℕ)
    (s : BackSubstitutionMachine.Configuration (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k d t, runFuel a k (enter a s) = (enter a t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (BackSubstitutionMachine.runFuel fuel (mapState (ArithmeticMachine.decode a) s)).1 ∧
      k + d.total ≤ 2048 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨k, d, he, hb⟩ := run_lowering a ha fuel (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩


/-- Consistent echelon data executes to a full solution with every supplied free coordinate
retained. The work bound depends only on vector length and input row counts. -/
theorem evaluation_correct (a : F) (ha : ¬IsSquare a) (n : ℕ)
    (ps : List (Pivot F)) (rs : List (Row F)) (v : List (Pair F)) :
    letI := fieldOfNonsquare a ha
    ForwardEchelonMachine.Echelon n 0 (mapPivots (ArithmeticMachine.decode a) ps)
      (mapRows (ArithmeticMachine.decode a) rs) → v.length = n →
    (∀ r ∈ rs, r.2 = (0, 0)) →
    ∃ k c out, runFuel a k (.ready (.check rs ps v)) = (.ready (.done out), c) ∧
      out.length = n ∧
      ForwardEchelonMachine.Solutions (mapPivots (ArithmeticMachine.decode a) ps)
        (mapRows (ArithmeticMachine.decode a) rs)
        (fun i => (out.map (ArithmeticMachine.decode a)).getD i 0) ∧
      BackSubstitutionMachine.FreePreserved (mapPivots (ArithmeticMachine.decode a) ps)
        (v.map (ArithmeticMachine.decode a)) (out.map (ArithmeticMachine.decode a)) ∧
      k + c.total ≤ 2048 * BackSubstitutionMachine.budget n ps.length rs.length := by
  let := fieldOfNonsquare a ha
  intro he hv hz
  have hzero : ∀ r ∈ mapRows (ArithmeticMachine.decode a) rs, r.2 = 0 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    change ArithmeticMachine.decode a r'.2 = 0
    rw [hz r' hr']
    rfl
  obtain ⟨out, sourceCost, hs, hlen, hsol, hfree, _⟩ :=
    BackSubstitutionMachine.evaluation_runFuel n (mapPivots (ArithmeticMachine.decode a) ps)
      (mapRows (ArithmeticMachine.decode a) rs) (v.map (ArithmeticMachine.decode a)) he
      (by simpa using hv) hzero
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha
    (BackSubstitutionMachine.budget n (mapPivots (ArithmeticMachine.decode a) ps).length
      (mapRows (ArithmeticMachine.decode a) rs).length)
    (.check (mapRows (ArithmeticMachine.decode a) rs) (mapPivots (ArithmeticMachine.decode a) ps)
      (v.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hin := encode_decode_state a (.check rs ps v)
  change mapState encode (.check (mapRows (ArithmeticMachine.decode a) rs)
    (mapPivots (ArithmeticMachine.decode a) ps) (v.map (ArithmeticMachine.decode a))) = _ at hin
  rw [hin] at hr
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, out.map encode, hr, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · simpa only [hout] using hsol
  · simpa only [hout] using hfree
  · simpa [mapPivots, QuadraticForwardEchelonMachine.mapPivots,
      mapRows, QuadraticSelectionMachine.mapRows] using hb

/-- An actual nonzero retained residual RHS causes inconsistency before any row solve. -/
theorem inconsistent_correct (a : F) (ha : ¬IsSquare a) (n : ℕ)
    (ps : List (Pivot F)) (rs : List (Row F)) (v : List (Pair F))
    (hbad : ∃ r ∈ rs, r.2 ≠ (0, 0)) :
    ∃ k c, runFuel a k (.ready (.check rs ps v)) = (.ready .inconsistent, c) ∧
      k + c.total ≤ 2048 * BackSubstitutionMachine.budget n ps.length rs.length := by
  let := fieldOfNonsquare a ha
  have hsource : ∃ r ∈ mapRows (ArithmeticMachine.decode a) rs, r.2 ≠ 0 := by
    obtain ⟨r, hr, hb⟩ := hbad
    refine ⟨QuadraticSelectionMachine.mapRow (ArithmeticMachine.decode a) r,
      List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    intro hz
    apply hb
    have h := congrArg encode hz
    simpa [QuadraticSelectionMachine.mapRow, encode, ArithmeticMachine.decode] using h
  obtain ⟨sourceCost, hs, _⟩ := BackSubstitutionMachine.inconsistent_runFuel n
    (mapPivots (ArithmeticMachine.decode a) ps) (mapRows (ArithmeticMachine.decode a) rs)
    (v.map (ArithmeticMachine.decode a)) hsource
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha
    (BackSubstitutionMachine.budget n (mapPivots (ArithmeticMachine.decode a) ps).length
      (mapRows (ArithmeticMachine.decode a) rs).length)
    (.check (mapRows (ArithmeticMachine.decode a) rs) (mapPivots (ArithmeticMachine.decode a) ps)
      (v.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hin := encode_decode_state a (.check rs ps v)
  change mapState encode (.check (mapRows (ArithmeticMachine.decode a) rs)
    (mapPivots (ArithmeticMachine.decode a) ps) (v.map (ArithmeticMachine.decode a))) = _ at hin
  rw [hin] at hr
  refine ⟨k, c, hr, ?_⟩
  simpa [mapPivots, QuadraticForwardEchelonMachine.mapPivots,
    mapRows, QuadraticSelectionMachine.mapRows] using hb

end Matrix.QuadraticBackSubstitutionMachine
