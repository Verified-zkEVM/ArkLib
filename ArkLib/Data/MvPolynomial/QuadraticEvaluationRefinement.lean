/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Same-execution lowering of sparse evaluation

Pointwise representation maps below are proof-only input relations. Every source transition is
simulated by actual lowered steps; arithmetic blocks reuse the existing literal base programs.
The bound follows from those concrete blocks and their launch/wrapper/return charges. It does not
certify input conversion, enclosing residual/decoder drivers, host execution or bit complexity.
-/

@[expose] public section

namespace MvPolynomial.QuadraticEvaluationMachine

open QuadraticAlgebra

/-- Semantic coordinate representation, not a runtime conversion instruction. -/
def encode {F : Type*} [Zero F] {a : F} (x : QuadraticAlgebra F a 0) : Pair F := (x.re, x.im)

/-- Pointwise state representation shares the unchanged natural-number metadata. -/
def mapState {A B : Type*} (f : A → B) :
    EvaluationMachine.Configuration A → EvaluationMachine.Configuration B
  | .terms ts acc => .terms (ts.map (fun t => (f t.1, t.2))) (f acc)
  | .factors ts acc p fs => .factors (ts.map (fun t => (f t.1, t.2))) (f acc) (f p) fs
  | .lookup ts acc p fs e i xs =>
      .lookup (ts.map (fun t => (f t.1, t.2))) (f acc) (f p) fs e i (xs.map f)
  | .power ts acc p fs x e => .power (ts.map (fun t => (f t.1, t.2))) (f acc) (f p) fs (f x) e
  | .done x => .done (f x)

variable {F : Type*} [Field F] [DecidableEq F]

private theorem single {a : F} {vs : List (Pair F)} {s t : Configuration F} {c : Cost}
    (h : step a vs s = some (t, c)) : Trace a vs 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

omit [DecidableEq F] in
/-- Decoding the pointwise encoding recovers the exact source configuration. -/
theorem decode_encode_state (a : F) (s : EvaluationMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every materialized coordinate state is represented without a hidden basis choice. -/
theorem encode_decode_state (a : F) (s : EvaluationMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := by
  have h := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩
  exact h

/-- Each actual child instruction is lifted with its own parent dispatch and root accesses. -/
theorem arithmetic_trace {a : F} {vs : List (Pair F)} (k : Continuation F)
    {input : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace input n s c t) :
    ∃ d, Trace a vs n (.call k input s) d (.call k input t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, Trace.nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, hc⟩ := ih
      have hs : step a vs (.call k input s) = some (.call k input u, delegated c) := by
        cases head <;> rfl
      refine ⟨delegated c + d, Trace.cons hs hd, ?_⟩
      rw [total_add, delegated_total, hc, base_total_add]
      omega

/-- A concrete arithmetic program returns to its saved continuation with a bounded real trace. -/
theorem call_returns (a : F) (vs : List (Pair F)) (k : Continuation F)
    (input : ArithmeticMachine.Input F) (op : ArithmeticMachine.Operation) (p : Pair F)
    (hp : ArithmeticMachine.specification input op = .pair p) :
    ∃ n c, Trace a vs n (.call k input (.start op)) c (.ready (resume k p)) ∧
      n + c.total ≤ 189 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace input op
  rw [hp] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (vs := vs) k ht
  refine ⟨n + 1, c + returned, hc.trans (single rfl), ?_⟩
  have hb := ArithmeticMachine.cost_total_le op
  rw [total_add, he]
  change n + 1 + (ArithmeticMachine.Cost.total (ArithmeticMachine.cost op) + 3 * n + 4) ≤ 189
  omega

/-- Addition replaces the source arithmetic step by initialization, base instructions and return. -/
theorem add_lowering (a : F) (vs : List (Pair F))
    (ts : List (EvaluationMachine.Term (Pair F))) (x y : QuadraticAlgebra F a 0) :
    ∃ n c, Trace a vs n (.ready (.factors ts (encode x) (encode y) [])) c
      (.ready (.terms ts (encode (x + y)))) ∧ n + c.total ≤ 256 := by
  obtain ⟨n, c, ht, hc⟩ := call_returns a vs (.add ts) ⟨a, encode x, encode y⟩ .add
    (encode (x + y)) rfl
  refine ⟨n + 1, (administrative EvaluationMachine.addCost + launch) + c,
    Trace.cons rfl ht, ?_⟩
  rw [total_add]
  change n + 1 + (12 + c.total) ≤ 256
  omega

/-- Multiplication's result is the same canonical quadratic product as the source step. -/
theorem multiply_lowering (a : F) (vs : List (Pair F))
    (ts : List (EvaluationMachine.Term (Pair F))) (acc : Pair F) (fs : List (ℕ × ℕ))
    (x y : QuadraticAlgebra F a 0) (e : ℕ) :
    ∃ n c, Trace a vs n (.ready (.power ts acc (encode x) fs (encode y) (e + 1))) c
      (.ready (.power ts acc (encode (x * y)) fs (encode y) e)) ∧ n + c.total ≤ 256 := by
  have hp : ArithmeticMachine.specification ⟨a, encode x, encode y⟩ .mul =
      .pair (encode (x * y)) := by
    rw [← mulCoordinates_eq a x y]
    rfl
  obtain ⟨n, c, ht, hc⟩ := call_returns a vs (.multiply ts acc fs (encode y) e)
    ⟨a, encode x, encode y⟩ .mul (encode (x * y)) hp
  refine ⟨n + 1, (administrative EvaluationMachine.multiplyCost + launch) + c,
    Trace.cons rfl ht, ?_⟩
  rw [total_add]
  change n + 1 + (15 + c.total) ≤ 256
  omega

/-- Every original evaluator transition has a concrete base-program simulation. -/
theorem step_lowering {a : F} {vs : List (QuadraticAlgebra F a 0)}
    {s t : EvaluationMachine.Configuration (QuadraticAlgebra F a 0)} {c : EvaluationMachine.Cost}
    (h : EvaluationMachine.Step vs s c t) :
    ∃ n d, Trace a (vs.map encode) n (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ n + d.total ≤ 256 := by
  cases h with
  | add => exact add_lowering _ _ _ _ _
  | multiply => exact multiply_lowering _ _ _ _ _ _ _ _
  | emit => exact ⟨1, administrative EvaluationMachine.emitCost, single rfl,
      by decide⟩
  | term => exact ⟨1, administrative EvaluationMachine.termCost, single rfl,
      by decide⟩
  | factor => exact ⟨1, administrative EvaluationMachine.factorCost, single rfl,
      by decide⟩
  | miss => exact ⟨1, administrative EvaluationMachine.missCost + zeroPair,
      single rfl, by decide⟩
  | hit => exact ⟨1, administrative EvaluationMachine.hitCost, single rfl,
      by decide⟩
  | seek => exact ⟨1, administrative EvaluationMachine.seekCost, single rfl,
      by decide⟩
  | powerDone => exact ⟨1, administrative EvaluationMachine.powerDoneCost,
      single rfl, by decide⟩

/-- Compositional lowering retains the same decoded endpoints, not just a multiplied ledger. -/
theorem trace_lowering {a : F} {vs : List (QuadraticAlgebra F a 0)} {n : ℕ}
    {s t : EvaluationMachine.Configuration (QuadraticAlgebra F a 0)} {c : EvaluationMachine.Cost}
    (h : EvaluationMachine.Trace vs n s c t) :
    ∃ k d, Trace a (vs.map encode) k (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ k + d.total ≤ 256 * n := by
  induction h with
  | nil s => exact ⟨0, 0, Trace.nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨k, d, hd, hb⟩ := step_lowering head
      obtain ⟨j, e, he, hc⟩ := ih
      refine ⟨k + j, d + e, hd.trans he, ?_⟩
      rw [total_add]
      omega

/-- An actual source execution lowers to an actual run with the same represented endpoint. -/
theorem run_lowering (a : F) (vs : List (QuadraticAlgebra F a 0)) (fuel : ℕ)
    (s : EvaluationMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (vs.map encode) k (.ready (mapState encode s)) =
      (.ready (mapState encode (EvaluationMachine.runFuel vs fuel s).1), d) ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨n, hn, ht⟩ := EvaluationMachine.runFuel_refines vs fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Starting from actual coordinate inputs yields exactly the original decoded execution. -/
theorem decoded_run_lowering (a : F) (vs : List (Pair F)) (fuel : ℕ)
    (s : EvaluationMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a vs k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (EvaluationMachine.runFuel (vs.map (ArithmeticMachine.decode a)) fuel
          (mapState (ArithmeticMachine.decode a) s)).1 ∧ k + d.total ≤ 256 * fuel := by
  obtain ⟨k, d, he, hb⟩ := run_lowering a (vs.map (ArithmeticMachine.decode a)) fuel
    (mapState (ArithmeticMachine.decode a) s)
  have hv : (vs.map (ArithmeticMachine.decode a)).map encode = vs := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  rw [hv, encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

end MvPolynomial.QuadraticEvaluationMachine
