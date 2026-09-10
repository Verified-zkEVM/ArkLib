/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.QuadraticJetHornerMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate lowering for Hasse-jet evaluation

Every original source transition is simulated by an actual base-program trace. The two calls of
an update share the retained old head; their emitted sum is explicitly saved into the new list.
The representation maps are proof-only relations on already materialized inputs and states.
-/

@[expose] public section

namespace Polynomial.QuadraticJetHornerMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only pointwise representation of every source control phase. -/
def mapState {K J : Type*} (f : K → J) :
    JetHornerMachine.Configuration K → JetHornerMachine.Configuration J
  | .initialize cs n zs => .initialize (cs.map f) n (zs.map f)
  | .coefficients cs js => .coefficients (cs.map f) (js.map f)
  | .update cs hs rev carry => .update (cs.map f) (hs.map f) (rev.map f) (f carry)
  | .reverse cs pending out => .reverse (cs.map f) (pending.map f) (out.map f)
  | .emit pending out => .emit (pending.map f) (out.map f)
  | .done out => .done (out.map f)

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding encoded source states recovers the exact source state. -/
theorem decode_encode_state (a : F) (s : JetHornerMachine.Configuration (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Every coordinate state has the canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : JetHornerMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Delegate the existing real base trace, preserving its ledger and each wrapper. -/
theorem arithmetic_trace {a : F} {x : Pair F} (k : Continuation F)
    {input : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace input n s c t) :
    ∃ d, Trace a x n (.call k input s) d (.call k input t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a x (.call k input s) = some (.call k input u, delegated c) := by
        cases head <;> rfl
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- Execute a literal program and its concrete continuation handoff. -/
theorem call_returns (a : F) (x : Pair F) (k : Continuation F) (input : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (p : Pair F)
    (hp : ArithmeticMachine.specification input op = .pair p) :
    ∃ n c, Trace a x n (.call k input (.start op)) c (resume a k p) ∧ n + c.total ≤ 197 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace input op
  rw [hp] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (x := x) k ht
  refine ⟨n + 1, c + returnCost k, hc.trans (single rfl), ?_⟩
  have hb := ArithmeticMachine.cost_total_le op
  have hr : (returnCost k).total ≤ 12 := by
    cases k <;> simp only [returnCost, total_add] <;> decide
  rw [total_add, he]
  omega

/-- One original fused update becomes two actual calls and an explicit list-cell allocation. -/
theorem update_lowering (a : F) (x h carry : QuadraticAlgebra F a 0)
    (cs hs rev : List (Pair F)) :
    ∃ n c, Trace a (encode x) n (.ready (.update cs (encode h :: hs) rev (encode carry))) c
      (.ready (.update cs hs (encode (x * h + carry) :: rev) (encode h))) ∧
      n + c.total ≤ 512 := by
  have hm : ArithmeticMachine.specification ⟨a, encode x, encode h⟩ .mul =
      .pair (encode (x * h)) := by rw [← mulCoordinates_eq a x h]; rfl
  obtain ⟨n, c, hc, hb⟩ := call_returns a (encode x)
    (.multiply cs hs rev (encode h) (encode carry)) ⟨a, encode x, encode h⟩ .mul
    (encode (x * h)) hm
  obtain ⟨m, d, hd, he⟩ := call_returns a (encode x) (.add cs hs rev (encode h))
    ⟨a, encode (x * h), encode carry⟩ .add (encode (x * h + carry)) rfl
  have ht := hc.trans (hd.trans (single (show step a (encode x)
    (.save cs hs rev (encode h) (encode (x * h + carry))) = _ from rfl)))
  refine ⟨n + (m + 1) + 1,
    (administrative JetHornerMachine.updateCost + launch) + (c + (d + saveCost)),
    .cons rfl ht, ?_⟩
  simp only [total_add]
  change n + (m + 1) + 1 + (8 + 7 + (c.total + (d.total + 6))) ≤ 512
  omega

/-- Every source rule has a concrete base-instruction simulation with matching endpoint. -/
theorem step_lowering {a : F} {x : QuadraticAlgebra F a 0}
    {s t : JetHornerMachine.Configuration (QuadraticAlgebra F a 0)} {c : JetHornerMachine.Cost}
    (h : JetHornerMachine.Step x s c t) :
    ∃ n d, Trace a (encode x) n (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ n + d.total ≤ 512 := by
  cases h with
  | update => exact update_lowering _ _ _ _ _ _ _
  | init => exact ⟨1, administrative JetHornerMachine.initCost + zeroPair, single rfl, by decide⟩
  | initDone => exact ⟨1, administrative JetHornerMachine.initDoneCost, single rfl, by decide⟩
  | take => exact ⟨1, administrative JetHornerMachine.takeCost, single rfl, by decide⟩
  | updateDone => exact ⟨1, administrative JetHornerMachine.updateDoneCost, single rfl, by decide⟩
  | reverse => exact ⟨1, administrative JetHornerMachine.reverseCost, single rfl, by decide⟩
  | reverseDone => exact ⟨1, administrative JetHornerMachine.reverseDoneCost, single rfl, by decide⟩
  | outputStart => exact ⟨1, administrative JetHornerMachine.outputStartCost, single rfl, by decide⟩
  | output => exact ⟨1, administrative JetHornerMachine.outputCost, single rfl, by decide⟩
  | outputDone => exact ⟨1, administrative JetHornerMachine.outputDoneCost, single rfl, by decide⟩

/-- Compose concrete simulations along the actual original execution. -/
theorem trace_lowering {a : F} {x : QuadraticAlgebra F a 0} {n : ℕ}
    {s t : JetHornerMachine.Configuration (QuadraticAlgebra F a 0)} {c : JetHornerMachine.Cost}
    (h : JetHornerMachine.Trace x n s c t) :
    ∃ k d, Trace a (encode x) k (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ k + d.total ≤ 512 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨k, d, hd, hb⟩ := step_lowering head
      obtain ⟨j, e, he, hc⟩ := ih
      refine ⟨k + j, d + e, hd.trans he, ?_⟩
      rw [total_add]
      omega

/-- An actual source run has an actual lowered execution with its same represented endpoint. -/
theorem run_lowering (a : F) (x : QuadraticAlgebra F a 0) (fuel : ℕ)
    (s : JetHornerMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (encode x) k (.ready (mapState encode s)) =
      (.ready (mapState encode (JetHornerMachine.runFuel x fuel s).1), d) ∧
      k + d.total ≤ 512 * fuel := by
  obtain ⟨n, hn, ht⟩ := JetHornerMachine.runFuel_refines x fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Arbitrary materialized coordinate inputs execute to the exact decoded source endpoint. -/
theorem decoded_run_lowering (a : F) (x : Pair F) (fuel : ℕ)
    (s : JetHornerMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a x k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (JetHornerMachine.runFuel (ArithmeticMachine.decode a x) fuel
          (mapState (ArithmeticMachine.decode a) s)).1 ∧ k + d.total ≤ 512 * fuel := by
  obtain ⟨k, d, he, hb⟩ := run_lowering a (ArithmeticMachine.decode a x) fuel
    (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at he
  exact ⟨k, d, _, he, decode_encode_state a _, hb⟩

/-- Initialization, every coordinate/list allocation, and output traversal belong to the same
run that produces the Hasse jet of the decoded coefficient polynomial. -/
theorem evaluation_correct (a : F) (x : Pair F) (cs : List (Pair F)) (r : ℕ) :
    ∃ k c js, runFuel a x k (.ready (.initialize cs (r + 1) [])) = (.ready (.done js), c) ∧
      js.length = r + 1 ∧
      (∀ j ≤ r, (js.map (ArithmeticMachine.decode a)).getD j 0 =
        (hasseDeriv j (JetHornerMachine.coefficientPolynomial
          (cs.map (ArithmeticMachine.decode a)))).eval (ArithmeticMachine.decode a x)) ∧
      k + c.total ≤ 2560 * (cs.length + 1) * (r + 1) := by
  obtain ⟨js, he, hl, hj⟩ := JetHornerMachine.evaluation_runFuel_spec
    (ArithmeticMachine.decode a x) (cs.map (ArithmeticMachine.decode a)) r
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (ArithmeticMachine.decode a x)
    (((cs.map (ArithmeticMachine.decode a)).length + 1) * (2 * (r + 1) + 3))
    (.initialize (cs.map (ArithmeticMachine.decode a)) (r + 1) [])
  have hcs : (cs.map (ArithmeticMachine.decode a)).map encode = cs := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hjs : (js.map encode).map (ArithmeticMachine.decode a) = js := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [he, mapState, hcs, List.map_nil] at hr
  refine ⟨k, c, js.map encode, hr, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hl
  · simpa only [hjs] using hj
  · simp only [List.length_map] at hb
    calc
      k + c.total ≤ 512 * ((cs.length + 1) * (2 * (r + 1) + 3)) := hb
      _ ≤ 512 * (5 * (cs.length + 1) * (r + 1)) :=
        Nat.mul_le_mul_left _ (JetHornerMachine.evaluationFuel_le cs.length r)
      _ = 2560 * (cs.length + 1) * (r + 1) := by ring

end Polynomial.QuadraticJetHornerMachine
