/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.QuadraticUpdateMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Same-execution coordinate indexed-update refinement

All cursor states, copied prefixes and failure tags retain their exact representation. Actual
base addition and a separate cell save replace the sole scalar source operation. The same run
preserves physical length and the descending polynomial interpretation at the requested index.
-/

@[expose] public section

namespace Polynomial.QuadraticUpdateMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Pointwise representation preserves the index, prefix, suffix and output tag. -/
def mapState {K J : Type*} (f : K → J) :
    CoefficientUpdateMachine.Configuration K → CoefficientUpdateMachine.Configuration J
  | .start cs j => .start (cs.map f) j
  | .scan j cs rev => .scan j (cs.map f) (rev.map f)
  | .add c cs rev => .add (f c) (cs.map f) (rev.map f)
  | .restore rev out => .restore (rev.map f) (out.map f)
  | .emit out => .emit (out.map (List.map f))
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Decoding an encoded source state recovers it exactly. -/
theorem decode_encode_state (a : F) (s : CoefficientUpdateMachine.Configuration
    (QuadraticAlgebra F a 0)) :
    mapState (ArithmeticMachine.decode a) (mapState encode s) = s := by
  cases s <;> simp [mapState, List.map_map, Option.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Materialized coordinate states have their canonical decoded representation. -/
theorem encode_decode_state (a : F) (s : CoefficientUpdateMachine.Configuration (Pair F)) :
    mapState encode (mapState (ArithmeticMachine.decode a) s) = s := by
  cases s <;> simp [mapState, List.map_map, Option.map_map, Function.comp_def,
    encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Actual arithmetic instructions retain their operand record and full ledger. -/
theorem arithmetic_trace {a : F} {gamma : Pair F} (cs rev : List (Pair F))
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a gamma n (.call cs rev payload s) d (.call cs rev payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- Base addition executes before its emitted pair is saved into a materialized cell. -/
theorem add_lowering (a : F) (gamma value : QuadraticAlgebra F a 0) (cs rev : List (Pair F)) :
    ∃ n c, Trace a (encode gamma) n (.ready (.add (encode value) cs rev)) c
      (.ready (.restore rev (encode (value + gamma) :: cs))) ∧ n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, encode value, encode gamma⟩ .add
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (gamma := encode gamma) cs rev ht
  have hs : step a (encode gamma)
      (.call cs rev ⟨a, encode value, encode gamma⟩
        (.done (ArithmeticMachine.specification ⟨a, encode value, encode gamma⟩ .add))) =
      some (.save (encode (value + gamma)) cs rev, returned) := rfl
  refine ⟨1 + (n + (1 + 1)), launch + (c + (returned +
      (administrative CoefficientUpdateMachine.addCost + allocation))),
    (single rfl).trans (hc.trans ((single hs).trans (single rfl))), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .add
  simp only [total_add, he]
  change 1 + (n + (1 + 1)) + (7 + ((ArithmeticMachine.cost .add).total + 3 * n + (4 + 7))) ≤ _
  omega

/-- Every source update edge lowers to identical coordinates and bounded actual work. -/
theorem step_lowering {a : F} {gamma : QuadraticAlgebra F a 0}
    {s t : CoefficientUpdateMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : CoefficientUpdateMachine.Cost} (h : CoefficientUpdateMachine.Step gamma s c t) :
    ∃ n d, Trace a (encode gamma) n (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ n + d.total ≤ 256 := by
  cases h with
  | start => exact ⟨1, administrative CoefficientUpdateMachine.startCost, single rfl, by decide⟩
  | reject => exact ⟨1, administrative CoefficientUpdateMachine.rejectCost, single rfl, by decide⟩
  | advance => exact ⟨1, administrative CoefficientUpdateMachine.advanceCost, single rfl, by decide⟩
  | select => exact ⟨1, administrative CoefficientUpdateMachine.selectCost, single rfl, by decide⟩
  | add => exact add_lowering _ _ _ _ _
  | restore => exact ⟨1, administrative CoefficientUpdateMachine.restoreCost, single rfl, by decide⟩
  | finish => exact ⟨1, administrative CoefficientUpdateMachine.finishCost + allocation,
      single rfl, by decide⟩
  | emit => exact ⟨1, administrative CoefficientUpdateMachine.emitCost, single rfl, by decide⟩

/-- Actual source traces compose without changing the supplied increment. -/
theorem trace_lowering {a : F} {gamma : QuadraticAlgebra F a 0} {n : ℕ}
    {s t : CoefficientUpdateMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : CoefficientUpdateMachine.Cost} (h : CoefficientUpdateMachine.Trace gamma n s c t) :
    ∃ k d, Trace a (encode gamma) k (.ready (mapState encode s)) d
      (.ready (mapState encode t)) ∧ k + d.total ≤ 256 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- A finite source run has an exact coordinate endpoint and ledger bound. -/
theorem run_lowering (a : F) (gamma : QuadraticAlgebra F a 0) (fuel : ℕ)
    (s : CoefficientUpdateMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (encode gamma) k (.ready (mapState encode s)) =
      (.ready (mapState encode (CoefficientUpdateMachine.runFuel gamma fuel s).1), d) ∧
      k + d.total ≤ 256 * fuel := by
  obtain ⟨n, hn, ht⟩ := CoefficientUpdateMachine.runFuel_refines gamma fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Any raw partial cursor reaches the same decoded source endpoint, including failure tags. -/
theorem decoded_run_lowering (a : F) (gamma : Pair F) (fuel : ℕ)
    (s : CoefficientUpdateMachine.Configuration (Pair F)) :
    ∃ k d t, runFuel a gamma k (.ready s) = (.ready t, d) ∧
      mapState (ArithmeticMachine.decode a) t =
        (CoefficientUpdateMachine.runFuel (ArithmeticMachine.decode a gamma) fuel
          (mapState (ArithmeticMachine.decode a) s)).1 ∧ k + d.total ≤ 256 * fuel := by
  obtain ⟨k, d, hr, hb⟩ := run_lowering a (ArithmeticMachine.decode a gamma) fuel
    (mapState (ArithmeticMachine.decode a) s)
  rw [encode_decode_state] at hr
  exact ⟨k, d, _, hr, decode_encode_state a _, hb⟩

/-- The actual updated vector retains its physical width and adds the indexed monomial. -/
theorem update_correct (a : F) (gamma : Pair F) (cs : List (Pair F)) (j : ℕ)
    (hj : j < cs.length) :
    ∃ k c out, runFuel a gamma k (.ready (.start cs j)) = (.ready (.done (some out)), c) ∧
      out.length = cs.length ∧ JetHornerMachine.coefficientPolynomial
        (out.map (ArithmeticMachine.decode a)) =
          JetHornerMachine.coefficientPolynomial (cs.map (ArithmeticMachine.decode a)) +
            C (ArithmeticMachine.decode a gamma) * X ^ (cs.length - 1 - j) ∧
      k + c.total ≤ 256 * (2 * cs.length + 5) := by
  obtain ⟨out, hs, hlen, hpoly, _⟩ := CoefficientUpdateMachine.update_runFuel
    (ArithmeticMachine.decode a gamma) j (cs.map (ArithmeticMachine.decode a)) (by simpa using hj)
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (ArithmeticMachine.decode a gamma)
    (2 * (cs.map (ArithmeticMachine.decode a)).length + 5)
    (.start (cs.map (ArithmeticMachine.decode a)) j)
  rw [hs] at hr
  have hcs : (cs.map (ArithmeticMachine.decode a)).map encode = cs := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [mapState, hcs, Option.map_some] at hr
  refine ⟨k, c, out.map encode, hr, ?_, ?_, ?_⟩
  · simpa using hlen
  · simpa only [hout, List.length_map] using hpoly
  · simpa only [List.length_map] using hb

end Polynomial.QuadraticUpdateMachine
