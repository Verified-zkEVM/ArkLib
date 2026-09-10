/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectArithmeticMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement
/-!
# Exact direct-coefficient local-phase lowering

The local graph embeds into the existing direct-coefficient machine, and every source step from
an embedded local phase belongs to that graph. Concrete arithmetic traces preserve its branches
and endpoints. Certification of inverse uses the supplied nonsquare parameter only in proofs.
No residual recovery, coefficient-update, lookup or input-materialization execution is claimed.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.DirectArithmeticMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Proof-only coordinate representation of each local phase. -/
def mapPhase {K J : Type*} (f : K → J) : Phase K → Phase J
  | .negate b o => .negate (f b) (f o)
  | .slope b o => .slope (f b) (f o)
  | .test b s => .test (f b) (f s)
  | .invert b s => .invert (f b) (f s)
  | .multiply b v => .multiply (f b) (f v)
  | .emit out => .emit (out.map f)
  | .done out => .done (out.map f)

/-- The exact inclusion into the existing direct-coefficient control graph. -/
def embedPhase {K : Type*} : Phase K → DirectCoefficientMachine.Configuration K
  | .negate b o => .negate b o
  | .slope b o => .slope b o
  | .test b s => .test b s
  | .invert b s => .invert b s
  | .multiply b v => .multiply b v
  | .emit out => .emit out
  | .done out => .done out

/-- The arithmetic-only subgraph, with the same equality branch as the original machine. -/
inductive LocalStep {K : Type*} [Field K] : Phase K → Phase K → Prop where
  | negate {b o} : LocalStep (.negate b o) (.slope (-b) o)
  | slope {b o} : LocalStep (.slope b o) (.test b (o + b))
  | zero {b s} (h : s = 0) : LocalStep (.test b s) (.emit none)
  | nonzero {b s} (h : s ≠ 0) : LocalStep (.test b s) (.invert b s)
  | invert {b s} : LocalStep (.invert b s) (.multiply b s⁻¹)
  | multiply {b v} : LocalStep (.multiply b v) (.emit (some (b * v)))
  | emit {out} : LocalStep (.emit out) (.done out)

/-- Each local rule is an actual original transition, with the original rule's exact charge. -/
theorem LocalStep.source_step {K : Type*} [Field K] {p q : Phase K}
    (h : LocalStep p q) (input : DirectCoefficientMachine.Input K) (w L k : ℕ) :
    ∃ c, DirectCoefficientMachine.Step input w L k (embedPhase p) c (embedPhase q) := by
  cases h with
  | negate => exact ⟨_, .negate⟩
  | slope => exact ⟨_, .slope⟩
  | zero h => exact ⟨_, .zero h⟩
  | nonzero h => exact ⟨_, .nonzero h⟩
  | invert => exact ⟨_, .invert⟩
  | multiply => exact ⟨_, .multiply⟩
  | emit => exact ⟨_, .emit⟩

/-- No original transition starting in this subgraph escapes the represented local phases. -/
theorem source_step_local {K : Type*} [Field K]
    {input : DirectCoefficientMachine.Input K} {w L k : ℕ} (p : Phase K)
    {t : DirectCoefficientMachine.Configuration K} {c : DirectCoefficientMachine.Cost}
    (h : DirectCoefficientMachine.Step input w L k (embedPhase p) c t) :
    ∃ q, LocalStep p q ∧ embedPhase q = t := by
  cases p <;> cases h
  all_goals first
    | exact ⟨_, .negate, rfl⟩
    | exact ⟨_, .slope, rfl⟩
    | exact ⟨_, .zero ‹_›, rfl⟩
    | exact ⟨_, .nonzero ‹_›, rfl⟩
    | exact ⟨_, .invert, rfl⟩
    | exact ⟨_, .multiply, rfl⟩
    | exact ⟨_, .emit, rfl⟩

/-- A finite path contains only the certified local rules. -/
inductive LocalTrace {K : Type*} [Field K] : ℕ → Phase K → Phase K → Prop where
  | nil (p) : LocalTrace 0 p p
  | cons {n p q r} (head : LocalStep p q) (tail : LocalTrace n q r) : LocalTrace (n + 1) p r

/-- Local paths are paths in the original machine; no child-cost assumption is used. -/
theorem LocalTrace.source_trace {K : Type*} [Field K] {n : ℕ} {p q : Phase K}
    (h : LocalTrace n p q) (input : DirectCoefficientMachine.Input K) (w L k : ℕ) :
    ∃ c, DirectCoefficientMachine.Trace input w L k n (embedPhase p) c (embedPhase q) := by
  induction h with
  | nil p => exact ⟨0, .nil _⟩
  | cons head tail ih =>
      obtain ⟨c, hc⟩ := head.source_step input w L k
      obtain ⟨d, hd⟩ := ih
      exact ⟨c + d, .cons hc hd⟩

/-- Proof-only value of the local arithmetic suffix, including its zero-slope rejection. -/
def tailResult {K : Type*} [Field K] [DecidableEq K] (beta one : K) : Option K :=
  if one + -beta = 0 then none else some (-beta * (one + -beta)⁻¹)

/-- The complete suffix follows exactly four rejection or six successful source edges. -/
theorem tail_local_trace {K : Type*} [Field K] [DecidableEq K] (beta one : K) :
    ∃ n ≤ 6, LocalTrace n (.negate beta one) (.done (tailResult beta one)) := by
  by_cases h : one + -beta = 0
  · refine ⟨4, by decide, ?_⟩
    simpa only [tailResult, if_pos h] using
      LocalTrace.cons LocalStep.negate (LocalTrace.cons LocalStep.slope
        (LocalTrace.cons (LocalStep.zero h) (LocalTrace.cons LocalStep.emit (.nil _))))
  · refine ⟨6, le_rfl, ?_⟩
    simpa only [tailResult, if_neg h] using
      LocalTrace.cons LocalStep.negate (LocalTrace.cons LocalStep.slope
        (LocalTrace.cons (LocalStep.nonzero h) (LocalTrace.cons LocalStep.invert
          (LocalTrace.cons LocalStep.multiply (LocalTrace.cons LocalStep.emit (.nil _))))))

variable {F : Type*} [Field F] [DecidableEq F]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Reuse each actual base program edge, including its own ledger and parent wrapper. -/
theorem arithmetic_trace {a : F} (k : Continuation F) {input : ArithmeticMachine.Input F}
    {n : ℕ} {s t : ArithmeticMachine.Configuration F} {c : ArithmeticMachine.Cost}
    (h : ArithmeticMachine.Trace input n s c t) :
    ∃ d, Trace a n (.call k input s) d (.call k input t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a (.call k input s) = some (.call k input u, delegated c) := by
        cases head <;> rfl
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- A selected literal program executes and installs its actual pair or Boolean result. -/
theorem call_returns (a : F) (k : Continuation F) (input : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (r : ArithmeticMachine.Result F) (p : Phase (Pair F))
    (hr : ArithmeticMachine.specification input op = r) (hp : resume k r = some p) :
    ∃ n c, Trace a n (.call k input (.start op)) c (.ready p) ∧ n + c.total ≤ 193 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace input op
  rw [hr] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) k ht
  have hs : step a (.call k input (.done r)) = some (.ready p, returned r) := by
    simp only [step, hp, Option.map_some]
  refine ⟨n + 1, c + returned r, hc.trans (single hs), ?_⟩
  have hb := ArithmeticMachine.cost_total_le op
  have hrb : (returned r).total ≤ 8 := by
    cases r <;> norm_num [returned, Cost.total, ArithmeticMachine.Cost.total]
  rw [total_add, he]
  omega

private theorem prepend {a : F} {p : Phase (Pair F)} {k : Continuation F}
    {input : ArithmeticMachine.Input F} {op : ArithmeticMachine.Operation} {q : Phase (Pair F)}
    {c : Cost} (hs : step a (.ready p) = some (.call k input (.start op), c))
    (hc : c.total ≤ 16)
    (ht : ∃ n d, Trace a n (.call k input (.start op)) d (.ready q) ∧ n + d.total ≤ 193) :
    ∃ n d, Trace a n (.ready p) d (.ready q) ∧ n + d.total ≤ 256 := by
  obtain ⟨n, d, hd, hb⟩ := ht
  refine ⟨n + 1, c + d, .cons hs hd, ?_⟩
  rw [total_add]
  omega

private theorem pair_specification (input : ArithmeticMachine.Input F)
    (op : ArithmeticMachine.Operation) (x : QuadraticAlgebra F input.parameter 0)
    (h : ArithmeticMachine.decodedOutput input.parameter
      (ArithmeticMachine.runFuel input (ArithmeticMachine.fuel op) (.start op)).1 =
        some (.inl x)) : ArithmeticMachine.specification input op = .pair (encode x) := by
  rw [ArithmeticMachine.runFuel_eq] at h
  cases hr : ArithmeticMachine.specification input op with
  | pair p =>
      rw [hr] at h
      have he := congrArg encode (Sum.inl.inj (Option.some.inj h))
      change p = encode x at he
      exact congrArg ArithmeticMachine.Result.pair he
  | boolean b => simp [hr, ArithmeticMachine.decodedOutput] at h

section Certified

variable (a : F) (ha : ¬IsSquare a)

/-- Each local source edge is replaced by the corresponding actual base instruction program. -/
theorem local_step_lowering {p q : Phase (QuadraticAlgebra F a 0)} :
    letI := fieldOfNonsquare a ha
    LocalStep p q → ∃ n c,
      Trace a n (.ready (mapPhase encode p)) c (.ready (mapPhase encode q)) ∧
      n + c.total ≤ 256 := by
  let := fieldOfNonsquare a ha
  intro h
  cases h with
  | negate =>
      rename_i b o
      exact prepend rfl (by decide) (call_returns a (.negate (encode o))
        ⟨a, encode b, encode b⟩ .neg (.pair (encode (-b))) _ rfl rfl)
  | slope =>
      rename_i b o
      exact prepend rfl (by decide) (call_returns a (.slope (encode b))
        ⟨a, encode o, encode b⟩ .add (.pair (encode (o + b))) _ rfl rfl)
  | zero hz =>
      rename_i b s
      subst s
      exact prepend rfl (by decide) (call_returns a (.test (encode b) (encode 0))
        ⟨a, encode 0, (0, 0)⟩ .equal (.boolean true) _
        (by simp [ArithmeticMachine.specification, encode]) rfl)
  | nonzero hz =>
      rename_i b s
      have hr : ArithmeticMachine.specification ⟨a, encode s, (0, 0)⟩ .equal =
          .boolean false := by
        have hs : ¬(s.re = 0 ∧ s.im = 0) := by
          intro hzero
          apply hz
          exact QuadraticAlgebra.ext hzero.1 hzero.2
        by_cases hr : s.re = 0 <;> simp_all [ArithmeticMachine.specification, encode]
      exact prepend rfl (by decide) (call_returns a (.test (encode b) (encode s))
        ⟨a, encode s, (0, 0)⟩ .equal (.boolean false) _ hr rfl)
  | invert =>
      rename_i b s
      have hr := pair_specification (⟨a, encode s, encode s⟩ : ArithmeticMachine.Input F) .inv
        s⁻¹ (ArithmeticMachine.inv_correct ⟨a, encode s, encode s⟩ ha)
      exact prepend rfl (by decide) (call_returns a (.invert (encode b))
        ⟨a, encode s, encode s⟩ .inv (.pair (encode s⁻¹)) _ hr rfl)
  | multiply =>
      rename_i b v
      have hr := pair_specification (⟨a, encode b, encode v⟩ : ArithmeticMachine.Input F) .mul
        (b * v) (ArithmeticMachine.mul_correct ⟨a, encode b, encode v⟩)
      exact prepend rfl (by decide) (call_returns a .multiply
        ⟨a, encode b, encode v⟩ .mul (.pair (encode (b * v))) _ hr rfl)
  | emit => exact ⟨1, emitCost, single rfl, by decide⟩

/-- Lower an exact original transition from any represented local phase. -/
theorem source_step_lowering (input : DirectCoefficientMachine.Input (QuadraticAlgebra F a 0))
    (w L k : ℕ) (p : Phase (QuadraticAlgebra F a 0))
    {t : DirectCoefficientMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : DirectCoefficientMachine.Cost} :
    letI := fieldOfNonsquare a ha
    DirectCoefficientMachine.Step input w L k (embedPhase p) c t → ∃ n d q,
      Trace a n (.ready (mapPhase encode p)) d (.ready (mapPhase encode q)) ∧
      embedPhase q = t ∧ n + d.total ≤ 256 := by
  let := fieldOfNonsquare a ha
  intro h
  obtain ⟨q, hq, he⟩ := source_step_local p h
  obtain ⟨n, d, hd, hb⟩ := local_step_lowering a ha hq
  exact ⟨n, d, q, hd, he, hb⟩

/-- Compose the actual local programs along the original local path. -/
theorem local_trace_lowering {n : ℕ} {p q : Phase (QuadraticAlgebra F a 0)} :
    letI := fieldOfNonsquare a ha
    LocalTrace n p q → ∃ k c,
      Trace a k (.ready (mapPhase encode p)) c (.ready (mapPhase encode q)) ∧
      k + c.total ≤ 256 * n := by
  let := fieldOfNonsquare a ha
  intro h
  induction h with
  | nil p => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := local_step_lowering a ha head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- The whole local suffix executes from actual coordinates and preserves the original branch
and endpoint. Residual recovery and coefficient update are outside this theorem. -/
theorem tail_run_correct (beta one : Pair F)
    (input : DirectCoefficientMachine.Input (QuadraticAlgebra F a 0)) (w L j : ℕ) :
    letI := fieldOfNonsquare a ha
    ∃ n c out m sourceCost,
      runFuel a n (.ready (.negate beta one)) = (.ready (.done out), c) ∧
      out.map (ArithmeticMachine.decode a) =
        tailResult (ArithmeticMachine.decode a beta) (ArithmeticMachine.decode a one) ∧
      DirectCoefficientMachine.Trace input w L j m
        (.negate (ArithmeticMachine.decode a beta) (ArithmeticMachine.decode a one))
        sourceCost (.done (out.map (ArithmeticMachine.decode a))) ∧ n + c.total ≤ 1536 := by
  let := fieldOfNonsquare a ha
  obtain ⟨m, hm, ht⟩ := tail_local_trace
    (ArithmeticMachine.decode a beta) (ArithmeticMachine.decode a one)
  obtain ⟨n, c, hc, hb⟩ := local_trace_lowering a ha ht
  obtain ⟨sourceCost, hs⟩ := ht.source_trace input w L j
  let result := tailResult (ArithmeticMachine.decode a beta) (ArithmeticMachine.decode a one)
  have he : (result.map encode).map (ArithmeticMachine.decode a) = result := by
    cases result <;> rfl
  refine ⟨n, c, result.map encode, m, sourceCost, hc.runFuel_eq, he, ?_, ?_⟩
  · simpa only [he, embedPhase] using hs
  · omega

end Certified

end ReedSolomon.HiddenDerivative.DirectArithmeticMachine
