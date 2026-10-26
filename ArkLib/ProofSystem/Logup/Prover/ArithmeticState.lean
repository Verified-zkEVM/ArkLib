/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.State
public import ArkLib.ToCompPoly.Multilinear.ArithmeticFold

/-!
# Measured cached denominator, helper, and folded table state

These programs construct the existing private state using certified extension-field requests.
Each original base table is bound once outside its entry loop. Its entries are embedded directly
before the denominator subtraction, without retaining a mapped-value table. Helpers sum individual
weighted total inverses, including at poles. Kernel initialization and table folding explicitly
select the measured fast basis and adjacent-pair programs.

The profiles count extension-field requests only. Base-table visits and embeddings, signed base
weight construction, histogram and natural-number work, allocations, and machine runtime require
separate accounting. No source opening or sparse mathematical polynomial executes in these drivers.
Their deterministic erasures equal the existing reference state APIs; final strategy selection is
a separate consumer obligation.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
namespace Logup.Prover.State
variable {E : Type} [CommRing E] [Inv E] [DecidableEq E] {n T K : Nat}

/-- Accumulate individual weighted inverse terms through a tail-recursive list fold. -/
def helperRowFromProgram (group : List (Fin T))
    (denominator weight : Vector (CMlPolynomialEval E n) T) (u : Fin (2 ^ n)) (acc : E) :
    OracleComp (ArithmeticSpec E) E :=
  group.foldlM (fun sum i => do
    Arithmetic.tick
    let d ← Arithmetic.valueRead (denominator.get i).toArray u.val
    let w ← Arithmetic.valueRead (weight.get i).toArray u.val
    let inv ← Arithmetic.inv d.val
    let term ← Arithmetic.mul w.val inv.val
    let next ← Arithmetic.add sum term.val
    pure next.val) acc

/-- Each occurrence charges its two retained-value reads and arithmetic and control requests. -/
def helperOccurrenceCost (length : Nat) : ArithmeticCost
  | .add | .mul | .inv | .metadata => length
  | .valueRead => 2 * length
  | _ => 0

/-- A partial helper accumulation has the exact termwise value and occurrence profile. -/
theorem profileArithmetic_helperRowFromProgram (group : List (Fin T))
    (denominator weight : Vector (CMlPolynomialEval E n) T) (u : Fin (2 ^ n)) (acc : E) :
    profileArithmetic (helperRowFromProgram group denominator weight u acc) =
      (acc + (group.map fun i => (weight.get i).get u * ((denominator.get i).get u)⁻¹).sum,
        helperOccurrenceCost group.length) := by
  induction group generalizing acc with
  | nil =>
    simp only [helperRowFromProgram, List.foldlM_nil, profileArithmetic_pure, List.map_nil,
      List.sum_nil, add_zero, List.length_nil]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> rfl
  | cons i group ih =>
    simp only [helperRowFromProgram, List.foldlM_cons, profileArithmetic_bind,
      profileArithmetic_tick, profileArithmetic_valueRead, profileArithmetic_inv,
      profileArithmetic_mul, profileArithmetic_add, profileArithmetic_pure]
    rw [show (profileArithmetic (List.foldlM _ _ group)) = _ from ih _]
    apply Prod.ext
    · simp [Vector.get_eq_getElem, u.isLt, add_assoc]
    · funext kind
      cases kind <;> simp [helperOccurrenceCost, arithmeticCost, ArithmeticOp.costKind,
        Nat.mul_add, Nat.add_comm]

/-- Construct one helper entry, charging its initial control step even for an empty group. -/
def helperRowProgram (group : List (Fin T))
    (denominator weight : Vector (CMlPolynomialEval E n) T) (u : Fin (2 ^ n)) :
    OracleComp (ArithmeticSpec E) E := do
  Arithmetic.tick
  helperRowFromProgram group denominator weight u 0

/-- One helper entry charges its occurrences and one initial control step. -/
def helperRowCost (length : Nat) : ArithmeticCost
  | .add | .mul | .inv => length
  | .valueRead => 2 * length
  | .metadata => length + 1
  | _ => 0

/-- Each helper entry equals the total inverse sum with its exact group-length profile. -/
theorem profileArithmetic_helperRowProgram (group : List (Fin T))
    (denominator weight : Vector (CMlPolynomialEval E n) T) (u : Fin (2 ^ n)) :
    profileArithmetic (helperRowProgram group denominator weight u) =
      ((group.map fun i => (weight.get i).get u * ((denominator.get i).get u)⁻¹).sum,
        helperRowCost group.length) := by
  simp only [helperRowProgram, profileArithmetic_bind, profileArithmetic_tick,
    profileArithmetic_helperRowFromProgram, zero_add]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [helperRowCost, helperOccurrenceCost, arithmeticCost,
      ArithmeticOp.costKind, Nat.add_comm]

/-- Construct all helper entries from the cached denominator and weight tables. -/
def helperTablesProgram (groups : Vector (List (Fin T)) K)
    (denominator weight : Vector (CMlPolynomialEval E n) T) :
    OracleComp (ArithmeticSpec E) (Vector (CMlPolynomialEval E n) K) :=
  Vector.ofFnM fun k =>
    let group := groups.get k
    Vector.ofFnM fun u => helperRowProgram group denominator weight u

/-- Sum the actual occurrence-dependent helper profiles over groups and Boolean rows. -/
def helperTablesCost (groups : Vector (List (Fin T)) K) (n : Nat) : ArithmeticCost :=
  fun kind => ∑ k : Fin K, 2 ^ n * helperRowCost (groups.get k).length kind

/-- The measured helper builder constructs precisely the termwise helper tables. -/
theorem profileArithmetic_helperTablesProgram (groups : Vector (List (Fin T)) K)
    (denominator weight : Vector (CMlPolynomialEval E n) T) :
    profileArithmetic (helperTablesProgram groups denominator weight) =
      (Vector.ofFn (fun k => Vector.ofFn fun u =>
        ((groups.get k).map fun i => (weight.get i).get u * ((denominator.get i).get u)⁻¹).sum),
        helperTablesCost groups n) := by
  apply profileArithmetic_ofFnM
  intro k
  apply profileArithmetic_ofFnM_uniform
  intro u
  exact profileArithmetic_helperRowProgram _ _ _ _


/-- Bind each original base table once and subtract each embedded entry from alpha. -/
def denominatorTablesProgram {B : Type} [CommRing B] (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    OracleComp (ArithmeticSpec E) (Vector (CMlPolynomialEval E n) T) :=
  Vector.ofFnM fun i =>
    let original := data (0, i)
    Vector.ofFnM fun u => Subtype.val <$> Arithmetic.sub alpha (f (original.get u))

/-- Denominator construction makes one extension-field subtraction per base entry. -/
theorem profileArithmetic_denominatorTablesProgram {B : Type} [CommRing B]
    (f : B →+* E) (alpha : E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    profileArithmetic (denominatorTablesProgram f alpha data) =
      (Vector.ofFn (fun i => Vector.ofFn fun u => alpha - f ((data (0, i)).get u)),
        fun kind => if kind = .sub then T * 2 ^ n else 0) := by
  unfold denominatorTablesProgram
  rw [profileArithmetic_ofFnM_uniform
    (values := fun i => Vector.ofFn fun u => alpha - f ((data (0, i)).get u))
    (cost := fun kind => 2 ^ n * (if kind = .sub then 1 else 0))]
  · apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> simp
  · intro i
    apply profileArithmetic_ofFnM_uniform
    intro u
    simp only [profileArithmetic_map, profileArithmetic_sub]
    rfl

/-- Initialize the equality-weight cache using the measured fast basis program. -/
def startProgram (prepared : Logup.Prover.Prepared E T K n)
    (z : Fin n → E) (lambda : Fin K → E) :
    OracleComp (ArithmeticSpec E) (Logup.Prover.State E T K n) := do
  let kernel ← CMlPolynomialEval.lagrangeBasisProgram (Vector.ofFn z)
  pure ⟨prepared, kernel, Vector.ofFn lambda⟩

/-- Kernel initialization returns the existing state with its exact fast-basis profile. -/
theorem profileArithmetic_startProgram (prepared : Logup.Prover.Prepared E T K n)
    (z : Fin n → E) (lambda : Fin K → E) :
    profileArithmetic (startProgram prepared z lambda) =
      (start prepared z lambda, CMlPolynomialEval.lagrangeBasisCost n) := by
  simp only [startProgram, profileArithmetic_bind,
    CMlPolynomialEval.profileArithmetic_lagrangeBasisProgram, profileArithmetic_pure, add_zero]
  rw [CMlPolynomialEval.lagrangeBasisFast_eq]
  rfl

/-- Apply the measured adjacent-pair fold to every table in a retained family. -/
def foldTablesProgram {m : Nat} (tables : Vector (CMlPolynomialEval E (n + 1)) m) (r : E) :
    OracleComp (ArithmeticSpec E) (Vector (CMlPolynomialEval E n) m) :=
  Vector.ofFnM fun i => CMlPolynomialEval.evalMleLayerProgram (tables.get i) r

/-- A family fold returns the canonical folded tables and charges each table once. -/
theorem profileArithmetic_foldTablesProgram {m : Nat}
    (tables : Vector (CMlPolynomialEval E (n + 1)) m) (r : E) :
    profileArithmetic (foldTablesProgram tables r) =
      (tables.map (fun table => CMlPolynomialEval.evalMleLayer table r),
        fun kind => m * CMlPolynomialEval.evalMleLayerCost n kind) := by
  have h := profileArithmetic_ofFnM_uniform
    (fun i => CMlPolynomialEval.evalMleLayerProgram (tables.get i) r)
    (fun i => CMlPolynomialEval.evalMleLayer (tables.get i) r)
    (CMlPolynomialEval.evalMleLayerCost n)
    (fun i => CMlPolynomialEval.profileArithmetic_evalMleLayerProgram _ _)
  rw [foldTablesProgram, h]
  apply Prod.ext
  · ext i hi
    simp [Vector.get_eq_getElem]
  · rfl

/-- Fold denominator, weight, helper and kernel tables while retaining batching coefficients. -/
def foldProgram (state : Logup.Prover.State E T K (n + 1)) (r : E) :
    OracleComp (ArithmeticSpec E) (Logup.Prover.State E T K n) := do
  let d ← foldTablesProgram state.denominator r
  let w ← foldTablesProgram state.weight r
  let h ← foldTablesProgram state.helper r
  let kernel ← CMlPolynomialEval.evalMleLayerProgram state.kernel r
  pure ⟨⟨d, w, h⟩, kernel, state.lambda⟩

/-- The actual state fold charges its four retained table families. -/
theorem profileArithmetic_foldProgram (state : Logup.Prover.State E T K (n + 1)) (r : E) :
    profileArithmetic (foldProgram state r) =
      (fold state r, fun kind => (2 * T + K + 1) *
        CMlPolynomialEval.evalMleLayerCost n kind) := by
  simp only [foldProgram, profileArithmetic_bind, profileArithmetic_foldTablesProgram,
    CMlPolynomialEval.profileArithmetic_evalMleLayerProgram, profileArithmetic_pure]
  apply Prod.ext
  · rfl
  · funext kind
    simp [Nat.add_mul, Nat.two_mul, Nat.add_assoc]


/-- Cache denominators and mapped weights, then construct termwise total-inverse helpers. -/
def prepareProgram {B : Type} [CommRing B] (f : B →+* E) (alpha : E)
    (groups : Vector (List (Fin T)) K) (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    OracleComp (ArithmeticSpec E) (Logup.Prover.Prepared E T K n) := do
  let d ← denominatorTablesProgram f alpha data
  let w := Vector.ofFn fun i => Vector.map f (data (1, i))
  let h ← helperTablesProgram groups d w
  pure ⟨d, w, h⟩

/-- Preparation charges denominator subtractions and the actual helper occurrence profile. -/
theorem profileArithmetic_prepareProgram_cost {B : Type} [CommRing B]
    (f : B →+* E) (alpha : E) (groups : Vector (List (Fin T)) K)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    (profileArithmetic (prepareProgram f alpha groups data)).2 =
      (fun kind => if kind = .sub then T * 2 ^ n else 0) + helperTablesCost groups n := by
  simp only [prepareProgram, profileArithmetic_bind, profileArithmetic_denominatorTablesProgram,
    profileArithmetic_helperTablesProgram, profileArithmetic_pure, add_zero]

/-- Measured denominators agree with the existing alpha-minus-embedded-value tables. -/
theorem simulateQ_denominatorTablesProgram {B F : Type} [CommRing B] [Field F] [DecidableEq F]
    (f : B →+* F) (alpha : F) (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    simulateQ arithmeticAnswer (denominatorTablesProgram f alpha data) =
      Logup.Prover.denominatorTables f alpha data := by
  rw [← profileArithmetic_fst, profileArithmetic_denominatorTablesProgram]
  change (Vector.ofFn (fun i => Vector.ofFn fun u => alpha - f ((data (0, i)).get u)) :
    Vector (CMlPolynomialEval F n) T) = Logup.Prover.denominatorTables f alpha data
  ext i hi j hj
  simp [Logup.Prover.denominatorTables, Vector.get_eq_getElem]

/-- Executing the helper program gives the existing termwise total-inverse tables. -/
theorem simulateQ_helperTablesProgram {F : Type} [Field F] [DecidableEq F]
    (groups : Vector (List (Fin T)) K) (d w : Vector (CMlPolynomialEval F n) T) :
    simulateQ arithmeticAnswer (helperTablesProgram groups d w) =
      Logup.Prover.helpers groups d w := by
  rw [← profileArithmetic_fst, profileArithmetic_helperTablesProgram]
  simp [Logup.Prover.helpers, Vector.get_eq_getElem]

/-- Executing preparation gives the existing cached state for every alpha, including poles. -/
theorem simulateQ_prepareProgram {B F : Type} [CommRing B] [Field F] [DecidableEq F] {ell : Nat}
    (f : B →+* F) (alpha : F) (cfg : Logup.Interaction.Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    simulateQ arithmeticAnswer (prepareProgram f alpha cfg.groups data) =
      prepare f alpha cfg data := by
  simp only [prepareProgram, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_denominatorTablesProgram]
  change (⟨Logup.Prover.denominatorTables f alpha data, Logup.Prover.weightTables f data,
    simulateQ arithmeticAnswer (helperTablesProgram cfg.groups
      (Logup.Prover.denominatorTables f alpha data) (Logup.Prover.weightTables f data))⟩ :
    Logup.Prover.Prepared F T (T ⌈/⌉ ell) n) = prepare f alpha cfg data
  rw [simulateQ_helperTablesProgram]
  rfl

/-- Executing the fast kernel initializer gives the existing started state. -/
theorem simulateQ_startProgram (prepared : Logup.Prover.Prepared E T K n)
    (z : Fin n → E) (lambda : Fin K → E) :
    simulateQ arithmeticAnswer (startProgram prepared z lambda) = start prepared z lambda := by
  rw [← profileArithmetic_fst, profileArithmetic_startProgram]

/-- Executing the measured table fold gives the existing folded state. -/
theorem simulateQ_foldProgram (state : Logup.Prover.State E T K (n + 1)) (r : E) :
    simulateQ arithmeticAnswer (foldProgram state r) = fold state r := by
  rw [← profileArithmetic_fst, profileArithmetic_foldProgram]


/-- Closed coordinates retain the actual occurrence count and empty-group control work. -/
theorem helperTablesCost_apply (groups : Vector (List (Fin T)) K) (n : Nat)
    (kind : ArithmeticCostKind) :
    helperTablesCost groups n kind =
      let occurrences := ∑ k : Fin K, (groups.get k).length
      match kind with
      | .add | .mul | .inv => 2 ^ n * occurrences
      | .valueRead => 2 * 2 ^ n * occurrences
      | .metadata => 2 ^ n * (K + occurrences)
      | _ => 0 := by
  cases kind <;>
    simp [helperTablesCost, helperRowCost, Finset.mul_sum, Nat.mul_add,
      Finset.sum_add_distrib, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm]

/-- Each table output charges an addition, difference and product, and two value reads. -/
theorem profileArithmetic_foldProgram_apply (state : Logup.Prover.State E T K (n + 1)) (r : E)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (foldProgram state r)).2 kind =
      if kind = .add ∨ kind = .sub ∨ kind = .mul then (2 * T + K + 1) * 2 ^ n
      else if kind = .valueRead then 2 * (2 * T + K + 1) * 2 ^ n else 0 := by
  rw [profileArithmetic_foldProgram]
  cases kind <;> simp [CMlPolynomialEval.evalMleLayerCost, pow_succ, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

end Logup.Prover.State
