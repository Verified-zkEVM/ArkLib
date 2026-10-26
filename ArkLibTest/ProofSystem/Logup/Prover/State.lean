/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.State
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Actual honest table state: nonzero cubic Q, retained source, and pole boundary -/

open CompPoly Interaction.Oracle OracleComp OracleSpec Logup.Interaction Logup.Prover
open MvPolynomial

namespace LogupStateTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def cfg : Config 1 2 1 := (Config.create? 1 2 1).get (by decide)
def data (i : Fin 2 × Fin 2) : CMlPolynomialEval F 1 :=
  if i.1 = 0 then #v[0,1] else if i.2 = 0 then #v[1,1] else #v[-1,-1]

def prepared (alpha : F) : Prepared F 2 2 1 := State.prepare (RingHom.id F) alpha cfg data
def initial (alpha : F) : Logup.Prover.State F 2 2 1 :=
  State.start (prepared alpha) (fun _ => 3) (![4,6])
def finalState : Logup.Prover.State F 2 2 0 := State.fold (initial 2) 5

abbrev access := (inputFamily (RingHom.id F) 1 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 1 2).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (inputFamily (RingHom.id F) 1 2) :=
  VirtualOracle.id _
theorem realizes : view.eval impl =
    (inputFamily (RingHom.id F) 1 2).behaviorOfRealizations data := VirtualOracle.eval_id impl

def originalQ (alpha x : F) : F :=
  simulateQ (Access.extendImpl access (helperInterface (E := F) 1 2) impl (prepared alpha).helper)
    (queryQ (RingHom.id F) 1 2 2 cfg.groups alpha (fun _ => 3) (![4,6])
      access view (fun _ => x))

/-- The state view is the exact same formal polynomial as the actual retained source view. -/
theorem source_coherence (alpha : F) :
    State.polynomial cfg.groups (initial alpha) =
      (qPolynomial (RingHom.id F) 1 2 2 cfg.groups alpha (fun _ => 3) (![4,6]) 1
        cfg.length_group_le data (prepared alpha).helper).val :=
  State.polynomial_start_prepare _ _ _ _ _ _

/-- The actual fold has the required formal head-partial semantics. -/
theorem fold_coherence : State.polynomial cfg.groups finalState =
    Polynomial.eval (C (5 : F)) (MvPolynomial.finSuccEquiv F 0
      (State.polynomial cfg.groups (initial 2))) := State.polynomial_fold _ _ _

private theorem table_one (a b : F) :
    State.tableView (n := 1) (#v[a,b] : CMlPolynomialEval F 1) =
      (1 - X 0) * C a + X 0 * C b := by
  have hu : (Finset.univ : Finset (Fin 1 → Fin 2)) = {(fun _ => 0), (fun _ => 1)} := by decide
  have hne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1) := by decide
  have hz : finFunctionFinEquiv (fun _ : Fin 1 => (0 : Fin 2)) = (0 : Fin 2) := by decide
  have ho : finFunctionFinEquiv (fun _ : Fin 1 => (1 : Fin 2)) = (1 : Fin 2) := by decide
  rw [State.tableView, MLE, hu]
  simp [eqPolynomial, hne, Vector.get_eq_getElem, hz, ho]

private theorem vectorTables_ext (xs ys : Vector (CMlPolynomialEval F 1) 2)
    (h : ∀ i u : Fin 2, xs[i.val].get u = ys[i.val].get u) : xs = ys := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro u hu
  exact h ⟨i, hi⟩ ⟨u, hu⟩

/-- Q vanishes on the Boolean row set while remaining a genuine nonzero cubic. -/
theorem honest_cubic : State.polynomial cfg.groups (initial 2) =
    C (2 : F) * X 0 - C (7 : F) * X 0 ^ 2 + C (5 : F) * X 0 ^ 3 := by
  have hd : (initial 2).denominator = #v[#v[2,1],#v[2,1]] := by
    apply vectorTables_ext
    intro i u
    change (denominatorTables (RingHom.id F) 2 data)[i.val].get u = _
    rw [get_denominatorTables]
    fin_cases i <;> fin_cases u <;> decide
  have hw : (initial 2).weight = #v[#v[1,1],#v[-1,-1]] := by
    apply vectorTables_ext
    intro i u
    change (weightTables (RingHom.id F) data)[i.val].get u = _
    rw [get_weightTables]
    fin_cases i <;> fin_cases u <;> decide
  have hh : (initial 2).helper = #v[#v[9,1],#v[-9,-1]] := by
    apply vectorTables_ext
    intro i u
    change (helpers cfg.groups (denominatorTables (RingHom.id F) 2 data)
      (weightTables (RingHom.id F) data))[i.val].get u = _
    simp only [get_helpers, get_denominatorTables, get_weightTables]
    have hg : cfg.groups = #v[[0],[1]] := by decide
    rw [hg]
    have hi : (2 : F)⁻¹ = 9 := inv_eq_of_mul_eq_one_right (by decide)
    fin_cases i <;> fin_cases u <;> norm_num [data, Vector.get_eq_getElem, div_eq_mul_inv, hi]
  have hk : (initial 2).kernel = #v[15,3] := by decide
  have hl : (initial 2).lambda = #v[4,6] := by decide
  have hg : cfg.groups = #v[[0],[1]] := by decide
  change State.polynomial (K := 2) cfg.groups (initial 2) = _
  unfold State.polynomial
  rw [hd, hw, hh, hk, hl, hg]
  simp [Logup.reconstructWithKernel, Logup.groupResidual, Logup.groupFraction,
    table_one, Fin.sum_univ_succ]
  simp only [map_ofNat]
  have h17 : (17 : MvPolynomial (Fin 1) F) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : F → MvPolynomial (Fin 1) F) (show (17 : F) = 0 by decide)
  linear_combination (-30 + 68 * X 0 - 49 * X 0 ^ 2 + 11 * X 0 ^ 3) * h17

open Lean Elab Command

run_cmd do
  unless (prepared 2).denominator == #v[#v[2,1],#v[2,1]] do
    throwError "denominator state initialization changed"
  unless (prepared 2).weight == #v[#v[1,1],#v[-1,-1]] do
    throwError "mapped weight signs changed"
  unless (prepared 2).helper == #v[#v[9,1],#v[8,16]] do
    throwError "termwise helper message changed"
  unless (initial 2).kernel == #v[15,3] do throwError "kernel cache order changed"
  unless finalState.denominator == #v[#v[14],#v[14]] do throwError "denominator fold failed"
  unless finalState.weight == #v[#v[1],#v[-1]] do throwError "weight fold failed"
  unless finalState.helper == #v[#v[3],#v[14]] do throwError "helper fold failed"
  unless finalState.kernel == #v[6] do throwError "kernel fold failed"
  unless finalState.lambda == #v[4,6] do throwError "batch coefficients changed"
  unless originalQ 2 0 == 0 && originalQ 2 1 == 0 && originalQ 2 5 == 1 do
    throwError "nonzero formal Q cannot be reconstructed by interpolating its Boolean zeros"
  unless (prepared 0).helper == #v[#v[0,-1],#v[0,1]] do
    throwError "state initialization changed total-inverse pole behavior"
  unless originalQ 0 0 == 13 && originalQ 0 1 == 0 do
    throwError "pole state lost the actual nonzero initial sum and explicit abort boundary"

run_cmd do
  for name in #[``State.prepare, ``State.start, ``State.fold,
      ``prepared, ``initial, ``finalState, ``originalQ] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing honest state executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``State.polynomial_fold, ``State.polynomial_start_prepare, ``realizes,
      ``source_coherence, ``fold_coherence, ``honest_cubic] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected honest state axiom: {name}"

end LogupStateTest
