/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Arithmetic.Ledger
public import ArkLib.ProofSystem.Logup.Prover.Arithmetic.RoundCost
import Mathlib.Algebra.Ring.GeomSum

/-!
# Geometric request bounds for the selected honest prover

The bounds follow the actual shared control at an arbitrary typed history of optional public
challenges. They charge the selected preparation, cache initialization, streamed coefficient
messages and nonterminal private folds. Public abort ends the observed execution, the final
round omits its unused private fold, and zero rounds omit cache initialization.

For N=2^n, the full message row sum is N-1 and the retained private-fold output row sum is N-2.
Under positive canonical partition bounds, every ArithmeticCost coordinate of the selected
complete prover is at most 1012*N*T*ell; their sum is at most 9108*N*T*ell. These counts belong
to the actual selected programs,
linked to the same complete argument-carrying Call history as the ordinary Unit interpretation.
They do not price a separate algorithm merely because it has equal outputs.

This envelope concerns private E arithmetic requests and their explicit coefficient/control
markers. Supplying original tables, the 2NT base visits/embeddings, scalar histograms and base
signed-weight construction, tuple compression, public sampling, source openings and dense source
backends, retained messages/storage, allocations and machine implementations are separate ledgers.
An independently profiled preprocessing cost can be retained as an initial annotation.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
namespace Logup.Prover.Honest.Accounting.Resources
variable {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E] {T K ell : Nat}

/-- Suffix rows visited by every native message in a complete n-round execution. -/
def messageRows (n : Nat) : Nat := ∑ r ∈ Finset.range n, 2 ^ r

/-- Output rows of the private folds consumed by subsequent native rounds. -/
def foldedRows (n : Nat) : Nat := ∑ r ∈ Finset.range (n - 1), 2 ^ (r + 1)

/-- Native message rows form the geometric sum N-1, including zero rounds. -/
theorem messageRows_eq (n : Nat) : messageRows n = 2 ^ n - 1 := by
  simpa [messageRows] using Nat.geomSum_eq (m := 2) (by decide) n

/-- Skipping the final unused private fold gives N-2 output rows. -/
theorem foldedRows_eq (n : Nat) : foldedRows n = 2 ^ n - 2 := by
  cases n with
  | zero => simp [foldedRows]
  | succ n =>
    simp only [foldedRows, Nat.add_sub_cancel, pow_succ]
    rw [← Finset.sum_mul]
    change messageRows n * 2 = _
    rw [messageRows_eq]
    have h : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
    omega

/-- A coordinatewise budget for the actual message and nonterminal-fold calls. -/
def nativeBudget (T K ell n : Nat) : Nat :=
  1000 * messageRows n * T * ell + 2 * (2 * T + K + 1) * foldedRows n

private theorem messageWith_cost_le (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (hT : 0 < T) (hell : 0 < ell)
    (hK : K ≤ T) (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    {r : Nat} (state : Logup.Prover.State E T K (r + 1)) (kind : ArithmeticCostKind) :
    (messageWith (costInterpreter (B := B)) cost_erases groups hgroups state).2 kind ≤
      1000 * 2 ^ r * T * ell := by
  rw [messageWith_snd]
  change (profileArithmetic (RoundCoefficients.messageProgram groups state.lambda
    state.denominator state.weight state.helper state.kernel)).2 kind ≤ _
  have h := RoundCoefficients.profileArithmetic_messageProgram_le_of_length_sum groups
    state.lambda state.denominator state.weight state.helper state.kernel ell
    hT hell hK hgroups htotal kind
  split_ifs at h <;> omega

private theorem fold_cost_le {r : Nat} (state : Logup.Prover.State E T K (r + 1))
    (challenge : E) (kind : ArithmeticCostKind) :
    (profileArithmetic (Call.fold (B := B) r state challenge).program).2 kind ≤
      2 * (2 * T + K + 1) * 2 ^ r := by
  change (profileArithmetic (State.foldProgram state challenge)).2 kind ≤ _
  rw [State.profileArithmetic_foldProgram_apply]
  simp only [Nat.mul_assoc]
  split_ifs <;> omega

private theorem nativeBudget_succ_succ (n : Nat) :
    nativeBudget T K ell (n + 2) = nativeBudget T K ell (n + 1) +
      1000 * 2 ^ (n + 1) * T * ell + 2 * (2 * T + K + 1) * 2 ^ (n + 1) := by
  simp [nativeBudget, messageRows, foldedRows, Finset.sum_range_succ]
  ring

/-- Every optional challenge history charges only actual messages and consumed private folds. -/
theorem observed_native_cost_le {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hT : 0 < T) (hell : 0 < ell) (hK : K ≤ T)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (count : Nat) (state : Logup.Prover.State E T K count)
    (choices : Vector (Option E) count) (initial : ArithmeticCost) (kind : ArithmeticCostKind) :
    (observeNative ambient handler count
      (nativeWith (costInterpreter (B := B)) cost_erases (· + ·) ambient groups hgroups
        count state initial) choices).2 kind ≤ initial kind + nativeBudget T K ell count := by
  induction count generalizing initial with
  | zero => simp [observeNative, nativeWith, nativeBudget, messageRows, foldedRows]
  | succ count ih =>
    cases count with
    | zero =>
      rw [observeNative_one]
      have hm := messageWith_cost_le (B := B) groups hgroups hT hell hK htotal state kind
      simpa [nativeBudget, messageRows, foldedRows] using Nat.add_le_add_left hm (initial kind)
    | succ count =>
      rw [observeNative_succ_succ]
      have hm := messageWith_cost_le (B := B) groups hgroups hT hell hK htotal state kind
      cases hc : choices[0] with
      | none =>
        change (initial + (messageWith (costInterpreter (B := B)) cost_erases
          groups hgroups state).2) kind ≤ _
        rw [nativeBudget_succ_succ]
        simp only [Pi.add_apply]
        omega
      | some r =>
        let call := Call.fold (B := B) (count + 1) state r
        let next := costInterpreter call call.program
        have hf := fold_cost_le (B := B) state r kind
        have hi := ih next.1 choices.tail (initial +
          (messageWith (costInterpreter (B := B)) cost_erases groups hgroups state).2 + next.2)
        change (observeNative ambient handler (count + 1)
          (nativeWith (costInterpreter (B := B)) cost_erases (· + ·) ambient groups hgroups
            (count + 1) next.1 (initial +
              (messageWith (costInterpreter (B := B)) cost_erases groups hgroups state).2 + next.2))
          choices.tail).2 kind ≤ _
        rw [nativeBudget_succ_succ]
        dsimp only [next, costInterpreter, call] at hi ⊢
        simp only [Pi.add_apply] at hi
        exact hi.trans (by omega)

/-- Positive partition bounds reduce the native budget to a linear geometric envelope. -/
theorem nativeBudget_le (n : Nat) (hT : 0 < T) (hell : 0 < ell) (hK : K ≤ T) :
    nativeBudget T K ell n ≤ 1008 * 2 ^ n * T * ell := by
  have hC : 2 * T + K + 1 ≤ 4 * T := by omega
  have hM : 1000 * (2 ^ n - 1) * T * ell ≤ 1000 * 2 ^ n * T * ell :=
    Nat.mul_le_mul_right ell (Nat.mul_le_mul_right T
      (Nat.mul_le_mul_left 1000 (Nat.sub_le (2 ^ n) 1)))
  have hF : 2 * (2 * T + K + 1) * (2 ^ n - 2) ≤ 8 * T * 2 ^ n * ell := by
    calc
      _ ≤ 2 * (4 * T) * 2 ^ n :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hC) (Nat.sub_le (2 ^ n) 2)
      _ = 8 * T * 2 ^ n := by ring
      _ ≤ 8 * T * 2 ^ n * ell := Nat.le_mul_of_pos_right _ hell
  rw [nativeBudget, messageRows_eq, foldedRows_eq]
  calc
    _ ≤ 1000 * 2 ^ n * T * ell + 8 * T * 2 ^ n * ell := Nat.add_le_add hM hF
    _ = _ := by ring

/-- Checked grouping supplies positivity and at most one group per column. -/
theorem config_group_bounds {n T ell : Nat} (cfg : Config n T ell) :
    0 < T ∧ 0 < ell ∧ T ⌈/⌉ ell ≤ T := by
  have hsome : (Config.create? n T ell).isSome := by
    unfold Config.create?
    split
    · rename_i h
      rw [cfg.checked] at h
      contradiction
    · rfl
  have hvalid := (Config.isSome_create? n T ell).mp hsome
  refine ⟨hvalid.1, by omega, ?_⟩
  apply (ceilDiv_le_iff_le_mul (by omega : 0 < ell)).mpr
  nlinarith

/-- Exact ordered column coverage gives the occurrence count used by arithmetic profiles. -/
theorem config_total_length {n T ell : Nat} (cfg : Config n T ell) :
    ((List.finRange (T ⌈/⌉ ell)).map fun k => (cfg.groups.get k).length).sum = T := by
  have h := congrArg List.length cfg.flatten_groups
  have hv : cfg.groups.toList = (List.finRange (T ⌈/⌉ ell)).map cfg.groups.get := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [Vector.getElem_toList, List.getElem_map, List.getElem_finRange]
      rfl
  simpa [List.length_flatten, hv, Function.comp_def] using h

/-- Actual denominator and termwise-helper preparation uses at most 2NT requests per axis. -/
theorem prepare_cost_le {n : Nat} (groups : Vector (List (Fin T)) K)
    (hK : K ≤ T)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (f : B →+* E) (alpha : E) (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (State.prepareProgram f alpha groups data)).2 kind ≤ 2 * 2 ^ n * T := by
  have hs : (∑ k : Fin K, (groups.get k).length) = T := by
    simpa only [Fin.sum_univ_def] using htotal
  rw [State.profileArithmetic_prepareProgram_cost, Pi.add_apply,
    State.helperTablesCost_apply, hs]
  have hk := Nat.mul_le_mul_left (2 ^ n) hK
  cases kind <;> simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm T (2 ^ n)] <;> omega

/-- The fast equality cache uses at most 2N requests on every axis. -/
theorem start_cost_le (n : Nat) (kind : ArithmeticCostKind) :
    CMlPolynomialEval.lagrangeBasisCost n kind ≤ 2 * 2 ^ n := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  cases kind <;> simp [CMlPolynomialEval.lagrangeBasisCost, pow_succ] <;> omega


/-- The complete calls recorded by the same actual native control satisfy its budget. -/
theorem observed_native_charges_le {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (hT : 0 < T) (hell : 0 < ell)
    (hK : K ≤ T) (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (count : Nat) (state : Logup.Prover.State E T K count)
    (choices : Vector (Option E) count) (kind : ArithmeticCostKind) :
    charges (observeNative ambient handler count
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
        count state []) choices).2 kind ≤ nativeBudget T K ell count := by
  have h := observed_native_cost_le (B := B) ambient handler groups hgroups hT hell hK htotal
    count state choices (charges ([] : List (Call B E T K))) kind
  rw [native_cost_eq_charges] at h
  simpa only [charges_nil, Pi.zero_apply, zero_add] using h

/-- Actual preparation and optional initialization precede the same budgeted native control. -/
theorem observed_prover_cost_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n)
    (kind : ArithmeticCostKind) :
    (observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) 0 f cfg data ambient)
      alpha joint choices).2.2 kind ≤
      2 * 2 ^ n * T + CMlPolynomialEval.lagrangeBasisCost n kind +
        nativeBudget T (T ⌈/⌉ ell) ell n := by
  obtain ⟨hT, hell, hK⟩ := config_group_bounds cfg
  have ht := config_total_length cfg
  have hp := prepare_cost_le cfg.groups hK ht f alpha data kind
  rw [observeProver_with]
  simp only [zero_add]
  change (observeNative ambient handler n
    (startWith (costInterpreter (B := B)) cost_erases (· + ·) ambient cfg.groups
      cfg.length_group_le n (profileArithmetic (State.prepareProgram f alpha cfg.groups data)).1
      joint.1 joint.2 (profileArithmetic (State.prepareProgram f alpha cfg.groups data)).2)
    choices).2 kind ≤ _
  cases n with
  | zero =>
    change (profileArithmetic (State.prepareProgram f alpha cfg.groups data)).2 kind ≤ _
    cases kind <;> simpa [nativeBudget, messageRows, foldedRows,
      CMlPolynomialEval.lagrangeBasisCost] using hp
  | succ n =>
    let prepared := (profileArithmetic (State.prepareProgram f alpha cfg.groups data)).1
    change (observeNative ambient handler (n + 1)
      (nativeWith (costInterpreter (B := B)) cost_erases (· + ·) ambient cfg.groups
        cfg.length_group_le (n + 1)
        (profileArithmetic (State.startProgram prepared joint.1 joint.2)).1
        ((profileArithmetic (State.prepareProgram f alpha cfg.groups data)).2 +
          (profileArithmetic (State.startProgram prepared joint.1 joint.2)).2)) choices).2 kind ≤ _
    rw [State.profileArithmetic_startProgram]
    have hb := observed_native_cost_le (B := B) ambient handler cfg.groups cfg.length_group_le
      hT hell hK ht (n + 1) (State.start prepared joint.1 joint.2) choices
      ((profileArithmetic (State.prepareProgram f alpha cfg.groups data)).2 +
        CMlPolynomialEval.lagrangeBasisCost (n + 1)) kind
    exact hb.trans (by
      simp only [Pi.add_apply]
      exact Nat.add_le_add_right (Nat.add_le_add_right hp _) _)


/-- Every coordinate of the complete selected prover is bounded by 1012NTell. -/
theorem observed_prover_cost_le_geometric {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n)
    (kind : ArithmeticCostKind) :
    (observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) 0 f cfg data ambient)
      alpha joint choices).2.2 kind ≤ 1012 * 2 ^ n * T * ell := by
  obtain ⟨hT, hell, hK⟩ := config_group_bounds cfg
  have hb := observed_prover_cost_le f cfg data ambient handler alpha joint choices kind
  have hn := nativeBudget_le n hT hell hK
  have hs := start_cost_le n kind
  have he : 2 * 2 ^ n * T ≤ 2 * 2 ^ n * T * ell := Nat.le_mul_of_pos_right _ hell
  have ht : 2 * 2 ^ n ≤ 2 * 2 ^ n * T := Nat.le_mul_of_pos_right _ hT
  have hi := hs.trans (ht.trans he)
  have hsum := Nat.add_le_add (Nat.add_le_add he hi) hn
  apply hb.trans
  calc
    _ ≤ 2 * 2 ^ n * T * ell + 2 * 2 ^ n * T * ell + 1008 * 2 ^ n * T * ell := hsum
    _ = _ := by ring

/-- Exact argument-carrying calls of the complete ordinary control obey the same envelope. -/
theorem observed_prover_charges_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n)
    (kind : ArithmeticCostKind) :
    charges (observeProver ambient handler
      (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
      alpha joint choices).2.2 kind ≤ 1012 * 2 ^ n * T * ell := by
  have h := observed_prover_cost_le_geometric f cfg data ambient handler alpha joint choices kind
  rw [prover_cost_eq_charges] at h
  exact h

/-- Separately profiled preprocessing adds its actual annotation to the weighted envelope. -/
theorem observed_prover_cost_initial_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n)
    (initial : ArithmeticCost) (kind : ArithmeticCostKind) :
    (observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) initial f cfg data ambient)
      alpha joint choices).2.2 kind ≤ initial kind + 1012 * 2 ^ n * T * ell := by
  rw [prover_cost_eq_initial_add_charges]
  exact Nat.add_le_add_left
    (observed_prover_charges_le f cfg data ambient handler alpha joint choices kind) _


/-- Summing all nine primitive-request coordinates gives the explicit total bound 9108NTell. -/
theorem observed_prover_total_cost_le {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n) :
    let cost := (observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) 0 f cfg data ambient)
      alpha joint choices).2.2
    ([ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
      .valueRead, .metadata].map cost).sum ≤ 9108 * 2 ^ n * T * ell := by
  dsimp only
  have h := observed_prover_cost_le_geometric f cfg data ambient handler alpha joint choices
  have ha := h .add
  have hs := h .sub
  have hm := h .mul
  have hi := h .inv
  have he := h .eq
  have hc := h .coefficientRead
  have hn := h .nodeRead
  have hv := h .valueRead
  have ht := h .metadata
  rw [show 9108 * 2 ^ n * T * ell = 9 * (1012 * 2 ^ n * T * ell) by ring]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

end Logup.Prover.Honest.Accounting.Resources
