/-  
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CompPoly.Fold
import ArkLib.Data.GroupTheory.Smooth
import ArkLib.Interaction.Oracle.Core
import ArkLib.Interaction.Oracle.Protocol
import ArkLib.ToMathlib.Finset.Basic
import CompPoly.Fields.Basic

/-!
# FRI Interaction: Core Definitions

This module defines the shared executable shape for the refactored FRI stack.

The key executable choice is that codewords are indexed by canonical `Fin`
positions rather than subtype-valued domain points. Semantic domain elements are
recovered separately through `evalPoint`.
-/

open scoped BigOperators
open Interaction CompPoly CPoly

namespace Fri

namespace OracleLayer

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- The cumulative folding exponent consumed by the first `i` rounds. -/
def prefixShift (i : ℕ) : ℕ :=
  ∑ j ∈ finRangeTo (k + 1) i, (s j).1

/-- The total cumulative folding exponent across all folding rounds. -/
def totalShift : ℕ :=
  ∑ j, (s j).1

/-- The remaining folding exponent before stage `i`. For `i > k + 1`, this
saturates at `0` because `prefixShift` already includes all rounds. -/
def remainingShift (i : ℕ) : ℕ :=
  totalShift s - prefixShift s i

/-- The honest polynomial degree bound before stage `i`. -/
def residualDegreeBound (i : ℕ) : ℕ :=
  2 ^ remainingShift s i * d

/-- The size of the `i`-th executable evaluation domain. -/
def evalSize (i : ℕ) : ℕ :=
  2 ^ (n - prefixShift s i)

/-- Canonical indices for the `i`-th executable evaluation domain. -/
abbrev EvalIdx (i : ℕ) :=
  Fin (evalSize (n := n) s i)

/-- The semantic field point associated to an executable domain index. -/
def evalPoint (i : ℕ) (idx : EvalIdx (n := n) s i) : Fˣ :=
  let _ := D
  let _ := idx
  x

/-- The underlying field element of `evalPoint`. -/
def evalPointVal (i : ℕ) (idx : EvalIdx (n := n) s i) : F :=
  (evalPoint (D := D) (x := x) (s := s) i idx).1

/-- A prover-sent codeword on the `i`-th evaluation domain. -/
abbrev Codeword (_s : Fin (k + 1) → ℕ+) (_n : ℕ) (i : ℕ) : Type :=
  EvalIdx (n := _n) _s i → F

/-- The honest polynomial state before stage `i`. -/
abbrev HonestPoly (i : ℕ) :=
  CDegreeLE F (residualDegreeBound s d i)

/-- The verifier challenges collected across the `k` non-final fold rounds. -/
abbrev FoldChallenges : Type :=
  Fin k → F

/-- Structurally stored non-initial FRI codewords.

`MessageTrace len start finish` stores `len` consecutive prover codeword
messages, starting at round `start` and ending at round `finish`. The endpoint
indices make appending the next codeword a structural operation rather than an
arithmetic cast. -/
inductive MessageTrace (_s : Fin (k + 1) → ℕ+) :
    Nat → Nat → Nat → Type where
  | nil {round : Nat} : MessageTrace _s 0 round round
  | cons {len round finish : Nat} :
      Codeword (F := F) _s n round.succ →
        MessageTrace _s len round.succ finish →
          MessageTrace _s (len + 1) round finish

namespace MessageTrace

/-- Query one codeword in a structurally stored FRI message trace. -/
inductive Query (_s : Fin (k + 1) → ℕ+) :
    Nat → Nat → Nat → Type where
  | here {len round finish : Nat} :
      EvalIdx (n := n) _s round.succ →
        Query _s (len + 1) round finish
  | later {len round finish : Nat} :
      Query _s len round.succ finish →
        Query _s (len + 1) round finish

/-- Append the next codeword to a structurally stored FRI message trace. -/
def snoc (_s : Fin (k + 1) → ℕ+) :
    {len start finish : Nat} →
      MessageTrace (F := F) (n := n) _s len start finish →
        Codeword (F := F) _s n finish.succ →
          MessageTrace (F := F) (n := n) _s (len + 1) start finish.succ
  | 0, _, _, .nil, codeword => .cons codeword .nil
  | _ + 1, _, _, .cons codeword rest, nextCodeword =>
      .cons codeword (snoc _s rest nextCodeword)

/-- Answer a query against a structurally stored FRI message trace. -/
def answer (_s : Fin (k + 1) → ℕ+) :
    {len start finish : Nat} →
      MessageTrace (F := F) (n := n) _s len start finish →
        Query (n := n) _s len start finish → F
  | 0, _, _, .nil, query => nomatch query
  | _ + 1, _, _, .cons codeword _, .here idx => codeword idx
  | _ + 1, _, _, .cons _ rest, .later query => answer _s rest query

end MessageTrace

/-- The full FRI codeword trace: the initial input codeword plus all non-final
fold-round codeword messages. -/
structure FoldCodewordTrace (_s : Fin (k + 1) → ℕ+) where
  initial : Codeword (F := F) _s n 0
  messages : MessageTrace (F := F) (n := n) _s k 0 k

namespace FoldCodewordTrace

/-- Query either the initial codeword or one of the non-final fold codeword
messages in a full FRI codeword trace. -/
abbrev Query (_s : Fin (k + 1) → ℕ+) : Type :=
  EvalIdx (n := n) _s 0 ⊕ MessageTrace.Query (n := n) _s k 0 k

/-- Answer a query against a full FRI codeword trace. -/
def answer (_s : Fin (k + 1) → ℕ+) (trace : FoldCodewordTrace (F := F) (n := n) _s) :
    Query (n := n) _s → F
  | .inl idx => trace.initial idx
  | .inr query => MessageTrace.answer (n := n) _s trace.messages query

end FoldCodewordTrace

/-- The queryable codeword trace emitted by the `k` non-final fold rounds. -/
abbrev FoldCodewordTraceOracleFamily
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) :
    Unit → Type :=
  fun _ => FoldCodewordTrace (F := F) (n := n) _s

instance instOracleInterfaceFoldCodewordTrace (_s : Fin (k + 1) → ℕ+) :
    OracleInterface (FoldCodewordTrace (F := F) (n := n) _s) where
  Query := FoldCodewordTrace.Query (n := n) _s
  toOC.spec := fun _ => F
  toOC.impl query := do
    return FoldCodewordTrace.answer (n := n) _s (← read) query

/-- The plain verifier statement after the final fold: all challenges together
with the final degree-bounded polynomial. -/
abbrev FinalStatement : Type :=
  FoldChallenges (F := F) (k := k) × F × CDegreeLE F d

/-- The single input oracle available to the FRI verifier: the initial codeword. -/
abbrev InputOracleFamily
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) :
    Unit → Type :=
  fun _ => Codeword (F := F) _s n 0

/-- Empty oracle family used by stages that produce no new terminal oracle
statement of their own. -/
abbrev EmptyOracleFamily : PEmpty → Type :=
  PEmpty.elim

instance instOracleInterfaceEmptyOracleFamily :
    ∀ i, OracleInterface (EmptyOracleFamily i) := by
  intro i
  cases i

/-- The cumulative shift after one more folding round. -/
theorem prefixShift_succ (i : Fin (k + 1)) :
    prefixShift s i.1.succ = prefixShift s i.1 + (s i).1 := by
  simpa [prefixShift] using
    (sum_finRangeTo_add_one (n := k) (i := i) (f := fun j => (s j).1))

/-- The current round's cumulative shift still leaves room for the `i`-th fold
arity inside the ambient smoothness bound `n`. -/
theorem prefixShift_le_sub_round
    (h_domain : totalShift s ≤ n) (i : Fin (k + 1)) :
    prefixShift s i.1 ≤ n - (s i).1 := by
  simpa [prefixShift, totalShift] using
    (sum_finRangeTo_le_sub_of_le (n := n) (k := k) (s := s) (i := i) h_domain)

/-- Evaluation-domain sizes are always positive. -/
theorem evalSize_pos (i : ℕ) : 0 < evalSize (n := n) s i := by
  simp [evalSize]

/-- The `i`-th round arity. -/
def roundArity (i : Fin (k + 1)) : ℕ :=
  2 ^ (s i).1

/-- The current round size factors as the next-round size times the round
arity. -/
theorem evalSize_factor
    (h_domain : totalShift s ≤ n) (i : Fin (k + 1)) :
    evalSize (n := n) s i.1 =
      evalSize (n := n) s i.1.succ * roundArity s i := by
  have hRound :
      prefixShift s i.1 ≤ n - (s i).1 :=
    prefixShift_le_sub_round (n := n) (s := s) h_domain i
  have hSi : (s i).1 ≤ totalShift s := by
    refine Finset.single_le_sum (f := fun j => (s j).1) ?_ (Finset.mem_univ i)
    intro j _
    exact Nat.zero_le _
  have hSi_le_n : (s i).1 ≤ n := le_trans hSi h_domain
  have hLe : prefixShift s i.1 + (s i).1 ≤ n :=
    (Nat.le_sub_iff_add_le hSi_le_n).1 hRound
  have hEq :
      n - prefixShift s i.1 =
        n - prefixShift s i.1.succ + (s i).1 := by
    rw [prefixShift_succ (s := s) i]
    have hCancel :
        n - (prefixShift s i.1 + (s i).1) +
          (prefixShift s i.1 + (s i).1) = n :=
      Nat.sub_add_cancel hLe
    have hAux :
        prefixShift s i.1 +
          (n - (prefixShift s i.1 + (s i).1) + (s i).1) = n := by
      simpa [add_assoc, add_left_comm, add_comm] using hCancel
    exact (Nat.eq_sub_of_add_eq' hAux).symm
  rw [evalSize, evalSize, hEq, roundArity, Nat.pow_add, Nat.mul_comm]

/-- Reindex a base-domain point into the `i`-th folded domain by taking the
canonical quotient index. -/
def roundAnchorIdx
    (baseIdx : EvalIdx (n := n) s 0) (i : Fin (k + 1)) :
    EvalIdx (n := n) s i.1 :=
  ⟨baseIdx.1 % evalSize (n := n) s i.1,
    Nat.mod_lt _ (evalSize_pos (n := n) (s := s) i.1)⟩

/-- Reindex a current-round point into the next round by taking the canonical
quotient index. -/
def nextRoundIdx
    (i : Fin (k + 1))
    (idx : EvalIdx (n := n) s i.1) :
    EvalIdx (n := n) s i.1.succ :=
  ⟨idx.1 % evalSize (n := n) s i.1.succ,
    Nat.mod_lt _ (evalSize_pos (n := n) (s := s) i.1.succ)⟩

/-- Enumerate the full fiber over a next-round index. -/
def roundFiberIdx
    (h_domain : totalShift s ≤ n)
    (i : Fin (k + 1))
    (nextIdx : EvalIdx (n := n) s i.1.succ)
    (u : Fin (roundArity s i)) :
    EvalIdx (n := n) s i.1 :=
  ⟨nextIdx.1 + evalSize (n := n) s i.1.succ * u.1,
    by
      have hNext :
          nextIdx.1 < evalSize (n := n) s i.1.succ :=
        nextIdx.2
      have hSum :
          nextIdx.1 + evalSize (n := n) s i.1.succ * u.1 <
            evalSize (n := n) s i.1.succ * roundArity s i := by
        calc
          nextIdx.1 + evalSize (n := n) s i.1.succ * u.1
              < evalSize (n := n) s i.1.succ +
                  evalSize (n := n) s i.1.succ * u.1 :=
            Nat.add_lt_add_right hNext _
          _ = evalSize (n := n) s i.1.succ * (u.1 + 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ evalSize (n := n) s i.1.succ * roundArity s i := by
            exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt u.2)
      simpa [evalSize_factor (n := n) (s := s) h_domain i] using hSum⟩

/-- Decorated oracle protocol for the `i`-th non-final fold round. -/
def foldRoundProtocol
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    Interaction.Oracle.Spec.Protocol :=
  Interaction.Oracle.Spec.Protocol.public .receiver F fun _ =>
    Interaction.Oracle.Spec.Protocol.oracle (Codeword (F := F) _s n i.1.succ)
      Interaction.Oracle.Spec.Protocol.done

/-- The interaction shape of the `i`-th non-final fold round. -/
def foldRoundSpec
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    Interaction.Oracle.Spec :=
  (foldRoundProtocol (F := F) (n := n) _D _x _s i).spec

/-- Role decoration for a non-final fold round. -/
def foldRoundRoles
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    Interaction.Oracle.Spec.RoleDeco (foldRoundSpec (F := F) (n := n) _D _x _s i) :=
  (foldRoundProtocol (F := F) (n := n) _D _x _s i).roles

/-- Oracle decoration for a non-final fold round: only the prover's codeword
message is queryable. -/
def foldRoundOD
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    Interaction.Oracle.Spec.OracleDeco
      (foldRoundSpec (F := F) (n := n) _D _x _s i) :=
  (foldRoundProtocol (F := F) (n := n) _D _x _s i).oracleDeco

/-- Challenge sent by the verifier in a non-final fold round. -/
abbrev foldRoundChallenge
    {_D : Subgroup Fˣ} {_x : Fˣ} {_s : Fin (k + 1) → ℕ+} {i : Fin k}
    (tr : Spec.Transcript (foldRoundSpec (F := F) (n := n) _D _x _s i).toInteractionSpec) :
    F :=
  match tr with
  | ⟨α, _⟩ => α

/-- Codeword sent by the prover in a non-final fold round. -/
abbrev foldRoundCodeword
    {_D : Subgroup Fˣ} {_x : Fˣ} {_s : Fin (k + 1) → ℕ+} {i : Fin k}
    (tr : Spec.Transcript (foldRoundSpec (F := F) (n := n) _D _x _s i).toInteractionSpec) :
    Codeword (F := F) _s n i.1.succ :=
  match tr with
  | ⟨_, ⟨codeword, _⟩⟩ => codeword

/-- Decorated oracle protocol for the terminal fold round. -/
def finalFoldRoundProtocol : Interaction.Oracle.Spec.Protocol :=
  Interaction.Oracle.Spec.Protocol.public .receiver F fun _ =>
    Interaction.Oracle.Spec.Protocol.oracle (CDegreeLE F d)
      Interaction.Oracle.Spec.Protocol.done

/-- The final fold round receives one last challenge and returns the final
degree-bounded polynomial. -/
def finalFoldSpec : Interaction.Oracle.Spec :=
  (finalFoldRoundProtocol (F := F) (d := d)).spec

/-- Role decoration for the final fold round. -/
def finalFoldRoles : Interaction.Oracle.Spec.RoleDeco (finalFoldSpec (F := F) (d := d)) :=
  (finalFoldRoundProtocol (F := F) (d := d)).roles

/-- Oracle decoration for the final fold round: only the final polynomial is
queryable. -/
def finalFoldOD :
    Interaction.Oracle.Spec.OracleDeco (finalFoldSpec (F := F) (d := d)) :=
  (finalFoldRoundProtocol (F := F) (d := d)).oracleDeco

/-- Final-round challenge. -/
abbrev finalFoldChallenge
    (tr : Spec.Transcript (finalFoldSpec (F := F) (d := d)).toInteractionSpec) : F :=
  match tr with
  | ⟨α, _⟩ => α

/-- Final polynomial sent by the prover. -/
abbrev finalFoldPolynomial
    (tr : Spec.Transcript (finalFoldSpec (F := F) (d := d)).toInteractionSpec) :
    CDegreeLE F d :=
  match tr with
  | ⟨_, ⟨finalPoly, _⟩⟩ => finalPoly

/-- Evaluate a computable polynomial on the `i`-th executable FRI domain index. -/
def evalAtIdx (p : CPolynomial F) {i : ℕ} (idx : EvalIdx (n := n) s i) : F :=
  CPolynomial.eval (evalPointVal (D := D) (x := x) (s := s) i idx) p

/-- The honest codeword induced by the honest polynomial state at round `i`. -/
def honestCodeword (i : ℕ) (p : HonestPoly (F := F) (s := s) (d := d) i) :
    Codeword (F := F) s n i :=
  fun idx => evalAtIdx (D := D) (x := x) (s := s) p.1 idx

omit [Finite F] in
/-- Degree bound for honest non-final folding. -/
theorem honestFoldPoly_natDegree_le {i : Fin k}
    (p : HonestPoly (F := F) (s := s) (d := d) i.1)
    (α : F) :
    (CompPoly.CPolynomial.foldNth (2 ^ (s i.castSucc).1) p.1 α).natDegree ≤
      residualDegreeBound s d i.1.succ := by
  refine CompPoly.CPolynomial.foldNth_natDegree_le_of_le _ _ p.1 α ?_
  refine p.2.trans ?_
  have hprefix :
      prefixShift s i.1.succ = prefixShift s i.1 + (s i.castSucc).1 := by
    simpa using prefixShift_succ (s := s) i.castSucc
  have hprefix_total : prefixShift s i.1.succ ≤ totalShift s := by
    rw [prefixShift, totalShift]
    exact Finset.sum_le_univ_sum_of_nonneg (by simp)
  have hremaining :
      remainingShift s i.1 = (s i.castSucc).1 + remainingShift s i.1.succ := by
    unfold remainingShift
    rw [hprefix]
    omega
  rw [residualDegreeBound, hremaining, residualDegreeBound, remainingShift]
  rw [pow_add, mul_assoc]

/-- Honest folding of the current polynomial state. -/
def honestFoldPoly {i : Fin k}
    (p : HonestPoly (F := F) (s := s) (d := d) i.1)
    (α : F) :
    HonestPoly (F := F) (s := s) (d := d) i.1.succ :=
  ⟨CompPoly.CPolynomial.foldNth (2 ^ (s i.castSucc).1) p.1 α,
    honestFoldPoly_natDegree_le (s := s) (d := d) p α⟩

omit [Finite F] in
/-- Honest final folding of the current polynomial state into the terminal
degree-bounded polynomial. -/
theorem honestFinalPolynomial_natDegree_le
    (p : HonestPoly (F := F) (s := s) (d := d) k)
    (α : F) :
    (CompPoly.CPolynomial.foldNth (2 ^ (s (Fin.last k)).1) p.1 α).natDegree ≤ d := by
  refine CompPoly.CPolynomial.foldNth_natDegree_le_of_le _ _ p.1 α ?_
  refine p.2.trans ?_
  have hprefix :
      prefixShift s k.succ = totalShift s := by
    have htake :
        List.take (k + 1) (List.finRange (k + 1)) = List.finRange (k + 1) := by
      exact List.take_of_length_le (by simp)
    simp [prefixShift, totalShift, finRangeTo, htake]
  have hlast :
      prefixShift s k.succ = prefixShift s k + (s (Fin.last k)).1 := by
    simpa using prefixShift_succ (s := s) (Fin.last k)
  have hremaining :
      remainingShift s k = (s (Fin.last k)).1 := by
    unfold remainingShift
    omega
  rw [residualDegreeBound, hremaining]

/-- Honest final folding of the current polynomial state into the terminal
degree-bounded polynomial. -/
def honestFinalPolynomial
    (p : HonestPoly (F := F) (s := s) (d := d) k)
    (α : F) :
    CDegreeLE F d :=
  ⟨CompPoly.CPolynomial.foldNth (2 ^ (s (Fin.last k)).1) p.1 α,
    honestFinalPolynomial_natDegree_le (s := s) (d := d) p α⟩

end

end OracleLayer

end Fri
