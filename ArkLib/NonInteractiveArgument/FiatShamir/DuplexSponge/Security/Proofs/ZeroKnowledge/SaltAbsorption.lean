/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import
  ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Security.Proofs.ZeroKnowledge.SaltForest
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Actual absorption and salt-forest paths

The executable absorber overwrites only rate coordinates. Its already-written rate prefix,
followed by its remaining input, is therefore the word represented by `SaltForest.AbsorbTrace`.
The execution lemmas below keep a forward query-answer log: only answers actually used during
this execution must belong to the fixed trace. No permutation or forest assumption is needed
for this operational bridge; the forest property is used only afterwards for salt uniqueness.
-/

@[expose] public section

open OracleSpec OracleComp

namespace DuplexSpongeFS.ZeroKnowledge.SaltAbsorption

open CanonicalSpongeState SaltForest

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- The full rate block of a canonical permutation state, viewed as a list. -/
def rateList (state : CanonicalSpongeState U) : List U := (rateSegment state).toList

/-- The rate coordinates already overwritten in the current absorption block. -/
def absorbedPrefix (s : CanonicalDuplexSponge U) : List U :=
  (rateList s.state).take s.absorbPos.val

@[simp] theorem rateList_length (state : CanonicalSpongeState U) :
    (rateList state).length = SpongeSize.R := by
  simp [rateList]

@[simp] theorem rateList_eq_take (state : CanonicalSpongeState U) :
    rateList state = state.toList.take SpongeSize.R := by
  simp only [rateList, rateSegment, takeExact, Vector.toList_cast, Vector.toList_take]

/-- Updating a rate coordinate of the canonical state preserves the entire capacity. -/
theorem capacitySegment_modify_set (state : CanonicalSpongeState U) (i : Nat)
    (hi : i < SpongeSize.R) (x : U) :
    capacitySegment (SpongeState.modify state
      (fun v => v.set i x (hi.trans SpongeSize.R_lt_N))) = capacitySegment state := by
  apply Vector.toList_inj.mp
  change (Vector.drop (state.set i x (hi.trans SpongeSize.R_lt_N))
    SpongeSize.R).toList = (Vector.drop state SpongeSize.R).toList
  rw [Vector.toList_drop, Vector.toList_drop, Vector.toList_set, List.drop_set, ite_eq_left hi]

/-- One rate overwrite appends exactly the newly absorbed unit to the written prefix. -/
theorem rateList_modify_set_take (state : CanonicalSpongeState U) (i : Nat)
    (hi : i < SpongeSize.R) (x : U) :
    (rateList (SpongeState.modify state
      (fun v => v.set i x (hi.trans SpongeSize.R_lt_N)))).take (i + 1) =
      (rateList state).take i ++ [x] := by
  have hn : i < state.toList.length := by simpa using hi.trans SpongeSize.R_lt_N
  change (rateList (state.set i x (hi.trans SpongeSize.R_lt_N))).take (i + 1) =
    (rateList state).take i ++ [x]
  simp only [rateList_eq_take, Vector.toList_set, List.take_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hi), Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [List.take_succ_eq_append_getElem (by simpa using hn),
    List.take_set_of_le (Nat.le_refl i), List.getElem_set_self]

/-- Forget the dependent-query packaging of a forward-only oracle log. -/
def forwardEdges (log : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  log.map fun entry => (entry.1, entry.2)

/-- An actual logged absorption follows an `AbsorbTrace` path, starting with the partially
written block. The fixed trace may contain other edges, repeated edges, or inverse-query edges
normalized to forward orientation; only inclusion of this execution's forward log is required. -/
theorem absorbTrace_of_mem_support_withQueryLog
    (trace : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (s : CanonicalDuplexSponge U) (units : List U)
    {target : CanonicalDuplexSponge U}
    {log : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))}
    (hRun : (target, log) ∈ support (s.absorb units).withQueryLog)
    (hTrace : forwardEdges log ⊆ trace) :
    AbsorbTrace trace capacitySegment rateList (capacitySegment s.state)
      (absorbedPrefix s ++ units) target.state := by
  induction units generalizing s log with
  | nil =>
    simp only [DuplexSponge.absorb, withQueryLog_pure, mem_support_pure_iff,
      Prod.mk.injEq] at hRun
    rcases hRun with ⟨rfl, rfl⟩
    simpa only [absorbedPrefix, List.append_nil] using
      (AbsorbTrace.done (trace := trace) (capacity := capacitySegment)
        (rate := rateList) (List.take_prefix _ _))
  | cons x xs ih =>
    simp only [DuplexSponge.absorb] at hRun
    split at hRun
    · rename_i hFull
      simp only [withQueryLog_bind, mem_support_bind_iff,
        support_map, Set.mem_image] at hRun
      obtain ⟨⟨output, headLog⟩, hQuery, ⟨result, tailLog⟩, hRest, hResult⟩ := hRun
      change (output, headLog) ∈ support
        (liftM (OracleSpec.query s.state) :
          OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) _).withQueryLog at hQuery
      simp only [withQueryLog_query, bind_pure_comp, support_map, Set.mem_image] at hQuery
      obtain ⟨answer, _, hQuery⟩ := hQuery
      cases hQuery
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hResult
      have hEdge : (s.state, output) ∈ trace :=
        hTrace (by simp [forwardEdges])
      have hTail : forwardEdges tailLog ⊆ trace :=
        fun edge hEdge => hTrace (List.mem_cons_of_mem _ hEdge)
      have hPath := ih _ hRest hTail
      have hPos : s.absorbPos.val = SpongeSize.R := hFull
      have hOne : (1 : Fin (SpongeSize.R + 1)).val = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by have := SpongeSize.R_pos; omega)]
      have hZero : 0 < SpongeSize.R := SpongeSize.R_pos
      simp only [absorbedPrefix, hOne, capacitySegment_modify_set _ _ hZero,
        rateList_modify_set_take _ 0 hZero, List.take_zero, List.nil_append,
        List.singleton_append] at hPath
      simpa only [absorbedPrefix, hPos, ← rateList_length s.state,
        List.take_length] using AbsorbTrace.step hEdge hPath
    · rename_i hNotFull
      have hlt : s.absorbPos.val < SpongeSize.R := by
        have hle := s.absorbPos.isLt
        omega
      have hPath := ih _ hRun hTrace
      have hNext : (s.absorbPos + 1).val = s.absorbPos.val + 1 :=
        Fin.val_add_one_of_lt hlt
      simpa only [absorbedPrefix, hNext, capacitySegment_modify_set _ _ hlt,
        rateList_modify_set_take _ _ hlt, List.append_assoc, List.singleton_append] using hPath

end DuplexSpongeFS.ZeroKnowledge.SaltAbsorption
