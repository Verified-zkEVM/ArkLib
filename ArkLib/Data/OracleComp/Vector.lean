/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import PolyFun.Control.Monad.Hom.Loops
public import Init.Data.Vector.OfFn
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Simulating finite vectors of oracle programs

Simulation preserves the existing standard vector traversal, including effects of the target
handler in their original order. The deterministic specialization gives an ordinary vector,
and its logged specialization concatenates the actual request/response logs in traversal order.
These laws preserve the existing runtime constructors and introduce no sampler.
-/

@[expose] public section

universe u v w

namespace MonadHom

/-- Mapping a vector-producing computation maps every entry computation in its original order. -/
theorem map_vector_ofFnM {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : m →ᵐ n)
    {α : Type u} {k : Nat} (f : Fin k → m α) :
    φ (Vector.ofFnM f) = Vector.ofFnM (fun i => φ (f i)) := by
  induction k with
  | zero => simp only [Vector.ofFnM_zero, φ.mmap_pure]
  | succ k ih =>
    rw [Vector.ofFnM_succ', Vector.ofFnM_succ', φ.mmap_bind]
    congr 1
    funext a
    rw [φ.mmap_bind, ih]
    simp only [φ.mmap_pure]

end MonadHom

open OracleSpec
namespace OracleComp

/-- Simulating a finite vector of programs executes each simulated entry in the target monad. -/
theorem simulateQ_vectorOfFnM {ι α : Type} {spec : OracleSpec ι} {k : Nat}
    {r : Type → Type v} [Monad r] [LawfulMonad r]
    (answer : QueryImpl spec r) (g : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM g) = Vector.ofFnM (fun i => simulateQ answer (g i)) :=
  (simulateQ' answer).map_vector_ofFnM g

/-- Deterministic simulation of a vector traversal is the vector of its simulated values. -/
theorem simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : Nat}
    (answer : QueryImpl spec Id) (g : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM g) = Vector.ofFn (fun i => simulateQ answer (g i)) := by
  rw [simulateQ_vectorOfFnM]
  exact Vector.idRun_ofFnM

/-- Deterministic simulation logs each entry's actual responses and concatenates its queries in
traversal order. Each entry may perform repeated or answer-dependent queries. -/
theorem simulateQ_withQueryLog_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : Nat}
    (answer : QueryImpl spec Id) (programs : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM programs).withQueryLog =
      (Vector.ofFn (fun i => (simulateQ answer (programs i).withQueryLog).1),
        (List.finRange k).flatMap (fun i => (simulateQ answer (programs i).withQueryLog).2)) := by
  induction k with
  | zero =>
    simp only [Vector.ofFnM_zero, withQueryLog_pure, simulateQ_pure]
    rfl
  | succ k ih =>
    rw [Vector.ofFnM_succ']
    simp only [withQueryLog_bind, withQueryLog_pure, simulateQ_bind, simulateQ_pure,
      simulateQ_map]
    rw [ih]
    simp only [List.finRange_succ, Vector.ofFn_succ', List.flatMap_cons, List.flatMap_map]
    change (_, _ ++ (_ ++ [])) = (_, _)
    simp only [List.append_nil, id_eq]

end OracleComp
