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

/-- Mapping a result preserves each actual request and response in the ordered log. -/
theorem withQueryLog_map {ι A B : Type} {spec : OracleSpec ι}
    (program : OracleComp spec A) (f : A → B) :
    (f <$> program).withQueryLog =
      (fun result => (f result.1, result.2)) <$> program.withQueryLog := by
  simp [map_eq_bind_pure_comp, withQueryLog_bind]

private theorem log_length_bind {ι A B : Type} {spec : OracleSpec ι}
    (first : OracleComp spec A) (next : A → OracleComp spec B) (c d : Nat)
    (hfirst : ∀ result ∈ support first.withQueryLog, result.2.length = c)
    (hnext : ∀ value, ∀ result ∈ support (next value).withQueryLog, result.2.length = d)
    (result : B × QueryLog spec)
    (member : result ∈ support (first >>= next).withQueryLog) : result.2.length = c + d := by
  rw [withQueryLog_bind, mem_support_bind_iff] at member
  obtain ⟨firstLog, hp, member⟩ := member
  rw [support_map] at member
  obtain ⟨tail, ht, rfl⟩ := member
  simp only [Prod.map, List.length_append]
  rw [hfirst firstLog hp, hnext firstLog.1 tail ht]

/-- If each completed entry has log length c, every completed traversal has log length n * c. -/
theorem withQueryLog_ofFnM_const_length {ι A : Type} {spec : OracleSpec ι}
    (sample : OracleComp spec A) (c n : Nat)
    (hsample : ∀ result ∈ support sample.withQueryLog, result.2.length = c)
    (result : Vector A n × QueryLog spec)
    (member : result ∈ support (Vector.ofFnM (fun _ : Fin n => sample)).withQueryLog) :
    result.2.length = n * c := by
  induction n with
  | zero =>
    rw [Vector.ofFnM_zero, withQueryLog_pure, mem_support_pure_iff] at member
    subst result
    simp only [List.length_nil, Nat.zero_mul]
  | succ n ih =>
    rw [Vector.ofFnM_succ'] at member
    have h := log_length_bind sample _ c (n * c) hsample ?_ result member
    · simpa only [Nat.succ_mul, Nat.add_comm] using h
    · intro value tail htail
      have ht := log_length_bind (Vector.ofFnM (fun _ : Fin n => sample)) _ (n * c) 0
        (fun r hr => ih r hr) ?_ tail htail
      · simpa only [Nat.add_zero] using ht
      · intro values out hout
        rw [withQueryLog_pure, mem_support_pure_iff] at hout
        subst out
        rfl

end OracleComp
