/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.KoalaBear
import Lean.Compiler.IR

/-! # Actual sampler structure and supported raw-query counts -/

open OracleComp OracleSpec
namespace SamplingTests
abbrev raw : OracleSpec Nat := Nat →ₒ Nat

def branch : OracleComp raw Nat := do
  let first ← liftM (raw.query 0)
  liftM (raw.query (if first = 0 then 1 else 2))

theorem branch_length (result : Nat × QueryLog raw)
    (member : result ∈ support branch.withQueryLog) : result.2.length = 2 := by
  rw [branch, withQueryLog_bind, mem_support_bind_iff] at member
  obtain ⟨first, hfirst, member⟩ := member
  rw [withQueryLog_query, mem_support_bind_iff] at hfirst
  obtain ⟨answer, _, hfirst⟩ := hfirst
  rw [mem_support_pure_iff] at hfirst
  subst first
  rw [support_map] at member
  obtain ⟨last, hlast, rfl⟩ := member
  rw [withQueryLog_query, mem_support_bind_iff] at hlast
  obtain ⟨response, _, hlast⟩ := hlast
  rw [mem_support_pure_iff] at hlast
  subst last
  rfl

theorem branch_vector_length (result : Vector Nat 3 × QueryLog raw)
    (member : result ∈ support (Vector.ofFnM (fun _ : Fin 3 => branch)).withQueryLog) :
    result.2.length = 6 :=
  withQueryLog_ofFnM_const_length branch 2 3 branch_length result member

theorem extension_vector_length (result : Vector KoalaBear.Ext6 2 × QueryLog unifSpec)
    (member : result ∈ support ($ᵗ (Vector KoalaBear.Ext6 2)).withQueryLog) :
    result.2.length = 12 := by
  rw [SampleableType.uniformSample_vector_eq_ofFnM] at member
  exact withQueryLog_ofFnM_const_length ($ᵗ KoalaBear.Ext6) 6 2
    KoalaBear.Ext6.uniformSample_log_length result member

def branchingAnswer : QueryImpl raw (StateM (Nat × List Nat)) := fun q => do
  let state ← get
  set (state.1 + 1, state.2 ++ [q])
  return if q = 0 then state.1 / 2 % 2 else state.1 + q

def branching := (simulateQ branchingAnswer
  (Vector.ofFnM (fun _ : Fin 3 => branch)).withQueryLog).run (0, [])
def mapped := (simulateQ branchingAnswer
  ((fun _ => (0 : Nat)) <$> Vector.ofFnM (fun _ : Fin 3 => branch)).withQueryLog).run (0, [])

def counter : QueryImpl unifSpec (StateM (Nat × List Nat)) := fun bound => do
  let state ← get
  set (state.1 + 1, state.2 ++ [bound])
  return ⟨state.1 % (bound + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def extension : ProbComp KoalaBear.Ext6 := $ᵗ KoalaBear.Ext6
def zeroVector : ProbComp (Vector KoalaBear.Ext6 0) := $ᵗ (Vector KoalaBear.Ext6 0)
def coordinates : ProbComp (Fin 2 → KoalaBear.Ext6) := $ᵗ (Fin 2 → KoalaBear.Ext6)
def joint : ProbComp ((Fin 1 → KoalaBear.Ext6) × (Fin 2 → KoalaBear.Ext6)) :=
  $ᵗ ((Fin 1 → KoalaBear.Ext6) × (Fin 2 → KoalaBear.Ext6))
def limbs (x : KoalaBear.Ext6) : List Nat :=
  ((KoalaBear.Ext6.coeffsEquiv.symm x).toList).map ZMod.val

open Lean Elab Command in
run_cmd do
  unless branching.1.1 == #v[2,5,6] && branching.2 == (6,[0,1,0,2,0,1]) &&
      branching.1.2.map (fun entry => (entry.1, entry.2)) ==
        [(0,0),(1,2),(0,1),(2,5),(0,0),(1,6)] do
    throwError "constant-length traversal lost answer-dependent query order or responses"
  unless mapped.1.1 == 0 && mapped.1.2.map (fun entry => (entry.1, entry.2)) ==
      branching.1.2.map (fun entry => (entry.1, entry.2)) && mapped.2 == branching.2 do
    throwError "mapping every output to zero erased or reordered actual raw queries"
  let observed := (simulateQ counter extension).run (0, [])
  unless limbs observed.1 == [0,1,2,3,4,5] && observed.2.1 == 6 &&
      observed.2.2.all (· == KoalaBear.fieldSize - 1) do
    throwError "selected Ext6 sampler changed its six ordered base-field draws"
  let empty := (simulateQ counter zeroVector).run (7, [])
  unless empty.1 == #v[] && empty.2 == (7,[]) do
    throwError "empty selected coordinate sampler issued a primitive query"
  let coords := (simulateQ counter coordinates).run (0, [])
  unless limbs (coords.1 0) == [0,1,2,3,4,5] &&
      limbs (coords.1 1) == [6,7,8,9,10,11] && coords.2.1 == 12 do
    throwError "selected Fin sampler reversed its coordinate/limb order"
  let paired := (simulateQ counter joint).run (0, [])
  unless limbs (paired.1.1 0) == [0,1,2,3,4,5] &&
      limbs (paired.1.2 0) == [6,7,8,9,10,11] &&
      limbs (paired.1.2 1) == [12,13,14,15,16,17] && paired.2.1 == 18 do
    throwError "selected joint sampler interleaved vectors or reused a coordinate draw"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``OracleComp.withQueryLog_map, ``OracleComp.withQueryLog_ofFnM_const_length,
      ``SampleableType.uniformSample_vector_eq_ofFnM,
      ``SampleableType.uniformSample_pi_fin_eq_ofFnM,
      ``SampleableType.uniformSample_pi_fin_prod_eq_ofFnM,
      ``KoalaBear.Field.uniformSample_log_length,
      ``KoalaBear.Ext6.uniformSample_eq_ofFnM, ``KoalaBear.Ext6.uniformSample_log_length,
      ``branch_length, ``branch_vector_length, ``extension_vector_length] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected canonical sampler/log-length axiom: {name}"
  for name in #[``branch, ``branching, ``mapped, ``extension, ``zeroVector,
      ``coordinates, ``joint, ``limbs] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing selected sampler/response-dependent caller IR: {name}"
  logInfo "canonical samplers: ordered actual draws, all support lengths and n0 passed"
end SamplingTests
