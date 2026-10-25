/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Initial
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Selected-key compression, actual collisions, and count wrap independent of compression -/

open CompPoly OracleComp Logup.Lookup Logup.Lookup.Tuple
open Lean Elab Command
open scoped ProbabilityTheory ENNReal
namespace LogupTupleInitialTest
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F

def schema : TaggedTuple.Schema F 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 2 := (ProviderLayout.create? 2 2 #[0, 1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 0]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def mu : Vector (CMlPolynomialEval F 1) 2 := #v[#v[0, 0], #v[2, 0]]

theorem false_lookup : ¬ InLanguage prepared.keyData := by unfold InLanguage; decide

def compressedFiber (beta encoded : F) : F :=
  ((Finset.univ : Finset (Fin 1 → Fin 2)).product (Finset.univ : Finset (Fin 3))).sumFiber
    (fun i => (prepared.weightedData f beta mu (0, i.2)).get (finFunctionFinEquiv i.1))
    (fun i => (prepared.weightedData f beta mu (1, i.2)).get (finFunctionFinEquiv i.1)) encoded

/-- There are three semantic keys, giving selected-key error4/17 rather than an all-pairs bound. -/
theorem initial_bound (msg : Vector (CMlPolynomialEval F 1) 2) :
    Pr{let beta ← $ᵗ F}[∀ encoded,
      ((Finset.univ : Finset (Fin 1 → Fin 2)).product (Finset.univ : Finset (Fin 3))).sumFiber
        (fun i => (prepared.weightedData f beta msg (0, i.2)).get (finFunctionFinEquiv i.1))
        (fun i => (prepared.weightedData f beta msg (1, i.2)).get (finFunctionFinEquiv i.1))
        encoded = 0] ≤ (4 : ℝ≥0∞) / 17 := by
  have hcard : prepared.occurringKeys.card = 3 := by decide
  simpa only [hcard, ZMod.card, Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat] using
    prob_weightedData_balanced_le prepared f 17 msg (by decide) false_lookup

theorem nonvacuous_bound : (4 : ℝ≥0∞) / 17 < 1 := by
  simpa only [ENNReal.div_self (a := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (show (4 : ℝ≥0∞) < 17 by norm_num)

/-- The selected-key source theorem quantifies over every fixed pre-beta multiplicity message. -/
theorem semantic_nonzero (msg : Vector (CMlPolynomialEval F 1) 2) :
    ∃ key, ((Finset.univ : Finset (Fin 1 → Fin 2)).product
      (Finset.univ : Finset (Fin 3))).sumFiber
      (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f 0 msg (1, i.2)).get (finFunctionFinEquiv i.1)) key ≠ 0 :=
  exists_semantic_weighted_fiber_ne_zero prepared f 17 msg (by decide) false_lookup

namespace WidthZero

def schema : TaggedTuple.Schema F 2 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0] #v[0, 1]).get (by decide)
def layout : ProviderLayout 2 1 := (ProviderLayout.create? 2 1 #[1]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 0) 2 :=
  #v[#v[⟨0, #v[]⟩], #v[⟨1, #v[]⟩]]
def prepared : PreparedProvider schema layout 0 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
theorem false_lookup : ¬ InLanguage prepared.keyData := by unfold InLanguage; decide

/-- A zero tag and width0 still distinguish the two buses; the compression error is exactly0. -/
theorem zero_bound (msg : Vector (CMlPolynomialEval F 0) 1) :
    Pr{let beta ← $ᵗ F}[∀ encoded,
      ((Finset.univ : Finset (Fin 0 → Fin 2)).product (Finset.univ : Finset (Fin 2))).sumFiber
        (fun i => (prepared.weightedData f beta msg (0, i.2)).get (finFunctionFinEquiv i.1))
        (fun i => (prepared.weightedData f beta msg (1, i.2)).get (finFunctionFinEquiv i.1))
        encoded = 0] ≤ 0 := by
  simpa only [Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div] using
    prob_weightedData_balanced_le prepared f 17 msg (by decide) false_lookup
end WidthZero

namespace CountWrap
abbrev F₂ := ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
def f : F₂ →+* F₂ := RingHom.id F₂
def schema : TaggedTuple.Schema F₂ 2 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0] #v[0, 1]).get (by decide)
def layout (owner : Fin 2) : ProviderLayout 2 1 := ⟨#v[owner]⟩
def key (owner : Fin 2) : schema.Key := ⟨owner, Vector.replicate schema.widths[owner.val] 0⟩
def keys (owner : Fin 2) : Vector (CMlPolynomialEval schema.Key 1) 2 :=
  #v[#v[key 0, key 0], #v[key owner, key owner]]
def prepared (owner : Fin 2) : PreparedProvider schema (layout owner) 1 1 :=
  PreparedProvider.prepare schema (layout owner) (keys owner)
    (by intro p r; fin_cases p; fin_cases r <;> rfl)
def indices : Vector (Fin 2) 2 := #v[0, 0]
def zeroMu : Vector (CMlPolynomialEval F₂ 1) 1 :=
  Vector.replicate 1 (Vector.replicate 2 0)

/-- Natural count2 wraps to0, yet a valid histogram remains correct for every beta. -/
theorem honest_every_beta (beta encoded : F₂) :
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product (Finset.univ : Finset (Fin 2))).sumFiber
      (fun i => ((prepared 0).weightedData f beta (multiplicities indices) (0, i.2)).get
        (finFunctionFinEquiv i.1))
      (fun i => ((prepared 0).weightedData f beta (multiplicities indices) (1, i.2)).get
        (finFunctionFinEquiv i.1)) encoded = 0 :=
  (prepared 0).weighted_fiber_multiplicities_eq_zero f indices
    (by intro i; fin_cases i <;> decide) beta encoded

theorem false_lookup : ¬ InLanguage (prepared 1).keyData := by unfold InLanguage; decide

/-- Count wrap can balance a false lookup even though its fingerprints never collide. -/
theorem false_every_beta : ∀ beta encoded : F₂,
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product (Finset.univ : Finset (Fin 2))).sumFiber
      (fun i => ((prepared 1).weightedData f beta zeroMu (0, i.2)).get
        (finFunctionFinEquiv i.1))
      (fun i => ((prepared 1).weightedData f beta zeroMu (1, i.2)).get
        (finFunctionFinEquiv i.1)) encoded = 0 := by
  intro beta encoded
  have h0 : schema.fingerprint f beta (key 0) = 0 := by
    change (0 : F₂) * beta ^ 0 = 0
    simp
  have h1 : schema.fingerprint f beta (key 1) = 1 := by
    change (1 : F₂) * beta ^ 0 = 1
    simp
  have hd : (prepared 1).fingerprintData f beta =
      (fun role => role.elim (fun _ => Vector.replicate 2 0)
        (fun _ => Vector.replicate 2 1) : Data F₂ 1 1 1) := by
    funext role
    cases role with
    | inl q =>
      fin_cases q
      change Vector.map (schema.fingerprint f beta) (Vector.replicate 2 (key 0)) = #v[0, 0]
      rw [Vector.map_replicate, h0]
      rfl
    | inr p =>
      fin_cases p
      change Vector.map (schema.fingerprint f beta) (Vector.replicate 2 (key 1)) = #v[1, 1]
      rw [Vector.map_replicate, h1]
      rfl
  have hcolumns (a : F₂) : columnEntries (n := 1) (fun _ : Fin 1 => Vector.replicate 2 a) =
      Vector.replicate 2 a := by
    apply Vector.ext
    intro i hi
    simp [columnEntries, Vector.get_eq_getElem]
  unfold PreparedProvider.weightedData
  rw [Logup.Lookup.weighted_fiber_eq_sub ((prepared 1).fingerprintData f beta)
    (Vector.map (CMlPolynomialEval.map f) zeroMu) encoded, hd]
  simp only [zeroMu, CMlPolynomialEval.map, Vector.map_replicate,
    Sum.elim_inl, Sum.elim_inr, Vector.getElem_replicate, hcolumns]
  have htwo : (2 : F₂) = 0 := by decide
  by_cases h : encoded = 0 <;>
    simp [h, eq_comm, Finset.sumFiber, hcolumns, htwo]

theorem no_compression_collision : ∀ beta : F₂,
    schema.fingerprint f beta ⟨0, #v[]⟩ ≠ schema.fingerprint f beta ⟨1, #v[]⟩ := by decide
end CountWrap

run_cmd do
  unless prepared.occurringKeys.card == 3 do throwError "original semantic support changed"
  let balanced := (List.finRange 17).filter fun beta =>
    (List.finRange 17).all fun encoded => compressedFiber beta.val encoded.val == 0
  unless balanced.map Fin.val == [0, 1] do
    throwError "actual fixed-mu collisions no longer match the selected-key event"
  unless (multiplicities (B := CountWrap.F₂) (n := 1) (P := 1) CountWrap.indices) ==
      (#v[#v[0, 0]] : Vector (CMlPolynomialEval CountWrap.F₂ 1) 1) do
    throwError "count-wrap histogram fixture did not cast its natural count after construction"

run_cmd do
  for name in #[``PreparedProvider.occurringKeys, ``compressedFiber, ``prepared,
      ``WidthZero.prepared, ``CountWrap.prepared] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing tuple initial finite-support executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PreparedProvider.weightedData_weight_eq,
      ``PreparedProvider.weighted_fiber_eq_fingerprint,
      ``PreparedProvider.weighted_fiber_eq_zero_of_semantic,
      ``PreparedProvider.weighted_fiber_multiplicities_eq_zero,
      ``exists_semantic_weighted_fiber_ne_zero, ``prob_weightedData_balanced_le,
      ``false_lookup, ``initial_bound, ``nonvacuous_bound,
      ``semantic_nonzero, ``WidthZero.false_lookup, ``WidthZero.zero_bound,
      ``CountWrap.honest_every_beta, ``CountWrap.false_lookup, ``CountWrap.false_every_beta,
      ``CountWrap.no_compression_collision] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "tuple initial-relation proof has an unexpected axiom: {name}"
end LogupTupleInitialTest
