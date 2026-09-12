/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.Candidates
public import ArkLib.Data.QuadraticAlgebra.FiniteWitness
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Euler-criterion center parameters and short quadratic prefixes

The parameter search tests successive prime-field residues using Euler's criterion. It does
not scan possible square roots, allocate a prime-field alphabet, or allocate the quadratic
alphabet. The quadratic prefix allocates exactly the requested number of coordinate pairs.
The caller must choose the prime-field branch when it already supplies enough centers; a
shared decoder field packet and its dispatch remain separate integration obligations.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Scan consecutive indices, stopping at the first accepted index. -/
def firstPassing? (test : ℕ → Bool) (start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 => if test start then some start else firstPassing? test (start + 1) fuel

private theorem firstPassing?_sound (test : ℕ → Bool) (fuel start value : ℕ)
    (h : firstPassing? test start fuel = some value) : test value = true := by
  induction fuel generalizing start with
  | zero => simp [firstPassing?] at h
  | succ fuel ih =>
    cases ht : test start with
    | false => exact ih (start + 1) (by simpa [firstPassing?, ht] using h)
    | true =>
      have hv : start = value := by simpa [firstPassing?, ht] using h
      simpa [← hv] using ht

private theorem firstPassing?_ne_none (test : ℕ → Bool) (fuel start value : ℕ)
    (hlo : start ≤ value) (hhi : value < start + fuel) (ht : test value = true) :
    firstPassing? test start fuel ≠ none := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    cases hs : test start with
    | true => simp [firstPassing?, hs]
    | false =>
      have hne : start ≠ value := by intro he; subst value; simp [hs] at ht
      simpa [firstPassing?, hs] using ih (start + 1) (by omega) (by omega)

/-- Euler test for a nonzero nonsquare residue. -/
def eulerNonsquareTest (p : ℕ) (a : ZMod p) : Bool :=
  decide (a ≠ 0 ∧ a ^ (p / 2) ≠ 1)

/-- The computed Euler test is exactly nonsquareness over a prime field. -/
theorem eulerNonsquareTest_iff (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    eulerNonsquareTest p a = true ↔ ¬IsSquare a := by
  rw [eulerNonsquareTest, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hp⟩ hs
    exact hp ((ZMod.euler_criterion p ha).mp hs)
  · intro hs
    have ha : a ≠ 0 := by rintro rfl; exact hs ⟨0, by simp⟩
    exact ⟨ha, fun hp => hs ((ZMod.euler_criterion p ha).mpr hp)⟩

/-- Search at most `p` residues by Euler tests. Failure remains explicit, including at `p=2`. -/
def nonsquareParameter? (p : ℕ) : Option (ZMod p) :=
  (firstPassing? (fun i => eulerNonsquareTest p (i : ZMod p)) 0 p).map Nat.cast

/-- Any parameter returned by the actual scan certifies quadratic-field arithmetic. -/
theorem nonsquareParameter?_sound (p : ℕ) [Fact p.Prime] {a : ZMod p}
    (h : nonsquareParameter? p = some a) : ¬IsSquare a := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (eulerNonsquareTest_iff p _).mp (firstPassing?_sound _ p 0 i hi)

/-- The bounded scan succeeds for every odd supplied prime. -/
theorem nonsquareParameter?_ne_none (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) :
    nonsquareParameter? p ≠ none := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hodd)
  have ht : eulerNonsquareTest p (a.val : ZMod p) = true := by
    rw [ZMod.natCast_zmod_val]
    exact (eulerNonsquareTest_iff p a).mpr ha
  have hn := firstPassing?_ne_none (fun i => eulerNonsquareTest p (i : ZMod p)) p 0
    a.val (Nat.zero_le _) (by simpa using a.val_lt) ht
  simpa [nonsquareParameter?] using hn

/-- Execute the parameter search and attach its proof-erased nonsquare certificate.
No value is extracted from the existence theorem: the unsuccessful match is unreachable. -/
def certifiedNonsquare (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) :
    {a : ZMod p // ¬IsSquare a} :=
  match h : nonsquareParameter? p with
  | some a => ⟨a, nonsquareParameter?_sound p h⟩
  | none => False.elim (nonsquareParameter?_ne_none p hodd h)

/-- The certified parameter is the value returned by the executed Euler scan. -/
theorem certifiedNonsquare_execution (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) :
    nonsquareParameter? p = some (certifiedNonsquare p hodd).val := by
  unfold certifiedNonsquare
  split
  · assumption
  · contradiction

/-- A short quadratic prefix, with the low radix digit in the real coordinate. The parameter
is arbitrary here; nonsquareness is needed only when using the resulting algebra as a field. -/
def quadraticPrefix (p : ℕ) (a : ZMod p) (count : ℕ) :
    List (QuadraticAlgebra (ZMod p) a 0) :=
  (List.range count).map fun i => ⟨(i % p : ℕ), (i / p : ℕ)⟩

@[simp] theorem length_quadraticPrefix (p : ℕ) (a : ZMod p) (count : ℕ) :
    (quadraticPrefix p a count).length = count := by simp [quadraticPrefix]

/-- Every requested prefix within the quadratic cardinality bound is duplicate-free. -/
theorem nodup_quadraticPrefix (p : ℕ) [Fact p.Prime] (a : ZMod p) (count : ℕ)
    (hcount : count ≤ p ^ 2) : (quadraticPrefix p a count).Nodup := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [quadraticPrefix, List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj he
  have hi' : i < p * p := by simpa [pow_two] using lt_of_lt_of_le (List.mem_range.mp hi) hcount
  have hj' : j < p * p := by simpa [pow_two] using lt_of_lt_of_le (List.mem_range.mp hj) hcount
  have hre := congrArg QuadraticAlgebra.re he
  have him := congrArg QuadraticAlgebra.im he
  have hmod : i % p = j % p :=
    CharP.natCast_injOn_Iio (ZMod p) p (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hre
  have hdiv : i / p = j / p :=
    CharP.natCast_injOn_Iio (ZMod p) p ((Nat.div_lt_iff_lt_mul hp).mpr hi')
      ((Nat.div_lt_iff_lt_mul hp).mpr hj') him
  calc
    i = i % p + p * (i / p) := (Nat.mod_add_div i p).symm
    _ = j % p + p * (j / p) := by rw [hmod, hdiv]
    _ = j := Nat.mod_add_div j p

end ArkLib.FiniteField.ExplicitConstruction
