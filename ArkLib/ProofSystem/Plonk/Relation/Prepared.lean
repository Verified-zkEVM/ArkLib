/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Relation.Basic
public import ArkLib.Data.Fin.Basic

/-! # Public inputs and prepared Plonk rows

Public inputs occupy a prefix of the variable assignment. Preparation prepends equality rows
and retains every computational gate. Clearing the constants on these rows separates the
public-input term from the fixed selectors.
-/

@[expose] public section

namespace Plonk

variable {R : Type} {m n ℓ : ℕ}

/-- Combine a public prefix and a private suffix into a full variable assignment. -/
def fullAssignment (hℓ : ℓ ≤ m) (x : Fin ℓ → R) (w : Fin (m - ℓ) → R) : Fin m → R :=
  Fin.append x w ∘ Fin.cast (by omega)

/-- Extract the private suffix of a full variable assignment. -/
def privateWitness (hℓ : ℓ ≤ m) (z : Fin m → R) : Fin (m - ℓ) → R :=
  fun i => z ⟨ℓ + i.val, by omega⟩

@[simp]
theorem fullAssignment_public (hℓ : ℓ ≤ m) (x : Fin ℓ → R)
    (w : Fin (m - ℓ) → R) (i : Fin ℓ) :
    fullAssignment hℓ x w (Fin.castLE hℓ i) = x i := by
  unfold fullAssignment Function.comp
  rw [Fin.append_left_of_lt _ _ (by simp)]
  rfl

@[simp]
theorem privateWitness_fullAssignment (hℓ : ℓ ≤ m) (x : Fin ℓ → R)
    (w : Fin (m - ℓ) → R) : privateWitness hℓ (fullAssignment hℓ x w) = w := by
  funext i
  unfold privateWitness fullAssignment Function.comp
  rw [Fin.append_right_of_not_lt _ _ (by simp)]
  congr 1
  apply Fin.ext
  simp

/-- Recombination recovers every full assignment whose prefix is the public input. -/
theorem fullAssignment_privateWitness (hℓ : ℓ ≤ m) (x : Fin ℓ → R) (z : Fin m → R)
    (hz : ∀ i, z (Fin.castLE hℓ i) = x i) :
    fullAssignment hℓ x (privateWitness hℓ z) = z := by
  funext i
  unfold fullAssignment Function.comp
  change Fin.append x (privateWitness hℓ z) ⟨i.val, _⟩ = z i
  by_cases hi : i.val < ℓ
  · rw [Fin.append_left_of_lt _ _ hi]
    exact (hz ⟨i.val, hi⟩).symm
  · rw [Fin.append_right_of_not_lt _ _ hi]
    unfold privateWitness
    congr 1
    apply Fin.ext
    simp
    omega

variable [CommRing R]

/-- The prefix/private relation uses the combined assignment. -/
theorem relation_iff_accepts_fullAssignment (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (w : Fin (m - ℓ) → R) :
    relation cs ℓ hℓ x w ↔ cs.accepts (fullAssignment hℓ x w) := Iff.rfl

/-- The split relation is the full-variable relation with the public prefix fixed. -/
theorem relation_iff_variableRelation (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (w : Fin (m - ℓ) → R) :
    relation cs ℓ hℓ x w ↔
      cs.variableRelation (Fin.castLEEmb hℓ) x (fullAssignment hℓ x w) := by
  simp [ConstraintSystem.variableRelation, relation_iff_accepts_fullAssignment]

/-- A full witness is equivalent to its private suffix together with the public-prefix equations. -/
theorem variableRelation_iff_privateWitness (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (z : Fin m → R) :
    cs.variableRelation (Fin.castLEEmb hℓ) x z ↔
      (∀ i, z (Fin.castLE hℓ i) = x i) ∧ relation cs ℓ hℓ x (privateWitness hℓ z) := by
  constructor
  · rintro ⟨hg, hx⟩
    refine ⟨hx, ?_⟩
    rw [relation_iff_accepts_fullAssignment, fullAssignment_privateWitness hℓ x z hx]
    exact hg
  · rintro ⟨hx, hg⟩
    rw [relation_iff_accepts_fullAssignment, fullAssignment_privateWitness hℓ x z hx] at hg
    exact ⟨hg, hx⟩

/-- Private and full variable witnesses give the same public-input language. -/
theorem exists_relation_iff_exists_variable (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) :
    (∃ w, relation cs ℓ hℓ x w) ↔ ∃ z, cs.variableRelation (Fin.castLEEmb hℓ) x z := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨fullAssignment hℓ x w, (relation_iff_variableRelation cs hℓ x w).mp hw⟩
  · rintro ⟨z, hz⟩
    exact ⟨privateWitness hℓ z, ((variableRelation_iff_privateWitness cs hℓ x z).mp hz).2⟩

namespace ConstraintSystem

/-- Prepend the public equality rows, keeping all original gates. -/
def prepare (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → R) :
    ConstraintSystem R m (ℓ + n) :=
  Fin.append (fun i => Gate.eq (Fin.castLE hℓ i) (x i)) cs

@[simp]
theorem prepare_public (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (i : Fin ℓ) :
    cs.prepare hℓ x (i.castAdd n) = Gate.eq (Fin.castLE hℓ i) (x i) := by
  exact Fin.append_left _ _ _

@[simp]
theorem prepare_original (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (i : Fin n) : cs.prepare hℓ x (i.natAdd ℓ) = cs i := by
  exact Fin.append_right _ _ _

/-- Preparation produces the reserved public equality rows. -/
theorem prepare_isPreparedFor (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) : (cs.prepare hℓ x).isPreparedFor ℓ (by omega) hℓ := by
  intro i
  exact ⟨x i, prepare_public cs hℓ x i⟩

/-- Prepared satisfaction is exactly original satisfaction with the prescribed public prefix. -/
theorem prepare_accepts_iff (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (z : Fin m → R) :
    (cs.prepare hℓ x).accepts z ↔ cs.accepts z ∧ ∀ i, z (Fin.castLE hℓ i) = x i := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h (i.natAdd ℓ)
    · intro i
      simpa using h (i.castAdd n)
  · rintro ⟨hg, hx⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using hx j
    · intro j
      simpa using hg j

/-- Preparation preserves and reflects the relation for each private witness. -/
theorem prepare_relation_iff (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (w : Fin (m - ℓ) → R) :
    relation (cs.prepare hℓ x) ℓ hℓ x w ↔ relation cs ℓ hℓ x w := by
  simp [relation_iff_accepts_fullAssignment, prepare_accepts_iff]

/-- A satisfying prepared assignment decodes to a satisfying private witness. -/
theorem privateWitness_of_prepare_accepts (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (z : Fin m → R) (hz : (cs.prepare hℓ x).accepts z) :
    relation cs ℓ hℓ x (privateWitness hℓ z) := by
  obtain ⟨hg, hx⟩ := (prepare_accepts_iff cs hℓ x z).mp hz
  rw [relation_iff_accepts_fullAssignment, fullAssignment_privateWitness hℓ x z hx]
  exact hg

/-- Preparing public rows preserves and reflects satisfiability. -/
theorem exists_prepare_accepts_iff (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) :
    (∃ z, (cs.prepare hℓ x).accepts z) ↔ ∃ w, relation cs ℓ hℓ x w := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨privateWitness hℓ z, privateWitness_of_prepare_accepts cs hℓ x z hz⟩
  · rintro ⟨w, hw⟩
    refine ⟨fullAssignment hℓ x w, (prepare_accepts_iff cs hℓ x _).mpr ⟨hw, ?_⟩⟩
    exact fullAssignment_public hℓ x w

/-- The left occurrence in each prepended public equality row. -/
def preparedPublicOccurrence (n : ℕ) (i : Fin ℓ) : Fin (3 * (ℓ + n)) :=
  finProdFinEquiv ((0 : Fin 3), i.castAdd n)

@[simp]
theorem wireAt_preparedPublicOccurrence (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (i : Fin ℓ) :
    (cs.prepare hℓ x).wireAt (preparedPublicOccurrence n i) = Fin.castLE hℓ i := by
  simp [preparedPublicOccurrence, Gate.eq]

/-- Decode an occurrence witness for the prepared circuit into the original private variables. -/
def decodePrepared (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → R)
    (w : Fin (3 * (ℓ + n)) → R) : Fin (m - ℓ) → R :=
  privateWitness hℓ ((cs.prepare hℓ x).assignmentOfOccurrences w)

/-- Decoding a valid prepared occurrence witness satisfies the original relation. -/
theorem relation_decodePrepared (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) (w : Fin (3 * (ℓ + n)) → R)
    (hw : (cs.prepare hℓ x).occurrenceRelation (preparedPublicOccurrence n) x w) :
    relation cs ℓ hℓ x (cs.decodePrepared hℓ x w) := by
  have hz := (cs.prepare hℓ x).assignmentOfOccurrences_relation (Fin.castLEEmb hℓ)
    (preparedPublicOccurrence n) (cs.wireAt_preparedPublicOccurrence hℓ x) x w hw
  exact cs.privateWitness_of_prepare_accepts hℓ x _ hz.1

/-- Preparation supplies public coverage and an exact occurrence-witness language. -/
theorem exists_relation_iff_exists_prepared_occurrence (cs : ConstraintSystem R m n)
    (hℓ : ℓ ≤ m) (x : Fin ℓ → R) :
    (∃ w, relation cs ℓ hℓ x w) ↔
      ∃ a, (cs.prepare hℓ x).occurrenceRelation (preparedPublicOccurrence n) x a := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(cs.prepare hℓ x).occurrences (fullAssignment hℓ x w), ?_⟩
    apply (cs.prepare hℓ x).occurrences_relation (Fin.castLEEmb hℓ)
      (preparedPublicOccurrence n) (cs.wireAt_preparedPublicOccurrence hℓ x)
    apply (relation_iff_variableRelation _ hℓ x w).mp
    exact (cs.prepare_relation_iff hℓ x w).mpr hw
  · rintro ⟨a, ha⟩
    exact ⟨cs.decodePrepared hℓ x a, cs.relation_decodePrepared hℓ x a ha⟩

/-- Clear the constant selector on reserved public rows. -/
def clearPublicConstants (cs : ConstraintSystem R m n) (ℓ : ℕ) :
    ConstraintSystem R m n :=
  fun i => if i.val < ℓ then { cs i with qC := 0 } else cs i

/-- The public-input contribution on the reserved rows, zero on computational rows. -/
def publicInputTerm (_hℓ : ℓ ≤ n) (x : Fin ℓ → R) : Fin n → R :=
  fun i => if hi : i.val < ℓ then -x ⟨i.val, hi⟩ else 0

/-- Clearing a prepared constant and adding the public-input term restores it exactly once. -/
theorem eval_clearPublicConstants_add_publicInputTerm
    (cs : ConstraintSystem R m n) (hrows : ℓ ≤ n) (hwires : ℓ ≤ m)
    (x : Fin ℓ → R)
    (hpublic : ∀ i, cs (Fin.castLE hrows i) = Gate.eq (Fin.castLE hwires i) (x i))
    (z : Fin m → R) (i : Fin n) :
    ((cs.clearPublicConstants ℓ) i).eval z + publicInputTerm hrows x i = (cs i).eval z := by
  by_cases hi : i.val < ℓ
  · have hg : cs i = Gate.eq (Fin.castLE hwires ⟨i.val, hi⟩) (x ⟨i.val, hi⟩) :=
      hpublic ⟨i.val, hi⟩
    simp [clearPublicConstants, publicInputTerm, hi, hg, Gate.eval, Gate.eq]
  · simp [clearPublicConstants, publicInputTerm, hi]

/-- Read the public values baked into the reserved equality-row constants. -/
def preparedInputs (cs : ConstraintSystem R m n) (hrows : ℓ ≤ n) : Fin ℓ → R :=
  fun i => -(cs (Fin.castLE hrows i)).qC

/-- The values of prepared equality rows are determined by their constant selectors. -/
theorem eq_preparedInputs_of_isPreparedFor (cs : ConstraintSystem R m n)
    (hrows : ℓ ≤ n) (hwires : ℓ ≤ m) (h : cs.isPreparedFor ℓ hrows hwires) (i : Fin ℓ) :
    cs (Fin.castLE hrows i) = Gate.eq (Fin.castLE hwires i) (cs.preparedInputs hrows i) := by
  obtain ⟨c, hc⟩ := h i
  simp [preparedInputs, hc, Gate.eq]

/-- A prepared circuit's baked-in constants can be replaced by its explicit public-input term. -/
theorem accepts_iff_clearPublicConstants (cs : ConstraintSystem R m n)
    (hrows : ℓ ≤ n) (hwires : ℓ ≤ m) (h : cs.isPreparedFor ℓ hrows hwires)
    (z : Fin m → R) :
    cs.accepts z ↔ ∀ i, ((cs.clearPublicConstants ℓ) i).eval z +
      publicInputTerm hrows (cs.preparedInputs hrows) i = 0 := by
  simp only [cs.eval_clearPublicConstants_add_publicInputTerm hrows hwires
    (cs.preparedInputs hrows) (cs.eq_preparedInputs_of_isPreparedFor hrows hwires h)]
  rfl

/-- The prepared selector data after clearing is independent of the public input values. -/
theorem clearPublicConstants_prepare (cs : ConstraintSystem R m n) (hℓ : ℓ ≤ m)
    (x : Fin ℓ → R) :
    (cs.prepare hℓ x).clearPublicConstants ℓ = cs.prepare hℓ (fun _ => 0) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [clearPublicConstants, Gate.eq, j.isLt]
  · intro j
    simp [clearPublicConstants]

end ConstraintSystem
end Plonk
