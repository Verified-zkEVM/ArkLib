/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.SplitZeroUnit
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.ComponentScan
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerEvaluation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerBatch
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SampleInterpolation

/-!
# Recovery from bounded-fiber towers

`RecoverAgreement` traverses the actual D5 zero/unit children, records distinct received
positions, interpolates over the original base field at `k` agreements, checks the full word,
and removes duplicate vectors. Internal component invariants are proof-only and erased; no
geometric point or decoded-list witness is supplied to the executable consumer.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.Tower

open CompPoly Polynomial Polynomial.JetHornerMachine SampleInterpolation TowerAlgebra

variable {F E : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] {n : ℕ}

/-- A retained finite component with erased invariants established by its constructor. -/
abbrev Component (E : Type*) [Field E] [BEq E] [LawfulBEq E] (k : ℕ) :=
  {r : TowerRepresentation (F := E) // r.WellFormed k}

/-- Split one live component by its computed residual at a received position. -/
def splitAt (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (component : Component E k) (i : Fin n) : List (Bool × Component E k) :=
  let residual := component.val.residual (base (domain i)) (base (received i))
  (splitZeroUnit component.val residual component.property).attach.map fun child =>
    (child.val.tag.isZero,
      ⟨child.val.tower, splitZeroUnit_wellFormed component.val residual
        component.property child.val child.property⟩)

/-- Run the collection scan on all supplied towers. Components are already positive-dimensional;
their D5 children have the same property, so the generic alive predicate is constantly true. -/
def blocks (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Component E k)) :
    List (ComponentScan.Block (Component E k) (Fin n)) :=
  ComponentScan.scanMany (fun _ => true) (splitAt base domain received k) k
    (List.ofFn (@id (Fin n))) (families.map fun r => ⟨r, []⟩)

/-- Execute tower agreement recovery, base-field interpolation, final agreement testing, and
fixed-width coefficient-vector deduplication. The finite families are constructor outputs. -/
def recoverAgreement (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (families : List (Component E k)) : List (List F) :=
  ((blocks base domain received k families).filterMap fun block =>
    checkedCandidate domain received k A block.positions.toFinset).dedup

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The collection scan is exactly the ordered concatenation of the component scans, including
all recorded-position metadata. -/
theorem blocks_eq (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Component E k)) :
    blocks base domain received k families = families.flatMap fun r =>
      ComponentScan.scan (fun _ => true) (splitAt base domain received k) k
        (List.ofFn (@id (Fin n))) ⟨r, []⟩ := by
  rw [blocks, ComponentScan.scanMany_eq, List.flatMap_map]

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Every interpolation attempt uses exactly `k` distinct positions of the supplied word. -/
theorem stopped_card (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Component E k))
    (out : ComponentScan.Block (Component E k) (Fin n))
    (hout : out ∈ blocks base domain received k families) : out.positions.toFinset.card = k := by
  rw [blocks_eq] at hout
  obtain ⟨r, _, hout⟩ := List.mem_flatMap.mp hout
  have hlen := ComponentScan.positions_length (fun _ => true)
    (splitAt base domain received k) k _ ⟨r, []⟩ out (by simp) hout
  have hsub := ComponentScan.positions_sublist (fun _ => true)
    (splitAt base domain received k) k _ ⟨r, []⟩ out hout
  have hnodup : out.positions.Nodup := hsub.nodup (by
    simpa using (List.nodup_ofFn.mpr (Function.injective_id : Function.Injective (@id (Fin n)))))
  rw [List.toFinset_card_of_nodup hnodup, hlen]

/-- Every returned vector has the requested width and passes the full agreement test. This
soundness property does not assume that the candidate constructor covers all wanted messages. -/
theorem mem_recoverAgreement_properties (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (families : List (Component E k)) (cs : List F)
    (hcs : cs ∈ recoverAgreement base domain received k A families) :
    cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  simp only [recoverAgreement, List.mem_dedup, List.mem_filterMap] at hcs
  obtain ⟨block, hblock, hc⟩ := hcs
  have hp := checkedCandidate_properties domain received k A block.positions.toFinset
    (stopped_card base domain received k families block hblock) cs hc
  exact ⟨hp.1, hp.2.2⟩

end ReedSolomon.ListDecoding.AgreementRecovery.Tower
