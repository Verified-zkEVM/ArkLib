/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Tower

/-!
# Batched bounded-fiber tower agreement recovery

This module is an adapter for `AgreementRecovery.Tower` that keeps each initial tower as the
common ancestor of its live descendants. At one received coordinate the ancestor residual is
formed once, then `TowerBatch.restrictBases` sends that same nested polynomial through one
product/remainder tree for the base moduli of all live descendants. Each descendant subsequently
performs its own fiber reduction and D5 zero/unit split.

The base batch therefore includes repeated moduli and does not assume that live descendants have
the same fiber polynomial. Stopped descendants are omitted from the product tree and keep their
recorded sample positions unchanged. The correctness companion proves refinement at the
observable recovered-message level; it deliberately does not claim an asymptotic cost bound.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.BatchedTower

open CompPoly CompPoly.CPolynomial Polynomial Polynomial.JetHornerMachine
  SampleInterpolation TowerAlgebra

variable {F E I : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] {n : ℕ}

/-- Package one D5 split using an explicitly supplied residual. This is the common local splitter
used by both the batched runtime and the pointwise refinement specification. -/
def splitWithResidual (k : ℕ) (component : Tower.Component E k)
    (residual : CPolynomial (CPolynomial E)) : List (Bool × Tower.Component E k) :=
  (splitZeroUnit component.val residual component.property).attach.map fun child =>
    (child.val.tag.isZero,
      ⟨child.val.tower, splitZeroUnit_wellFormed component.val residual
        component.property child.val child.property⟩)

/-- Canonical residual used by the pointwise specification of one live descendant. The initial
family residual is first restricted to the descendant base algebra and only then reduced in its
possibly different fiber algebra. -/
def restrictedResidual (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    {k : ℕ} (source current : Tower.Component E k) (i : Fin n) :
    CPolynomial (CPolynomial E) :=
  let raw := source.val.residual (base (domain i)) (base (received i))
  let baseResidual := TowerRepresentation.reduceBase current.val.modulus raw
  TowerRepresentation.reduceElement current.val.modulus current.val.fiber baseResidual

/-- Pointwise splitter corresponding to the batched row operation. It is not the runtime batch:
it states the per-descendant operation to which the product-tree execution refines. -/
def splitAtSource (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (source current : Tower.Component E k) (i : Fin n) :
    List (Bool × Tower.Component E k) :=
  splitWithResidual k current (restrictedResidual base domain received source current i)

/-- Base moduli of exactly the live descendants. Stopped components consume no batch slot, while
repeated base factors are retained in their original order. -/
def liveModuli (k : ℕ) : List (ComponentScan.Block (Tower.Component E k) I) →
    List (CPolynomial E)
  | [] => []
  | block :: rest =>
      if k ≤ block.positions.length then liveModuli k rest
      else block.component.val.modulus :: liveModuli k rest

/-- Split one live block after its base-restricted residual has been obtained from the shared
product tree. The second reduction is local because different live branches may have different
fiber moduli. -/
def splitRestricted (k : ℕ) (i : I)
    (block : ComponentScan.Block (Tower.Component E k) I)
    (baseResidual : CPolynomial (CPolynomial E)) :
    List (ComponentScan.Block (Tower.Component E k) I) :=
  let residual := TowerRepresentation.reduceElement block.component.val.modulus
    block.component.val.fiber baseResidual
  (splitWithResidual k block.component residual).map fun child =>
    ⟨child.2, if child.1 then i :: block.positions else block.positions⟩

/-- Consume the ordered batch results. Stopped blocks preserve their position and do not consume a
remainder. Every live block consumes exactly one base remainder and may emit several D5 children. -/
def advanceWithRestricted (k : ℕ) (i : I) :
    List (ComponentScan.Block (Tower.Component E k) I) →
      List (CPolynomial (CPolynomial E)) →
        List (ComponentScan.Block (Tower.Component E k) I)
  | [], _ => []
  | block :: rest, residuals =>
      if k ≤ block.positions.length then
        block :: advanceWithRestricted k i rest residuals
      else
        match residuals with
        | [] => []
        | residual :: more =>
            splitRestricted k i block residual ++ advanceWithRestricted k i rest more

/-- Advance all descendants of one initial tower through one received coordinate. This is the
actual batched call path: one ancestor residual and one `restrictBases` call cover every live base
modulus in the family before any branch-specific fiber work is performed. -/
def advanceFamily (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (source : Tower.Component E k) (i : Fin n)
    (blocks : List (ComponentScan.Block (Tower.Component E k) (Fin n))) :
    List (ComponentScan.Block (Tower.Component E k) (Fin n)) :=
  let raw := source.val.residual (base (domain i)) (base (received i))
  let moduli := liveModuli k blocks
  let restricted := TowerBatch.restrictBases M D raw moduli
  advanceWithRestricted k i blocks restricted

/-- Row-wise scan for all descendants of one common ancestor. Once the rows are exhausted, the
ordinary empty-row scan drops components that never reached `k` recorded agreements. -/
def scanFamily (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (source : Tower.Component E k) :
    List (Fin n) → List (ComponentScan.Block (Tower.Component E k) (Fin n)) →
      List (ComponentScan.Block (Tower.Component E k) (Fin n))
  | [], blocks =>
      blocks.flatMap (ComponentScan.scan (fun _ => true)
        (splitAtSource base domain received k source) k [])
  | i :: rest, blocks =>
      scanFamily M D base domain received k source rest
        (advanceFamily M D base domain received k source i blocks)

/-- Batched stopped blocks for all supplied tower families. Batching is per initial family because
that family supplies the common coefficient/residual data shared by all of its descendants. -/
def blocks (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Tower.Component E k)) :
    List (ComponentScan.Block (Tower.Component E k) (Fin n)) :=
  families.flatMap fun source =>
    scanFamily M D base domain received k source (List.ofFn (@id (Fin n))) [⟨source, []⟩]

/-- Execute batched tower recovery, interpolation over the original base field, full agreement
checking, and fixed-width vector deduplication. -/
def recoverAgreement (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (families : List (Tower.Component E k)) : List (List F) :=
  ((blocks M D base domain received k families).filterMap fun block =>
    checkedCandidate domain received k A block.positions.toFinset).dedup

/-- Drop-in adapter with the repository's ordinary executable polynomial backends. The signature
apart from the namespace matches `Tower.recoverAgreement`, so callers can switch after review. -/
def recoverAgreementDefault (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (families : List (Tower.Component E k)) : List (List F) :=
  recoverAgreement .naive .remainderOnly base domain received k A families

end ReedSolomon.ListDecoding.AgreementRecovery.BatchedTower
