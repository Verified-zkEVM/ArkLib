/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Rlin
import ArkLib.Data.Lattices.CyclotomicRing.QuotientLift
import ArkLib.ProofSystem.RingSwitching.Lift.Reduction

/-!
  # Hachi's `Lift` instance (Figure 4 / Lemma 9)

  This file is the **cyclotomic instance** of generic `Lift`
  (`ProofSystem/RingSwitching/Lift/`): the presentation is `Rq Φ` with canonical
  reduced representatives (`cyclotomicPresentation`, laws discharged from the `Rq` quotient
  bridge in `Data/Lattices/CyclotomicRing/QuotientLift.lean`). The generic layers supply
  everything construction-shaped: the lifted witness and `checkAt` predicate, the
  `2d`-point interpolation/descent recovery, the escape/collision/common-opening extractor,
  and the CWSS plumbing. The composable package is therefore assembled **wholesale from generic
  `Lift.package`** at `cyclotomicPresentation`; the single Hachi-specific obligation handed to it
  is the norm implication `vecLInftyNorm_le_of_liftShort`. (See the note above `liftPackage` on
  why the CWSS certificate is exposed as `liftPackage.isCWSS` rather than a standalone theorem in
  Hachi's relation vocabulary.)

  The data that is genuinely specific to Hachi stays here:

  * the coefficient/norm bounds on the lifted witness (`RhoShort`, `liftShort`);
  * how the `R^lin` statement carries its public norm bound (`zOk`/`sideCond` instantiation);
  * the weak-binding `w̃`-commitment interface (`LiftCom`, Module-SIS escape budget).

  The name **Lift** refers to turning equality modulo `Φ.φ` into an exact polynomial
  equality with an explicit quotient witness. Its sibling is **Packing**, which instead
  encodes a basis-sized block of small-field coefficients as one large-field coefficient.

  This is intentionally a sibling of the DP24/Binius `Packing` switch
  (`ProofSystem/RingSwitching/Packing/`), not an instance of `RingSwitchingProfile`:
  packing a small-field polynomial into a larger field and evaluating a quotient presentation
  are different algebraic constructions (see the taxonomy in
  `ProofSystem/RingSwitching/Basic.lean`).

  ## Paper-model boundary

  Figure 4's simplified presentation commits to `(z, r)`.  The full protocol decomposes the
  quotient into short base-`b` digits before commitment.  `RhoShort` records the resulting
  admissibility requirement abstractly; the concrete digit encoding and its completeness bound
  remain the responsibility of the downstream Hachi constraint layer.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type}

/-! ## The cyclotomic presentation used by `Lift` -/

/-- `Rq Φ` presented by the cyclotomic modulus with canonical (reduced) representatives —
Hachi's instance of the generic `Lift.Presentation` data.  Proof-free, like
`CyclotomicModulus` itself; the laws are `isPresentation_cyclotomic`. -/
noncomputable def cyclotomicPresentation : Lift.Presentation (ZMod q) (Rq Φ) where
  modulus := Φ.φ.toPoly
  rep a := a.1.toPoly

omit [NeZero q] in
/-- The presentation degree is the ring dimension. -/
theorem cyclotomicPresentation_modulus_natDegree :
    (cyclotomicPresentation Φ).modulus.natDegree = Φ.φ.natDegree :=
  (CompPoly.CPolynomial.natDegree_toPoly Φ.φ).symm

omit [NeZero q] in
/-- The presentation laws for the cyclotomic instance, discharged from the `Rq` quotient
bridge (`QuotientLift.lean`).  Positivity of the ring dimension is the one genuine
hypothesis. -/
theorem isPresentation_cyclotomic (hd : 0 < Φ.φ.natDegree) :
    Lift.IsPresentation (cyclotomicPresentation Φ) where
  monic := IsCyclotomic.monic
  natDegree_rep_lt s := by
    simpa [cyclotomicPresentation, CompPoly.CPolynomial.natDegree_toPoly] using
      Rq.natDegree_val_toPoly_lt' Φ hd s
  rep_injective := val_toPoly_injective Φ
  modulus_dvd_rep_add := modulus_dvd_toPoly_add_sub Φ
  modulus_dvd_rep_mul := modulus_dvd_toPoly_mul_sub Φ

/-! ## Hachi witness and relation instance -/

/-- Hachi Eq. (21)'s lifted witness: the `R^lin` witness `z ∈ Rq^μ` and one quotient
polynomial per row in `ZMod q[X]` of degree at most `d − 1` (honest quotients satisfy the
tighter `d − 2`) — the generic lifted witness at the cyclotomic degree. -/
abbrev LiftedWitness (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) :=
  Lift.LiftedWitness (ZMod q) (Rq Φ) Φ.φ.natDegree μ n

/-- Coefficient-range predicate on the quotient polynomials. -/
def RhoShort (ρBound : ℕ) (ρ : Fin n → Polynomial (ZMod q)) : Prop :=
  ∀ i k, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound

/-- Hachi's norm-conditioned admissibility predicate for a lifted opening. -/
def liftShort (bound ρBound : ℕ) (w : LiftedWitness Φ μ n) : Prop :=
  vecLInftyNorm Φ w.z ≤ bound ∧ RhoShort ρBound w.ρ

/-- Compatibility name for the reusable norm-conditioned binding interface. -/
abbrev LiftCom (W E : Type) (Short : W → Prop) :=
  CoordinateWise.BindingCommitment W E Short

/-- The injective commitment witnesses that the abstraction is non-vacuous. -/
example (bound ρBound : ℕ) :
    LiftCom (LiftedWitness Φ μ n) Unit (liftShort Φ bound ρBound) :=
  { TCom := LiftedWitness Φ μ n
    com := id
    esc := ∅
    escOfCollision := fun _ _ => ()
    collision_mem := fun _ _ hne heq _ _ => absurd heq hne }

/-- Output statement: the input `R^lin` claim, the opening commitment, and evaluation point. -/
abbrev LiftStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) : Type :=
  CommittedScalar.Statement (RlinStatement Φ n μ) TCom F

variable {F : Type} [Field F] (bound ρBound : ℕ)

/-- Challenge-local Hachi predicate: every quotient identity holds at `α`, and the global
norm parameter is compatible with the public `R^lin` bound — the generic `checkAt` at the
cyclotomic presentation. -/
def liftCheckAt (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) : Prop :=
  Lift.checkAt (cyclotomicPresentation Φ) φF (fun s => s.M) (fun s => s.yvec)
    (fun s => bound ≤ s.bound) s a w

/-- The Hachi output relation, instantiated from the generic anchored committed-scalar relation. -/
def relLift (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  CommittedScalar.rel K (liftCheckAt Φ bound φF)

/-- Escape-threaded Hachi lift relation. -/
def relLiftE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relLift Φ bound ρBound K φF).withEscape K.esc

/-! ## Specialization of the generic switch -/

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
  (φF : ZMod q →+* F)

omit [NeZero q] [IsCyclotomic Φ] in
/-- The **sole Hachi-specific obligation** of Lemma 9 in the generic-consumption model: the
norm implication. A short lifted witness (`‖z‖∞ ≤ bound`) at a statement whose public bound
dominates (`bound ≤ s.bound`) has `‖z‖∞ ≤ s.bound`. This is exactly generic `Lift`'s
`short_zOk` hypothesis; the interpolation/descent recovery and the escape/collision extractor
are supplied by the generic layer. -/
theorem vecLInftyNorm_le_of_liftShort (s : RlinStatement Φ n μ) (w : LiftedWitness Φ μ n)
    (hshort : liftShort Φ bound ρBound w) (hside : bound ≤ s.bound) :
    vecLInftyNorm Φ w.z ≤ s.bound :=
  le_trans hshort.1 hside

/-! ### Why the CWSS certificate is exposed only as `liftPackage.isCWSS`

We deliberately do **not** provide a standalone `lift_coordinateWiseSpecialSound` restated in
Hachi's `relRlinE`/`relLiftE` relation vocabulary. Doing so forces the elaborator to check a
`whnf` defeq between that vocabulary and the generic `Lift.relLin`/`Lift.relOutE`/`Lift.verifier`
*inside the full `coordinateWiseSpecialSound` proposition* — which unfolds `Rq`'s computable layer
(via the `verifier`) and times out (`maximum number of heartbeats` at `whnf`). The certificate is
therefore `liftPackage.isCWSS` (generic `Lift.coordinateWiseSpecialSound` specialized). Crucially,
the `▷` seams in `Composition.lean` still close by `rfl`: that `rfl` compares only the two relations
(structurally identical after β-reduction — same `*ᵥ` subterms), never the verifier. -/

/-- Hachi's `Lift` instance as a composable CWSS package, **assembled wholesale from generic
`Lift.package`** at the cyclotomic presentation: the verifier, structure, purity witness, and
CWSS certificate are all the generic layer's. Hachi supplies only the presentation data
(`cyclotomicPresentation`/`isPresentation_cyclotomic`) and the norm implication
(`vecLInftyNorm_le_of_liftShort`). -/
noncomputable def liftPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    CWSSPackage init impl
      (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (pSpecScalar K.TCom F) :=
  haveI := isPresentation_cyclotomic Φ hd
  Lift.package (cyclotomicPresentation Φ) φF (fun s => s.M) (fun s => s.yvec)
    (fun s z => vecLInftyNorm Φ z ≤ s.bound) (fun s => bound ≤ s.bound) K
    φF.injective (cyclotomicPresentation_modulus_natDegree Φ)
    (fun s w hshort hside => vecLInftyNorm_le_of_liftShort Φ bound ρBound s w hshort hside)
    init impl

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
