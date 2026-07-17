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
  everything construction-shaped: the lifted witness and `checkAt` predicate plus the
  `2d`-point interpolation/descent engine (`Lift`), and the commit-then-challenge
  protocol with the escape/collision/common-opening extractor and CWSS plumbing (the
  committed-scalar shell). Following the instantiation note in
  `ProofSystem/RingSwitching/Lift.lean`, the package is assembled through the shell
  with `liftCheckAt`/`liftRecover` passed as single opaque terms.

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

/-- Figure 4's pure statement-extending verifier — the committed-scalar shell (definitionally
`Lift.verifier`). -/
def liftVerifier :
    Verifier oSpec (RlinStatement Φ n μ) (LiftStatement Φ K.TCom F n μ)
      (pSpecScalar K.TCom F) :=
  CommittedScalar.verifier K

/-- Honest prover shell.  Its commitment is definitionally derived from the output opening. -/
def liftProver (WitIn : Type)
    (computeW : RlinStatement Φ n μ → WitIn → LiftedWitness Φ μ n) :
    Prover oSpec (RlinStatement Φ n μ) WitIn (LiftStatement Φ K.TCom F n μ)
      (LiftedWitness Φ μ n) (pSpecScalar K.TCom F) :=
  CommittedScalar.prover K computeW

/-- Compatibility name for the generic branch-opening projection. -/
noncomputable def respOpening (r : LiftedWitness Φ μ n ⊕ E) : LiftedWitness Φ μ n :=
  CommittedScalar.responseOpening r

omit [NeZero q] in
@[simp] theorem respOpening_inl (w : LiftedWitness Φ μ n) :
    respOpening Φ (Sum.inl (β := E) w) = w := rfl

omit [NeZero q] in
/-- The Hachi-specific algebraic obligation of Lemma 9: one short opening passing the local
check at `2d` distinct points recovers `R^lin`. The interpolation, descent, and degree
bookkeeping are the generic presentation engine
(`Lift.Presentation.mulVec_eq_of_evalAt_rowSum`); this proof contributes only the
norm implication. -/
theorem liftRecover (hd : 0 < Φ.φ.natDegree) (s : RlinStatement Φ n μ)
    (w : LiftedWitness Φ μ n) (fam : Fin (2 * Φ.φ.natDegree) → F)
    (hinj : Function.Injective fam)
    (hcheck : ∀ j, liftCheckAt Φ bound φF s (fam j) w)
    (hshort : liftShort Φ bound ρBound w) : (s, w.z) ∈ relRlin Φ := by
  haveI := isPresentation_cyclotomic Φ hd
  refine ⟨?_, le_trans hshort.1 (hcheck ⟨0, by omega⟩).2⟩
  funext i
  exact (cyclotomicPresentation Φ).mulVec_eq_of_evalAt_rowSum φF.injective
    (cyclotomicPresentation_modulus_natDegree Φ) (w.hρ i) hinj
    (fun j => (hcheck j).1 i)

/-- Explicit Hachi Lemma 9 assembler — the generic escape/collision/common-opening
extractor, projecting the common opening to its `z`-component. -/
noncomputable def liftBuildWitness (hd : 0 < Φ.φ.natDegree)
    (s : RlinStatement Φ n μ) (t : K.TCom)
    (fam : Fin (2 * Φ.φ.natDegree) → F)
    (resp : Fin (2 * Φ.φ.natDegree) → (LiftedWitness Φ μ n ⊕ E)) :
    PolyVec (Rq Φ) μ ⊕ E :=
  CommittedScalar.buildWitness (by omega) K (fun w => w.z) s t fam resp

omit [NeZero q] in
/-- Hachi Lemma 9's auditable extraction theorem. The committed-scalar shell handles the
three commitment cases; `liftRecover` supplies precisely the quotient-interpolation step. -/
theorem liftBuildWitness_mem_relRlinE (hd : 0 < Φ.φ.natDegree)
    (s : RlinStatement Φ n μ) (t : K.TCom)
    (fam : Fin (2 * Φ.φ.natDegree) → F)
    (resp : Fin (2 * Φ.φ.natDegree) → (LiftedWitness Φ μ n ⊕ E))
    (hresp : ∀ j, ((s, t, fam j), resp j) ∈ relLiftE Φ bound ρBound K φF)
    (hinj : Function.Injective fam) :
    (s, liftBuildWitness Φ bound ρBound K hd s t fam resp) ∈ relRlinE Φ K.esc := by
  simpa only [liftBuildWitness, relRlinE, relLiftE, relLift] using
    CommittedScalar.buildWitness_mem (by omega) K (fun w => w.z)
      (liftCheckAt Φ bound φF) (relRlin Φ)
      (fun s' w fam' hinj' hcheck hshort =>
        liftRecover Φ bound ρBound φF hd s' w fam' hinj' hcheck hshort)
      s t fam resp hresp hinj

omit [NeZero q] in
/-- Hachi Lemma 9: CWSS at `k = 2d`, from the committed-scalar shell with `liftRecover` as
the substantive algebra. -/
theorem lift_coordinateWiseSpecialSound
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    (liftVerifier (oSpec := oSpec) Φ bound ρBound K).coordinateWiseSpecialSound init impl
      (scalarStructure (2 * Φ.φ.natDegree) (by omega))
      (relRlinE Φ (n := n) (μ := μ) K.esc)
      (relLiftE Φ bound ρBound K φF) := by
  simpa only [liftVerifier, relRlinE, relLiftE, relLift] using
    CommittedScalar.coordinateWiseSpecialSound (by omega) K (fun w => w.z)
      (liftCheckAt Φ bound φF) (relRlin Φ)
      (fun s w fam hinj hcheck hshort =>
        liftRecover Φ bound ρBound φF hd s w fam hinj hcheck hshort)
      init impl

/-- Hachi's `Lift` instance as a composable CWSS package. -/
def liftPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    CWSSPackage init impl
      (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (pSpecScalar K.TCom F) where
  verifier := liftVerifier Φ bound ρBound K
  struct := scalarStructure (2 * Φ.φ.natDegree) (by omega)
  relIn := relRlinE Φ K.esc
  relOut := relLiftE Φ bound ρBound K φF
  isPure := ⟨fun stmt tr =>
    (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := lift_coordinateWiseSpecialSound Φ bound ρBound K φF init impl hd

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
