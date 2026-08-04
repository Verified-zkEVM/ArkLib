/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Lift.Presentation
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.CommittedScalar

/-!
  # `Lift` — protocol layer

  The two-round `Lift` reduction, written once over an arbitrary
  `Presentation R S` (`Presentation.lean`) and the committed-scalar shell
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`). The
  protocol moves a linear claim over the quotient ring `S` into the field `F` where all
  later checking happens:

  * the prover commits to the **lifted witness** `(z, ρ)` — the `S`-witness of a linear
    relation `M z = y` together with one quotient polynomial per row, of degree `≤ d − 1`;
  * the verifier sends one scalar challenge `α ← F`;
  * the output relation checks the lifted row identities *evaluated at `α`*
    (`checkAt`), commitment consistency, and admissibility.

  The name records the first of these operations: `ρ` lifts equality in `S = R[X]/(φ)` to
  exact equality in `R[X]`; the random evaluation challenge then checks that lift in `F`.

  Soundness rests on the degree structure of the lift: each lifted row identity is a
  polynomial identity of degree `< 2d`, so openings passing `checkAt` at `2d`
  pairwise-distinct challenges determine it exactly, and the identity descends to `S`.
  Coordinate-wise special soundness therefore holds at plain `k = 2d` special soundness: the
  generic extractor is the committed-scalar three-way assembler, and the single
  construction-specific obligation — one short opening passing `checkAt` at `2d`
  pairwise-distinct challenges recovers the input relation — is discharged **generically**
  by the presentation's interpolation engine (`recover`). An instance therefore supplies
  only:

  * a `Presentation R S` with its `IsPresentation` laws (e.g. the cyclotomic
    `cyclotomicPresentation` over `Rq Φ`,
    in `Commitments/Functional/Hachi/RingSwitch/Reduction.lean`);
  * how to read the linear statement off its statement type (`getM`, `getY`);
  * its admissibility predicates (`zOk` on input witnesses, `wShort` on lifted openings,
    `sideCond` on statements) and the one implication tying them together;
  * a `BindingCommitment` for the lifted witness (weak binding via the escape budget).

  ## Statement-type genericity

  The statement is an abstract `Stmt` with projections `getM : Stmt → Matrix _ _ S` and
  `getY : Stmt → Fin n → S`, so instances can carry extra public data (Hachi: the norm
  bound) without wrapping.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace RingSwitching.Lift

open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound
open ArkLib.Lattices

/-- The lifted witness of `Lift`: the `S`-witness `z` of the linear
relation and one quotient polynomial per row, degree-bounded by the presentation degree
(`d − 1`; honest quotients satisfy the tighter `d − 2`). The degree `d` is a plain parameter
so that instances can state it against their own degree expression. -/
structure LiftedWitness (R : Type) [Semiring R] (S : Type) (d μ n : ℕ) where
  /-- The witness `z ∈ S^μ` of the linear relation. -/
  z : Fin μ → S
  /-- Per-row quotient polynomials in `R[X]`. -/
  ρ : Fin n → Polynomial R
  /-- Degree bound on the quotients. -/
  hρ : ∀ i, (ρ i).natDegree ≤ d - 1

/-- The all-zero lifted witness. -/
instance {R : Type} [Semiring R] {S : Type} [Zero S] {d μ n : ℕ} :
    Nonempty (LiftedWitness R S d μ n) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => by simp⟩⟩

variable {R S : Type} [CommRing R] [CommRing S]
variable {n μ d : ℕ} {E : Type} {F : Type} {Stmt : Type}

/-- The input relation of the switch: the linear relation `M z = y` read off the statement,
together with the instance's admissibility predicate on witnesses. -/
def relLin (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
    (zOk : Stmt → PolyVec S μ → Prop) : Set (Stmt × PolyVec S μ) :=
  {p | getM p.1 *ᵥ p.2 = getY p.1 ∧ zOk p.1 p.2}

section CheckAt

variable [CommSemiring F]

/-- The challenge-local predicate of the switch: every lifted row identity holds at the
challenge point `a`, plus the instance's statement-side condition (Hachi: compatibility of
the global norm parameter with the public bound). -/
def checkAt (P : Presentation R S) (φF : R →+* F)
    (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
    (sideCond : Stmt → Prop)
    (s : Stmt) (a : F) (w : LiftedWitness R S d μ n) : Prop :=
  (∀ i, evalAt φF a (P.rowSum (getM s) w.z i) =
      evalAt φF a (P.rep (getY s i)) +
        evalAt φF a P.modulus * evalAt φF a (w.ρ i)) ∧
    sideCond s

end CheckAt

variable [Field F]
variable (P : Presentation R S) (φF : R →+* F)
variable (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
variable (zOk : Stmt → PolyVec S μ → Prop) (sideCond : Stmt → Prop)
variable {wShort : LiftedWitness R S d μ n → Prop}
variable (K : BindingCommitment (LiftedWitness R S d μ n) E wShort)

/-- The anchored output relation of the switch, from the committed-scalar shell:
commitment consistency, `checkAt`, and admissibility of the opening. -/
def relOut : Set (CommittedScalar.Statement Stmt K.TCom F × LiftedWitness R S d μ n) :=
  CommittedScalar.rel K (checkAt P φF getM getY sideCond)

/-- Escape-threaded output relation. -/
def relOutE :
    Set (CommittedScalar.Statement Stmt K.TCom F × (LiftedWitness R S d μ n ⊕ E)) :=
  (relOut P φF getM getY sideCond K).withEscape K.esc

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The switch's pure statement-extending verifier, from the committed-scalar shell. -/
def verifier :
    Verifier oSpec Stmt (CommittedScalar.Statement Stmt K.TCom F)
      (pSpecScalar K.TCom F) :=
  CommittedScalar.verifier K

/-- Honest prover shell. Its commitment is definitionally derived from the output opening. -/
def prover (WitIn : Type) (computeW : Stmt → WitIn → LiftedWitness R S d μ n) :
    Prover oSpec Stmt WitIn (CommittedScalar.Statement Stmt K.TCom F)
      (LiftedWitness R S d μ n) (pSpecScalar K.TCom F) :=
  CommittedScalar.prover K computeW

/-- **The generic recovery theorem** (the [NOZ26] Lemma 9 obligation, discharged once): a
short opening passing the local check at `2d` pairwise-distinct challenges recovers the
input relation. The linear part is the presentation's interpolation engine per row; the
admissibility part is the instance's `short_zOk` implication. -/
theorem recover [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.natDegree = d)
    (short_zOk : ∀ (s : Stmt) (w : LiftedWitness R S d μ n),
      wShort w → sideCond s → zOk s w.z)
    (s : Stmt) (w : LiftedWitness R S d μ n) (fam : Fin (2 * d) → F)
    (hinj : Function.Injective fam)
    (hcheck : ∀ j, checkAt P φF getM getY sideCond s (fam j) w)
    (hshort : wShort w) : (s, w.z) ∈ relLin getM getY zOk := by
  have hpos : 0 < d := hd ▸ P.natDegree_modulus_pos
  have hside : sideCond s := (hcheck ⟨0, by omega⟩).2
  refine ⟨?_, short_zOk s w hshort hside⟩
  funext i
  exact P.mulVec_eq_of_evalAt_rowSum hφF hd (w.hρ i) hinj (fun j => (hcheck j).1 i)

/-- The switch's extractor: the committed-scalar three-way assembler, projecting the common
opening to its `z`-component. -/
noncomputable def buildWitness [IsPresentation P] (hd : P.modulus.natDegree = d)
    (s : Stmt) (t : K.TCom) (fam : Fin (2 * d) → F)
    (resp : Fin (2 * d) → (LiftedWitness R S d μ n ⊕ E)) :
    (Fin μ → S) ⊕ E :=
  CommittedScalar.buildWitness
    (by have := hd ▸ P.natDegree_modulus_pos; omega) K (fun w => w.z) s t fam resp

/-- Correctness of the extractor against the input relation. -/
theorem buildWitness_mem [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.natDegree = d)
    (short_zOk : ∀ s w, wShort w → sideCond s → zOk s w.z)
    (s : Stmt) (t : K.TCom) (fam : Fin (2 * d) → F)
    (resp : Fin (2 * d) → (LiftedWitness R S d μ n ⊕ E))
    (hresp : ∀ j, ((s, t, fam j), resp j) ∈ relOutE P φF getM getY sideCond K)
    (hinj : Function.Injective fam) :
    (s, buildWitness P K hd s t fam resp)
      ∈ (relLin getM getY zOk).withEscape K.esc := by
  simpa only [buildWitness, relOutE, relOut] using
    CommittedScalar.buildWitness_mem
      (by have := hd ▸ P.natDegree_modulus_pos; omega) K (fun w => w.z)
      (checkAt P φF getM getY sideCond) (relLin getM getY zOk)
      (fun s' w fam' hinj' hcheck hshort =>
        recover P φF getM getY zOk sideCond hφF hd short_zOk s' w fam' hinj' hcheck hshort)
      s t fam resp hresp hinj

/-- **CWSS of `Lift`**, at plain `k = 2d` special soundness, from the
generic committed-scalar theorem. -/
theorem coordinateWiseSpecialSound [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.natDegree = d)
    (short_zOk : ∀ s w, wShort w → sideCond s → zOk s w.z)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (verifier (oSpec := oSpec) (F := F) K).coordinateWiseSpecialSound init impl
      (scalarStructure (2 * d) (by have := hd ▸ P.natDegree_modulus_pos; omega))
      ((relLin getM getY zOk).withEscape K.esc)
      (relOutE P φF getM getY sideCond K) := by
  simpa only [verifier, relOutE, relOut] using
    CommittedScalar.coordinateWiseSpecialSound
      (by have := hd ▸ P.natDegree_modulus_pos; omega) K (fun w => w.z)
      (checkAt P φF getM getY sideCond) (relLin getM getY zOk)
      (fun s w fam hinj hcheck hshort =>
        recover P φF getM getY zOk sideCond hφF hd short_zOk s w fam hinj hcheck hshort)
      init impl

/-- `Lift` as a composable CWSS package. -/
def package [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.natDegree = d)
    (short_zOk : ∀ s w, wShort w → sideCond s → zOk s w.z)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    CWSSPackage init impl Stmt ((Fin μ → S) ⊕ E)
      (CommittedScalar.Statement Stmt K.TCom F) (LiftedWitness R S d μ n ⊕ E)
      (pSpecScalar K.TCom F) where
  verifier := verifier K
  struct := scalarStructure (2 * d) (by have := hd ▸ P.natDegree_modulus_pos; omega)
  relIn := (relLin getM getY zOk).withEscape K.esc
  relOut := relOutE P φF getM getY sideCond K
  isPure := ⟨fun stmt tr =>
    (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := coordinateWiseSpecialSound P φF getM getY zOk sideCond K hφF hd short_zOk init impl

end Protocol

end RingSwitching.Lift
