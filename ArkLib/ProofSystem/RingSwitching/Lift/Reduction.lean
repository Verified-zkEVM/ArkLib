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
  extractor is the committed-scalar assembler `CommittedScalar.treeExtractor`, and the single
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
  * a `BindingCommitment` for the lifted witness.

  ## Where weak binding lives

  The commitment is only binding on short openings, so the certificate is the **escape-threaded**
  one: `package` is an `EscapeCWSSPackage` whose event is `CommittedScalar.escEvent`, i.e.
  "the tree's branch openings exhibit a short collision of the committed value". Relations and the
  extractor stay ordinary — nothing here is widened by a sum type, and the extractor returns a plain
  `Fin μ → S`. See `CommittedScalar.lean` for why the break has to be an event on `(statement,
  tree)` rather than an extractor output.

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
open ArkLib.Lattices CompPoly

/-- The lifted witness of `Lift`: the `S`-witness `z` of the linear
relation and one **computable** quotient polynomial per row, degree-bounded by the presentation
degree (`d − 1`; honest quotients satisfy the tighter `d − 2`). The degree `d` is a plain
parameter so that instances can state it against their own degree expression.

`ρ` carries `CPolynomial` data and the bound speaks about its `toPoly` semantics, uniformly
with the `IsPresentation` laws — which is what makes concrete lifted witnesses constructible at
all (no Mathlib `Polynomial` value compiles). -/
structure LiftedWitness (R : Type) [Semiring R] (S : Type) (d μ n : ℕ) where
  /-- The witness `z ∈ S^μ` of the linear relation. -/
  z : Fin μ → S
  /-- Per-row quotient polynomials, computable. -/
  ρ : Fin n → CPolynomial R
  /-- Degree bound on the quotients (semantic form). -/
  hρ : ∀ i, (ρ i).toPoly.natDegree ≤ d - 1

/-- The all-zero lifted witness. -/
instance {R : Type} [Semiring R] {S : Type} [Zero S] {d μ n : ℕ} :
    Nonempty (LiftedWitness R S d μ n) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => by
    rw [CPolynomial.toPoly_zero, Polynomial.natDegree_zero]; exact Nat.zero_le _⟩⟩

variable {R S : Type} [CommRing R] [CommRing S]
variable {n μ d : ℕ} {F : Type} {Stmt : Type}

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
      evalAt φF a ((P.rep (getY s i)).toPoly) +
        evalAt φF a (P.modulus.toPoly) * evalAt φF a ((w.ρ i).toPoly)) ∧
    sideCond s

end CheckAt

variable [Field F]
variable (P : Presentation R S) (φF : R →+* F)
variable (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
variable (zOk : Stmt → PolyVec S μ → Prop) (sideCond : Stmt → Prop)
variable {wShort : LiftedWitness R S d μ n → Prop}
variable (K : BindingCommitment (LiftedWitness R S d μ n) wShort)

/-- The anchored output relation of the switch, from the committed-scalar shell:
commitment consistency, `checkAt`, and admissibility of the opening. -/
def relOut : Set (CommittedScalar.Statement Stmt K.TCom F × LiftedWitness R S d μ n) :=
  CommittedScalar.rel K (checkAt P φF getM getY sideCond)

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
    (hd : P.modulus.toPoly.natDegree = d)
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

/-- The switch's **escape event**: the committed-scalar collision event at this switch's output
relation — the tree's branch openings exhibit a short collision of the committed lifted witness.
This is the only place weak binding enters the certificate. -/
def escEvent [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d) :
    ChallengeTree.EscapeEvent Stmt (pSpecScalar K.TCom F)
      (CWSSStructure.toShape (scalarStructure (Msg := K.TCom) (C := F) (2 * d)
        (by have := hd ▸ P.natDegree_modulus_pos; omega))).arity :=
  CommittedScalar.escEvent
    (by have := hd ▸ P.natDegree_modulus_pos; omega) K (checkAt P φF getM getY sideCond)

/-- The switch's named extractor: the committed-scalar assembler, projecting the common opening to
its `z`-component.

**Computable.** The `k = 2d` branch openings arrive on the leaf witnessing rather than being
recovered by inverting the output relation, so this takes no `checkAt` argument and pulls in no
`Classical.choice`. -/
def treeExtractor [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d) :
    Extractor.TreeBased Stmt (PolyVec S μ) (LiftedWitness R S d μ n) (pSpecScalar K.TCom F)
      (CWSSStructure.toShape (scalarStructure (Msg := K.TCom) (C := F) (2 * d)
        (by have := hd ▸ P.natDegree_modulus_pos; omega))).arity :=
  CommittedScalar.treeExtractor
    (by have := hd ▸ P.natDegree_modulus_pos; omega) K (fun w => w.z)

/-- **CWSS of `Lift`**, escape-threaded, at plain `k = 2d` special soundness: on every structured
accepting tree, either the tree exhibits a short collision of the commitment (`escEvent`) or
`treeExtractor` produces a witness of the input linear relation. Straight from the generic
committed-scalar certificate at `recover`. -/
theorem coordinateWiseSpecialSoundWithEscape [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.toPoly.natDegree = d)
    (short_zOk : ∀ s w, wShort w → sideCond s → zOk s w.z)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (scalarStructure (2 * d) (by have := hd ▸ P.natDegree_modulus_pos; omega))
      (escEvent P φF getM getY sideCond K hd)
      (relLin getM getY zOk) (relOut P φF getM getY sideCond K)
      (verifier (oSpec := oSpec) (F := F) K)
      (treeExtractor P K hd) :=
  CommittedScalar.coordinateWiseSpecialSoundWithEscape
    (by have := hd ▸ P.natDegree_modulus_pos; omega) K (fun w => w.z)
    (checkAt P φF getM getY sideCond) (relLin getM getY zOk)
    (fun s w fam hinj hcheck hshort =>
      recover P φF getM getY zOk sideCond hφF hd short_zOk s w fam hinj hcheck hshort)
    init impl

/-- `Lift` as a composable escape-aware CWSS package.

Computable: the purity field carries the verdict function as data (`PureForm`), and the extractor
is the witness-only committed-scalar assembler. -/
def package [IsPresentation P] (hφF : Function.Injective φF)
    (hd : P.modulus.toPoly.natDegree = d)
    (short_zOk : ∀ s w, wShort w → sideCond s → zOk s w.z)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    EscapeCWSSPackage init impl Stmt (PolyVec S μ)
      (CommittedScalar.Statement Stmt K.TCom F) (LiftedWitness R S d μ n)
      (pSpecScalar K.TCom F) where
  verifier := verifier K
  struct := scalarStructure (2 * d) (by have := hd ▸ P.natDegree_modulus_pos; omega)
  relIn := relLin getM getY zOk
  relOut := relOut P φF getM getY sideCond K
  esc := escEvent P φF getM getY sideCond K hd
  isPure := CommittedScalar.verifierPureForm K
  extractor := treeExtractor P K hd
  isCWSS := coordinateWiseSpecialSoundWithEscape P φF getM getY zOk sideCond K hφF hd
    short_zOk init impl

end Protocol

end RingSwitching.Lift
