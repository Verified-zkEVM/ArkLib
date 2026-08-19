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

/-! ### The honest prover and completeness -/

/-- **The honest lifted witness** of a quotient-evaluation switch: the `R^lin` witness `z` together
with the per-row honest quotients `ρᵢ := (rowSumᵢ − rep yᵢ) /ₘ φ` (`Presentation.quotient`).

This is the honest prover's `computeW`, and it is total: the degree field is discharged by the
*unconditional* `Presentation.natDegree_quotient_le`, so no validity of the input statement is
needed to build the witness — validity is what makes it satisfy `checkAt`
(`checkAt_honestWitness`). `noncomputable` as stated: the quotients are Mathlib polynomials
obtained by division (`Presentation.quotient`), repackaged as canonical coefficient arrays by
`Polynomial.toImpl`; an executable prover restates the division over `CPolynomial` and transfers
by an agreement lemma. -/
noncomputable def honestWitness [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d)
    (s : Stmt) (z : PolyVec S μ) : LiftedWitness R S d μ n where
  z := z
  ρ := fun i => ⟨(P.quotient (getM s) z (getY s) i).toImpl,
    CPolynomial.Raw.isCanonical_toImpl _⟩
  hρ := fun i => by
    rw [CPolynomial.toPoly_mk_toImpl]
    have h := P.natDegree_quotient_le (getM s) z (getY s) i
    omega

/-- **The honest opening passes the local check at every challenge.** At a valid statement
(`getM s *ᵥ z = getY s`) the honest quotients turn each row into an exact `R[X]` identity
(`Presentation.rowSum_eq_of_mulVec_eq`), and `evalAt φF a` is a ring homomorphism, so the identity
survives evaluation at *any* point `a`.

Quantifying over all `a` is what makes the completeness error of a quotient-evaluation switch
exactly `0`: the honest prover has nothing to fear from the challenge. The `sideCond` conjunct is
statement-level and is passed straight through. -/
theorem checkAt_honestWitness [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d)
    (s : Stmt) (z : PolyVec S μ) (hz : getM s *ᵥ z = getY s) (hside : sideCond s) (a : F) :
    checkAt P φF getM getY sideCond s a (honestWitness P getM getY hd s z) := by
  refine ⟨fun i => ?_, hside⟩
  rw [show (honestWitness P getM getY hd s z).z = z from rfl,
    show ((honestWitness P getM getY hd s z).ρ i).toPoly
      = P.quotient (getM s) z (getY s) i from CPolynomial.toPoly_mk_toImpl _,
    P.rowSum_eq_of_mulVec_eq (congrFun hz i), map_add, map_mul]

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

/-- **The switch as a protocol object**: the honest prover at `honestWitness` paired with the
statement-extending verifier, i.e. the committed-scalar protocol of this phase. Its verifier is
`verifier K` on the nose (`reduction_verifier`), the verifier `package` certifies, so the two
security directions of the switch cannot drift onto different verifiers. -/
noncomputable def reduction [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d) :
    Reduction oSpec Stmt (PolyVec S μ) (CommittedScalar.Statement Stmt K.TCom F)
      (LiftedWitness R S d μ n) (pSpecScalar K.TCom F) :=
  CommittedScalar.reduction K (honestWitness P getM getY hd)

omit [Field F] in
/-- The protocol object's verifier is the certified one. Holds by `rfl`. -/
@[simp] theorem reduction_verifier [IsPresentation P] (hd : P.modulus.toPoly.natDegree = d) :
    (reduction (oSpec := oSpec) P getM getY K hd).verifier = verifier (oSpec := oSpec) (F := F) K :=
  rfl

/-- **Perfect completeness of a quotient-evaluation switch**, at error exactly `0`.

Two hypotheses, both genuinely instance-side and neither provable at this generality:

* `hside` — the statement-level side condition holds at the statements the switch is run on (for
  Hachi: the global norm parameter is dominated by the statement's public bound). It is not part of
  `relLin`, so completeness cannot derive it.
* `hshort` — the honest lifted witness is **admissible** for the commitment's shortness regime
  `wShort`. This is the honest-side range check of the paper's figure (Hachi Figure 4's
  `‖z‖∞ ≤ b − 1`, `‖r‖∞ ≤ b − 1`): a statement about the honest quotients' coefficient growth at
  the concrete parameters, which the abstract `wShort` cannot see. Note the direction of the
  asymmetry — `relLin`'s `zOk` bounds `z` by the *statement's* bound, while `wShort` bounds it by
  the *protocol's*, so even the `z`-half does not follow.

Everything else — commitment consistency, the check at every challenge, the impossibility of
failure — is discharged generically by `CommittedScalar.reduction_perfectCompleteness` and
`checkAt_honestWitness`. -/
theorem reduction_perfectCompleteness [IsPresentation P] [SampleableType F]
    (hd : P.modulus.toPoly.natDegree = d)
    (hside : ∀ s z, (s, z) ∈ relLin getM getY zOk → sideCond s)
    (hshort : ∀ s z, (s, z) ∈ relLin getM getY zOk →
      wShort (honestWitness P getM getY hd s z))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (reduction (oSpec := oSpec) P getM getY K hd).perfectCompleteness init impl
      (relLin getM getY zOk) (relOut P φF getM getY sideCond K) :=
  CommittedScalar.reduction_perfectCompleteness K (honestWitness P getM getY hd)
    (checkAt P φF getM getY sideCond) (relLin getM getY zOk)
    (fun s z hIn a =>
      checkAt_honestWitness P φF getM getY sideCond hd s z hIn.1 (hside s z hIn) a)
    (fun s z hIn => hshort s z hIn) init impl

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
