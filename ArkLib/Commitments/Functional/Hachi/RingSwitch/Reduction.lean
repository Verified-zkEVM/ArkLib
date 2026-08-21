/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Rlin
import ArkLib.Data.Lattices.CyclotomicRing.QuotientLift
import ArkLib.ProofSystem.RingSwitching.Lift.Reduction
import CompPoly.Univariate.ToPoly.Impl

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
  * the weak-binding `w̃`-commitment interface (`LiftCom`, whose short-collision set
    `LiftCom.Collision` is the escape event's hardness target).

  The name **Lift** refers to turning equality modulo `Φ.φ` into an exact polynomial
  equality with an explicit quotient witness. Its sibling is **Packing**, which instead
  encodes a basis-sized block of small-field coefficients as one large-field coefficient.

  This is intentionally a sibling of the DP24/Binius `Packing` switch
  (`ProofSystem/RingSwitching/Packing/`), not an instance of `RingSwitchingProfile`:
  packing a small-field polynomial into a larger field and evaluating a quotient presentation
  are different algebraic constructions (see the taxonomy in
  `ProofSystem/RingSwitching/Basic.lean`).

  Output relation `relLift`: an opening `w̃` of `t` whose lifted rows vanish at `α` and which is
  short. **CWSS at `k = 2d`** (`scalarStructure`, plain special soundness): each row's defect
  polynomial `∑ⱼ Mᵢⱼ·zⱼ − yᵢ − (X^d+1)·ρᵢ` has degree `≤ 2d − 1`, so `2d` accepting branches at
  pairwise-distinct `α` either exhibit two distinct short openings of `t` — the weak-binding
  **escape event** `CommittedScalar.escEvent` (`LiftCom.Collision`; [NOZ26] Remark 2 / Lemma 7) —
  or share one opening whose row defects have `2d` roots, hence vanish identically: `M z = y` over
  `Rq` plus the range bound, i.e. `relRlin` membership.

  Both halves of that argument are **proven generically**, one layer up: the interpolation descent
  is `RingSwitching.Lift.recover` over an arbitrary `Presentation`, and the collision/extraction
  dispatch is `CommittedScalar.mkWitness_mem`. This file supplies only the cyclotomic
  presentation (`cyclotomicPresentation`, `isPresentation_cyclotomic`), the challenge-local
  predicate (`liftCheckAt`), the norm bookkeeping (`vecLInftyNorm_le_of_liftShort`), and the
  resulting `liftPackage`.

  ## The commitment `LiftCom` and the norm bookkeeping

  The interface is abstract, so `LiftCom` carries nothing but `{TCom, com}` over its
  shortness index; `hachiLiftCom` below is the concrete Ajtai instantiation the nonrecursive
  chain runs at (see `Hachi/Concrete.lean`).
  Weak binding is **norm-conditioned**, hence that index: this chain instantiates
  `Short := liftShort bound ρBound` at the *global* norm parameters, and the short-collision set
  `LiftCom.Collision` — the target of the escape event — reads it. `relLift`
  therefore carries (i) `liftShort bound ρBound w̃` — feeding
  both the collision argument and, (ii) via the public sanity conjunct `bound ≤ s.bound`, the
  statement-level `R^lin` bound of the extraction target (assembled statements have
  `s.bound = γ = bound`, so completeness is unaffected). `hachiLiftCom` supplies the commitment
  map; what is still to come is the *soundness* side of that instantiation — discharging
  `LiftCom.Collision` by `outputToModuleSIS_valid_of_verified` ([NOZ26] §4.5) — and the
  commitment reinterpretation at the next ring dimension used by the recursion handoff
  (`Recursion/TraceHandoff.lean`).

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

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ}

/-! ## The cyclotomic presentation used by `Lift` -/

/-- `Rq Φ` presented by the cyclotomic modulus with canonical (reduced) representatives —
Hachi's instance of the generic `Lift.Presentation` data.  Proof-free, like
`CyclotomicModulus` itself; the laws are `isPresentation_cyclotomic`.

Two projections, hence a plain (computable) `def` — `CPolynomial` data all the way down. -/
def cyclotomicPresentation : Lift.Presentation (ZMod q) (Rq Φ) where
  modulus := Φ.φ
  rep a := a.1

omit [NeZero q] in
/-- The presentation degree is the ring dimension: `modulus` is `Φ.φ`, read through `toPoly`. -/
theorem cyclotomicPresentation_modulus_natDegree :
    (cyclotomicPresentation Φ).modulus.toPoly.natDegree = Φ.φ.natDegree :=
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
polynomial per row over `ZMod q` of degree at most `d − 1` (honest quotients satisfy the
tighter `d − 2`) — the generic lifted witness at the cyclotomic degree. -/
abbrev LiftedWitness (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) :=
  Lift.LiftedWitness (ZMod q) (Rq Φ) Φ.φ.natDegree μ n

/-- Coefficient-range predicate on the quotient polynomials.

Not consumed by any proof in this file: `liftPackage` discharges the generic `short_zOk` obligation
through `vecLInftyNorm_le_of_liftShort`, which needs only the `z`-side conjunct of `liftShort`.
`RhoShort` is a forward-compatibility hook modelling Figure 4's `‖r‖∞ ≤ b − 1` check, carried
through `relOut` for the digit layer (Lemma 10) that re-derives it. -/
def RhoShort (ρBound : ℕ) (ρ : Fin n → CPolynomial (ZMod q)) : Prop :=
  ∀ i k, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound

/-- Hachi's norm-conditioned admissibility predicate for a lifted opening. -/
def liftShort (bound ρBound : ℕ) (w : LiftedWitness Φ μ n) : Prop :=
  vecLInftyNorm Φ w.z ≤ bound ∧ RhoShort ρBound w.ρ

/-- Hachi's name for the reusable norm-conditioned binding interface. Weak binding is not a field:
it enters the certificate as the escape event `CommittedScalar.escEvent`, whose hardness target is
the short-collision set `LiftCom.Collision` ([NOZ26] Remark 2 / Lemma 7). -/
abbrev LiftCom (W : Type) (Short : W → Prop) :=
  CoordinateWise.BindingCommitment W Short

/-- The injective commitment witnesses that the abstraction is non-vacuous (its collision set is
empty, so the escape event never fires there). -/
example (bound ρBound : ℕ) :
    LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound) :=
  { TCom := LiftedWitness Φ μ n
    com := id }

/-! ### The concrete Ajtai instantiation of `LiftCom`

`hachiLiftCom` replaces the abstract commitment by the Eq. (16)-shaped Ajtai product, so the
nonrecursive chain has a `TCom` and a `com` an implementation can actually compute. Everything
here is a plain `def`: `Rq Φ` has a computable `CommRing` instance, `Simple.commit` is
`matVecMul`, and the quotient rows enter through `Polynomial.coeff` (reading a Mathlib
polynomial is computable, unlike building one).

**Why the lift needs its own key.** The obvious candidate for the matrix is `pp.dMatrix`, the
Eq. (16) short-commitment matrix that `keygen` already samples and that the `R^lin` statement's
c1 row consumes (`rlin_linear_iff`). Its width is wrong: `PublicParamsD.dMatrix` has
`blocks * messageDigits = rlinCW` columns — the *carrier slice* `ŵ` alone — whereas a lifted
witness is `μ + n` ring elements (`μ = rlinCW + (rlinCT + rlinCZ)` for the `R^lin` witness `z`,
plus one quotient row each). Committing under `pp.dMatrix` would therefore have to drop `ρ` and
two thirds of `z`, leaving a commitment whose `LiftCom.Collision` set is enormous and which the
deferred Module-SIS argument could never discharge. The c1 commitment and the lift's commitment
are different objects: c1 constrains the carrier decomposition inside the statement, the lift
binds the whole opening. So the key is taken as a parameter at the matching width; a full
treatment would sample it in `keygen` alongside `D`, which needs a new `PublicParamsD` field. -/

/-- A quotient row of a lifted witness, read back as a ring element. The rows have degree
`≤ d − 1` (`LiftedWitness.hρ`), so the reduced representative of degree `< d` loses nothing —
this is a change of presentation, not a reduction. Computable: `Polynomial.coeff` is a
projection out of the `Finsupp`, and `Rq.ofFinCoeff` builds the representative directly. -/
def rhoAsRq (p : Polynomial (ZMod q)) : Rq Φ :=
  Rq.ofFinCoeff Φ Φ.φ.natDegree p.coeff

/-- The message an Ajtai lift commitment binds: the whole lifted witness as one `Rq`-vector,
the `R^lin` witness followed by the quotient rows. This is Figure 4's `(z, r)`; the full
protocol's base-`b` digit decomposition of the quotient block sits between this and the paper's
Lemma 10, and is the downstream constraint layer's business (see the paper-model boundary note
in the module docstring). -/
def liftMessage (w : LiftedWitness Φ μ n) : ArkLib.Lattices.PolyVec (Rq Φ) (μ + n) :=
  Fin.append w.z (fun i => rhoAsRq Φ (w.ρ i))

/-- **The concrete lift commitment**: the Ajtai product `D · (z ‖ ρ)` at a key of the matching
width. Computable, so the whole nonrecursive chain can be run once its other links are; and a
genuine Module-SIS shape, so the deferred escape-event argument has a real target — a member of
`LiftCom.Collision` here is a short nonzero kernel vector of `D`. -/
def hachiLiftCom {dRows : ℕ} (bound ρBound : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n)) :
    LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound) where
  TCom := Simple.Commitment Φ dRows
  com := fun w => Simple.commit Φ D (liftMessage Φ w)

/-- The concrete commitment's space is the same `PolyVec (Rq Φ) dRows` the chain already carries
as `CarrierCom`, so `DecidableEq` is derivable and the terminal check's instance argument is
discharged without `Classical.dec`. Holds by `rfl`. -/
@[simp] theorem hachiLiftCom_TCom {dRows : ℕ} (bound ρBound : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n)) :
    (hachiLiftCom Φ (n := n) (μ := μ) bound ρBound D).TCom = CarrierCom Φ dRows := rfl

/-- The concrete commitment map, unfolded. Holds by `rfl`. -/
@[simp] theorem hachiLiftCom_com {dRows : ℕ} (bound ρBound : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n)) (w : LiftedWitness Φ μ n) :
    (hachiLiftCom Φ (n := n) (μ := μ) bound ρBound D).com w
      = Simple.commit Φ D (liftMessage Φ w) := rfl

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

/-- The computable `i`-th lifted row
`∑ⱼ Mᵢⱼ(X)·zⱼ(X) ∈ Zq[X]`, formed from the canonical `CPolynomial` representatives. -/
def cRowSum (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    CPolynomial (ZMod q) :=
  ∑ j, (s.M i j).1 * (z j).1

/-- Computable evaluation of a `Zq[X]` polynomial at `a ∈ F` through the base-field embedding. -/
def cEvalAt (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) : F :=
  p.eval₂ φF a

/-- Mathlib view of `cRowSum`, retained for degree and root-counting proofs. -/
noncomputable def rowSum (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    Polynomial (ZMod q) :=
  (cRowSum Φ s z i).toPoly

omit [NeZero q] [IsCyclotomic Φ] in
/-- `rowSum` is the expected Mathlib sum of products of canonical representatives. -/
theorem rowSum_eq_sum_toPoly (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    rowSum Φ s z i = ∑ j, (s.M i j).1.toPoly * (z j).1.toPoly := by
  unfold rowSum cRowSum
  rw [CPolynomial.toPoly_sum]
  exact Finset.sum_congr rfl fun j _ => CPolynomial.toPoly_mul _ _

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable and Mathlib row-sum evaluations agree. The Mathlib side is the generic
`RingSwitching.evalAt` that `Lift.checkAt` is stated against, so this is the bridge between the
computable row encoding and the presentation layer. -/
theorem cEvalAt_cRowSum_eq_evalAt (φF : ZMod q →+* F) (a : F)
    (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    cEvalAt φF a (cRowSum Φ s z i) = evalAt φF a (rowSum Φ s z i) := by
  exact CPolynomial.eval₂_toPoly φF a (cRowSum Φ s z i)

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- Evaluation of any computable polynomial agrees with evaluation of its Mathlib image. -/
theorem cEvalAt_eq_evalAt_toPoly (φF : ZMod q →+* F) (a : F)
    (p : CPolynomial (ZMod q)) :
    cEvalAt φF a p = evalAt φF a p.toPoly := by
  exact CPolynomial.eval₂_toPoly φF a p

/-- The Hachi output relation, instantiated from the generic anchored committed-scalar relation. -/
def relLift (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  CommittedScalar.rel K (liftCheckAt Φ bound φF)

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
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

/-- Hachi's `Lift` instance as a composable CWSS package, reusing the generic ring-switching
`Lift.package` at the cyclotomic presentation. Hachi supplies only the presentation data
(`cyclotomicPresentation`/`isPresentation_cyclotomic`) and the norm implication
(`vecLInftyNorm_le_of_liftShort`); the CWSS certificate is `liftPackage.isCWSS`.

**Why the certificate is a package field, not a standalone theorem.** `isCWSS` is the uniform
`EscapeCWSSPackage` field (`.../CoordinateWiseSpecialSoundness/Escape.lean`), and it is the field —
not any named theorem — that the chain composition operator `▷` consumes: every link in the Hachi
opening chain (`QuadEval/Bridge.lean`, `QuadEval/Soundness.lean`, `Sumcheck/Rounds.lean`,
`ZeroCheck/Reduction.lean`, …) exposes its certificate the same way,
and `iteration.isCWSS` is assembled from them in `Composition.lean`. Because this package is
built wholesale from generic `Lift.package`, its certificate already arrives in that shape, stated
in the generic `Lift` vocabulary. Restating it as a standalone theorem over Hachi's own
`relRlin`/`relLift` at `Rq Φ` would duplicate the proposition without adding content and would sit
outside the composition
interface, so nothing would consume it. -/
def liftPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    EscapeCWSSPackage init impl
      (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (pSpecScalar K.TCom F) :=
  haveI := isPresentation_cyclotomic Φ hd
  Lift.package (cyclotomicPresentation Φ) φF (fun s => s.M) (fun s => s.yvec)
    (fun s z => vecLInftyNorm Φ z ≤ s.bound) (fun s => bound ≤ s.bound) K
    φF.injective (cyclotomicPresentation_modulus_natDegree Φ)
    (fun s w hshort hside => vecLInftyNorm_le_of_liftShort Φ bound ρBound s w hshort hside)
    init impl

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
