/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Rlin
import ArkLib.Commitments.Functional.Hachi.RingSwitch.RhoDigits
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
  `Short := liftShort bound bDig` at the *global* norm parameters, and the short-collision set
  `LiftCom.Collision` — the target of the escape event — reads it. `relLift`
  therefore carries (i) `liftShort bound bDig w̃` — feeding
  both the collision argument and, (ii) via the public sanity conjunct `bound ≤ s.bound`, the
  statement-level `R^lin` bound of the extraction target (assembled statements have
  `s.bound = γ = bound`, so completeness is unaffected). At the concrete instantiation
  `hachiLiftCom`, a short collision is a Module-SIS solution for the key `D`
  (`moduleSIS_relation_of_mem_Collision`).

  ## Paper-model boundary — closed

  Figure 4's *simplified* presentation commits to `(z, r)`; the full protocol decomposes the
  quotient into short base-`b` digits before commitment. That decomposition lives **here**:
  `rhoDigits` (`RingSwitch/RhoDigits.lean`) is the encoding, `liftMessage` commits it, and
  `RhoDigitsShort` is the admissibility it satisfies — unconditionally, at radius `⌊b/2⌋`
  (`rhoDigitsShort_of_digitBaseOk`). `RhoShort` is the vocabulary of the *raw* quotient growth
  bounds in `QuotientNorms.lean`, which the encoding makes irrelevant to the commitment.

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

/-- Coefficient-range predicate on the **raw** quotient polynomials.

Not part of `liftShort`: the committed vector carries the quotient's base-`b` digits, not the
quotient itself, so admissibility there is `RhoDigitsShort`. This predicate is the vocabulary of the
raw coefficient-growth bounds in `RingSwitch/QuotientNorms.lean` — statements about how large an
*undecomposed* quotient can get. It is what `rhoShort_half` bounds, and that bound's `q/2` is
exactly the parameter degeneracy the digit encoding avoids. -/
def RhoShort (ρBound : ℕ) (ρ : Fin n → CPolynomial (ZMod q)) : Prop :=
  ∀ i k, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound

/-- Coefficient-range predicate on the quotient **digits** ([NOZ26] §4.3): every coefficient of
every base-`b` digit of every quotient row is `bound`-bounded.

This is what the committed vector's quotient block actually contains, so this — not `RhoShort` — is
the half of `liftShort` that the Eq. (20) range check certifies and that bounds the Module-SIS
escape target. Unlike `RhoShort ρBound`, it is satisfiable at `bound = O(b)`: by
`rhoDigits_valMinAbs_natAbs_le` the balanced digits of an *arbitrary* quotient are `⌊b/2⌋`-bounded,
with no shortness hypothesis on the quotient at all. -/
def RhoDigitsShort (bound bDig : ℕ) (ρ : Fin n → CPolynomial (ZMod q)) : Prop :=
  ∀ (i : Fin n) (u : Fin (rhoDigitCount q bDig)) (k : ℕ),
    ((rhoDigits Φ bDig (ρ i) (u : ℕ)).coeff k).valMinAbs.natAbs ≤ bound

/-- **Admissibility of a digit base** at a given norm bound. Three conditions, bundled because
every link that consumes the digit encoding needs exactly this triple:

* `one_lt` — a base of `0` or `1` is not a decomposition (`rhoDigits_reconstruct`);
* `le_half` — anti-wraparound, so a balanced digit *is* the centered representative
  (`balancedZmodDigit_valMinAbs_mem`);
* `radius_le` — the digit radius `⌊bDig/2⌋` fits inside the declared bound.

Under them the quotient half of `liftShort` costs nothing at all
(`rhoDigitsShort_of_digitBaseOk`), for an arbitrary quotient. That is the parameter choice stated
as a hypothesis class: with the raw quotient the corresponding condition was
`q/2 ≤ bound` (`rhoShort_half`), which is what pinned `γ = q/2 = bZero − 1`. -/
structure DigitBaseOk (q bound bDig : ℕ) : Prop where
  /-- The digit base is nontrivial. -/
  one_lt : 1 < bDig
  /-- Anti-wraparound: balanced digits are centered representatives. -/
  le_half : bDig ≤ q / 2
  /-- The digit radius fits the declared norm bound. -/
  radius_le : bDig / 2 ≤ bound

omit [NeZero q] [IsCyclotomic Φ] in
/-- **The digit encoding is short by construction.** For *any* quotient family whatever — no
shortness hypothesis, no assumption that the commitment key is short — the balanced base-`b`
digits are `⌊b/2⌋`-bounded, so `RhoDigitsShort` holds at every `bound ≥ ⌊b/2⌋`.

This is the exact counterpart of `rhoShort_half` (`QuotientNorms.lean`), and the contrast is the
parameter choice in one line: the raw quotient could only be bounded by `q/2`, its digits are
bounded by `⌊b/2⌋ = O(b)`. -/
theorem rhoDigitsShort_of_half_le {bound bDig : ℕ} (hb : 1 < bDig) (hbq : bDig ≤ q / 2)
    (hbound : bDig / 2 ≤ bound) (ρ : Fin n → CPolynomial (ZMod q)) :
    RhoDigitsShort Φ bound bDig ρ :=
  fun i u k => le_trans (rhoDigits_valMinAbs_natAbs_le Φ hb hbq (ρ i) u.isLt k) hbound

omit [NeZero q] [IsCyclotomic Φ] in
/-- `rhoDigitsShort_of_half_le` at a bundled admissible base — the form the links consume. -/
theorem rhoDigitsShort_of_digitBaseOk {bound bDig : ℕ} (h : DigitBaseOk q bound bDig)
    (ρ : Fin n → CPolynomial (ZMod q)) :
    RhoDigitsShort Φ bound bDig ρ :=
  rhoDigitsShort_of_half_le Φ h.one_lt h.le_half h.radius_le ρ

/-- Hachi's norm-conditioned admissibility predicate for a lifted opening: a **single** bound on
every entry of the committed vector `z ‖ digits(ρ)` — the paper's weak-opening condition
`S_b` (Fig. 3 / Lemma 7).

A single bound suffices because the quotient block is committed as digits (see `RhoDigitsShort`).
Committing it raw would need a second, separate bound, and that bound could only be `q/2`
(`rhoShort_half`), forcing `γ = bZero − 1 = q/2` and emptying both the range check and the escape
target of content. -/
def liftShort (bound bDig : ℕ) (w : LiftedWitness Φ μ n) : Prop :=
  vecLInftyNorm Φ w.z ≤ bound ∧ RhoDigitsShort Φ bound bDig w.ρ

/-- Hachi's name for the reusable norm-conditioned binding interface. Weak binding is not a field:
it enters the certificate as the escape event `CommittedScalar.escEvent`, whose hardness target is
the short-collision set `LiftCom.Collision` ([NOZ26] Remark 2 / Lemma 7). -/
abbrev LiftCom (W : Type) (Short : W → Prop) :=
  CoordinateWise.BindingCommitment W Short

/-- The injective commitment witnesses that the abstraction is non-vacuous (its collision set is
empty, so the escape event never fires there). -/
example (bound bDig : ℕ) :
    LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig) :=
  { TCom := LiftedWitness Φ μ n
    com := id }

/-! ### The concrete Ajtai instantiation of `LiftCom`

`hachiLiftCom` replaces the abstract commitment by the Eq. (16)-shaped Ajtai product, so the
nonrecursive chain has a `TCom` and a `com` an implementation can actually compute. Everything
here is a plain `def`: `Rq Φ` has a computable `CommRing` instance, `Simple.commit` is
`matVecMul`, and the quotient rows enter through `CPolynomial.coeff` — computable coefficient
arrays all the way down.

**Why the lift needs its own key.** The obvious candidate for the matrix is `pp.dMatrix`, the
Eq. (16) short-commitment matrix that `keygen` already samples and that the `R^lin` statement's
c1 row consumes (`rlin_linear_iff`). Its width is wrong: `PublicParamsD.dMatrix` has
`blocks * messageDigits = rlinCW` columns — the *carrier slice* `ŵ` alone — whereas the committed
vector of a lifted witness is `μ + n·δ` ring elements (`μ = rlinCW + (rlinCT + rlinCZ)` for the
`R^lin` witness `z`, plus `δ = clog_b q` digit rows per quotient row). Committing under
`pp.dMatrix` would therefore have to drop `ρ` and two thirds of `z`, leaving a commitment whose
`LiftCom.Collision` set is enormous and carries no Module-SIS content. The c1 commitment and the
lift's commitment are different objects: c1 constrains the carrier decomposition inside the
statement, the lift binds the whole opening. The key is therefore a parameter at the matching
width; sampling it in `keygen` alongside `D` would need a new `PublicParamsD` field. -/

/-- A quotient row of a lifted witness, read back as a ring element. The rows have degree
`≤ d − 1` (`LiftedWitness.hρ`), so the reduced representative of degree `< d` loses nothing —
this is a change of presentation, not a reduction. Computable: `CPolynomial.coeff` reads the
coefficient array, and `Rq.ofFinCoeff` builds the representative directly. -/
def rhoAsRq (p : CPolynomial (ZMod q)) : Rq Φ :=
  Rq.ofFinCoeff Φ Φ.φ.natDegree p.coeff

/-- Entry `j` of the quotient block of the committed vector: `j` is the flattened `(row, digit)`
index, split by `finProdFinEquiv` into row `j / δ` and digit `j % δ` — the same flattening the
gadget matrix uses (`gadgetEntry_finProdFinEquiv`), so the block is laid out digit-major within
each row, exactly as `wTable`'s widened quotient rows read it. -/
def rhoDigitAsRq (b : ℕ) (ρ : Fin n → CPolynomial (ZMod q)) (j : Fin (n * rhoDigitCount q b)) :
    Rq Φ :=
  rhoAsRq Φ (rhoDigits Φ b (ρ (finProdFinEquiv.symm j).1) ((finProdFinEquiv.symm j).2 : ℕ))

/-- The message an Ajtai lift commitment binds: the `R^lin` witness `z`, followed by the `n·δ`
**digits** of the quotient rows. This is [NOZ26] §4.3's `(z, r₁, …, r_δ)`, the encoding the paper
commits to and then drops the digit subscript from ("there is a hidden gadget decomposition
of `r`").

Committing the digits rather than Figure 4's raw `(z, r)` is the whole point of the wire format:
every entry of the quotient block is `⌊b/2⌋`-bounded by construction
(`rhoDigits_valMinAbs_natAbs_le`), so `LiftCom.Collision` is a *short* kernel problem for `D`. With
the raw quotient the block was only `q/2`-bounded, and the Module-SIS target was trivially
solvable. -/
def liftMessage (b : ℕ) (w : LiftedWitness Φ μ n) :
    ArkLib.Lattices.PolyVec (Rq Φ) (μ + n * rhoDigitCount q b) :=
  Fin.append w.z (rhoDigitAsRq Φ b w.ρ)

/-- **The concrete lift commitment**: the Ajtai product `D · (z ‖ ρ)` at a key of the matching
width. Computable, so the whole nonrecursive chain runs; and a genuine Module-SIS shape, since a
member of `LiftCom.Collision` here is a short nonzero kernel vector of `D`. -/
def hachiLiftCom {dRows : ℕ} (bound bDig : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n * rhoDigitCount q bDig)) :
    LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig) where
  TCom := Simple.Commitment Φ dRows
  com := fun w => Simple.commit Φ D (liftMessage Φ bDig w)

/-! ### What the digit encoding buys the escape target

The point of committing digits rather than the raw quotient, stated rather than left implicit:
*every* coordinate of the committed vector of a short opening is bounded by the single norm
parameter `bound`, so a short collision satisfies `ModuleSIS.relation` for the key `D` at radius
`2·bound` — nonzero, short, and in the kernel
(`moduleSIS_relation_of_mem_Collision`, via `liftMessage_injective`).

Under Figure 4's simplified wire format this fails where it matters. A quotient block of raw rows
has only the unconditional bound `q/2` (`rhoShort_half`, and sharp — the `R^lin` matrix carries the
Ajtai key blocks), so the collision set would contain pairs differing by a vector of `ℓ∞` norm up to
`q`: no restriction at all over `ZMod q`, leaving `LiftCom.Collision` trivially inhabited by
short-in-name-only openings and undischargeable by any Module-SIS assumption. -/

omit [NeZero q] in
/-- A quotient-shaped `CPolynomial`, read into `Rq Φ`, inherits any coefficient bound it has. -/
theorem lInftyNorm_rhoAsRq_le {bound : ℕ} (p : CPolynomial (ZMod q))
    (h : ∀ k, (p.coeff k).valMinAbs.natAbs ≤ bound) :
    Rq.lInftyNorm Φ (rhoAsRq Φ p) ≤ bound := by
  refine Finset.sup_le fun k hk => ?_
  rw [show (rhoAsRq Φ p).1.coeff k = _ from
    Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ) k, if_pos (Finset.mem_range.mp hk)]
  exact h k

omit [NeZero q] in
/-- **Every coordinate of a short opening's committed vector is `bound`-bounded** — the `z` block by
the `ℓ∞` conjunct of `liftShort`, the `n·δ` quotient-digit block by its `RhoDigitsShort` conjunct.

This is the whole content of the gadget decomposition at the commitment layer: it is what makes the
Ajtai product `D · (z ‖ digits)` a *short* product, hence its collisions Module-SIS solutions. -/
theorem vecLInftyNorm_liftMessage_le (bound bDig : ℕ) (w : LiftedWitness Φ μ n)
    (h : liftShort Φ bound bDig w) :
    vecLInftyNorm Φ (liftMessage Φ bDig w) ≤ bound := by
  refine Finset.sup_le fun j _ => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [show liftMessage Φ bDig w (Fin.castAdd (n * rhoDigitCount q bDig) j) = w.z j from
      Fin.append_left _ _ j]
    exact le_trans (Finset.le_sup (f := fun i => Rq.lInftyNorm Φ (w.z i)) (Finset.mem_univ j))
      h.1
  · rw [show liftMessage Φ bDig w (Fin.natAdd μ j) = rhoDigitAsRq Φ bDig w.ρ j from
      Fin.append_right _ _ j]
    exact lInftyNorm_rhoAsRq_le Φ _ (fun k => h.2 _ _ k)

omit [NeZero q] in
/-- **The kernel and norm halves of the Module-SIS solution hidden in a short collision.** The two
committed vectors have the same Ajtai image, so their difference lies in the kernel of `D`, and each
is `bound`-bounded coordinatewise (`vecLInftyNorm_liftMessage_le`), so the difference is
`2·bound`-bounded (`sub_lInftyNorm_le`).

This is two of the three conjuncts of `ModuleSIS.relation`; the third — that the difference is
**nonzero** — needs injectivity of `liftMessage` and is supplied by
`moduleSIS_relation_of_mem_Collision`, which is the statement to cite. -/
theorem mulVec_sub_eq_zero_of_mem_Collision {dRows : ℕ} (bound bDig : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n * rhoDigitCount q bDig))
    {p : LiftedWitness Φ μ n × LiftedWitness Φ μ n}
    (hp : p ∈ (hachiLiftCom Φ (n := n) (μ := μ) bound bDig D).Collision) :
    D *ᵥ (liftMessage Φ bDig p.1 - liftMessage Φ bDig p.2) = 0 ∧
      vecLInftyNorm Φ (liftMessage Φ bDig p.1 - liftMessage Φ bDig p.2)
        ≤ subLInftyNormBound bound := by
  obtain ⟨-, hcom, hs1, hs2⟩ := hp
  refine ⟨?_, sub_lInftyNorm_le Φ _ _ (vecLInftyNorm_liftMessage_le Φ bound bDig _ hs1)
    (vecLInftyNorm_liftMessage_le Φ bound bDig _ hs2)⟩
  rw [matVecMul_sub, sub_eq_zero]
  exact hcom

omit [NeZero q] in
/-- **The committed vector determines the opening**, at any base that is genuinely a base.

The `z` block is read back verbatim; the quotient block is read back by *reconstruction*
(`balancedDigit_reconstruct`): the `δ` digits of each coefficient recombine to it under the weights
`b^u`, so agreeing digit blocks force agreeing quotient coefficients below `deg φ`, and above
`deg φ` both quotients vanish by `LiftedWitness.hρ`. `1 < bDig` is exactly what makes the digit
expansion a decomposition rather than a truncation; nothing else is needed.

This is the third conjunct of Module-SIS: without it a collision would only give a *short kernel
vector*, which the zero vector also is. -/
theorem liftMessage_injective {bDig : ℕ} (hb : 1 < bDig) (hd : 0 < Φ.φ.natDegree) :
    Function.Injective (liftMessage Φ (μ := μ) (n := n) bDig) := by
  rintro ⟨z₁, ρ₁, hd₁⟩ ⟨z₂, ρ₂, hd₂⟩ h
  -- Past `deg φ` a quotient row vanishes, so only the coefficients the digits carry matter.
  have hzero : ∀ ρ : Fin n → CPolynomial (ZMod q),
      (∀ i, (ρ i).toPoly.natDegree ≤ Φ.φ.natDegree - 1) →
      ∀ i k, ¬ k < Φ.φ.natDegree → (ρ i).coeff k = 0 := by
    intro ρ hdeg i k hk
    rw [CPolynomial.coeff_toPoly]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i) (by omega))
  have hz : z₁ = z₂ := by
    funext j
    have hj := congrFun h (Fin.castAdd (n * rhoDigitCount q bDig) j)
    simpa only [liftMessage, Fin.append_left] using hj
  have hρ : ρ₁ = ρ₂ := by
    funext i
    rw [CPolynomial.eq_iff_coeff]
    intro k
    by_cases hk : k < Φ.φ.natDegree
    · -- Below `deg φ`: every digit of the two coefficients agrees, so they reconstruct equal.
      have hdig : ∀ u : Fin (rhoDigitCount q bDig),
          balancedDigit bDig (rhoDigitCount q bDig) ((ρ₁ i).coeff k) (u : ℕ)
            = balancedDigit bDig (rhoDigitCount q bDig) ((ρ₂ i).coeff k) (u : ℕ) := by
        intro u
        have hj := congrFun h (Fin.natAdd μ (finProdFinEquiv (i, u)))
        simp only [liftMessage, Fin.append_right, rhoDigitAsRq, Equiv.symm_apply_apply] at hj
        have hc := congrArg (fun a : Rq Φ => a.1.coeff k) hj
        simpa only [rhoAsRq, Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ) k,
          if_pos hk, rhoDigits_coeff] using hc
      have hrec := balancedDigit_reconstruct (q := q) hb (Nat.le_pow_clog hb q)
      rw [← hrec ((ρ₁ i).coeff k), ← hrec ((ρ₂ i).coeff k)]
      exact Finset.sum_congr rfl fun u _ => by rw [hdig u]
    · rw [hzero ρ₁ hd₁ i k hk, hzero ρ₂ hd₂ i k hk]
  subst hz; subst hρ; rfl

omit [NeZero q] in
/-- **A short collision of `hachiLiftCom` *is* a Module-SIS solution for the key `D`**, at radius
`2·bound`: the difference of the two committed vectors is nonzero (`liftMessage_injective`, using
`hp`'s `p.1 ≠ p.2`), `2·bound`-short, and in the kernel of `D`.

This is the statement the gadget decomposition of the quotient exists to make true: it is what
turns a weak-binding collision of the lift commitment into a hardness instance.

The reduction is stated *for the key `D` it is given*, which is a parameter of `hachiLiftCom`
rather than something `keygen` samples (see "Why the lift needs its own key" above).

At the chain's parameters `bound = γ = O(b)` (`HonestRangeParams.ofPinnedDigitBase`), so the
radius is `O(b)`. Committing the raw quotient instead leaves the norm conjunct vacuous — see the
section note above — and the solution worthless even though the other two conjuncts still hold. -/
theorem moduleSIS_relation_of_mem_Collision {dRows : ℕ} (bound bDig : ℕ)
    (hdig : DigitBaseOk q bound bDig) (hd : 0 < Φ.φ.natDegree)
    (D : Simple.PublicParams Φ dRows (μ + n * rhoDigitCount q bDig))
    {p : LiftedWitness Φ μ n × LiftedWitness Φ μ n}
    (hp : p ∈ (hachiLiftCom Φ (n := n) (μ := μ) bound bDig D).Collision) :
    ModuleSIS.relation Φ (fun v => decide (vecLInftyNorm Φ v ≤ subLInftyNormBound bound)) D
      (liftMessage Φ bDig p.1 - liftMessage Φ bDig p.2) = true := by
  have hker := mulVec_sub_eq_zero_of_mem_Collision Φ bound bDig D hp
  obtain ⟨hne, -, -, -⟩ := hp
  refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [decide_eq_true_iff, sub_ne_zero]
    exact fun hEq => hne (liftMessage_injective Φ hdig.one_lt hd hEq)
  · rw [decide_eq_true_iff]; exact hker.2
  · rw [decide_eq_true_iff]; exact hker.1

/-- Output statement: the input `R^lin` claim, the opening commitment, and evaluation point. -/
abbrev LiftStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) : Type :=
  CommittedScalar.Statement (RlinStatement Φ n μ) TCom F

variable {F : Type} [Field F] (bound bDig : ℕ)

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
def relLift (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  CommittedScalar.rel K (liftCheckAt Φ bound φF)

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
  (φF : ZMod q →+* F)

omit [NeZero q] [IsCyclotomic Φ] in
/-- The **sole Hachi-specific obligation** of Lemma 9 in the generic-consumption model: the
norm implication. A short lifted witness (`‖z‖∞ ≤ bound`) at a statement whose public bound
dominates (`bound ≤ s.bound`) has `‖z‖∞ ≤ s.bound`. This is exactly generic `Lift`'s
`short_zOk` hypothesis; the interpolation/descent recovery and the escape/collision extractor
are supplied by the generic layer. -/
theorem vecLInftyNorm_le_of_liftShort (s : RlinStatement Φ n μ) (w : LiftedWitness Φ μ n)
    (hshort : liftShort Φ bound bDig w) (hside : bound ≤ s.bound) :
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
    (fun s w hshort hside => vecLInftyNorm_le_of_liftShort Φ bound bDig s w hshort hside)
    init impl

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
