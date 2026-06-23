/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.Simple.Scheme
import ArkLib.CommitmentScheme.Ajtai.Gadget
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds
import VCVio

/-!
# Inner-Outer Ajtai Commitment Scheme

The Greyhound [NS24] / Hachi [NOZ26] inner-outer commitment composition over the cyclotomic
ring `Rq Φ`:
each message block is gadget-decomposed and inner-committed under `A`; the inner
commitments are gadget-decomposed, flattened, and outer-committed under `B`.

## Weak openings

Following Hachi [NOZ26, §4.1], the opening carried by this scheme is a *weak opening*
`(sᵢ, t̂ᵢ, cᵢ)ᵢ`: per block `i` a (gadget-decomposed) message `sᵢ`, an inner decomposition
`t̂ᵢ`, and a *challenge* `cᵢ`. The challenge originates as the verifier's challenge in the
evaluation/opening protocol and is only ever recovered during knowledge extraction; it is not
something the committer chooses. We reflect this in the types: the committer-produced data
`(sᵢ, t̂ᵢ)` is the `Decomp` structure, and an `Opening` extends `Decomp` with the challenge.
The honest committer generates only the `Decomp` (`generateDecomps`); `commitmentScheme` pairs
it with the trivial challenge `cᵢ = 1`, the special case in which weak verification
(`verify_weak`) collapses to the ordinary honest check (`1` is invertible, `‖1‖₁ = 1`, and
`‖1·sᵢ‖ = ‖sᵢ‖`).

`verify_weak` checks, per block: the challenge is nonzero and `ℓ₁`-bounded (`0 < ‖cᵢ‖₁ ≤ κ`),
the scaled message is `ℓ₂²`-short (`‖cᵢ·sᵢ‖₂² ≤ βSq`), and the inner gadget relation
`A sᵢ = G t̂ᵢ` holds; and globally: the flattened inner decomposition is `ℓ∞`-short
(`‖t̂‖∞ ≤ γ`, matching Hachi [NOZ26, §4.1]) and outer-commits to `u`. Because the norms
`Rq.l1Norm`/`vecL2NormSq`/`vecLInftyNorm` are defined over `ZMod q`, `verify_weak` and the
bundled `commitmentScheme` live in the `ZMod q` section.

## The challenge condition `0 < ‖cᵢ‖₁` and invertibility

Hachi's weak opening [NOZ26, §4.1] requires the (extracted) challenge `cᵢ` to be *invertible*
in `Rq Φ` (`c̄ᵢ ∈ R_q^×`). We check the weaker `0 < ‖cᵢ‖₁` (i.e. `cᵢ ≠ 0`) here because
invertibility is not an independent hypothesis: it is a *consequence* of the shortness bound
`‖cᵢ‖₁ ≤ κ` via the Lyubashevsky–Seiler lemma [LS18] (short elements of `Rq Φ` are invertible,
formalized as `isUnit_of_l1Norm_le`). For `q ≡ 5 (mod 8)` and `κ` below the LS18 threshold, any
nonzero `cᵢ` with `‖cᵢ‖₁ ≤ κ` is automatically a unit, so the explicit nonzero check together
with the `ℓ₁` bound already pins down invertibility. The honest challenge `cᵢ = 1` is a unit.

## Deriving the message from a weak opening

A weak opening does not store the message: per Hachi [NOZ26, Eq. (13)] the message block is
*derived* from `sᵢ` by applying the message gadget matrix, `mᵢ = G · sᵢ` (`derivedMessage`).
The bundled `commitmentScheme` therefore verifies an opening against a claimed message `m` by
checking `derivedMessage opening.toDecomp = m` (replacing the old explicit message-gadget check)
together with `verify_weak`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai

namespace ArkLib.Lattices.Ajtai.InnerOuter

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

/-- Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`. -/
structure PublicParams (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) where
  /-- Inner Ajtai matrix `A`. -/
  innerMatrix : Simple.PublicParams Φ innerRows (messageRows * messageDigits)
  /-- Outer Ajtai matrix `B`. -/
  outerMatrix : Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits))

/-- The decomposition data `(sᵢ, t̂ᵢ)ᵢ` underlying an opening, *without* the challenge:
per-block gadget-decomposed messages `(sᵢ)` and inner decompositions `(t̂ᵢ)`. This is what the
honest committer produces (`generateDecomps`); a weak `Opening` extends it with a challenge. -/
structure Decomp (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Per-block (gadget-decomposed) messages `(sᵢ)`. -/
  message : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks
  /-- Per-block inner decompositions `(t̂ᵢ)`. -/
  innerDecomp : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks

/-- A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)`
(`Decomp`) extended with per-block challenges `(cᵢ)`. The challenge originates as the verifier's
challenge during knowledge extraction; in this scheme definition the committer pairs the
decomposition with the trivial challenge `cᵢ = 1` (see `commitmentScheme`). -/
structure Opening (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) extends
    Decomp Φ innerRows messageRows messageDigits blocks innerDigits where
  /-- Per-block challenges `(cᵢ)`. -/
  challenge : PolyVec (Rq Φ) blocks

/-- The decomposition operations used by the honest committer. -/
structure Decomposition (Φ : CyclotomicModulus R)
    (messageRows messageDigits innerRows innerDigits : Nat) where
  /-- Decompose one message block w.r.t. the message gadget. -/
  message : PolyVec (Rq Φ) messageRows → PolyVec (Rq Φ) (messageRows * messageDigits)
  /-- Decompose one inner commitment w.r.t. the inner gadget. -/
  inner : PolyVec (Rq Φ) innerRows → PolyVec (Rq Φ) (innerRows * innerDigits)

/-- The honest decomposition whose message and inner steps are both the Hachi gadget inverse
`G⁻¹` (`gadgetDecompose`) built from base-`b` digit decompositions. -/
def Decomposition.ofDigits [DecidableEq R] {base : R}
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits) :
    Decomposition Φ messageRows messageDigits innerRows innerDigits where
  message := gadgetDecompose Φ ddMsg
  inner := gadgetDecompose Φ ddInner

/-- Messages: block vectors over the message row space. -/
abbrev Message (Φ : CyclotomicModulus R) (messageRows blocks : Nat) :=
  PolyVec (PolyVec (Rq Φ) messageRows) blocks

/-- Inner-outer commitments live in the outer row space. -/
abbrev Commitment (Φ : CyclotomicModulus R) (outerRows : Nat) := Simple.Commitment Φ outerRows

/-- The message block derived from the decomposition data: `mᵢ = G · sᵢ`, the message gadget
matrix applied to the per-block decomposition (Hachi [NOZ26, Eq. (13)]). The decomposition does
not store the message; this recovers it. -/
def derivedMessage (base : R)
    (decomp : Decomp Φ innerRows messageRows messageDigits blocks innerDigits) :
    Message Φ messageRows blocks :=
  fun i => Simple.commit Φ (gadgetMatrix Φ base messageRows messageDigits) (decomp.message i)

/-- Honest decomposition generation from the supplied decomposition operations: per-block
messages `sᵢ = G⁻¹(mᵢ)` and inner decompositions `t̂ᵢ = G⁻¹(A sᵢ)`. No challenge is produced
here; the honest committer pairs this with the trivial challenge `cᵢ = 1` in `commitmentScheme`,
under which `verify_weak` reduces to the ordinary honest check. -/
def generateDecomps (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    Decomp Φ innerRows messageRows messageDigits blocks innerDigits :=
  let ss := fun i => decomp.message (m i)
  { message := ss
    innerDecomp := fun i => decomp.inner (Simple.commit Φ pp.innerMatrix (ss i)) }

/-- Compute the outer commitment from the decomposition data. -/
def commitWithDecomps
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (decomp : Decomp Φ innerRows messageRows messageDigits blocks innerDigits) :
    Commitment Φ outerRows :=
  Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks decomp.innerDecomp)

end Defs

/-! ## Weak verification and the bundled commitment scheme (over `ZMod q`)

The weak verifier and the bundled `CommitmentScheme` are pinned to `R = ZMod q`, since the
short-vector norms `Rq.l1Norm` and `vecL2NormSq` are only defined there. -/

section WeakScheme

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

/-- Verify a Hachi/Greyhound weak opening `(sᵢ, t̂ᵢ, cᵢ)ᵢ` against the outer commitment `u`.

Per block `i`: the challenge is nonzero and `ℓ₁`-short (`0 < ‖cᵢ‖₁ ≤ κ`), the scaled message
is `ℓ₂²`-short (`‖cᵢ·sᵢ‖₂² ≤ βSq`), and the inner gadget relation `A sᵢ = G t̂ᵢ` holds.
Globally: the flattened inner decomposition is `ℓ∞`-short (`‖t̂‖∞ ≤ γ`, as in
Hachi [NOZ26, §4.1]) and outer-commits to `u`.

The nonzero check `0 < ‖cᵢ‖₁` stands in for invertibility of `cᵢ`; the latter follows from the
`ℓ₁` bound by [LS18] (see the module docstring). -/
def verify_weak (base : ZMod q) (βSq γ κ : Nat)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment Φ outerRows)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    decide (0 < ‖opening.challenge i‖₁) &&
      decide (‖opening.challenge i‖₁ ≤ κ) &&
      decide (‖opening.challenge i •ᵥ opening.message i‖₂² ≤ βSq) &&
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        (opening.innerDecomp i) (Simple.commit Φ pp.innerMatrix (opening.message i)) ()) &&
    decide (vecLInftyNorm Φ (PolyVec.flattenBlocks opening.innerDecomp) ≤ γ) &&
    Simple.verify Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) u ()

variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

/-- The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound
weak verifier `verify_weak`.

Verification ties the claimed message `m` to the opening by deriving it via the message gadget
matrix (`derivedMessage opening = m`, i.e. `mᵢ = G · sᵢ`) and then running `verify_weak`. The
honest committer produces a weak opening with trivial challenge `cᵢ = 1`. -/
def commitmentScheme (base : ZMod q) (βSq γ κ : Nat)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits) :
    CommitmentScheme
      (PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message Φ messageRows blocks) (Commitment Φ outerRows)
      (Opening Φ innerRows messageRows messageDigits blocks innerDigits) where
  setup := do
    let A ← $ᵗ (Simple.PublicParams Φ innerRows (messageRows * messageDigits))
    let B ← $ᵗ (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))
    pure { innerMatrix := A, outerMatrix := B }
  commit pp m :=
    let decomps := generateDecomps Φ decomp pp m
    pure (commitWithDecomps Φ pp decomps, { toDecomp := decomps, challenge := fun _ => 1 })
    -- dummy challenge value c=1 here
  verify pp m c opening :=
    (List.finRange blocks).all (fun i =>
      decide (derivedMessage Φ base opening.toDecomp i = m i)) &&
      verify_weak Φ base βSq γ κ pp c opening

end WeakScheme

end ArkLib.Lattices.Ajtai.InnerOuter
