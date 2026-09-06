/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.Commitments.Functional.Hachi.EvalSplit
import ArkLib.ProofSystem.Component.ReduceClaim
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape

/-!
  # Polynomial-level bridge into Hachi's `QuadEval` reduction

  `QuadEval/Reduction.lean` (Hachi Lemma 8, proven in `QuadEval/Soundness.lean`) states its
  evaluation claim over *opaque* Eq. (12) basis vectors `avec`/`bvec` — it never mentions
  `CMlPolynomial` (a computable multilinear polynomial, stored as its coefficient vector).
  `EvalSplit.lean` proves that a multilinear evaluation factors as the split bilinear form
  of a reshaped coefficient matrix against the monomial tensor bases (`evalSplit_eq_eval`,
  `splitForm_monomialBasis_eq_eval`), but nothing connects the two.

  This module is the connective tissue: a zero-round **bridge** that reinterprets a
  `CMlPolynomial`-level statement (`PolyEvalStatement`) as a `QuadEvalStatement` by taking the
  Eq. (12) bases to be the monomial tensor bases `mb(xl)` / `mb(xh)` of the low/high halves of the
  evaluation point (`toQuadEvalStatement`), realized as the `ReduceClaim` reduction. Because
  `ReduceClaim`'s verifier is pure with no challenge rounds, its coordinate-wise special soundness
  (CWSS; `ReduceClaim.verifier_coordinateWiseSpecialSoundWith`) collapses to the
  transcript-level pull-back `mem_relPolyEval_of_relIn`, so the bridge is CWSS for **any** `D`
  (`bridge_coordinateWiseSpecialSoundWith`).

  The result is a polynomial-level input relation `relPolyEval` (a weak `VerifiedOpening` whose
  *extracted polynomial* evaluates to `y` at `xl ++ xh`) that
  `QuadEval`'s two-round reduction refines to Hachi Eq. (20). `Composition.lean` chains the bridge
  before `QuadEval` at the head of the `iteration` (`bridgePackage ▷ quadEvalPackage ▷ …`).

  ## Main definitions

  * `PolyEvalStatement`: the polynomial-level statement — outer commitment `u`, split evaluation
    point `(xl, xh)`, and claimed value `y` (the key `(A, B, D)` is the relations' `pp`
    parameter, not statement data).
  * `toQuadEvalStatement`: the reinterpretation, with `bvec := mb(xl)` and `avec := mb(xh)`.
  * `bridgeVerifier`: the zero-round `ReduceClaim` verifier realizing it.
  * `bridgeReduction`: the computable protocol object of the link (that verifier paired with the
    honest prover, which applies the same reinterpretation and passes the witness through).
  * `extractedPoly`: the polynomial read back from a weak opening's Eq. (15) derived-message
    matrix via `Hachi.toPolynomial`.
  * `relPolyEval`: the polynomial-level input relation described above.
  * `bridgeVerifierPureForm`: the verifier's purity as data (`toQuadEvalStatement` as the verdict),
    which the package carries and a composed chain runs at the seam.
  * `bridgePackage`: the bridge as a composable, escape-free `CWSSPackage`.

  ## Main results

  * `mem_relPolyEval_of_relIn`: `QuadEval`'s `relIn` at `toQuadEvalStatement Φ s` pulls back to
    `relPolyEval` at `s`, via `splitForm_monomialBasis_eq_eval`.
  * `bridge_coordinateWiseSpecialSoundWith`: the bridge is CWSS for any `D`, at the named
    witness-only `ReduceClaim.treeExtractor`.
  * `mem_relIn_of_relPolyEval`: the converse push-forward, so `relPolyEval` is *exactly* the
    pull-back of `relIn` along `toQuadEvalStatement`.
  * `bridgeReduction_perfectCompleteness`: perfect completeness of the link, error `0`; the
    honest counterpart of `bridge_coordinateWiseSpecialSoundWith`, about the same verifier
    (`bridgeReduction_verifier`).

  ## Faithfulness note (Eq. (12) convention)

  The paper's `bᵀ = (x₁^{i₁}⋯x_r^{i_r})ᵢ` ranges over the **first** `r` variables and indexes the
  matrix **rows**; `aᵀ` over the **last** `m` variables indexes the columns. `EvalSplit`
  fixes exactly this split (low/first = rows = `b`), and `QuadEval`'s `derivedMsgMatrix` has
  rows = outer/`b` blocks. Hence `bvec := mb(xl)` (over `xl`, the first `r` variables) and
  `avec := mb(xh)` (over `xh`, the last `m` variables) is the faithful instantiation, and
  `evalConsistency` (`splitForm M b a`, argument order load-bearing) matches
  `splitForm_monomialBasis_eq_eval` on the nose.

  This is the `Rq`-level protocol of Hachi §4.2/Figure 3 (`Data = CMlPolynomial (Rq Φ) (r + m)`);
  the paper's headline multilinear-over-`𝔽_{q^k}` protocol (§3 packing) is a later
  zero-round head adapter in front of `relPolyEval`, built by the same recipe.

  Sits inside `namespace ArkLib.Lattices.Ajtai.InnerOuter` (activates the scoped
  `PolyVec`/`*ᵥ`/`dot`/`splitForm`) with `open WeakBinding`; the split layer is reached as
  `Hachi.toPolynomial` etc. Never `open ArkLib.Lattices` here (the `⬝ᵥ` token is ambiguous).

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

/-! ## The polynomial-level statement and the bridge map (any coefficient field `R`) -/

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι}

/-- Input statement of the composed Hachi evaluation protocol at the polynomial level (Hachi
§4.2/Figure 3, `Rq`-level): the outer commitment `u`, the evaluation point *split as a pair*
`(xl, xh)` (low/first `r` variables and high/last `m` variables — storing the split avoids
`take`/`drop` casts; `xl ++ xh` recovers the paper's point), and the claimed evaluation
`y = f(xl ++ xh)`. As at the `QuadEval` level, the public parameters `(A, B, D)` are the fixed
commitment key — a parameter of the relations, not statement data. -/
structure PolyEvalStatement (Φ : CyclotomicModulus R)
    (innerRows messageDigits outerRows innerDigits dRows m r : Nat) where
  /-- The outer commitment `u`. -/
  u : Commitment Φ outerRows
  /-- The outer/low point half `x₁ … x_r` (the first `r` variables; the matrix-row / `b` split). -/
  xl : Vector (Rq Φ) r
  /-- The inner/high point half `x_{r+1} … x_l` (the last `m` variables; the column / `a` split). -/
  xh : Vector (Rq Φ) m
  /-- The claimed evaluation `y = f(xl ++ xh)`. -/
  y : Rq Φ

/-- Reinterpret the polynomial-level statement as a `QuadEvalStatement` by taking the two Hachi
Eq. (12) evaluation bases to be the monomial tensor bases of the point halves:
`bᵀ := mb(xl)` (outer, over the first `r` variables, indexing rows) and `aᵀ := mb(xh)` (inner, over
the last `m` variables, indexing columns). `.get : Fin (2^·) → Rq Φ` is definitionally the
`PolyVec` the `QuadEvalStatement` fields expect. -/
def toQuadEvalStatement
    (s : PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r) :
    QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows where
  u := s.u
  avec := (CMlPolynomial.monomialBasis s.xh).get
  bvec := (CMlPolynomial.monomialBasis s.xl).get
  y := s.y

/-- The zero-round **bridge verifier**: a `ReduceClaim` head that reinterprets the polynomial-level
statement as a `QuadEvalStatement` via `toQuadEvalStatement`. Pure with no challenge rounds, so its
CWSS holds for any `D` (`bridge_coordinateWiseSpecialSoundWith`). -/
def bridgeVerifier :
    Verifier oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      !p[] :=
  ReduceClaim.verifier oSpec (toQuadEvalStatement Φ)

/-- The zero-round **bridge protocol** (Hachi §4.2/Figure 3, the polynomial-level head): the
`ReduceClaim` reduction whose prover and verifier both reinterpret the statement by
`toQuadEvalStatement` and hand the witness on untouched (the witness type is unchanged, so the
honest witness map is the identity — the same map the extractor inverts).

This is the primary object of the link: computable, and what an honest execution runs. Its verifier
is `bridgeVerifier` on the nose (`bridgeReduction_verifier`, a `rfl` check), the very verifier the
soundness certificate `bridgePackage` is stated about, so the two security directions of the link
cannot drift onto different verifiers. Perfect completeness is
`bridgeReduction_perfectCompleteness`. -/
def bridgeReduction :
    Reduction oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      !p[] :=
  ReduceClaim.reduction oSpec (toQuadEvalStatement Φ) (fun _ w => w)

/-- The bridge protocol's verifier **is** `bridgeVerifier`, the verifier of the soundness
certificate `bridgePackage`: completeness and coordinate-wise special soundness of this link speak
about the same object. Holds by `rfl`. -/
@[simp] theorem bridgeReduction_verifier :
    (bridgeReduction (oSpec := oSpec) Φ (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
        (dRows := dRows) (m := m) (r := r)).verifier
      = bridgeVerifier (oSpec := oSpec) Φ (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
        (dRows := dRows) (m := m) (r := r) :=
  rfl

/-- **The bridge verifier's purity as data** (`Verifier.PureForm`): the verdict is
`toQuadEvalStatement`, read off the `ReduceClaim` head, so `verify_eq` is `rfl`.

The bridge package carries this instead of a `Verifier.IsPure` instance, because the chain that
composes it before `QuadEval` must *run* this verdict at the seam, and reading it off the `IsPure`
existential would cost `Classical.choice`. -/
def bridgeVerifierPureForm : (bridgeVerifier (oSpec := oSpec) Φ (innerRows := innerRows)
    (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
    (dRows := dRows) (m := m) (r := r)).PureForm where
  verify := fun stmt _ => toQuadEvalStatement Φ stmt
  verify_eq := fun _ _ => rfl

end Defs

/-! ## The polynomial-level relation and the pull-back (over `ZMod q`) -/

section ZModDefs

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι}

/-- The polynomial extracted from a weak opening: the inverse reshape (`Hachi.toPolynomial`) of the
Eq. (15) derived-message matrix `M`. The reshape is a bijection
(`Hachi.toMatrix_toPolynomial`), so the polynomial reading stays interchangeable with the matrix
reading. -/
def extractedPoly (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    CMlPolynomial (Rq Φ) (r + m) :=
  Hachi.toPolynomial (derivedMsgMatrix Φ base o)

/-- **`relPolyEval` — the polynomial-level input relation** of the composed Hachi evaluation
protocol: a weak `VerifiedOpening` for `u` under the fixed key `pp` whose *extracted polynomial*
evaluates to `y` at `xl ++ xh`. It pulls back `QuadEval`'s ordinary `relIn` (whose second
conjunct is the matrix-level `evalConsistency`) through `toQuadEvalStatement`; this is the
interface into a `CMlPolynomial`-level functional commitment. -/
def relPolyEval
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ) :
    Set (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p |
    VerifiedOpening Φ base βSq γ κ pp.toPublicParams p.1.u p.2 ∧
    CMlPolynomial.eval (extractedPoly Φ base p.2) (p.1.xl ++ p.1.xh) = p.1.y }

omit [NeZero q] in
/-- **Pull-back lemma** (the `hRel` for the bridge's CWSS): a `QuadEvalWitness` accepted by
`QuadEval`'s `relIn` at the reinterpreted statement `toQuadEvalStatement Φ s` is accepted by
`relPolyEval` at the polynomial-level statement `s`. The proof converts the matrix-level
`evalConsistency`
(`splitForm (derivedMsgMatrix …) (mb xl) (mb xh) = y`) to the `CMlPolynomial.eval` claim via
`Hachi.splitForm_monomialBasis_eq_eval`. -/
theorem mem_relPolyEval_of_relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ)
    (s : PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (toQuadEvalStatement Φ s, w) ∈ relIn Φ pp base βSq γ κ) :
    (s, w) ∈ relPolyEval Φ pp base βSq γ κ := by
  obtain ⟨hvo, hec⟩ := h
  refine ⟨hvo, ?_⟩
  change CMlPolynomial.eval (Hachi.toPolynomial (derivedMsgMatrix Φ base w)) (s.xl ++ s.xh)
    = s.y
  rw [← Hachi.splitForm_monomialBasis_eq_eval (derivedMsgMatrix Φ base w) s.xl s.xh]
  exact hec

omit [NeZero q] in
/-- **CWSS of the bridge, named form.** The zero-round `ReduceClaim` head is coordinate-wise
special sound for any `D`, at the named witness-only `ReduceClaim.treeExtractor`: the tree carries
no information, so extraction is the pull-back of the leaf witnessing's output witness, and the
statement it must certify is pinned by the verifier's own verdict. The protocol content is the
transcript-level pull-back `mem_relPolyEval_of_relIn`, reducing `QuadEval`'s `relIn` to the
polynomial-level `relPolyEval`. The witness type is unchanged (`QuadEvalWitness`), so the witness
pull-back is the identity. -/
theorem bridge_coordinateWiseSpecialSoundWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (D : CWSSStructure (!p[] : ProtocolSpec 0))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ) :
    Verifier.coordinateWiseSpecialSoundWith init impl D
      (relPolyEval Φ pp base βSq γ κ) (relIn Φ pp base βSq γ κ)
      (bridgeVerifier (oSpec := oSpec) Φ (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r))
      (ReduceClaim.treeExtractor (fun _ w => w) D) :=
  ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relPolyEval Φ pp base βSq γ κ) (relOut := relIn Φ pp base βSq γ κ)
    (mapWitInv := fun _ w => w) (D := D)
    (mem_relPolyEval_of_relIn Φ pp base βSq γ κ)

/-- **The polynomial-level bridge as a (plain) `CWSSPackage`** (Hachi [NOZ26, §4.2]): the
zero-round `ReduceClaim` head `bridgeVerifier` bundled with the empty challenge structure
(`ofIsEmpty`) and its named CWSS certificate `bridge_coordinateWiseSpecialSoundWith`, ready to be
`▷`-composed before `QuadEval`. Its public `relOut` is `QuadEval`'s ordinary input relation
`relIn`.

The bridge is a statement *reinterpretation* with no cryptographic content, so it carries no escape
event; composing it before the escape-aware `quadEvalPackage` costs nothing, the universal `▷`
lifting it at the never-firing event. -/
def bridgePackage {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ) :
    CWSSPackage init impl
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (!p[] : ProtocolSpec 0) where
  verifier := bridgeVerifier (oSpec := oSpec) Φ
  struct := CWSSStructure.ofIsEmpty
  relIn := relPolyEval Φ pp base βSq γ κ
  relOut := relIn Φ pp base βSq γ κ
  isPure := bridgeVerifierPureForm Φ
  extractor := ReduceClaim.treeExtractor (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := bridge_coordinateWiseSpecialSoundWith Φ init impl CWSSStructure.ofIsEmpty pp base
    βSq γ κ

/-! ## Completeness: the honest direction of the bridge -/

omit [NeZero q] in
/-- **Push-forward lemma** (the honest direction, converse of `mem_relPolyEval_of_relIn`): a weak
opening whose *extracted polynomial* evaluates to `y` at `xl ++ xh` is, at the reinterpreted
statement `toQuadEvalStatement Φ s`, eval-consistent in the matrix sense of `QuadEval`'s `relIn`.

Same one rewrite as the pull-back, run the other way: `Hachi.splitForm_monomialBasis_eq_eval`
identifies `CMlPolynomial.eval (toPolynomial M) (xl ++ xh)` with
`splitForm M (mb xl) (mb xh)`, and the `VerifiedOpening` conjunct is literally shared (the
reinterpretation leaves `u` alone). Together with `mem_relPolyEval_of_relIn` this makes
`relPolyEval` *exactly* the pull-back of `relIn`, which is what the bridge's completeness needs. -/
theorem mem_relIn_of_relPolyEval
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ)
    (s : PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (s, w) ∈ relPolyEval Φ pp base βSq γ κ) :
    (toQuadEvalStatement Φ s, w) ∈ relIn Φ pp base βSq γ κ := by
  obtain ⟨hvo, hev⟩ := h
  refine ⟨hvo, ?_⟩
  change splitForm (derivedMsgMatrix Φ base w) (CMlPolynomial.monomialBasis s.xl).get
    (CMlPolynomial.monomialBasis s.xh).get = s.y
  rw [Hachi.splitForm_monomialBasis_eq_eval]
  exact hev

omit [NeZero q] in
/-- **Perfect completeness of the polynomial-level bridge** (Hachi §4.2/Figure 3, the zero-round
head). An honest prover holding a weak opening of `u` whose extracted polynomial evaluates to `y`
at `xl ++ xh` always succeeds: the reinterpreted statement and the untouched witness lie in
`QuadEval`'s input relation `relIn`, and the prover's and the verifier's output statements agree.
Full `Reduction.perfectCompleteness`, for arbitrary shared oracles `oSpec`, state initialization
`init` and query implementation `impl`.

The error is exactly `0`, and for a stronger reason than at the interactive links: the bridge draws
no challenges and performs no check, so there is nothing to fail — all of its content is the
relation equivalence `relPolyEval s w ↔ relIn (toQuadEvalStatement s) w`, whose two halves are
`mem_relIn_of_relPolyEval` (here, honest direction) and `mem_relPolyEval_of_relIn` (the
`hRel` of `bridge_coordinateWiseSpecialSoundWith`). Composed with
`quadEvalReduction_perfectCompleteness` this puts a `CMlPolynomial`-level evaluation claim at the
head of the honest chain, mirroring `bridgePackage ▷ quadEvalPackage` on the soundness side. -/
theorem bridgeReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ) :
    (bridgeReduction (oSpec := oSpec) Φ (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
        (dRows := dRows) (m := m) (r := r)).perfectCompleteness init impl
      (relPolyEval Φ pp base βSq γ κ) (relIn Φ pp base βSq γ κ) :=
  ReduceClaim.reduction_completeness (relPolyEval Φ pp base βSq γ κ) (relIn Φ pp base βSq γ κ)
    (fun s w => ⟨mem_relIn_of_relPolyEval Φ pp base βSq γ κ s w,
      mem_relPolyEval_of_relIn Φ pp base βSq γ κ s w⟩)

/-! ## The message-bounded seam, for the bounded-`z` reading of `QuadEval`

`QuadEval`'s bounded-`z` completeness runs from `relInMsgShort` — `relIn` plus an `ℓ∞` bound on
the honest committer's message decomposition, which is what makes the folded witness
`z = Σᵢ cᵢ sᵢ` short and hence `τ`-digit reconstructible (see `relInMsgShort`). The bridge has to
carry that conjunct across, so the polynomial-level relation gets the same strengthening. The
witness type is unchanged by the bridge, so the conjunct passes through literally and the
strengthened equivalence is the old one plus `Iff.rfl` on the new part. -/

/-- **`relPolyEval` with the honest committer's message decomposition pinned `ℓ∞`-short** — the
polynomial-level counterpart of `relInMsgShort`, and the input relation of the bounded-`z` honest
chain. `relPolyEvalMsgShort_subset_relPolyEval` is the forgetful inclusion; the soundness-side
`relPolyEval` is untouched. -/
def relPolyEvalMsgShort
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ msgBound : ℕ) :
    Set (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | p ∈ relPolyEval Φ pp base βSq γ κ ∧
      ∀ i, vecLInftyNorm Φ (p.2.message i) ≤ msgBound }

omit [NeZero q] in
/-- **The forgetful inclusion `relPolyEvalMsgShort ⊆ relPolyEval`.** -/
theorem relPolyEvalMsgShort_subset_relPolyEval
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ msgBound : ℕ) :
    relPolyEvalMsgShort Φ pp base βSq γ κ msgBound ⊆ relPolyEval Φ pp base βSq γ κ :=
  fun _ h => h.1

omit [NeZero q] in
/-- **Perfect completeness of the bridge at the message-bounded relations.** Identical to
`bridgeReduction_perfectCompleteness` — the bridge is a statement reinterpretation with an identity
witness map, so the extra `ℓ∞` conjunct on the (unchanged) witness transports by `Iff.rfl`. -/
theorem bridgeReduction_perfectCompleteness_msgShort {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ msgBound : ℕ) :
    (bridgeReduction (oSpec := oSpec) Φ (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
        (dRows := dRows) (m := m) (r := r)).perfectCompleteness init impl
      (relPolyEvalMsgShort Φ pp base βSq γ κ msgBound)
      (relInMsgShort Φ pp base βSq γ κ msgBound) :=
  ReduceClaim.reduction_completeness (relPolyEvalMsgShort Φ pp base βSq γ κ msgBound)
    (relInMsgShort Φ pp base βSq γ κ msgBound)
    (fun s w =>
      ⟨fun h => ⟨mem_relIn_of_relPolyEval Φ pp base βSq γ κ s w h.1, h.2⟩,
       fun h => ⟨mem_relPolyEval_of_relIn Φ pp base βSq γ κ s w h.1, h.2⟩⟩)

end ZModDefs

end ArkLib.Lattices.Ajtai.InnerOuter
