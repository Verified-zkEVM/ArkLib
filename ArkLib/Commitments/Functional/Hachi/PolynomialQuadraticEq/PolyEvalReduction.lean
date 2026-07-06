/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.PolynomialQuadraticEq.QuadEval
import ArkLib.Commitments.Functional.Hachi.PolynomialEvalSplit
import ArkLib.ProofSystem.Component.ReduceClaim

/-!
  # Polynomial-level bridge into Hachi's `QuadEval` reduction

  `PolynomialQuadraticEq/QuadEval.lean` (Hachi Lemma 8) states its evaluation claim over *opaque*
  Eq. (12) basis vectors `avec`/`bvec` — it never mentions `CMlPolynomial`.
  `PolynomialEvalSplit.lean` proves that a multilinear evaluation factors as the split bilinear form
  of a reshaped coefficient matrix against the monomial tensor bases (`evalSplit_eq_eval`,
  `splitForm_monomialBasis_eq_eval`), but
  nothing connects the two.

  This module is the connective tissue: a zero-round **bridge** that reinterprets a
  `CMlPolynomial`-level statement (`PolyEvalStatement`) as a `QuadEvalStatement` by taking the
  Eq. (12) bases to be the monomial tensor bases `mb(xl)` / `mb(xh)` of the low/high halves of the
  evaluation point (`toQuadEvalStatement`), realized as the `ReduceClaim` reduction. Because
  `ReduceClaim`'s verifier is pure with no challenge rounds, its coordinate-wise special soundness
  (`ReduceClaim.verifier_coordinateWiseSpecialSound`) collapses to the transcript-level pull-back
  `mem_relPolyEval_of_relIn`, so the bridge is CWSS for **any** `D`
  (`bridge_coordinateWiseSpecialSound`).

  The result is a polynomial-level input relation `relPolyEval` (a weak `VerifiedOpening` whose
  *extracted polynomial* evaluates to `y` at `xl ++ xh`, or a Module-SIS solution for `B`/`D`) that
  `QuadEval`'s two-round reduction refines to Hachi Eq. (20). `Basic.lean` composes the two
  (`bridge.append QuadEval.verifier`) into the sorry-free
  `hachi_eval_coordinateWiseSpecialSound`.

  ## Faithfulness note (Eq. (12) convention)

  The paper's `bᵀ = (x₁^{i₁}⋯x_r^{i_r})ᵢ` ranges over the **first** `r` variables and indexes the
  matrix **rows**; `aᵀ` over the **last** `m` variables indexes the columns. `PolynomialEvalSplit`
  fixes exactly this split (low/first = rows = `b`), and `QuadEval`'s `derivedMsgMatrix` has
  rows = outer/`b` blocks. Hence `bvec := mb(xl)` (over `xl`, the first `r` variables) and
  `avec := mb(xh)` (over `xh`, the last `m` variables) is the faithful instantiation, and
  `evalConsistency` (`splitForm M b a`, argument order load-bearing) matches
  `splitForm_monomialBasis_eq_eval` on the nose.

  This is the `Rq`-level protocol of Hachi §4.2/Figure 3 (`Data = CMlPolynomial (Rq Φ) (r + m)`);
  the paper's headline multilinear-over-`𝔽_{q^k}` protocol (§4.1 ring switch/packing) is a later
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
open OracleComp OracleSpec ProtocolSpec CoordinateWise.SingleRound

/-! ## The polynomial-level statement and the bridge map (any coefficient field `R`) -/

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι}

/-- Input statement of the composed Hachi evaluation protocol at the polynomial level (Hachi
§4.2/Figure 3, `Rq`-level): the public parameters `(A, B, D)`, the outer commitment `u`, the
evaluation point *split as a pair* `(xl, xh)` (low/first `r` variables and high/last `m` variables —
storing the split avoids `take`/`drop` casts; `xl ++ xh` recovers the paper's point), and the
claimed evaluation `y = f(xl ++ xh)`. -/
structure PolyEvalStatement (Φ : CyclotomicModulus R)
    (innerRows messageDigits outerRows innerDigits dRows m r : Nat) where
  /-- Public matrices `(A, B, D)`. -/
  pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
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
  pp := s.pp
  u := s.u
  avec := (CMlPolynomial.monomialBasis s.xh).get
  bvec := (CMlPolynomial.monomialBasis s.xl).get
  y := s.y

/-- The zero-round **bridge verifier**: a `ReduceClaim` head that reinterprets the polynomial-level
statement as a `QuadEvalStatement` via `toQuadEvalStatement`. Pure with no challenge rounds, so its
CWSS holds for any `D` (`bridge_coordinateWiseSpecialSound`). -/
def bridgeVerifier :
    Verifier oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      !p[] :=
  ReduceClaim.verifier oSpec (toQuadEvalStatement Φ)

end Defs

/-! ## The polynomial-level relation and the pull-back (over `ZMod q`) -/

section ZModDefs

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι}

/-- The polynomial extracted from a weak opening: the inverse reshape (`Hachi.toPolynomial`) of the
Eq. (15) derived-message matrix `M`. A bijection, so
`toMatrix (extractedPoly …) = derivedMsgMatrix …` (`toMatrix_extractedPoly`), keeping the
polynomial reading interchangeable with the matrix reading for downstream binding arguments. -/
def extractedPoly (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    CMlPolynomial (Rq Φ) (r + m) :=
  Hachi.toPolynomial (derivedMsgMatrix Φ base o)

omit [NeZero q] in
/-- Round-trip: the reshaped `extractedPoly` recovers the Eq. (15) derived-message matrix. -/
@[simp] theorem toMatrix_extractedPoly (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    Hachi.toMatrix (extractedPoly Φ base o) = derivedMsgMatrix Φ base o := by
  simp only [extractedPoly, Hachi.toMatrix_toPolynomial]

/-- **`relPolyEval` — the polynomial-level input relation** of the composed Hachi evaluation
protocol: either a weak `VerifiedOpening` for `u` whose *extracted polynomial* evaluates to `y` at
`xl ++ xh`, or a Module-SIS solution for the outer matrix `B`, or one for the short-commitment
matrix `D`. It pulls back `QuadEval`'s `relIn` (whose opening disjunct is the matrix-level
`evalConsistency`) through `toQuadEvalStatement`; the opening disjunct is the interface into a
`CMlPolynomial`-level functional commitment. -/
def relPolyEval (base : ZMod q) (βSq γ κ : ℕ) :
    Set (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | match p with
    | (s, .opening o) =>
        VerifiedOpening Φ base βSq γ κ s.pp.toPublicParams s.u o ∧
        CMlPolynomial.eval (extractedPoly Φ base o) (s.xl ++ s.xh) = s.y
    | (s, .msisB z) => ModuleSIS.relation Φ (outerShort Φ γ) s.pp.outerMatrix z = true
    | (s, .msisD z) => ModuleSIS.relation Φ (dShort Φ γ) s.pp.dMatrix z = true }

omit [NeZero q] in
/-- **Pull-back lemma** (the `hRel` for the bridge's CWSS): a `QuadEvalWitness` accepted by
`QuadEval`'s `relIn` at the reinterpreted statement `toQuadEvalStatement Φ s` is accepted by
`relPolyEval` at the polynomial-level statement `s`. The MSIS disjuncts are preserved verbatim
(`toQuadEvalStatement` keeps `pp`); the opening disjunct converts the matrix-level `evalConsistency`
(`splitForm (derivedMsgMatrix …) (mb xl) (mb xh) = y`) to the `CMlPolynomial.eval` claim via
`Hachi.splitForm_monomialBasis_eq_eval`. -/
theorem mem_relPolyEval_of_relIn (base : ZMod q) (βSq γ κ : ℕ)
    (s : PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (toQuadEvalStatement Φ s, w) ∈ relIn Φ base βSq γ κ) :
    (s, w) ∈ relPolyEval Φ base βSq γ κ := by
  cases w with
  | opening o =>
      obtain ⟨hvo, hec⟩ := h
      refine ⟨hvo, ?_⟩
      change CMlPolynomial.eval (Hachi.toPolynomial (derivedMsgMatrix Φ base o)) (s.xl ++ s.xh)
        = s.y
      rw [← Hachi.splitForm_monomialBasis_eq_eval (derivedMsgMatrix Φ base o) s.xl s.xh]
      exact hec
  | msisB z => exact h
  | msisD z => exact h

omit [NeZero q] in
/-- **CWSS of the bridge.** The zero-round `ReduceClaim` head is coordinate-wise special sound for
any `D`: with no challenge rounds, CWSS collapses (via the no-challenge bridge) to the
transcript-level pull-back `mem_relPolyEval_of_relIn`, reducing `QuadEval`'s `relIn` to the
polynomial-level `relPolyEval`. The witness type is unchanged (`QuadEvalWitness`), so the witness
pull-back is the identity. -/
theorem bridge_coordinateWiseSpecialSound {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (D : CWSSStructure (!p[] : ProtocolSpec 0)) (base : ZMod q) (βSq γ κ : ℕ) :
    (bridgeVerifier (oSpec := oSpec) Φ (innerRows := innerRows) (messageDigits := messageDigits)
        (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m)
        (r := r)).coordinateWiseSpecialSound init impl D
      (relPolyEval Φ base βSq γ κ) (relIn Φ base βSq γ κ) := by
  refine ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relPolyEval Φ base βSq γ κ) (relOut := relIn Φ base βSq γ κ)
    (mapWitInv := fun _ w => w) (D := D) ?_
  intro s w h
  exact mem_relPolyEval_of_relIn Φ base βSq γ κ s w h

end ZModDefs

end ArkLib.Lattices.Ajtai.InnerOuter
