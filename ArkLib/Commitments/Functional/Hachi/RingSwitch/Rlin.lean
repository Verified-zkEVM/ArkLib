/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.ProofSystem.Component.ReduceClaim
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge

/-!
  # Eq. (20) → `R^lin` adapter — skeleton (Hachi §4.3 entry; sumcheck-track milestone F2)

  Hachi §4.3 proves knowledge of a short solution of an **unstructured linear relation**

  `R^lin := {(z, (M, y)) : M z = y ∧ ‖z‖∞ ≤ bound}`   ([NOZ26] §4.3, `R^lin_{q,d,n,μ,b}`)

  and Eq. (20) — the output of the `QuadEval` reduction — *is* such an instance: stacking the
  response `ζ := (ŵ, flatten t̂, ẑ)` as one column and the five verification rows as one block
  matrix:

  ```
             ŵ                    flatten t̂            ẑ                      rhs
  c1   [ D                    |  0                 |  0              ]   =    v
  c2   [ 0                    |  B                 |  0              ]   =    u
  c3   [ (bᵀ G_{2^r,δ}) row   |  0                 |  0              ]   =    y
  c4   [ (cᵀ ⊗ G₁) row        |  0                 | −(aᵀ G_{2^m} J) ]   =    0
  c5   [ 0                    |  (cᵀ ⊗ G_{n_A})    | −(A J)          ]   =    0
  ```

  (c6, the `S_b` range checks, becomes the `‖ζ‖∞ ≤ bound` conjunct.) This file is the zero-round
  `ReduceClaim` bridge realizing that reading. It is **statement reshaping only** — no soundness
  error, CWSS for any structure, pure verifier — assembled sorry-free from `ReduceClaim`; the
  **sorried** pieces are the assembly/unstacking functions (`rlinStmt`, `unstack`) and the
  block-row equivalence pull-back (`mem_relOut_of_relRlin`) — pure index bookkeeping
  (milestone F2.1/F2.2: `stackRows`/`pasteCols`/`finAppend` helpers plus the
  `tensorG`/`tensorG1`-as-matrix-rows rewriting lemmas over `QuadEval/Gadgets.lean`).

  Seam discipline (design decision G6): the package's public `relIn` **is** the plain Eq. (20)
  `relOut`, and its public `relOut` is the next link's plain `relRlin`. The escape set is
  transported independently.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} {E : Type}

/-- Column count `μ` of the Eq. (20) block system: the stacked witness
`ζ = ŵ ++ (flatten t̂ ++ ẑ)`. Associativity fixed once, here (F2.2 convention pin). -/
abbrev rlinCols (innerRows messageDigits innerDigits zDigits m r : Nat) : Nat :=
  2 ^ r * messageDigits + (2 ^ r * (innerRows * innerDigits) + 2 ^ m * messageDigits * zDigits)

/-- Row count `n` of the Eq. (20) block system: the stacked rows `c1 ++ (c2 ++ (c3 ++ (c4 ++
c5)))`. Associativity fixed once, here (F2.2 convention pin). -/
abbrev rlinRows (innerRows outerRows dRows : Nat) : Nat :=
  dRows + (outerRows + (1 + (1 + innerRows)))

/-- The `R^lin` statement ([NOZ26] §4.3): a public matrix `M`, a public right-hand side `yvec`,
and a public `ℓ∞`-norm bound on the witness. -/
structure RlinStatement (Φ : CyclotomicModulus (ZMod q)) (n μ : ℕ) where
  /-- The public matrix `M ∈ Rq^{n×μ}`. -/
  M : PolyMatrix (Rq Φ) n μ
  /-- The public right-hand side `y ∈ Rq^n`. -/
  yvec : PolyVec (Rq Φ) n
  /-- The public `ℓ∞`-norm bound on the witness (`b − 1` in the paper's `R^lin`; `γ` in this
  chain, inherited from Eq. (20)'s c6). -/
  bound : ℕ

/-- **The `R^lin` relation** ([NOZ26] §4.3): `M ζ = y` and `‖ζ‖∞ ≤ bound`. -/
def relRlin {n μ : ℕ} : Set (RlinStatement Φ n μ × PolyVec (Rq Φ) μ) :=
  {p | p.1.M *ᵥ p.2 = p.1.yvec ∧ vecLInftyNorm Φ p.2 ≤ p.1.bound}

/-- Escape-threaded `R^lin` relation — the §4.3 chain's second seam. -/
def relRlinE {n μ : ℕ} (esc : Set E) :
    Set (RlinStatement Φ n μ × (PolyVec (Rq Φ) μ ⊕ E)) :=
  (relRlin Φ).withEscape esc

/-- **Statement assembly** (the bridge's `mapStmt`): build the Eq. (20) block matrix and
right-hand side from `QuadEval`'s output statement `(stmt, v, c)` — rows c1–c5 as in the module
docstring, from `stmt.pp.dMatrix`/`stmt.pp.outerMatrix`/`stmt.pp.innerMatrix`, the bases
`stmt.bvec`/`stmt.avec`, the carrier commitment `v`, the challenges `c`, and the gadget matrices
`gadgetMatrix`/`jMatrix` (`QuadEval/Gadgets.lean`); right-hand side `(v, u, y, 0, 0)`;
`bound := γ`.

**Sorried (F2.2)**: needs the `stackRows`/`pasteCols` block-matrix helpers (F2.1). -/
def rlinStmt (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) :
    RlinStatement Φ (rlinRows innerRows outerRows dRows)
      (rlinCols innerRows messageDigits innerDigits zDigits m r) :=
  sorry

/-- **Witness unstacking** (the bridge's `mapWitInv`): split a stacked `ζ ∈ Rq^μ` back into the
`QuadEvalResponse` triple `(ŵ, t̂, ẑ)` (`Fin.addCases` splits + `finProdFinEquiv` un-flatten,
inverse to the stacking convention pinned at `rlinCols`).

**Sorried (F2.2).** -/
def unstack
    (ζ : PolyVec (Rq Φ) (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits :=
  sorry

/-- **Block-row equivalence pull-back** (the bridge's `hRel`; the substance of F2): an `R^lin`
witness at the assembled statement `rlinStmt base ω γ X` un-stacks to an Eq. (20)-valid
`QuadEvalResponse` at `X` — c1–c5 are the five block rows of `M ζ = y`, c6 is the norm conjunct
split along the stacking. Escapes pass through.

**Sorried (F2.2)**: `matVecMul`-over-`stackRows`/`pasteCols` splits `M ζ = yvec` into the five
component equations; c3/c4 via `dot`-associativity and a `tensorG1`-as-row lemma; c5 via a
`tensorG`-as-matrix lemma plus `matVecMul` composition for `A·J`; the norm conjunct by a
`vecLInftyNorm`-over-append lemma (`max ≤ γ ↔` three `≤ γ`). -/
theorem mem_relOut_of_relRlin (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (w : PolyVec (Rq Φ) (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (h : (rlinStmt (zDigits := zDigits) Φ base ω γ X, w) ∈ relRlin Φ) :
    (X, unstack Φ w) ∈ relOut (zDigits := zDigits) Φ base ω γ := by
  sorry

/-- **The `R^lin` adapter as an `EscapeCWSSPackage`** (Hachi [NOZ26] §4.3 entry): the zero-round
`ReduceClaim` head `rlinStmt` with the empty challenge structure, reducing plain `relOut` to
plain `relRlin` while carrying `esc` unchanged. Assembled from
`ReduceClaim.verifier_coordinateWiseSpecialSound`; all remaining work lives in the sorried
`rlinStmt`/`unstack`/`mem_relOut_of_relRlin`. -/
def rlinPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (base : ZMod q) (ω γ : ℕ) (esc : Set E) :
    EscapeCWSSPackage init impl E
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (RlinStatement Φ (rlinRows innerRows outerRows dRows)
        (rlinCols innerRows messageDigits innerDigits zDigits m r))
      (PolyVec (Rq Φ) (rlinCols innerRows messageDigits innerDigits zDigits m r))
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (rlinStmt (zDigits := zDigits) Φ base ω γ)
  struct := CWSSStructure.ofIsEmpty
  relIn := relOut (zDigits := zDigits) Φ base ω γ
  relOut := relRlin Φ
  escIn := esc
  escOut := esc
  escape_mono := fun _ h => h
  isPure := ⟨fun stmt _ => rlinStmt (zDigits := zDigits) Φ base ω γ stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := (relOut (zDigits := zDigits) Φ base ω γ).withEscape esc)
    (relOut := relRlinE Φ esc)
    (mapWitInv := fun _ w => w.map (unstack Φ) id) (D := CWSSStructure.ofIsEmpty)
    (fun X w h => by
      cases w with
      | inl w => exact mem_relOut_of_relRlin Φ base ω γ X w h
      | inr e => exact h)

end ArkLib.Lattices.Ajtai.InnerOuter
