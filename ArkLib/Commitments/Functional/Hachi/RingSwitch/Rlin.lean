/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.ProofSystem.Component.ReduceClaim
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-!
  # Eq. (20) → `R^lin` adapter (Hachi §4.3 entry)

  Hachi §4.3 proves knowledge of a short solution of an **unstructured linear relation**

  `R^lin := {(z, (M, y)) : M z = y ∧ ‖z‖∞ ≤ bound}`   ([NOZ26] §4.3, `R^lin_{q,d,n,μ,b}`)

  and Eq. (20) — the output of the `QuadEval` reduction — *is* such an instance: stacking the
  response `ζ := (ŵ, flatten t̂, ẑ)` as one column and the five verification rows as one block
  matrix (`c := (chalᵢ).val`, `z := J ẑ`):

  ```
             ŵ (cW)               flatten t̂ (cT)      ẑ (cZ)                 rhs
  c1   [ D                    |  0                 |  0              ]   =    v
  c2   [ 0                    |  B                 |  0              ]   =    u
  c3   [ (G_{2^r})ᵀ b   row   |  0                 |  0              ]   =    y
  c4   [ (G_{2^r})ᵀ c   row   |  0                 | −(G_{2^m}J)ᵀ a  ]   =    0
  c5   [ 0                    |  (cᵀ ⊗ G_{n_A})    | −(A J)          ]   =    0
  ```

  Rows c3/c4 use `dot u (G *ᵥ x) = dot (Gᵀ *ᵥ u) x` (`dot_matVecMul_transpose`, from
  `splitForm_transpose`) to move the public gadget onto the coefficient side; the `ẑ`-columns of
  c4/c5 fold `G_{2^m}·J`, `A·J` via `matVecMul_matMul`; the c5 middle block `(cᵀ ⊗ G_{n_A})` is
  the explicit matrix `tensorGMatrix` whose action on `flatten t̂` reproduces `tensorG`. (c6, the
  `S_b` range checks, becomes the single `‖ζ‖∞ ≤ bound` conjunct, equivalent by
  `vecLInftyNorm_append`.) This file is the zero-round `ReduceClaim` bridge realizing that
  reading — **statement reshaping only**: no soundness error, CWSS for any structure, pure
  verifier — assembled from `ReduceClaim.verifier_coordinateWiseSpecialSoundWith`.

  The substance is the block-row equivalence `rlin_iff_relOut` (`M ζ = y ∧ ‖ζ‖∞ ≤ γ`, at the
  assembled statement, ⟺ the Eq. (20) relation `relOut` at the un-stacked response), proved via
  the linear part `rlin_linear_iff` (c1–c5) and the norm part `rlin_norm_iff` (c6). Both
  directions are established: the CWSS pull-back `mem_relOut_of_relRlin` (the bridge's `hRel`)
  and — guarding against a vacuous encoding — the completeness direction
  `mem_relRlin_of_relOut`.

  Seam discipline: this file's `relIn` **is** `QuadEval`'s `relOut` (the Eq. (20) relation), and
  its `relOut` `relRlin` is definitionally the next link's (`RingSwitch/Reduction.lean`) `relIn`.
  The adapter is pure statement reshaping, so it carries no escape event of its own; the
  weak-binding escape enters one link later, in the lift.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise

section Rlin

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ## The `R^lin` statement and relation -/

/-- Column count `μ` of the Eq. (20) block system: the stacked witness
`ζ = ŵ ++ (flatten t̂ ++ ẑ)`. Associativity fixed once, here. -/
abbrev rlinCols (innerRows messageDigits innerDigits zDigits m r : Nat) : Nat :=
  2 ^ r * messageDigits + (2 ^ r * (innerRows * innerDigits) + 2 ^ m * messageDigits * zDigits)

/-- Row count `n` of the Eq. (20) block system: the stacked rows `c1 ++ (c2 ++ (c3 ++ (c4 ++
c5)))`. Associativity fixed once, here. -/
abbrev rlinRows (innerRows outerRows dRows : Nat) : Nat :=
  dRows + (outerRows + (1 + (1 + innerRows)))

/-- The carrier-block width `cW = 2^r · messageDigits` (`ŵ`); the first column block. -/
abbrev rlinCW (messageDigits r : Nat) : Nat := 2 ^ r * messageDigits
/-- The inner-block width `cT = 2^r · (innerRows · innerDigits)` (`flatten t̂`); middle block. -/
abbrev rlinCT (innerRows innerDigits r : Nat) : Nat := 2 ^ r * (innerRows * innerDigits)
/-- The response-block width `cZ = (2^m · messageDigits) · zDigits` (`ẑ`); last column block. -/
abbrev rlinCZ (messageDigits zDigits m : Nat) : Nat := 2 ^ m * messageDigits * zDigits

/-! The unstructured linear relation is the Hachi-specific seam between Eq. (20) and the
`Lift`. The reusable ring-switching layer only needs an abstract input
relation; keeping this statement here avoids baking `Rq`, its norm, and Hachi's bound convention
into the generic protocol machinery. -/

/-- Statement of Hachi's unstructured linear relation `R^lin`: a public matrix, a public
right-hand side, and a public `ℓ∞`-norm bound on the witness. -/
structure RlinStatement (n μ : ℕ) where
  /-- The public matrix `M ∈ Rq^{n×μ}`. -/
  M : ArkLib.Lattices.PolyMatrix (Rq Φ) n μ
  /-- The public right-hand side `y ∈ Rq^n`. -/
  yvec : ArkLib.Lattices.PolyVec (Rq Φ) n
  /-- The public `ℓ∞`-norm bound on the witness. -/
  bound : ℕ

/-- Hachi's `R^lin` relation: knowledge of a short solution of the linear system. -/
def relRlin {n μ : ℕ} :
    Set (RlinStatement Φ n μ × ArkLib.Lattices.PolyVec (Rq Φ) μ) :=
  {p | p.1.M *ᵥ p.2 = p.1.yvec ∧ vecLInftyNorm Φ p.2 ≤ p.1.bound}

/-! ## Stacking / un-stacking the response and the `c5` gadget matrix -/

/-- Un-flatten a row-major block vector into blocks — the inverse of `PolyVec.flattenBlocks`. -/
def unflatten {P : Type} {blocks width : Nat} (v : ArkLib.Lattices.PolyVec P (blocks * width)) :
    ArkLib.Lattices.PolyVec (ArkLib.Lattices.PolyVec P width) blocks :=
  fun i j => v (finProdFinEquiv (i, j))

@[simp] theorem flattenBlocks_unflatten {P : Type} {blocks width : Nat}
    (v : ArkLib.Lattices.PolyVec P (blocks * width)) :
    ArkLib.Lattices.PolyVec.flattenBlocks (unflatten v) = v := by
  funext j
  simp only [ArkLib.Lattices.PolyVec.flattenBlocks, unflatten, Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] theorem unflatten_flattenBlocks {P : Type} {blocks width : Nat}
    (xs : ArkLib.Lattices.PolyVec (ArkLib.Lattices.PolyVec P width) blocks) :
    unflatten (ArkLib.Lattices.PolyVec.flattenBlocks xs) = xs := by
  funext i j
  simp only [unflatten, ArkLib.Lattices.PolyVec.flattenBlocks_apply]

/-- **The `c5` block matrix** `(cᵀ ⊗ G_{k})` acting on the flattened block vector `flatten t̂`:
entry `(p, finProdFinEquiv (i, e)) = cᵢ · G_k(p, e)`, so that
`tensorGMatrix c *ᵥ flatten x = tensorG c x` (`tensorGMatrix_mulVec`). -/
def tensorGMatrix (base : ZMod q) (k digits blocks : Nat)
    (c : ArkLib.Lattices.PolyVec (Rq Φ) blocks) :
    ArkLib.Lattices.PolyMatrix (Rq Φ) k (blocks * (k * digits)) :=
  fun p flat =>
    c (finProdFinEquiv.symm flat).1 * gadgetMatrix Φ base k digits p (finProdFinEquiv.symm flat).2

omit [NeZero q] in
/-- `tensorGMatrix c` applied to a flattened block family reproduces `tensorG` — the c5 block-row
identity. -/
theorem tensorGMatrix_mulVec (base : ZMod q) (k digits blocks : Nat)
    (c : ArkLib.Lattices.PolyVec (Rq Φ) blocks)
    (x : ArkLib.Lattices.PolyVec (ArkLib.Lattices.PolyVec (Rq Φ) (k * digits)) blocks) :
    tensorGMatrix Φ base k digits blocks c *ᵥ ArkLib.Lattices.PolyVec.flattenBlocks x
      = Hachi.tensorG Φ base k digits c x := by
  funext p
  simp only [matVecMul_apply, dot_eq_sum, tensorGMatrix]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ArkLib.Lattices.PolyVec.flattenBlocks_apply]
  simp only [Hachi.tensorG, Finset.sum_apply, scalarVecMul, matVecMul_apply, dot_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-- **Witness stacking** `ζ = ŵ ++ (flatten t̂ ++ ẑ)`: the inverse of `unstack`, used by the
completeness direction. -/
def stack (resp : QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    ArkLib.Lattices.PolyVec (Rq Φ) (rlinCols innerRows messageDigits innerDigits zDigits m r) :=
  Fin.append resp.carrierDec
    (Fin.append (ArkLib.Lattices.PolyVec.flattenBlocks resp.innerDec) resp.zDec)

/-- **Witness unstacking** (the bridge's `mapWitInv`): split a stacked `ζ ∈ Rq^μ` back into the
`QuadEvalResponse` triple `(ŵ, t̂, ẑ)` — `carrierDec`/`zDec` are the outer/inner `Fin.append`
slices, `innerDec` un-flattens the middle slice; inverse to `stack`/the `rlinCols` layout. -/
def unstack
    (ζ : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits where
  carrierDec := fun k => ζ (Fin.castAdd _ k)
  innerDec := unflatten fun k =>
    ζ (Fin.natAdd (rlinCW messageDigits r) (Fin.castAdd _ k))
  zDec := fun k =>
    ζ (Fin.natAdd (rlinCW messageDigits r) (Fin.natAdd (rlinCT innerRows innerDigits r) k))

omit [NeZero q] [IsCyclotomic Φ] in
/-- Round trip: un-stacking a stacked response recovers it (used for completeness / non-vacuity). -/
@[simp] theorem unstack_stack
    (resp : QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    unstack Φ (stack Φ resp) = resp := by
  obtain ⟨cd, idc, zd⟩ := resp
  simp only [unstack, stack, Fin.append_left, Fin.append_right, unflatten_flattenBlocks]

omit [NeZero q] [IsCyclotomic Φ] in
/-- Round trip: stacking an un-stacked vector recovers it — with `unstack_stack` this makes
`stack`/`unstack` mutually inverse (used by the norm equivalence and non-vacuity). -/
@[simp] theorem stack_unstack
    (ζ : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    stack Φ (unstack Φ ζ) = ζ := by
  simp only [stack, unstack, flattenBlocks_unflatten]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    refine Fin.addCases (fun i2 => ?_) (fun i2 => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]

/-! ## The assembled `R^lin` statement -/

/-- **Statement assembly** (the bridge's `mapStmt`): build the Eq. (20) block matrix and
right-hand side from `QuadEval`'s output statement `(stmt, v, c)` — rows c1–c5 as in the module
docstring, right-hand side `(v, u, y, 0, 0)`, `bound := γ`. -/
def rlinStmt
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) :
    RlinStatement Φ (rlinRows innerRows outerRows dRows)
      (rlinCols innerRows messageDigits innerDigits zDigits m r) where
  M :=
    let stmt := X.1
    let c : ArkLib.Lattices.PolyVec (Rq Φ) (2 ^ r) := fun i => (X.2.2 i).val
    let G2r := gadgetMatrix Φ base (2 ^ r) messageDigits
    let G2m := gadgetMatrix Φ base (2 ^ m) messageDigits
    let J := Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits
    Fin.append
      -- c1: [ D | 0 ]
      (fun i => Fin.append (pp.dMatrix i)
        (0 : ArkLib.Lattices.PolyVec (Rq Φ)
          (rlinCT innerRows innerDigits r + rlinCZ messageDigits zDigits m)))
      (Fin.append
        -- c2: [ 0 | B | 0 ]
        (fun i => Fin.append (0 : ArkLib.Lattices.PolyVec (Rq Φ) (rlinCW messageDigits r))
          (Fin.append (pp.outerMatrix i)
            (0 : ArkLib.Lattices.PolyVec (Rq Φ) (rlinCZ messageDigits zDigits m))))
        (Fin.append
          -- c3: [ (G_{2^r})ᵀ b | 0 ]
          (fun _ : Fin 1 => Fin.append (G2r.transpose *ᵥ stmt.bvec)
            (0 : ArkLib.Lattices.PolyVec (Rq Φ)
              (rlinCT innerRows innerDigits r + rlinCZ messageDigits zDigits m)))
          (Fin.append
            -- c4: [ (G_{2^r})ᵀ c | 0 | −(G_{2^m}J)ᵀ a ]
            (fun _ : Fin 1 => Fin.append (G2r.transpose *ᵥ c)
              (Fin.append (0 : ArkLib.Lattices.PolyVec (Rq Φ) (rlinCT innerRows innerDigits r))
                (-((ArkLib.Lattices.matMul G2m J).transpose *ᵥ stmt.avec))))
            -- c5: [ 0 | (cᵀ ⊗ G_{n_A}) | −(A J) ]
            (fun p : Fin innerRows =>
              Fin.append (0 : ArkLib.Lattices.PolyVec (Rq Φ) (rlinCW messageDigits r))
                (Fin.append (tensorGMatrix Φ base innerRows innerDigits (2 ^ r) c p)
                  (-(ArkLib.Lattices.matMul pp.innerMatrix J p)))))))
  yvec :=
    Fin.append X.2.1
      (Fin.append X.1.u
        (Fin.append (fun _ : Fin 1 => X.1.y)
          (Fin.append (fun _ : Fin 1 => (0 : Rq Φ)) (fun _ : Fin innerRows => (0 : Rq Φ)))))
  bound := γ

omit [NeZero q] in
/-- The assembled statement's public bound is the range parameter `γ`. This is what lets the honest
chain's seam relation `relRlinImage` pin the lift's `sideCond` and its `z`-bound to `γ`. Holds by
`rfl`. -/
@[simp] theorem rlinStmt_bound
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) :
    (rlinStmt (zDigits := zDigits) Φ pp base ω γ X).bound = γ :=
  rfl

/-! ## The block-row equivalence -/

omit [NeZero q] in
-- Same cause as `matVecMul_append_rows`: rewriting `Fin.append _ _ *ᵥ _` into the block matrix
-- needs `PolyMatrix`/`PolyVec` to unfold, which v4.33 blocks at implicit transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Linear part** (Eq. (20) rows c1–c5 ⟺ `M ζ = y`): the block matrix `rlinStmt`'s action on
`ζ` splits — via `matVecMul_append_rows` / `dot_append` / `dot_matVecMul_transpose` /
`matVecMul_matMul` / `tensorGMatrix_mulVec` — into the five verification rows read at the
un-stacked response `unstack ζ`. -/
theorem rlin_linear_iff
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (ζ : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    (rlinStmt (zDigits := zDigits) Φ pp base ω γ X).M *ᵥ ζ
        = (rlinStmt (zDigits := zDigits) Φ pp base ω γ X).yvec ↔
      (Simple.commit Φ pp.dMatrix (unstack Φ ζ).carrierDec = X.2.1 ∧
        Simple.commit Φ pp.outerMatrix
          (ArkLib.Lattices.PolyVec.flattenBlocks (unstack Φ ζ).innerDec) = X.1.u ∧
        ArkLib.Lattices.dot X.1.bvec
          (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ (unstack Φ ζ).carrierDec) = X.1.y ∧
        Hachi.tensorG1 Φ base messageDigits (fun i => (X.2.2 i).val) (unstack Φ ζ).carrierDec =
          ArkLib.Lattices.dot X.1.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ
            (Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ (unstack Φ ζ).zDec)) ∧
        Hachi.tensorG Φ base innerRows innerDigits (fun i => (X.2.2 i).val) (unstack Φ ζ).innerDec =
          pp.innerMatrix *ᵥ
            (Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ (unstack Φ ζ).zDec)) := by
  simp only [rlinStmt]
  rw [matVecMul_append_rows, matVecMul_append_rows, matVecMul_append_rows,
      matVecMul_append_rows, funext_fin_add_iff, funext_fin_add_iff, funext_fin_add_iff,
      funext_fin_add_iff]
  simp only [Fin.append_left, Fin.append_right]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · -- c1: `D ŵ = v`
    simp only [funext_iff, matVecMul_apply, dot_append, dot_zero_left, add_zero, Simple.commit,
      unstack]
  · -- c2: `B (flatten t̂) = u`
    simp only [funext_iff, matVecMul_apply, dot_append, dot_zero_left, zero_add, add_zero,
      Simple.commit, unstack, flattenBlocks_unflatten]
  · -- c3: `bᵀ (G ŵ) = y`, via the transpose adjunction
    simp only [funext_iff, Fin.forall_fin_one, matVecMul_apply, dot_append,
      dot_zero_left, add_zero, unstack, dot_matVecMul_transpose]
  · -- c4: `(cᵀ⊗G₁) ŵ = aᵀ G (J ẑ)`, folding `G·J` and moving the transpose/`sub`
    simp only [funext_iff, Fin.forall_fin_one, matVecMul_apply, dot_append,
      dot_zero_left, dot_neg_left, unstack, Hachi.tensorG1, zero_sub,
      ← sub_eq_add_neg, sub_eq_zero, ← dot_matVecMul_transpose, matVecMul_matMul]
  · -- c5: `(cᵀ⊗G_{n_A}) t̂ = A (J ẑ)`, via `tensorGMatrix_mulVec` on the flattened block
    have key :
        (fun p => Fin.append (0 : ArkLib.Lattices.PolyVec (Rq Φ) (rlinCW messageDigits r))
              (Fin.append
                (tensorGMatrix Φ base innerRows innerDigits (2 ^ r) (fun i => (X.2.2 i).val) p)
                (-(ArkLib.Lattices.matMul pp.innerMatrix
                    (Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits) p)))) *ᵥ ζ
          = tensorGMatrix Φ base innerRows innerDigits (2 ^ r) (fun i => (X.2.2 i).val)
              *ᵥ ArkLib.Lattices.PolyVec.flattenBlocks (unstack Φ ζ).innerDec
            - ArkLib.Lattices.matMul pp.innerMatrix
                (Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits) *ᵥ (unstack Φ ζ).zDec := by
      funext p
      simp only [matVecMul_apply, dot_append, dot_zero_left, dot_neg_left, zero_add,
        Pi.sub_apply, ← sub_eq_add_neg, unstack, flattenBlocks_unflatten]
    rw [key, tensorGMatrix_mulVec, matVecMul_matMul, funext_iff]
    simp only [Pi.sub_apply, sub_eq_zero, ← funext_iff]

omit [NeZero q] [IsCyclotomic Φ] in
/-- `‖·‖∞` of an appended vector is `≤ γ` iff both halves are — the c6 splitting fact. -/
theorem vecLInftyNorm_append {a b : Nat} (u : ArkLib.Lattices.PolyVec (Rq Φ) a)
    (v : ArkLib.Lattices.PolyVec (Rq Φ) b) (γ : ℕ) :
    vecLInftyNorm Φ (Fin.append u v) ≤ γ ↔ vecLInftyNorm Φ u ≤ γ ∧ vecLInftyNorm Φ v ≤ γ := by
  simp only [vecLInftyNorm, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  rw [Fin.forall_fin_add]
  simp only [Fin.append_left, Fin.append_right]

omit [NeZero q] in
/-- **Norm part** (Eq. (20) c6 ⟺ `‖ζ‖∞ ≤ γ`): the single stacked-vector bound is equivalent to
the three per-block bounds via `vecLInftyNorm_append` and the stack layout. -/
theorem rlin_norm_iff
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (ζ : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    vecLInftyNorm Φ ζ ≤ (rlinStmt (zDigits := zDigits) Φ pp base ω γ X).bound ↔
      (vecLInftyNorm Φ (unstack Φ ζ).carrierDec ≤ γ ∧
        vecLInftyNorm Φ (ArkLib.Lattices.PolyVec.flattenBlocks (unstack Φ ζ).innerDec) ≤ γ ∧
        vecLInftyNorm Φ (unstack Φ ζ).zDec ≤ γ) := by
  change vecLInftyNorm Φ ζ ≤ γ ↔ _
  conv_lhs => rw [← stack_unstack Φ ζ, stack]
  rw [vecLInftyNorm_append, vecLInftyNorm_append]

omit [NeZero q] in
/-- **The block-row equivalence** ([NOZ26] §4.3): an `R^lin` witness `ζ` at
the assembled statement `rlinStmt X` satisfies `relRlin` iff its un-stacking is an Eq. (20)-valid
`QuadEvalResponse` at `X`. -/
theorem rlin_iff_relOut
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (ζ : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r)) :
    (rlinStmt (zDigits := zDigits) Φ pp base ω γ X, ζ) ∈ relRlin Φ ↔
      (X, unstack Φ ζ) ∈ relOut (zDigits := zDigits) Φ pp base ω γ := by
  rw [relRlin, Set.mem_ofPred_eq, rlin_linear_iff, rlin_norm_iff, relOut, Set.mem_ofPred_eq]
  tauto

/-! ## The pull-back and completeness directions -/

omit [NeZero q] in
/-- **Block-row equivalence pull-back** (the bridge's `hRel`): an `R^lin` witness at
`rlinStmt X` un-stacks to an Eq. (20)-valid `QuadEvalResponse` at `X`. -/
theorem mem_relOut_of_relRlin
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (w : ArkLib.Lattices.PolyVec (Rq Φ)
          (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (h : (rlinStmt (zDigits := zDigits) Φ pp base ω γ X, w) ∈ relRlin Φ) :
    (X, unstack Φ w) ∈ relOut (zDigits := zDigits) Φ pp base ω γ :=
  (rlin_iff_relOut Φ pp base ω γ X w).mp h

omit [NeZero q] in
/-- **Completeness / non-vacuity**: every Eq. (20)-valid transcript's
response stacks to an `R^lin` witness at the assembled statement. Guarantees the pull-back is not
vacuous. -/
theorem mem_relRlin_of_relOut
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
    (w : QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (h : (X, w) ∈ relOut (zDigits := zDigits) Φ pp base ω γ) :
    (rlinStmt (zDigits := zDigits) Φ pp base ω γ X, stack Φ w) ∈ relRlin Φ := by
  have hun : (X, unstack Φ (stack Φ w)) ∈ relOut (zDigits := zDigits) Φ pp base ω γ := by
    rw [unstack_stack]; exact h
  exact (rlin_iff_relOut Φ pp base ω γ X (stack Φ w)).mpr hun

/-! ## The honest seam: the image of the adapter -/

/-- **`relRlinImage` — the honest chain's seam relation at the `R^lin` interface**: the *image* of
the Eq. (20) output relation under the adapter's two maps. A pair belongs to it exactly when it
*came from* an Eq.-(20)-valid transcript, `p = (rlinStmt X, stack w)` with `(X, w) ∈ relOut`.

**Why the honest side needs this and soundness does not.** The two directions of a link consume
relations with opposite variance: soundness must be stated at the *broadest* input a malicious
prover could produce (here `relRlin`, which constrains only `M ζ = y` and `‖ζ‖∞ ≤ s.bound`), while
completeness may — and often must — assume everything the honest predecessor actually established.
`relRlin` deliberately forgets three things the lift's honest prover needs:

* the *provenance* of the matrix, hence any bound on its coefficients (an arbitrary
  `RlinStatement` has an arbitrary `M`, so nothing can be said about the honest quotient);
* the value of the public bound (`s.bound` is a free field, so `bound ≤ s.bound` is not derivable
  and, quantified over all statements, is false for positive `bound` — `s.bound = 0` is legal);
* consequently, the *protocol-level* norm bound on `z`: `relRlin` gives `‖ζ‖∞ ≤ s.bound`, which
  says nothing about the lift's own `bound` until `s.bound` is known.

Taking the image fixes all three at once, and it is the strongest honest seam available: it is
exactly what the adapter proves (`rlinReduction_perfectCompleteness_image`). Recorded consequences:
`mem_relRlin_of_mem_relRlinImage`, `bound_eq_of_mem_relRlinImage`,
`vecLInftyNorm_le_of_mem_relRlinImage`, `matVecMul_eq_of_mem_relRlinImage`.

`relRlinImage ⊆ relRlin` (first lemma), so nothing about the soundness abstraction is weakened. -/
def relRlinImage
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    Set (RlinStatement Φ (rlinRows innerRows outerRows dRows)
          (rlinCols innerRows messageDigits innerDigits zDigits m r) ×
        ArkLib.Lattices.PolyVec (Rq Φ)
          (rlinCols innerRows messageDigits innerDigits zDigits m r)) :=
  { p | ∃ (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
              dRows ×
            CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
          (w : QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits),
        (X, w) ∈ relOut (zDigits := zDigits) Φ pp base ω γ ∧
          p = (rlinStmt (zDigits := zDigits) Φ pp base ω γ X, stack Φ w) }

omit [NeZero q] in
/-- The honest seam refines the soundness relation: `relRlinImage ⊆ relRlin`. Immediate from the
block-row pull-back `mem_relRlin_of_relOut`, and the reason the two directions of the lift can be
stated around the same protocol object without any relation being weakened. -/
theorem mem_relRlin_of_mem_relRlinImage
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    {p : RlinStatement Φ (rlinRows innerRows outerRows dRows)
          (rlinCols innerRows messageDigits innerDigits zDigits m r) ×
        ArkLib.Lattices.PolyVec (Rq Φ)
          (rlinCols innerRows messageDigits innerDigits zDigits m r)}
    (h : p ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ) :
    p ∈ relRlin Φ := by
  obtain ⟨X, w, hrel, rfl⟩ := h
  exact mem_relRlin_of_relOut Φ pp base ω γ X w hrel

omit [NeZero q] in
/-- On the honest seam the statement's public bound **is** the range parameter `γ`: the assembled
statement is `rlinStmt`, whose `bound` field is `γ` (`rlinStmt_bound`). This is what turns
`relRlin`'s `‖ζ‖∞ ≤ s.bound` into a *protocol-level* bound.

Stated with the statement and witness as separate arguments (rather than an implicit pair) so that
consumers never force the unifier to solve `?p.1 =?= s` at the chain's large dimension
expressions. -/
theorem bound_eq_of_mem_relRlinImage
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (s : RlinStatement Φ (rlinRows innerRows outerRows dRows)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (z : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (h : (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ) :
    s.bound = γ := by
  obtain ⟨X, w, -, heq⟩ := h
  rw [(Prod.mk.injEq _ _ _ _).mp heq |>.1]
  exact rlinStmt_bound Φ pp base ω γ X

omit [NeZero q] in
/-- **The `z`-bound the lift needs**, read off the seam: the witness is `ℓ∞`-bounded by the
Eq. (20) range parameter `γ`. Via `relRlin` at the seam's own public bound
(`bound_eq_of_mem_relRlinImage`). -/
theorem vecLInftyNorm_le_of_mem_relRlinImage
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (s : RlinStatement Φ (rlinRows innerRows outerRows dRows)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (z : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (h : (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ) :
    vecLInftyNorm Φ z ≤ γ := by
  have hb : s.bound = γ := bound_eq_of_mem_relRlinImage Φ pp base ω γ s z h
  have hz : vecLInftyNorm Φ z ≤ s.bound :=
    (mem_relRlin_of_mem_relRlinImage Φ pp base ω γ h).2
  rwa [hb] at hz

omit [NeZero q] in
/-- The linear system holds on the seam (the lift's `hrow`). -/
theorem matVecMul_eq_of_mem_relRlinImage
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ)
    (s : RlinStatement Φ (rlinRows innerRows outerRows dRows)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (z : ArkLib.Lattices.PolyVec (Rq Φ)
      (rlinCols innerRows messageDigits innerDigits zDigits m r))
    (h : (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ) :
    s.M *ᵥ z = s.yvec :=
  (mem_relRlin_of_mem_relRlinImage Φ pp base ω γ h).1

/-! ## The package -/

/-- **The `R^lin` adapter verifier's purity as data** (`Verifier.PureForm`): the verdict is
`rlinStmt`, read off the zero-round `ReduceClaim` head, so `verify_eq` is `rfl`.

The package carries this instead of a `Verifier.IsPure` instance, because the composed chain must
*run* this verdict at the seam and reading it off the `IsPure` existential would cost
`Classical.choice`. -/
def rlinVerifierPureForm
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    (ReduceClaim.verifier oSpec (rlinStmt (zDigits := zDigits) Φ pp base ω γ)).PureForm where
  verify := fun stmt _ => rlinStmt (zDigits := zDigits) Φ pp base ω γ stmt
  verify_eq := fun _ _ => rfl

/-- **The `R^lin` adapter as a (plain) `CWSSPackage`** (Hachi [NOZ26] §4.3 entry): the
zero-round `ReduceClaim` head `rlinStmt` with the empty challenge structure, reducing `relOut` to
`relRlin`. Pure statement reshaping with no cryptographic content, hence escape-free. Assembled
from `ReduceClaim.verifier_coordinateWiseSpecialSoundWith` at the block-row pull-back
`mem_relOut_of_relRlin`. -/
def rlinPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    CWSSPackage init impl
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (RlinStatement Φ (rlinRows innerRows outerRows dRows)
        (rlinCols innerRows messageDigits innerDigits zDigits m r))
      (PolyVec (Rq Φ) (rlinCols innerRows messageDigits innerDigits zDigits m r))
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (rlinStmt (zDigits := zDigits) Φ pp base ω γ)
  struct := CWSSStructure.ofIsEmpty
  relIn := relOut (zDigits := zDigits) Φ pp base ω γ
  relOut := relRlin Φ
  isPure := rlinVerifierPureForm Φ pp base ω γ
  extractor := ReduceClaim.treeExtractor (fun _ w => unstack Φ w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relOut (zDigits := zDigits) Φ pp base ω γ)
    (relOut := relRlin Φ)
    (mapWitInv := fun _ w => unstack Φ w) (D := CWSSStructure.ofIsEmpty)
    (fun X w h => mem_relOut_of_relRlin Φ pp base ω γ X w h)

end Rlin

end ArkLib.Lattices.Ajtai.InnerOuter
