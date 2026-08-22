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
  verifier — assembled sorry-free from `ReduceClaim.verifier_coordinateWiseSpecialSoundWith`.

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

/-! ## Generic index / vector helpers

Small reusable facts about `Fin.append`, `dot`, and `matVecMul` used to split the Eq. (20) block
matrix along its rows and columns. Stated locally; candidates for promotion to `Data/Lattices`. -/

section GenericHelpers

/-- Split a `∀` over `Fin (m + n)` into its `castAdd`/`natAdd` halves. -/
theorem forall_fin_add {m n : ℕ} {motive : Fin (m + n) → Prop} :
    (∀ i, motive i) ↔
      (∀ i : Fin m, motive (Fin.castAdd n i)) ∧ (∀ i : Fin n, motive (Fin.natAdd m i)) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i; exact Fin.addCases h1 h2 i

/-- Two functions on `Fin (m + n)` agree iff their `castAdd`/`natAdd` restrictions agree. -/
theorem funext_fin_add_iff {α : Type*} {m n : ℕ} {f g : Fin (m + n) → α} :
    f = g ↔
      (fun i : Fin m => f (Fin.castAdd n i)) = (fun i => g (Fin.castAdd n i)) ∧
      (fun i : Fin n => f (Fin.natAdd m i)) = (fun i => g (Fin.natAdd m i)) := by
  rw [funext_iff, forall_fin_add]
  simp only [funext_iff]

variable {P : Type} [CommRing P]

/-- `dot` splits along an append in its first argument. -/
theorem dot_append {m n : ℕ} (u : ArkLib.Lattices.PolyVec P m) (v : ArkLib.Lattices.PolyVec P n)
    (w : ArkLib.Lattices.PolyVec P (m + n)) :
    ArkLib.Lattices.dot (Fin.append u v) w
      = ArkLib.Lattices.dot u (fun k => w (Fin.castAdd n k))
        + ArkLib.Lattices.dot v (fun k => w (Fin.natAdd m k)) := by
  simp only [dot_eq_sum]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_)
  · rw [Fin.append_left]
  · rw [Fin.append_right]

/-- `dot` with a zero first argument is zero. -/
theorem dot_zero_left {k : ℕ} (w : ArkLib.Lattices.PolyVec P k) :
    ArkLib.Lattices.dot (0 : ArkLib.Lattices.PolyVec P k) w = 0 := by
  simp only [dot_eq_sum, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- `dot` negates in its first argument. -/
theorem dot_neg_left {k : ℕ} (u w : ArkLib.Lattices.PolyVec P k) :
    ArkLib.Lattices.dot (-u) w = -(ArkLib.Lattices.dot u w) := by
  simp only [dot_eq_sum, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- **Transpose adjunction for `dot`**: `⟨u, A v⟩ = ⟨Aᵀ u, v⟩`. Moves a public gadget matrix off
the witness side onto the coefficient side (Eq. (20) rows c3/c4). -/
theorem dot_matVecMul_transpose {a b : ℕ} (A : ArkLib.Lattices.PolyMatrix P a b)
    (u : ArkLib.Lattices.PolyVec P a) (v : ArkLib.Lattices.PolyVec P b) :
    ArkLib.Lattices.dot u (A *ᵥ v) = ArkLib.Lattices.dot (A.transpose *ᵥ u) v := by
  have h := splitForm_transpose A u v
  simp only [splitForm] at h
  rw [h]; exact dot_comm _ _

set_option backward.isDefEq.respectTransparency false in
/-- `matVecMul` splits along a row-append: block rows act independently. -/
theorem matVecMul_append_rows {a b c : ℕ} (M₁ : ArkLib.Lattices.PolyMatrix P a c)
    (M₂ : ArkLib.Lattices.PolyMatrix P b c) (ζ : ArkLib.Lattices.PolyVec P c) :
    (Fin.append M₁ M₂ : ArkLib.Lattices.PolyMatrix P (a + b) c) *ᵥ ζ
      = Fin.append (M₁ *ᵥ ζ) (M₂ *ᵥ ζ) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    change ArkLib.Lattices.dot (Fin.append M₁ M₂ (Fin.castAdd b i)) ζ =
      ArkLib.Lattices.dot (M₁ i) ζ
    rw [Fin.append_left]
  · rw [Fin.append_right]
    change ArkLib.Lattices.dot (Fin.append M₁ M₂ (Fin.natAdd a i)) ζ =
      ArkLib.Lattices.dot (M₂ i) ζ
    rw [Fin.append_right]

end GenericHelpers

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
noncomputable def rlinStmt
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

/-! ## The block-row equivalence -/

omit [NeZero q] in
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
  rw [forall_fin_add]
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

/-! ## The package -/

/-- **The `R^lin` adapter as a (plain) `CWSSPackage`** (Hachi [NOZ26] §4.3 entry): the zero-round
`ReduceClaim` head `rlinStmt` with the empty challenge structure, reducing `relOut` to `relRlin`.
Pure statement reshaping with no cryptographic content, hence escape-free. Assembled from
`ReduceClaim.verifier_coordinateWiseSpecialSoundWith` at the proven block-row pull-back
`mem_relOut_of_relRlin` — sorry-free. -/
noncomputable def rlinPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
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
  isPure := ⟨fun stmt _ => rlinStmt (zDigits := zDigits) Φ pp base ω γ stmt, fun _ _ => rfl⟩
  extractor := ReduceClaim.treeExtractor
    (mapStmt := rlinStmt (zDigits := zDigits) Φ pp base ω γ)
    (relRlin Φ) (fun _ w => unstack Φ w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relOut (zDigits := zDigits) Φ pp base ω γ)
    (relOut := relRlin Φ)
    (mapWitInv := fun _ w => unstack Φ w) (D := CWSSStructure.ofIsEmpty)
    (fun X w h => mem_relOut_of_relRlin Φ pp base ω γ X w h)

end Rlin

end ArkLib.Lattices.Ajtai.InnerOuter
