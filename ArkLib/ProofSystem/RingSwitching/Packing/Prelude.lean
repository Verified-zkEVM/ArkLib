/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.RingSwitching.Transport.Coeffs
import ArkLib.ProofSystem.Sumcheck.Structured
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Packing algebra and protocol vocabulary

Everything the `Packing` protocol files speak about, one level below any particular
message flow.

## Main components

1. **The pack/unpack pair** — `packMLE` reads each `2^κ`-block of a `B`-multilinear's
   Boolean-cube evaluations (its coefficients in the multilinear Lagrange basis) as one
   `L`-element along the basis, producing a multilinear in `κ` fewer
   variables; `unpackMLE` reverses it by reading off basis coordinates. These realize the
   claim-preserving change of ring that the protocol then has to make checkable.
2. **Carrier operations** — the tensor-algebra carrier `L ⊗[K] L` with its two embeddings
   `φ₀ = · ⊗ 1`, `φ₁ = 1 ⊗ ·` and its row/column coordinate maps: the concrete data behind
   the binary-tower profile instance `binaryTowerProfile` (defined at the end of this file).
3. **Protocol subroutines** — `embedded_MLP_eval`, the honest folded carrier element
   (the packed polynomial, coefficients embedded via `φ₁`, evaluated at the `φ₀`-image of
   the point's tail); `eqWeightedCoordSum`, the verifier's coordinate-reconstruction
   subroutine that every check of the protocol applies to some coordinate family; and
   `compute_A_func`/`compute_A_MLE`, the public multiplier that turns the batched claim into
   a sumcheck about the packed polynomial.
4. **Protocol types and relations** — statement/witness types at the phase boundaries, the
   `MLIOPCS` interface for the downstream opening (any protocol that opens a large-ring
   multilinear evaluation claim, bundled with its completeness and round-by-round
   knowledge-soundness obligations), and the relations/knowledge-state predicates the
   security analysis threads through the phases.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
-/

noncomputable section

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial TensorProduct
open scoped NNReal
open Sumcheck.Structured

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section TensorAlgebraOps
/-!
## The tensor-algebra carrier

The concrete carrier of the binary-tower instance: `A = L ⊗[K] L`, its two embeddings
`φ₀ = · ⊗ 1` and `φ₁ = 1 ⊗ ·`, and the row/column coordinate maps with respect to a
`K`-basis `β` of `L`.
-/

/-- The tensor-algebra carrier `A = L ⊗[K] L`: as a `K`-module, a `(2^κ) × (2^κ)` array of
`K`-elements, holding polynomial data (`φ₁`-factor) and evaluation-point data (`φ₀`-factor)
independently. The imported `TensorAlgebra` file provides the left-algebra instances. -/
abbrev TensorAlgebra (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := by rfl
  map_mul' α β := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [tmul_zero]
  map_add' α β := by simp only [tmul_add]

open Module
/-- Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} ŝ_u ⊗ β_u)`.
This views `L ⊗ L` as a module over `L` (left action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_rows {σ : Type*} (β : Basis σ K L)
    (s_hat : TensorAlgebra K L) : σ → L :=
  fun u =>
    (β.baseChange L).repr s_hat u

/-- Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} β_v ⊗ ŝ_v)`.
This views `L ⊗ L` as a module over `L` (right action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_columns {σ : Type*} (β : Basis σ K L) (s_hat : L ⊗[K] L) : σ → L :=
  fun v => by
    let b := Basis.baseChangeRight (b:=β) (Right:=L)
    letI rightAlgebra : Algebra L (L ⊗[K] L) := by
      exact Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    exact b.repr s_hat v
/--
**MLE packing**: pack a small-ring multilinear `t` into a large-ring multilinear `t'` by
reinterpreting each chunk of `2^κ` coefficients as a single `L`-element along the basis `β`
([DP24] Definition 2.1).
For each `w ∈ {0,1}^ℓ'`, the evaluation `t'(w)` is defined as:
`t'(w) := ∑_{v ∈ {0,1}^κ} t(v₀, ..., v_{κ-1}, w₀, ..., w_{ℓ'-1}) ⋅ β_v`
-/
def packMLE (β : Basis (Fin κ → Fin 2) K L) (t : MultilinearPoly K ℓ) :
    MultilinearPoly L ℓ' :=
  -- 1. Define the function that gives the evaluations of t' on the boolean hypercube.
  let packing_func (w : Fin ℓ' → Fin 2) : L :=
    -- a. Define a function that computes the K-coefficients for a given `w`.
    let coeffs_for_w (v : Fin κ → Fin 2) : K :=
      -- Construct the full evaluation point `(v, w)` of length `ℓ`.
      let concatenated_point (i : Fin ℓ) : Fin 2 :=
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩
      -- Evaluate the small-field polynomial `t` at this point.
      MvPolynomial.eval (fun i => ↑(concatenated_point i)) t.val
    -- b. Use `equivFun.symm` = ∑ v, (coeffs_for_w v) • (β v).
    β.equivFun.symm coeffs_for_w
  -- 2. The packed polynomial `t'` is the multilinear extension of this function.
  ⟨MvPolynomial.MLE packing_func, MLE_mem_restrictDegree packing_func⟩

/--
**Unpacking a Packed Multilinear Polynomial**.
Reverses the packing defined in `packMLE`. It reconstructs the small-field
multilinear `t` from the large-field multilinear `t'`.

The evaluation of `t` at a point `(v, w)` is recovered by taking the evaluation
of `t'` at `w`, which is an element of `L`, and finding its `v`-th coordinate
with respect to the basis `β`.
-/
def unpackMLE (β : Basis (Fin κ → Fin 2) K L) (t' : MultilinearPoly L ℓ') :
    MultilinearPoly K ℓ :=
  -- 1. Define the function that gives the evaluations of the original small-field polynomial `t`.
  let unpacked_evals (p : Fin ℓ → Fin 2) : K :=
    -- a. Deconstruct the evaluation point `p` into `v` (first κ bits) and `w` (last ℓ' bits).
    let v (i : Fin κ) : Fin 2 := p ⟨i.val, by omega⟩
    let w (i : Fin ℓ') : Fin 2 := p ⟨i.val + κ, by { rw [h_l]; omega }⟩
    -- b. Evaluate the large-field polynomial `t'` at the point `w`.
    let t'_eval_at_w : L := MvPolynomial.eval (fun i => ↑(w i)) t'.val
    -- c. Get the K-coefficients of this L-element with respect to the basis `β`.
    -- `β.repr/β.equivFun` maps an element of L to its coordinate function `(Fin κ → Fin 2) → K`.
    let coeffs : (Fin κ → Fin 2) → K := β.repr t'_eval_at_w
    -- d. The desired evaluation t(p) = t(v,w)
      -- is the coefficient corresponding to the basis vector `β_v`.
    coeffs v
  -- 2. The unpacked polynomial `t` is the multilinear extension of this evaluation function.
  ⟨MvPolynomial.MLE unpacked_evals, MLE_mem_restrictDegree unpacked_evals⟩

/--
**Component-wise `φ₁` embedding**.
Takes a polynomial `t'` with coefficients in `L` and embeds it into a polynomial
with coefficients in the tensor algebra `A` by applying `φ₁` to each coefficient.
The multilinear (`d = 1`) case of the family-shared degree-generic coefficient transport
`RingSwitching.embedCoeffs` (`ArkLib/ProofSystem/RingSwitching/Transport/Coeffs.lean`).
-/
def componentWise_embed_MLE {A' : Type} [CommRing A'] (φ : L →+* A')
    (t' : MultilinearPoly L ℓ') : MultilinearPoly A' ℓ' :=
  embedCoeffs φ t'

/-- Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`. -/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  componentWise_embed_MLE L ℓ' (A' := TensorAlgebra K L) (φ₁ L K) t'

end TensorAlgebraOps

section ProtocolTypes
/-!
## Statement and witness types at the phase boundaries

What each phase of the reduction consumes and produces, plus the downstream-opening
interface.
-/

/-- Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`. -/
structure MLPEvalStatement where
  /-- The evaluation point `r = (r₀, …, r_{ℓ-1})` — shared input. -/
  t_eval_point : Fin ℓ → L
  /-- The claimed evaluation `s = t(r)`. -/
  original_claim : L

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext (P : RingSwitchingProfile K L κ)
    extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : P.A -- ŝ
  r_batching : Fin κ → L -- r''

-- `SumcheckWitness` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured` (the data shape is
-- generic and degree-neutral; only the per-round prover/verifier in `SumcheckPhase.lean` consume
-- it). Binius ring-switching is the degree-2 case `H = m · t'`, so this Binius-local abbrev pins
-- `d := 2`. Other instantiations (e.g. Hachi at `d := 2b+1`) pin their own degree — no
-- instantiation is privileged by a default on the generic type. The packed polynomial `t'` and
-- round polynomial `H` (after fixing previous challenges) live in the same structure.
abbrev SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) :=
  Sumcheck.Structured.SumcheckWitness L ℓ i 2

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  stmt.original_claim = wit.t.val.eval stmt.t_eval_point

structure AbstractOStmtIn where
  ιₛᵢ : Type
  OStmtIn : ιₛᵢ → Type
  Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)
  -- The abstract initial compatibility relation, which along with
  -- MLPEvalRelation, forms the initial input relation for the MLIOPCS.
  initialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop

def AbstractOStmtIn.toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
    Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    MLPEvalRelation L ℓ' aOStmtIn.ιₛᵢ aOStmtIn.OStmtIn input
    ∧ aOStmtIn.initialCompatibility ⟨input.2.t, input.1.2⟩}

structure MLIOPCS extends (AbstractOStmtIn L ℓ') where
  /-- Protocol specification -/
  numRounds : ℕ
  pSpec : ProtocolSpec numRounds
  Oₘ: ∀ j, OracleInterface (pSpec.Message j)
  O_challenges: ∀ (i : pSpec.ChallengeIdx), SampleableType (pSpec.Challenge i)
  /-- The evaluation protocol Π' as an oracle proof. -/
  oracleReduction : OracleProof (oSpec := []ₒ)
    (Statement := MLPEvalStatement L ℓ') (OStatement := OStmtIn)
    (Witness := WitMLP L ℓ')
    (pSpec := pSpec)
  -- Security properties
  perfectCompleteness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleProof.perfectCompleteness (oSpec := []ₒ)
      (Statement := MLPEvalStatement L ℓ') (OStatement := OStmtIn)
      (Witness := WitMLP L ℓ') (pSpec := pSpec) (init := init) (impl := impl)
      (relation := toAbstractOStmtIn.toRelInput)
      (oracleProof := oracleReduction)
  -- RBR knowledge error function for the MLIOPCS
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  -- RBR knowledge soundness property
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)
  },
    OracleProof.rbrKnowledgeSoundness
      (verifier := oracleReduction.toOracleVerifier)
      (init := init)
      (impl := impl)
      (relIn := toAbstractOStmtIn.toRelInput)
      (rbrKnowledgeError := rbrKnowledgeError)

end MLIOPCS

section OStmt
variable (aOStmtIn : AbstractOStmtIn L ℓ')

instance instOstmtMLIOPCS : ∀ (i : aOStmtIn.ιₛᵢ), OracleInterface (aOStmtIn.OStmtIn i) :=
  fun i => aOStmtIn.Oₛᵢ i

end OStmt

end ProtocolTypes
end Preliminaries

/- This section defines the specific relations for the ring-switching protocol, whereas
the basis of L over K has rank `2^κ` instead of `κ` as in the Preliminaries section.
-/
section Relations
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- **The verifier's coordinate-reconstruction subroutine**: the eq̃-weighted sum
`∑_{u ∈ {0,1}^κ} eq̃(u, r) ⋅ c u` of a `2^κ`-indexed coordinate family `c` at the round
randomness `r` — equivalently, the evaluation at `r` of the multilinear extension of `c`
(Boolean points cast into `L`). Every DP24 verifier check below is this sum at a different
coordinate family and randomness: step 2 checks the original claim against the column
coordinates of `ŝ`, step 5 batches the row coordinates of `ŝ` into the sumcheck target `s₀`,
and step 8 weighs the row coordinates of the final eq̃-tensor. -/
def eqWeightedCoordSum (c : (Fin κ → Fin 2) → L) (r : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r) * c u

/-- The honest folded carrier element: the packed polynomial, coefficients embedded via
`φ₁`, evaluated at the `φ₀`-image of the point's tail —
`ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))`. This is the prover's batching-phase message; its
row/column coordinates carry the claims the verifier checks and batches. -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    P.A :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly P.A ℓ' := componentWise_embed_MLE L ℓ' P.φ₁ t'
  let φ₀_mapped_r: Fin ℓ' → P.A := fun i => P.φ₀ (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-- The verifier's claim-consistency check: the claimed evaluation `s` must equal the
eq̃-weighted reconstruction from `ŝ`'s column coordinates at the point prefix,
`s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v` — `eqWeightedCoordSum` at
`P.decomposeColumns` ([DP24] step 2, Check 1). -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : P.A) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  decide (s = eqWeightedCoordSum κ L (P.decomposeColumns s_hat) r_prefix)

/-- The batched-multiplier function on the cube: for each `w ∈ {0,1}^{ℓ'}`, decompose
`eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1}) =: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u` into basis
coordinates and batch those with the eq̃-weights of the batching scalars,
`A : w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
([DP24] step 4a).
-/
def compute_A_func (original_r_eval_suffix : Fin ℓ' → L)
    (r''_batching : Fin κ → L) : ((Fin (ℓ') → (Fin 2)) → L) :=
  fun w =>
    -- Decompose eq̃(r_suffix, w) into K-basis coefficients A_{w,u}
    let w_as_L : Fin ℓ' → L := fun i => if w i == 1 then 1 else 0
    -- `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    let eq_w: L := eqTilde original_r_eval_suffix w_as_L
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := P.basis.repr eq_w
    -- Compute A(w) = Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⋅ A_{w,u}
    Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
      let A_w_u : K := coords_A_w_u u
      let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
      -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
      let eq_u_r_batching : L := eqTilde u_as_L r''_batching
      A_w_u • eq_u_r_batching

/-- The batched multiplier `A(X_0, ..., X_{ℓ'-1})` — the multilinear extension of
`compute_A_func`, the public factor of the relocation sumcheck's polynomial `h = A · t'`
([DP24] step 4b). -/
def compute_A_MLE
    (original_r_eval_suffix : Fin ℓ' → L) (r''_batching : Fin κ → L) :
  MultilinearPoly L ℓ' :=
  let A_func := compute_A_func κ L K P ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
    SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ P) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K P ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
  -- Ring-switching is the plain degree-2 case `H = P · t'`: combinator `Q := X`, degree 1.
  combinator := fun _ => Polynomial.X
  degCombinator := 1
  combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le
}

/-- The batched sumcheck target: `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where `ŝ_u`
are the row components of `ŝ` — `eqWeightedCoordSum` at `P.decomposeRows` and the batching
scalars ([DP24] step 5). -/
def compute_s0 (s_hat : P.A) (r''_batching : Fin κ → L) : L :=
  eqWeightedCoordSum κ L (P.decomposeRows s_hat) r''_batching

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : P.A :=
  let φ₀_mapped_r_suffix : Fin ℓ' → P.A := fun i =>
    P.φ₀ (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → P.A := fun i => P.φ₁ (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`,
where e_u is the row components of e.
Then compute `Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u`.
-/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges
  eqWeightedCoordSum κ L (P.decomposeRows e_tensor) r''_batching

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
    (ctx := stmt.ctx) (t := wit.t')
    (i := i) (challenges := stmt.challenges)
  ).val

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
    Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

end Relations

open Module in
/-- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the tensor-algebra
definitions above: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the decompositions
are the `K`-basis coordinates via the left/right `L`-module structures.

Marked `@[reducible]` so that, once the protocol code is rewired through the profile, references to
`(binaryTowerProfile …).A` (etc.) unfold to `L ⊗[K] L` at reducible transparency — preserving the
existing `rfl`/instance-driven Binius proofs (and the byte-identical `#print axioms`). -/
@[reducible] def binaryTowerProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Module.Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ where
  basis := β
  A := TensorAlgebra K L
  commRingA := inferInstanceAs (CommRing (L ⊗[K] L))
  algLA := Algebra.TensorProduct.leftAlgebra
  φ₀ := φ₀ L K
  φ₁ := φ₁ L K
  decomposeRows := fun s => decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s
  decomposeColumns := fun s => decompose_tensor_algebra_columns (L := L) (K := K) (β := β) s
  decomposeRows_spec := fun z => by
    conv_lhs => rw [← (β.baseChange L).sum_repr z]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold decompose_tensor_algebra_rows
    rw [Basis.baseChange_apply, smul_tmul']
    change _ = (φ₀ L K) _ * (φ₁ L K) _
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeColumns_spec := fun z => by
    let rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    conv_lhs => rw [← (Basis.baseChangeRight (b := β) (Right := L)).sum_repr z]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold decompose_tensor_algebra_columns
    rw [Basis.baseChangeRight_apply, Algebra.smul_def]
    change algebraMap L (L ⊗[K] L) _ * _ = (φ₁ L K) _ * (φ₀ L K) _
    rw [show (algebraMap L (L ⊗[K] L)) =
      (Algebra.TensorProduct.includeRight).toRingHom.comp (algebraMap L L) by rfl]
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]

end RingSwitching
