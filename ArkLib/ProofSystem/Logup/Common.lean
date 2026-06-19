import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Basic

/-!
# LogUp Common Definitions

Shared vocabulary for the LogUp lookup argument formalization, following Protocol 2 of Haböck's
LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The protocol checks that every value in the `M` lookup-column oracles occurs somewhere in the table
oracle. Rows are indexed by the signed hypercube `H = {±1}^n`, represented here as bit vectors and
embedded into a field by `signPoint`. The table oracle and lookup-column oracles are stored in
Lagrange form, so a query at `z : Fin n → F` is the inner product against the kernel `L_H(., z)`.

This file collects the common definitions and algebraic tools reused by the other LogUp files.
-/

namespace Logup

universe u

open scoped BigOperators

/-- The boolean hypercube with `2^n` points.

The paper writes this domain as `H = {±1}^n`; we use bit vectors as row indices and embed
them into a field by `bitToSign`.
-/
@[reducible]
def Hypercube (n : ℕ) : Type :=
  Fin n → Fin 2

/-- Embed a hypercube bit as a `{±1}` field element. -/
def bitToSign (F : Type u) [One F] [Neg F] (b : Fin 2) : F :=
  if b = 0 then -1 else 1

/-- Embed a hypercube row as a point of `{±1}^n ⊂ Fⁿ`. -/
def signPoint (F : Type u) [One F] [Neg F] {n : ℕ} (u : Hypercube n) : Fin n → F :=
  fun j => bitToSign F (u j)

/-- The Lagrange kernel `L_H(x, z) = 2^{-n} * ∏ᵢ (1 + xᵢ zᵢ)` for `H = {±1}^n`. -/
noncomputable def lagrangeKernelAtPoint (F : Type u) [Field F] {n : ℕ}
    (x z : Fin n → F) : F :=
  ((2 : F) ^ n)⁻¹ * ∏ j : Fin n, (1 + x j * z j)

/-- The Lagrange kernel with the first argument restricted to a hypercube row. -/
noncomputable def lagrangeKernel (F : Type u) [Field F] {n : ℕ}
    (u : Hypercube n) (z : Fin n → F) : F :=
  lagrangeKernelAtPoint F (signPoint F u) z

/-- A Lagrange oracle is a function on `H`; queries ask for inner products with `L_H(., z)`. -/
structure LagrangeOracle (F : Type u) (n : ℕ) where
  values : Hypercube n → F

instance {F : Type u} {n : ℕ} : CoeFun (LagrangeOracle F n) (fun _ => Hypercube n → F) where
  coe oracle := oracle.values

/-- A multilinear oracle over the row variables of `H = {±1}^n`, represented in Lagrange form. -/
@[reducible]
def MultilinearOracle (F : Type u) (n : ℕ) : Type u :=
  LagrangeOracle F n

/-- Evaluate a multilinear oracle on a Boolean-hypercube row. -/
def evalOnHypercube {F : Type u} {n : ℕ}
    (p : MultilinearOracle F n) (u : Hypercube n) : F :=
  p u

/-- Lagrange-oracle queries are exactly the paper's inner products with `L_H(., z)`. -/
noncomputable instance instLagrangeOracleInterface {F : Type u} [Field F] {n : ℕ} :
    OracleInterface (LagrangeOracle F n) where
  Query := Fin n → F
  toOC.spec := (Fin n → F) →ₒ F
  toOC.impl z := do
    let oracle ← read
    return ∑ u : Hypercube n, oracle u * lagrangeKernel F u z

/-- The semantic value returned by querying a Lagrange-form multilinear oracle at `z`. -/
noncomputable def lagrangeOracleEval {F : Type u} [Field F] {n : ℕ}
    (oracle : MultilinearOracle F n) (z : Fin n → F) : F :=
  ∑ u : Hypercube n, oracle u * lagrangeKernel F u z

/-- Input oracle labels for Protocol 2: one table oracle and `M` lookup-column oracles. -/
inductive InputOracleIdx (M : ℕ) where
  | table : InputOracleIdx M
  | column : Fin M → InputOracleIdx M
deriving DecidableEq

/-- Term labels `0, ..., M` from the paper, with `0` denoting the table term. -/
@[reducible]
def TermIdx (M : ℕ) : Type :=
  Fin (M + 1)

/-- Interpret term index `0` as the table and term indices `1, ..., M` as lookup columns. -/
def termToInput {M : ℕ} (i : TermIdx M) : InputOracleIdx M :=
  if h : i.val = 0 then
    .table
  else
    .column ⟨i.val - 1, by omega⟩

/-- Interpret input-oracle labels as term indices `0, ..., M`. -/
def inputToTerm {M : ℕ} : InputOracleIdx M → TermIdx M
  | .table => ⟨0, by omega⟩
  | .column i => ⟨i.val + 1, by omega⟩

/-- Protocol parameter `ℓ`, the chosen partial-sum size from Protocol 2. -/
structure ProtocolParams (M : ℕ) where
  /-- The partial-sum size `ℓ`. -/
  sumSize : ℕ
  /-- Protocol 2 requires `1 ≤ ℓ`. -/
  sumSize_pos : 0 < sumSize
  /-- Protocol 2 requires `ℓ ≤ M + 1`. -/
  sumSize_le : sumSize ≤ M + 1

namespace ProtocolParams

/-- The number of partial-sum groups `K = ceil((M + 1) / ℓ)`. -/
def numGroups {M : ℕ} (params : ProtocolParams M) : ℕ :=
  (M + params.sumSize) / params.sumSize

/-- The consecutive interval `Iₖ = [(k - 1)ℓ, kℓ) ∩ [0, M]`, zero-indexed. -/
def group {M : ℕ} (params : ProtocolParams M) (k : Fin params.numGroups) :
    Finset (TermIdx M) :=
  Finset.univ.filter fun i : TermIdx M =>
    k.val * params.sumSize ≤ i.val ∧ i.val < (k.val + 1) * params.sumSize

end ProtocolParams

/-- Public parameter assumptions for Protocol 2.

The paper fixes a finite field with characteristic larger than `M * 2^n`; we also record that
`-1` and `1` are distinct so that `{±1}^n` is genuinely a Boolean hypercube in the field.
-/
structure StmtIn (F : Type u) [Field F] [Fintype F] (n M : ℕ) : Type u where
  /-- The paper's characteristic condition `char(F) > M * 2^n`. -/
  charLarge : M * 2 ^ n < ringChar F
  /-- The two signs used for the hypercube are distinct. -/
  signsDistinct : (-1 : F) ≠ 1

/-- Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles. -/
@[reducible, simp]
def OStmtIn (F : Type u) (n M : ℕ) : InputOracleIdx M → Type u
  | .table => MultilinearOracle F n
  | .column _ => MultilinearOracle F n

/-- Input LogUp oracles are accessed by evaluating their multilinear polynomial extensions. -/
noncomputable instance instOStmtInOracleInterface {F : Type u} [Field F] {n M : ℕ} :
    ∀ i, OracleInterface (OStmtIn F n M i)
  | .table => inferInstance
  | .column _ => inferInstance

/-- Accessor for the input table oracle `t`. -/
@[reducible, simp]
def tableOracle {F : Type u} {n M : ℕ}
    (oStmt : ∀ i, OStmtIn F n M i) : MultilinearOracle F n :=
  oStmt .table

/-- Accessor for the `i`-th lookup-column oracle `fᵢ`. -/
@[reducible, simp]
def columnOracle {F : Type u} {n M : ℕ}
    (oStmt : ∀ i, OStmtIn F n M i) (i : Fin M) : MultilinearOracle F n :=
  oStmt (.column i)

/-- Semantic input relation for Protocol 2: every lookup-column value occurs in the table range. -/
def inputRelation (F : Type u) [Field F] [Fintype F] (n M : ℕ) :
    Set ((StmtIn F n M × (∀ i, OStmtIn F n M i)) × Unit) :=
  { ⟨⟨_, oStmt⟩, _⟩ |
    ∀ i : Fin M, ∀ x : Hypercube n, ∃ y : Hypercube n,
      evalOnHypercube (columnOracle oStmt i) x = evalOnHypercube (tableOracle oStmt) y }

/-- The full LogUp protocol returns no additional public data on success. -/
@[reducible, simp]
def StmtOut : Type :=
  Unit

/-- The full LogUp protocol leaves no output oracle statements. -/
@[reducible, simp]
def OutputOracleIdx : Type :=
  Fin 0

/-- Output oracle statements for the full LogUp protocol. -/
@[reducible, simp]
def OStmtOut : OutputOracleIdx → Type :=
  fun i => Fin.elim0 i

/-- The full LogUp protocol has no output oracle interfaces to provide. -/
instance instOStmtOutOracleInterface :
    ∀ i, OracleInterface (OStmtOut i) :=
  fun i => Fin.elim0 i

/-- The full protocol has a trivial final relation: successful verification returns `Unit`. -/
def outputRelation : Set ((StmtOut × (∀ i, OStmtOut i)) × Unit) :=
  Set.univ

section ProtocolSpec

/-- The prover's first Protocol 2 message: the multiplicity function `m : H → F`. -/
@[reducible, simp]
def MultiplicityMessage (F : Type) (n : ℕ) : Type :=
  MultilinearOracle F n

/-- The prover's second Protocol 2 message: helper functions `h₁, ..., h_K : H → F`. -/
@[reducible, simp]
def HelperMessages (F : Type) (n K : ℕ) : Type :=
  Fin K → MultilinearOracle F n

/-- The verifier's second outer challenge: `z ∈ Fⁿ` and batching scalars `λ₁, ..., λ_K`. -/
@[reducible, simp]
def BatchingChallenge (F : Type) (n K : ℕ) : Type :=
  (Fin n → F) × (Fin K → F)

end ProtocolSpec

section OuterIO

variable (F : Type) [Field F] [Fintype F] (n M : ℕ) (params : ProtocolParams M)

/-- The outer LogUp statement after the verifier has sampled `x`, `z`, and `λ`. -/
structure StmtAfterOuter where
  /-- The logarithmic-derivative challenge `x`. -/
  xChallenge : F
  /-- The Lagrange-kernel point `z ∈ Fⁿ`. -/
  zChallenge : Fin n → F
  /-- The batching scalars `λ₁, ..., λ_K`. -/
  batchingScalars : Fin params.numGroups → F

/-- Oracle labels retained after the outer LogUp phase. -/
inductive OuterOracleIdx (M : ℕ) where
  | input : InputOracleIdx M → OuterOracleIdx M
  | multiplicity : OuterOracleIdx M
  | helpers : OuterOracleIdx M
deriving DecidableEq

/-- Oracle statements retained after the outer LogUp phase. -/
@[reducible, simp]
def OStmtAfterOuter (F : Type) [Field F] (n M : ℕ) (params : ProtocolParams M) :
    OuterOracleIdx M → Type
  | .input i => OStmtIn F n M i
  | .multiplicity => MultiplicityMessage F n
  | .helpers => HelperMessages F n params.numGroups

/-- Oracle interfaces for all oracle statements retained after the outer LogUp phase. -/
noncomputable instance instOStmtAfterOuterOracleInterface
    {F : Type} [Field F] {n M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface (OStmtAfterOuter F n M params i)
  | .input i => inferInstanceAs (OracleInterface (OStmtIn F n M i))
  | .multiplicity => inferInstanceAs (OracleInterface (MultiplicityMessage F n))
  | .helpers => inferInstanceAs (OracleInterface (HelperMessages F n params.numGroups))

/-- Protocol 2 has no private witness beyond the input oracles at this layer. -/
@[reducible, simp]
def WitIn (F : Type u) [Field F] [Fintype F] (_n M : ℕ) (_params : ProtocolParams M) : Type :=
  Unit

end OuterIO

section ProtocolAlgebra

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}
variable (params : ProtocolParams M)

/-- A decomposition of the term indices `{0, ..., M}` into the partial-sum groups `Iₖ`. -/
@[reducible]
def PartialSumGroups (M K : ℕ) : Type :=
  Fin K → Finset (TermIdx M)

/-- The paper's canonical consecutive groups `Iₖ`, derived from the parameter `ℓ`. -/
def canonicalGroups : PartialSumGroups M params.numGroups :=
  fun k => params.group k

/-- Outer transcript data produced before entering the embedded sumcheck. -/
structure OuterTranscriptData (F : Type) [Field F] [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) where
  /-- The multiplicity function `m : H → F`. -/
  multiplicity : MultiplicityMessage F n
  /-- The verifier challenge `x : F`. -/
  xChallenge : F
  /-- The helper functions `h₁, ..., h_K : H → F`. -/
  helpers : HelperMessages F n params.numGroups
  /-- The Lagrange-kernel point `z ∈ Fⁿ`. -/
  zChallenge : Fin n → F
  /-- The batching scalars `λ₁, ..., λ_K`. -/
  batchingScalars : Fin params.numGroups → F

/-- Number of table rows with value `a`. -/
def tableMultiplicityCount (oStmt : ∀ i, OStmtIn F n M i) (a : F) : ℕ :=
  ((Finset.univ : Finset (Hypercube n)).filter fun u =>
    evalOnHypercube (tableOracle oStmt) u = a).card

/-- Total number of lookup-column entries with value `a`. -/
def lookupMultiplicityCount (oStmt : ∀ i, OStmtIn F n M i) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun ix =>
    evalOnHypercube (columnOracle oStmt ix.1) ix.2 = a).card

/-- The normalized multiplicity from paper equation (14), evaluated at one table row. -/
noncomputable def normalizedMultiplicityValue (oStmt : ∀ i, OStmtIn F n M i)
    (u : Hypercube n) : F :=
  let a := evalOnHypercube (tableOracle oStmt) u
  (lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F)

/-- The honest multiplicity oracle `m : H → F` from paper equation (14). -/
noncomputable def honestMultiplicity (oStmt : ∀ i, OStmtIn F n M i) :
    MultiplicityMessage F n :=
  ⟨fun u => normalizedMultiplicityValue oStmt u⟩

/-- The denominator term `φᵢ(u)` from Protocol 2. -/
noncomputable def phi (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    InputOracleIdx M → Hypercube n → F
  | .table => fun u => xChallenge + evalOnHypercube (tableOracle oStmt) u
  | .column i => fun u => xChallenge + evalOnHypercube (columnOracle oStmt i) u

/-- The numerator term `mᵢ(u)` from Protocol 2, with `m₀ = m` and `mᵢ = -1` for columns. -/
noncomputable def numerator (multiplicity : MultilinearOracle F n) :
    InputOracleIdx M → Hypercube n → F
  | .table => evalOnHypercube multiplicity
  | .column _ => fun _ => -1

/-- The denominator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termPhi (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F)
    (i : TermIdx M) (u : Hypercube n) : F :=
  phi oStmt xChallenge (termToInput i) u

/-- The numerator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termNumerator (multiplicity : MultilinearOracle F n)
    (i : TermIdx M) (u : Hypercube n) : F :=
  numerator multiplicity (termToInput i) u

/-- Product of the denominator terms in one partial-sum group. -/
noncomputable def denominatorProduct (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  ∏ i ∈ groups k, termPhi oStmt xChallenge i u

/-- The domain-identity expression for one helper function `hₖ`. -/
noncomputable def domainIdentityTerm (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  evalOnHypercube (helpers k) u * denominatorProduct groups oStmt xChallenge k u -
    ∑ i ∈ groups k,
      termNumerator multiplicity i u * ∏ j ∈ (groups k).erase i, termPhi oStmt xChallenge j u

/-- The helper value `hₖ(u) = Σᵢ mᵢ(u)/φᵢ(u)` from paper equation (16). -/
noncomputable def helperValue (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  ∑ i ∈ groups k, termNumerator multiplicity i u / termPhi oStmt xChallenge i u

/-- The honest helper oracle `hₖ : H → F` for one partial-sum group. -/
noncomputable def helperOracle (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (xChallenge : F) (k : Fin K) : MultilinearOracle F n :=
  ⟨fun u => helperValue groups oStmt multiplicity xChallenge k u⟩

/-- The honest helper-oracle bundle `h₁, ..., h_K` from paper equation (16). -/
noncomputable def honestHelpers (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    HelperMessages F n params.numGroups :=
  let multiplicity := honestMultiplicity oStmt
  fun k => helperOracle (canonicalGroups params) oStmt multiplicity xChallenge k

/-- The batched polynomial expression `Q` from paper equation (18), evaluated on a row `u ∈ H`. -/
noncomputable def qOnHypercube (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (xChallenge : F) (zChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (u : Hypercube n) : F :=
  ∑ k : Fin K, (
    evalOnHypercube (helpers k) u +
      lagrangeKernel F u zChallenge * batchingScalars k *
        domainIdentityTerm groups oStmt multiplicity helpers xChallenge k u)

/-- Point evaluations queried by the verifier at the final sumcheck point `r`. -/
structure PointEvaluations (F : Type) (M K : ℕ) where
  /-- Claimed value `m(r)`. -/
  multiplicity : F
  /-- Claimed value `t(r)`. -/
  table : F
  /-- Claimed values `fᵢ(r)`. -/
  columns : Fin M → F
  /-- Claimed values `hₖ(r)`. -/
  helpers : Fin K → F

/-- Denominator term at the final sumcheck point, reconstructed from oracle query answers. -/
def phiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) :
    InputOracleIdx M → F
  | .table => xChallenge + evals.table
  | .column i => xChallenge + evals.columns i

/-- Numerator term at the final sumcheck point, reconstructed from oracle query answers. -/
def numeratorAtPoint (evals : PointEvaluations F M K) : InputOracleIdx M → F
  | .table => evals.multiplicity
  | .column _ => -1

/-- Term denominator at the final sumcheck point, indexed by `0, ..., M`. -/
def termPhiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  phiAtPoint xChallenge evals (termToInput i)

/-- Term numerator at the final sumcheck point, indexed by `0, ..., M`. -/
def termNumeratorAtPoint (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  numeratorAtPoint evals (termToInput i)

/-- The domain-identity expression at the final sumcheck point `r`. -/
noncomputable def domainIdentityAtPoint (groups : PartialSumGroups M K)
    (xChallenge : F) (evals : PointEvaluations F M K) (k : Fin K) : F :=
  evals.helpers k * (∏ i ∈ groups k, termPhiAtPoint xChallenge evals i) -
    ∑ i ∈ groups k,
      termNumeratorAtPoint evals i *
        ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge evals j

/-- The verifier's final check value `Q(L_H(r,z), m(r), φᵢ(r), hₖ(r))` from paper (19). -/
noncomputable def qAtPoint (groups : PartialSumGroups M K) (xChallenge : F)
    (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (evals : PointEvaluations F M K) : F :=
  ∑ k : Fin K, (
    evals.helpers k +
      lagrangeKernelAtPoint F rChallenge zChallenge * batchingScalars k *
        domainIdentityAtPoint groups xChallenge evals k)

/-- Predicate for paper step 4: final oracle-query answers match the sumcheck's expected value. -/
noncomputable def finalQueryCheck (groups : PartialSumGroups M K) (xChallenge : F)
    (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (evals : PointEvaluations F M K) (expectedValue : F) : Prop :=
  qAtPoint groups xChallenge zChallenge rChallenge batchingScalars evals = expectedValue

end ProtocolAlgebra

end Logup
