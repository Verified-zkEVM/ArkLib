/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Order.Floor.Div
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.OracleInterface
import ArkLib.ProofSystem.Logup.Algebra
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# LogUp Protocol

Protocol specs, honest prover, verifier, and oracle reductions for Protocol 2 of Haböck's LogUp
lookup argument (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The protocol checks that every value in the `M` lookup-column oracles occurs somewhere in the table
oracle.

## Protocol Specification

The LogUp protocol is parameterized by:
- a field `F`;
- a row dimension `n`, with rows indexed by the Boolean hypercube `H = {±1}ⁿ`;
- `M` lookup-column oracles `fᵢ : H → F` and one table oracle `t : H → F`;
- a partial-sum size `ℓ` (`1 ≤ ℓ ≤ M + 1`), stored in `ProtocolParams`, which determines the number
  `K = ⌈(M + 1) / ℓ⌉` of helper oracles; and
- the characteristic condition `char(F) > M * 2^n`.

### The relation and its logarithmic-derivative reformulation

The input relation is the set inclusion `⋃ᵢ {fᵢ(u) : u ∈ H} ⊆ {t(u) : u ∈ H}`: every value
appearing in any lookup column also appears somewhere in the table. Under the characteristic
condition, Lemma 5 of the paper makes this equivalent to the existence of a multiplicity function
`m : H → F` satisfying the rational identity (paper eq. (13))

  `∑ u ∈ H, ∑ i ∈ [1, M], 1 / (X + fᵢ(u)) = ∑ u ∈ H, m(u) / (X + t(u))` in `F(X)`.

The canonical witness is the normalized multiplicity (paper eq. (14)),
`m(u) = (∑ᵢ #{y ∈ H : fᵢ(y) = t(u)}) / #{y ∈ H : t(y) = t(u)}`, which counts how often the table
value `t(u)` is used across the lookup columns (and equals the plain count when `t` is injective).

### The protocol

1. The prover sends the multiplicity oracle `m`. The verifier samples the logarithmic-derivative
   challenge `x ←$ F`. The paper draws `x ∉ {-t(u) : u ∈ H}` by rejection sampling so that every
   denominator is nonzero; following Remark 3, this formalization instead samples `x` uniformly from
   all of `F` and absorbs the rare bad event (a vanishing denominator) into the completeness error,
   avoiding the rejection-sampling constraint. Specializing the identity above at `X = x` and
   clearing it to one side gives the scalar claim (paper eq. (15))

     `∑ u ∈ H, (∑ i ∈ [1, M], 1 / (x + fᵢ(u))) - m(u) / (x + t(u)) = 0`.

   It is convenient to fold the table and columns into `M + 1` indexed terms (paper notation):
   `m₀ = m`, `ϕ₀(u) = x + t(u)`, and `mᵢ = -1`, `ϕᵢ(u) = x + fᵢ(u)` for `i = 1, ..., M`, so the
   summand is `∑ i ∈ [0, M], mᵢ(u) / ϕᵢ(u)`.

2. The denominator index set `[0, M]` is partitioned into the `K` consecutive groups
   `Iₖ = [(k-1)ℓ, kℓ) ∩ [0, M]`. For each group the prover forms the partial sum (paper eq. (16))
   `hₖ(u) = ∑ i ∈ Iₖ, mᵢ(u) / ϕᵢ(u)` and sends the helper oracles `h₁, ..., h_K`. By construction
   the helpers sum to zero, `∑ u ∈ H, (h₁(u) + ... + h_K(u)) = 0`, and each obeys the
   cleared-denominator *domain identity* (paper eq. (17))

     `hₖ(u) * (∏ i ∈ Iₖ, ϕᵢ(u)) = ∑ i ∈ Iₖ, mᵢ(u) * (∏ j ∈ Iₖ \ {i}, ϕⱼ(u))`   for all `u ∈ H`.

3. The verifier samples a point `z : Fin n → F` and batching scalars `λ₁, ..., λ_K`. Multiplying the
   domain identities by the Lagrange kernel `L_H(·, z)` turns each "for all `u ∈ H`" identity into a
   zero-sum over `H`, and the `λ`-batching collapses the `K` domain identities together with the
   helper zero-sum into the single batched polynomial `Q` (paper eq. (18))

     `Q = ∑ k ∈ [1, K], (hₖ + L * λₖ * (hₖ * ∏ i ∈ Iₖ, ϕᵢ - ∑ i ∈ Iₖ, mᵢ * ∏ j ∈ Iₖ \ {i}, ϕⱼ))`,

   where `L = L_H(u, z)`. Prover and verifier then run generic sumcheck (Protocol 1) on the claim
   `∑ u ∈ H, Q(L_H(u, z), m(u), ϕ₀(u), ..., ϕ_M(u), h₁(u), ..., h_K(u)) = 0`.

4. Sumcheck leaves a final point `r : Fin n → F` and a claimed value `v` for the polynomial of
   paper eq. (19) at `r`. The verifier queries the retained LogUp oracles `m, t, f₁, ..., f_M`,
   `h₁, ..., h_K` at `r`, computes the kernel value `L_H(r, z)` itself, reconstructs `Q(r)` from
   these answers, and accepts only if this reconstructed value equals `v`.

### Formalization

The LogUp paper writes the row domain as `{±1}^n`; this formalization uses the affine-equivalent
Boolean hypercube together with ArkLib's existing equality polynomial and
[`MLE`](ArkLib/Data/MvPolynomial/Multilinear.lean) definitions.

The formalization is split into three ArkLib reductions.

* The outer LogUp phase sends the multiplicity oracle `m`, samples the challenge `x`, sends the
  helper oracles, and samples the batching challenge `(z, lambda)`. At the end of this phase, the
  verifier has the data needed to state a single zero-sum claim about the LogUp polynomial `Q`.
* The sumcheck phase runs ArkLib's generic sumcheck on the claim that `Q` sums to zero. The
  *polynomial and all of LogUp's fractional-identity algebra* are protocol-agnostic and live in
  [`Algebra`](ArkLib/ProofSystem/Logup/Algebra.lean), parameterized on bare oracle functions. This
  file supplies the oracle data from the retained LogUp oracles and connects the two worlds through
  the context lens `logupSumcheckContextLens`.
* The final zero-round phase queries the retained LogUp oracles at sumcheck's final point and checks
  that those oracle values really give the value claimed by sumcheck.

This file holds the LogUp *interactive oracle reduction* itself: the oracle representation types,
the input/output statements and relations, the sumcheck bridge and context lens, the transcript
shapes, the prover/verifier objects, and the oracle reductions for each phase and the composed
protocol.

The main artefacts that define the protocol are `pSpec`, `logupProver`, `logupVerifier`,
and `logupOracleReduction`.

-/

namespace Logup

universe u

open scoped BigOperators MvPolynomial

/-! # Phase 1 — Outer LogUp

The input boundary, outer transcript, honest multiplicity/helper messages, outer prover/verifier,
and first oracle reduction. -/

section Phase1

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

/-- `numGroups` really is the ceiling `⌈(M + 1) / ℓ⌉`: the floor-division formula
`(M + ℓ) / ℓ` agrees with `Nat.ceilDiv` because `ℓ ≥ 1` (`sumSize_pos`). -/
theorem numGroups_eq_ceilDiv {M : ℕ} (params : ProtocolParams M) :
    params.numGroups = (M + 1) ⌈/⌉ params.sumSize := by
  have h := params.sumSize_pos
  rw [Nat.ceilDiv_eq_add_pred_div]
  unfold numGroups
  congr 1
  omega

/-- The consecutive interval `Iₖ = [(k - 1)ℓ, kℓ) ∩ [0, M]`, zero-indexed. -/
def group {M : ℕ} (params : ProtocolParams M) (k : Fin params.numGroups) :
    Finset (TermIdx M) :=
  Finset.univ.filter fun i : TermIdx M =>
    k.val * params.sumSize ≤ i.val ∧ i.val < (k.val + 1) * params.sumSize

end ProtocolParams

/-- Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear polynomials
(reusing ArkLib's bounded-degree polynomial oracle, queried by evaluation). -/
@[reducible, simp]
def OStmtIn (F : Type u) [CommSemiring F] (n M : ℕ) : InputIdx M → Type u
  | .table => F⦃≤ 1⦄[X (Fin n)]
  | .column _ => F⦃≤ 1⦄[X (Fin n)]

/-- Input LogUp oracles are accessed by evaluating their multilinear polynomial extensions. -/
noncomputable instance instOStmtInOracleInterface {F : Type u} [Field F] {n M : ℕ} :
    ∀ i, OracleInterface (OStmtIn F n M i)
  | .table => inferInstance
  | .column _ => inferInstance

/-- The prover's first Protocol 2 message: the multiplicity function `m : H → F`, as a
multilinear polynomial. -/
@[reducible, simp]
def MultiplicityMessage (F : Type) [CommSemiring F] (n : ℕ) : Type :=
  F⦃≤ 1⦄[X (Fin n)]

/-- The prover's second Protocol 2 message: helper functions `h₁, ..., h_K : H → F`, as
multilinear polynomials. -/
@[reducible, simp]
def HelperMessages (F : Type) [CommSemiring F] (n K : ℕ) : Type :=
  Fin K → F⦃≤ 1⦄[X (Fin n)]

/-- The verifier's second outer challenge: `z ∈ Fⁿ` and batching scalars `λ₁, ..., λ_K`. -/
@[reducible, simp]
def BatchingChallenge (F : Type) (n K : ℕ) : Type :=
  (Fin n → F) × (Fin K → F)

variable (F : Type) [Field F] [Fintype F] (n M : ℕ) (params : ProtocolParams M)

/-- The outer LogUp statement after the verifier has sampled `x`, `z`, and `λ`. -/
structure StmtAfterOuter where
  /-- The logarithmic-derivative challenge `x`. -/
  xChallenge : F
  /-- The equality-kernel point `z ∈ Fⁿ`. -/
  zChallenge : Fin n → F
  /-- The batching scalars `λ₁, ..., λ_K`. -/
  batchingScalars : Fin params.numGroups → F

/-- Oracle labels retained after the outer LogUp phase. -/
inductive OuterOracleIdx (M : ℕ) where
  | input : InputIdx M → OuterOracleIdx M
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


variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
variable (params : ProtocolParams M)


/-- The honest multiplicity oracle `m : H → F` from paper equation (14), as the multilinear
extension of the normalized-multiplicity table. -/
noncomputable def honestMultiplicity (oStmt : ∀ i, OStmtIn F n M i) : MultiplicityMessage F n :=
  (MvPolynomial.MLEEquiv (R := F) (σ := Fin n)).symm
    (normalizedMultiplicityValue (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
      (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1))

/-- The honest helper-oracle bundle `h₁, ..., h_K` from paper equation (16). -/
noncomputable def honestHelpers (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    HelperMessages F n params.numGroups :=
  fun k =>
    (MvPolynomial.MLEEquiv (R := F) (σ := Fin n)).symm
      (helperValue (params.group) (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
        (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
        (MvPolynomial.toEvalsZeroOne (honestMultiplicity oStmt).1) xChallenge k)

/-- Public parameter assumptions for Protocol 2. -/
structure StmtIn (F : Type u) [Field F] [Fintype F] (n M : ℕ) : Type u where
  /-- The paper's characteristic condition `char(F) > M * 2^n`. -/
  charLarge : M * 2 ^ n < ringChar F

/-- Semantic input relation for Protocol 2: every lookup-column value occurs in the table range. -/
def inputRelation (F : Type u) [Field F] [Fintype F] (n M : ℕ) :
    Set ((StmtIn F n M × (∀ i, OStmtIn F n M i)) × Unit) :=
  { ⟨⟨_, oStmt⟩, _⟩ |
    ∀ i : Fin M, ∀ x : (Fin n → Fin 2), ∃ y : (Fin n → Fin 2),
      MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 x
        = MvPolynomial.toEvalsZeroOne (oStmt .table).1 y }

open ProtocolSpec

/-- The four outer messages of Protocol 2.

The transcript shape is:
1. `P → V`: multiplicity oracle `m`.
2. `V → P`: challenge `x`.
3. `P → V`: helper oracles `h₁, ..., h_K`.
4. `V → P`: challenge `(z, λ)`.
-/
@[reducible]
def outerPSpec (F : Type) [Field F] (n : ℕ) {M : ℕ} (params : ProtocolParams M) : ProtocolSpec 4 :=
  ⟨!v[.P_to_V], !v[MultiplicityMessage F n]⟩ ++ₚ
    ⟨!v[.V_to_P], !v[F]⟩ ++ₚ
    ⟨!v[.P_to_V], !v[HelperMessages F n params.numGroups]⟩ ++ₚ
    ⟨!v[.V_to_P], !v[BatchingChallenge F n params.numGroups]⟩

/-- The prover messages in the outer LogUp transcript are oracle-accessible. -/
noncomputable instance instOuterPSpecMessageOracleInterface
    {F : Type} [Field F] {n M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface ((outerPSpec F n params).Message i) := by
  intro i
  rcases i with ⟨⟨idx, hidx⟩, hi⟩
  rcases idx with _ | idx
  · exact inferInstanceAs (OracleInterface (MultiplicityMessage F n))
  rcases idx with _ | idx
  · exact OracleInterface.instDefault
  rcases idx with _ | idx
  · exact inferInstanceAs (OracleInterface (HelperMessages F n params.numGroups))
  rcases idx with _ | idx
  · exact OracleInterface.instDefault
  omega

/-- The verifier challenges in the outer LogUp transcript are sampled uniformly from their types. -/
instance instOuterPSpecChallengeSampleable
    {F : Type} [Field F] [Fintype F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((outerPSpec F n params).Challenge i)
  | ⟨0, h0⟩ => by
      change Direction.P_to_V = Direction.V_to_P at h0
      cases h0
  | ⟨1, _⟩ => by
      change SampleableType F
      infer_instance
  | ⟨2, h2⟩ => by
      change Direction.P_to_V = Direction.V_to_P at h2
      cases h2
  | ⟨3, _⟩ => by
      -- `BatchingChallenge` is a product type, and VCVio's `SampleableType (α × β)` instance
      -- requires `Inhabited` on each factor; supply it from the field's zero.
      letI : Inhabited F := ⟨0⟩
      change SampleableType (BatchingChallenge F n params.numGroups)
      infer_instance

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The outer LogUp prover state. -/
def outerProverState : Fin 5 → Type
  | 0 => ∀ i, OStmtIn F n M i
  | 1 => ∀ i, OStmtIn F n M i
  | 2 => (∀ i, OStmtIn F n M i) × F
  | 3 => (∀ i, OStmtIn F n M i) × F
  | 4 => (∀ i, OStmtIn F n M i) × F × BatchingChallenge F n params.numGroups

/-- The honest prover for the outer LogUp phase. -/
noncomputable def outerProver :
    OracleProver oSpec (StmtIn F n M) (OStmtIn F n M) (Unit)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (outerPSpec F n params) where
  PrvState := outerProverState F n M params

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt

  sendMessage
  | ⟨0, _⟩ => fun oStmt => pure (honestMultiplicity oStmt, oStmt)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun state => pure (honestHelpers params state.1 state.2, state)
  | ⟨3, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun oStmt => pure fun x => (oStmt, x)
  | ⟨2, h⟩ => nomatch h
  | ⟨3, _⟩ => fun state => pure fun batch => (state.1, state.2, batch)

  output := fun state =>
    let oStmt := state.1
    let x := state.2.1
    let batch := state.2.2
    pure (({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
      fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt x),
      ())

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

@[grind]
def outerChallengeXIdx : (outerPSpec F n params).ChallengeIdx :=
  ⟨1, rfl⟩

@[grind]
def outerChallengeBatchIdx : (outerPSpec F n params).ChallengeIdx :=
  ⟨3, rfl⟩

@[grind]
def outerMultiplicityMessageIdx : (outerPSpec F n params).MessageIdx :=
  ⟨0, rfl⟩

@[grind]
def outerHelpersMessageIdx : (outerPSpec F n params).MessageIdx :=
  ⟨2, rfl⟩

/-- The verifier for the outer LogUp phase. -/
noncomputable def outerVerifier :
    OracleVerifier oSpec (StmtIn F n M) (OStmtIn F n M)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (outerPSpec F n params) where
  verify := fun _ challenges => do
    let x : F := challenges (outerChallengeXIdx F n M params)
    -- Following Remark 3 of the LogUp paper, the verifier samples `x` uniformly and does not
    -- scan the table to reject poles. Pole challenges are treated as bad/failing inputs for the
    -- honest handoff, and `Completeness.lean` accounts for that event.
    let batch : BatchingChallenge F n params.numGroups :=
      challenges (outerChallengeBatchIdx F n M params)
    pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }

  embed :=
    { toFun := fun
        | .input i => .inl i
        | .multiplicity => .inr (outerMultiplicityMessageIdx F n M params)
        | .helpers => .inr (outerHelpersMessageIdx F n M params)
      inj' := by
        intro a b h
        cases a with grind
    }

  hEq := by
    intro i
    cases i with
    | input j => rfl
    | multiplicity => rfl
    | helpers => rfl

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The outer LogUp phase as an ArkLib oracle reduction. -/
noncomputable def outerOracleReduction :
    OracleReduction oSpec (StmtIn F n M) (OStmtIn F n M) (Unit)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (outerPSpec F n params) where
  prover := outerProver oSpec F n M params
  verifier := outerVerifier oSpec F n M params

end Phase1


/-! # Phase 2 — Sumcheck

Runs ArkLib's generic sumcheck on the zero-sum claim for LogUp's polynomial `Q`. Contains the
bridge packaging `Q` for generic sumcheck, the context lens, the lifted prover/verifier, and
the assembled oracle reduction. -/

section Phase2

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Individual-degree bound for LogUp's embedded sumcheck polynomial. -/
def logupSumcheckDegree (_params : ProtocolParams M) : ℕ :=
  M + 3

/-- LogUp state after the embedded sumcheck, before the final oracle-query check. -/
structure StmtAfterSumcheck where
  /-- The outer transcript data retained for reconstructing `Q(r)`. -/
  outer : StmtAfterOuter F n M params
  /-- Sumcheck's final point claim `Q(r) = v`. -/
  finalClaim : (Sumcheck.Spec.StatementRound F n (.last n))


/-- LogUp enters the embedded sumcheck with the zero-sum claim. -/
def logupInitialSumcheckStatement : (Sumcheck.Spec.StatementRound F n 0) where
  target := 0
  challenges := fun i => Fin.elim0 i

/-- Package `logupQPolynomial` with its degree certificate into ArkLib's oracle statement type. -/
noncomputable def logupSumcheckPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    (Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params)) () := by
  classical
  refine ⟨logupQPolynomial (params.group) (oStmt (.input .table)).1
      (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
      (fun k => (oStmt .helpers k).1) stmt.xChallenge stmt.zChallenge stmt.batchingScalars, ?_⟩
  rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
  intro i
  exact logupQPolynomial_degreeOf (params.group)
    ((MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp (oStmt (.input .table)).2)
    (fun j => (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp
    (oStmt (.input (.column j))).2) ((MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp
    (oStmt .multiplicity).2) (fun k => (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp
    (oStmt .helpers k).2) stmt.xChallenge stmt.zChallenge stmt.batchingScalars i

/-- Package the LogUp `Q` polynomial as the single oracle statement expected by Sumcheck. -/
noncomputable def logupSumcheckOracleStmt
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    ∀ i, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) i :=
  fun _ => logupSumcheckPolynomial F n M params stmt oStmt

/-- The LogUp zero-sum claim that is fed to the generic sumcheck. -/
noncomputable def logupOuterSumcheckClaim
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : F :=
  ∑ u : (Fin n → Fin 2),
    MvPolynomial.eval (u : Fin n → F)
      (logupQPolynomial (params.group) (oStmt (.input .table)).1
        (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
        (fun k => (oStmt .helpers k).1) stmt.xChallenge stmt.zChallenge stmt.batchingScalars)

/-- Relation handed from the outer LogUp phase to the embedded sumcheck: the outer algebra produced
a genuine zero-sum claim. -/
def logupMidRelation :
    Set ((StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) :=
  { x | logupOuterSumcheckClaim F n M params x.1.1 x.1.2 = 0 }

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The Boolean sumcheck domain, packaged in the form expected by `Sumcheck.Spec`. -/
def booleanDomain : Fin 2 ↪ F where
  toFun := fun b => (b : F)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · simp at h
    · simp at h
    · rfl

/-- Relation after embedded sumcheck: the final sumcheck point claim is valid for the retained
LogUp polynomial. The final LogUp phase consumes this by querying the retained oracles at that
point and recomputing `Q(r)`. -/
def logupAfterSumcheckRelation :
    Set ((StmtAfterSumcheck F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) :=
  { x |
    ((x.1.1.finalClaim,
        logupSumcheckOracleStmt F n M params x.1.1.outer x.1.2), ()) ∈
      Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n) }

/-- The initial generic Sumcheck relation induced by a LogUp outer transcript. -/
def logupSumcheckRelationInput
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ((logupInitialSumcheckStatement F n, logupSumcheckOracleStmt F n M params stmt oStmt),
      ()) ∈
    Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Context lens from LogUp's retained outer state to ArkLib's generic Sumcheck state.

The projection builds the generic zero-sum claim and its single polynomial oracle. The lift keeps
the outer LogUp data and retained oracles together with Sumcheck's final point claim, so the next
LogUp phase can perform the paper's final oracle-query check.
-/
noncomputable def logupSumcheckContextLens :
    OracleContext.Lens
      (StmtAfterOuter F n M params) (StmtAfterSumcheck F n M params)
      ((Sumcheck.Spec.StatementRound F n 0)) ((Sumcheck.Spec.StatementRound F n (.last n)))
      (OStmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params))
      (Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params))
      Unit Unit Unit Unit where
  stmt :=
    ⟨fun ctx =>
        (logupInitialSumcheckStatement F n,
          logupSumcheckOracleStmt F n M params ctx.1 ctx.2),
      fun ctx inner =>
        ({ outer := ctx.1, finalClaim := inner.1 }, ctx.2)⟩
  wit :=
    ⟨fun _ => (),
      fun _ _ => ()⟩

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- ArkLib's generic sumcheck reduction specialized to LogUp's Boolean domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleReduction [SampleableType F] :
    OracleReduction oSpec ((Sumcheck.Spec.StatementRound F n 0))
      (Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params)) Unit
      ((Sumcheck.Spec.StatementRound F n (.last n)))
      (Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params)) Unit
      ((Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)) :=
  Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params)
    (booleanDomain F) n oSpec

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The prover for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckProver :
    OracleProver oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params) Unit
      ((Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)) :=
  (logupConcreteSumcheckOracleReduction oSpec F n M params).prover.liftContext
    (logupSumcheckContextLens F n M params)

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The verifier for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckVerifier [SampleableType F] :
    OracleVerifier oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params)
      ((Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)) :=
  (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.liftContext
    (logupSumcheckContextLens F n M params).stmt

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The embedded LogUp sumcheck phase, obtained by lifting ArkLib's generic Sumcheck reduction
through the LogUp-to-Sumcheck context lens with the generic `OracleReduction.liftContext`. Its
prover and verifier are defeq to `sumcheckProver`/`sumcheckVerifier`, which the full-protocol
appends consume directly. -/
noncomputable def sumcheckOracleReduction :
    OracleReduction oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params) Unit
      ((Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)) :=
  (logupConcreteSumcheckOracleReduction oSpec F n M params).liftContext
    (logupSumcheckContextLens F n M params)

end Phase2


/-! # Phase 3 — Final point check

The verifier queries the retained LogUp oracles at sumcheck's final
point and checks that they reproduce the claimed value. -/

section Phase3

/-- The final LogUp point check has no transcript messages; it only queries retained oracles. -/
@[reducible]
def finalCheckPSpec : ProtocolSpec 0 :=
  !p[]

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

/-- The final relation after the point check: accepted executions return `Unit`. -/
def outputRelation : Set ((StmtOut × (∀ i, OStmtOut i)) × Unit) :=
  Set.univ

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The prover for the final LogUp point check; there are no messages in this phase. -/
noncomputable def finalCheckProver :
    OracleProver oSpec (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params) Unit
      StmtOut OStmtOut Unit
      finalCheckPSpec where
  PrvState := fun _ => StmtAfterSumcheck F n M params ×
    (∀ i, OStmtAfterOuter F n M params i)
  input := fun ⟨ctx, _⟩ => ctx
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output := fun _ => pure ((((), fun i => Fin.elim0 i), ()))

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Query one retained LogUp oracle during the final point check. -/
def finalCheckQuery
    (i : OuterOracleIdx M)
    (q : (instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Query) :
    OptionT
      (OracleComp (oSpec + ([OStmtAfterOuter F n M params]ₒ + [finalCheckPSpec.Message]ₒ)))
      ((instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Response q) :=
  OptionT.mk <| some <$> OracleComp.lift
    (OracleSpec.query
      (show (oSpec + ([OStmtAfterOuter F n M params]ₒ +
          [finalCheckPSpec.Message]ₒ)).Domain from Sum.inr (Sum.inl ⟨i, q⟩)))

/-- The verifier's final Protocol 2 check: reconstruct `Q(r)` from retained LogUp oracle
evaluations and compare it with the expected value output by sumcheck. -/
noncomputable def finalCheckVerifier :
    OracleVerifier oSpec (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params)
      StmtOut OStmtOut
      finalCheckPSpec where
  verify := fun stmt _ => do
    let r : Fin n → F := stmt.finalClaim.challenges
    let expectedValue : F := stmt.finalClaim.target
    let multiplicity ← finalCheckQuery oSpec F n M params .multiplicity r
    let table ← finalCheckQuery oSpec F n M params (.input .table) r
    let columnValues ← (Vector.finRange M).mapM
      (fun i => finalCheckQuery oSpec F n M params (.input (.column i)) r)
    let helperValues ← (Vector.finRange params.numGroups).mapM
      (fun k => finalCheckQuery oSpec F n M params .helpers ⟨k, r⟩)
    guard (qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge r
      stmt.outer.batchingScalars multiplicity table (fun i => columnValues[i])
      (fun k => helperValues[k]) = expectedValue)
    pure ()

  embed :=
    { toFun := fun i => Fin.elim0 i
      inj' := fun i => Fin.elim0 i }

  hEq := fun i => Fin.elim0 i

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The final LogUp point check as an ArkLib oracle reduction. -/
noncomputable def finalCheckOracleReduction :
    OracleReduction oSpec (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtOut) (OStmtOut) Unit
      finalCheckPSpec where
  prover := finalCheckProver oSpec F n M params
  verifier := finalCheckVerifier oSpec F n M params

end Phase3


/-! # Full protocol

The three phase reductions composed into the full LogUp transcript, prover, verifier, and oracle
reduction. -/

section FullProtocol

open ProtocolSpec

/-- Protocol 2 before the final point check: outer LogUp followed by generic sumcheck. -/
@[reducible]
noncomputable def pSpecBeforeFinal (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :=
  outerPSpec F n params ++ₚ (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)

/-- Protocol 2 transcript shape: outer LogUp, ArkLib's generic sumcheck, and the final point check.
-/
@[reducible]
noncomputable def pSpec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :=
  pSpecBeforeFinal F n M params ++ₚ finalCheckPSpec

/-- The prover messages before the final check are oracle-accessible: outer LogUp followed by the
embedded sumcheck messages. -/
noncomputable instance instPSpecBeforeFinalMessageOracleInterface
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, OracleInterface ((pSpecBeforeFinal F n M params).Message i) := by
  unfold pSpecBeforeFinal
  exact ProtocolSpec.instOracleInterfaceMessageAppend

/-- The full LogUp prover messages are oracle-accessible: outer LogUp and sumcheck messages; the
final point check has no messages. -/
noncomputable instance instPSpecMessageOracleInterface
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, OracleInterface ((pSpec F n M params).Message i) := by
  unfold pSpec
  exact ProtocolSpec.instOracleInterfaceMessageAppend

/-- The verifier challenges before the final check are sampleable: outer LogUp followed by the
embedded sumcheck challenges. -/
noncomputable instance instPSpecBeforeFinalChallengeSampleable
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((pSpecBeforeFinal F n M params).Challenge i) := by
  unfold pSpecBeforeFinal
  exact ProtocolSpec.instSampleableTypeChallengeAppend

/-- The full LogUp verifier challenges are sampleable: the final point check has no challenges. -/
noncomputable instance instPSpecChallengeSampleable
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((pSpec F n M params).Challenge i) := by
  unfold pSpec
  exact ProtocolSpec.instSampleableTypeChallengeAppend

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp prover, composed from the outer prover and embedded sumcheck prover. -/
noncomputable def logupProver :
    OracleProver oSpec (StmtIn F n M) (OStmtIn F n M) (Unit)
      (StmtOut) (OStmtOut) Unit
      (pSpec F n M params) :=
  Prover.append
    (Prover.append (outerProver oSpec F n M params) (sumcheckProver oSpec F n M params))
    (finalCheckProver oSpec F n M params)

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp verifier, obtained by composing the outer verifier with the embedded sumcheck
verifier and final point check. -/
noncomputable def logupVerifier :
    OracleVerifier oSpec (StmtIn F n M) (OStmtIn F n M)
      (StmtOut) (OStmtOut)
      (pSpec F n M params) :=
  OracleVerifier.append
    (OracleVerifier.append (outerVerifier oSpec F n M params)
      (sumcheckVerifier oSpec F n M params))
    (finalCheckVerifier oSpec F n M params)

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp Protocol as an ArkLib oracle reduction. -/
noncomputable def logupOracleReduction :
    OracleReduction oSpec (StmtIn F n M) (OStmtIn F n M) (Unit)
      (StmtOut) (OStmtOut) Unit
      (pSpec F n M params) where
  prover := logupProver oSpec F n M params
  verifier := logupVerifier oSpec F n M params

end FullProtocol


end Logup
