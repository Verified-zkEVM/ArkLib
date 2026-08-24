/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # Batching bridge — Hachi Eqs. (22)–(23)

  A zero-round reduction between two readings of the lift's claims:

  * `relLift` — `w̃` opens `t`, the per-row `α`-evaluated constraints hold, `w̃` is short
    (`RingSwitch/Reduction.lean`, the committed-scalar shell at `liftCheckAt`);
  * `relBatched` — `w̃` opens `t`, the batched polynomials `H₀^{w̃}` and `H_α^{w̃}` are identically
    zero (Eqs. (22)–(23), `ZeroCheck/Constraints.lean`).

  The statement and witness are unchanged (`ReduceClaim` at `mapStmt := id`); only the reading of
  the claims changes, which separates the batching algebra from the transcript-tree zero test.
  Shortness is **not** a conjunct of `relBatched`: the range identity `H₀^{w̃} ≡ 0`
  already forces every committed coefficient into `[−(b−1), b−1]`, so `liftShort` is *derived*, not
  assumed — the range machinery is load-bearing (review PR #656, resolution option 1).

  The reduction's content is the pull-back `mem_relLift_of_relBatched` from `relBatched` to
  `relLift`: the per-row equation is recovered from `H_α ≡ 0` via `hAlpha_eq_zero_iff`
  and `hAlphaEvals_rowPoint`, and shortness from `H₀ ≡ 0` via `hZero_eq_zero_imp_liftShort`. Its
  hypotheses are the arity bounds `n ≤ 2 ^ m₁` and `(μ + n)·deg φ ≤ 2 ^ m₀`, positivity
  `0 < deg φ`, and the range-base fits `b − 1 ≤ bound`, `b − 1 ≤ ρBound`.

  Escapes are no longer threaded through the relations as a `⊕ E` summand: weak binding enters
  the certificate as an *event on the transcript tree* whose hardness target is the
  short-collision set `LiftCom.Collision`. This bridge has no challenge round, so it carries no
  escape at all and composes with escape-aware neighbours through `CWSSPackage.toEscape`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The batched relation (Hachi Eqs. (22)–(23) as polynomial identities): `w̃` opens `t`, the
range polynomial `H₀^{w̃}` and the linear-constraint polynomial `H_α^{w̃}` are both identically
zero, and `bound ≤ rlin.bound`. This is the zero-check's input relation.

Shortness is **not** a conjunct here: `H₀ ≡ 0` already forces `w̃` short (every committed
coefficient is a root of the range factor `P_b`), so `liftShort` is *derived* — not assumed — by
the pull-back `mem_relLift_of_relBatched` (via `hZero_eq_zero_imp_liftShort`). This is the
range machinery being load-bearing rather than inert.

Both conjuncts are the paper's polynomials, not stand-ins. `hAlpha`'s Boolean table is *written*
as the per-row `α`-defect in the ring representation, but `hAlpha_eq_zero_iff_alphaDefect` proves
`hAlpha … = 0` equivalent to the vanishing of every row's Eq. (22) contraction
`∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − yᵢ(α)` of the public `M̃_α`/`α̃` against the committed table
(arity pins `hd`, `(μ + n)·deg φ ≤ 2^{m₀}`). So this relation may be read as Eqs. (22)–(23)
themselves rather than as an abstract direct-defect variant of them. -/
def relBatched (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    hZero Φ m₀ φF b p.2 = 0 ∧
    hAlpha Φ m₁ φF b p.1.1 p.1.2.2 p.2 = 0 ∧
    bound ≤ p.1.1.bound}

-- `[IsCyclotomic Φ]` is needed to synthesize the `Rq`/`wTable` instances inside the `hZero` term
-- carried by `relBatched` and by `hZero_eq_zero_imp_liftShort`, but the linter's usage analysis
-- misses instance-synth-only section vars.
set_option linter.unusedSectionVars false in
/-- The batched identities imply the lift's per-row **and shortness** claims.

The per-row equation is recovered from `H_α ≡ 0`: by `hAlpha_eq_zero_iff` every
Boolean-point coefficient `hAlphaEvals` vanishes, and by `hAlphaEvals_rowPoint` the coefficient at
`rowPoint i` is row `i`'s `α`-evaluated lift defect, giving the row equation of `relLift`.
Shortness (`liftShort`, `relLift`'s norm conjunct) is **derived** from the range identity
`H₀ ≡ 0` via `hZero_eq_zero_imp_liftShort`: every committed coefficient is a root of the range
factor `P_b`, hence a centered residue of absolute value `≤ b − 1`, which meets the norm bounds
under `hbound : b − 1 ≤ bound` and `hρBound : b − 1 ≤ ρBound`. The `K.com` and bound conjuncts are
shared between the two relations. The hypotheses are the row-encoding bound `hn : n ≤ 2 ^ m₁`, the
column-encoding bound `hμn : (μ + n)·deg φ ≤ 2 ^ m₀`, and `hd : 0 < deg φ`. No anti-wraparound
condition on `q` is needed — see `valMinAbs_natAbs_le_of_rangeProduct_eq_zero`. -/
theorem mem_relLift_of_relBatched (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hρBound : b - 1 ≤ ρBound)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n)
    (h : (X, w) ∈ relBatched Φ m₀ m₁ bound ρBound K φF b) :
    (X, w) ∈ relLift Φ bound ρBound K φF := by
  simp only [relBatched, Set.mem_setOf_eq] at h
  obtain ⟨hcom, hZeroZ, hAlphaZ, hbound'⟩ := h
  have hshort : liftShort Φ bound ρBound w :=
    hZero_eq_zero_imp_liftShort Φ m₀ φF b bound ρBound hd hμn hbound hρBound w hZeroZ
  refine ⟨hcom, ⟨fun i => ?_, hbound'⟩, hshort⟩
  rw [hAlpha_eq_zero_iff] at hAlphaZ
  have hi := hAlphaZ (rowPoint m₁ hn i)
  rw [hAlphaEvals_rowPoint] at hi
  -- Bridge the computable row encoding to the presentation's `evalAt`/`rowSum`.
  have hrow : evalAt φF X.2.2 ((cyclotomicPresentation Φ).rowSum X.1.M w.z i)
      = cEvalAt φF X.2.2 (cRowSum Φ X.1 w.z i) := by
    rw [cEvalAt_cRowSum_eq_evalAt, rowSum_eq_sum_toPoly]
    simp only [Presentation.rowSum, cyclotomicPresentation]
  have hy : evalAt φF X.2.2 ((cyclotomicPresentation Φ).rep (X.1.yvec i))
      = cEvalAt φF X.2.2 (X.1.yvec i).1 := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
  have hmod : evalAt φF X.2.2 (cyclotomicPresentation Φ).modulus
      = cEvalAt φF X.2.2 Φ.φ := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
  rw [hrow, hy, hmod]
  linear_combination hi

/-- The batching bridge packaged as a `CWSSPackage`: a zero-round `ReduceClaim` at `mapStmt := id`
reducing `relLift` to `relBatched` with no soundness error, its correctness supplied by
`mem_relLift_of_relBatched`.

The bridge has no challenge round, so it carries no escape event; it lands in the plain corner of
the package lattice and lifts to the escape-aware one through `CWSSPackage.toEscape`. -/
noncomputable def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hρBound : b - 1 ≤ ρBound) :
    CWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec id
  struct := CWSSStructure.ofIsEmpty
  relIn := relLift Φ bound ρBound K φF
  relOut := relBatched Φ m₀ m₁ bound ρBound K φF b
  isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
  extractor := ReduceClaim.treeExtractor (mapStmt := id)
    (relBatched Φ m₀ m₁ bound ρBound K φF b) (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relLift Φ bound ρBound K φF)
    (relOut := relBatched Φ m₀ m₁ bound ρBound K φF b)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun stmtIn witOut h =>
      mem_relLift_of_relBatched Φ m₀ m₁ bound ρBound K φF b hn hd hμn hbound hρBound
        stmtIn witOut h)

end ArkLib.Lattices.Ajtai.InnerOuter
