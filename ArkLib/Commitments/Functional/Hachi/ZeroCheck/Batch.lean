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
  assumed — the range machinery is load-bearing.

  The reduction's content is the pull-back `mem_relLift_of_relBatched` from `relBatched` to
  `relLift`: the per-row equation is recovered from `H_α ≡ 0` via `hAlpha_eq_zero_iff`
  and `hAlphaEvals_rowPoint`, and shortness from `H₀ ≡ 0` via `hZero_eq_zero_imp_liftShort`. Its
  hypotheses are the arity bounds `n ≤ 2 ^ m₁` and `(μ + n)·deg φ ≤ 2 ^ m₀`, positivity
  `0 < deg φ`, and the range-base fits `b − 1 ≤ bound`, `b − 1 ≤ ρBound`.

  The **honest direction** `mem_relBatched_of_relLift` is proved here too, so the bridge is settled
  both ways: a lift-valid short witness satisfies the two identities. Its halves are
  `hZero_eq_zero_of_liftShort` (shortness puts every table entry among `P_b`'s roots — the converse
  of the range-side soundness) and `hAlpha_eq_zero_of_rows` (the `n` row equations are the *whole*
  Boolean table, which is zero-padded beyond row `n`). It needs neither arity hypothesis and no
  property of `α`, but it needs the range-base fits in the *other* orientation
  (`bound ≤ b − 1`, `ρBound ≤ b − 1`): at the paper's `bound = ρBound = b − 1` both hold and the two
  relations coincide. The link's perfect completeness, which uses this direction **alone** (through
  `ReduceClaim.reduction_completeness_of_imp`, so neither arity hypothesis of the pull-back is
  needed), is `batchReduction_perfectCompleteness` (`ZeroCheck/Completeness.lean`).

  Weak binding enters the certificate as an *event on the transcript tree*, rather than as a
  `⊕ E` relation summand; its hardness target is the
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
  have hy : evalAt φF X.2.2 ((cyclotomicPresentation Φ).rep (X.1.yvec i)).toPoly
      = cEvalAt φF X.2.2 (X.1.yvec i).1 := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
  have hmod : evalAt φF X.2.2 (cyclotomicPresentation Φ).modulus.toPoly
      = cEvalAt φF X.2.2 Φ.φ := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
  rw [hrow, hy, hmod]
  linear_combination hi

/-! ## The honest direction: `relLift → relBatched` -/

omit [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- **Converse of `valMinAbs_natAbs_le_of_rangeProduct_eq_zero`**: a residue with a small centered
representative is a root of the range factor. Writing `c.valMinAbs = ±j` with `j ≤ b − 1`, the
embedded value `φF c` is `±(j : F)`, one of `P_b`'s listed roots. -/
theorem rangeProduct_eq_zero_of_valMinAbs_natAbs_le (φF : ZMod q →+* F) {b : ℕ} {c : ZMod q}
    (h : (c.valMinAbs).natAbs ≤ b - 1) : rangeProduct b (φF c) = 0 := by
  rw [rangeProduct_eq_zero_iff]
  -- Name the centered absolute value, so that rewriting `c` cannot loop through `c.valMinAbs`.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (c.valMinAbs).natAbs = j := ⟨_, rfl⟩
  have hc : ((j : ℕ) : ZMod q) = if c.val ≤ q / 2 then c else -c := by
    rw [← hj]; exact ZMod.natCast_natAbs_valMinAbs c
  rw [hj] at h
  refine ⟨j, h, ?_⟩
  by_cases hval : c.val ≤ q / 2
  · rw [if_pos hval] at hc
    exact Or.inl (by rw [← hc, map_natCast])
  · rw [if_neg hval] at hc
    refine Or.inr ?_
    have hc' : c = -((j : ℕ) : ZMod q) := by rw [hc]; ring
    rw [hc', _root_.map_neg, map_natCast]

set_option linter.unusedSectionVars false in
/-- **Range side of the honest direction**: a short witness makes the range polynomial vanish
identically. Every entry of the table `w̃` is either a committed coefficient — bounded by `bound`
or `ρBound`, hence by `b − 1`, hence a root of `P_b` — or the zero padding, at which `P_b(0) = 0`.

The hypotheses are the mirror image of `hZero_eq_zero_imp_liftShort`'s: there the declared bounds
had to *dominate* the range base (`b − 1 ≤ bound`), here they must be *dominated* by it
(`bound ≤ b − 1`). At the paper's parameters both hold simultaneously, `bound = ρBound = b − 1`,
which is what makes `relLift` and `relBatched` equivalent rather than merely comparable.

Note also what is *not* needed: no arity hypothesis. `hZero_eq_zero_imp_liftShort` needs
`(μ + n)·deg φ ≤ 2 ^ m₀` to know every coefficient position is a genuine cube point; the honest
direction quantifies over cube points instead, and the table is zero-padded, so any surplus cube
points take care of themselves. -/
theorem hZero_eq_zero_of_liftShort (φF : ZMod q →+* F) (b : ℕ) (hd : 0 < Φ.φ.natDegree)
    (hbound : bound ≤ b - 1) (hρBound : ρBound ≤ b - 1)
    (w : LiftedWitness Φ μ n) (h : liftShort Φ bound ρBound w) :
    hZero Φ m₀ φF b w = 0 := by
  rw [hZero_eq_zero_iff]
  intro x
  simp only [wTable]
  split_ifs with hz hr
  · exact rangeProduct_eq_zero_of_valMinAbs_natAbs_le φF
      (le_trans (Rq.valMinAbs_natAbs_coeff_le_of_vecLInftyNorm_le Φ h.1 _
        (Nat.mod_lt _ hd)) hbound)
  · exact rangeProduct_eq_zero_of_valMinAbs_natAbs_le φF
      (le_trans (h.2 _ _) hρBound)
  · simp only [rangeProduct, zero_mul]

set_option linter.unusedSectionVars false in
/-- **Linear side of the honest direction**: the per-row `α`-evaluated lift equations make the
batched constraint polynomial vanish identically.

`H_α`'s Boolean table is zero-padded beyond row `n` (`hAlphaEvals`), so `H_α ≡ 0` needs exactly the
`n` row equations `relLift` provides and nothing more — in particular no `n ≤ 2 ^ m₁` arity
hypothesis, and no property of `α`: the identity holds at *every* evaluation point, which is why
this link's completeness error is `0`. The three `evalAt`/`cEvalAt` bridges are the same ones
`mem_relLift_of_relBatched` uses, run in the opposite direction. -/
theorem hAlpha_eq_zero_of_rows (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n)
    (hrows : ∀ i, evalAt φF α ((cyclotomicPresentation Φ).rowSum s.M w.z i)
      = evalAt φF α ((cyclotomicPresentation Φ).rep (s.yvec i)).toPoly
        + evalAt φF α (cyclotomicPresentation Φ).modulus.toPoly
          * evalAt φF α ((w.ρ i)).toPoly) :
    hAlpha Φ m₁ φF b s α w = 0 := by
  rw [hAlpha_eq_zero_iff]
  intro x
  simp only [hAlphaEvals]
  split_ifs with hlt
  · have hi := hrows ⟨_, hlt⟩
    have hrow : evalAt φF α ((cyclotomicPresentation Φ).rowSum s.M w.z ⟨_, hlt⟩)
        = cEvalAt φF α (cRowSum Φ s w.z ⟨_, hlt⟩) := by
      rw [cEvalAt_cRowSum_eq_evalAt, rowSum_eq_sum_toPoly]
      simp only [Presentation.rowSum, cyclotomicPresentation]
    have hy : evalAt φF α ((cyclotomicPresentation Φ).rep (s.yvec ⟨_, hlt⟩)).toPoly
        = cEvalAt φF α (s.yvec ⟨_, hlt⟩).1 := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
    have hmod : evalAt φF α (cyclotomicPresentation Φ).modulus.toPoly
        = cEvalAt φF α Φ.φ := (cEvalAt_eq_evalAt_toPoly _ _ _).symm
    rw [hrow, hy, hmod] at hi
    linear_combination hi
  · rfl

set_option linter.unusedSectionVars false in
/-- **The honest direction of the batching bridge** (converse of `mem_relLift_of_relBatched`): a
lift-valid, short witness satisfies the two batched polynomial identities.

Together with the pull-back this makes `relBatched` *equivalent* to `relLift` at the paper's
parameters (`bound = ρBound = b − 1`), so the bridge loses nothing in either direction: the range
identity `H₀ ≡ 0` is exactly the shortness of the committed data (`hZero_eq_zero_of_liftShort` /
`hZero_eq_zero_imp_liftShort`), and the constraint identity `H_α ≡ 0` is exactly the `n` row
equations (`hAlpha_eq_zero_of_rows` / `hAlphaEvals_rowPoint`). The `K.com` and bound conjuncts are
shared verbatim, the latter being the `sideCond` of `liftCheckAt`.

This direction needs neither arity hypothesis (`hn`, `hμn`) — see the two lemmas above. -/
theorem mem_relBatched_of_relLift (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hd : 0 < Φ.φ.natDegree)
    (hbound : bound ≤ b - 1) (hρBound : ρBound ≤ b - 1)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n)
    (h : (X, w) ∈ relLift Φ bound ρBound K φF) :
    (X, w) ∈ relBatched Φ m₀ m₁ bound ρBound K φF b := by
  obtain ⟨hcom, ⟨hrows, hside⟩, hshort⟩ := h
  exact ⟨hcom,
    hZero_eq_zero_of_liftShort Φ m₀ bound ρBound φF b hd hbound hρBound w hshort,
    hAlpha_eq_zero_of_rows Φ m₁ φF b X.1 X.2.2 w hrows,
    hside⟩

/-- **The batching bridge verifier's purity as data** (`Verifier.PureForm`): the statement map is
`id`, so the verdict is the input statement itself and `verify_eq` is `rfl`.

The package carries this instead of a `Verifier.IsPure` instance, because the composed chain must
*run* this verdict at the seam and reading it off the `IsPure` existential would cost
`Classical.choice`. -/
def batchVerifierPureForm
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) :
    (ReduceClaim.verifier oSpec
      (id : LiftStatement Φ K.TCom F n μ → LiftStatement Φ K.TCom F n μ)).PureForm where
  verify := fun stmt _ => stmt
  verify_eq := fun _ _ => rfl

/-- **The batching bridge as a (plain) `CWSSPackage`**: zero-round `ReduceClaim` at
`mapStmt := id`,
reducing `relLift` to `relBatched` with no soundness error. Its completed un-batching pull-back
is `mem_relLift_of_relBatched`. The bridge has no challenge round, so it carries no escape event
and lifts to the escape-aware package lattice through `CWSSPackage.toEscape`. -/
def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
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
  isPure := batchVerifierPureForm Φ bound ρBound K
  extractor := ReduceClaim.treeExtractor (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relLift Φ bound ρBound K φF)
    (relOut := relBatched Φ m₀ m₁ bound ρBound K φF b)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun stmtIn witOut h =>
      mem_relLift_of_relBatched Φ m₀ m₁ bound ρBound K φF b hn hd hμn hbound hρBound
        stmtIn witOut h)

end ArkLib.Lattices.Ajtai.InnerOuter
