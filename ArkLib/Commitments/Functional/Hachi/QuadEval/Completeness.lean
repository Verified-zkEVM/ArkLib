/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms
import VCVio.OracleComp.QueryTracking.ProgrammingOracle

/-!
  # Hachi polynomial-evaluation reduction (`QuadEval`) — completeness (Hachi §4.2, Figure 3)

  The honest side of the polynomial-evaluation link; `QuadEval/Soundness.lean` carries Lemma 8.
  Each theorem states its own boundary — in particular **which** output relation it reaches, since
  ArkLib's `relOut` deliberately relaxes Eq. (20)'s balanced-digit box `S_b` to the enclosing
  symmetric `ℓ∞` ball (see `relOut`), and for the honest direction that difference is not cosmetic.

  Two readings, both proved:

  * **Ball-relaxed** (`relIn → relOut`): `quadEvalReduction_perfectCompleteness`, with
    `…_zmodDigits` at the *unsigned* base-`b` digits. Reaches `relOut`, not Eq. (20): unsigned
    digits generally fall outside `S_b`.
  * **Paper-exact** (`relInBox → paperRelOut`): `quadEvalReduction_perfectCompleteness_paperRelOut`,
    with `…_balancedDigits` at the **balanced** base-`b` digits, whose range is exactly `S_b`
    (`balancedZmodDigitDecomposition` / `balancedZmodDigit_valMinAbs_mem`). This is completeness for
    the Figure 3 verifier as the paper writes it. Its input relation `relInBox` adds the box
    shortness of the input opening's own inner decomposition — a property of the committer, which
    the honest committer supplies and which `relIn` alone cannot (see `relInBox`).
    `…_relOut_of_balancedDigits` derives the relaxed conclusion from it through
    `paperRelOut_subset_relOut`, making the direction of the containment explicit: box→ball
    transports completeness *out of* the paper relation, never into it.

  Everything rests on three pieces: `honestRows_of_relIn` (Eq. (20) rows c1–c5, shared by both
  readings and valid at *every* challenge, which is why the error is `0`), the range steps
  (`gadgetDecompose_vecLInftyNorm_le_of_digit_le` for the ball,
  `gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem` for the box), and the execution half
  `quadEvalReduction_run_support`, joined by `Reduction.perfectCompleteness_of_run_support`.

  Hypotheses throughout are the two gadget round-trips (`0 < messageDigits`, `0 < zDigits`,
  `1 ≤ deg φ`) plus digit range bounds; `relIn`'s `βSq` and `κ` play no part in the honest
  direction. `SampleableType` is needed only so that execution can draw the challenge.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ} {σ : Type}

-- `[IsCyclotomic Φ]` and the `BEq`/`LawfulBEq` instances are needed only to synthesize the `Rq`
-- structures inside the relations and the gadget decompositions, which the linter's usage
-- analysis misses.
set_option linter.unusedSectionVars false in
/-- **The five linear rows of Eq. (20) at the honest values** (c1–c5), shared by the two
range-check readings of the output relation.

`relOut` and `paperRelOut` differ *only* in c6 (symmetric `ℓ∞` ball versus the paper's
balanced-digit box `S_b`), so the linear content is proved once here and both memberships are
assembled from it — `mem_relOut_of_relIn` and `mem_paperRelOut_of_relIn`. No range hypothesis
appears; the rows do not need one.

Row by row, with `w` the carrier (`wᵢ = aᵀ G sᵢ`), `ŵ = G⁻¹(w)`, `z = Σᵢ cᵢ sᵢ`, `ẑ = J⁻¹(z)`:

* c1 `D ŵ = v` — true by construction: `v` *is* `honestComputeV`.
* c2 `B (flatten t̂) = u` — `VerifiedOpening.outer_eq` of the input witness.
* c3 `bᵀ (G ŵ) = y` — the carrier round-trip `w = G ŵ` (`Hachi.carrier_eq_gadget`) plus the fact
  that Eq. (15)'s matrix `M` applied to the inner basis *is* the carrier (`hMa`, one `dot_comm`);
  `evalConsistency` then closes it.
* c4 `(cᵀ ⊗ G₁) ŵ = aᵀ G z` — bilinearity: both sides are `Σᵢ cᵢ (aᵀ G sᵢ)`.
* c5 `(cᵀ ⊗ G_{n_A}) t̂ = A z` — the per-block inner gadget relation `G t̂ᵢ = A sᵢ` pushed through
  `matVecMul_sum` / `matVecMul_scalarVecMul`.

Stated at an arbitrary `c`, which is why the completeness error is `0`. -/
theorem honestRows_of_relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ : ℕ}
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (stmt, wit) ∈ relIn Φ pp base βSq γ κ)
    (c : Fin (2 ^ r) → ShortChallenge Φ ω) :
    (let resp := honestComputeResp Φ ddCarrier ddZ (zDigits := zDigits) stmt wit c
     let cv : PolyVec (Rq Φ) (2 ^ r) := fun i => (c i).val
     let z : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
       Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ resp.zDec
     Simple.commit Φ pp.dMatrix resp.carrierDec
         = honestComputeV Φ pp ddCarrier stmt wit ∧
       Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks resp.innerDec) = stmt.u ∧
       dot stmt.bvec (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ resp.carrierDec) = stmt.y ∧
       Hachi.tensorG1 Φ base messageDigits cv resp.carrierDec =
         dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ z) ∧
       Hachi.tensorG Φ base innerRows innerDigits cv resp.innerDec = pp.innerMatrix *ᵥ z) := by
  obtain ⟨hopen, heval⟩ := h
  -- Figure 3's two gadget round-trips, `w = G ŵ` and `z = J ẑ`.
  have hcarrier : Hachi.carrier Φ base stmt.avec wit.message
      = gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ
        Hachi.carrierDecomp Φ ddCarrier stmt.avec wit.message :=
    Hachi.carrier_eq_gadget Φ hmd hdeg ddCarrier stmt.avec wit.message
  have hz : Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ
      Hachi.zDecomp Φ ddZ (honestZ Φ wit c) = honestZ Φ wit c :=
    (Hachi.z_eq_jMatrix Φ hτ hdeg ddZ (honestZ Φ wit c)).symm
  -- Eq. (15)'s matrix `M` applied to the inner basis IS the carrier: row `i` of `M` is `G sᵢ`.
  have hMa : derivedMsgMatrix Φ base wit *ᵥ stmt.avec
      = Hachi.carrier Φ base stmt.avec wit.message := by
    funext i
    simp only [matVecMul_apply, Hachi.carrier, Hachi.carrierEntry, splitForm]
    exact dot_comm _ _
  simp only [honestComputeResp]
  refine ⟨rfl, hopen.outer_eq, ?_, ?_, ?_⟩
  · -- c3: `bᵀ (G ŵ) = y` — the carrier round-trip turns Eq. (15) into the row-3 check.
    rw [← hcarrier, ← hMa]
    exact heval
  · -- c4: `(cᵀ ⊗ G₁) ŵ = aᵀ G z`, i.e. bilinearity of `splitForm` in the folded blocks.
    have hsplit : dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ honestZ Φ wit c)
        = splitForm (gadgetMatrix Φ base (2 ^ m) messageDigits) stmt.avec (honestZ Φ wit c) := rfl
    rw [hz, Hachi.tensorG1, ← hcarrier, hsplit, honestZ, splitForm_sum_right, dot_eq_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (splitForm_smul_right (gadgetMatrix Φ base (2 ^ m) messageDigits) stmt.avec _ _).symm
  · -- c5: `(cᵀ ⊗ G_{n_A}) t̂ = A z`, from the per-block inner gadget relation `G t̂ᵢ = A sᵢ`.
    rw [hz, Hachi.tensorG, honestZ, matVecMul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [matVecMul_scalarVecMul]
    exact congrArg (fun v => (c i).val •ᵥ v) (hopen.block i).inner_eq

set_option linter.unusedSectionVars false in
/-- **The relation-preservation step of `QuadEval`, at ArkLib's ball-relaxed `relOut`.** An honest
weak opening that is eval-consistent (Eq. (15)) makes the honest round-0 commitment and round-1
response satisfy `relOut` at *every* challenge vector, so no property of the challenges is used.

**Exact boundary.** The output relation is `relOut`, which models Eq. (20)'s balanced-digit box
`S_b` by the *larger* symmetric ball `‖·‖∞ ≤ γ` (see `relOut`'s docstring). Membership here is
therefore weaker than what the Figure 3 verifier checks; the paper-exact statement is
`mem_paperRelOut_of_relIn`, and the containment runs `paperRelOut ⊆ relOut`
(`paperRelOut_subset_relOut`) — the direction that helps *soundness*, not completeness.

The linear rows come from `honestRows_of_relIn`; the two decomposition range bounds come from the
digit bound hypotheses `hddCarrier` / `hddZ` via `gadgetDecompose_vecLInftyNorm_le_of_digit_le`, and
the middle one (`flatten t̂`) is the input opening's own `outer_short`. -/
theorem mem_relOut_of_relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ : ℕ}
    (hddCarrier : ∀ (x : ZMod q) (e : Fin messageDigits),
      (ddCarrier.digit x e).valMinAbs.natAbs ≤ γ)
    (hddZ : ∀ (x : ZMod q) (e : Fin zDigits), (ddZ.digit x e).valMinAbs.natAbs ≤ γ)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (stmt, wit) ∈ relIn Φ pp base βSq γ κ)
    (c : Fin (2 ^ r) → ShortChallenge Φ ω) :
    ((stmt, honestComputeV Φ pp ddCarrier stmt wit, c),
        honestComputeResp Φ ddCarrier ddZ stmt wit c)
      ∈ relOut (zDigits := zDigits) Φ pp base ω γ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    honestRows_of_relIn Φ pp ddCarrier ddZ hmd hτ hdeg stmt wit h c
  refine ⟨h1, h2, h3, h4, h5, ?_, h.1.outer_short, ?_⟩
  · -- c6, `ŵ`: an honest digit decomposition is `ℓ∞`-bounded by its digit bound.
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ ddCarrier hddCarrier _
  · -- c6, `ẑ`: likewise for the `J`-decomposition of the masked opening.
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ ddZ hddZ _

/-! ## The paper-exact reading: Eq. (20)'s balanced-digit box `S_b`

`relOut` relaxes Eq. (20)'s box `S_b` to the enclosing symmetric `ℓ∞` ball, and the containment
`paperRelOut ⊆ relOut` is what makes the *soundness* theorem cover the paper's verifier. For
completeness the containment points the wrong way: landing in `relOut` says nothing about landing in
`paperRelOut`. The results below close that gap.
-/

/-- **`relIn` with the input opening's inner decomposition pinned to the box `S_b`** — the input
relation of the paper-exact honest direction.

The honest response passes the input witness's own `t̂` straight through
(`honestComputeResp.innerDec = wit.innerDecomp`), so Eq. (20)'s middle range check is a property of
the *input* opening, and `relIn` only bounds it by the ball `‖·‖∞ ≤ γ`. Demanding the box of every
`relIn` member is false (a ball-short opening with a coefficient above `⌈b/2⌉−1` is a legal member),
so — exactly as with the lift's image seam `relRlinImage` — the condition belongs in the
relation, where the
layer that *chose* the committer's decomposition establishes it: for an honest committer
instantiated with `balancedZmodDigitDecomposition` (`Decomposition.ofDigits`), box shortness of
`flatten t̂` is `gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem` applied to
`balancedZmodDigit_valMinAbs_mem` — the same two lemmas that discharge the response-side box checks
here. Wiring that in belongs to the commitment layer (`Commitment.lean`), not to this link. -/
def relInBox
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ b : ℕ) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | p ∈ relIn Φ pp base βSq γ κ ∧
      vecInSb Φ b (PolyVec.flattenBlocks p.2.innerDecomp) }

set_option linter.unusedSectionVars false in
/-- **The relation-preservation step at the paper's exact Eq. (20)** (`paperRelOut`): with
balanced digits, the honest response's three range checks are the paper's box `S_b`, not merely the
enclosing ball.

The linear rows are `honestRows_of_relIn`; each box check is `S_b`-membership of a gadget
decomposition's coefficients, which is one application of
`gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem` per decomposition — and for the middle one the
input opening's own box shortness, carried by `relInBox`. The digit hypotheses are the two-sided box
bounds (`balancedZmodDigit_valMinAbs_mem` supplies them for the balanced decomposition), *not* the
one-sided `ℓ∞` bounds of `mem_relOut_of_relIn`. -/
theorem mem_paperRelOut_of_relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ b : ℕ}
    (hddCarrier : ∀ (x : ZMod q) (e : Fin messageDigits),
      -((b / 2 : ℕ) : ℤ) ≤ (ddCarrier.digit x e).valMinAbs ∧
        (ddCarrier.digit x e).valMinAbs ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1)
    (hddZ : ∀ (x : ZMod q) (e : Fin zDigits),
      -((b / 2 : ℕ) : ℤ) ≤ (ddZ.digit x e).valMinAbs ∧
        (ddZ.digit x e).valMinAbs ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (h : (stmt, wit) ∈ relInBox Φ pp base βSq γ κ b)
    (c : Fin (2 ^ r) → ShortChallenge Φ ω) :
    ((stmt, honestComputeV Φ pp ddCarrier stmt wit, c),
        honestComputeResp Φ ddCarrier ddZ stmt wit c)
      ∈ paperRelOut (zDigits := zDigits) Φ pp base ω b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    honestRows_of_relIn Φ pp ddCarrier ddZ hmd hτ hdeg stmt wit h.1 c
  refine ⟨h1, h2, h3, h4, h5, ?_, h.2, ?_⟩
  · exact fun j k hk =>
      gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem Φ ddCarrier hddCarrier _ j hk
  · exact fun j k hk => gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem Φ ddZ hddZ _ j hk

/-- Abbreviation for this reduction's two-round `ProtocolSpec`, kept local so the round-unfolding
lemmas below stay readable. -/
private abbrev qePSpec (Φ : CyclotomicModulus (ZMod q)) (dRows ω r : ℕ) : ProtocolSpec 2 :=
  pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r

set_option linter.unusedSectionVars false in
-- v4.33 respects transparency when matching implicit arguments: `rw` no longer unifies
-- `Prover.processRound 0` against a target whose transcript is already reduced to `Fin 0`, and
-- the closing `rfl` no longer sees `Transcript.concat`/`Fin.snoc` and `FullTranscript.mk2`'s
-- match form as definitionally equal.
set_option backward.isDefEq.respectTransparency false in
/-- **Honest execution of both rounds.** Running the Figure-3 prover to the last round draws the
challenge vector `c` and ends with the transcript `⟨v, c⟩` (`FullTranscript.mk2`) and the state
`((X, w), c)`: round 0 appends the carrier commitment `v = computeV X w` and leaves the state
untouched, round 1 appends `c` and stores it.

Proved by the two framework round-unfoldings rather than by induction — the protocol has only two
rounds. The `hdir` hypothesis is `pSpec.dir 1 = .V_to_P`, passed as a named argument rather than
`rfl` so that the round-1 challenge index stays type-correct under the reduced transparency `rw`
uses. -/
lemma prover_runToRound_last {WitIn : Type}
    (computeV :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → CarrierCom Φ dRows)
    (computeResp :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → (Fin (2 ^ r) → ShortChallenge Φ ω) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (wit : WitIn) (hdir : (qePSpec Φ dRows ω r).dir 1 = .V_to_P) :
    (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
        (Fin.last 2) stmt wit
      = (do
          let ch ← (qePSpec Φ dRows ω r).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (computeV stmt wit) ch, ((stmt, wit), ch))) := by
  -- `Fin.last 2 = Fin.succ 1` and `Fin.succ 0 = Fin.castSucc 1` only after `Fin.val` arithmetic,
  -- so the two round unfoldings are ascribed at the indices that actually occur.
  have step2 : (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
        (Fin.last 2) stmt wit
      = (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).processRound (1 : Fin 2)
          ((InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
            ((1 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (1 : Fin 2) stmt wit _
  have step1 : (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
        ((1 : Fin 2).castSucc) stmt wit
      = (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).processRound (0 : Fin 2)
          ((InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
            ((0 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (0 : Fin 2) stmt wit _
  have step0 : (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).runToRound
        ((0 : Fin 2).castSucc) stmt wit
      = pure ((fun i => Fin.elim0 i), (stmt, wit)) := rfl
  refine step2.trans ?_
  rw [step1, step0, Prover.processRound_of_dir_eq_P_to_V (0 : Fin 2) rfl,
    Prover.processRound_of_dir_eq_V_to_P (1 : Fin 2) hdir]
  simp only [InnerOuter.prover, liftM, monadLift, MonadLift.monadLift,
    OracleComp.liftComp_pure, monad_norm, FullTranscript.mk2_eq_snoc_snoc]
  rfl

set_option linter.unusedSectionVars false in
/-- **The honest prover's run in closed form.** `prover_runToRound_last` followed by `output`: the
prover's whole execution is "draw `c`, then emit the transcript `⟨v, c⟩`, the output statement
`(X, v, c)`, and the response `computeResp X w c`". Everything about the run is a function of the
one challenge vector. -/
lemma prover_run_eq {WitIn : Type}
    (computeV :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → CarrierCom Φ dRows)
    (computeResp :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → (Fin (2 ^ r) → ShortChallenge Φ ω) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (wit : WitIn) (hdir : (qePSpec Φ dRows ω r).dir 1 = .V_to_P) :
    (InnerOuter.prover (oSpec := oSpec) Φ WitIn computeV computeResp).run stmt wit
      = (do
          let ch ← (qePSpec Φ dRows ω r).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (computeV stmt wit) ch,
            (stmt, computeV stmt wit, ch), computeResp stmt wit ch)) := by
  unfold Prover.run
  rw [prover_runToRound_last Φ computeV computeResp stmt wit hdir]
  simp only [InnerOuter.prover, liftM, monadLift, MonadLift.monadLift]
  rfl

set_option linter.unusedSectionVars false in
/-- **Honest-run characterization.** Every element of the support of an honest execution of
`quadEvalReduction` is a success, and it is determined by the drawn challenge vector alone: prover
and verifier both output `(X, v, c)` with `v` the honest carrier commitment, and the prover hands
on the honest response.

This is the whole execution content of completeness. Failure is impossible because the only
`OptionT` layer in `Reduction.run` comes from the verifier, and `verifier` is a `pure`
pass-through with no acceptance test to fail — the Eq.-(20) checks live in `relOut`, which
`mem_relOut_of_relIn` discharges. -/
lemma quadEvalReduction_run_support
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hdir : (qePSpec Φ dRows ω r).dir 1 = .V_to_P)
    (X : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    ∀ x ∈ support ((quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp
        ddCarrier ddZ).run X w).run,
      ∃ ch : Fin (2 ^ r) → ShortChallenge Φ ω,
        x = some ((FullTranscript.mk2 (honestComputeV Φ pp ddCarrier X w) ch,
              (X, honestComputeV Φ pp ddCarrier X w, ch),
              honestComputeResp Φ ddCarrier ddZ X w ch),
            (X, honestComputeV Φ pp ddCarrier X w, ch)) := by
  intro x hx
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨prOpt, hpr, hx⟩ := hx
  rw [show ((liftM (Prover.run X w
        (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp ddCarrier ddZ).prover) :
        OptionT (OracleComp _) _)).run
      = (Prover.run X w
          (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp ddCarrier ddZ).prover)
        >>= fun a => pure (some a) from rfl] at hpr
  rw [mem_support_bind_iff] at hpr
  obtain ⟨pr, hpr, hprOpt⟩ := hpr
  rw [mem_support_pure_iff] at hprOpt
  subst hprOpt
  rw [show (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp ddCarrier ddZ).prover
      = InnerOuter.prover Φ
          (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
          (honestComputeV Φ pp ddCarrier) (honestComputeResp Φ ddCarrier ddZ) from rfl,
    prover_run_eq Φ _ _ X w hdir, mem_support_bind_iff] at hpr
  obtain ⟨ch, -, hpr⟩ := hpr
  rw [mem_support_pure_iff] at hpr
  subst hpr
  refine ⟨ch, ?_⟩
  simp only [Option.elim_some, quadEvalReduction, InnerOuter.verifier, Verifier.run] at hx
  simp only [ChallengeIdx, Challenge, OptionT.run_pure, liftM_pure,
    ProgrammingPolicy.empty_apply, pure_bind, Option.elim_some, Option.getM_some, support_pure,
    Set.mem_singleton_iff] at hx
  exact hx

set_option linter.unusedSectionVars false in
/-- **Perfect completeness of the polynomial-evaluation reduction (Hachi §4.2, Figure 3) at
ArkLib's ball-relaxed output relation.** An honest prover holding an eval-consistent weak opening of
`u` is accepted with probability one and the response it hands on lies in `relOut`, with the
prover's and the verifier's output statements equal.

**Exact boundary.** `relOut` is Eq. (20) rows c1–c5 verbatim, but with the balanced-digit box `S_b`
of the c6 range checks replaced by the enclosing symmetric ball `‖·‖∞ ≤ γ` (see `relOut`). So this
is *not* completeness for the Figure 3 verifier as the paper writes it: `paperRelOut ⊆ relOut`
(`paperRelOut_subset_relOut`) is the containment that transports **soundness** to the paper's
verifier, and it is useless in this direction. The paper-exact statement is
`quadEvalReduction_perfectCompleteness_paperRelOut`, concretely
`…_balancedDigits`.

The completeness error is `0` rather than something in `1 / |C|`: the honest masked opening
`z = Σᵢ cᵢ sᵢ` satisfies Eq. (20)'s folded rows c4/c5 identically in the challenge vector, so
`mem_relOut_of_relIn` holds at every `c` and the proof quantifies over the whole support of the
run. The `SampleableType` instance is required only so that execution can draw the challenge, not
for any property of its distribution.

The hypotheses are exactly the two gadget round-trips (`0 < messageDigits`, `0 < zDigits`,
`1 ≤ deg φ`) and the two digit bounds that put the honest decompositions inside `relOut`'s range
`γ`; `relIn`'s `βSq` and `κ` are unconstrained. For the concrete unsigned base-`b` decomposition
see `quadEvalReduction_perfectCompleteness_zmodDigits`. -/
theorem quadEvalReduction_perfectCompleteness
    [∀ i, SampleableType ((qePSpec Φ dRows ω r).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ : ℕ}
    (hddCarrier : ∀ (x : ZMod q) (e : Fin messageDigits),
      (ddCarrier.digit x e).valMinAbs.natAbs ≤ γ)
    (hddZ : ∀ (x : ZMod q) (e : Fin zDigits), (ddZ.digit x e).valMinAbs.natAbs ≤ γ) :
    (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω)
        Φ pp ddCarrier ddZ).perfectCompleteness init impl
      (relIn Φ pp base βSq γ κ) (relOut (zDigits := zDigits) Φ pp base ω γ) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro X w hIn x hx
  obtain ⟨ch, rfl⟩ := quadEvalReduction_run_support Φ pp ddCarrier ddZ rfl X w x hx
  exact ⟨_, rfl,
    mem_relOut_of_relIn Φ pp ddCarrier ddZ hmd hτ hdeg hddCarrier hddZ X w hIn ch, rfl⟩

set_option linter.unusedSectionVars false in
/-- **Ball-relaxed completeness at the concrete *unsigned* base-`b` digit decomposition.**
`quadEvalReduction_perfectCompleteness` instantiated with `zmodDigitDecomposition` at both gadget
steps, whose digits are the unsigned digits `0, …, b − 1`, centered-bounded by `b - 1 ≤ b`
(`zmodDigit_natAbs_le`).

**Exact boundary.** The output relation is `relOut` at `γ := b`, i.e. the symmetric ball of radius
`b` — *not* Eq. (20)'s box `S_b`, which unsigned digits generally violate (a digit `b − 1` exceeds
the box's upper end `⌈b/2⌉ − 1` as soon as `b ≥ 3`). `γ = b` does match the `γ` of
`quadEval_coordinateWiseSpecialSoundWithEscape_paperParams`, so at these parameters both security
directions are available for the *same* `relIn`/`relOut` pair — but the paper-exact honest statement
is `quadEvalReduction_perfectCompleteness_balancedDigits`, which needs the *balanced* digits
instead. `relIn`'s `βSq` and `κ` stay free here, so the soundness side's `quadEvalBetaSq …` value
can be plugged in. -/
theorem quadEvalReduction_perfectCompleteness_zmodDigits
    [∀ i, SampleableType ((qePSpec Φ dRows ω r).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {b : ℕ} (hb : 1 < b) (hqm : q ≤ b ^ messageDigits) (hqz : q ≤ b ^ zDigits)
    (hbq : b - 1 ≤ q / 2)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree) {βSq κ : ℕ} :
    (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω) Φ pp
        (zmodDigitDecomposition b messageDigits hb hqm)
        (zmodDigitDecomposition b zDigits hb hqz)).perfectCompleteness init impl
      (relIn Φ pp (b : ZMod q) βSq b κ) (relOut (zDigits := zDigits) Φ pp (b : ZMod q) ω b) :=
  quadEvalReduction_perfectCompleteness Φ init impl pp _ _ hmd hτ hdeg
    (fun x e => le_trans (zmodDigit_natAbs_le hb hqm hbq x e) (Nat.sub_le b 1))
    (fun x e => le_trans (zmodDigit_natAbs_le hb hqz hbq x e) (Nat.sub_le b 1))

set_option linter.unusedSectionVars false in
/-- **Paper-exact perfect completeness of Figure 3** (Hachi Eq. (20) verbatim, box `S_b` and all):
the honest prover of Figure 3 is accepted with probability one and its response lies in
`paperRelOut`, the relation the paper's verifier actually checks.

Everything is as in the ball-relaxed theorem except the range readings: the digit hypotheses are
the two-sided box bounds and the input relation is `relInBox` (see `relInBox` for why the input
opening's box shortness has to be part of the relation). For the concrete instance at the balanced
base-`b` digits — where the hypotheses are discharged — see
`quadEvalReduction_perfectCompleteness_balancedDigits`. -/
theorem quadEvalReduction_perfectCompleteness_paperRelOut
    [∀ i, SampleableType ((qePSpec Φ dRows ω r).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : DigitDecomposition base zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ b : ℕ}
    (hddCarrier : ∀ (x : ZMod q) (e : Fin messageDigits),
      -((b / 2 : ℕ) : ℤ) ≤ (ddCarrier.digit x e).valMinAbs ∧
        (ddCarrier.digit x e).valMinAbs ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1)
    (hddZ : ∀ (x : ZMod q) (e : Fin zDigits),
      -((b / 2 : ℕ) : ℤ) ≤ (ddZ.digit x e).valMinAbs ∧
        (ddZ.digit x e).valMinAbs ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1) :
    (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω)
        Φ pp ddCarrier ddZ).perfectCompleteness init impl
      (relInBox Φ pp base βSq γ κ b) (paperRelOut (zDigits := zDigits) Φ pp base ω b) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro X w hIn x hx
  obtain ⟨ch, rfl⟩ := quadEvalReduction_run_support Φ pp ddCarrier ddZ rfl X w x hx
  exact ⟨_, rfl,
    mem_paperRelOut_of_relIn Φ pp ddCarrier ddZ hmd hτ hdeg hddCarrier hddZ X w hIn ch, rfl⟩

set_option linter.unusedSectionVars false in
/-- **Paper-exact perfect completeness at the balanced base-`b` digit decomposition** — Figure 3's
honest prover, accepted by the paper's own Eq. (20) verifier.

`balancedZmodDigitDecomposition`'s digits lie in `[⌈−b/2⌉, ⌈b/2⌉−1]`, which *is* the box `S_b`
(`balancedZmodDigit_valMinAbs_mem`), so the two digit hypotheses of
`quadEvalReduction_perfectCompleteness_paperRelOut` are discharged and nothing about the range is
left assumed. The anti-wraparound condition is `b ≤ q/2` (marginally stronger than the unsigned
`b − 1 ≤ q/2`, and needed because the balanced digits are genuinely two-sided). -/
theorem quadEvalReduction_perfectCompleteness_balancedDigits
    [∀ i, SampleableType ((qePSpec Φ dRows ω r).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {b : ℕ} (hb : 1 < b) (hqm : q ≤ b ^ messageDigits) (hqz : q ≤ b ^ zDigits)
    (hbq : b ≤ q / 2)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree) {βSq γ κ : ℕ} :
    (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω) Φ pp
        (balancedZmodDigitDecomposition b messageDigits hb hqm)
        (balancedZmodDigitDecomposition b zDigits hb hqz)).perfectCompleteness init impl
      (relInBox Φ pp (b : ZMod q) βSq γ κ b)
      (paperRelOut (zDigits := zDigits) Φ pp (b : ZMod q) ω b) :=
  quadEvalReduction_perfectCompleteness_paperRelOut Φ init impl pp _ _ hmd hτ hdeg
    (fun x e => balancedZmodDigit_valMinAbs_mem hb hqm hbq x e)
    (fun x e => balancedZmodDigit_valMinAbs_mem hb hqz hbq x e)

set_option linter.unusedSectionVars false in
/-- **Ball-relaxed completeness derived from the paper-exact one**, through the containment
`paperRelOut ⊆ relOut` (`paperRelOut_subset_relOut`) and `Reduction.completeness_relOut_mono`.

This is the honest direction's use of the box→ball containment, and it makes the direction explicit:
paper-exact completeness *implies* the relaxed statement, never the other way round. Note the input
relation stays `relInBox`, which is stronger than `relIn` — so this is not the same theorem as
`quadEvalReduction_perfectCompleteness`, which reaches `relOut` from all of `relIn` but under the
one-sided digit hypotheses. -/
theorem quadEvalReduction_perfectCompleteness_relOut_of_balancedDigits
    [∀ i, SampleableType ((qePSpec Φ dRows ω r).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {b : ℕ} (hb : 1 < b) (hqm : q ≤ b ^ messageDigits) (hqz : q ≤ b ^ zDigits)
    (hbq : b ≤ q / 2)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hdeg : 1 ≤ Φ.φ.natDegree)
    {βSq γ κ γ' : ℕ} (hγ : b / 2 ≤ γ') :
    (quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω) Φ pp
        (balancedZmodDigitDecomposition b messageDigits hb hqm)
        (balancedZmodDigitDecomposition b zDigits hb hqz)).perfectCompleteness init impl
      (relInBox Φ pp (b : ZMod q) βSq γ κ b)
      (relOut (zDigits := zDigits) Φ pp (b : ZMod q) ω γ') :=
  Reduction.completeness_relOut_mono init impl (paperRelOut_subset_relOut Φ pp (b : ZMod q) ω hγ)
    (quadEvalReduction_perfectCompleteness_balancedDigits Φ init impl pp hb hqm hqz hbq
      hmd hτ hdeg)

end ArkLib.Lattices.Ajtai.InnerOuter
