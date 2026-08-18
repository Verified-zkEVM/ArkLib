/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms

/-!
  # Hachi polynomial-evaluation reduction (`QuadEval`) — completeness (Hachi §4.2, Figure 3)

  The honest side of the polynomial-evaluation link. Where `QuadEval/Soundness.lean` certifies
  (Hachi Lemma 8) that any prover the verifier accepts on `2ʳ+1` suitably-related transcripts
  yields either a weak opening or a Module-SIS break, this file proves the converse: the honest
  prover of Figure 3 is always accepted.

  ## What is proved here

  `quadEvalReduction_perfectCompleteness`: the honest run of `quadEvalReduction`
  (`QuadEval/Reduction.lean`) succeeds with probability one, the prover's and the verifier's output
  statements agree, and the resulting statement/response pair lies in `relOut` (Eq. (20)). That is
  `Reduction.perfectCompleteness` in full, for arbitrary shared oracles `oSpec`, state
  initialization `init` and query implementation `impl`.
  `quadEvalReduction_perfectCompleteness_zmodDigits` instantiates it at the concrete base-`b`
  digit decomposition and the paper's range `γ := b`, which is the `γ` of
  `quadEval_coordinateWiseSpecialSoundWithEscape_paperParams` — so both security directions are
  available at the same relations.

  It rests on two independent halves, joined by `Reduction.perfectCompleteness_of_run_support`
  (`OracleReduction/Security/Basic.lean`, the criterion introduced for the zero-check pilot).

  * *Algebra.* `mem_relOut_of_relIn`, the relation-preservation step: an honest weak opening that is
    eval-consistent (Eq. (15)) makes all eight rows of `relOut` hold, at *every* challenge vector.
    This is where the mathematics lives; see the row-by-row account below.
  * *Execution.* `quadEvalReduction_run_support`: an honest run cannot fail, and every outcome is
    determined by the single challenge vector it draws — the transcript is
    `FullTranscript.mk2 v c` with `v` the honest carrier commitment, and prover and verifier both
    output `(X, v, c)`. They agree because the verifier is the pure pass-through that re-reads
    exactly the two transcript slots the prover wrote. Proved by unfolding the two rounds
    (`prover_runToRound_last`, `prover_run_eq`).

  ## The eight rows of `relOut`, and where each comes from

  Writing `w` for the carrier (`wᵢ = aᵀ G sᵢ`), `ŵ = G⁻¹(w)`, `z = Σᵢ cᵢ sᵢ` and `ẑ = J⁻¹(z)`:

  * c1 `D ŵ = v` — true by construction: `v` *is* `honestComputeV`, i.e. `Simple.commit D ŵ`.
  * c2 `B (flatten t̂) = u` — `VerifiedOpening.outer_eq` of the input witness.
  * c3 `bᵀ (G ŵ) = y` — the carrier round-trip `w = G ŵ` (`Hachi.carrier_eq_gadget`) plus the
    observation that Eq. (15)'s matrix `M` applied to the inner basis is exactly the carrier
    (`hMa`, one `dot_comm`); then `evalConsistency` closes it.
  * c4 `(cᵀ ⊗ G₁) ŵ = aᵀ G z` — bilinearity: both sides are `Σᵢ cᵢ (aᵀ G sᵢ)`, via
    `splitForm_sum_right` / `splitForm_smul_right`.
  * c5 `(cᵀ ⊗ G_{n_A}) t̂ = A z` — the per-block inner gadget relation `G t̂ᵢ = A sᵢ`
    (`VerifiedBlock.inner_eq`) pushed through `matVecMul_sum` / `matVecMul_scalarVecMul`.
  * c6 the three range checks — `‖flatten t̂‖∞ ≤ γ` is `VerifiedOpening.outer_short`; the two
    decomposition bounds `‖ŵ‖∞ ≤ γ` and `‖ẑ‖∞ ≤ γ` come from the digit bound hypotheses
    `hddCarrier` / `hddZ` via `gadgetDecompose_vecLInftyNorm_le_of_digit_le`
    (`Gadget/Norms.lean`).

  ## Why the completeness error is zero, and what the hypotheses buy

  No property of the challenge distribution is used: `mem_relOut_of_relIn` is stated for an
  *arbitrary* challenge vector `c`, because the honest `z = Σᵢ cᵢ sᵢ` satisfies rows c4/c5
  identically in `c`. The `SampleableType` instance is needed only so that execution can draw the
  challenge at all. The arithmetic hypotheses are exactly the two gadget round-trips
  (`0 < messageDigits`, `0 < zDigits`, `1 ≤ deg φ`) and the two digit bounds; nothing else.

  Note that `relOut`'s `γ` and `relIn`'s `γ` are the same parameter: the input relation's
  `‖flatten t̂‖∞ ≤ γ` is transported verbatim into c6, and the honest decompositions must fit in
  the same ball — which is what `hddCarrier`/`hddZ` assert. `relIn`'s `βSq` and `κ` play no part in
  the honest direction and stay free.

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
/-- **The relation-preservation step of `QuadEval`.** An honest weak opening that is eval-consistent
(Eq. (15)) makes the honest round-0 commitment and round-1 response satisfy Eq. (20) at *every*
challenge vector, so no property of the challenges is used.

This is the relation obligation of completeness, not completeness itself: it says nothing about
executing `quadEvalReduction`, about probability, or about the prover and verifier agreeing on the
output statement. Those are supplied by `quadEvalReduction_run_support`, and the two are combined
in `quadEvalReduction_perfectCompleteness`. See the module docstring for the row-by-row account of
the eight `relOut` conjuncts.

Stated for an arbitrary `c` rather than for the transcript's challenge, so that the
execution-level proof can instantiate it at whatever the challenge oracle returns. -/
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
  simp only [relOut, Set.mem_setOf_eq, honestComputeResp]
  refine ⟨rfl, hopen.outer_eq, ?_, ?_, ?_, ?_, hopen.outer_short, ?_⟩
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
  · -- c6, `ŵ`: an honest digit decomposition is `ℓ∞`-bounded by its digit bound.
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ ddCarrier hddCarrier _
  · -- c6, `ẑ`: likewise for the `J`-decomposition of the masked opening.
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ ddZ hddZ _

/-- Abbreviation for this reduction's two-round `ProtocolSpec`, kept local so the round-unfolding
lemmas below stay readable. -/
private abbrev qePSpec (Φ : CyclotomicModulus (ZMod q)) (dRows ω r : ℕ) : ProtocolSpec 2 :=
  pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r

set_option linter.unusedSectionVars false in
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
/-- **Perfect completeness of the polynomial-evaluation reduction (Hachi §4.2, Figure 3).** An
honest prover holding an eval-consistent weak opening of `u` is accepted with probability one, and
the response it hands on lies in `relOut` (Eq. (20)), with the prover's and the verifier's output
statements equal.

The completeness error is `0` rather than something in `1 / |C|`: the honest masked opening
`z = Σᵢ cᵢ sᵢ` satisfies Eq. (20)'s folded rows c4/c5 identically in the challenge vector, so
`mem_relOut_of_relIn` holds at every `c` and the proof quantifies over the whole support of the
run. The `SampleableType` instance is required only so that execution can draw the challenge, not
for any property of its distribution.

The hypotheses are exactly the two gadget round-trips (`0 < messageDigits`, `0 < zDigits`,
`1 ≤ deg φ`) and the two digit bounds that put the honest decompositions inside `relOut`'s range
`γ`; `relIn`'s `βSq` and `κ` are unconstrained. For the concrete base-`b` decomposition see
`quadEvalReduction_perfectCompleteness_zmodDigits`. -/
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
/-- **Perfect completeness at the concrete base-`b` gadget, paper range `γ := b`.**
`quadEvalReduction_perfectCompleteness` instantiated with `zmodDigitDecomposition` at both gadget
steps — the decomposition the honest committer actually uses (`Decomposition.ofDigits`) — whose
digits are centered-bounded by `b - 1 ≤ b` (`zmodDigit_natAbs_le`).

The range is the paper's own `γ = b`, which is also the range of
`quadEval_coordinateWiseSpecialSoundWithEscape_paperParams`: at these parameters both security
directions of the link are available for the *same* `relIn`/`relOut` pair. `relIn`'s `βSq` and `κ`
stay free here, so the soundness side's `quadEvalBetaSq …` value can be plugged in. -/
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

end ArkLib.Lattices.Ajtai.InnerOuter
