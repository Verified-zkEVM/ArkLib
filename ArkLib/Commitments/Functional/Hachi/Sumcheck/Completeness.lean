/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval

/-!
  # The honest side of the Hachi sumcheck (§4.3)

  The completeness layer of the sumcheck loop, closing the honest chain
  `relNestedZeroCheck → nestedRoundRel 0 → nestedRoundRel m₀ → relWEvalClaim`. The two ends were
  already staged — `Sumcheck/Bridge.lean` installs the round-`0` claims,
  `Sumcheck/FinalEval.lean` consumes the round-`m₀` ones — so what is built here is the honest
  `m₀` interactive rounds and the composition.

  ## Contents

  * `honestComputeG` — the honest round message: the pair of *computable* partial hypercube sums
    in the free coordinate (`computableRoundPoly`, `Sumcheck/RoundPoly.lean`) together with their
    `degreeLE` memberships, i.e. `roundProver`'s parameter at its intended value.
  * `roundCheck_honestComputeG` / `mem_nestedRoundRel_roundOut_honestComputeG` — the honest
    message passes the round guard, and the round's output statement satisfies the round-`(i+1)`
    relation *at every challenge*, which is why the error is `0`.
  * `roundReduction`, `roundProver_run_eq`, `roundReduction_run_support`,
    `roundReduction_perfectCompleteness` — one round as a protocol object, its execution in
    closed form, and its perfect completeness. `roundReduction_verifier` records that this
    protocol object and the soundness certificate `roundPackage` share their verifier.
  * `roundsReduction` (+ `…Aux`) — the `m₀`-fold honest loop, mirroring `roundsChain`'s recursion
    over the binary append, with `roundsReduction_verifier` matching the two chains' verifiers.
  * `sumcheckReduction` — `bridge ▷ rounds ▷ final evaluation`, with
    `sumcheckReduction_perfectCompleteness` from `relNestedZeroCheck` to `relWEvalClaim`.

  Everything is stated at arity `m₀ = M + 1`: a round only exists when a cube coordinate is left
  to fold, the same successor shape `Sumcheck/RoundPoly.lean` and the round soundness theorem use.

  ## Axiom boundary

  `roundReduction_perfectCompleteness` — the per-round result, which carries all of the Hachi
  content — is **axiom-clean** (`propext`, `Classical.choice`, `Quot.sound`). Every *folded*
  statement (`roundsReductionAux_perfectCompleteness`, `roundsReduction_perfectCompleteness`,
  `sumcheckReduction_perfectCompleteness`) goes through `Reduction.append_perfectCompleteness`,
  which is `convert`-ed from the generic `Reduction.append_completeness` of
  `OracleReduction/Composition/Sequential/Append.lean` — **still `sorry`**. Those statements
  therefore depend on `sorryAx`, and each says so in its docstring. Nothing in this file adds a
  `sorry` of its own.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

section Rounds

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ M : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **The honest round message.** Both components are the computable partial hypercube sum of the
corresponding summand in the free coordinate `i` (`computableRoundPoly`), paired with its degree
membership — the first at `roundDegZero b = 2b`, the second at `roundDegAlpha = 2`.

This is `roundProver`'s `computeG` parameter at its intended value. Stated at arity `M + 1`
because a round only exists when a cube coordinate is left to fold, exactly as in
`Sumcheck/RoundPoly.lean` and in `round_coordinateWiseSpecialSoundWithEscape`. The `0 < b`
hypothesis is the range factor's degree condition, carried by
`computableRoundPoly_sumcheckPolyZero_mem_degreeLE`. -/
def honestComputeG {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1)
    (stmt : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n) :
    RoundMsg F b :=
  (⟨computableRoundPoly (sumcheckPolyZero Φ (M + 1) φF b stmt.zc.τ₀ w) ⟨i, hi⟩ stmt.challenges,
      computableRoundPoly_sumcheckPolyZero_mem_degreeLE Φ hb φF stmt.zc.τ₀ w ⟨i, hi⟩
        stmt.challenges⟩,
    ⟨computableRoundPoly
        (sumcheckPolyAlpha Φ (M + 1) m₁ φF b stmt.zc.rlin stmt.zc.α stmt.zc.τα w) ⟨i, hi⟩
        stmt.challenges,
      computableRoundPoly_sumcheckPolyAlpha_mem_degreeLE Φ φF b stmt.zc.rlin stmt.zc.α m₁
        stmt.zc.τα w ⟨i, hi⟩ stmt.challenges⟩)

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- The honest range component's values are the round-`(i+1)` partial sums of `F_{0,τ₀}`. -/
theorem honestComputeG_fst_eval {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F)
    (i : ℕ) (hi : i < M + 1)
    (stmt : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n) (T : F) :
    (honestComputeG Φ m₁ b hb φF i hi stmt w).1.1.eval T
      = hypercubeSum (M + 1) (sumcheckPolyZero Φ (M + 1) φF b stmt.zc.τ₀ w) (i + 1)
          (Fin.snoc stmt.challenges T) :=
  computableRoundPoly_eval _ _ _ T

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- The honest linear component's values are the round-`(i+1)` partial sums of `F_{α,τα}`. -/
theorem honestComputeG_snd_eval {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F)
    (i : ℕ) (hi : i < M + 1)
    (stmt : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n) (T : F) :
    (honestComputeG Φ m₁ b hb φF i hi stmt w).2.1.eval T
      = hypercubeSum (M + 1)
          (sumcheckPolyAlpha Φ (M + 1) m₁ φF b stmt.zc.rlin stmt.zc.α stmt.zc.τα w) (i + 1)
          (Fin.snoc stmt.challenges T) :=
  computableRoundPoly_eval _ _ _ T

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **The honest round message passes the round check.** For each summand the round-`i` claim of
`nestedRoundRel` *is* the partial cube sum, which splits into its two Boolean extensions
(`hypercubeSum_succ`); those two are the honest polynomial's values at `0` and `1`
(`computableRoundPoly_eval`). So `g(0) + g(1) = targetᵢ` for both components, which is exactly
`roundCheck`.

Holds for every statement in the round-`i` relation, with no condition beyond `0 < b` (needed
only to *type* the message). -/
theorem roundCheck_honestComputeG
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1)
    (stmt : NestedRoundStatement Φ K.TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n)
    (h : (stmt, w) ∈ nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b i) :
    roundCheck Φ (M + 1) m₁ b stmt (honestComputeG Φ m₁ b hb φF i hi stmt w) = true := by
  obtain ⟨-, -, hZero, hAlpha, -⟩ := h
  change hypercubeSum (M + 1) (sumcheckPolyZero Φ (M + 1) φF b stmt.zc.τ₀ w) i
    stmt.challenges = stmt.target₀ at hZero
  change hypercubeSum (M + 1)
    (sumcheckPolyAlpha Φ (M + 1) m₁ φF b stmt.zc.rlin stmt.zc.α stmt.zc.τα w) i
    stmt.challenges = stmt.targetα at hAlpha
  rw [hypercubeSum_succ (i := ⟨i, hi⟩)] at hZero hAlpha
  rw [roundCheck, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
    honestComputeG_fst_eval, honestComputeG_fst_eval,
    honestComputeG_snd_eval, honestComputeG_snd_eval]
  exact ⟨hZero, hAlpha⟩

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Relation preservation of one honest round.** At *every* challenge `a`, the round-`(i+1)`
relation holds at the honest output statement: the commitment, shortness and bound-sanity
conjuncts are carried over from the round-`i` relation, and the two new targets are by
construction the honest polynomials' values at `a`, which are the round-`(i+1)` partial sums at
the extended prefix (`computableRoundPoly_eval`).

That this holds for *every* `a` — no property of the challenge distribution — is why the round's
completeness error is exactly `0`. -/
theorem mem_nestedRoundRel_roundOut_honestComputeG
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1)
    (stmt : NestedRoundStatement Φ K.TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n)
    (h : (stmt, w) ∈ nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b i) (a : F) :
    (roundOut Φ (M + 1) m₁ b stmt (honestComputeG Φ m₁ b hb φF i hi stmt w) a, w) ∈
      nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b (i + 1) := by
  obtain ⟨hcom, hshort, -, -, hbound⟩ := h
  refine ⟨hcom, hshort, ?_, ?_, hbound⟩
  · exact (honestComputeG_fst_eval Φ m₁ b hb φF i hi stmt w a).symm
  · exact (honestComputeG_snd_eval Φ m₁ b hb φF i hi stmt w a).symm

/-! ## One honest round as a reduction -/

variable [SampleableType F]

/-- **The `i`-th paired sumcheck round as a protocol object**: the honest prover at
`honestComputeG` paired with the guarded round verifier of `Sumcheck/Rounds.lean`. Its verifier
is `roundPackage`'s on the nose (`roundReduction_verifier`). -/
def roundReduction {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1) :
    Reduction oSpec
      (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ (i + 1)) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F) where
  prover := roundProver Φ (M + 1) m₁ b i (honestComputeG Φ m₁ b hb φF i hi)
  verifier := roundVerifier Φ (M + 1) m₁ b i

set_option linter.unusedSectionVars false in
/-- The round's protocol object and its soundness certificate speak about the same verifier.
Holds by `rfl`. -/
@[simp] theorem roundReduction_verifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1) :
    (roundReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ b hb φF i hi).verifier
      = (roundPackage Φ (M + 1) m₁ bound ρBound b init impl K φF hb i hi).verifier :=
  rfl

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Honest execution of a round's two rounds.** Running the round prover to the end draws the
challenge `a` and ends with the transcript `⟨g, a⟩` and the state `((stmt, wit), a)`: the message
round appends `g = computeG stmt wit` and leaves the state untouched, the challenge round appends
`a` and stores it.

Two framework round-unfoldings rather than an induction, at the indices that literally occur
(`Fin.last 2`, then `(1 : Fin 2).castSucc = (0 : Fin 2).succ`), as in `QuadEval`'s
`prover_runToRound_last` — `rw` on a dependent round index does not typecheck. `hdir` is passed
as a named hypothesis for the same reason. -/
lemma roundProver_runToRound_last {TCom Wit : Type} (i : ℕ)
    (computeG : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i → Wit → RoundMsg F b)
    (stmt : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (wit : Wit)
    (hdir : (pSpecScalar (RoundMsg F b) F).dir 1 = .V_to_P) :
    (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound (Fin.last 2) stmt wit
      = (do
          let ch ← (pSpecScalar (RoundMsg F b) F).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (computeG stmt wit) ch, ((stmt, wit), ch))) := by
  have step2 : (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound
        (Fin.last 2) stmt wit
      = (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).processRound (1 : Fin 2)
          ((roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound
            ((1 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (1 : Fin 2) stmt wit _
  have step1 : (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound
        ((1 : Fin 2).castSucc) stmt wit
      = (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).processRound (0 : Fin 2)
          ((roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound
            ((0 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (0 : Fin 2) stmt wit _
  have step0 : (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).runToRound
        ((0 : Fin 2).castSucc) stmt wit
      = pure ((fun j => Fin.elim0 j), (stmt, wit)) := rfl
  refine step2.trans ?_
  rw [step1, step0, Prover.processRound_of_dir_eq_P_to_V (0 : Fin 2) rfl,
    Prover.processRound_of_dir_eq_V_to_P (1 : Fin 2) hdir]
  simp only [roundProver, liftM, monadLift, MonadLift.monadLift,
    OracleComp.liftComp_pure, monad_norm, FullTranscript.mk2_eq_snoc_snoc]
  rfl

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **The honest round prover's run in closed form**: draw `a`, then emit the transcript `⟨g, a⟩`,
the output statement `roundOut stmt g a` and the witness unchanged. Everything about the run is a
function of the one challenge. -/
lemma roundProver_run_eq {TCom Wit : Type} (i : ℕ)
    (computeG : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i → Wit → RoundMsg F b)
    (stmt : NestedRoundStatement Φ TCom F n μ (M + 1) m₁ i) (wit : Wit)
    (hdir : (pSpecScalar (RoundMsg F b) F).dir 1 = .V_to_P) :
    (roundProver (oSpec := oSpec) Φ (M + 1) m₁ b i computeG).run stmt wit
      = (do
          let ch ← (pSpecScalar (RoundMsg F b) F).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (computeG stmt wit) ch,
            roundOut Φ (M + 1) m₁ b stmt (computeG stmt wit) ch, wit)) := by
  unfold Prover.run
  rw [roundProver_runToRound_last Φ m₁ b i computeG stmt wit hdir]
  simp only [roundProver, liftM, monadLift, MonadLift.monadLift]
  rfl

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Honest-run characterization of one round.** Every outcome of an honest run is the single
success determined by the drawn challenge `a`: prover and verifier both output
`roundOut stmt g a` at the honest message `g`, and the witness is passed through.

Failure is excluded by `roundCheck_honestComputeG` — the round verifier is
`if roundCheck … then … else failure`, and the honest message passes it. -/
lemma roundReduction_run_support
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1)
    (hdir : (pSpecScalar (RoundMsg F b) F).dir 1 = .V_to_P)
    (stmt : NestedRoundStatement Φ K.TCom F n μ (M + 1) m₁ i) (w : LiftedWitness Φ μ n)
    (h : (stmt, w) ∈ nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b i) :
    ∀ x ∈ support ((roundReduction (oSpec := oSpec) (TCom := K.TCom)
        Φ m₁ b hb φF i hi).run stmt w).run,
      ∃ a : F,
        x = some ((FullTranscript.mk2 (honestComputeG Φ m₁ b hb φF i hi stmt w) a,
              roundOut Φ (M + 1) m₁ b stmt (honestComputeG Φ m₁ b hb φF i hi stmt w) a, w),
            roundOut Φ (M + 1) m₁ b stmt (honestComputeG Φ m₁ b hb φF i hi stmt w) a) := by
  have hg := roundCheck_honestComputeG Φ m₁ bound ρBound b K hb φF i hi stmt w h
  intro x hx
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨prOpt, hpr, hx⟩ := hx
  rw [show ((liftM (Prover.run stmt w
        (roundReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ b hb φF i hi).prover) :
        OptionT (OracleComp _) _)).run
      = (Prover.run stmt w
          (roundReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ b hb φF i hi).prover)
        >>= fun a => pure (some a) from rfl] at hpr
  rw [mem_support_bind_iff] at hpr
  obtain ⟨pr, hpr, hprOpt⟩ := hpr
  rw [mem_support_pure_iff] at hprOpt
  subst hprOpt
  rw [show (roundReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ b hb φF i hi).prover
      = roundProver Φ (M + 1) m₁ b i (honestComputeG Φ m₁ b hb φF i hi) from rfl,
    roundProver_run_eq Φ m₁ b i _ stmt w hdir, mem_support_bind_iff] at hpr
  obtain ⟨a, -, hpr⟩ := hpr
  rw [mem_support_pure_iff] at hpr
  subst hpr
  refine ⟨a, ?_⟩
  simp only [Option.elim_some, roundReduction, roundVerifier, Verifier.run, hg, if_true] at hx
  simp only [OptionT.run_pure, liftM_pure, ProgrammingPolicy.empty_apply, pure_bind,
    Option.elim_some, Option.getM_some, support_pure, Set.mem_singleton_iff] at hx
  exact hx

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Perfect completeness of one paired sumcheck round**, error exactly `0`.

The honest message passes the round check (`roundCheck_honestComputeG`) and the output statement
lands in the round-`(i+1)` relation at *every* challenge
(`mem_nestedRoundRel_roundOut_honestComputeG`), so no property of the challenge distribution is
used; `SampleableType F` is needed only so that the run can draw the challenge at all.

Hypotheses: `0 < b` (the range factor's degree bound, which the message's type carries) and
`i < m₀` (a cube coordinate is left to fold) — the same two side conditions the round's soundness
theorem carries. -/
theorem roundReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (i : ℕ) (hi : i < M + 1) :
    (roundReduction (oSpec := oSpec) (TCom := K.TCom)
        Φ m₁ b hb φF i hi).perfectCompleteness init impl
      (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b i)
      (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b (i + 1)) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt w h x hx
  obtain ⟨a, hx'⟩ :=
    roundReduction_run_support Φ m₁ bound ρBound b K hb φF i hi rfl stmt w h x hx
  refine ⟨_, hx', ?_, rfl⟩
  exact mem_nestedRoundRel_roundOut_honestComputeG Φ m₁ bound ρBound b K hb φF i hi stmt w h a

/-! ## The honest round chain

The `Reduction`-level counterpart of `roundsChainAux`: the same recursion over the binary append,
with the honest prover in place of the soundness certificate. `roundsReduction_verifier` records
that the two recursions build the *same* verifier, so the honest chain and the special-soundness
chain are two faces of one protocol.

**Axiom boundary.** `roundsReductionAux_perfectCompleteness` and everything downstream of it go
through `Reduction.append_perfectCompleteness`, which is `convert`-ed from the generic
`Reduction.append_completeness` — still `sorry` in
`OracleReduction/Composition/Sequential/Append.lean`. Those theorems therefore *depend on
`sorryAx`*, and `#print axioms` reports it. The per-round result
`roundReduction_perfectCompleteness` above is axiom-clean and is what actually carries the Hachi
content; the folded statements are exactly as strong as the framework's append lemma. -/

/-- The honest sumcheck loop over `count` rounds, by recursion over the binary append: the
zero-round `ReduceClaim` identity, then one `roundReduction` per round. Mirrors `roundsChainAux`
(`Sumcheck/Rounds.lean`) step for step, so that the two chains' verifiers agree
(`roundsReduction_verifier`).

No relation invariant has to ride along here (as it does for the packages): a `Reduction` carries
no relation fields, and the input/output relations appear only in the completeness statement. -/
def roundsReductionAux {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F) :
    (count : ℕ) → count ≤ M + 1 →
      Reduction oSpec
        (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ 0) (LiftedWitness Φ μ n)
        (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ count) (LiftedWitness Φ μ n)
        (roundsSpec F b count)
  | 0, _ => ReduceClaim.reduction oSpec id (fun _ w => w)
  | count + 1, hcount =>
    (roundsReductionAux hb φF count (by omega)).append
      (roundReduction Φ m₁ b hb φF count (by omega))

/-- The honest sumcheck loop, from the round-`0` statement (installed by the sumcheck bridge) to
the round-`count` statement (consumed by the final-evaluation step). Instantiated at
`count := m₀` in `sumcheckReduction`. -/
def roundsReduction {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F) (count : ℕ)
    (hcount : count ≤ M + 1) :
    Reduction oSpec
      (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ 0) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ TCom F n μ (M + 1) m₁ count) (LiftedWitness Φ μ n)
      (roundsSpec F b count) :=
  roundsReductionAux Φ m₁ b (TCom := TCom) hb φF count hcount

set_option linter.unusedSectionVars false in
/-- **The honest chain and the soundness chain share their verifier**, at every `count`. Proved by
recursion rather than by `rfl`: the two chains associate their appends the same way, but for an
open `count` the recursion's endpoints are only definitional per instance, so the induction step
has to be taken explicitly (`Reduction.append` and `EscapeGCWSSPackage.append` both build
`Verifier.append` of the two component verifiers). -/
theorem roundsReduction_verifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) :
    ∀ (count : ℕ) (hcount : count ≤ M + 1),
      (roundsReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ b hb φF count hcount).verifier
        = (roundsChain Φ (M + 1) m₁ bound ρBound b init impl K φF hb count hcount).verifier
  | 0, _ => rfl
  | count + 1, hcount =>
    congrArg (fun V => Verifier.append V (roundVerifier Φ (M + 1) m₁ b (TCom := K.TCom) count))
      (roundsReduction_verifier init impl K hb φF count (by omega))

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Perfect completeness of the honest round chain**, by recursion on `count`: the zero-round
base is `ReduceClaim` at the identity map, and each step appends one
`roundReduction_perfectCompleteness`.

⚠ **Inherits `sorryAx`** through `Reduction.append_perfectCompleteness`, whose content is the
still-unproved generic `Reduction.append_completeness`. The per-round input is axiom-clean. -/
theorem roundsReductionAux_perfectCompleteness (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) :
    ∀ (count : ℕ) (hcount : count ≤ M + 1),
      (roundsReductionAux (oSpec := oSpec) (TCom := K.TCom)
          Φ m₁ b hb φF count hcount).perfectCompleteness init impl
        (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b 0)
        (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b count)
  | 0, _ => by
    -- The zero-round base. Not `ReduceClaim.reduction_completeness_of_imp`: that theorem is
    -- stated at the empty spec `!p[]`, whose `SampleableType` instance is *not* the loop's
    -- `roundsSpecSampleable … 0` (the two specs are definitionally equal, the two instances are
    -- not syntactically), and unifying the two completeness statements makes the elaborator
    -- unfold `Reduction.run`. The instance-free `ReduceClaim.reduction_run_support` avoids the
    -- issue entirely.
    apply Reduction.perfectCompleteness_of_run_support
    intro stmt w hmem x hx
    exact ⟨_, ReduceClaim.reduction_run_support (mapStmt := id) (mapWit := fun _ w => w)
      stmt w x hx, hmem, rfl⟩
  | count + 1, hcount =>
    Reduction.append_perfectCompleteness
      (roundsReductionAux Φ m₁ b hb φF count (by omega))
      (roundReduction Φ m₁ b hb φF count (by omega))
      (roundsReductionAux_perfectCompleteness init impl K hb φF count (by omega))
      (roundReduction_perfectCompleteness Φ m₁ bound ρBound b init impl K hb φF count (by omega))
-- DIAGNOSTIC MARKER

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- Perfect completeness of `roundsReduction`, the exposed form of
`roundsReductionAux_perfectCompleteness`. ⚠ Inherits `sorryAx` for the same reason. -/
theorem roundsReduction_perfectCompleteness (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F) (count : ℕ) (hcount : count ≤ M + 1) :
    (roundsReduction (oSpec := oSpec) (TCom := K.TCom)
        Φ m₁ b hb φF count hcount).perfectCompleteness init impl
      (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b 0)
      (nestedRoundRel Φ (M + 1) m₁ bound ρBound K φF b count) :=
  roundsReductionAux_perfectCompleteness Φ m₁ bound ρBound b init impl K hb φF count hcount

/-! ## The local sumcheck, composed

`bridge ▷ rounds ▷ final evaluation`: from the zero-check's point claims
(`relNestedZeroCheck`) to the evaluation claim the recursion consumes (`relWEvalClaim`). -/

/-- The wire format of the whole local sumcheck: the zero-round bridge, then `m₀` paired rounds,
then the final-evaluation message. -/
@[reducible] def sumcheckSpec (F : Type) [Field F] (b m₀ : ℕ) : ProtocolSpec (0 + (2 * m₀ + 1)) :=
  (!p[] : ProtocolSpec 0) ++ₚ (roundsSpec F b m₀ ++ₚ pSpecFinalEval F)

/-- Sampleability of the sumcheck's tail (`m₀` rounds, then the final-evaluation message),
assembled explicitly: the generic append instance does not reliably fire through the
equation-compiled `roundsSpec`. -/
@[reducible] instance roundsFinalEvalSampleable (m₀ : ℕ) :
    ∀ i, SampleableType ((roundsSpec F b m₀ ++ₚ pSpecFinalEval F).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := roundsSpecSampleable F b m₀) (h₂ := inferInstance)

/-- Sampleability of the whole local sumcheck's wire format. -/
@[reducible] instance sumcheckSpecSampleable (m₀ : ℕ) :
    ∀ i, SampleableType ((sumcheckSpec F b m₀).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
    (h₂ := roundsFinalEvalSampleable b m₀)

/-- **The complete local sumcheck as one protocol object**: the zero-round bridge, the honest
`m₀`-round loop, and the final-evaluation step, appended. -/
def sumcheckReduction {TCom : Type} (hb : 0 < b) (φF : ZMod q →+* F) :
    Reduction oSpec
      (NestedZeroCheckStatement Φ TCom F n μ (M + 1) m₁) (LiftedWitness Φ μ n)
      (WEvalStatement TCom F (M + 1)) (LiftedWitness Φ μ n)
      (sumcheckSpec F b (M + 1)) :=
  (nestedSumcheckBridgeReduction Φ (M + 1) m₁ φF).append
    ((roundsReduction Φ m₁ b (TCom := TCom) hb φF (M + 1) le_rfl).append
      (finalEvalReduction Φ (M + 1) m₁ bound b φF))

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Perfect completeness of the local Hachi sumcheck**, from `relNestedZeroCheck` to
`relWEvalClaim`, error `0`.

The three links meet on the nose: the bridge installs `nestedRoundRel 0`, the loop carries it to
`nestedRoundRel m₀`, and the final-evaluation step turns that into `relWEvalClaim`. Hypotheses are
exactly the union of the links' own — `0 < b` (rounds), `0 < deg φ` and
`(μ + n)·deg φ ≤ 2^{m₀}` (the bridge's sum identities) — plus the standing field, sampling and
commitment assumptions. No hypothesis is needed for the final-evaluation step: its bound-sanity
conjunct is *carried* by the round relation.

⚠ **Inherits `sorryAx`** through `Reduction.append_perfectCompleteness` (generic
`Reduction.append_completeness`, still `sorry`). All three inputs are individually axiom-clean:
`nestedSumcheckBridgeReduction_perfectCompleteness`, `roundReduction_perfectCompleteness`,
`finalEvalReduction_perfectCompleteness`. -/
theorem sumcheckReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hb : 0 < b) (φF : ZMod q →+* F)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ (M + 1)) :
    (sumcheckReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ bound b hb
        φF).perfectCompleteness init impl
      (relNestedZeroCheck Φ (M + 1) m₁ bound ρBound K φF b)
      (relWEvalClaim Φ (M + 1) bound ρBound b K φF) :=
  Reduction.append_perfectCompleteness _ _
    (nestedSumcheckBridgeReduction_perfectCompleteness Φ (M + 1) m₁ bound ρBound init impl K φF b
      hd hμn)
    (Reduction.append_perfectCompleteness _ _
      (roundsReduction_perfectCompleteness Φ m₁ bound ρBound b init impl K hb φF (M + 1) le_rfl)
      (finalEvalReduction_perfectCompleteness Φ (M + 1) m₁ bound ρBound b init impl K φF))

end Rounds

end ArkLib.Lattices.Ajtai.InnerOuter
