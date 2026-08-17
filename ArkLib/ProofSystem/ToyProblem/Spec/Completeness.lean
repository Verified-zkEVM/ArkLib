/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Honest completeness of the toy-problem IORs (ABF26 Constructions 6.2 and 6.9)

Perfect completeness of both §6 toy-problem oracle reductions, together with
their point-form companions. The C6.2 results live in `Spec`; the C6.9 results
live in `SimplifiedIOR`. They are split out of the protocol-definition files to
keep those modules focused and below the long-file cap.

Like the rest of the §6 layer, all results are generic over the codeword
alphabet `A` (an `F`-module): `A = F` is the scalar specialization, while
`A = Fin s → F` is the genuine interleaved alphabet implemented by
`Impl/IRS.lean`. `Impl/FRS.lean` is the separate folded-RS model.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6, Constructions 6.2 and 6.9).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ProximityGap
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
variable (k t : ℕ)

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- Honest completeness for ABF26 Construction 6.2, point form: if
`((v, μ₁, μ₂), (f₁, f₂))` lies in `inputRelation` with the underlying
messages `M = (M₀, M₁)` (and `fᵢ` is the `encode`-image of `Mᵢ`), then
for any verifier challenges `(γ, xs)` the §6.1 decision `accepts` holds
against the honest prover's message `g = M₀ + γ · M₁`.

This is the point-form companion to the
`OracleReduction.perfectCompleteness` theorem that wraps the prover and
verifier objects below. -/
theorem accepts_of_inputRelation {k t : ℕ}
    {encode : (Fin k → F) →ₗ[F] (ι → A)}
    (stmt : Statement (F := F) k)
    (M : Witness (F := F) k)
    (hM : ∀ i, ∑ j, M i j * stmt.1 j =
        (if i = (0 : Fin 2) then stmt.2.1 else stmt.2.2))
    (f : ∀ i, OracleStatement ι A i)
    (hf : ∀ i, f i = encode (M i))
    (γ : F) (xs : Fin t → ι) :
    accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → A)))
      stmt f γ (fun j ↦ M 0 j + γ * M 1 j) xs := by
  refine ⟨?_, ?_⟩
  · -- Linear-constraint: ∑ j, (M 0 j + γ * M 1 j) * v j = μ₁ + γ * μ₂.
    have h0 : ∑ j, M 0 j * stmt.1 j = stmt.2.1 := by
      have := hM 0; simpa using this
    have h1 : ∑ j, M 1 j * stmt.1 j = stmt.2.2 := by
      have := hM 1
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simpa [if_neg hne] using this
    calc ∑ j, (M 0 j + γ * M 1 j) * stmt.1 j
        = ∑ j, (M 0 j * stmt.1 j + γ * (M 1 j * stmt.1 j)) := by
          apply Finset.sum_congr rfl; intros j _; ring
      _ = (∑ j, M 0 j * stmt.1 j) + ∑ j, γ * (M 1 j * stmt.1 j) :=
          Finset.sum_add_distrib
      _ = (∑ j, M 0 j * stmt.1 j) + γ * ∑ j, M 1 j * stmt.1 j := by
          rw [← Finset.mul_sum]
      _ = stmt.2.1 + γ * stmt.2.2 := by rw [h0, h1]
  · -- Spot-check: encode(g) x = f 0 x + γ • f 1 x.
    intro j
    have hg_eq : (fun i ↦ M 0 i + γ * M 1 i) = M 0 + γ • M 1 := by
      funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg_eq, map_add, map_smul, hf 0, hf 1]
    simp [Pi.add_apply, Pi.smul_apply]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `inputRelationFor encode`
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = M₀ + γ M₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

The proof unfolds
`OracleReduction.perfectCompleteness` through `toReduction`, expands the
prover's three-round `runToRound` via `Fin.induction_three`, resolves the three
round directions via the framework per-direction `processRound` unfolds
(`Prover.processRound_of_dir_eq_{V_to_P,P_to_V}`, `OracleReduction/Execution.lean`),
and reduces the `Pr[…] = 1` goal to a support-membership
obligation via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
(`ArkLib/ToVCVio/OracleComp/SimSemantics/SimulateQ.lean`). The support
obligation splits into:

  1. **The monadic core** — resolving the verifier body's `queryG`/`queryF`
     against `simOracle2` through the composed `MonadLiftT`/`OptionT` instance
     chains and collapsing the spot-check `forIn` — packaged as
     `verifierBody_simulateQ_eq_pure` (above), built on the staged toolkit
     (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
     `OracleComp.monadLift_liftM_OptionT`); the query routing itself is done by
     manual definitional bridges, not by the staged `simulateQ_add_add_liftM_*`
     simp family (whose `implA + implB` left-hand sides do not match
     `simOracle2`'s `addLift`/`liftTarget` spelling — that family remains an
     upstream-candidate for canonically-spelled goals). The recurrent obstacle —
     elaborated `MonadLift`/`ForIn` instance trees that are *definitionally* but
     not *syntactically* equal to the toolkit lemmas' canonical spellings — is
     bridged by `conv … change`/`show … from rfl` steps and a universe-pinned
     `emptySpec.{0,0}` ascription (the `[]ₒ` notation otherwise leaves a free
     universe metavariable that blocks `rw`).
  2. **Support plumbing** — peeling the `Reduction.run` OptionT-bind chain
     (challenge sampling, `Transcript.concat` layers, final `Option.getM`) via
     the `obtain`-friendly defeq peelers (`OptionT.mem_support_run_bind`,
     `OracleComp.mem_support_bind_peel`, …, same staged file), landing each
     support element on `verifierBody_simulateQ_eq_pure` with the accept
     hypotheses supplied by `accepts_of_inputRelation` from `hRel`.

**Statement faithfulness (fixed 2026-06-04).** The input relation is the
**fixed-encoding** `inputRelationFor encode` (the verifier's own `encode`, with
the witness `M` tied to the codewords `fᵢ = encode (M i)`). An earlier
existential-encoding form (`ToyProblem.relation`, `∃ encode'`) made completeness
*unprovable / false* — the honest prover's `encode g` need not match
`fᵢ = encode' (Mᵢ)` when `encode' ≠ encode` (the same defect found for the L6.12
attack). With `inputRelationFor encode` the discharge to `accepts_of_inputRelation`
(`hf : fᵢ = encode (M i)`, `hM : ⟨M i, v⟩ = μᵢ`) goes through. -/
theorem oracleReduction_perfectCompleteness
    [SampleableType F] [SampleableType ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → A)) :
    (oracleReduction (ι := ι) (F := F) (k := k) (t := t)
        (encode : (Fin k → F) → (ι → A))).perfectCompleteness
      init impl
      (inputRelationFor (encode := (encode : (Fin k → F) → (ι → A))))
      (Set.univ : Set (((OutputStatement × ∀ i, OutputOracleStatement i)) ×
        OutputWitness)) := by
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hRel
  -- Resolve the three round directions (`V_to_P` / `P_to_V` / `V_to_P`) via the framework-level
  -- per-direction `processRound` unfolds (`processRound_of_dir_eq_{V_to_P,P_to_V}`) instead of
  -- three hand-rolled `split`/`absurd` blocks, then unfold the reduction run, the 3-round prover
  -- (`Fin.induction_three`), and the oracle verifier's `toVerifier` wrapper. (`dir N` is proven by
  -- `rfl`, not `decide`, since the toy `pSpec`'s type vector carries the free vars `k`/`t`.)
  have h0 : (pSpec (ι := ι) (F := F) k t).dir 0 = .V_to_P := rfl
  have h1 : (pSpec (ι := ι) (F := F) k t).dir 1 = .P_to_V := rfl
  have h2 : (pSpec (ι := ι) (F := F) k t).dir 2 = .V_to_P := rfl
  simp only [OracleReduction.toReduction, Reduction.run, oracleReduction,
    oracleProver, OracleVerifier.toVerifier,
    Prover.run, Prover.runToRound, Fin.induction_three,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1,
    Prover.processRound_of_dir_eq_V_to_P 2 h2,
    Verifier.run, pSpec, bind_pure_comp]
  -- Reduce `Pr[…] = 1` to a support-membership obligation on the (pre-simulation)
  -- `OracleComp` body via the toolkit lemma, which peels the `(← init)` bind, the
  -- `simulateQ`/`StateT.run'` layers, and the `OptionT.mk` failure bookkeeping.
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx
  -- The output relation is trivial: `OutputStatement = OutputWitness = Unit`, so both
  -- conjuncts (`(a.2, a.1.2.2) ∈ Set.univ` and `a.1.2.1 = a.2`) hold for *every* `a`
  -- (`Subsingleton Unit`). It therefore suffices to show `x = some a` for some `a`.
  refine (fun ⟨a, ha⟩ ↦ ⟨a, ha, Set.mem_univ _, Subsingleton.elim _ _⟩) (?_ : ∃ a, x = some a)
  -- The monadic-simulation core (the historical C6.2 blocker — routing `queryG`/`queryF` through
  -- the composed `simOracle2` `MonadLift` chain and collapsing the `OptionT` spot-check `forIn`) is
  -- now **closed**, packaged as `verifierBody_simulateQ_eq_pure` (above) on top of the staged
  -- toolkit (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
  -- `OracleComp.monadLift_liftM_OptionT`). The defeq-vs-syntactic lift-instance gaps are bridged
  -- there by `conv … change` + universe-pinned `emptySpec.{0,0}` ascriptions.
  --
  -- The verifier body resolves to `pure (some ())` by `verifierBody_simulateQ_eq_pure` (above) —
  -- this is the load-bearing C6.2 content, now **fully proven**: for *any* sampled challenge `γ`
  -- and spot-check positions `xs`, the honest prover's round-1 message `g = M₀ + γ·M₁` makes both
  -- guards pass (`accepts_of_inputRelation`, supplied via `hRel : … ∈ inputRelationFor encode`),
  -- so the simulated verifier body never fails and yields `some ()`. Concretely, in `hx`'s run the
  -- verifier subterm is `simulateQ (simOracle2 []ₒ stmtIn.2 proverResult.1.messages) (do let g ←
  -- queryG; guard …; for …; …).run`, which is exactly `verifierBody_simulateQ_eq_pure` at
  -- `oStmt := stmtIn.2`, `msgs := proverResult.1.messages`, `g := proverResult.1.messages ⟨1,rfl⟩`.
  --
  -- The remaining work (ABF26-C6.2, now **closed**) is generic support plumbing: decompose
  -- `support (Reduction.run …)` through the `Prover.run` challenge-sampling binds (`getChallenge`
  -- for the two `V_to_P` rounds), the `Transcript.concat`/`liftM` coercion layers, and the final
  -- `OptionT.run`/`Option.getM`. The elaborated `liftM`/`OptionT`/`Fin.induction` bind tree is
  -- defeq but not syntactically `>>=`, so the syntactic `support_bind`/`mem_support_liftComp_iff`
  -- `rw`s do not engage; instead the peel is driven by the *definitional*-unification `obtain`
  -- helpers `OracleComp.mem_support_bind_peel`/`mem_support_map_peel`/`eq_of_mem_support_pure` and
  -- `OptionT.mem_support_run_bind`/`_lift_bind` (`ArkLib/ToVCVio/.../SimulateQ.lean`). Each support
  -- element fixes a sampled `(γ₀, xs₂)` and the deterministic honest message
  -- `proverResult.1.messages ⟨1,rfl⟩ = fun j => witIn 0 j + γ₀ · witIn 1 j`; under that message
  -- `verifierBody_simulateQ_eq_pure` (via `accepts_of_inputRelation`) collapses the verifier body
  -- to `pure (some ())`, forcing `stmtOut = some _` and hence `x = some _`.
  obtain ⟨proverResult, hPR, hx⟩ := OptionT.mem_support_run_lift_bind _ _ hx
  -- Characterize the honest prover's transcript from `hPR`.
  rw [show (monadLift : OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _) = id from rfl,
      id_eq] at hPR
  -- Peel the prover-run binds by *definitional*-unification `obtain` (the elaborated
  -- `Fin.induction` bind tree is defeq but not syntactically `>>=`, so `rw`-based
  -- peelers do not engage).
  -- `prover.run = let r ← runToRound (last 3); ⟨r.1, ← output r.2⟩`.
  obtain ⟨r3, hr3, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  obtain ⟨out, hout, hPReq⟩ := OracleComp.mem_support_map_peel _ _ hPR
  have hout := OracleComp.eq_of_mem_support_pure _ hout
  subst hout
  -- runToRound = processRound 2 (processRound 1 (processRound 0 (pure base))).
  -- Peel the round-2 bind: `r3 ∈ support (let r2 ← (rounds 0-1); round2body r2)`.
  obtain ⟨r2, hr2, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Peel the round-1 bind from `hr2`: `r2 ∈ support (let r1 ← (round 0); round1body r1)`.
  obtain ⟨r1, hr1, hr2⟩ := OracleComp.mem_support_bind_peel _ _ hr2
  -- Peel the round-0 bind from `hr1`: `r1 ∈ support (let r0 ← pure base; round0body r0)`.
  obtain ⟨r0, hr0, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- Resolve `r0` to the pure base value (kept symbolic to avoid spelling `default`).
  have hr0 := OracleComp.eq_of_mem_support_pure _ hr0
  subst hr0
  -- round 0: peel the challenge `γ₀`, then resolve `r1`.
  obtain ⟨γ₀, hγ₀, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- round 2: peel the challenge `xs₂`, then resolve `r3`.
  obtain ⟨xs₂, hxs₂, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Resolve `r1`, `r2`, `r3` from their `map`-of-`liftM (pure …)` supports.
  obtain ⟨f1, hf1, hr1⟩ := OracleComp.mem_support_map_peel _ _ hr1
  obtain ⟨f2, hf2, hr2⟩ := OracleComp.mem_support_map_peel _ _ hr2
  obtain ⟨f3, hf3, hr3⟩ := OracleComp.mem_support_map_peel _ _ hr3
  have hf1 := OracleComp.eq_of_mem_support_pure _ hf1
  have hf2 := OracleComp.eq_of_mem_support_pure _ hf2
  have hf3 := OracleComp.eq_of_mem_support_pure _ hf3
  subst hf1 hf2 hf3 hr1 hr2 hr3 hPReq
  -- Extract the witness facts from the input relation.
  obtain ⟨hf, hM⟩ := hRel
  have hacc := accepts_of_inputRelation (encode := encode) stmtIn.1 witIn
    (fun i ↦ by have := hM i; fin_cases i <;> simpa using this) stmtIn.2
    (fun i ↦ by have := hf i; simpa using this) (cast (by rfl) γ₀) xs₂
  -- Rewrite through the stable `OracleVerifier`-boundary characterization; the output map is
  -- retained and materializes the (empty) output-oracle family after successful verification.
  rw [oracleVerifier_simulateQ_eq_pure_ite
      (encode := (encode : (Fin k → F) → (ι → A)))] at hx
  simp only [FullTranscript.challenges, FullTranscript.messages, Fin.snoc,
    Fin.val_zero, Fin.val_one, Fin.val_two, lt_self_iff_false, Fin.val_castLT,
    Fin.castSucc_castLT, show (0 : ℕ) < 2 from by norm_num,
    show (0 : ℕ) < 1 from by norm_num, show (1 : ℕ) < 2 from by norm_num,
    show ¬ ((2 : ℕ) < 0) from by norm_num, dif_pos, cast_eq, dite_false] at hx
  split at hx
  · -- The verifier computation cannot fail. Peel its output map and the trailing reduction bind.
    rcases OptionT.mem_support_run_bind _ _ hx with ⟨hverNone, _⟩ | ⟨stmtOut, hSO, hx⟩
    · exact absurd (OracleComp.eq_of_mem_support_pure _ hverNone) (by simp)
    · have hSO := OracleComp.eq_of_mem_support_pure _ hSO
      rw [Option.some.injEq] at hSO
      subst hSO
      have hx := OracleComp.eq_of_mem_support_pure _ hx
      exact ⟨_, hx⟩
  · rename_i hreject
    exfalso
    apply hreject
    convert hacc using 1 <;> congr 1

/-! ### Regression guards: both decision checks are load-bearing

The C6.2 security statements use `Set.univ` as their output relation — legitimately, since
`OutputStatement = OutputWitness = Unit` — so *all* of the accept-gating rides on the
verifier's `OptionT` failure, i.e. on the two `guard`s of `oracleVerifier` and hence on
`accepts` being a genuinely partial predicate.  A refactor that dropped or weakened either
`guard` would leave every theorem in this file still true and still provable, while making
them vacuous.

The two lemmas below pin that invariant at its source.  Each is a pair of instances of
`accepts` that differ in **exactly one** input — the constraint value `μ₁` in the first, the
oracle codewords in the second — with acceptance flipping between them.  So neither check can
be dropped without breaking a compiled theorem, and neither is implied by the other.

They pin the predicate, not the game: the stronger statement — that an always-accepting C6.2
verifier fails knowledge soundness at small error — needs the full `Reduction.run`
probability computation against a cheating prover and is not proven here. -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **The linear-constraint check is load-bearing.** Two statements that differ only in `μ₁`
(`0` versus `1`), at the zero encoder, zero codewords and zero prover message: the first is
accepted, the second must not be.  Every spot-check passes in both, so acceptance here is
decided by the linear constraint alone. -/
theorem accepts_iff_of_linear_constraint {k t : ℕ} (γ : F) (xs : Fin t → ι) :
    accepts (ι := ι) (F := F) (A := A) k t (fun _ ↦ (0 : ι → A))
        ((0 : Fin k → F), (0 : F), (0 : F)) (fun _ _ ↦ (0 : A)) γ 0 xs ∧
      ¬ accepts (ι := ι) (F := F) (A := A) k t (fun _ ↦ (0 : ι → A))
        ((0 : Fin k → F), (1 : F), (0 : F)) (fun _ _ ↦ (0 : A)) γ 0 xs := by
  refine ⟨⟨by simp, fun j ↦ by simp⟩, ?_⟩
  rintro ⟨hlin, -⟩
  simp at hlin

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **The spot-checks are load-bearing.** Two oracle assignments that differ only in the first
codeword (`0` versus the nonzero constant `a`), at the zero statement, zero encoder and zero
prover message: the first is accepted, the second must not be.  The linear constraint passes
in both, so acceptance here is decided by the spot-checks alone. -/
theorem accepts_iff_of_spot_check {k t : ℕ}
    (γ : F) (xs : Fin t → ι) (hpos : 0 < t) (a : A) (ha : a ≠ 0) :
    accepts (ι := ι) (F := F) (A := A) k t (fun _ ↦ (0 : ι → A))
        ((0 : Fin k → F), (0 : F), (0 : F)) (fun _ _ ↦ (0 : A)) γ 0 xs ∧
      ¬ accepts (ι := ι) (F := F) (A := A) k t (fun _ ↦ (0 : ι → A))
        ((0 : Fin k → F), (0 : F), (0 : F))
        (fun i _ ↦ if i = 0 then a else 0) γ 0 xs := by
  refine ⟨⟨by simp, fun j ↦ by simp⟩, ?_⟩
  rintro ⟨-, hspot⟩
  exact ha (by simpa using (hspot ⟨0, hpos⟩).symm)

end Protocol

end Spec

namespace SimplifiedIOR

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]

/-- Honest completeness for ABF26 Construction 6.9, point form.  A witness for
the two-word relaxed relation maps, for every challenge `γ`, to the linear
combination witness for the derived one-word relaxed relation.  The same
agreement set works before and after the transition. -/
theorem derivedOutput_mem_outputRelationFor {k : ℕ}
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι A i))
    (M : Spec.Witness (F := F) k)
    (hM : (stmtIn, M) ∈ Spec.outputRelationFor k
      (encode : (Fin k → F) → (ι → A)) δ)
    (γ : F) :
    (derivedOutput (ι := ι) (F := F) (A := A) k stmtIn γ,
        fun j ↦ M 0 j + γ * M 1 j) ∈
      outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ := by
  rcases hM with ⟨hlin, S, hScard, hagree⟩
  refine ⟨?_, S, hScard, ?_⟩
  · have h0 := hlin 0
    have h1 := hlin 1
    simp only [derivedOutput]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    calc
      ∑ j, (M 0 j + γ * M 1 j) * stmtIn.1.1 j =
          (∑ j, M 0 j * stmtIn.1.1 j) + γ * ∑ j, M 1 j * stmtIn.1.1 j := by
            simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      _ = stmtIn.1.2.1 + γ * stmtIn.1.2.2 := by rw [h0, h1]
  · intro j hj
    simp only [derivedOutput]
    have h0 := hagree 0 j hj
    have h1 := hagree 1 j hj
    rw [show (fun x ↦ M 0 x + γ * M 1 x) = M 0 + γ • M 1 by
      funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
    rw [map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [← h0, ← h1]

/-- **Perfect completeness for Construction 6.9** (protocol-level form).

For every verifier challenge, the honest prover and the virtual-output
verifier produce the same derived statement and oracle, and
`derivedOutput_mem_outputRelationFor` supplies the corresponding combined
witness.  Thus C6.9 is perfectly complete from `R̃²_{C,δ}` to
`R̃¹_{C,δ}`. -/
theorem oracleReduction_perfectCompleteness {k : ℕ}
    [SampleableType F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    (oracleReduction (ι := ι) (F := F) (A := A) (k := k)).perfectCompleteness
      init impl
      (Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ) := by
  classical
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hRel
  have h0 : (pSpec (F := F)).dir 0 = .V_to_P := rfl
  simp only [OracleReduction.toReduction, Reduction.run, oracleReduction,
    oracleProver, Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, prover]
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx
  obtain ⟨proverResult, hPR, hx⟩ := OptionT.mem_support_run_lift_bind _ _ hx
  rw [show (monadLift : OracleComp ([]ₒ + [(pSpec (F := F)).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [(pSpec (F := F)).Challenge]ₒ) _) = id from rfl,
      id_eq] at hPR
  obtain ⟨r1, hr1, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  obtain ⟨out, hout, hPReq⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  change out ∈ support (pure (match r1.2 with
      | (γ, (stmt, oStmt), M) =>
        (((stmt.1, stmt.2.1 + γ * stmt.2.2),
          fun _ j => oStmt 0 j + γ • oStmt 1 j),
          fun j => M 0 j + γ * M 1 j)) :
        OracleComp ([]ₒ + [(pSpec (F := F)).Challenge]ₒ) _) at hout
  have hout_eq := OracleComp.eq_of_mem_support_pure _ hout
  subst out
  have hPReq_eq := OracleComp.eq_of_mem_support_pure _ hPReq
  subst proverResult
  obtain ⟨r0, hr0, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  have hr0_eq := OracleComp.eq_of_mem_support_pure _ hr0
  subst r0
  obtain ⟨γ, -, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  obtain ⟨f1, hf1, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  change f1 ∈ support (pure (fun γ => (γ, (default, id (stmtIn, witIn)).2)) :
    OracleComp ([]ₒ + [(pSpec (F := F)).Challenge]ₒ) _) at hf1
  have hf1_eq := OracleComp.eq_of_mem_support_pure _ hf1
  subst f1
  have hr1_eq := OracleComp.eq_of_mem_support_pure _ hr1
  subst r1
  rw [oracleVerifier_toVerifier_run_eq_pure] at hx
  rcases OptionT.mem_support_run_bind _ _ hx with ⟨hverNone, _⟩ | ⟨stmtOut, hSO, hx⟩
  · exact absurd (OracleComp.eq_of_mem_support_pure _ hverNone) (by simp)
  · have hSO_eq := OracleComp.eq_of_mem_support_pure _ hSO
    rw [Option.some.injEq] at hSO_eq
    subst stmtOut
    have hx_eq := OracleComp.eq_of_mem_support_pure _ hx
    refine ⟨_, hx_eq, ?_, ?_⟩
    · apply derivedOutput_mem_outputRelationFor
        (encode := encode) (δ := δ) (stmtIn := stmtIn)
        (M := witIn) (γ := cast (by rfl) γ) hRel
    · rfl

end SimplifiedIOR

end ToyProblem
