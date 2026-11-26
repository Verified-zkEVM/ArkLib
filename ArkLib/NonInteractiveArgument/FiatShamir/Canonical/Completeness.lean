/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Shared

/-!
# Completeness of canonical Fiat–Shamir

Fixed verifier-message tables preserve perfect completeness. A shared lazy random
oracle preserves the completeness error bound.
-/

@[expose] public section

universe u v

open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

open FiatShamir

section Security

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

noncomputable section

open scoped NNReal

variable [samples : ∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Perfect completeness is preserved for every fixed challenge table. Full support of each
uniform interactive challenge ensures that every transformed honest execution is an interactive
branch; verifier reconstruction replays exactly that branch. -/
theorem fiatShamir_perfectCompleteness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hR : R.perfectCompleteness init impl relIn relOut)
    (f : QueryImpl (srVerifierMessageOracle StmtIn pSpec) Id) :
    R.fiatShamir.perfectCompleteness (do return (← init, f))
      (impl.addLift fsChallengeQueryImpl') relIn relOut := by
  erw [Reduction.perfectCompleteness_eq_prob_one] at hR ⊢
  intro stmt wit hin
  have hgood := (OracleComp.OptionT.prEvent_mk_eq_one_iff _ _).mp (hR stmt wit hin)
  apply (OracleComp.OptionT.prEvent_mk_eq_one_iff _ _).mpr
  intro result hresult
  simp only [bind_assoc, pure_bind] at hresult
  obtain ⟨s, hs, hresult⟩ := mem_support_bind_peel _ _ hresult
  rw [StateT.run'_eq] at hresult
  obtain ⟨z, hz, hresult⟩ := mem_support_map_peel _ _ hresult
  subst result
  obtain ⟨y, hy, heq⟩ := R.fiatShamir_run_support impl stmt wit s f z (by
    convert hz using 1
    congr 3
    funext q
    rcases q with q | q
    · rfl
    · exact isEmptyElim q.1)
  have hyInit : y.1 ∈ support (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (R.run stmt wit).run).run' (← init)) := by
    apply (mem_support_bind_iff _ _ _).mpr
    refine ⟨s, hs, ?_⟩
    rw [StateT.run'_eq]
    rw [support_map]
    exact ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hrel, hagree⟩ := hgood y.1 hyInit
  cases hzopt : z.1 with
  | none => simp [hzopt, hr] at heq
  | some zr =>
    refine ⟨zr, rfl, ?_⟩
    have hout : (zr.1.2, zr.2) = (r.1.2, r.2) := by
      simpa [hzopt, hr] using heq
    rcases zr with ⟨⟨_, _, _⟩, _⟩
    rcases r with ⟨⟨_, _, _⟩, _⟩
    simp only [Prod.mk.injEq] at hout
    rcases hout with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨hrel, hagree⟩

/-- Completeness error is preserved by a lazy random challenge oracle shared by the
transformed prover and verifier. The cache starts empty; distinct round indices make every
honest prover query fresh, and reconstruction replays the cached answers. Decidable equality
of query keys suffices, with no finite statement, message, or base-state assumption. -/
theorem fiatShamir_completeness_randomOracle
    [DecidableEq (srVerifierMessageOracle StmtIn pSpec).Domain]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (ε : ℝ≥0)
    (hR : R.completeness init impl relIn relOut ε) :
    R.fiatShamir.completeness
      (do return (← init, (∅ : (srVerifierMessageOracle StmtIn pSpec).QueryCache)))
      (fsRandomOracleImpl impl) relIn relOut ε := by
  intro stmt wit hin
  have hd := EvalDistEq.bind_right init fun s =>
    R.fiatShamir_randomOracle_outputs impl stmt wit s
  have hp := hd.prEvent_eq (fun z => z.1.elim False (fun r =>
    (r.2, r.1.2) ∈ relOut ∧ r.1.1 = r.2))
  have h := hR stmt wit hin
  simp only [OptionT.prEvent_mk, StateT.run'_eq, bind_assoc, pure_bind,
    map_bind] at h ⊢
  simp only [map_bind, Functor.map_map, Option.elim_map, Function.comp_def] at hp h ⊢
  convert h.trans hp.ge using 1
  apply congrArg prEvent
  apply bind_congr
  intro s
  congr 3
  funext q
  rcases q with q | q
  · rfl
  · exact isEmptyElim q.1

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
