/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FiniteDomainQuotient
public import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# Finite-domain quotient zero test

The prover sends a polynomial of natural degree at most `d - S.card` before the verifier
samples a uniform field element. The verifier queries the input polynomial and quotient once
each and guards their multiplication identity. The output relation is acceptance, with no
output oracles and a `Unit` witness. The inclusive input bound `natDegree ≤ d` gives error
`d / |F|`, including the zero polynomial convention `natDegree 0 = 0`.

Coefficient arrays make the honest quotient and evaluation oracle executable. A domain carries
an executable nodal evaluation, allowing subgroup instances to use powering directly.
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory
open FiniteDomainQuotient

namespace QuotientZeroTest

variable (F : Type) [Field F]

/-- A finite domain with a certified executable nodal evaluation. -/
structure Domain where
  points : Finset F
  evalNodal : F → F
  evalNodal_eq : ∀ z, evalNodal z = (Lagrange.nodal points id).eval z

/-- Evaluate the nodal polynomial by its finite product. -/
def finiteDomain (S : Finset F) : Domain F where
  points := S
  evalNodal z := ∏ x ∈ S, (z - x)
  evalNodal_eq _ := Lagrange.eval_nodal.symm

/-- A subgroup domain evaluates its nodal polynomial directly as `z ^ |H| - 1`. -/
def subgroupDomain (H : Subgroup Fˣ) [Fintype H] : Domain F where
  points := Finset.univ.map (Lagrange.subgroupEmbedding H)
  evalNodal z := z ^ Fintype.card H - 1
  evalNodal_eq z := (Lagrange.eval_nodal_image_subgroup H z).symm

variable [DecidableEq F]

/-- Degree-bounded polynomial oracles expose only evaluation queries. -/
instance (d : ℕ) : OracleInterface (Poly F d) where
  Query := F
  toOC.spec := fun _ => F
  toOC.impl z := do return eval (← read) z

variable (D : Domain F) (d : ℕ)

/-- The quotient is fixed in the first round, before the uniform evaluation challenge. -/
@[reducible] def pSpec : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Poly F (d - D.points.card), F]⟩

instance : ∀ i, OracleInterface ((pSpec F D d).Message i)
  | ⟨0, _⟩ => inferInstanceAs (OracleInterface (Poly F (d - D.points.card)))
  | ⟨1, h⟩ => nomatch h

instance [SampleableType F] : ∀ i, SampleableType ((pSpec F D d).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType F)

/-- The sole input oracle is the degree-bounded dividend. -/
abbrev OStmtIn := fun _ : Unit => Poly F d
/-- No polynomial oracles remain after the acceptance check. -/
abbrev OStmtOut := fun _ : Empty => Unit

instance : ∀ i, OracleInterface (OStmtOut i) := fun i => nomatch i

/-- The input relation has no private witness beyond the polynomial oracle. -/
def relIn : Set ((Unit × ∀ i, OStmtIn F d i) × Unit) :=
  {x | Polynomial.ZeroOn D.points (x.1.2 ()).val.toPoly}

/-- All returned outputs are accepting; a failed equation aborts the verifier. -/
def relOut : Set ((Unit × ∀ i, OStmtOut i) × Unit) := Set.univ

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Query the dividend and quotient, guard their evaluation identity, then return acceptance. -/
def oracleVerifier : OracleVerifier oSpec Unit (OStmtIn F d)
    Unit OStmtOut (pSpec F D d) where
  verify _ chals := do
    let z : F := chals ⟨1, rfl⟩
    let fz : F ← query (spec := [OStmtIn F d]ₒ) ⟨(), z⟩
    let qz : F ← query (spec := [(pSpec F D d).Message]ₒ) ⟨⟨0, rfl⟩, z⟩
    guard (fz = qz * D.evalNodal z)
    return ()
  outputOracle := .inl {
    embed := Function.Embedding.ofIsEmpty
    hEq := fun i => nomatch i
    outputInterface_heq := fun i => nomatch i }

/-- The deterministic equation on a fully materialized transcript. -/
def check (stmt : Unit × ∀ i, OStmtIn F d i) (tr : (pSpec F D d).FullTranscript) : Prop :=
  eval (stmt.2 ()) (tr 1) = eval (tr 0) (tr 1) * D.evalNodal (tr 1)

instance (stmt : Unit × ∀ i, OStmtIn F d i) (tr : (pSpec F D d).FullTranscript) :
    Decidable (check F D d stmt tr) := inferInstanceAs (Decidable (_ = _))

/-- Materialization performs exactly the pure check, with failure when the equation is false. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn F d i)
    (tr : (pSpec F D d).FullTranscript) :
    (oracleVerifier F D d oSpec).toVerifier.verify stmt tr =
      if check F D d stmt tr then pure ((), Empty.elim) else failure := by
  have hfst (z : F) :
      simulateQ (OracleInterface.simOracle2 oSpec stmt.2 tr.messages)
        (liftM (OracleSpec.query (spec := [OStmtIn F d]ₒ) ⟨(), z⟩) :
          OracleComp (oSpec + ([OStmtIn F d]ₒ + [(pSpec F D d).Message]ₒ)) F) =
        pure (eval (stmt.2 ()) z) := rfl
  simp only [OracleVerifier.toVerifier, oracleVerifier, guard]
  erw [OptionT.run_bind, simulateQ_bind, OptionT.run_monadLift]
  simp only [simulateQ_map]
  erw [hfst, map_pure, pure_bind, Option.elim_some]
  erw [OptionT.run_bind, simulateQ_bind, OptionT.run_monadLift]
  simp only [simulateQ_map]
  erw [OracleInterface.simulateQ_simOracle2_liftM_query_snd, map_pure, pure_bind,
    Option.elim_some]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

/-- Named guard and output data for guarded composition and knowledge bridges. -/
def guardedForm : (oracleVerifier F D d oSpec).toVerifier.GuardedForm where
  check stmt tr := decide (check F D d stmt tr)
  out _ _ := ((), Empty.elim)
  verify_eq stmt tr := by
    rw [oracleVerifier_toVerifier]
    simp only [decide_eq_true_eq]

/-- The honest prover sends the computable monic quotient and has no output witness. -/
def oracleProver : OracleProver oSpec Unit (OStmtIn F d) Unit
    Unit OStmtOut Unit (pSpec F D d) where
  PrvState _ := Poly F d
  input x := x.1.2 ()
  sendMessage
    | ⟨0, _⟩ => fun f => pure (quotient D.points f, f)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun f => pure (fun _ => f)
  output _ := pure (((), Empty.elim), ())

instance : (oracleProver F D d oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- The finite-domain zero test as an oracle reduction. -/
def oracleReduction : OracleReduction oSpec Unit (OStmtIn F d) Unit
    Unit OStmtOut Unit (pSpec F D d) :=
  ⟨oracleProver F D d oSpec, oracleVerifier F D d oSpec⟩

/-- Each backward extraction step returns the unique input witness. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn F d i)
    Unit Unit (pSpec F D d) (fun _ => Unit) where
  extractIn _ w := w
  extractMid _ _ _ _ := ()
  extractOut _ _ _ := ()

variable [SampleableType F]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Before the challenge, knowledge means the input vanishes on the domain; afterwards it
means the sampled identity holds. A prover message cannot change the former property. -/
def knowledgeStateFunction : (oracleVerifier F D d oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn F D d) relOut (rbrExtractor F D d oSpec) where
  toFun
    | 0 => fun stmt _ _ => Polynomial.ZeroOn D.points (stmt.2 ()).val.toPoly
    | 1 => fun stmt _ _ => Polynomial.ZeroOn D.points (stmt.2 ()).val.toPoly
    | 2 => fun stmt tr _ => check F D d stmt tr
  toFun_empty _ _ h := h
  toFun_next
    | ⟨0, _⟩ => fun _ _ _ _ _ h => h
    | ⟨1, _⟩ => fun h => nomatch h
  toFun_full stmt tr _ h := by
    change check F D d stmt tr
    have hc := ((guardedForm F D d oSpec).check_and_of_prEvent_pos h).1
    simpa only [guardedForm, decide_eq_true_eq] using hc

omit [SampleableType F] in
/-- The honest quotient passes at every point, including points inside the domain. -/
theorem honest_check (f : Poly F d) (hf : Polynomial.ZeroOn D.points f.val.toPoly) (z : F) :
    eval f z = eval (quotient D.points f) z * D.evalNodal z := by
  rw [eval_eq, eval_eq, D.evalNodal_eq, ← Polynomial.eval_mul,
    ← quotient_identity D.points f hf]

/-- Perfect completeness for every ambient oracle implementation and initial state. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction F D d oSpec).perfectCompleteness init impl (relIn F D d) relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hf x hx
  rw [Reduction.run_run_eq_bind] at hx
  simp only [oracleReduction, OracleReduction.toReduction] at hx
  have hpr : (oracleProver F D d oSpec).run stmt wit = (do
      let z ← (pSpec F D d).getChallenge ⟨1, rfl⟩
      pure (((default : (pSpec F D d).Transcript 0).concat
        (m := (0 : Fin 2)) (quotient D.points (stmt.2 ()))).concat
        (m := (1 : Fin 2)) z, (((), Empty.elim), ()))) := by
    simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
      Prover.processRound, oracleProver, ProtocolSpec.getChallenge, Fin.vcons, Fin.dcons]
  rw [hpr] at hx
  simp only [bind_assoc, pure_bind, Verifier.run, oracleVerifier_toVerifier] at hx
  have hc (z : F) : check F D d stmt
      (((default : (pSpec F D d).Transcript 0).concat
        (m := (0 : Fin 2)) (quotient D.points (stmt.2 ()))).concat
        (m := (1 : Fin 2)) z) := by
    change eval (stmt.2 ()) z = eval (quotient D.points (stmt.2 ())) z * D.evalNodal z
    exact honest_check F D d (stmt.2 ()) hf z
  simp only [hc, ite_true, OptionT.run_pure, liftComp_pure, pure_bind,
    Option.map_some, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨z, _, rfl⟩ := hx
  exact ⟨_, rfl, Set.mem_univ _, rfl⟩

variable [Fintype F]

/-- At every fixed prefix, a false domain-vanishing claim passes with probability at most
`d / |F|`. The message's type enforces the quotient degree even for a dishonest prover. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith (hcard : D.points.card ≤ d) :
    (oracleVerifier F D d oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn F D d) relOut (fun _ => Unit) (rbrExtractor F D d oSpec)
      (knowledgeStateFunction F D d oSpec init impl)
      (fun _ => (d : ℝ≥0) / Fintype.card F) := by
  apply Verifier.rbrKnowledgeSoundnessWith_of_two_message rfl rfl
  intro stmt tr
  let q : Poly F (d - D.points.card) := tr ⟨0, Nat.zero_lt_one⟩
  change Pr{let z ← $ᵗ F}[∃ _ : Unit,
    ¬ Polynomial.ZeroOn D.points (stmt.2 ()).val.toPoly ∧
      check F D d stmt (tr.concat (m := (1 : Fin 2)) z)] ≤ _
  simp only [exists_const]
  by_cases hf : Polynomial.ZeroOn D.points (stmt.2 ()).val.toPoly
  · simp [hf]
  · simp only [hf, not_false_eq_true, true_and]
    have hcheck (z : F) : check F D d stmt (tr.concat (m := (1 : Fin 2)) z) ↔
        (stmt.2 ()).val.toPoly.eval z = q.val.toPoly.eval z *
          (Lagrange.nodal D.points id).eval z := by
      change eval (stmt.2 ()) z = eval q z * D.evalNodal z ↔ _
      rw [eval_eq, eval_eq, D.evalNodal_eq]
    rw [prEvent_congr ($ᵗ F) _ _ hcheck]
    have hbound := Polynomial.prob_eval_eq_mul_nodal_le hcard hf
      (stmt.2 ()).property q.property
    have hdenom : (Fintype.card F : ℝ≥0) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simpa only [ENNReal.coe_div hdenom, ENNReal.coe_natCast] using hbound

/-- Existential form of the named fixed-prefix knowledge certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundness (hcard : D.points.card ≤ d) :
    (oracleVerifier F D d oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn F D d) relOut (fun _ => (d : ℝ≥0) / Fintype.card F) :=
  ⟨_, rbrExtractor F D d oSpec, knowledgeStateFunction F D d oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWith F D d oSpec init impl hcard⟩

/-- The guarded bridge gives ordinary knowledge soundness with the named backward-fold
extractor. There is exactly one challenge contribution. -/
theorem oracleVerifier_knowledgeSoundnessWith (hcard : D.points.card ≤ d) :
    (oracleVerifier F D d oSpec).toVerifier.knowledgeSoundnessWith init impl
      (relIn F D d) relOut (rbrExtractor F D d oSpec).foldExtractor
      (∑ _ : (pSpec F D d).ChallengeIdx, (d : ℝ≥0) / Fintype.card F) :=
  (guardedForm F D d oSpec).knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith
    (knowledgeStateFunction F D d oSpec init impl)
    (oracleVerifier_rbrKnowledgeSoundnessWith F D d oSpec init impl hcard)

end QuotientZeroTest
