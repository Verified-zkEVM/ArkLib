/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.RoundExecution
public import ArkLib.Data.Probability.Instances

/-!
# Knowledge security of a product-sumcheck round

The pre-challenge state requires the sent polynomial to be the residual sum polynomial.
The post-challenge state requires only the accepted guard and equality at the sampled point.
Commitment functionality fixes the original packed witness before that challenge is drawn.
Distinct degree-two messages collide with probability at most `2 / card C` over a finite
commutative ring with no zero divisors.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck.Round
open OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m) (i : Fin m)

/--
Before sampling, the received polynomial equals the residual polynomial of the committed
witness.
-/
def beforeChallenge (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (g : C⦃≤ 2⦄[X]) (p : P⦃≤ 1⦄[X Fin m]) : Prop :=
  check i stmt g ∧ pc.commitsTo ost p ∧ g = honestMessage multiplier i stmt p

/-- After sampling, the local guard and next residual-sum relation hold. -/
def afterChallenge (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (g : C⦃≤ 2⦄[X]) (c : C) (p : P⦃≤ 1⦄[X Fin m]) : Prop :=
  check i stmt g ∧ ((nextStatement i stmt g c, ost), p) ∈ rel multiplier pc i.succ

/-- Honest polynomial equality reads the accepted Boolean sum back to the input relation. -/
theorem mem_rel_of_beforeChallenge (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (g : C⦃≤ 2⦄[X]) (p : P⦃≤ 1⦄[X Fin m])
    (h : beforeChallenge multiplier pc i stmt ost g p) :
    ((stmt, ost), p) ∈ rel multiplier pc i.castSucc := by
  obtain ⟨hc, hcommit, rfl⟩ := h
  refine ⟨?_, hcommit⟩
  exact hc.symm.trans (roundMessage_sum i (productPoly (multiplier stmt.ctx) p) stmt.challenges)

/-- Fixing the input oracle collection fixes the witness before the random challenge. -/
theorem bad_event_le [NoZeroDivisors C] [Fintype C] [SampleableType C] (hfunctional : pc.Functional)
    (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j) (g : C⦃≤ 2⦄[X]) :
    Pr{let c ← $ᵗ C}[∃ p, ¬ beforeChallenge multiplier pc i stmt ost g p ∧
      afterChallenge multiplier pc i stmt ost g c p] ≤
        (((2 : ℝ≥0) / Fintype.card C : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hlive : ∃ p₀, pc.commitsTo ost p₀ ∧ check i stmt g ∧
      g ≠ honestMessage multiplier i stmt p₀
  · obtain ⟨p₀, hcommit, _, hne⟩ := hlive
    refine (prEvent_mono _ _ _ ?_).trans
      (Probability.prob_degreeLE_eval_eq_le hne)
    rintro c ⟨p, _, _, hsum, hcommit'⟩
    obtain rfl : p = p₀ := hfunctional hcommit' hcommit
    exact hsum.trans (roundMessage_eval i (productPoly (multiplier stmt.ctx) p)
      stmt.challenges c).symm
  · push Not at hlive
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ ?_) zero_le
    rintro c ⟨p, hnot, hc, _, hcommit⟩
    exact hnot ⟨hc, hcommit, hlive p hcommit hc⟩

/-- The original packed polynomial is retained at all three prefixes. -/
abbrev WitMid (_j : Fin 3) : Type := P⦃≤ 1⦄[X Fin m]

/-- No witness replacement is needed at a sumcheck message or at the output. -/
def extractor :
    Extractor.RoundByRound []ₒ (StmtIn := Statement Context C i.castSucc × (∀ j, pc.OStmt j))
      (WitIn := P⦃≤ 1⦄[X Fin m]) (WitOut := P⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec C) (WitMid := WitMid (P := P) (m := m)) where
  extractIn := fun _ w => w
  extractMid _ _ _ p := p
  extractOut _ _ p := p

/-- Knowledge states with message and output extraction obligations. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier (C := C) (Context := Context) pc i).KnowledgeStateFunction init impl
      (rel multiplier pc i.castSucc) (rel multiplier pc i.succ)
      (extractor (C := C) (Context := Context) pc i) where
  toFun
    | ⟨0, _⟩ => fun stmt _ p => (stmt, p) ∈ rel multiplier pc i.castSucc
    | ⟨1, _⟩ => fun stmt tr p => beforeChallenge multiplier pc i stmt.1 stmt.2 (tr 0) p
    | ⟨2, _⟩ => fun stmt tr p => afterChallenge multiplier pc i stmt.1 stmt.2 (tr 0) (tr 1) p
  toFun_empty _ _ h := h
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr g p h => mem_rel_of_beforeChallenge multiplier pc i stmt.1 stmt.2
      g p h
    | ⟨1, _⟩ => fun hdir => nomatch hdir
  toFun_full stmt tr p h :=
    check_and_mem_of_prEvent_pos pc i init impl stmt.1 stmt.2 tr p (rel multiplier pc i.succ) h

/-- The scalar challenge carries the degree-two collision bound. -/
def rbrError [Fintype C] (_j : (pSpec C).ChallengeIdx) : ℝ≥0 :=
  2 / Fintype.card C

/-- Round-by-round knowledge soundness at every fixed transcript prefix, with the round
extractor. -/
theorem rbrKnowledgeSoundnessWith [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (rel multiplier pc i.castSucc) (rel multiplier pc i.succ) (verifier pc i).toVerifier
      (WitMid (P := P) (m := m)) (extractor (C := C) (Context := Context) pc i)
      (knowledgeStateFunction multiplier pc i init impl) (rbrError (C := C)) := by
  classical
  refine Verifier.rbrKnowledgeSoundnessWith_of_two_message rfl rfl _ _
    fun stmt tr => ?_
  exact bad_event_le multiplier pc i hfunctional stmt.1 stmt.2
    (tr ⟨0, by change 0 < 1; decide⟩)

end RingSwitching.Packing.ProductSumcheck.Round
