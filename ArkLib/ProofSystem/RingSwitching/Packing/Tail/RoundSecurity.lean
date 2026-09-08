/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.RoundExecution
import ArkLib.ProofSystem.RingSwitching.Packing.Batching

/-!
# Fixed-prefix knowledge security of a product-sumcheck round

The pre-challenge state requires the sent polynomial to be the residual sum polynomial.
The post-challenge state requires only the accepted guard and equality at the sampled point.
Commitment functionality fixes the original packed witness before that challenge is drawn.
Distinct degree-two messages collide with probability at most 2/card(C) over a finite domain.
-/

noncomputable section
namespace RingSwitching.Packing.Tail.Round
open OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m) (i : Fin m)

private theorem message_natDegree (g : C⦃≤ 2⦄[X]) : g.val.natDegree ≤ 2 :=
  Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp g.property)

private theorem message_coefficients_injective :
    Function.Injective (fun g : C⦃≤ 2⦄[X] => fun k : Fin 3 => g.val.coeff k) := by
  intro g h heq
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  by_cases hn : n < 3
  · exact congrFun heq ⟨n, hn⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := message_natDegree g; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by have := message_natDegree h; omega)]

private theorem message_eval (g : C⦃≤ 2⦄[X]) (c : C) :
    g.val.eval c = ∑ k : Fin 3, c ^ (k : ℕ) * g.val.coeff k := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by have := message_natDegree g; omega)]
  rw [Fin.sum_univ_eq_sum_range (fun n => c ^ n * g.val.coeff n) 3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The genuine degree-two root bound for distinct clear round messages. -/
theorem message_collision_le [IsDomain C] [Fintype C] (g h : C⦃≤ 2⦄[X]) (hne : g ≠ h) :
    Pr_{ let c ←$ᵖ C }[g.val.eval c = h.val.eval c] ≤
      (((2 : ℝ≥0) / Fintype.card C : ℝ≥0) : ℝ≥0∞) := by
  have hcoeff : (fun k : Fin 3 => g.val.coeff k) ≠ fun k : Fin 3 => h.val.coeff k :=
    fun heq => hne (message_coefficients_injective heq)
  have hb := (BatchingStrategy.gammaPowers C 3).separates
    (fun k => g.val.coeff k) (fun k => h.val.coeff k) hcoeff
  simpa only [BatchingStrategy.gammaPowers, ← message_eval, Nat.reduceSub, Nat.cast_ofNat] using hb

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
theorem readback (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (g : C⦃≤ 2⦄[X]) (p : P⦃≤ 1⦄[X Fin m])
    (h : beforeChallenge multiplier pc i stmt ost g p) :
    ((stmt, ost), p) ∈ rel multiplier pc i.castSucc := by
  obtain ⟨hc, hcommit, rfl⟩ := h
  refine ⟨?_, hcommit⟩
  exact hc.symm.trans (roundMessage_sum i (productPoly (multiplier stmt.ctx) p) stmt.challenges)

/-- Fixing the input oracle collection fixes the witness before the random challenge. -/
theorem bad_event_le [IsDomain C] [Fintype C] (hfunctional : pc.Functional)
    (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j) (g : C⦃≤ 2⦄[X]) :
    Pr_{ let c ←$ᵖ C }[∃ p, ¬ beforeChallenge multiplier pc i stmt ost g p ∧
      afterChallenge multiplier pc i stmt ost g c p] ≤
        (((2 : ℝ≥0) / Fintype.card C : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hlive : ∃ p₀, pc.commitsTo ost p₀ ∧ check i stmt g ∧
      g ≠ honestMessage multiplier i stmt p₀
  · obtain ⟨p₀, hcommit, _, hne⟩ := hlive
    refine (Pr_le_Pr_of_implies _ _ _ ?_).trans
      (message_collision_le g (honestMessage multiplier i stmt p₀) hne)
    rintro c ⟨p, _, _, hsum, hcommit'⟩
    obtain rfl : p = p₀ := hfunctional hcommit' hcommit
    exact hsum.trans (roundMessage_eval i (productPoly (multiplier stmt.ctx) p)
      stmt.challenges c).symm
  · push Not at hlive
    refine le_of_eq_of_le (prob_eq_zero_of_forall_not _ _ ?_) zero_le
    rintro c ⟨p, hnot, hc, _, hcommit⟩
    exact hnot ⟨hc, hcommit, hlive p hcommit hc⟩

/-- The original packed polynomial is retained at all three prefixes. -/
abbrev WitMid (_j : Fin 3) : Type := P⦃≤ 1⦄[X Fin m]

/-- No witness replacement is needed at a sumcheck message or at the output. -/
def extractor :
    Extractor.RoundByRound []ₒ (StmtIn := Statement Context C i.castSucc × (∀ j, pc.OStmt j))
      (WitIn := P⦃≤ 1⦄[X Fin m]) (WitOut := P⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec C) (WitMid := WitMid (P := P) (m := m)) where
  eqIn := rfl
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
  toFun_empty _ _ := Iff.rfl
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr g p h => readback multiplier pc i stmt.1 stmt.2 g p h
    | ⟨1, _⟩ => fun hdir => nomatch hdir
  toFun_full stmt tr p h :=
    positive_output pc i init impl stmt.1 stmt.2 tr p (rel multiplier pc i.succ) h

/-- The scalar challenge carries the degree-two collision bound. -/
def rbrError [Fintype C] (_j : (pSpec C).ChallengeIdx) : ℝ≥0 :=
  2 / Fintype.card C

/-- Worst-case knowledge soundness at every fixed transcript prefix, with the round extractor. -/
theorem rbrKnowledgeSoundnessWorstCaseWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel multiplier pc i.castSucc) (rel multiplier pc i.succ) (verifier pc i).toVerifier
      (WitMid (P := P) (m := m)) (extractor (C := C) (Context := Context) pc i)
      (knowledgeStateFunction multiplier pc i init impl) (rbrError (C := C)) := by
  intro stmt j tr
  rcases j with ⟨j, hdir⟩
  fin_cases j
  · contradiction
  · change Transcript (1 : Fin 3) (pSpec C) at tr
    let : SampleableType C := SampleableType.ofFintype C
    change Pr[ fun c => ∃ p,
      ¬ beforeChallenge multiplier pc i stmt.1 stmt.2 (tr ⟨0, by decide⟩) p ∧
        afterChallenge multiplier pc i stmt.1 stmt.2 (tr ⟨0, by decide⟩) c p |
      $ᵗ C] ≤ (((2 : ℝ≥0) / Fintype.card C : ℝ≥0) : ℝ≥0∞)
    rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
    exact bad_event_le multiplier pc i hfunctional stmt.1 stmt.2 (tr ⟨0, by decide⟩)

end RingSwitching.Packing.Tail.Round
