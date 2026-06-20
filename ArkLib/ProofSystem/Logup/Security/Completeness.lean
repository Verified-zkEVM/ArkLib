import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Completeness

Completeness statements for Protocol 2 of Haböck's LogUp lookup argument (Cryptology ePrint
Archive, Paper 2022/1530, <https://eprint.iacr.org/2022/1530>).
-/

open scoped NNReal

namespace Logup

section OuterAlgebra

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- For honest helpers (`hₖ = ∑ᵢ mᵢ/φᵢ`) the domain-identity term vanishes pointwise, away from
poles (`φᵢ ≠ 0`). -/
theorem domainIdentityTerm_eq_zero (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (k : Fin K) (u : Hypercube n)
    (hh : evalOnHypercube (helpers k) u = helperValue groups oStmt mult x k u)
    (hφ : ∀ i ∈ groups k, termPhi oStmt x i u ≠ 0) :
    domainIdentityTerm groups oStmt mult helpers x k u = 0 := by
  rw [domainIdentityTerm, denominatorProduct, hh, helperValue, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.mul_prod_erase _ _ hi]
  field_simp [hφ i hi]

/-- The honest log-derivative identity (heart of LogUp): with the normalized multiplicity, the table
side equals the column side. Needs every column value to occur in the table (`hcols`) and the table
counts used by nonzero lookup multiplicities to be nonzero in `F` (`hchar`, from `charLarge`).
Holds even at poles, since `x/0 = 0`. -/
theorem honest_multiplicity_identity (oStmt : ∀ i, OStmtIn F n M i) (x : F)
    (hcols : ∀ j : Fin M, ∀ u : Hypercube n, ∃ v : Hypercube n,
      evalOnHypercube (columnOracle oStmt j) u = evalOnHypercube (tableOracle oStmt) v)
    (hchar : ∀ a : F, lookupMultiplicityCount oStmt a ≠ 0 →
      (tableMultiplicityCount oStmt a : F) ≠ 0) :
    (∑ u : Hypercube n,
        evalOnHypercube (honestMultiplicity oStmt) u / (x + evalOnHypercube (tableOracle oStmt) u))
      = ∑ j : Fin M, ∑ u : Hypercube n,
          (1 : F) / (x + evalOnHypercube (columnOracle oStmt j) u) := by
  classical
  -- per-value cancellation
  have key : ∀ a : F,
      tableMultiplicityCount oStmt a •
          ((lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F) / (x + a))
        = lookupMultiplicityCount oStmt a • ((1 : F) / (x + a)) := by
    intro a
    by_cases hT : tableMultiplicityCount oStmt a = 0
    · have hL : lookupMultiplicityCount oStmt a = 0 := by
        rw [lookupMultiplicityCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨j, u⟩ - hja
        obtain ⟨v, hv⟩ := hcols j u
        have hav : evalOnHypercube (tableOracle oStmt) v = a := hv.symm.trans hja
        rw [tableMultiplicityCount] at hT
        exact absurd hT (Finset.card_ne_zero_of_mem
          (show v ∈ Finset.univ.filter
              fun w => evalOnHypercube (tableOracle oStmt) w = a by simp [hav]))
      simp [hT, hL]
    · rw [nsmul_eq_mul, nsmul_eq_mul]
      by_cases hL : lookupMultiplicityCount oStmt a = 0
      · simp [hL]
      · have hTF := hchar a hL
        field_simp
  -- group the table side by table value
  have hLHS :
      (∑ u : Hypercube n, evalOnHypercube (honestMultiplicity oStmt) u /
          (x + evalOnHypercube (tableOracle oStmt) u))
        = ∑ a : F, tableMultiplicityCount oStmt a •
            ((lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F)
              / (x + a)) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Hypercube n))
        (fun u => evalOnHypercube (tableOracle oStmt) u)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h : ∀ u ∈ Finset.univ.filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
        evalOnHypercube (honestMultiplicity oStmt) u /
            (x + evalOnHypercube (tableOracle oStmt) u)
          = (lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F)
              / (x + a) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      change (lookupMultiplicityCount oStmt (evalOnHypercube (tableOracle oStmt) u) : F) /
            (tableMultiplicityCount oStmt (evalOnHypercube (tableOracle oStmt) u) : F) /
            (x + evalOnHypercube (tableOracle oStmt) u)
          = (lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F) / (x + a)
      rw [hu]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  -- group the column side by column value
  have hRHS :
      (∑ j : Fin M, ∑ u : Hypercube n, (1 : F) /
          (x + evalOnHypercube (columnOracle oStmt j) u))
        = ∑ a : F, lookupMultiplicityCount oStmt a • ((1 : F) / (x + a)) := by
    rw [← Finset.sum_product', Finset.univ_product_univ,
      ← Finset.sum_fiberwise (Finset.univ : Finset (Fin M × Hypercube n))
        (fun p => evalOnHypercube (columnOracle oStmt p.1) p.2)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h : ∀ p ∈ Finset.univ.filter
          (fun p : Fin M × Hypercube n =>
            evalOnHypercube (columnOracle oStmt p.1) p.2 = a),
        (1 : F) / (x + evalOnHypercube (columnOracle oStmt p.1) p.2) = (1 : F) / (x + a) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [hp]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl (fun a _ => key a)

omit [Fintype F] [DecidableEq F] in
/-- The canonical groups partition the term indices `{0,…,M}`, so summing group-by-group equals
summing over all terms. -/
theorem sum_canonicalGroups (params : ProtocolParams M) (g : TermIdx M → F) :
    (∑ k : Fin params.numGroups, ∑ i ∈ canonicalGroups params k, g i) = ∑ i : TermIdx M, g i := by
  classical
  have hℓ := params.sumSize_pos
  have hidx : ∀ i : TermIdx M, i.val / params.sumSize < params.numGroups := by
    intro i
    have hiM : i.val ≤ M := Nat.lt_succ_iff.mp i.isLt
    have hle : i.val / params.sumSize ≤ M / params.sumSize := Nat.div_le_div_right hiM
    rw [ProtocolParams.numGroups, Nat.add_div_right _ hℓ]
    omega
  rw [← Finset.sum_fiberwise Finset.univ
      (fun i : TermIdx M => (⟨i.val / params.sumSize, hidx i⟩ : Fin params.numGroups)) g]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  ext i
  simp only [canonicalGroups, ProtocolParams.group, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : k.val ≤ i.val / params.sumSize := (Nat.le_div_iff_mul_le hℓ).mpr h1
    have hb : i.val / params.sumSize < k.val + 1 := (Nat.div_lt_iff_lt_mul hℓ).mpr h2
    omega
  · intro h
    exact ⟨(Nat.le_div_iff_mul_le hℓ).mp (by omega), (Nat.div_lt_iff_lt_mul hℓ).mp (by omega)⟩

/-- The honest batched claim sums to zero: `∑ᵤ Q(u) = 0` for the honest multiplicity and helpers,
away from poles. Combines `domainIdentityTerm_eq_zero`, `sum_canonicalGroups`, and
`honest_multiplicity_identity`. -/
theorem logupOuterClaim_zero (params : ProtocolParams M) (oStmtIn : ∀ i, OStmtIn F n M i)
    (x : F) (z : Fin n → F) (lam : Fin params.numGroups → F)
    (hcols : ∀ j : Fin M, ∀ u : Hypercube n, ∃ v : Hypercube n,
      evalOnHypercube (columnOracle oStmtIn j) u = evalOnHypercube (tableOracle oStmtIn) v)
    (hchar : ∀ a : F, lookupMultiplicityCount oStmtIn a ≠ 0 →
      (tableMultiplicityCount oStmtIn a : F) ≠ 0)
    (hpoles : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmtIn x i u ≠ 0) :
    (∑ u : Hypercube n,
        qOnHypercube (canonicalGroups params) oStmtIn (honestMultiplicity oStmtIn)
          (honestHelpers params oStmtIn x) x z lam u) = 0 := by
  -- honest helpers kill the domain-identity term, leaving `∑ₖ helperValue`
  have hq : ∀ u : Hypercube n,
      qOnHypercube (canonicalGroups params) oStmtIn (honestMultiplicity oStmtIn)
          (honestHelpers params oStmtIn x) x z lam u
        = ∑ k : Fin params.numGroups,
            helperValue (canonicalGroups params) oStmtIn (honestMultiplicity oStmtIn) x k u := by
    intro u
    simp only [qOnHypercube]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [domainIdentityTerm_eq_zero (canonicalGroups params) oStmtIn (honestMultiplicity oStmtIn)
      (honestHelpers params oStmtIn x) x k u rfl (fun i _ => hpoles i u), mul_zero, add_zero]
    rfl
  -- each helper expands to the per-group term sum, which partitions to the full term sum
  have hsum : ∀ u : Hypercube n,
      (∑ k : Fin params.numGroups,
          helperValue (canonicalGroups params) oStmtIn (honestMultiplicity oStmtIn) x k u)
        = ∑ i : TermIdx M,
            termNumerator (honestMultiplicity oStmtIn) i u / termPhi oStmtIn x i u := by
    intro u
    simp only [helperValue]
    exact sum_canonicalGroups params
      (fun i => termNumerator (honestMultiplicity oStmtIn) i u / termPhi oStmtIn x i u)
  -- split the term sum into the table term and the column terms
  have hterm : ∀ u : Hypercube n,
      (∑ i : TermIdx M, termNumerator (honestMultiplicity oStmtIn) i u / termPhi oStmtIn x i u)
        = evalOnHypercube (honestMultiplicity oStmtIn) u /
              (x + evalOnHypercube (tableOracle oStmtIn) u)
          + ∑ j : Fin M, (-1 : F) / (x + evalOnHypercube (columnOracle oStmtIn j) u) := by
    intro u
    have hcol : ∀ j : Fin M,
        termNumerator (honestMultiplicity oStmtIn) (Fin.succ j) u /
            termPhi oStmtIn x (Fin.succ j) u
          = (-1 : F) / (x + evalOnHypercube (columnOracle oStmtIn j) u) := by
      intro j
      have htt : termToInput (Fin.succ j : TermIdx M) = InputOracleIdx.column j := by
        simp only [termToInput, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte]
        congr 1
      simp only [termNumerator, termPhi, htt, numerator, phi]
    rw [Fin.sum_univ_succ]
    refine congrArg₂ (· + ·) rfl ?_
    exact Finset.sum_congr rfl (fun j _ => hcol j)
  simp_rw [hq, hsum, hterm]
  rw [Finset.sum_add_distrib, honest_multiplicity_identity oStmtIn x hcols hchar,
    Finset.sum_comm (f := fun u j => (-1 : F) / (x + evalOnHypercube (columnOracle oStmtIn j) u)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun u _ => by ring)

/-- The table poles `{x : ∃ u, x + t(u) = 0} = {-t(u) : u ∈ H}` number at most `|H|`. This is the
counting fact behind the pole-sampling completeness error. -/
theorem pole_card_le (oStmt : ∀ i, OStmtIn F n M i) :
    (Finset.univ.filter (fun x : F => ∃ u : Hypercube n,
        x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ Fintype.card (Hypercube n) := by
  classical
  calc (Finset.univ.filter (fun x : F => ∃ u : Hypercube n,
          x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ (Finset.univ.image
          (fun u : Hypercube n => -evalOnHypercube (tableOracle oStmt) u)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨u, hu⟩ := hx
        exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, (eq_neg_of_add_eq_zero_left hu).symm⟩
    _ ≤ Fintype.card (Hypercube n) := by
        rw [← Finset.card_univ]; exact Finset.card_image_le

omit [Fintype F] [DecidableEq F] in
/-- A `LagrangeOracle` query at a Boolean-hypercube point returns the oracle's value there. -/
theorem lagrange_answer_hypercube (oracle : MultilinearOracle F n)
    (a : Hypercube n) :
    OracleInterface.answer oracle (a : Fin n → F) = evalOnHypercube oracle a :=
  lagrangeOracleEval_hypercube oracle a

end OuterAlgebra

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instOracleCompLawfulMonad' {τ : Type} (spec : OracleSpec τ) :
    LawfulMonad (OracleComp spec) :=
  OracleComp.instLawfulMonad spec

/-- Completeness error from the current `x`-sampling model: the verifier samples `x` from all of
`F`. Following Remark 3 of the LogUp paper, table-pole challenges are treated as bad inputs for
the honest handoff rather than rejected by an exponential verifier scan. -/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Hypercube n) : ℝ≥0) / (Fintype.card F)

/-- `simulateQ` distributes over a `forIn` loop in `OptionT (OracleComp spec)`: the OptionT
sibling of `simulateQ_list_forIn`, built on `simulateQ_optionT_bind`. -/
private theorem simulateQ_optionT_list_forIn {ι : Type} {spec : OracleSpec ι}
    {nn : Type → Type*} [Monad nn] [LawfulMonad nn] (impl : QueryImpl spec nn)
    {α β : Type} (xs : List α) (init : β)
    (f : α → β → OptionT (OracleComp spec) (ForInStep β)) :
    simulateQ impl (forIn xs init f : OptionT (OracleComp spec) β)
      = (forIn xs init (fun a b => simulateQ impl (f a b)) : OptionT nn β) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind]
    congr 1
    funext step
    cases step with
    | done b => rfl
    | yield b => exact ih b

/-- `simulateQ` leaves a `guard` unchanged: `guard` has no queries, so its simulation is itself. -/
private theorem simulateQ_optionT_guard {ι : Type} {spec : OracleSpec ι}
    {nn : Type → Type*} [Monad nn] [LawfulMonad nn] (impl : QueryImpl spec nn)
    (P : Prop) [Decidable P] :
    simulateQ impl (guard P : OptionT (OracleComp spec) Unit) = (guard P : OptionT nn Unit) := by
  change simulateQ impl (if P then pure () else failure : OptionT (OracleComp spec) Unit)
    = (if P then pure () else failure : OptionT nn Unit)
  by_cases hP : P
  · rw [if_pos hP, if_pos hP]; rfl
  · rw [if_neg hP, if_neg hP]; rfl

/-- A list of abort-on-`P` checks can only return successfully when every check avoided `P`. -/
private theorem guarded_foldlM_succeeds {ι : Type} {spec : OracleSpec ι}
    {β γ : Type} (L : List β) (P : β → Prop) [DecidablePred P] (r : γ) :
    r ∈ support (List.foldlM (m := OptionT (OracleComp spec))
        (fun (_ : γ) (u : β) =>
          if P u then failure else pure r) r L) →
      ∀ u ∈ L, ¬ P u := by
  induction L with
  | nil => intro _ u hu; simp at hu
  | cons a L' ih =>
      intro h u hu
      rw [List.foldlM_cons] at h
      by_cases hPa : P a
      · simp [hPa] at h
      · simp only [hPa, ↓reduceIte, pure_bind, OptionT.mem_support_iff] at h
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hPa
        · exact ih h u hu'

private theorem support_bind_exists {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α β : Type} (x : m α) (f : α → m β) {y : β}
    (hy : y ∈ support (x >>= f)) : ∃ a, a ∈ support x ∧ y ∈ support (f a) := by
  simpa [mem_support_bind_iff] using hy

private theorem support_pure_eq {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α : Type} {x y : α} (h : y ∈ support (pure x : m α)) : y = x := by
  simpa [mem_support_pure_iff] using h

private theorem mem_support_of_mem_support_liftComp {ι τ α : Type} {spec : OracleSpec ι}
    {superSpec : OracleSpec τ} [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (x : α) :
    x ∈ support (oa.liftComp superSpec) → x ∈ support oa := by
  intro hx
  induction oa using OracleComp.inductionOn generalizing x with
  | pure y =>
      simpa using hx
  | query_bind q oa ih =>
      rw [OracleComp.liftComp_bind, mem_support_bind_iff] at hx
      rw [mem_support_bind_iff]
      obtain ⟨u, _hu, hx⟩ := hx
      exact ⟨u, OracleComp.mem_support_query q u, ih u x hx⟩

private theorem support_simulateQ_run_fst_subset {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM] {σ α : Type}
    (impl : QueryImpl spec (StateT σ m)) {oa : OracleComp spec α} {s s' : σ} {y : α}
    (h : (y, s') ∈ support ((simulateQ impl oa).run s)) :
    y ∈ support oa :=
  OracleComp.support_simulateQ_run'_subset impl oa s (by
    rw [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨(y, s'), h, rfl⟩)

set_option linter.unusedSectionVars false in
open OracleComp OracleSpec in
omit [SampleableType F] in
/-- Simulating the scan-free outer verifier against the honest oracles leaves only the public
challenge data packaged as the outer statement. -/
theorem outerVerify_simulateQ_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (messages : ∀ i, (outerPSpec F n params).Message i)
    (challenges : ∀ i, (outerPSpec F n params).Challenge i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((outerVerifier oSpec F n M params).verify stmt challenges)
      = (do
          let x : F := challenges (outerChallengeXIdx F n M params)
          let batch : BatchingChallenge F n params.numGroups :=
            challenges (outerChallengeBatchIdx F n M params)
          pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
        : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params)) := by
  simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx]
  rfl

/-- Four-round unfolding of `Fin.induction` (the analog of `Fin.induction_two`), for the outer
LogUp prover's `runToRound`. -/
private theorem Fin.induction_four {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
    Fin.induction (motive := motive) zero succ (Fin.last 4)
      = succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

/-- Completeness of the outer LogUp phase: the honest outer prover reaches the zero-sum handoff
relation, except with the pole-sampling error. -/
theorem logup_outer_completeness [Inhabited F] :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (logupMidRelation F n M params) (logupCompletenessError F n) := by
  unfold OracleReduction.completeness Reduction.completeness
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [outerOracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, Prover.runToRound, outerProver, Fin.induction_four,
    Prover.processRound, outerPSpec]
  repeat' split <;> rename_i hd <;> first | exact absurd hd (by decide) | skip
  simp only [ProtocolSpec.getChallenge, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, OracleComp.liftComp_pure, bind_pure_comp, map_pure,
    QueryImpl.addLift_def]
  refine ge_trans (probEvent_mono
    (p := fun out => ∀ u : Hypercube n,
      out.2.1.xChallenge + evalOnHypercube (tableOracle oStmt) u ≠ 0) ?goodOutputs) ?goodProb
  · -- every output with a non-pole outer challenge satisfies the success predicate
    intro out hout hGood
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, -, hout⟩ := hout
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hout
    obtain ⟨⟨_, s'⟩, hout, rfl⟩ := hout
    erw [simulateQ_bind, StateT.run_bind] at hout
    rw [mem_support_bind_iff] at hout
    obtain ⟨⟨pres, s2⟩, hpres, hver⟩ := hout
    simp only [OptionT.lift, OptionT.mk] at hpres
    erw [simulateQ_map, StateT.run_map] at hpres
    rw [support_map, Set.mem_image] at hpres
    obtain ⟨⟨pval, sp⟩, hpval, hpeq⟩ := hpres
    erw [simulateQ_map, StateT.run_map] at hpval
    rw [support_map, Set.mem_image] at hpval
    obtain ⟨⟨a, sa⟩, ha, hpval_eq⟩ := hpval
    erw [simulateQ_bind, StateT.run_bind] at ha
    rw [mem_support_bind_iff] at ha
    obtain ⟨⟨b, sb⟩, hb, ha3⟩ := ha
    erw [simulateQ_map, StateT.run_map] at ha3
    rw [support_map, Set.mem_image] at ha3
    obtain ⟨⟨zlam, szlam⟩, hzlam, ha3eq⟩ := ha3
    -- round 1: peel `hb` to reach the `x` challenge query
    erw [simulateQ_map, StateT.run_map] at hb
    rw [support_map, Set.mem_image] at hb
    obtain ⟨⟨c, sc⟩, hc, hbeq⟩ := hb
    erw [simulateQ_bind, StateT.run_bind] at hc
    rw [mem_support_bind_iff] at hc
    obtain ⟨⟨d, sd⟩, hd, hc2⟩ := hc
    erw [simulateQ_map, StateT.run_map] at hc2
    rw [support_map, Set.mem_image] at hc2
    obtain ⟨⟨xval, sx⟩, hx, hc2eq⟩ := hc2
    -- round 0 is deterministic (a pure `honestMultiplicity` send)
    erw [simulateQ_map, StateT.run_map] at hd
    rw [support_map, Set.mem_image] at hd
    obtain ⟨⟨e, se⟩, he, hdeq⟩ := hd
    erw [simulateQ_pure, StateT.run_pure] at he
    rw [support_pure, Set.mem_singleton_iff] at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    -- substitute the prover-side equation chain to make `pval`/`pres` concrete
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc2eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha3eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpval_eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpeq
    change F at xval
    change BatchingChallenge F n params.numGroups at zlam
    -- peel the verifier (match on `some pval` resolves; then its bind)
    simp only at hver
    erw [simulateQ_bind, StateT.run_bind] at hver
    rw [mem_support_bind_iff] at hver
    obtain ⟨⟨vstmt, sv⟩, hverify, hvout⟩ := hver
    -- The scan-free verifier packages the sampled challenges; the non-pole assumption comes from
    -- the good-challenge event above.
    simp only [OracleVerifier.toVerifier] at hverify
    rw [outerVerify_simulateQ_eq] at hverify
    -- The verifier accepted: `vstmt = some _` (the `none` branch of `hvout` yields `none ≠ some`).
    rcases vstmt with _ | vAccepted
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hvout
      simp at hvout
    · rcases vAccepted with _ | vAccepted
      · simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages,
          Nat.reduceAdd, Fin.vcons_fin_zero, BatchingChallenge] at hvout
        have hvoutBase := support_simulateQ_run_fst_subset
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params))) hvout
        letI :
            (i : (outerPSpec F n params).ChallengeIdx) →
              OracleInterface ((outerPSpec F n params).Challenge i) :=
          ProtocolSpec.challengeOracleInterface
        letI : LawfulMonad (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) :=
          OracleComp.instLawfulMonad _
        change some out ∈ support
          ((_ <$>
            (failure :
              OptionT (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) _)).run)
          at hvoutBase
        rw [OptionT.run_map, OptionT.run_failure] at hvoutBase
        rw [support_map, support_pure, Set.mem_image] at hvoutBase
        obtain ⟨a, ha, hmap⟩ := hvoutBase
        rw [Set.mem_singleton_iff] at ha
        subst a
        simp at hmap
      · -- The honest output: `out` pairs the prover view with the verifier's accepted statement.
        rw [show (some (some vAccepted), sv).1 = some (some vAccepted) by rfl] at hvout
        simp only [Option.getM_some, map_pure] at hvout
        obtain ⟨rfl, rfl⟩ := hvout
        simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages] at hverify
        have hverifyBase := support_simulateQ_run_fst_subset
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params))) hverify
        letI :
            (i : (outerPSpec F n params).ChallengeIdx) →
              OracleInterface ((outerPSpec F n params).Challenge i) :=
          ProtocolSpec.challengeOracleInterface
        letI : LawfulMonad (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) :=
          OracleComp.instLawfulMonad _
        have hverifyEq := support_pure_eq
          (m := OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) hverifyBase
        simp only [Option.some.injEq] at hverifyEq
        subst vAccepted
        have hNoTablePoles :
            ∀ u : Hypercube n, xval + evalOnHypercube (tableOracle oStmt) u ≠ 0 := by
          intro u
          simpa [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
            ProtocolSpec.FullTranscript.challenges, ProtocolSpec.Transcript.concat, Fin.snoc]
            using hGood u
        have hcols : ∀ j : Fin M, ∀ u : Hypercube n, ∃ v : Hypercube n,
            evalOnHypercube (columnOracle oStmt j) u =
              evalOnHypercube (tableOracle oStmt) v := by
          simpa [inputRelation] using hIn
        have hchar : ∀ a : F, lookupMultiplicityCount oStmt a ≠ 0 →
            (tableMultiplicityCount oStmt a : F) ≠ 0 := by
          intro a hlookup
          classical
          have hlookupCard :
              ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun ix =>
                evalOnHypercube (columnOracle oStmt ix.1) ix.2 = a).card ≠ 0 := by
            simpa [lookupMultiplicityCount] using hlookup
          obtain ⟨⟨j, u⟩, hju⟩ := Finset.card_ne_zero.mp hlookupCard
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hju
          obtain ⟨v, hv⟩ := hcols j u
          have hvTable : evalOnHypercube (tableOracle oStmt) v = a := hv.symm.trans hju
          have htablePos : 0 < tableMultiplicityCount oStmt a := by
            rw [tableMultiplicityCount, Finset.card_pos]
            exact ⟨v, by simp [hvTable]⟩
          have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
          have htable_le_card :
              tableMultiplicityCount oStmt a ≤ Fintype.card (Hypercube n) := by
            rw [tableMultiplicityCount, ← Finset.card_univ]
            exact Finset.card_filter_le _ _
          have hcard_hypercube : Fintype.card (Hypercube n) = 2 ^ n := by
            simp [Hypercube]
          have hpow_le : 2 ^ n ≤ M * 2 ^ n := by
            have hMone : 1 ≤ M := Nat.succ_le_of_lt hMpos
            nth_rewrite 1 [← Nat.one_mul (2 ^ n)]
            exact Nat.mul_le_mul_right (2 ^ n) hMone
          have htable_lt_char : tableMultiplicityCount oStmt a < ringChar F := by
            calc
              tableMultiplicityCount oStmt a ≤ Fintype.card (Hypercube n) := htable_le_card
              _ = 2 ^ n := hcard_hypercube
              _ ≤ M * 2 ^ n := hpow_le
              _ < ringChar F := stmt.charLarge
          intro hzero
          have hdvd : ringChar F ∣ tableMultiplicityCount oStmt a :=
            (ringChar.spec F (tableMultiplicityCount oStmt a)).1 hzero
          exact (Nat.not_dvd_of_pos_of_lt htablePos htable_lt_char) hdvd
        have hpoles : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmt xval i u ≠ 0 := by
          intro i u
          cases hti : termToInput i with
          | table =>
              rw [termPhi, hti]
              simpa [phi, tableOracle] using hNoTablePoles u
          | column j =>
              obtain ⟨v, hv⟩ := hcols j u
              rw [termPhi, hti, phi]
              simpa [hv] using hNoTablePoles v
        let stmtAfter : StmtAfterOuter F n M params :=
          { xChallenge := xval, zChallenge := zlam.1, batchingScalars := zlam.2 }
        let oStmtAfter : ∀ i, OStmtAfterOuter F n M params i :=
          fun
            | .input i => oStmt i
            | .multiplicity => honestMultiplicity oStmt
            | .helpers => honestHelpers params oStmt xval
        have hmid : ((stmtAfter, oStmtAfter), ()) ∈ logupMidRelation F n M params := by
          simpa [stmtAfter, oStmtAfter, logupMidRelation, logupOuterSumcheckClaim] using
            logupOuterClaim_zero (F := F) (n := n) (M := M) params oStmt xval
              zlam.1 zlam.2 hcols hchar hpoles
        simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
          ProtocolSpec.FullTranscript.challenges, ProtocolSpec.FullTranscript.messages,
          ProtocolSpec.Transcript.concat, Fin.snoc]
        constructor
        · convert hmid using 2
          apply Prod.ext
          · rfl
          · funext i
            cases i <;> simp [oStmtAfter, outerMultiplicityMessageIdx,
              outerHelpersMessageIdx]
        · funext i
          cases i <;> simp [outerMultiplicityMessageIdx,
            outerHelpersMessageIdx]
  · -- pole-probability bound `Pr[x avoids all table poles] ≥ 1 - |H|/|F|`
    sorry


/-- Lens-completeness for the LogUp→Sumcheck lens: `proj` builds the zero-sum instance, and `lift`
retains the outer LogUp data together with sumcheck's final valid point claim. -/
instance logupSumcheckLensComplete :
    (logupSumcheckContextLens F n M params).toContext.IsComplete
      (logupMidRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0)
      (logupAfterSumcheckRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n))
      ((logupConcreteSumcheckOracleReduction oSpec F n M params).toReduction.compatContext
        (logupSumcheckContextLens F n M params).toContext) where
  proj_complete := by
    rintro ⟨stmt, oStmt⟩ ⟨⟩ h
    exact logupSumcheckRelationInput_of_zero F n M params h
  lift_complete := by
    intro outerStmt outerWit innerStmtOut innerWitOut hCompat _ hRelOut
    have hOStmt :
        innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
      -- The generic sumcheck prover preserves its polynomial oracle statement through every round.
      -- A small support-preservation lemma for `Sumcheck.Spec.oracleReduction` should discharge
      -- this from `hCompat`.
      sorry
    cases innerWitOut
    have hPair :
        (innerStmtOut.1, logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) =
          innerStmtOut := by
      cases innerStmtOut
      simpa using hOStmt.symm
    simpa [logupSumcheckContextLens, logupAfterSumcheckRelation, hPair] using hRelOut

omit [Fintype F] in
/-- Completeness of the embedded sumcheck phase: it carries `logupMidRelation` to the retained
final sumcheck claim with no extra error, by reusing the generic sumcheck's perfect completeness
through the LogUp-to-Sumcheck context lens. -/
theorem logupSumcheckPhaseCompleteness :
    (sumcheckOracleReduction oSpec F n M params).completeness init impl
      (logupMidRelation F n M params) (logupAfterSumcheckRelation F n M params) 0 :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := logupSumcheckContextLens F n M params)
    (lensComplete := logupSumcheckLensComplete oSpec F n M params)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness
      F (logupSumcheckDegree M params) (booleanDomain F) n oSpec)

/-- Completeness of the final LogUp point check: once sumcheck's final claim is valid for the
retained LogUp polynomial, the verifier's oracle queries reconstruct the same value. -/
theorem finalCheckCompleteness :
    (finalCheckOracleReduction oSpec F n M params).completeness init impl
      (logupAfterSumcheckRelation F n M params) outputRelation 0 := by
  sorry

/-- Main ArkLib completeness theorem for LogUp Protocol 2. -/
theorem logup_completeness :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  letI : Inhabited F := ⟨0⟩
  have hOuterSumcheck := OracleReduction.append_completeness.{0, 0, 0, 0}
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    (logup_outer_completeness oSpec F n M params init impl)
    (logupSumcheckPhaseCompleteness oSpec F n M params init impl)
  have hFull := OracleReduction.append_completeness.{0, 0, 0, 0}
    ((outerOracleReduction oSpec F n M params).append
      (sumcheckOracleReduction oSpec F n M params))
    (finalCheckOracleReduction oSpec F n M params)
    hOuterSumcheck
    (finalCheckCompleteness oSpec F n M params init impl)
  simpa only [add_zero] using hFull

end Completeness

end Logup
