import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ProofSystem.Logup.Sumcheck.Security

/-!
# LogUp Completeness

Main completeness statement for the LogUp protocol.

`logupOracleReduction` is `outerOracleReduction ++ₚ sumcheckOracleReduction`, so completeness is
proved compositionally via `append_completeness`: the outer phase reaches `logupMidRelation` (with
the pole-rejection error), the embedded sumcheck phase carries it to `outputRelation` with no extra
error. The two halves are the remaining obligations.
-/

open scoped NNReal

namespace Logup

section OuterAlgebra

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

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
counts to be nonzero in `F` (`hchar`, from `charLarge`). Holds even at poles, since `x/0 = 0`. -/
theorem honest_multiplicity_identity (oStmt : ∀ i, OStmtIn F n M i) (x : F)
    (hcols : ∀ j : Fin M, ∀ u : Hypercube n, ∃ v : Hypercube n,
      evalOnHypercube (columnOracle oStmt j) u = evalOnHypercube (tableOracle oStmt) v)
    (hchar : ∀ a : F, tableMultiplicityCount oStmt a ≠ 0 →
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
      have hTF := hchar a hT
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
      show (lookupMultiplicityCount oStmt (evalOnHypercube (tableOracle oStmt) u) : F) /
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
    (hchar : ∀ a : F, tableMultiplicityCount oStmtIn a ≠ 0 →
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

/-- The polynomial `Q` agrees with `qOnHypercube` on the signed hypercube — a structural fact (no
honesty needed), from `logupQPolynomial_eval_signPoint`. -/
theorem logupRowsAgree (params : ProtocolParams M) (hs : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    logupSumcheckPolynomialRowsAgree F n M params stmt oStmt :=
  fun u => logupQPolynomial_eval_signPoint F n M params hs stmt oStmt u

/-- The table poles `{x : ∃ u, x + t(u) = 0} = {-t(u) : u ∈ H}` number at most `|H|`. This is the
counting fact behind the pole-rejection completeness error. -/
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

/-- A `LagrangeOracle` query at a signed-hypercube point returns the oracle's value there. -/
theorem lagrange_answer_signPoint (hs : (-1 : F) ≠ 1) (oracle : MultilinearOracle F n)
    (a : Hypercube n) :
    OracleInterface.answer oracle (signPoint F a) = evalOnHypercube oracle a :=
  lagrangeOracleEval_signPoint F n hs oracle a

end OuterAlgebra

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Completeness error from the current `x`-sampling model: the verifier samples `x` from all of `F`
and rejects table poles, so completeness carries this bad-`x` probability. It would be `0` if `x`
were sampled from the pole complement, as the LogUp protocol intends. -/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Hypercube n) : ℝ≥0) / (Fintype.card F)

/-- `simulateQ` distributes over a `forIn` loop in `OptionT (OracleComp spec)`: the OptionT
sibling of `simulateQ_list_forIn`, built on `simulateQ_optionT_bind`. -/
theorem simulateQ_optionT_list_forIn {ι : Type} {spec : OracleSpec ι}
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

/-- `simulateQ` distributes over `OptionT.map` (the `<$>` form), the OptionT sibling of
`simulateQ_map`. -/
theorem simulateQ_optionT_map {ι : Type} {spec : OracleSpec ι}
    {nn : Type → Type*} [Monad nn] [LawfulMonad nn] (impl : QueryImpl spec nn)
    {α β : Type} (f : α → β) (x : OptionT (OracleComp spec) α) :
    simulateQ impl (f <$> x : OptionT (OracleComp spec) β)
      = (f <$> simulateQ impl x : OptionT nn β) := by
  rw [map_eq_pure_bind, simulateQ_optionT_bind, map_eq_pure_bind]
  rfl

/-- `simulateQ` leaves a `guard` unchanged: `guard` has no queries, so its simulation is itself. -/
theorem simulateQ_optionT_guard {ι : Type} {spec : OracleSpec ι}
    {nn : Type → Type*} [Monad nn] [LawfulMonad nn] (impl : QueryImpl spec nn)
    (P : Prop) [Decidable P] :
    simulateQ impl (guard P : OptionT (OracleComp spec) Unit) = (guard P : OptionT nn Unit) := by
  show simulateQ impl (if P then pure () else failure : OptionT (OracleComp spec) Unit)
    = (if P then pure () else failure : OptionT nn Unit)
  by_cases hP : P
  · rw [if_pos hP, if_pos hP]; rfl
  · rw [if_neg hP, if_neg hP]; rfl

/-- Resolve `simulateQ` over a `bind`-then-`guard` loop step in `OptionT (OracleComp spec)`:
`simulateQ` passes through the bind and leaves the guard on the simulated value. -/
theorem simulateQ_optionT_bind_guard {ι : Type} {spec : OracleSpec ι}
    {nn : Type → Type*} [Monad nn] [LawfulMonad nn] (impl : QueryImpl spec nn)
    {γ : Type} (mx : OptionT (OracleComp spec) γ) (Pf : γ → Prop) [DecidablePred Pf] :
    simulateQ impl ((mx >>=
        fun t => (fun _ => ForInStep.yield PUnit.unit) <$> guard (Pf t)) :
        OptionT (OracleComp spec) (ForInStep PUnit))
      = ((simulateQ impl mx >>=
        fun t => (fun _ => ForInStep.yield PUnit.unit) <$> guard (Pf t)) :
        OptionT nn (ForInStep PUnit)) := by
  rw [simulateQ_optionT_bind]
  congr 1
  funext t
  rw [simulateQ_optionT_map, simulateQ_optionT_guard]

/-- A guarded `forIn` loop in `OptionT (OracleComp spec)` only lands in `support` (succeeds) when
every guard passed. The key fact behind the verifier's pole-rejection check. -/
theorem guarded_forIn_succeeds {ι : Type} {spec : OracleSpec ι}
    {β : Type} (L : List β) (P : β → Prop) [DecidablePred P] (r : PUnit) :
    r ∈ support (forIn L PUnit.unit
        (fun u (_ : PUnit) => (fun _ => ForInStep.yield PUnit.unit) <$>
          (guard (P u) : OptionT (OracleComp spec) PUnit))) →
      ∀ u ∈ L, P u := by
  induction L with
  | nil => intro _ u hu; simp at hu
  | cons a L' ih =>
    intro hr u hu
    rw [List.forIn_cons] at hr
    by_cases hPa : P a
    · simp only [guard, hPa, if_true, map_pure, pure_bind] at hr
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hPa
      · exact ih hr u hu'
    · simp [guard, hPa] at hr

open OracleComp OracleSpec in
/-- Simulating the outer verifier's table queries against the honest oracles `oStmt` turns the
oracle-accessing pole-rejection scan into a query-free `evalOnHypercube` loop. This is the LogUp
analog of `Sumcheck.Spec.SingleRound.oracleVerifier_eq_verifier`: it does the `simOracle2` peel
once, so the completeness proof never has to. -/
theorem outerVerify_simulateQ_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (messages : ∀ i, (outerPSpec F n params).Message i)
    (challenges : ∀ i, (outerPSpec F n params).Challenge i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((outerVerifier oSpec F n M params).verify stmt challenges)
      = (do
          let x : F := challenges (outerChallengeXIdx F n M params)
          for u in (Finset.univ : Finset (Hypercube n)).toList do
            guard (x + evalOnHypercube (tableOracle oStmt) u ≠ 0)
          let batch : BatchingChallenge F n params.numGroups :=
            challenges (outerChallengeBatchIdx F n M params)
          pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
        : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params)) := by
  classical
  -- Per iteration, simulating the lifted table query against `oStmt` returns the honest table
  -- value. Proved standalone (the multi-lemma `SubSpec`/`simOracle0` routing chains here but not
  -- under the `forIn` binder); as a single rewrite rule it then fires under the binder below.
  have hquery : ∀ a : Hypercube n,
      simulateQ (QueryImpl.liftTarget (OracleComp oSpec) (QueryImpl.id oSpec) +
          QueryImpl.liftTarget (OracleComp oSpec)
            ((OracleInterface.simOracle0 (OStmtIn F n M) oStmt).add
              (OracleInterface.simOracle0 (outerPSpec F n params).Message messages)))
          (liftM (OracleSpec.query (spec := [OStmtIn F n M]ₒ)
            ⟨InputOracleIdx.table, signPoint F a⟩))
        = (pure (evalOnHypercube (tableOracle oStmt) a) : OracleComp oSpec F) := by
    intro a
    rw [← lagrange_answer_signPoint Fact.out (tableOracle oStmt) a]
    rfl
  simp only [outerVerifier, OracleInterface.simOracle2, QueryImpl.addLift_def,
    simulateQ_optionT_bind, simulateQ_optionT_list_forIn, simulateQ_optionT_map,
    simulateQ_optionT_guard, simulateQ_optionT_lift, simulateQ_pure, simulateQ_map,
    QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    QueryImpl.add, OracleInterface.simOracle0,
    OracleComp.liftComp_bind, OracleComp.liftComp_pure, OracleComp.liftComp_query,
    OracleComp.liftComp_map, OracleQuery.cont_query, OracleQuery.input_query,
    OptionT.lift, OptionT.mk, id_map, id_eq, Function.comp,
    bind_pure_comp, map_pure, pure_bind, bind_assoc]
  -- Reduce the table query per element: discharge the `forIn` binder via `congr`/`funext`, then
  -- `rw [hquery]` (which works outside binders where `simp` could not match it).
  congr 1
  congr 1
  funext a b
  rw [← lagrange_answer_signPoint Fact.out (tableOracle oStmt) a]
  rfl

/-- Four-round unfolding of `Fin.induction` (the analog of `Fin.induction_two`), for the outer
LogUp prover's `runToRound`. -/
private theorem Fin.induction_four {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
    Fin.induction (motive := motive) zero succ (Fin.last 4)
      = succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

/-- Completeness of the outer LogUp phase: the honest outer prover reaches `logupMidRelation`,
except with the pole-sampling error.

The membership content of `logupMidRelation` is fully proved: `logupRowsAgree` (the polynomial
agreement) and `logupOuterClaim_zero` (the zero-sum claim, valid whenever `x` avoids the table
poles). What remains is the **monad-execution shell**: unfolding the honest 4-message
`Reduction.run` (prover sends `m`, gets `x`, sends helpers, gets `(z,λ)`; verifier runs the
pole-rejection guard loop), showing `{x not a pole} ⊆ {success}`, and bounding
`P(x is a pole) ≤ |H|/|F|`. This is intricate `OracleComp`/`probEvent` reasoning (cf. the proved
template `Sumcheck.Spec.SingleRound.Simpler.reduction_perfectCompleteness`), the last open piece. -/
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
    MonadLiftT.monadLift, OracleComp.liftComp_pure, OracleComp.liftComp_query,
    bind_pure_comp, map_pure, pure_bind, bind_assoc, Functor.map_map, Function.comp,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    QueryImpl.simulateQ_add_liftComp_left, simulateQ_query, simulateQ_pure, simulateQ_bind,
    simulateQ_map, StateT.run_bind, StateT.run_pure, StateT.run_map,
    ProtocolSpec.challengeQueryImpl]
  rw [ge_iff_le, probEvent_ext (q := fun _ => True) ?allSuccess, probEvent_True_eq_sub]
  · -- pole-probability bound `Pr[⊥] ≤ |H|/|F|`
    refine tsub_le_tsub_left ?_ 1
    sorry
  · -- every non-failing output satisfies the success predicate
    intro out hout
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
    -- peel the verifier (match on `some pval` resolves; then its bind)
    simp only at hver
    erw [simulateQ_bind, StateT.run_bind] at hver
    rw [mem_support_bind_iff] at hver
    obtain ⟨⟨vstmt, sv⟩, hverify, hvout⟩ := hver
    -- Replace the verifier's table-query pole-rejection scan by the clean `evalOnHypercube` loop.
    simp only [OracleVerifier.toVerifier] at hverify
    rw [outerVerify_simulateQ_eq] at hverify
    -- The verifier accepted: `vstmt = some _` (the `none` branch of `hvout` yields `none ≠ some`).
    rcases vstmt with _ | ⟨vStmtOut, vOracles⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hvout
      simp at hvout
    · -- The honest output: `out` pairs the prover view with the verifier's accepted statement.
      dsimp only [Option.getM] at hvout
      simp only [simulateQ_map, simulateQ_pure, StateT.run_map, StateT.run_pure,
        support_map, support_pure, Set.mem_image, Set.mem_singleton_iff, pure_bind,
        Functor.map_map, Function.comp, map_pure] at hvout
      skip
    

/-- Lens-completeness for the LogUp→Sumcheck lens: `proj` is the zero-sum instance
(`logupSumcheckRelationInput_of_rowsAgree`), `lift` is trivial as `outputRelation = univ`. -/
instance logupSumcheckLensComplete :
    (logupSumcheckContextLens F n M params).toContext.IsComplete
      (logupMidRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F Fact.out) 0)
      outputRelation
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F Fact.out)
        (Fin.last n))
      ((logupConcreteSumcheckOracleReduction oSpec F n M params Fact.out).toReduction.compatContext
        (logupSumcheckContextLens F n M params).toContext) where
  proj_complete := by
    rintro ⟨stmt, oStmt⟩ ⟨⟩ h
    exact logupSumcheckRelationInput_of_rowsAgree F n M params (hSigns := Fact.out) h.1 h.2
  lift_complete := by
    intro _ _ _ _ _ _ _
    simp [outputRelation]

/-- Completeness of the embedded sumcheck phase: it carries `logupMidRelation` to `outputRelation`
with no extra error, by reusing the generic sumcheck's perfect completeness through the
LogUp-to-Sumcheck context lens. -/
theorem logupSumcheckPhaseCompleteness :
    (sumcheckOracleReduction oSpec F n M params).completeness init impl
      (logupMidRelation F n M params) outputRelation 0 :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := logupSumcheckContextLens F n M params)
    (lensComplete := logupSumcheckLensComplete oSpec F n M params)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness
      F (logupSumcheckDegree M params) (signDomain F Fact.out) n oSpec)

/-- Main ArkLib completeness theorem for LogUp Protocol 2. -/
theorem logup_completeness :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  letI : Inhabited F := ⟨0⟩
  have happ := OracleReduction.append_completeness.{0, 0, 0, 0}
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    (logup_outer_completeness oSpec F n M params init impl)
    (logupSumcheckPhaseCompleteness oSpec F n M params init impl)
  simpa only [add_zero] using happ

end Completeness

end Logup
