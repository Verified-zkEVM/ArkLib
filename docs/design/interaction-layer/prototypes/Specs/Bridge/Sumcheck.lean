/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bridge.Rounds
import Specs.Examples.Sumcheck
import Specs.Kit.Sumcheck

/-!
# Soundness of the sum-check specification through the bridge

This module proves soundness of the verifier that `sumcheckSpec` derives, `Spec.verifier`, with
ArkLib's error `n · d / |R|`, through the bridge theorem `Bridge.verdict_roundsGo` and the kit's
sum-check round obligation `Kit.sumcheck_roundSound`. It does not use `Sumcheck.indexedVerifier`,
`Sumcheck.indexedVerdict` or the example's agreement theorems.

* `scSpecStep`: the pure meaning of one round of `sumcheckRound` on the description's own state
  `Claim R i`.
* `sumcheckRound_verdict`: one round's verdict is `scSpecStep`, then the continuation. This is the
  bridge's `hbody` for sum-check.
* `sumcheckSpec_verdict_eq`: the specification's verdict factors through the kit's
  `iterVerdict`, from the bridge theorem.
* `scSpec_roundSound`: the per-round obligation for `scSpecStep`, moved from
  `Kit.sumcheck_roundSound`.
* `sumcheckSpec_rbrSound` and `sumcheckSpec_sound`: the main theorems.
* `scCheck`, `scStartProg`, `scFinishProg`: sum-check as query programs of the kit's iteration
  verifier. `scCheck_step`: the check's queries compute `scSpecStep`. `sumcheckSpec_agrees`: the
  specification's verifier agrees (`OracleVerifier.Agrees`) with the kit's `Rounds.verifier` for
  these programs, by the generic `Bridge.agrees_of_kit`.

## Design choices

* **The kit's state is the description's state `Claim R i`.** *Why:* the bridge theorem then
  applies without translating the state, and the only translation is in the per-round obligation,
  where `Claim R i` and `RoundStatement R n i` hold the same target and challenges.
* **The input and output problems are ArkLib's `indexedInputProblem` and
  `indexedOutputProblem`.** *Why:* this matches the statement of
  `Sumcheck.indexedVerifier_soundness`, so the two theorems can be compared directly.
  `Specs.Claims.sumcheckSpec_claimSound` restates the theorem with the problems that the stage's
  own claim formulas denote.
* **The round formulas evaluate by `Specs.eval_round_value` and `Specs.eval_round_check` of
  `Specs.Examples.Sumcheck`.** *Why:* `simp` and `rw` time out on `Curry.app`, and these lemmas
  evaluate the two round formulas by `rfl` at their exact hole lists.
-/

set_option linter.hashCommand false

namespace Specs.Bridge
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens
open Interaction.Oracle
open Specs.Kit Sumcheck Polynomial MvPolynomial
open scoped ENNReal NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k n : ℕ}

variable (R d) in
/-- The kit's round family of sum-check, as the bridge builds it. -/
abbrev scFam (n : ℕ) : Fin n → Round := fam n (fun _ => scRound R d)

/-- One round of `sumcheckRound` as a pure step on the description's state: check
`Σ_{a ∈ D} g(a) = c_i`, then move to `c_{i+1} = g(r_i)` and append `r_i`. -/
noncomputable def scSpecStep (D : Fin k → R) : Step (scFam R d n) (fun i => Claim R i.val) :=
  fun _ st vals r =>
    if (∑ a, vals.1.val.eval (D a)) = st.c.val then
      some ⟨⟨vals.1.val.eval r⟩, Fin.snoc st.rs r⟩ else none

/-- **One round through the bridge.** The verdict of round `i` of `sumcheckRound` is the step
`scSpecStep`, then the continuation with the round polynomial added to the handler table. -/
theorem sumcheckRound_verdict (D : Fin k → R) {In : OracleBundle} {W T : Type}
    (poly : W → R⦃≤ d⦄[X Fin n]) (ans : QueryImpl In.spec Id) {t : OracleProtocol} {ks : Skel}
    (i : ℕ) (hi : i < n) (st : Claim R i) (nx : Claim R (i + 1) → Desc In W T t ks)
    (tr : Transcript oracleSig ((scRound R d).then t)) (env : Handlers Id) (ℓ : ℕ) :
    ∃ env' ℓ', True ∧ (sumcheckRound n D poly i hi st nx).verdict ans tr env ℓ =
      (scSpecStep (n := n) D ⟨i, hi⟩ st (Block.split (scRound R d).msgs tr).1
        (Chal.split (Block.split (scRound R d).msgs tr).2).1).bind fun st' =>
        (nx st').verdict ans (Chal.split (Block.split (scRound R d).msgs tr).2).2 env' ℓ' := by
  obtain ⟨g, x, tr⟩ := tr
  refine ⟨env.ext ℓ (Desc.honestEntry (inferInstance : OracleInterface (R⦃≤ d⦄[X])) (A := R)
    (fun _ => rfl) (show R⦃≤ d⦄[X] from g)), ℓ + 1, trivial, ?_⟩
  rw [sumcheckRound]
  simp only [oracle, check, challenge, compute]
  erw [Desc.verdict.eq_3, Desc.verdict.eq_5]
  simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
    Args.append, eval_round_check, askId, Handlers.find_ext_self]
  erw [Desc.verdict.eq_4, Desc.verdict.eq_6]
  simp only [Closed.inst, eval_round_value, askId, Handlers.find_ext_self]
  dsimp only [Desc.honestEntry, Id.run_pure, cast_eq, OracleInterface.instPolynomialDegreeLE,
    Block.split, Chal.split, scSpecStep]
  by_cases hc : ∑ a, Polynomial.eval (D a) g.val = st.c.val
  · simp only [hc, decide_true, ↓reduceIte, Option.bind_some]
  · simp only [hc, decide_false, ↓reduceIte, Bool.false_eq_true, Option.bind_none]

/-- The certificate that the bridge builds for the `rounds` block of `sumcheckSpec`. -/
noncomputable abbrev scCert (R : Type) [CommSemiring R] (d n : ℕ) :
    Rounds (scFam R d n) [] 0 n (Nat.zero_add n) (protocol R d n) :=
  cert (rsN := fun _ => scRound R d) (suf := []) (fun _ r => protocol R d r) (fun _ => rfl)
    (fun _ _ => rfl) n 0 (Nat.zero_add n)

/-- The initial state of `sumcheckSpec`: the input target and challenges. -/
def scStart (x : RoundStatement R n 0 × (polynomialFamily R n d).Data) (_ : PUnit) :
    Option (Claim R 0) :=
  some ⟨⟨x.1.target⟩, x.1.challenges⟩

/-- The output of `sumcheckSpec` from the final state. -/
def scFinish (_ : RoundStatement R n 0 × (polynomialFamily R n d).Data)
    (q : Claim R n × PUnit) : Option (RoundStatement R n (Fin.last n)) :=
  some ⟨q.1.c.val, q.1.rs⟩

/-- **The verdict of `sumcheckSpec` factors through the kit**, by the bridge theorem with the
round lemma `sumcheckRound_verdict`. -/
theorem sumcheckSpec_verdict_eq (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data)
    (tr : Transcript oracleSig (protocol R d n)) :
    (sumcheckSpec R d n D).verdict x.1 x.2 tr =
      ((scCert R d n).iterVerdict (pre := []) scStart (fun _ => scSpecStep D) x tr).bind
        (scFinish x) :=
  verdict_roundsGo (In := polynomialFamily R n d) (W := R⦃≤ d⦄[X Fin n])
    (T := RoundStatement R n (Fin.last n)) (rsN := fun _ => scRound R d) (suf := []) _
    _ (sumcheckRound n D id) _ (fun _ r => protocol R d r) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (scSpecStep D) (fun st v => scFinish x (st, v))
    (fun _ _ => True)
    (fun i hi st nx tr env ℓ _ => sumcheckRound_verdict D id _ i hi st nx tr env ℓ)
    (by intros; rfl) n 0 (Nat.zero_add n) _ tr _ _ trivial

omit [DecidableEq R] [TypeName R] in
/-- The challenge of every round of the certificate is drawn uniformly. -/
theorem scCert_drawIs [SampleableType R] : ∀ (k j : ℕ) (h : j + k = n),
    (cert (rsN := fun _ => scRound R d) (suf := []) (fun _ r => protocol R d r) (fun _ => rfl)
      (fun _ _ => rfl) k j h).DrawIs (fun _ => $ᵗ R) (indexedDraw (R := R) (deg := d) k)
  | 0, j, h => by subst h; exact True.intro
  | k + 1, j, h => fun _ => ⟨rfl, scCert_drawIs k (j + 1) (by omega)⟩

omit [TypeName R] in
/-- **The per-round obligation for the description's step**, moved from
`Kit.sumcheck_roundSound`: `Claim R i` and `RoundStatement R n i` hold the same target and
challenges. -/
theorem scSpec_roundSound [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    (p : R⦃≤ d⦄[X Fin n]) :
    RoundSound (fun _ => $ᵗ R) (scSpecStep (d := d) D)
      (fun i st => indexedRelation D i ⟨st.c.val, st.rs⟩ p)
      (fun _ => (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  intro i st vals hfalse
  refine le_trans (le_of_eq ?_)
    (sumcheck_roundSound (deg := d) D p i ⟨st.c.val, st.rs⟩ vals hfalse)
  congr 1
  refine congrArg (· <$> _) (funext fun r => ?_)
  by_cases hs : (∑ a, vals.1.val.eval (D a)) = st.c.val <;>
    simp [scSpecStep, scStep, hs]

/-- **Round-by-round soundness of the sum-check specification's own verifier**, through the
bridge: error `d / |R|` at every challenge. -/
theorem sumcheckSpec_rbrSound [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (sumcheckSpec R d n D).RBRSound ambient impl (indexedInputProblem (deg := d) D)
      (indexedOutputProblem (R := R) (deg := d) (n := n)) (indexedDraw (R := R) (deg := d) n)
      (fun _ => (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  rbrSound_of_kit (pre := []) (sumcheckSpec R d n D) ambient impl
    (indexedInputProblem (deg := d) D) (indexedOutputProblem (R := R) (deg := d) (n := n))
    (indexedDraw (R := R) (deg := d) n) (scCert R d n) scStart
    (fun _ => scSpecStep D) scFinish (fun x i st => indexedRelation D i ⟨st.c.val, st.rs⟩ (x.2 ()))
    (fun _ => $ᵗ R) _ (sumcheckSpec_verdict_eq D) (fun _ => scCert_drawIs n 0 (Nat.zero_add n))
    (fun _ _ _ _ hs h => by cases hs; exact ⟨(), h⟩)
    (fun x _ q o hf hl => by
      cases hf
      obtain ⟨_, hl⟩ := hl
      exact (indexedRelation_last D _ (x.2 ())).mpr hl)
    (fun x => scSpec_roundSound D (x.2 ()))

/-- **Soundness of the sum-check specification's own verifier**, through the bridge and the kit's
sum-check round obligation, with ArkLib's error `n · (d / |R|)`. The statement is that of
`Sumcheck.indexedVerifier_soundness` with `Spec.verifier (sumcheckSpec R d n D)` in place of
`indexedVerifier`. -/
theorem sumcheckSpec_sound [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (sumcheckSpec R d n D).Sound ambient init impl (indexedDraw (R := R) (deg := d) n)
      (indexedInputProblem (deg := d) D) (indexedOutputProblem (R := R) (deg := d) (n := n))
      ((n : ℝ≥0∞) * (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := sound_of_kit (pre := []) (sumcheckSpec R d n D) ambient init impl
    (indexedInputProblem (deg := d) D) (indexedOutputProblem (R := R) (deg := d) (n := n))
    (indexedDraw (R := R) (deg := d) n) (scCert R d n) scStart (fun _ => scSpecStep D) scFinish
    (fun x i st => indexedRelation D i ⟨st.c.val, st.rs⟩ (x.2 ())) (fun _ => $ᵗ R)
    (fun _ => (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) (sumcheckSpec_verdict_eq D)
    (fun _ => scCert_drawIs n 0 (Nat.zero_add n))
    (fun _ _ _ _ hs h => by cases hs; exact ⟨(), h⟩)
    (fun x _ q o hf hl => by
      cases hf
      obtain ⟨_, hl⟩ := hl
      exact (indexedRelation_last D _ (x.2 ())).mpr hl)
    (fun x => scSpec_roundSound D (x.2 ()))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-! ### The kit's iteration verifier for sum-check -/

/-- A query to the round polynomial, from a program on the round's block. -/
noncomputable def scAsk (a : R) :
    OracleComp ((polynomialFamily R n d).sum (Block.bundle (scRound R d).msgs)).spec R :=
  liftM (((polynomialFamily R n d).sum (Block.bundle (scRound R d).msgs)).spec.query
    (.inr (.inl a)))

/-- **The kit's round check of sum-check**, as a query program on the description's state: sum
the round polynomial over `D`, compare with `c_i`, then move to `c_{i+1} = g_i(r_i)`. -/
noncomputable def scCheck (D : Fin k → R) :
    Check (polynomialFamily R n d) (scFam R d n) (fun i => Claim R i.val) :=
  fun _ st _ r => OptionT.mk do
    let values ← (List.finRange k).mapM fun a => scAsk (n := n) (d := d) (D a)
    if values.sum = st.c.val then
      let value ← scAsk (n := n) (d := d) r
      return some ⟨⟨value⟩, Fin.snoc st.rs r⟩
    else return none

omit [TypeName R] in
/-- The check's queries compute the description's round step. -/
theorem scCheck_step (D : Fin k → R) (data : (polynomialFamily R n d).Data) :
    (scCheck (n := n) (d := d) D).step data = scSpecStep D := by
  funext i st vals r
  unfold Check.step Block.run scCheck scSpecStep
  change simulateQ _ ((List.finRange k).mapM
      (fun a => scAsk (n := n) (d := d) (D a)) >>= _) = _
  simp only [simulateQ_bind, simulateQ_list_mapM]
  change ((List.finRange k).mapM (fun a => (pure (vals.1.val.eval (D a)) : Id R)) >>= _) = _
  simp only [List.mapM_pure, LawfulMonad.pure_bind]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  split <;> rfl

/-- The kit's start program of sum-check: the input statement as the initial state. -/
def scStartProg : RoundStatement R n 0 → Block.ViewValues [] →
    Block.Program (polynomialFamily R n d) [] (Claim R 0) :=
  fun stmt _ => OptionT.mk (pure (some ⟨⟨stmt.target⟩, stmt.challenges⟩))

/-- The kit's finish program of sum-check: the final state as the output. -/
def scFinishProg : Claim R n → Block.ViewValues [] →
    Block.Program (polynomialFamily R n d) [] (RoundStatement R n (Fin.last n)) :=
  fun st _ => OptionT.mk (pure (some ⟨st.c.val, st.rs⟩))

/-- **The sum-check specification's verifier agrees with the kit's iteration verifier** for the
check program `scCheck`, in ArkLib's sense (`OracleVerifier.Agrees`), so every security notion
transfers between them. -/
theorem sumcheckSpec_agrees (D : Fin k → R) {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier.Agrees ((sumcheckSpec R d n D).verifier ambient)
      (Rounds.verifier (pre := []) (polynomialFamily R n d) (scStartProg (n := n) (d := d))
        (scCheck D) (scFinishProg (n := n) (d := d)) ambient (scCert R d n)) := by
  refine agrees_of_kit (pre := []) (K := fun i : Fin (n + 1) => Claim R i.val)
    (sumcheckSpec R d n D) ambient (scCert R d n) scStartProg (scCheck D) scFinishProg ?_
  intro x tr
  refine (sumcheckSpec_verdict_eq D x tr).trans ?_
  have hs : (fun x : RoundStatement R n 0 × (polynomialFamily R n d).Data =>
      (scCheck (n := n) (d := d) D).step x.2) = fun _ => scSpecStep D :=
    funext fun x => scCheck_step D x.2
  rw [hs]
  rfl

end Specs.Bridge

#print axioms Specs.Bridge.sumcheckRound_verdict
#print axioms Specs.Bridge.sumcheckSpec_verdict_eq
#print axioms Specs.Bridge.scSpec_roundSound
#print axioms Specs.Bridge.sumcheckSpec_rbrSound
#print axioms Specs.Bridge.sumcheckSpec_sound
#print axioms Specs.Bridge.scCheck_step
#print axioms Specs.Bridge.sumcheckSpec_agrees
