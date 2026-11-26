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

## Design choices

* **The kit's state is the description's state `Claim R i`.** *Why:* the bridge theorem then
  applies without translating the state, and the only translation is in the per-round obligation,
  where `Claim R i` and `RoundStatement R n i` hold the same target and challenges.
* **The input and output problems are ArkLib's `indexedInputProblem` and
  `indexedOutputProblem`.** *Why:* this matches the statement of
  `Sumcheck.indexedVerifier_soundness`, so the two theorems can be compared directly.
-/

set_option linter.hashCommand false

namespace Specs.Bridge
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens
open Interaction.Oracle
open Specs.Kit Sumcheck Polynomial MvPolynomial
open scoped ENNReal NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k n : ℕ}

omit [DecidableEq R] [TypeName R] in
/-- The local value `g_i(r_i)` of a round evaluates by one query to `g_i` (a copy of the private
lemma of `Specs.Examples.Sumcheck`). -/
private theorem eval_round_value (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (OracleInterface.Query (R⦃≤ d⦄[X])) R) (c : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := R)
      (Γ := [Hole.orc nm (OracleInterface.Query (R⦃≤ d⦄[X])) R] ++ [Hole.val nm' R])
      (fun g r => ask g r) (Args.orc h (Args.val c Args.nil))) = ask' h c := rfl

omit [TypeName R] in
/-- The round check `Σ_{a ∈ D} g_i(a) = c_i` evaluates to a sum over the domain indices (a copy
of the private lemma of `Specs.Examples.Sumcheck`). -/
private theorem eval_round_check (D : Fin k → R) (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (OracleInterface.Query (R⦃≤ d⦄[X])) R) (x : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := Bool)
      (Γ := [Hole.orc nm (OracleInterface.Query (R⦃≤ d⦄[X])) R] ++ [Hole.val nm' R])
      (fun g c => (∑∈ a ∈ Dom.ofFn "D" D, ask g a) =' .var c)
      (Args.orc h (Args.val x Args.nil))) = decide (∑ a : Fin k, ask' h (D a) = x) := by
  change Fml.eval ask' ((∑∈ a ∈ Dom.ofFn "D" D, ask h a) =' .var x) = _
  simp only [Fml.eval_eq, Fml.eval_sum, Fml.eval_query, Fml.eval_var, Dom.ofFn, List.map_ofFn,
    List.sum_ofFn]
  rfl

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
    "sumcheck" "n" _ (sumcheckRound n D id) _ (fun _ r => protocol R d r) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (scSpecStep D) (fun st v => scFinish x (st, v))
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

end Specs.Bridge

#print axioms Specs.Bridge.sumcheckRound_verdict
#print axioms Specs.Bridge.sumcheckSpec_verdict_eq
#print axioms Specs.Bridge.scSpec_roundSound
#print axioms Specs.Bridge.sumcheckSpec_rbrSound
#print axioms Specs.Bridge.sumcheckSpec_sound
