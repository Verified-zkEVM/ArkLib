/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bridge.Sumcheck

/-!
# Sum-check soundness and completeness on its own stage claims

The `sumcheck` stage of `sumcheckSpec` states its input claim `Σ_{x ∈ D^n} p(x) = c_0` and its
output claim `p(r) = c_n` as formulas. This module proves that these formulas are what the
security statements are about, by instantiating the stage contracts of `Specs.Security`
(`Spec.ClaimSound`, `Spec.ClaimRBRSound`, `Spec.ClaimComplete`, `Spec.StageContract`).

* `sum_tuples` and `roundSum_zero`: the list sum over the tuples of `Dom.pow` is ArkLib's round
  sum before any challenge. `sumcheckSpec_InClaim_iff`: the input claim, evaluated, is ArkLib's
  `indexedRelation D 0`. `sumcheckSpec_inputProblem_iff`: the two input languages coincide.
* `sumcheckSpec_outClaim_of_verdict`: on an accepted transcript with output `o`, the output claim
  evaluates to `p(o.challenges) = o.target`. `sumcheckSpec_outputProblem_le`: the output claim's
  language is contained in ArkLib's `indexedOutputProblem`.
* `sumcheckSpec_claimSound` (soundness with the specification's own `inputProblem` and
  `outputProblem`, error `n · (d / |R|)`) follows from `Bridge.sumcheckSpec_sound` by
  `Spec.ClaimSound.of_sound`. `sumcheckSpec_claimRBRSound` is the round-by-round version, through
  the bridge.
* `sumcheckSpec_complete` and `sumcheckSpec_outClaim_of_honest`: with the input polynomial as the
  witness and a true input claim, every check holds on the honest values and the output claim is
  `true` on every honest transcript. `sumcheckSpec_claimComplete` packs them as the completeness
  contract and `sumcheckSpec_contract` packs both directions.
* `outClaim_roundsGo_of_verdict`, `complete_roundsGo` and `outClaim_roundsGo_of_honest` are the
  three round inductions behind these, each for an arbitrary continuation after the rounds.

## Design choices

* **The output side is an inclusion, not an equality of languages.** *Why:* the output problem
  of a specification holds when some accepted transcript returns the output with a true output
  claim. ArkLib's output language holds for every output with `p(r) = c_n`, also for outputs that
  no accepted transcript returns. Soundness needs only the inclusion.
* **The round inductions track the handler table with the invariant `PolyInv`**: level `0` holds
  the input polynomial and the next level is above it. *Why:* the output claim reads `p` through
  its handle at level `0` after the `n` rounds have added their round polynomials above it.
* **Completeness is deterministic** (`Desc.Complete` and the output claim on every honest
  transcript), not ArkLib's probabilistic `Spec.Complete`. *Why:* it is the statement the stage
  claims make, it holds for every choice of challenges, and `Spec.verdict_isSome` turns it into
  acceptance of every honest transcript.
-/

set_option linter.hashCommand false

namespace Specs.Claims
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens
open Interaction.Oracle
open Specs.Kit Specs.Bridge Sumcheck Polynomial MvPolynomial
open scoped ENNReal NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k n : ℕ}

/-- The sum of a `flatMap` is the sum of the sums. -/
theorem sum_flatMap' {α M : Type} [AddCommMonoid M] (g : α → List M) :
    ∀ l : List α, (l.flatMap g).sum = (l.map fun a => (g a).sum).sum
  | [] => rfl
  | a :: l => by simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap' g l]

omit [CommSemiring R] [DecidableEq R] [TypeName R] in
/-- The list sum over the tuples of `Dom.pow` is the sum over all index tuples. -/
theorem sum_tuples {M : Type} [AddCommMonoid M] (D : Fin k → R) (f : (Fin n → R) → M) :
    ((Dom.tuples (List.ofFn D) n).map f).sum = ∑ x : Fin n → Fin k, f (D ∘ x) := by
  induction n generalizing M with
  | zero =>
    rw [Fintype.sum_unique]
    simp only [Dom.tuples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact congrArg f (funext fun i => i.elim0)
  | succ n ih =>
    have hs := Fin.sum_piFinset_cons (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))
      (fun x => f (D ∘ x))
    simp only [Fintype.piFinset_univ] at hs
    rw [hs]
    simp only [Dom.tuples, List.map_flatMap, sum_flatMap', List.map_map, Function.comp_def]
    simp only [ih, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hu : Fintype.piFinset (Fin.tail fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k))) =
        Finset.univ := Fintype.piFinset_univ
    rw [hu]
    refine Finset.sum_congr rfl fun y _ => congrArg f (funext fun i => ?_)
    exact Fin.cases rfl (fun _ => rfl) i

omit [DecidableEq R] [TypeName R] in
/-- ArkLib's round sum before any challenge is the sum over all index tuples. -/
theorem roundSum_zero (D : Fin k → R) (c : Fin ((0 : Fin (n + 1)) : ℕ) → R)
    (p : MvPolynomial (Fin n) R) :
    roundSum D 0 c p = ∑ x : Fin n → Fin k, p.eval (D ∘ x) := by
  unfold roundSum
  refine Finset.sum_congr rfl fun x _ =>
    congrArg (fun v => MvPolynomial.eval v p) (funext fun j => ?_)
  change Fin.append c (D ∘ x) (Fin.cast _ j) = D (x j)
  rw [show (Fin.cast (by simp) j :
      Fin (((0 : Fin (n + 1)) : ℕ) + (n - ((0 : Fin (n + 1)) : ℕ)))) =
        Fin.natAdd ((0 : Fin (n + 1)) : ℕ)
          (Fin.cast (by simp) j : Fin (n - ((0 : Fin (n + 1)) : ℕ))) from
      Fin.ext (show (j : ℕ) = 0 + (j : ℕ) from (Nat.zero_add _).symm), Fin.append_right]
  rfl

omit [TypeName R] in
/-- The input claim formula evaluates to a list sum over the tuples. -/
private theorem eval_inClaim (D : Fin k → R) (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (Fin n → R) R) (c : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := Bool)
      (Γ := [Hole.orc nm (Fin n → R) R] ++ [Hole.val nm' R])
      (fun p c => (∑∈ x ∈ (Dom.ofFn "D" D).pow n "n", ask p x) =' .var c)
      (Args.orc h (Args.val c Args.nil))) =
      decide (((Dom.tuples (List.ofFn D) n).map fun y => ask' h y).sum = c) := by
  change Fml.eval ask' ((∑∈ x ∈ (Dom.ofFn "D" D).pow n "n", ask h x) =' .var c) = _
  simp only [Fml.eval_eq, Fml.eval_sum, Fml.eval_query, Fml.eval_var, Dom.ofFn, Dom.pow]

/-- The input claim of the sum-check specification, evaluated. -/
theorem sumcheckSpec_inClaim (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data) :
    (sumcheckSpec R d n D).inClaim x = some (decide
      (((Dom.tuples (List.ofFn D) n).map fun y => (x.2 ()).val.eval y).sum = x.1.target)) := by
  unfold Spec.inClaim sumcheckSpec
  dsimp only [input, stage]
  erw [Desc.inClaim.eq_8, Desc.inClaim.eq_9]
  simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
    Args.append, eval_inClaim, askId, Handlers.find_ext_self]
  rfl

/-- **The input claim is ArkLib's input relation**: `Σ_{x ∈ D^n} p(x) = c_0` holds exactly when
`indexedRelation D 0` does. -/
theorem sumcheckSpec_InClaim_iff (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data) :
    (sumcheckSpec R d n D).InClaim x ↔ indexedRelation D 0 x.1 (x.2 ()) := by
  unfold Spec.InClaim indexedRelation
  rw [sumcheckSpec_inClaim, roundSum_zero, sum_tuples]
  simp only [Option.getD_some, decide_eq_true_eq]

/-- The invariant of the handler table inside the rounds: level `0` holds the input polynomial
`P`, and the next level is above it. -/
def PolyInv (P : R⦃≤ d⦄[X Fin n]) (env : Handlers Id) (ℓ : ℕ) : Prop :=
  0 < ℓ ∧ ∀ (dflt : R) (q : Fin n → R), (env.find dflt 0 q).run = P.val.eval q

omit [DecidableEq R] [TypeName R] in
/-- Adding an entry at the next level keeps the invariant. -/
theorem PolyInv.ext {P : R⦃≤ d⦄[X Fin n]} {env : Handlers Id} {ℓ : ℕ} (h : PolyInv P env ℓ)
    {Q A : Type} (f : Q → Id A) : PolyInv P (env.ext ℓ f) (ℓ + 1) :=
  ⟨Nat.succ_pos ℓ, fun dflt q => by
    rw [Handlers.find_ext_ne _ (Nat.ne_of_lt h.1)]
    exact h.2 dflt q⟩

omit [CommSemiring R] [TypeName R] in
/-- The output claim formula evaluates by one query to `p`. -/
private theorem eval_outClaim (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' nm'' : Name} (h : Ref (Fin n → R) R) (r : Fin n → R) (c : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := Bool)
      (Γ := [Hole.orc nm (Fin n → R) R] ++ ([Hole.val nm' (Fin n → R)] ++ [Hole.val nm'' R]))
      (fun p r c => ask p r =' .var c)
      (Args.orc h (Args.val r (Args.val c Args.nil)))) = decide (ask' h r = c) := rfl

/-- **Sum-check rounds, soundness direction.** On a transcript that the rounds accept with
output `o`, the output claim after the rounds is the claim of the continuation on `o`. -/
theorem outClaim_roundsGo_of_verdict {n : ℕ} (D : Fin k → R)
    (ans : QueryImpl (polynomialFamily R n d).spec Id) (P : R⦃≤ d⦄[X Fin n])
    {ks : Skel} (next : Claim R n → Desc (polynomialFamily R n d) (R⦃≤ d⦄[X Fin n])
      (RoundStatement R n (Fin.last n)) (protocol R d 0) ks)
    (good : RoundStatement R n (Fin.last n) → Option Bool)
    (hnext : ∀ st tr env ℓ acc o, PolyInv P env ℓ → (next st).verdict ans tr env ℓ = some o →
      (next st).outClaim ans tr env ℓ acc = good o) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (tr : Transcript oracleSig (protocol R d r))
      (env : Handlers Id) (ℓ : ℕ) (acc : Option Bool) (o : RoundStatement R n (Fin.last n)),
      PolyInv P env ℓ →
      Desc.verdict ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) tr env ℓ = some o →
      Desc.outClaim ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) tr env ℓ acc = good o := by
  intro r
  induction r with
  | zero =>
    intro j h st tr env ℓ acc o hinv hv
    subst h
    exact hnext st tr env ℓ acc o hinv hv
  | succ r ih =>
    intro j h st tr env ℓ acc o hinv hv
    obtain ⟨g, x, tr⟩ := tr
    rw [roundsGo] at hv ⊢
    simp only [Desc.retree_rfl] at hv ⊢
    rw [sumcheckRound] at hv ⊢
    simp only [oracle, check, challenge, compute] at hv ⊢
    erw [Desc.verdict.eq_11, Desc.verdict.eq_3, Desc.verdict.eq_5] at hv
    erw [Desc.outClaim.eq_11, Desc.outClaim.eq_3, Desc.outClaim.eq_5, Desc.outClaim.eq_4,
      Desc.outClaim.eq_6, Desc.outClaim.eq_11]
    split at hv
    · erw [Desc.verdict.eq_4, Desc.verdict.eq_6, Desc.verdict.eq_11] at hv
      exact ih (j + 1) _ _ tr _ _ acc o (hinv.ext _) hv
    · cases hv

/-- **The output claim of an accepted sum-check transcript** is `p(r) = c_n` on the output
`(c_n, r)`. -/
theorem sumcheckSpec_outClaim_of_verdict (D : Fin k → R) (stmt : RoundStatement R n 0)
    (data : (polynomialFamily R n d).Data) (tr : Transcript oracleSig (protocol R d n))
    (o : RoundStatement R n (Fin.last n))
    (hv : (sumcheckSpec R d n D).verdict stmt data tr = some o) :
    (sumcheckSpec R d n D).outClaim stmt data tr =
      some (decide ((data ()).val.eval o.challenges = o.target)) := by
  unfold Spec.outClaim Spec.verdict sumcheckSpec at *
  dsimp only [input, stage] at *
  erw [Desc.verdict.eq_7, Desc.verdict.eq_9] at hv
  erw [Desc.outClaim.eq_7, Desc.outClaim.eq_9]
  refine outClaim_roundsGo_of_verdict D _ (data ()) _
    (fun o => some (decide ((data ()).val.eval o.challenges = o.target))) ?_ n 0 _ _ tr _ _
    none o ⟨Nat.one_pos, fun dflt q => by rw [Handlers.find_ext_self]; rfl⟩ hv
  intro st tr env ℓ acc o hinv hv
  erw [Desc.verdict.eq_10] at hv
  erw [Desc.outClaim.eq_10]
  cases hv
  simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
    Args.append, eval_outClaim, askId, hinv.2]
  rfl

/-- **Sum-check rounds, completeness direction: the checks.** If the claim entering round `j`
is the true remaining sum of `w`, every check of the remaining rounds holds on the honest
values. -/
theorem complete_roundsGo {n : ℕ} (D : Fin k → R)
    (ans : QueryImpl (polynomialFamily R n d).spec Id) (w : R⦃≤ d⦄[X Fin n])
    {ks : Skel} (next : Claim R n → Desc (polynomialFamily R n d) (R⦃≤ d⦄[X Fin n])
      (RoundStatement R n (Fin.last n)) (protocol R d 0) ks)
    (hnext : ∀ st env ℓ, st.c.val = roundSum D (Fin.last n) st.rs w.val →
      (next st).Complete w ans env ℓ) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (env : Handlers Id) (ℓ : ℕ),
      st.c.val = roundSum D ⟨j, by omega⟩ st.rs w.val →
      Desc.Complete w ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) env ℓ := by
  intro r
  induction r with
  | zero =>
    intro j h st env ℓ hc
    subst h
    exact hnext st env ℓ hc
  | succ r ih =>
    intro j h st env ℓ hc
    rw [roundsGo]
    simp only [Desc.retree_rfl]
    rw [sumcheckRound]
    simp only [oracle, check, challenge, compute]
    erw [Desc.Complete.eq_11, Desc.Complete.eq_3, Desc.Complete.eq_5]
    refine ⟨?_, ?_⟩
    · simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
        Args.append, eval_round_check, askId, Handlers.find_ext_self]
      dsimp only [Desc.honestEntry, Id.run_pure, cast_eq, OracleInterface.instPolynomialDegreeLE]
      rw [decide_eq_true_eq]
      exact (sum_projectedRoundPolynomial D ⟨j, by omega⟩ st.rs w).trans hc.symm
    · erw [Desc.Complete.eq_4]
      intro x
      erw [Desc.Complete.eq_6, Desc.Complete.eq_11]
      simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
        Args.append, eval_round_value, askId, Handlers.find_ext_self]
      refine ih (j + 1) _ _ _ _ ?_
      dsimp only [Desc.honestEntry, Id.run_pure, cast_eq, OracleInterface.instPolynomialDegreeLE]
      exact (roundSum_succ D ⟨j, by omega⟩ st.rs w x).symm

/-- **Sum-check rounds, completeness direction: the output claim.** If the claim entering round
`j` is the true remaining sum of `w`, the output claim after the rounds holds on every honest
transcript. -/
theorem outClaim_roundsGo_of_honest {n : ℕ} (D : Fin k → R)
    (ans : QueryImpl (polynomialFamily R n d).spec Id) (P w : R⦃≤ d⦄[X Fin n])
    {ks : Skel} (next : Claim R n → Desc (polynomialFamily R n d) (R⦃≤ d⦄[X Fin n])
      (RoundStatement R n (Fin.last n)) (protocol R d 0) ks)
    (hnext : ∀ st tr env ℓ acc, PolyInv P env ℓ →
      st.c.val = roundSum D (Fin.last n) st.rs w.val →
      (next st).outClaim ans tr env ℓ acc = some true) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (tr : Transcript oracleSig (protocol R d r))
      (env : Handlers Id) (ℓ : ℕ) (acc : Option Bool), PolyInv P env ℓ →
      st.c.val = roundSum D ⟨j, by omega⟩ st.rs w.val →
      Desc.Honest w ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) tr env ℓ →
      Desc.outClaim ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) tr env ℓ acc = some true := by
  intro r
  induction r with
  | zero =>
    intro j h st tr env ℓ acc hinv hc _
    subst h
    exact hnext st tr env ℓ acc hinv hc
  | succ r ih =>
    intro j h st tr env ℓ acc hinv hc hh
    obtain ⟨g, x, tr⟩ := tr
    rw [roundsGo] at hh ⊢
    simp only [Desc.retree_rfl] at hh ⊢
    rw [sumcheckRound] at hh ⊢
    simp only [oracle, check, challenge, compute] at hh ⊢
    erw [Desc.Honest.eq_11, Desc.Honest.eq_3] at hh
    obtain ⟨rfl, hh⟩ := hh
    erw [Desc.Honest.eq_5, Desc.Honest.eq_4, Desc.Honest.eq_6, Desc.Honest.eq_11] at hh
    erw [Desc.outClaim.eq_11, Desc.outClaim.eq_3, Desc.outClaim.eq_5, Desc.outClaim.eq_4,
      Desc.outClaim.eq_6, Desc.outClaim.eq_11]
    simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
      Args.append, eval_round_value, askId, Handlers.find_ext_self] at hh ⊢
    refine ih (j + 1) _ _ tr _ _ acc (hinv.ext _) ?_ hh
    dsimp only [Desc.honestEntry, Id.run_pure, cast_eq, OracleInterface.instPolynomialDegreeLE]
    exact (roundSum_succ D ⟨j, by omega⟩ st.rs w x).symm

/-- The checks of the sum-check specification hold on the honest values when the input claim
holds and the witness is the input polynomial. -/
theorem sumcheckSpec_complete (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data)
    (hin : (sumcheckSpec R d n D).InClaim x) :
    ((sumcheckSpec R d n D).desc x.1).Complete (x.2 ()) ((polynomialFamily R n d).answer x.2)
      .empty 0 := by
  have hc := (sumcheckSpec_InClaim_iff D x).mp hin
  unfold sumcheckSpec
  dsimp only [input, stage]
  erw [Desc.Complete.eq_7, Desc.Complete.eq_9]
  exact complete_roundsGo D _ (x.2 ()) _ (fun _ _ _ _ => by erw [Desc.Complete.eq_10]; trivial)
    n 0 (Nat.zero_add n) _ _ _ hc.symm

/-- The output claim of the sum-check specification holds on every honest transcript when the
input claim holds and the witness is the input polynomial. -/
theorem sumcheckSpec_outClaim_of_honest (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data)
    (hin : (sumcheckSpec R d n D).InClaim x) (tr : Transcript oracleSig (protocol R d n))
    (hh : ((sumcheckSpec R d n D).desc x.1).Honest (x.2 ())
      ((polynomialFamily R n d).answer x.2) tr .empty 0) :
    (sumcheckSpec R d n D).outClaim x.1 x.2 tr = some true := by
  have hc := (sumcheckSpec_InClaim_iff D x).mp hin
  unfold Spec.outClaim sumcheckSpec at *
  dsimp only [input, stage] at *
  erw [Desc.Honest.eq_7, Desc.Honest.eq_9] at hh
  erw [Desc.outClaim.eq_7, Desc.outClaim.eq_9]
  refine outClaim_roundsGo_of_honest D _ (x.2 ()) (x.2 ()) _ ?_ n 0 _ _ tr _ _ none
    ⟨Nat.one_pos, fun dflt q => by rw [Handlers.find_ext_self]; rfl⟩ hc.symm hh
  intro st tr env ℓ acc hinv hst
  erw [Desc.outClaim.eq_10]
  simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
    Args.append, eval_outClaim, askId, hinv.2]
  have h := (indexedRelation_last D ⟨st.c.val, st.rs⟩ (x.2 ())).mp hst.symm
  change some (decide ((MvPolynomial.eval st.rs) (x.2 ()).val = st.c.val)) = some true
  rw [h]
  exact congrArg some (decide_eq_true rfl)

/-- **The output claim's language is in ArkLib's output language.** An output that some
accepted transcript returns with a true output claim `p(r) = c_n` satisfies ArkLib's final
evaluation claim. -/
theorem sumcheckSpec_outputProblem_le (D : Fin k → R) (p : Path (protocol R d n))
    (o : RoundStatement R n (Fin.last n) × (polynomialFamily R n d).Data) :
    (sumcheckSpec R d n D).outputProblem.language p o →
      (indexedOutputProblem (R := R) (deg := d) (n := n)).language p o := by
  intro hl
  obtain ⟨stmt, tr, -, hv, hc⟩ := ((sumcheckSpec R d n D).outputProblem_language p o).mp hl
  rw [sumcheckSpec_outClaim_of_verdict D stmt o.2 tr o.1 hv] at hc
  exact ⟨(), (by simpa using hc : (o.2 ()).val.eval o.1.challenges = o.1.target)⟩

/-- **The input claim's language is ArkLib's input language.** -/
theorem sumcheckSpec_inputProblem_iff (D : Fin k → R)
    (x : RoundStatement R n 0 × (polynomialFamily R n d).Data) :
    (sumcheckSpec R d n D).inputProblem.language () x ↔
      (indexedInputProblem (deg := d) D).language () x :=
  ((sumcheckSpec R d n D).inputProblem_language x).trans
    ((sumcheckSpec_InClaim_iff D x).trans ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩)

/-- **Soundness of the sum-check specification on its own stage claims.** If the input claim
`Σ_{x ∈ D^n} p(x) = c_0` is false, the verifier that `sumcheckSpec` derives accepts an output
`(c_n, r)` whose output claim `p(r) = c_n` is true with probability at most `n · (d / |R|)`. The
problems are the specification's `inputProblem` and `outputProblem`, which the stage's claim
formulas denote. -/
theorem sumcheckSpec_claimSound [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (sumcheckSpec R d n D).Sound ambient init impl (indexedDraw (R := R) (deg := d) n)
      (sumcheckSpec R d n D).inputProblem (sumcheckSpec R d n D).outputProblem
      ((n : ℝ≥0∞) * (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  Spec.ClaimSound.of_sound (fun _ => trivial)
    (fun x hl => (sumcheckSpec_InClaim_iff D x).mpr (by obtain ⟨_, h⟩ := hl; exact h))
    (sumcheckSpec_outputProblem_le D) (sumcheckSpec_sound D ambient init impl)

/-- **Round-by-round soundness of the sum-check specification on its own stage claims**, with
error `d / |R|` at every challenge, through the bridge. -/
theorem sumcheckSpec_claimRBRSound [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (sumcheckSpec R d n D).ClaimRBRSound ambient impl (indexedDraw (R := R) (deg := d) n)
      (fun _ => (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  rbrSound_of_kit (pre := []) (sumcheckSpec R d n D) ambient impl
    (sumcheckSpec R d n D).inputProblem (sumcheckSpec R d n D).outputProblem
    (indexedDraw (R := R) (deg := d) n) (scCert R d n) scStart
    (fun _ => scSpecStep D) scFinish (fun x i st => indexedRelation D i ⟨st.c.val, st.rs⟩ (x.2 ()))
    (fun _ => $ᵗ R) _ (sumcheckSpec_verdict_eq D) (fun _ => scCert_drawIs n 0 (Nat.zero_add n))
    (fun x _ _ _ hs h => by
      cases hs
      exact (sumcheckSpec_inputProblem_iff D x).mpr ⟨(), h⟩)
    (fun x p q o hf hl => by
      cases hf
      obtain ⟨_, hl⟩ := sumcheckSpec_outputProblem_le D p _ hl
      exact (indexedRelation_last D _ (x.2 ())).mpr hl)
    (fun x => scSpec_roundSound D (x.2 ()))

/-- **Completeness of the sum-check specification on its own stage claims.** With the input
polynomial as the witness, if the input claim holds, every check holds on the honest values and
the output claim holds on every honest transcript. -/
theorem sumcheckSpec_claimComplete (D : Fin k → R) :
    (sumcheckSpec R d n D).ClaimComplete fun x w => w = x.2 () := by
  rintro x w rfl hin
  exact ⟨sumcheckSpec_complete D x hin, fun tr hh => by
    unfold Spec.OutClaim
    rw [sumcheckSpec_outClaim_of_honest D x hin tr hh]
    rfl⟩

/-- **The stage contract of sum-check**: soundness with error `n · (d / |R|)` and completeness,
both on the stage's own claims. -/
theorem sumcheckSpec_contract [IsDomain R] [Fintype R] [SampleableType R] (D : Fin k → R)
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (sumcheckSpec R d n D).StageContract ambient init impl (indexedDraw (R := R) (deg := d) n)
      ((n : ℝ≥0∞) * (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) (fun x w => w = x.2 ()) :=
  ⟨sumcheckSpec_claimSound D ambient init impl, sumcheckSpec_claimComplete D⟩

end Specs.Claims

#print axioms Specs.Claims.sum_tuples
#print axioms Specs.Claims.roundSum_zero
#print axioms Specs.Claims.sumcheckSpec_InClaim_iff
#print axioms Specs.Claims.sumcheckSpec_outClaim_of_verdict
#print axioms Specs.Claims.sumcheckSpec_outputProblem_le
#print axioms Specs.Claims.sumcheckSpec_complete
#print axioms Specs.Claims.sumcheckSpec_outClaim_of_honest
#print axioms Specs.Claims.sumcheckSpec_claimSound
#print axioms Specs.Claims.sumcheckSpec_claimRBRSound
#print axioms Specs.Claims.sumcheckSpec_claimComplete
#print axioms Specs.Claims.sumcheckSpec_contract
