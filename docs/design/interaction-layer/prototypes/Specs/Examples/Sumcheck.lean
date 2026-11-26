/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Run
import ArkLib.ProofSystem.Sumcheck.IntervalCompleteness
import ArkLib.ProofSystem.Sumcheck.Indexed

/-!
# Sum-check as a specification

This module writes sum-check with formulas and proves that it agrees with ArkLib's sum-check.

* `sumcheckRound` is one round and `sumcheck` the `n`-round loop. Other examples reuse `sumcheck`
  inside larger protocols.
* `sumcheckSpec R d n D` is the full protocol: it reads the input polynomial `p`, states the input
  claim `Σ_{x ∈ D^n} p(x) = c_0` and the output claim `p(r) = c_n`, and runs the loop.
* Agreement with ArkLib: the tree is `Sumcheck.protocol R d n` (`sumcheck_tree`), the honest
  prover is `intervalProver` (`sumcheck_prover`), the verdict is `indexedVerdict`
  (`sumcheck_verdict`), the decision of `Spec.verifier` agrees with `indexedVerifier` on every
  transcript (`sumcheck_decide`), and both keep the input polynomial (`sumcheck_outputMap`).
* `prove_roundsGo` and `verdict_roundsGo` are the round inductions behind `sumcheck_prover` and
  `sumcheck_verdict`. `Claim.toIndexed` turns a claim after `j` rounds into ArkLib's indexed claim.
* The tests check the transcript accessors (`tr⟦sumcheck, 1, g⟧`), the folded and expanded TeX of
  the round check, and that the first-order form of the round check evaluates like the formula.

## Design choices

* `sumcheckSpec` names ArkLib's tree family for its rounds (`tree := …`). *Why:* the statements of
  the agreement theorems then typecheck at a variable `n` with no cast. The loop `sumcheck` keeps
  the default tree, and `roundsTree_sumcheck` proves by induction that the two agree.
* The claim between rounds is a structure of handles: the target `c_i` as a named value and the
  challenges so far. *Why:* the target's name carries the round, so the check and the local value
  print as `c_{i}` and `c_{i+1}`.
* `sumcheck_decide` follows from the generic theorem `Spec.decide_eq_verdict` and
  `sumcheck_verdict`. The only sum-check-specific induction is `verdict_roundsGo`, which compares
  two pure functions on transcripts.
* The private lemmas `eval_round_value` and `eval_round_check` evaluate the two round formulas
  by `rfl` at their exact hole lists. *Why:* `simp` and `rw` time out on `Curry.app`, because the
  formula is a `Curry` function only after unfolding.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec Polynomial MvPolynomial

section Sumcheck

instance : TypeName ℚ := ⟨"\\mathbb{F}"⟩

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k : ℕ}

instance : TypeName (R⦃≤ d⦄[X]) := ⟨TypeName.name R ++ "_{\\le " ++ toString d ++ "}[X]"⟩

/-- The default answer of a handle over a ring. -/
local instance : Inhabited R := ⟨0⟩

/-- The claim after `i` rounds: the target `c_i` and the challenges `r_{<i}`. -/
structure Claim (R : Type) (i : ℕ) where
  /-- The current target. -/
  c : Val (ix "c" i) R
  /-- The challenges so far. -/
  rs : Fin i → R

variable {In : OracleBundle} {W T : Type}

/-- Round `i` of sum-check over the domain `D` for the polynomial `poly w`. -/
noncomputable def sumcheckRound (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n])
    {t : OracleProtocol} {ks : Skel} (i : ℕ) (hi : i < n) (st : Claim R i)
    (next : Claim R (i + 1) → Desc In W T t ks) :=
  oracle (ix "g" i) (R⦃≤ d⦄[X]) R "\\mathsf{proj}"
    (fun w => Sumcheck.projectedRoundPolynomial D ⟨i, hi⟩ st.rs (poly w)) fun g =>
  check "sum" ⟪g, st.c⟫ (fun g c => (∑∈ a ∈ Dom.ofFn "D" D, ask g a) =' .var c) <|
  challenge (ix "r" i) R fun r =>
  compute (ix "c" (i + 1)) R ⟪g, r⟫ (fun g r => ask g r) fun c =>
  next ⟨c, Fin.snoc st.rs r.val⟩

/-- The tree of one sum-check round followed by `t`. -/
abbrev roundTree (R : Type) [CommSemiring R] (d : ℕ) (t : OracleProtocol) : OracleProtocol :=
  .liftBind (.oracle (R⦃≤ d⦄[X]) inferInstance) fun _ => .liftBind (.challenge R) fun _ => t

/-- Sum-check: `n` rounds from the claim `input`. `tree` names the tree family of the rounds. -/
noncomputable abbrev sumcheck (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n])
    (input : Claim R 0) {t : OracleProtocol} {ks : Skel} (next : Claim R n → Desc In W T t ks)
    (tree : ℕ → ℕ → OracleProtocol := roundsTree (fun _ => roundTree R d) t)
    (h0 : ∀ j, tree j 0 = t := by intros; rfl)
    (hS : ∀ j k, tree j (k + 1) = roundTree R d (tree (j + 1) k) := by intros; rfl) :=
  rounds "sumcheck" n input (sumcheckRound n D poly) next (fun _ => toString d ++ "/|F|") "n"
    tree h0 hS

omit [DecidableEq R] [TypeName R] in
/-- The tree of the loop is ArkLib's sum-check tree. -/
theorem roundsTree_sumcheck (j r : ℕ) :
    roundsTree (fun _ => roundTree R d) (.pure ⟨⟩) j r = Sumcheck.protocol R d r := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih => exact congrArg (roundTree R d) (ih (j + 1))

variable (R) in
/-- The sum-check specification over the domain `D`: the statement is the input claim, the
witness and the input oracle are the polynomial. -/
noncomputable def sumcheckSpec (d n : ℕ) (D : Fin k → R) :=
  Spec.mk (In := Sumcheck.polynomialFamily R n d) (W := R⦃≤ d⦄[X Fin n])
    (T := Sumcheck.RoundStatement R n (Fin.last n)) fun stmt : Sumcheck.RoundStatement R n 0 =>
  input "p" (Fin n → R) R "R_{\\le d}[X_{1..n}]" (fun x => ⟨(), x⟩) (fun _ => rfl) fun p =>
  stage "sumcheck" ⟪p, (⟨stmt.target⟩ : Val (ix "c" 0) R)⟫
    (fun p c => (∑∈ x ∈ (Dom.ofFn "D" D).pow n "n", ask p x) =' .var c)
    (fun st : Claim R n => ⟪p, (⟨st.rs⟩ : Val "r" (Fin n → R)), st.c⟫)
    (fun p r c => ask p r =' .var c)
    (fun next => sumcheck n D id ⟨⟨stmt.target⟩, stmt.challenges⟩ next
      (tree := fun _ r => Sumcheck.protocol R d r))
    fun st => done ⟨st.c.val, st.rs⟩

/-- The tree of the specification is ArkLib's sum-check tree. -/
theorem sumcheck_tree (d n : ℕ) (D : Fin k → R) :
    Spec.tree (sumcheckSpec R d n D) = Sumcheck.protocol R d n := rfl

/-- ArkLib's claim with `r` rounds left after the `j` rounds of `st`. -/
def Claim.toIndexed {n j r : ℕ} (h : j + r = n) (st : Claim R j) :
    Sumcheck.IndexedClaim R n r :=
  ⟨⟨j, by omega⟩, h, ⟨st.c.val, st.rs⟩⟩

omit [DecidableEq R] [TypeName R] in
/-- The local value `g_i(r_i)` of a round evaluates by one query to `g_i`. -/
private theorem eval_round_value (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (OracleInterface.Query (R⦃≤ d⦄[X])) R) (c : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := R)
      (Γ := [Hole.orc nm (OracleInterface.Query (R⦃≤ d⦄[X])) R] ++ [Hole.val nm' R])
      (fun g r => ask g r) (Args.orc h (Args.val c Args.nil))) = ask' h c := rfl

open Sumcheck in
/-- The honest prover of the rounds `j, …, j + r - 1` is ArkLib's interval prover from the
corresponding claim, for any continuation that returns the final claim. -/
theorem prove_roundsGo {n : ℕ} (D : Fin k → R) (p : R⦃≤ d⦄[X Fin n]) {m : Type → Type}
    [Monad m] (ans : QueryImpl (Sumcheck.polynomialFamily R n d).spec Id)
    {ks : Skel} (next : Claim R n → Desc (Sumcheck.polynomialFamily R n d) (R⦃≤ d⦄[X Fin n])
      (RoundStatement R n (Fin.last n)) (Sumcheck.protocol R d 0) ks)
    (hnext : ∀ st env ℓ, (next st).prove (m := m) p ans env ℓ = (pure ⟨st.c.val, st.rs⟩ : m _)) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (env : Handlers Id) (ℓ : ℕ),
    Desc.prove (m := m) p ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => Sumcheck.protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) env ℓ =
      intervalProver D p r (Claim.toIndexed h st)
  := by
  intro r
  induction r with
  | zero =>
    intro j h st env ℓ
    subst h
    exact hnext st env ℓ
  | succ r ih =>
    intro j h st env ℓ
    rw [roundsGo]
    simp only [Desc.retree_rfl]
    rw [sumcheckRound]
    simp only [oracle, check, challenge, compute]
    erw [Desc.prove.eq_11, Desc.prove.eq_3]
    erw [Desc.prove.eq_5, Desc.prove.eq_4]
    simp only [Desc.prove.eq_6, Desc.prove.eq_11, ih]
    simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
      Args.append, eval_round_value, askId, Handlers.find_ext_self]
    rfl

omit [TypeName R] in
/-- The round check `Σ_{a ∈ D} g_i(a) = c_i` evaluates to a sum over the domain indices. -/
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

open Sumcheck in
/-- The verdict of the rounds `j, …, j + r - 1` is ArkLib's indexed verdict from the corresponding
claim, for any continuation that accepts with the final claim. -/
theorem verdict_roundsGo {n : ℕ} (D : Fin k → R) (ans : QueryImpl (polynomialFamily R n d).spec Id)
    {ks : Skel} (next : Claim R n → Desc (polynomialFamily R n d) (R⦃≤ d⦄[X Fin n])
      (RoundStatement R n (Fin.last n)) (protocol R d 0) ks)
    (hnext : ∀ st tr env ℓ, (next st).verdict ans tr env ℓ = some ⟨st.c.val, st.rs⟩) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (tr : Transcript oracleSig (protocol R d r))
      (env : Handlers Id) (ℓ : ℕ),
    Desc.verdict ans (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|")
        (sumcheckRound n D id) next (fun _ r => protocol R d r) (fun _ => rfl)
        (fun _ _ => rfl) r j h st) tr env ℓ =
      indexedVerdict D r (some (Claim.toIndexed h st)) tr := by
  intro r
  induction r with
  | zero =>
    intro j h st tr env ℓ
    subst h
    exact hnext st tr env ℓ
  | succ r ih =>
    intro j h st tr env ℓ
    rw [indexedVerdict_succ]
    obtain ⟨g, x, tr⟩ := tr
    rw [roundsGo]
    simp only [Desc.retree_rfl]
    rw [sumcheckRound]
    simp only [oracle, check, challenge, compute]
    erw [Desc.verdict.eq_11, Desc.verdict.eq_3, Desc.verdict.eq_5]
    simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
      Args.append, eval_round_check, askId, Handlers.find_ext_self]
    erw [Desc.verdict.eq_4, Desc.verdict.eq_6, Desc.verdict.eq_11, ih]
    simp only [Closed.inst, eval_round_value, askId, Handlers.find_ext_self]
    unfold indexedNext
    simp only [Option.bind_some]
    dsimp only [Interpreted.message, Interpreted.challenge, Interpreted.tail, Claim.toIndexed,
      Desc.honestEntry, Id.run_pure, cast_eq, OracleInterface.instPolynomialDegreeLE]
    by_cases hc : ∑ a, Polynomial.eval (D a) g.val = st.c.val
    · simp only [hc, decide_true, ↓reduceIte]
      rfl
    · simp only [hc, decide_false, ↓reduceIte, Bool.false_eq_true]
      rfl

open Sumcheck in
/-- The honest prover of the specification is ArkLib's honest interval prover. -/
theorem sumcheck_prover {n : ℕ} (D : Fin k → R) (stmt : RoundStatement R n 0)
    (p : R⦃≤ d⦄[X Fin n]) (data : (polynomialFamily R n d).Data) {m : Type → Type} [Monad m] :
    Spec.prover (m := m) (sumcheckSpec R d n D) stmt p data =
      intervalProver D p n (IndexedClaim.initial stmt) :=
  prove_roundsGo D p _ _ (fun _ _ _ => rfl) n 0 (Nat.zero_add n) _ _ _

open Sumcheck in
/-- The verdict of the specification is ArkLib's indexed verdict. -/
theorem sumcheck_verdict {n : ℕ} (D : Fin k → R) (stmt : RoundStatement R n 0)
    (data : (polynomialFamily R n d).Data) (tr : Transcript oracleSig (protocol R d n)) :
    Spec.verdict (sumcheckSpec R d n D) stmt data tr =
      indexedVerdict D n (some (IndexedClaim.initial stmt)) tr :=
  verdict_roundsGo D _ _ (fun _ _ _ _ => rfl) n 0 (Nat.zero_add n) _ tr _ _

open Sumcheck in
/-- On every transcript, the decision of the specification's verifier agrees with ArkLib's
`indexedVerifier` once the oracle queries are answered from the input data and the transcript. -/
theorem sumcheck_decide {n : ℕ} (D : Fin k → R) {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n d i)
    (tr : Transcript oracleSig (protocol R d n)) :
    simulateQ (QueryImpl.addLift (r := m) impl ((pathBundle (polynomialFamily R n d)
        (protocol R d n) tr.path).answer (data, oracleMessages _ tr)))
      ((Spec.verifier (sumcheckSpec R d n D) ambient).decide stmt _ (toView _ tr)).run =
    simulateQ (QueryImpl.addLift (r := m) impl ((pathBundle (polynomialFamily R n d)
        (protocol R d n) tr.path).answer (data, oracleMessages _ tr)))
      ((indexedVerifier R d n D ambient).decide stmt _ (toView _ tr)).run := by
  rw [Spec.decide_eq_verdict, simulateQ_indexedVerifier_decide, sumcheck_verdict]

open Sumcheck in
/-- Both verifiers keep the input polynomial as their output oracle. -/
theorem sumcheck_outputMap {n : ℕ} (D : Fin k → R) {ι : Type} (ambient : OracleSpec ι) :
    (Spec.verifier (sumcheckSpec R d n D) ambient).outputMap =
      (indexedVerifier R d n D ambient).outputMap := rfl

/-! ### Tests -/

section Tests
variable (D : Fin 2 → ℚ)

/-- The transcripts of the specification are ArkLib's sum-check transcripts. -/
example : (sumcheckSpec ℚ 2 3 D).Tr = Transcript oracleSig (Sumcheck.protocol ℚ 2 3) := rfl

/-- The polynomial `g_1` of round 1 by its label, and the challenge `r_2`. -/
example (tr : (sumcheckSpec ℚ 2 3 D).Tr) : tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl
example (tr : (sumcheckSpec ℚ 2 3 D).Tr) : tr⟦sumcheck, 2, r⟧ = tr.2.2.2.2.2.1 := by simp
example (tr : (sumcheckSpec ℚ 2 3 D).Tr) : tr⟦g⟧ = tr.1 := rfl

/-- The accessor works on a view of the verifier. -/
example (p : Path (sumcheckSpec ℚ 2 3 D).tree) (v : (sumcheckSpec ℚ 2 3 D).Vw p) :
    v⟦sumcheck, 1, g⟧ = v.1.2.2.1 := rfl

/-! The round check prints folded with the round variable `i`, and expanded with the round. -/
#guard ((sumcheckSpec ℚ 2 3 ![0, 1]).skeleton.checks.map fun c => c.2.tex
    { folded := true, round := some 1 }) ==
  ["\\sum_{a \\in D} g_{i-1}(a) = c_{i-1}", "\\sum_{a \\in D} g_{i}(a) = c_{i}",
    "\\sum_{a \\in D} g_{i+1}(a) = c_{i+1}"]
#guard ((sumcheckSpec ℚ 2 3 ![0, 1]).skeleton.checks.map fun c => c.2.tex Mode.expanded) ==
  ["\\sum_{a \\in D} g_{0}(a) = c_{0}", "\\sum_{a \\in D} g_{1}(a) = c_{1}",
    "\\sum_{a \\in D} g_{2}(a) = c_{2}"]

/-- The round check of round 1 over `ℚ` with `D = {0, 1}`, written again as a closed formula. The
first test shows that its syntax is the check that the skeleton exports. -/
private def roundCheck : Closed [.orc (ix "g" 1) ℚ ℚ, .val (ix "c" 1) ℚ] Bool :=
  ⟨fun g c => (∑∈ a ∈ Dom.ofFn "D" ![(0 : ℚ), 1], ask g a) =' .var c⟩

#guard roundCheck.syntax == ((sumcheckSpec ℚ 2 3 ![0, 1]).skeleton.checks[1]!).2

open Classical in
/-- An environment for the first-order tree: `c_1` is `x`, and `g_1` answers by `f`. -/
private noncomputable def roundEnv (f : ℚ → ℚ) (x : ℚ) : Env :=
  Env.bind ⟨fun _ _ => none, fun nm Q A =>
    if h : nm = ix "g" 1 ∧ Q = ℚ ∧ A = ℚ then some (by obtain ⟨-, rfl, rfl⟩ := h; exact f)
    else none⟩ (ix "c" 1) x

/-- The exported first-order tree of the round check evaluates as the check itself does. -/
example (f : ℚ → ℚ) (x : ℚ) :
    (roundCheck.inst (Hole.names _)).toFO.eval (roundEnv f x) =
      some ((roundCheck.inst (v := fun α => α) (o := fun Q A => Q → A)
        (.orc f (.val x .nil))).eval fun ⦃_ _⦄ h q => h q) := by
  change FO.eval (roundEnv f x) (Fml.toFO (((∑∈ a ∈ Dom.ofFn "D" ![(0 : ℚ), 1],
      ask (v := NameV) (o := NameO) (Q := ℚ) (A := ℚ) (ix "g" 1) a) =' .var (ix "c" 1)))) =
    some (Fml.eval (fun ⦃_ _⦄ h q => h q) ((∑∈ a ∈ Dom.ofFn "D" ![(0 : ℚ), 1],
      ask (v := fun α => α) (o := fun Q A => Q → A) f a) =' .var x))
  simp [roundEnv, Env.bind, FO.eval, Fml.toFO, Dom.ofFn, List.ofFn_succ]

end Tests

end Sumcheck

#print axioms sumcheck_tree
#print axioms sumcheck_prover
#print axioms sumcheck_verdict
#print axioms sumcheck_decide
#print axioms sumcheck_outputMap

end Specs
