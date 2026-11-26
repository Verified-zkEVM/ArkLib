/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Examples.Sumcheck

/-!
# A protocol whose shape depends on a prover message

This module writes a protocol in which a plain prover message selects the shape of the rest.

* `branchingSpec R d D`: the statement is a target `c`. The prover sends the number of variables
  `m : Fin 4` with `branch`, then a polynomial `p` in `m` variables as an oracle message. The stage
  `sumcheck` reduces `Σ_{x ∈ D^m} p(x) = c_0` to `p(r) = c_m` with the loop `sumcheck` of
  `Specs.Examples.Sumcheck`, and the check `final` queries `p` at `r`.
* `branching_tree`: the tree is the message `m`, the oracle `p` and ArkLib's `m`-round sum-check
  tree `Sumcheck.protocol R d m`. Lean proves it by `rfl`.
* `branching_verdict_isSome`: if the witness polynomial sums to `c` over `D^m`, the verdict accepts
  every honest transcript. It applies the generic `Spec.verdict_isSome`.
* `sumcheck_complete`: every check of the sum-check loop holds on the honest messages, for any
  continuation that is complete when its claim holds. `Frozen` states that the handler table keeps
  the oracles recorded before the loop, so a continuation can still query them. Spartan uses both.
* `roundsGo_complete`: a `rounds` block is complete if each round preserves an invariant of the
  state, the handler table and the level. FRI uses it for its three blocks.
* The tests read the branching message by its label (`tr⟦m⟧`) and check that the skeleton has one
  case per value of `m` with the expected checks in expanded TeX.

This module proves no soundness statement. The protocol demonstrates the shape mechanism only: the
prover chooses `p`, so the claim it proves holds for every `c` that some polynomial sums to.

## Design choices

* The prover sends `p` as an oracle message after `m`. *Why:* the type of `p` depends on `m`, and
  an input bundle is fixed before the prover sends `m`.
* The honest functions read the whole witness `⟨m, p⟩`, so the honest oracle message of case `m`
  is `polyAt m w`, which is `p` when `m` matches and `0` in the cases the honest prover never
  takes (`polyAt_self`).
* The accessor addresses only the branching message. *Why:* the accessor stops at a branch, since
  the transcript type after it depends on the message. Lean reports for `tr⟦p⟧`: "the label is not
  found before a branch; a label inside a branch is not supported".
* `sumcheck_complete` belongs in `Specs.Examples.Sumcheck`, and `roundsGo_complete` in
  `Specs.Run`. They live here because this task may not edit those modules.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec Polynomial MvPolynomial

section Branching

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k : ℕ}

/-- The default answer of a handle over a ring. -/
local instance : Inhabited R := ⟨0⟩

variable {In : OracleBundle} {W T : Type}

/-! ## Completeness of the sum-check loop -/

section Retree
variable {w : W} {ans : QueryImpl In.spec Id}

/-- Moving a description to an equal tree keeps its completeness condition. -/
theorem Desc.complete_retree {t t' : OracleProtocol} {ks : Skel} (h : t = t')
    (d : Desc In W T t ks) (env : Handlers Id) (ℓ : ℕ) :
    (d.retree h).Complete w ans env ℓ ↔ d.Complete w ans env ℓ := by
  subst h; rfl

end Retree

omit [TypeName R] in
/-- The round check `Σ_{a ∈ D} g_i(a) = c_i` evaluates to a sum over the domain indices. -/
private theorem eval_round_check' (D : Fin k → R) (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (OracleInterface.Query (R⦃≤ d⦄[X])) R) (x : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := Bool)
      (Γ := [Hole.orc nm (OracleInterface.Query (R⦃≤ d⦄[X])) R] ++ [Hole.val nm' R])
      (fun g c => (∑∈ a ∈ Dom.ofFn "D" D, ask g a) =' .var c)
      (Args.orc h (Args.val x Args.nil))) = decide (∑ a : Fin k, ask' h (D a) = x) := by
  change Fml.eval ask' ((∑∈ a ∈ Dom.ofFn "D" D, ask h a) =' .var x) = _
  simp only [Fml.eval_eq, Fml.eval_sum, Fml.eval_query, Fml.eval_var, Dom.ofFn, List.map_ofFn,
    List.sum_ofFn]
  rfl

omit [DecidableEq R] [TypeName R] in
/-- The local value `g_i(r_i)` of a round evaluates by one query to `g_i`. -/
private theorem eval_round_value' (ask' : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A)
    {nm nm' : Name} (h : Ref (OracleInterface.Query (R⦃≤ d⦄[X])) R) (c : R) :
    Fml.eval ask' (Curry.app (v := fun α => α) (o := Ref) (β := R)
      (Γ := [Hole.orc nm (OracleInterface.Query (R⦃≤ d⦄[X])) R] ++ [Hole.val nm' R])
      (fun g r => ask g r) (Args.orc h (Args.val c Args.nil))) = ask' h c := rfl

/-- **Completeness of the sum-check loop.** If the claim `c_j` of the rounds `j, …, n - 1` is the
remaining sum of `poly w` over the domain, every check of these rounds holds on the honest
messages, for every choice of challenges, provided the continuation is complete whenever its
claim `p(r) = c_n` holds. `P` is any invariant of the handler table that survives the oracle
messages of the rounds, so the continuation can still read the oracles recorded before. -/
theorem sumcheck_complete {n : ℕ} (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n]) (w : W)
    (ans : QueryImpl In.spec Id) {t : OracleProtocol} {ks : Skel}
    (next : Claim R n → Desc In W T t ks) (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = t)
    (hS : ∀ j k, τ j (k + 1) = roundTree R d (τ (j + 1) k))
    (P : Handlers Id → ℕ → Prop)
    (hP : ∀ env ℓ {Q A : Type} (f : Q → Id A), P env ℓ → P (env.ext ℓ f) (ℓ + 1))
    (hnext : ∀ st env ℓ, P env ℓ → (poly w).val.eval st.rs = st.c.val →
      (next st).Complete w ans env ℓ) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (env : Handlers Id) (ℓ : ℕ), P env ℓ →
      Sumcheck.roundSum D ⟨j, by omega⟩ st.rs (poly w).val = st.c.val →
      (roundsGo "sumcheck" n "n" (fun _ => toString d ++ "/|F|") (sumcheckRound n D poly) next
        τ h0 hS r j h st).Complete w ans env ℓ := by
  intro r
  induction r with
  | zero =>
    intro j h st env ℓ hp hs
    subst h
    rw [roundsGo, Desc.complete_retree]
    refine hnext st env ℓ hp ?_
    exact (Sumcheck.indexedRelation_last D ⟨st.c.val, st.rs⟩ (poly w)).1 hs
  | succ r ih =>
    intro j h st env ℓ hp hs
    rw [roundsGo, Desc.complete_retree]
    rw [sumcheckRound]
    simp only [oracle, check, challenge, compute]
    erw [Desc.Complete.eq_11, Desc.Complete.eq_3, Desc.Complete.eq_5, Desc.Complete.eq_4]
    simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
      Args.append, eval_round_check', askId, Handlers.find_ext_self]
    refine ⟨?_, fun r => ?_⟩
    · dsimp only [Desc.honestEntry, Id.run_pure, cast_eq,
        OracleInterface.instPolynomialDegreeLE]
      exact decide_eq_true ((Sumcheck.sum_projectedRoundPolynomial D ⟨j, by omega⟩ st.rs
        (poly w)).trans hs)
    · erw [Desc.Complete.eq_6]
      simp only [Closed.inst, eval_round_value', askId, Handlers.find_ext_self]
      erw [Desc.Complete.eq_11]
      refine ih (j + 1) (by omega) _ _ _ (hP _ _ _ hp) ?_
      dsimp only [Desc.honestEntry, Id.run_pure, cast_eq,
        OracleInterface.instPolynomialDegreeLE]
      exact Sumcheck.roundSum_succ D ⟨j, by omega⟩ st.rs (poly w) r

/-- **Completeness of a `rounds` block.** If every round is complete whenever its continuation is
complete, the block is complete. `I i st env ℓ` is an invariant of the state before round `i`
together with the handler table and the next level. -/
theorem roundsGo_complete {State : ℕ → Type} {F : ℕ → OracleProtocol → OracleProtocol}
    {G : ℕ → Skel → Skel} (block : String) (n : ℕ) (countName : String) (error : ℕ → String)
    (body : ∀ {t : OracleProtocol} {ks : Skel}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc In W T t ks) → Desc In W T (F i t) (G i ks))
    {t : OracleProtocol} {ks : Skel} (next : State n → Desc In W T t ks)
    (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = t)
    (hS : ∀ j k, τ j (k + 1) = F j (τ (j + 1) k)) (w : W) (ans : QueryImpl In.spec Id)
    (I : (i : ℕ) → State i → Handlers Id → ℕ → Prop)
    (hbody : ∀ {t' : OracleProtocol} {ks' : Skel} (i : ℕ) (hi : i < n) (st : State i)
      (next' : State (i + 1) → Desc In W T t' ks') (env : Handlers Id) (ℓ : ℕ), I i st env ℓ →
      (∀ st' env' ℓ', I (i + 1) st' env' ℓ' → (next' st').Complete w ans env' ℓ') →
      (body i hi st next').Complete w ans env ℓ)
    (hnext : ∀ st env ℓ, I n st env ℓ → (next st).Complete w ans env ℓ) :
    ∀ (r j : ℕ) (h : j + r = n) (st : State j) (env : Handlers Id) (ℓ : ℕ), I j st env ℓ →
      (roundsGo block n countName error body next τ h0 hS r j h st).Complete w ans env ℓ := by
  intro r
  induction r with
  | zero =>
    intro j h st env ℓ hI
    subst h
    rw [roundsGo, Desc.complete_retree]
    exact hnext _ env ℓ hI
  | succ r ih =>
    intro j h st env ℓ hI
    rw [roundsGo, Desc.complete_retree]
    erw [Desc.Complete.eq_11]
    refine hbody j (by omega) st _ env ℓ hI fun st' env' ℓ' hI' => ?_
    erw [Desc.Complete.eq_11]
    exact ih (j + 1) (by omega) st' env' ℓ' hI'

/-! ## Handler tables that keep the earlier levels -/

/-- The table `env` at level `ℓ` agrees with `env₀` on every level below `ℓ₀`, and `ℓ₀ ≤ ℓ`. Later
oracle messages record at levels `ℓ ≥ ℓ₀`, so they keep this property. -/
def Frozen (env₀ : Handlers Id) (ℓ₀ : ℕ) (env : Handlers Id) (ℓ : ℕ) : Prop :=
  ℓ₀ ≤ ℓ ∧ ∀ i < ℓ₀, env i = env₀ i

theorem Frozen.refl (env₀ : Handlers Id) (ℓ₀ : ℕ) : Frozen env₀ ℓ₀ env₀ ℓ₀ :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem Frozen.ext {env₀ : Handlers Id} {ℓ₀ : ℕ} (env : Handlers Id) (ℓ : ℕ) {Q A : Type}
    (f : Q → Id A) (h : Frozen env₀ ℓ₀ env ℓ) : Frozen env₀ ℓ₀ (env.ext ℓ f) (ℓ + 1) := by
  refine ⟨by have := h.1; omega, fun i hi => ?_⟩
  have hne : i ≠ ℓ := by have := h.1; omega
  simp only [Handlers.ext, hne, ite_false]
  exact h.2 i hi

/-- A frozen level answers as in `env₀`. -/
theorem Frozen.find {env₀ : Handlers Id} {ℓ₀ : ℕ} {env : Handlers Id} {ℓ : ℕ}
    (h : Frozen env₀ ℓ₀ env ℓ) {i : ℕ} (hi : i < ℓ₀) {Q A : Type} (dflt : A) (q : Q) :
    env.find dflt i q = env₀.find dflt i q := by
  simp only [Handlers.find, h.2 i hi]

omit [DecidableEq R] [TypeName R] in
/-- The sum of the first round is the sum of `p` over the whole domain. -/
theorem roundSum_zero {n : ℕ} (D : Fin k → R) (p : MvPolynomial (Fin n) R) :
    Sumcheck.roundSum D 0 Fin.elim0 p = ∑ x : Fin n → Fin k, p.eval (D ∘ x) := by
  refine Finset.sum_congr rfl fun x _ => congrArg (fun f => MvPolynomial.eval f p) ?_
  funext i
  simp [Fin.append, Fin.addCases]
  rfl

/-! ## The specification -/

/-- The witness: a number of variables `m < 4` and a polynomial in `m` variables. -/
abbrev BranchWitness (R : Type) [CommSemiring R] (d : ℕ) : Type := (m : Fin 4) × R⦃≤ d⦄[X Fin m]

/-- The output: the number of variables, the challenges and the final target. -/
abbrev BranchOutput (R : Type) : Type := (m : ℕ) × (Fin m → R) × R

instance {m : ℕ} : TypeName (R⦃≤ d⦄[X Fin m]) :=
  ⟨TypeName.name R ++ "_{\\le " ++ toString d ++ "}[X_1, \\dots, X_{" ++ toString m ++ "}]"⟩

/-- The polynomial of the witness if it has `m` variables, and `0` otherwise. -/
noncomputable def polyAt (m : Fin 4) (w : BranchWitness R d) : R⦃≤ d⦄[X Fin m] :=
  if h : w.1 = m then h ▸ w.2 else 0

omit [DecidableEq R] [TypeName R] in
theorem polyAt_self (w : BranchWitness R d) : polyAt w.1 w = w.2 := by
  simp [polyAt]

variable (R) in
/-- Sum-check with a prover-chosen number of variables. The statement is the target `c`. The prover
sends the number of variables `m : Fin 4` as a plain message, then a polynomial `p` in `m`
variables as an oracle. The stage `sumcheck` reduces the claim `Σ_{x ∈ D^m} p(x) = c_0` to
`p(r) = c_m` by `m` rounds, and the final check queries `p` at `r`. -/
noncomputable def branchingSpec (d : ℕ) (D : Fin k → R) :=
  Spec.mk (In := OracleBundle.empty) (W := BranchWitness R d) (T := BranchOutput R) fun c : R =>
  branch "m" (Fin 4) "\\mathsf{arity}" (fun w => w.1)
    [("0", 0), ("1", 1), ("2", 2), ("3", 3)] fun m =>
  oracle "p" (R⦃≤ d⦄[X Fin m.val]) R "\\mathsf{poly}" (polyAt m.val) fun p =>
  stage "sumcheck" ⟪p, (⟨c⟩ : Val (ix "c" 0) R)⟫
    (fun p c => (∑∈ x ∈ (Dom.ofFn "D" D).pow m.val "m", ask p x) =' .var c)
    (fun st : Claim R m.val => ⟪p, (⟨st.rs⟩ : Val "r" (Fin m.val → R)), st.c⟫)
    (fun p r c => ask p r =' .var c)
    (fun next => sumcheck m.val D (polyAt m.val) ⟨⟨c⟩, Fin.elim0⟩ next
      (tree := fun _ r => Sumcheck.protocol R d r))
    fun st =>
  check "final" ⟪p, (⟨st.rs⟩ : Val "r" (Fin m.val → R)), st.c⟫ (fun p r c => ask p r =' .var c) <|
  done ⟨m.val, st.rs, st.c.val⟩

variable (R) in
/-- The expected tree: the message `m`, the oracle `p` in `m` variables, and ArkLib's `m`-round
sum-check tree. -/
noncomputable abbrev branchingTree (d : ℕ) : OracleProtocol :=
  .liftBind (.message (Fin 4)) fun (m : Fin 4) =>
    .liftBind (.oracle (R⦃≤ d⦄[X Fin m]) inferInstance) fun _ => Sumcheck.protocol R d m

/-- The tree of the specification is the expected tree. -/
theorem branching_tree (d : ℕ) (D : Fin k → R) :
    (branchingSpec R d D).tree = branchingTree R d := rfl

/-- **Honest acceptance.** If the polynomial of the witness sums to `c` over `D^m`, the verdict
accepts every transcript of the honest prover. -/
theorem branching_verdict_isSome (D : Fin k → R) (c : R) (w : BranchWitness R d)
    (data : OracleBundle.empty.Data) (tr : (branchingSpec R d D).Tr)
    (hsum : ∑ x : Fin w.1 → Fin k, w.2.val.eval (D ∘ x) = c)
    (hh : ((branchingSpec R d D).desc c).Honest w (OracleBundle.empty.answer data) tr .empty 0) :
    ((branchingSpec R d D).verdict c data tr).isSome := by
  refine Spec.verdict_isSome _ c w data tr ?_ hh
  unfold branchingSpec
  erw [Desc.Complete.eq_8, Desc.Complete.eq_3, Desc.Complete.eq_9]
  refine sumcheck_complete D (polyAt w.1) w _ _ _ _ _ (Frozen _ 1) Frozen.ext ?_ _ 0 _ _ _ _
    (Frozen.refl _ _) ?_
  · intro st env ℓ hp hev
    erw [Desc.Complete.eq_10, Desc.Complete.eq_5]
    refine ⟨?_, trivial⟩
    simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
      Args.append]
    change decide ((env.find (default : R) 0 st.rs).run = st.c.val) = true
    rw [hp.find (by omega), Handlers.find_ext_self]
    exact decide_eq_true hev
  · change Sumcheck.roundSum D 0 Fin.elim0 (polyAt w.1 w).val = c
    rw [polyAt_self, roundSum_zero]
    exact hsum

/-! ### Tests -/

section Tests

/-- The branching message by its label. -/
example (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) : tr⟦m⟧ = tr.1 := rfl

/-- The labels and expanded TeX of the checks of each case of the skeleton. -/
def caseChecks (ks : Skel) (mode : Mode) : List (String × List (String × String)) :=
  match ks with
  | .branch _ _ _ cases =>
    cases.map fun (c : String × Skel) =>
      (c.1, c.2.checks.map fun (e : String × Syn) => (e.1, e.2.tex mode))
  | _ => []

/-! The skeleton has one case per value of `m`. The case `m = j` has `j` round checks and the final
check, and its final check reads the target `c_j`. -/
#guard caseChecks (branchingSpec ℚ 2 ![(0 : ℚ), 1]).skeleton Mode.expanded ==
  [("0", [("final", "p(r) = c_{0}")]),
   ("1", [("sum", "\\sum_{a \\in D} g_{0}(a) = c_{0}"), ("final", "p(r) = c_{1}")]),
   ("2", [("sum", "\\sum_{a \\in D} g_{0}(a) = c_{0}"),
     ("sum", "\\sum_{a \\in D} g_{1}(a) = c_{1}"), ("final", "p(r) = c_{2}")]),
   ("3", [("sum", "\\sum_{a \\in D} g_{0}(a) = c_{0}"),
     ("sum", "\\sum_{a \\in D} g_{1}(a) = c_{1}"),
     ("sum", "\\sum_{a \\in D} g_{2}(a) = c_{2}"), ("final", "p(r) = c_{3}")])]

end Tests

end Branching

#print axioms sumcheck_complete
#print axioms roundsGo_complete
#print axioms roundSum_zero
#print axioms branching_tree
#print axioms branching_verdict_isSome

end Specs
