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
* `Frozen` states that the handler table keeps the oracles recorded before a loop, so a
  continuation can still query them. This module and Spartan use it with `sumcheck_complete` of
  `Specs.Examples.Sumcheck`.
* The tests read the branching message by its label (`tr⟦m⟧`), read moves inside a case
  (`tr⟦m = 2, sumcheck, 0, g⟧`), and check that the skeleton has one case per value of `m` with the
  expected checks in expanded TeX.

This module proves no soundness statement. The protocol demonstrates the shape mechanism only: the
prover chooses `p`, so the claim it proves holds for every `c` that some polynomial sums to.

## Design choices

* The prover sends `p` as an oracle message after `m`. *Why:* the type of `p` depends on `m`, and
  an input bundle is fixed before the prover sends `m`.
* The honest functions read the whole witness `⟨m, p⟩`, so the honest oracle message of case `m`
  is `polyAt m w`, which is `p` when `m` matches and `0` in the cases the honest prover never
  takes (`polyAt_self`).
* A label inside a branch names the case first (`tr⟦m = 2, p⟧`), and the accessor returns an
  `Option`: `some` of the move when the transcript's message `m` is `2`, and `none` otherwise.
  *Why:* the transcript type after the message depends on the message, so the case must be fixed
  before any move inside it has a type.
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

/-- Moves inside the case `m = 2`: the oracle `p` and the first round polynomial of the stage. -/
example (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, p⟧ = (caseOf tr 2).map (·.1) := rfl
example (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, sumcheck, 0, g⟧ = (caseOf tr 2).map (·.2.1) := rfl
example (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, sumcheck, 1, r⟧ = (caseOf tr 2).map (·.2.2.2.2.1) := rfl

/-- The transcript type of the case `m`. -/
abbrev CaseTr (m : Fin 4) : Type :=
  Transcript oracleSig (.liftBind (.oracle (ℚ⦃≤ 2⦄[X Fin m]) inferInstance) fun _ =>
    Sumcheck.protocol ℚ 2 m)

/-- On a transcript whose message is `2` the accessor returns the move, and on any other message it
returns `none`. -/
example (x : CaseTr 2) (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) (h : tr = ⟨(2 : Fin 4), x⟩) :
    tr⟦m = 2, sumcheck, 0, g⟧ = some x.2.1 := by
  subst h; rfl
example (x : CaseTr 1) (tr : (branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) (h : tr = ⟨(1 : Fin 4), x⟩) :
    tr⟦m = 2, p⟧ = none := by
  subst h; rfl

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

#print axioms roundSum_zero
#print axioms branching_tree
#print axioms branching_verdict_isSome

end Specs
