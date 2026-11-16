/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.Fin.BigOperators
public import ArkLib.Data.MvPolynomial.Hypercube
public import ArkLib.Data.Polynomial.PointCollision
public import ArkLib.ProofSystem.Sumcheck.Message.Quadratic

/-!
# Sumcheck: soundness by counting, and compressed round messages

This is the sum-check protocol of [LFKN92], in the presentation of [Tha22, Section 4.1].

The prover claims `H = sum_{b in {0,1}^n} g(b)` for `g` of degree at most `d` in each variable.

Soundness counts the challenge vectors on which a false claim passes.

```text
    round i:  the prover sends g_i, of degree at most d
              the verifier checks g_i(0) + g_i(1) = c_i
              the verifier samples r_i and sets c_{i+1} = g_i(r_i)
    end:      the verifier checks g(r) = c_n
```

## Main statements

- `Sumcheck.Counting.completeness`: the honest prover is accepted on every challenge vector.
- `Sumcheck.Counting.soundness`: a false claim passes on at most `n d |F|^(n-1)` vectors.
- `Sumcheck.Counting.accepts_induced_iff`: replaying messages is checking their decodings.
- `Sumcheck.Counting.soundness_decoded`: the soundness bound carries over to messages.
- `Sumcheck.Counting.completeness_decoded`: so does completeness.
- `Sumcheck.Counting.soundness_quadratic`: soundness for quadratic messages, with `d = 2`.
- `Sumcheck.Counting.completeness_quadratic`: completeness for quadratic messages.

## Provers

A prover is a deterministic strategy from challenge vectors to round messages.

It is causal when round `i` reads only the challenges before `i`.

Against a causal prover the soundness error is therefore `n d / |F|`.

## Compressed round messages

A message model decodes a round message under the running claim.

The result is a polynomial of degree at most `d`.

The executable verifier replays the messages on the Boolean domain `{0, 1}`.

Each round runs the acceptance check, then moves the claim to the message's value at the challenge.

The verifier accepts when the replay ends at `g(r)`.

The quadratic message `(h(0), coefficient of X^2)` is such a model.

## Relation to the interaction-layer execution

The interaction-layer executor samples each challenge in turn and lets an effectful prover answer.

It succeeds when every sum check passes and the final check holds.

That check compares the exported original evaluation with the last message at the last challenge.

On the Boolean domain with messages of degree at most `d`, that is the event counted here.

Here the prover is deterministic and causal, and challenge vectors are counted, not sampled.

With uniform independent challenges, the count divided by `|F|^n` is the success probability.

So `n d / |F|` matches the executor's soundness bound.

## Computability

The honest prover, the decoded polynomials and the final claim are Mathlib polynomials.

They form the mathematical view, noncomputable because Mathlib polynomial arithmetic is.

The replay runs only the executable message operations and is proved to agree with that view.

## Provenance

Ported from Plonky3-lean, where it specifies the Plonky3 sumcheck verifier.

- Repository: https://github.com/Plonky3/Plonky3-lean
- Commit: `fdef3385014bd2e0d12d959c9afe70e2a9134775`
- Paths:
  - `Plonky3Lean/Spec/Sumcheck.lean`
  - `Plonky3Lean/Proofs/Sumcheck/Protocol.lean`
  - `Plonky3Lean/Proofs/Sumcheck/Decoded.lean`
  - `Plonky3Lean/Proofs/Sumcheck/Quadratic.lean`

## References

* [Lund, C., Fortnow, L., Karloff, H., and Nisan, N., *Algebraic methods for interactive proof
    systems*][LFKN92]
* [Thaler, J., *Proofs, Arguments, and Zero-Knowledge*][Tha22]
-/

@[expose] public section

namespace Sumcheck.Counting

open Finset MvPolynomial

section Spec

variable {F : Type} [CommRing F]

/-- The honest prover.

Round 0 sends the first coordinate-line restriction summed over the Boolean cube.

Later rounds recurse on `g` with its first variable set to `r_0`.
-/
noncomputable def honestProver :
    {n : ℕ} → MvPolynomial (Fin n) F → Fin n → (Fin n → F) → Polynomial F
  | 0, _ => fun i => i.elim0
  | n + 1, g => fun i r =>
    Fin.cases (∑ x : Fin (n + 1 - (0 + 1)) → Fin 2, g.evalExcept 0 (hypercubeSuffix 0 Fin.elim0 x))
      (fun j => honestProver (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => r 0)) j
        (Fin.tail r)) i

/-- A strategy is causal when its message in round `i` reads only the challenges before `i`. -/
def Causal {α : Type _} {n : ℕ} (P : Fin n → (Fin n → F) → α) : Prop :=
  ∀ i r r', (∀ j : Fin n, j < i → r j = r' j) → P i r = P i r'

/-- The verifier accepts the claim `c` against the prover `P` on the challenges `r`.

Every round checks the degree bound and the sum `g_i(0) + g_i(1) = c_i`.

The last check is `g(r) = c_n`.
-/
def Accepts (d : ℕ) :
    {n : ℕ} → MvPolynomial (Fin n) F → F → (Fin n → (Fin n → F) → Polynomial F) →
    (Fin n → F) → Prop
  | 0, g, c, _, r => eval r g = c
  | n + 1, g, c, P, r =>
    (P 0 r).natDegree ≤ d ∧ (P 0 r).eval 0 + (P 0 r).eval 1 = c ∧
      Accepts d (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => r 0))
        ((P 0 r).eval (r 0)) (fun i r' => P i.succ (Fin.cons (r 0) r')) (Fin.tail r)

end Spec

section Proofs

variable {F : Type} [CommRing F]

/-! ## The first variable -/

/-- Fixing the first variable evaluates by prepending its value. -/
theorem eval_fixFirstVariablesOfMQP_cons {n : ℕ} (a : F) (g : MvPolynomial (Fin (n + 1)) F)
    (s : Fin n → F) :
    eval s (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => a)) =
      eval (Fin.cons a s) g := by
  rw [eval_fixFirstVariablesOfMQP_one (ℓ := n + 1) (h := by omega) (H := g) (c := a) (x := s)]
  rfl

/-! ## The honest prover -/

/-- The honest first message evaluates to the hypercube sum with the first variable fixed. -/
theorem eval_honestProver_zero {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) (r : Fin (n + 1) → F)
    (a : F) :
    (honestProver g 0 r).eval a =
      hypercubeSum n (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => a)) 0
        Fin.elim0 := by
  refine (eval_sum_evalExcept_hypercube g 0 Fin.elim0 a).trans ?_
  refine Eq.trans ?_ (hypercubeSum_eq_fixFirstVariablesOfMQP g ⟨1, by omega⟩ (fun _ => a))
  unfold hypercubeSum
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1

/-- The honest first message passes the sum check against the true sum. -/
theorem honestProver_zero_sum {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) (r : Fin (n + 1) → F) :
    (honestProver g 0 r).eval 0 + (honestProver g 0 r).eval 1 =
      hypercubeSum (n + 1) g 0 Fin.elim0 :=
  sum_eval_sum_evalExcept_hypercube g 0 Fin.elim0

/-- The honest first message has degree at most the degree bound of `g`. -/
theorem natDegree_honestProver_zero_le {n d : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    (hg : g ∈ restrictDegree (Fin (n + 1)) F d) (r : Fin (n + 1) → F) :
    (honestProver g 0 r).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (natDegree_evalExcept_le 0 _ g).trans ((mem_restrictDegree_iff_degreeOf_le g d).mp hg 0)

/-- After the first challenge the honest prover is the honest prover of the fixed polynomial. -/
theorem honestProver_succ {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) (a : F) :
    (fun i r' => honestProver g i.succ (Fin.cons a r')) =
      honestProver (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => a)) := by
  funext i r'
  simp only [honestProver, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons]

/-- The honest prover is causal. -/
theorem honestProver_causal :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), Causal (honestProver g)
  | 0, _ => fun i => i.elim0
  | n + 1, g => fun i r r' h => by
    refine Fin.cases (fun _ => rfl) (fun j h => ?_) i h
    have h0 : r 0 = r' 0 := h 0 (Fin.succ_pos j)
    simp only [honestProver, Fin.cases_succ, h0]
    exact honestProver_causal _ j _ _ fun k hk => h k.succ (Fin.succ_lt_succ_iff.mpr hk)

/-! ## Completeness -/

/-- The honest prover makes the verifier accept the true sum, on every challenge vector. -/
theorem completeness {d : ℕ} :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), g ∈ restrictDegree (Fin n) F d →
    ∀ r, Accepts d g (hypercubeSum n g 0 Fin.elim0) (honestProver g) r
  | 0, g, _, r => by
    simp only [Accepts, Subsingleton.elim (Fin.elim0 : Fin 0 → F) r]
    exact (hypercubeSum_last 0 g r).symm
  | n + 1, g, hg, r => by
    refine ⟨natDegree_honestProver_zero_le hg r, honestProver_zero_sum g r, ?_⟩
    have h := completeness (n := n) (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => r 0))
      (fixFirstVariablesOfMQP_degreeLE (n + 1) ⟨1, by omega⟩ hg) (Fin.tail r)
    rw [← honestProver_succ g (r 0), ← eval_honestProver_zero g r (r 0)] at h
    exact h

/-! ## Soundness -/

open scoped Classical in
/-- Against a false claim, at most `n d |F|^(n-1)` challenge vectors accept.

This holds for every causal prover.
-/
theorem soundness [IsDomain F] [Fintype F] {d : ℕ} :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), g ∈ restrictDegree (Fin n) F d →
      ∀ (H : F), H ≠ hypercubeSum n g 0 Fin.elim0 →
      ∀ P, Causal P → #{r | Accepts d g H P r} * Fintype.card F ≤ n * d * Fintype.card F ^ n
  | 0, g, _, H, hH, P, _ => by
    have : ∀ r : Fin 0 → F, ¬ Accepts d g H P r := fun r h => hH <| by
      simp only [Accepts] at h
      rw [← h, Subsingleton.elim (Fin.elim0 : Fin 0 → F) r]
      exact (hypercubeSum_last 0 g r).symm
    simp [Finset.filter_false_of_mem fun r _ => this r]
  | n + 1, g, hg, H, hH, P, hP => by
    -- The first message reads no challenge.
    set p := P 0 (fun _ => 0)
    have hp : ∀ r, P 0 r = p := fun r => hP 0 _ _ fun j hj => absurd hj (Fin.not_lt_zero j)
    set s := honestProver g 0 (fun _ => 0)
    by_cases hacc : ∃ r, Accepts d g H P r
    swap
    · push Not at hacc
      simp [Finset.filter_false_of_mem fun r _ => hacc r]
    -- A first message that passes the sum check is not the honest one.
    obtain ⟨r₀, hr₀⟩ := hacc
    simp only [Accepts, hp] at hr₀
    have hps : p ≠ s := fun he => hH (hr₀.2.1 ▸ he ▸ honestProver_zero_sum g _)
    -- On the first challenge a, the rest of the run is a sumcheck of g(a, .) against p(a).
    set Q : F → Fin n → (Fin n → F) → Polynomial F := fun a i r' => P i.succ (Fin.cons a r')
    have hQ : ∀ a, Causal (Q a) := fun a i r r' h => hP _ _ _ fun j hj => by
      exact Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj
    have key : ∀ a, #{t | Accepts d g H P (Fin.cons a t)} * Fintype.card F ≤
        if p.eval a = s.eval a then Fintype.card F ^ n * Fintype.card F
        else n * d * Fintype.card F ^ n := by
      intro a
      split_ifs with ha
      · exact Nat.mul_le_mul_right _ ((card_le_univ _).trans (by simp))
      · refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun t ht => ?_))
          (soundness _ (fixFirstVariablesOfMQP_degreeLE (n + 1) ⟨1, by omega⟩ hg) (p.eval a)
            (fun h => ha (h.trans (eval_honestProver_zero g (fun _ => 0) a).symm)) (Q a) (hQ a))
        simp only [mem_filter, mem_univ, true_and, Accepts, hp, Fin.cons_zero,
          Fin.tail_cons] at ht ⊢
        exact ht.2.2
    have hroots : #{a | p.eval a = s.eval a} ≤ d :=
      Polynomial.card_le_of_eval_eq hps hr₀.1 (natDegree_honestProver_zero_le hg _) _
        fun a ha => (mem_filter.mp ha).2
    rw [Fin.card_filter_cons, Finset.sum_mul]
    refine (Finset.sum_le_sum fun a _ => key a).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have := card_le_univ (univ.filter fun a => ¬ p.eval a = s.eval a)
    calc _ ≤ d * (Fintype.card F ^ n * Fintype.card F) +
          Fintype.card F * (n * d * Fintype.card F ^ n) :=
          add_le_add (Nat.mul_le_mul_right _ hroots) (Nat.mul_le_mul_right _ this)
      _ = _ := by ring

end Proofs

section Decoded

variable {F : Type} [CommRing F] {Msg : Type}

/-- The executable verifier's replay of the messages against the challenges.

Each round runs the acceptance check, then moves the claim to the message's value at the challenge.

The result is the final claim, or nothing if some round rejects.
-/
def replay (ops : MessageOps F Msg) : F → List Msg → List F → Option F
  | c, m :: ms, r :: rs => if ops.accept c m then replay ops (ops.evaluate c m r) ms rs else none
  | c, _, _ => some c

/-- The final claim of the mathematical view.

It replays the decoded polynomials against the challenges. -/
noncomputable def finalClaim (dec : F → Msg → Polynomial F) : F → List Msg → List F → F
  | c, m :: ms, r :: rs => finalClaim dec ((dec c m).eval r) ms rs
  | c, _, _ => c

/-- When every message is accepted, the replay ends at the decoded polynomials' final claim. -/
theorem replay_eq_some_finalClaim (ops : MessageOps F Msg) (dec : F → Msg → Polynomial F)
    (hev : ∀ c m x, ops.evaluate c m x = (dec c m).eval x) (hacc : ∀ c m, ops.accept c m = true) :
    ∀ (c : F) (ms : List Msg) (rs : List F), replay ops c ms rs = some (finalClaim dec c ms rs)
  | _, [], _ => by simp [replay, finalClaim]
  | _, _ :: _, [] => by simp [replay, finalClaim]
  | c, m :: ms, r :: rs => by
    simp only [replay, finalClaim, hacc, ↓reduceIte, hev]
    exact replay_eq_some_finalClaim ops dec hev hacc _ ms rs

/-- The executable replay of quadratic messages ends at the decoded quadratics' final claim. -/
theorem replay_quadraticOps (c : F) (ms : List (F × F)) (rs : List F) :
    replay quadraticOps c ms rs = some (finalClaim (fun c m => (quadratic c m).val) c ms rs) :=
  replay_eq_some_finalClaim _ _ (fun _ _ _ => by simp [quadraticOps, quadratic])
    (fun _ _ => rfl) c ms rs

/-- The polynomials the verifier decodes, as a prover strategy. -/
noncomputable def induced (dec : F → Msg → Polynomial F) :
    {n : ℕ} → F → (Fin n → (Fin n → F) → Msg) → Fin n → (Fin n → F) →
      Polynomial F
  | 0, _, _ => fun i => i.elim0
  | _ + 1, c, M => fun i r =>
    Fin.cases (dec c (M 0 r))
      (fun j => induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r'))
        j (Fin.tail r)) i

omit [CommRing F] in
/-- A causal strategy's first message reads no challenge. -/
theorem causal_zero {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α}
    (hM : Causal M) (r r' : Fin (n + 1) → F) : M 0 r = M 0 r' :=
  hM 0 r r' fun j hj => absurd hj (Fin.not_lt_zero j)

omit [CommRing F] in
/-- After the first challenge a causal strategy stays causal. -/
theorem causal_shift {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α}
    (hM : Causal M) (a : F) : Causal fun (i : Fin n) r' => M i.succ (Fin.cons a r') :=
  fun i r r' h => hM _ _ _ fun j hj =>
    Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj

/-- The first decoded polynomial is the decoding of the first message under the claim. -/
theorem induced_zero (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    (M : Fin (n + 1) → (Fin (n + 1) → F) → Msg) (r : Fin (n + 1) → F) :
    induced dec c M 0 r = dec c (M 0 r) := rfl

/-- After the first challenge the decoded strategy decodes from the updated claim. -/
theorem induced_succ (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    {M : Fin (n + 1) → (Fin (n + 1) → F) → Msg} (hM : Causal M) (r : Fin (n + 1) → F) :
    (fun i r' => induced dec c M i.succ (Fin.cons (r 0) r')) =
      induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r')) := by
  funext i r'
  simp only [induced, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons,
    causal_zero hM (Fin.cons (r 0) r') r]

/-- A causal message strategy decodes to a causal prover. -/
theorem induced_causal (dec : F → Msg → Polynomial F) :
    ∀ {n : ℕ} (c : F) (M : Fin n → (Fin n → F) → Msg), Causal M →
      Causal (induced dec c M)
  | 0, _, _, _ => fun i => i.elim0
  | n + 1, c, M, hM => fun i r r' h => by
    refine Fin.cases (by simp [induced, causal_zero hM r r']) (fun j h => ?_) i h
    have h0 : r 0 = r' 0 := h 0 (Fin.succ_pos j)
    simp only [induced, Fin.cases_succ, causal_zero hM r r', h0]
    refine induced_causal dec _ _ (causal_shift hM _) j _ _ fun k hk => ?_
    simpa [Fin.tail] using h k.succ (Fin.succ_lt_succ_iff.mpr hk)

variable [DecidableEq F] {ops : MessageOps F Msg} {d : ℕ}

/-- The verifier above accepts the decoded polynomials exactly when the replay ends at `g(r)`.

Here the messages are decoded by a message model on the Boolean domain.
-/
theorem accepts_induced_iff [Nontrivial F] (model : MessageModel ({0, 1} : Finset F) ops d) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F) (c : F) (M : Fin n → (Fin n → F) → Msg),
      Causal M →
      ∀ r, Accepts d g c (induced (fun c m => (model.interpret c m).val) c M) r ↔
        replay ops c (List.ofFn fun i => M i r) (List.ofFn r) = some (eval r g)
  | 0, g, c, M, _, r => by
    simp [Accepts, replay, eq_comm]
  | n + 1, g, c, M, hM, r => by
    have hdeg : (model.interpret c (M 0 r)).val.natDegree ≤ d :=
      Polynomial.natDegree_le_iff_degree_le.mpr
        (Polynomial.mem_degreeLE.mp (model.interpret c (M 0 r)).property)
    have hsum := model.accept_iff c (M 0 r)
    rw [Finset.sum_pair zero_ne_one] at hsum
    have ih := accepts_induced_iff model (n := n)
      (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => r 0))
      ((model.interpret c (M 0 r)).val.eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r'))
      (causal_shift hM _) (Fin.tail r)
    rw [← induced_succ (fun c m => (model.interpret c m).val) c hM r,
      eval_fixFirstVariablesOfMQP_cons, Fin.cons_self_tail] at ih
    simp only [Accepts, induced_zero, hdeg, true_and, List.ofFn_succ, replay,
      model.evaluate_eq]
    by_cases hacc : ops.accept c (M 0 r) = true
    · simp only [hacc, ↓reduceIte, hsum.mp hacc, true_and]
      exact ih
    · simp only [hacc, hsum.not.mp hacc, false_and, Bool.false_eq_true, ↓reduceIte,
        reduceCtorEq]

open scoped Classical in
/-- Against a false claim, at most `n d |F|^(n-1)` challenge vectors replay to `g(r)`.

This holds for every causal message strategy.
-/
theorem soundness_decoded [IsDomain F] [Fintype F]
    (model : MessageModel ({0, 1} : Finset F) ops d)
    {n : ℕ} (g : MvPolynomial (Fin n) F) (hg : g ∈ restrictDegree (Fin n) F d) (H : F)
    (hH : H ≠ hypercubeSum n g 0 Fin.elim0)
    (M : Fin n → (Fin n → F) → Msg) (hM : Causal M) :
    #{r | replay ops H (List.ofFn fun i => M i r) (List.ofFn r) = some (eval r g)} *
        Fintype.card F ≤ n * d * Fintype.card F ^ n := by
  have := soundness g hg H hH _
    (induced_causal (fun c m => (model.interpret c m).val) H M hM)
  simpa only [accepts_induced_iff model g H M hM] using this

/-- Decoding the encoded honest messages under the true running claims gives the honest prover. -/
theorem induced_encode_honestProver [Nontrivial F] (model : MessageModel ({0, 1} : Finset F) ops d)
    (enc : Polynomial F → Msg)
    (henc : ∀ c p, p.natDegree ≤ d → p.eval 0 + p.eval 1 = c →
      (model.interpret c (enc p)).val = p) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), g ∈ restrictDegree (Fin n) F d →
      induced (fun c m => (model.interpret c m).val) (hypercubeSum n g 0 Fin.elim0)
        (fun i r => enc (honestProver g i r)) = honestProver g
  | 0, _, _ => funext fun i => i.elim0
  | n + 1, g, hg => by
    funext i r
    have h0 := henc _ _ (natDegree_honestProver_zero_le hg r) (honestProver_zero_sum g r)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · simp only [induced, Fin.cases_succ, h0, eval_honestProver_zero]
      have := induced_encode_honestProver model enc henc
        (fixFirstVariablesOfMQP (n + 1) ⟨1, by omega⟩ g (fun _ => r 0))
        (fixFirstVariablesOfMQP_degreeLE (n + 1) ⟨1, by omega⟩ hg)
      rw [← honestProver_succ] at this
      have h := congrFun (congrFun this j) (Fin.tail r)
      simp only [Fin.cons_self_tail] at h
      exact h

/-- The encoded honest messages replay to `g(r)` from the true sum.

This needs a message for every polynomial of degree at most `d` whose Boolean sum is the claim.
-/
theorem completeness_decoded [Nontrivial F] (model : MessageModel ({0, 1} : Finset F) ops d)
    (enc : Polynomial F → Msg)
    (henc : ∀ c p, p.natDegree ≤ d → p.eval 0 + p.eval 1 = c →
      (model.interpret c (enc p)).val = p)
    {n : ℕ} (g : MvPolynomial (Fin n) F) (hg : g ∈ restrictDegree (Fin n) F d) (r : Fin n → F) :
    replay ops (hypercubeSum n g 0 Fin.elim0) (List.ofFn fun i => enc (honestProver g i r))
      (List.ofFn r) = some (eval r g) := by
  have hM : Causal fun i r => enc (honestProver g i r) := fun i r r' h =>
    congrArg enc (honestProver_causal g i r r' h)
  refine (accepts_induced_iff model g _ _ hM r).mp ?_
  rw [induced_encode_honestProver model enc henc g hg]
  exact completeness g hg r

/-! ## Quadratic rounds -/

open scoped Classical in
/-- Soundness for quadratic messages replayed with the shared executable operations. -/
theorem soundness_quadratic [IsDomain F] [Fintype F]
    {n : ℕ} (g : MvPolynomial (Fin n) F) (hg : g ∈ restrictDegree (Fin n) F 2) (H : F)
    (hH : H ≠ hypercubeSum n g 0 Fin.elim0)
    (M : Fin n → (Fin n → F) → F × F) (hM : Causal M) :
    #{r | replay quadraticOps H (List.ofFn fun i => M i r) (List.ofFn r) = some (eval r g)} *
        Fintype.card F ≤ n * 2 * Fintype.card F ^ n :=
  soundness_decoded quadraticModel g hg H hH M hM

omit [DecidableEq F] in
/-- Completeness for quadratic messages: the encoded honest messages replay to `g(r)`. -/
theorem completeness_quadratic [Nontrivial F] {n : ℕ} (g : MvPolynomial (Fin n) F)
    (hg : g ∈ restrictDegree (Fin n) F 2) (r : Fin n → F) :
    replay quadraticOps (hypercubeSum n g 0 Fin.elim0)
      (List.ofFn fun i => quadraticEncode (honestProver g i r)) (List.ofFn r) =
        some (eval r g) := by
  classical
  exact completeness_decoded quadraticModel quadraticEncode
    (fun _ _ hp hc => quadratic_quadraticEncode hp hc) g hg r

end Decoded

end Sumcheck.Counting
